import ClausalExtraction.ToExpr
import Lean

open Lean
open Lean.Meta


section Expr
open Lean.Expr
open Lean.Literal

variable (m:Std.HashMap FVarId Expr)

private def toExprExpr  : Expr → MetaM Expr
  | bvar n _        => mkApp (mkConst ``mkBVar) (mkNatLit n)
  | fvar n _        =>
    match m.find? n with
    | some e => e
    | none => mkApp (mkConst ``mkFVar) (toExpr n)
  | mvar n _ =>
    throwError "Meta variables cannot be lifted."
  | sort l _        => mkApp (mkConst ``mkSort) (toExpr l)
  | const n ls _    => mkApp2 (mkConst ``mkConst) (toExpr n) (toExpr ls)
  | app f x _       => do return mkApp2 (mkConst ``mkApp) (← toExprExpr f) (← toExprExpr x)
  | lam x d b c     => do return mkApp4 (mkConst ``mkLambda) (toExpr x) (toExpr c.binderInfo) (← toExprExpr d) (← toExprExpr b)
  | forallE x d b c => do return mkApp4 (mkConst ``mkForall) (toExpr x) (toExpr c.binderInfo) (← toExprExpr d) (← toExprExpr b)
  | letE x t v b c  => do return mkApp5 (mkConst ``mkLet) (toExpr x) (← toExprExpr t) (← toExprExpr v) (← toExprExpr b) (toExpr c.nonDepLet)
  | lit (natVal n) _ => pure <| mkApp (mkConst ``mkNatLit) (mkNatLit n)
  | lit (strVal s) _ => pure <| mkApp (mkConst ``mkStrLit) (mkStrLit s)
  | mdata md e _    => do return mkApp2 (mkConst ``mkMData) (toExpr md) (← toExprExpr e)
  | proj s i e _    => do return mkApp3 (mkConst ``mkProj) (toExpr s) (mkNatLit i) (← toExprExpr e)

end Expr

def exprType := Lean.mkConst `Lean.Expr []

structure ArgBinding where
(fvar : FVarId)
(userName : Name)
(freshName : Name)
-- Meta variable representing type of variable
(type : Expr)

structure ArgState where
(antiquotedVars : Array ArgBinding)

namespace ArgState

def addPatVar (lctx:LocalContext) (b:ArgBinding ): LocalContext :=
  lctx.mkLocalDecl b.fvar b.freshName b.type BinderInfo.implicit

-- Add antiquoted variables to local context
def patContext (s:ArgState) (lctx:LocalContext) : LocalContext :=
  s.antiquotedVars.foldl addPatVar lctx

def bindAntiquoteVarSyntax (b:ArgBinding) (v:LocalContext × Array Expr × Array Expr × Syntax)
    : Lean.Elab.Term.TermElabM (LocalContext × Array Expr × Array Expr × Syntax) := do
  let (lctx, fvars, types, rhs) := v
  -- Create free variable representing type of expression
  let fvar ← mkFreshFVarId
  -- Create fresh name for syntax
  let tpv ← mkFreshUserName `v
  -- Extend local context
  let lctx := lctx.mkLocalDecl fvar tpv exprType BinderInfo.default
  let fvars := fvars.push (mkFVar fvar)
  let tp ← instantiateMVars b.type
  let types := types.push (← toExprExpr Std.HashMap.empty tp)
  let rhs ← `(Bind.bind (mkFreshExprMVar (some $(mkIdent tpv)))
                        (fun ($(mkIdent b.userName) : Expr) => $(rhs)))
  pure (lctx, fvars, types, rhs)

-- Create map that maps the ith antiquoted variable to the ith binder.
def mkBoundVarMap (s:ArgState) : Std.HashMap FVarId Expr := Id.run do
  let n := s.antiquotedVars.size - 1
  let ins (m:Std.HashMap FVarId Expr) (b:ArgBinding) : Std.HashMap FVarId Expr :=
        m.insert b.fvar (mkBVar (n - m.size))
  pure <| s.antiquotedVars.foldl ins Std.HashMap.empty

-- Create map that maps the ith antiquoted variable to a meta variable.
def mkMetaVarMap (s:ArgState) : MetaM (Std.HashMap FVarId Expr) := do
  let n := s.antiquotedVars.size - 1
  let ins (m:Std.HashMap FVarId Expr) (b:ArgBinding) : MetaM (Std.HashMap FVarId Expr) := do
        let v ← mkFreshExprMVar (some b.type) MetavarKind.natural b.userName
        pure <| m.insert b.fvar (ToExpr.toExpr v)
  s.antiquotedVars.foldlM ins Std.HashMap.empty

open Lean.Elab.Term

def mkRhs (s:ArgState) (patS:Syntax) (rhs:Syntax) (expType: Option Expr) : TermElabM (Expr × Expr) := do
  let lctx ← getLCtx
  let localInsts ← getLocalInstances
  let pat ← withLCtx (s.patContext lctx) localInsts $ Lean.Elab.Term.elabTerm patS none
  let pat ← instantiateMVars pat
  let rhs ← do
    let e ← mkFreshUserName `e
    let patIdent ← mkFreshUserName `termPat
    let appVar (a:Syntax) (b:ArgBinding) : TermElabM Syntax := `($(a) $(mkIdent b.userName))
    let d ← s.antiquotedVars.foldlM appVar (mkIdent patIdent)
    let rhs ← `(Bind.bind (isDefEq $(mkIdent e) $(d))
                  (fun (b:Bool) => if b then $rhs else pure none))

    let patFVar ← mkFreshFVarId
    let insLambda (b:ArgBinding) (e:Expr) : Expr :=
          mkLambda b.userName BinderInfo.default exprType e
    let patValue := s.antiquotedVars.foldr insLambda (← toExprExpr (mkBoundVarMap s) pat)
    let fvars := #[mkFVar patFVar]
    let values := #[patValue]
    let (lctx, fvars, values, rhs) ← s.antiquotedVars.foldrM bindAntiquoteVarSyntax (lctx, fvars, values, rhs)

    let lctx :=
          let insPatType (b:ArgBinding) (e:Expr) : Expr :=
                mkForall b.userName BinderInfo.default exprType e
          let termIdentType := s.antiquotedVars.foldr insPatType exprType
          lctx.mkLocalDecl patFVar patIdent termIdentType BinderInfo.default

    let rhs ← `(fun ($(mkIdent e) : Expr) => $(rhs))
    let rhs ← withLCtx lctx localInsts <| Lean.Elab.Term.elabTerm rhs expType
    let rhs := rhs.replaceFVars fvars values
    let rhs ← instantiateMVars rhs
    pure rhs
  let patE ← toExprExpr (← mkMetaVarMap s) pat
  pure (patE, rhs)

end ArgState

section ArgInfo

private partial def getArgInfo (pat:Syntax) : StateRefT' IO.RealWorld ArgState MetaM Syntax := do
  if pat.isAntiquot then
    let k := pat.antiquotKind? |>.get!
    let t := pat.getAntiquotTerm
    match t with
    | `(_) => pure t
    | `($id:ident) => do
      let fvarId ← mkFreshFVarId
      let userName := id.getId
      let freshName ← mkFreshUserName userName
      let type ← mkFreshTypeMVar
      let binding := {
            fvar := fvarId,
            userName := userName,
            freshName := freshName,
            type := type
          }
      let () ← modifyGet <| fun s =>
         ((), { antiquotedVars := s.antiquotedVars.push binding
              })
      pure (mkIdent freshName)
    | anti => throwErrorAt anti "unsupported antiquotation kind in pattern"
  else
    if pat.getNumArgs > 0 then
      pat.setArgs <$> pat.getArgs.mapM getArgInfo
    else
      pure pat

private partial def getHeadInfo (pat:Syntax) : MetaM (Syntax × ArgState) := do
  -- quotation pattern
  unless pat.isQuot do
    throwError "Expected quot."
  let s := { antiquotedVars := Array.empty }
  let (pat, s) ← (getArgInfo pat.getQuotContent).run s
  pure (pat, s)

end ArgInfo

section Parser

open Lean.Elab
open Lean.Parser

@[termParser] def «matchrule» : Parser :=
  leading_parser:leadPrec "matchrule " >> termParser >> darrow >> termParser


@[termElab «matchrule»] def elabMatchRule : Lean.Elab.Term.TermElab := λ(s:Syntax) (expType:Option Expr) => do
  match s with
  | `(matchrule $pat => $rhs) => do
    let (pat, s) ← getHeadInfo pat
    let (pat, rhs) ← s.mkRhs pat rhs expType
    pure rhs
  | _ =>
    throwUnsupportedSyntax


@[termParser] def «simprule» : Parser :=
  leading_parser:leadPrec "simprule " >> termParser >> darrow >> termParser


@[termElab «simprule»] def elabSimpRule : Lean.Elab.Term.TermElab := λ(s:Syntax) (expType:Option Expr) => do
  match s with
  | `(simprule $pat => $rhs) => do
    let (pat, s) ← getHeadInfo pat
    let (pat, rhs) ← s.mkRhs pat rhs none
    let rhsType ← inferType rhs
    pure (mkAppN (mkConst `Prod.mk [levelZero, levelZero])
           #[mkConst `Lean.Expr, rhsType, pat, rhs])
  | _ =>
    throwUnsupportedSyntax

end Parser

/-
#check matchrule `(($(x) : Int) = $(y)) => some <$> Lean.Meta.instantiateMVars x

def test3 := matchrule `(($(x) : Int) = $(y)) => some <$> Lean.Meta.instantiateMVars x

#print test3
-/