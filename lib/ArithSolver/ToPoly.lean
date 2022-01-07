/-
This module defines operations for constructing a
linear arithmetic state form a Lean context while
ensuring Lean proofs can be constructed from SAT check.
-/
import ArithSolver.ConstantTheory
import ArithSolver.IntNormalization
import Lean

open Lean
open Lean.Meta
open Lean.Elab.Tactic

namespace ArithSolver

section ExpressionUtils

private def propExpr : Expr := mkSort levelZero

def falseExpr : Expr := mkConst ``False

def exprHead : Expr → Option Name
| Expr.bvar .. => none
-- FIXME: Figure out if we want to see through free variables with let bindings in local context.
| Expr.fvar .. => none
| Expr.mvar .. => none
| Expr.sort .. => none
| Expr.const nm .. => nm
| Expr.app f a .. => exprHead f
| Expr.lam .. => none
| Expr.forallE .. => none
-- FIXME: Figure out if we want to see through let bindings.
| Expr.letE .. => none
| Expr.lit .. =>  none
-- FIXME: Figure out if ignoring metadata is always ok.
| Expr.mdata  _ x .. => exprHead x
 -- FIXME: Figure out if we want to see through projections.
| Expr.proj n i s .. => none

end ExpressionUtils

-- | Assertion added
structure Assertion where
  -- Identifies the free variable in the initial context used to generate this one.
  -- Used to allow deleting original proposition from local context.
  origin : Option FVarId
  -- The free variable used to identify the assertion in the local context
  -- generated for the assertion.
  name : Name
  -- A proof of the assertion in the context of the original goal.
  proof : Expr
  -- Predicate that was asserted.
  pred : Pred

namespace Assertion

instance : Inhabited Assertion := ⟨
     { origin := arbitrary,
       name := arbitrary,
       proof := arbitrary,
       pred := arbitrary
     }
  ⟩

end Assertion

def uninterpTheoryRef : TheoryRef := ⟨0⟩

structure Context where
  -- Maps constant names to the theory associated with that constant.
  constTheoryMap : Std.PersistentHashMap Name TheoryRef
  -- An array of theory operation.
  -- The first theory is used for uninterpreted constants.
  theories : Array TheoryOps

namespace Context

partial def varExpr (ctx:Context) (v:Var) : IO Expr := do
  let th := ctx.theories[v.theory.toNat]
  th.varExpr (varExpr ctx) v.theoryVar

def predExpr (ctx:Context) (p:Pred) : IO Expr := do
  let ref := p.theory.toNat
  if h : ref < ctx.theories.size then
    let ops := (ctx.theories.get ⟨ref, h⟩)
    let e ← ops.predExpr (ctx.varExpr) p.theoryPred
    pure e
  else
    panic! "Invalid theory index."

mutual

-- | Create a variable for the current expression from a theory.
--
-- The source theory is the theory that initiated the request from a variable.
-- If the expression head is assigned to this theory, then we ensure this is an
-- uninterpreted symbol.
partial
def exprVar (ctx:Context) (e:Expr) : MetaM (ExprEvalResult Var) := do
  -- Get theory associated with head symbol.
  let mut thRef :=
        match exprHead e with
        | some head => ctx.constTheoryMap.findD head uninterpTheoryRef
        | none => uninterpTheoryRef
  let th := ctx.theories[thRef.toNat]
  let r ← th.exprVar e (services ctx)
  pure { r with var := Var.mkVar thRef r.var }

partial
def services (ctx:Context) : SolverServices := {
    varExpr := varExpr ctx,
    uninterpVar := fun e => do
      let thRef := uninterpTheoryRef
      let th := ctx.theories[thRef.toNat]
      let r ← th.exprVar e (services ctx)
      pure (Var.mkVar thRef r.var)
    exprVar := exprVar ctx,
  }

end

end Context

structure State where
  -- Predicates asserted to be true.
  assertions : Array Assertion := #[]

namespace State


-- | Return proofs associated with assertions.
def proofs (s:State) : Array Expr := s.assertions.map Assertion.proof

-- | Add assertions to local context.
-- Return new local context along with array of free variables identifying assertions.
def addAssertions (ctx:Context) (s:State) (lctx:LocalContext) : MetaM (LocalContext × Array Expr) := do
  let mut lctx := lctx
  let mut fvars : Array Expr := #[]
  for a in s.assertions do
    let newVar ← mkFreshFVarId
    fvars := fvars.push (mkFVar newVar)
    match a.origin with
    | some prevVar =>
      -- FIXME: Make sure erasing the previous declaration does not break things.
      lctx := lctx.erase prevVar
    | none =>
      pure ()
    let e ← ctx.predExpr a.pred
    lctx := lctx.mkLocalDecl newVar a.name e
  pure (lctx, fvars)

end State

structure Goal where
  -- Given a proof from the solver
  onMkProof : Expr → Expr

def Goal.onAddAssumptions (ctx:Context) (tactic:Name) (g:Goal) (goalId:MVarId) (s:State) : MetaM (List MVarId) := do
  checkNotAssigned goalId tactic
  let tag   ← getMVarTag goalId
  let lctx ← getLCtx
  let (lctx, fvars) ← State.addAssertions ctx s lctx
  withReader (fun ctx => { ctx with lctx := lctx }) $ do
    let solverGoal ← mkFreshExprSyntheticOpaqueMVar falseExpr tag
    -- Turn goal into lambda with free variables from assertions
    let fn ← Meta.mkLambdaFVars fvars solverGoal
    -- Assign goal
    assignExprMVar goalId (g.onMkProof (mkAppN fn s.proofs))
    pure [solverGoal.mvarId!]

-- | This represents a functions of the form ∀(args), P → Q
structure Transformer where
  -- Meta variables created for arguments
  -- These should all be resolved by matching against P or Q.
  arguments : Array Expr
  -- Binders for arguments (binders.size = arguments.size)
  binders : Array BinderInfo
  -- The assumption proposition P
  assumptionType : Expr
  -- | The result proposition Q
  resultType : Expr

-- | This constructs a transformer from a term denoing an inference rule.
def mkTransformer (proof:Expr) : MetaM Transformer := do
  -- Get variables and type of proof
  let (vars, binders, resultType) ← forallMetaTelescope (← inferType proof)
  if vars.size = 0 then
    throwError m!"Expected predicate with at least one argument {indentExpr proof}."
  let avar := vars.back.mvarId!
  let some avarDecl ← (← getMCtx).findDecl? avar
    | throwError "unknown goal {avar.name}"
  pure {
      arguments := vars.pop,
      binders := binders.pop,
      assumptionType := avarDecl.type,
      resultType := resultType
    }

def resolveTransformerArgs (proofExpr:Expr) (t:Transformer) : MetaM Bool := do
  for v in t.arguments, b in t.binders do
    if ← isExprMVarAssigned v.mvarId! then
      continue
    match b with
    | BinderInfo.instImplicit =>
      -- Synthesize class instance
      let classType ← inferType v
      let classVal  ← synthInstance classType
      unless (← isDefEq v classVal) do
        return false
    | _ =>
      throwError m!"Unresolved transformer argument in {indentExpr proofExpr}"
  return true

-- | A rule that given a proposition, tries to produce a predicate
-- and a function expression that transforms proofs of the original
-- proposition into proofs of the predicate.
structure PredRule where
  theoryRef : TheoryRef
  action (prop : Expr) : SolverM (Option (TheoryPred × Expr))

def runTerminals (terminals:Array PredRule) (prop:Expr) : SolverM (Option (Pred × Expr)) := do
  for t in terminals do
    match ← t.action prop with
    | none => pure ()
    | some (p, transform) =>
      return (some (Pred.mkPred t.theoryRef p, transform))
  return none

-- | See if we can add the local declaration to the arithmetic unit.
-- proof is a term of type prop.
def addAssertion (prules:Array PredRule)
                 (r:IO.Ref State)
                 (origin : Option FVarId)
                 (name:Name)
                 (proof:Expr)
                 (prop:Expr) : SolverM Bool := do
  match ← runTerminals prules prop with
  | none => do
    pure false
  | some (pred, proofFn) => do
    let a := { origin := origin, name := name, proof := mkApp proofFn proof, pred := pred }
    r.modify $ λs => { s with assertions := s.assertions.push a }
    pure true

namespace ArithTheory

private def intNonNegMkExpr : Expr := mkConst ``Int.NonNeg.mk
private def ofNatExpr : Expr := mkConst ``Int.ofNat

def matchNatExpr (prules:Array PredRule) (r:IO.Ref ArithSolver.State) (nm:Name) (e:Expr) (tp:Expr) : SolverM Bool := do
  unless (← isDefEq tp natExpr) do
    return false
  -- Assert v is non negative
  let proof := mkApp intNonNegMkExpr e
  let prop := mkIntNonNegExpr (mkApp ofNatExpr e)
  _ ← addAssertion prules r none (nm ++ "isGe0") proof prop
  return true

end ArithTheory

def processDecls (prules:Array PredRule) (r:IO.Ref State) (lctx:LocalContext) : SolverM Unit := do
  let mut seenFirst := false
  for md in lctx.decls do
    -- Skip first declaration (as it corresponds to initial goal for
    -- recursive purposes)
    unless seenFirst do
      seenFirst := true
      continue
    -- Skip if declaration has been deleted.
    let some d ← pure md
         | continue
    -- FIXME: Figure out how to support let declarations
    if d.isLet then
      continue
    -- If we have a natural number, then declare it.
    if ← ArithTheory.matchNatExpr prules r d.userName (mkFVar d.fvarId) d.type then
      continue
    -- If this is a proposition then try assuming it.
    if ← isDefEq (← inferType d.type) propExpr then do
      let _ ← addAssertion prules r (some d.fvarId) d.userName (mkFVar d.fvarId) d.type

-- Negating goal

theorem decidable_by_contra {P:Prop} [h:Decidable P] (q : ¬¬P) : P :=
  match h with
  | isFalse h => False.elim (q h)
  | isTrue h => h

def matchNot (e:Expr) : MetaM (Option Expr) := do
  let mvar ← mkFreshExprMVar propExpr MetavarKind.natural `a
  let p := mkApp (mkConst ``Not) mvar
  pure $ if ← isDefEq p e then mvar else none

def analyzeGoal (prules:Array PredRule) (r : IO.Ref State) (tactic:Name) (goalId:MVarId) (target:Expr) : SolverM Goal := do
  -- If goal is already false, then just negate it.
  if ← isDefEq target falseExpr then
    return { onMkProof := id }

  -- If goal has form `Not p` then we can diretly process property.
  match ← matchNot target with
  | some prop => do
    if ← addAssertion prules r none `negGoal (mkBVar 0) prop then
      return { onMkProof := mkLambda Name.anonymous BinderInfo.default prop }
  -- Goal is not a negation, so we seeing if we can extract a predicate from
  -- negated goal and then use decidable_by_contra to get proof of negation
  -- of target.
  | none =>
    let prop := mkApp (mkConst ``Not) target
    if ← addAssertion prules r none `negGoal (mkBVar 0) prop then
      let some classVal ← synthInstance? (mkApp (mkConst ``Decidable) target)
          | throwTacticEx tactic goalId "Could not synthesize Decidable instance for proposition:."
      let decideByContraExpr := mkAppN (mkConst ``decidable_by_contra) #[target, classVal]
      return {
          onMkProof := fun goalProof =>
            mkApp decideByContraExpr (mkLambda Name.anonymous BinderInfo.default prop goalProof)
          }

  -- In final case, we just ignore the goal and try to prove a contradiction from assumptions
  -- alone.
  match ← inferType target with
  | Expr.sort lvl _ =>
    pure { onMkProof := fun goalProof =>
      mkAppN (mkConst ``False.elim [lvl]) #[target, goalProof]
    }
  | _ =>
    throwTacticEx tactic goalId "Expected a type."

def mkTermTrans (thref:TheoryRef) (terminals:Array PredRule) (nm:Name) : PredRule :=
  { theoryRef := thref,
    action := fun (prop:Expr) => do
      let rule := mkConst nm
      let trans ← mkTransformer rule
      unless ← isDefEq trans.assumptionType prop do
        return none
      unless ← resolveTransformerArgs rule trans do
        return none
      let propProofFn := mkAppN rule trans.arguments
      for t in terminals do
        match ← t.action trans.resultType with
        | none =>
          pure ()
        | some (pred, nextProofFn) => do
          let finalProofFn :=
                mkLambda Name.anonymous BinderInfo.default prop
                  (mkApp nextProofFn (mkApp propProofFn (mkBVar 0)))
          return (some (pred, finalProofFn))
      return none
  }

def mapFromList (l:List (Name × TheoryRef)) : Std.PersistentHashMap Name TheoryRef := Id.run do
  let mut r := {}
  for (nm,ref) in l do
    r := r.insert nm ref
  pure r

abbrev arithTheoryRef : TheoryRef := ⟨1⟩

def mkArithGoal (terminals: Array PredRule) (tactic:Name) (goalId:MVarId) : SolverM (Goal × State) := do
  withMVarContext goalId do
    let md ← getMVarDecl goalId
    let stateRef ← IO.mkRef {}
    processDecls terminals stateRef md.lctx
    let g ← analyzeGoal terminals stateRef tactic goalId md.type
    pure (g, ← stateRef.get)

syntax (name := to_poly) "to_poly" : tactic

@[tactic to_poly] def evalToPoly : Tactic := fun stx => do
  liftMetaTactic fun mvarId => do
    let constRef ← IO.mkRef {}
    let arithRef ← IO.mkRef {}
    let ctx : Context := {
      constTheoryMap := mapFromList [
        (``HAdd.hAdd, arithTheoryRef),
        (``HSub.hSub, arithTheoryRef),
        (``HMul.hMul, arithTheoryRef)
      ],
      theories := #[ConstantTheory.ops constRef, ArithTheory.ops arithRef ]
    }
    let terminals := #[
            ArithTheory.matchIntNonNeg arithRef,
            ArithTheory.matchIntEq0 arithRef,
            ArithTheory.matchNotIntEq0 arithRef
          ]
    let convTerm (f : Expr → SolverM (Option (TheoryPred × Expr))) : PredRule :=
          { theoryRef := arithTheoryRef,
            action := f
          }
    let terminals := terminals.map convTerm
    -- Create list of transformers to apply
    let transformers := ArithTheory.transformerNames.map (mkTermTrans arithTheoryRef terminals)
    let terminals := terminals ++ transformers

    let (goal, s) ← mkArithGoal terminals `to_poly mvarId ctx.services
    let r@([goalId]) ← goal.onAddAssumptions ctx `to_poly mvarId s
      | throwError "Expected more goals"
    pure r

end ArithSolver