/-
This defines the ArithM monad basic operations used to generate a system of
numerical equations from a Lean local context.
-/
import ArithSolver.Basic
import ArithSolver.Int

open Lean

namespace ArithSolver

private def notExpr : Expr := mkConst ``Not

def natExpr : Expr := mkConst ``Nat
def intExpr := mkConst ``Int

def intAddConst : Expr :=
  let f := mkConst ``HAdd.hAdd [levelZero, levelZero, levelZero]
  let inst := mkAppN (mkConst ``instHAdd [levelZero]) #[intExpr, mkConst ``Int.instAddInt]
  mkAppN f #[intExpr, intExpr, intExpr, inst]

def intSubConst : Expr :=
  let f := mkConst ``HSub.hSub [levelZero, levelZero, levelZero]
  let inst := mkAppN (mkConst ``instHAdd [levelZero]) #[intExpr, mkConst ``Int.instSubInt]
  mkAppN f #[intExpr, intExpr, intExpr, inst]

def intMulConst : Expr :=
  let f := mkConst ``HMul.hMul [levelZero, levelZero, levelZero]
  let inst := mkAppN (mkConst ``instHMul [levelZero]) #[intExpr, mkConst ``Int.instMulInt]
  mkAppN f #[intExpr, intExpr, intExpr, inst]

def intNegConst : Expr :=
  let f := mkConst ``Neg.neg [levelZero]
  let inst := mkConst ``Int.instNegInt
  mkAppN f #[intExpr, inst]

-- A structure used to denote an integer expression
structure IntExpr where
  toExpr : Expr
  deriving Inhabited

instance : Coe IntExpr Expr where
  coe := IntExpr.toExpr

instance : Add IntExpr where
  add := λx y => IntExpr.mk (mkAppN intAddConst #[x, y])

-- Create a nat lit as an int
def natLitAsIntExpr (n:Nat) : IntExpr :=
  let z := mkRawNatLit n
  let ofNat := mkConst ``OfNat.ofNat [levelZero]
  let inst := mkConst ``Int.instOfNatInt
  IntExpr.mk (mkAppN ofNat #[intExpr, z, mkApp inst z])

def mkIntLit : Int → IntExpr
| Int.ofNat n => natLitAsIntExpr n
| Int.negSucc n => IntExpr.mk (mkApp intNegConst (natLitAsIntExpr (n+1)))

instance : Coe Int IntExpr where
  coe := fun x => mkIntLit x

def intZeroExpr : IntExpr := natLitAsIntExpr 0

private def intNonNegExpr : Expr := mkConst ``Int.NonNeg
def mkIntNonNegExpr (e:Expr) : Expr := mkApp intNonNegExpr e

private def intEqExpr : Expr := mkApp (mkConst ``Eq [levelOne]) (mkConst ``Int)
def mkIntEq0Expr (e:Expr) : Expr := mkAppN intEqExpr #[e, intZeroExpr]

namespace State

mutual

partial def scalarProd (s:State) : Int × Var → IntExpr
| (m, ⟨0⟩) => m
| (m,  v) => IntExpr.mk (mkAppN intMulConst #[m, s.varExpr v])

-- | Map polynomial to expression given mapping from variables
-- to expressions.
-- The optional parameter allowss this to to only take the first n elements.
partial def polyExpr (s:State) (poly:Poly) (limit: optParam Nat (poly.elements.size)): IntExpr :=
  if limit = 0 then
    (0 : Int)
  else Id.run do
    let mut e := scalarProd s poly.elements[0]
    for p in poly.elements[1:limit] do
      e := e + scalarProd s p
    pure e

partial def varExpr (s:State) (v:Var) : IntExpr :=
  match s.varExprs.get! v.index.toNat with
  | Decl.uninterp e => IntExpr.mk e
  | Decl.poly p => polyExpr s p

end

def predExpr (s:State) : Pred → Expr
| Pred.IsEq0 v => mkIntEq0Expr (s.varExpr v)
| Pred.IsNe0 v => mkApp notExpr (mkIntEq0Expr (s.varExpr v))
| Pred.IsGe0 v => mkIntNonNegExpr (s.varExpr v)

-- | Add assertions to local context.
-- Return new local context along with array of free variables identifying assertions.
def addAssertions (s : State) (lctx:LocalContext) : MetaM (LocalContext × Array Expr) := do
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
    lctx := lctx.mkLocalDecl newVar a.name (s.predExpr a.prop)
  pure (lctx, fvars)

end State

abbrev ArithM  := StateRefT State MetaM

@[inline] def ArithM.run (m : ArithM α) (s : State := {}) : MetaM (α × State) :=
  StateRefT'.run m s

-- | Return a theory variable associated with the given uninterpreted Lean expression.
private def getDeclVar (d:Decl) : ArithM Var := do
  let s ← get
  match s.exprMap.find? d with
  | none => pure ()
  | some v => return v
  let newVar := ⟨OfNat.ofNat s.varExprs.size⟩
  IO.println s!"New variable: {newVar} := {d}"
  let newExprMap  := s.exprMap.insert d newVar
  let newVarExprs := s.varExprs.push d
  if (OfNat.ofNat s.varExprs.size : UInt32) = 0 then
    throwError m!"Only 2^32 arithmetic variables allowed."
  set { s with exprMap := newExprMap, varExprs := newVarExprs }
  return newVar

-- | Return a theory variable associated with the given uninterpreted Lean expression.
def getUninterpVar (e:Expr) : ArithM Var := getDeclVar (Decl.uninterp e)

-- | Return a theory variable associated with the given uninterpreted Lean expression.
def getPolyVar (p:Poly) : ArithM Var := getDeclVar (Decl.poly p)

-- | Assert a predicate holds using the given expression to refer to the
-- proof.
def assertPred (origin:Option FVarId) (userName:Name) (proof:Expr) (prop:Pred) : ArithM Unit := do
  let a := { origin := origin, name := userName, proof := proof, prop := prop }
  modifyGet fun s => ((), { s with assertions := s.assertions.push a })

def varExpr (v:Var) : ArithM IntExpr := do
  let s ← get
  pure $ s.varExpr v

def polyExpr (poly:Poly) : ArithM IntExpr := do
  let s ← get
  pure $ s.polyExpr poly

end ArithSolver