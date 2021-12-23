import Std.Data.HashMap
import Lean.Meta

open Lean
open Std (HashMap)

namespace ArithSolver

def notExpr : Expr := mkConst ``Not

def mkIntEq0Expr (e:Expr) : Expr :=
  let intZeroExpr : Expr := mkApp (mkConst ``Int.ofNat) (mkLit (Literal.natVal 0))
  mkAppN (mkConst ``Eq [levelOne]) #[mkConst ``Int, e, intZeroExpr]

def intNonNegExpr : Expr := mkConst ``Int.NonNeg

def mkIntNonNegExpr (e:Expr) : Expr := mkApp intNonNegExpr e

structure Var where
  (index : UInt32)
  deriving BEq, Hashable

namespace Var

instance : ToString Var := ⟨λv => toString v.index⟩

end Var

-- | An atomic predicate
inductive Pred where
-- This denotes a proof of the form (v = 0)
| IsEq0 : Var → Pred
-- This denotes a proof of the form (Not (v = 0))
| IsNe0 : Var → Pred
-- This denotes a proof of the form (Int.NonNeg v)
| IsGe0 : Var → Pred

-- Represents a polynomial.
structure Poly where
  -- Poly should be a sorted array of non-zero integers and variable pairs.
  -- The
  elements : Array (Int × Var)

-- | Identifies the origin of an assertion
inductive Origin
-- | A local context with the given name, user name and the new name.
| localContext : FVarId → Name → FVarId → Origin
| negGoal : FVarId → Origin
| uninterpNat : Origin

structure Assertion where
  origin : Origin
  proof : Expr
  prop : Pred

def int1Lit : Expr := mkApp (mkConst ``Int.ofNat) (mkLit (Literal.natVal 1))

structure State where
  -- Map from expressions (which should have type 'Int') to the theor
  -- variable associated with it.
  exprMap : HashMap Expr Var := Std.mkHashMap
  -- Map from variables (which should have type 'Int') to the expression
  -- associated with it.
  varExprs : Array Expr := #[int1Lit]
  -- Predicates asserted to be true.
  assertions : Array Assertion := #[]

namespace State

def varExpr (s:State) (v:Var) : Expr := s.varExprs.get! v.index.toNat

def predExpr (s:State) : Pred → Expr
| Pred.IsEq0 v => mkIntEq0Expr (s.varExpr v)
| Pred.IsNe0 v => mkApp notExpr (mkIntEq0Expr (s.varExpr v))
| Pred.IsGe0 v => mkIntNonNegExpr (s.varExpr v)

end State

abbrev ArithM  := StateRefT State MetaM

@[inline] def ArithM.run (m : ArithM α) (s : State := {}) : MetaM (α × State) :=
  StateRefT'.run m s

-- | Return a theory variable associated with the given uninterpreted Lean expression.
def getUninterpVar (e:Expr) : ArithM Var := do
  let s ← get
  match s.exprMap.find? e with
  | none => pure ()
  | some v => return v
  let newVar := ⟨OfNat.ofNat s.varExprs.size⟩
  let newExprMap  := s.exprMap.insert e newVar
  let newVarExprs := s.varExprs.push e
  if (OfNat.ofNat s.varExprs.size : UInt32) = 0 then
    throwError m!"Arithmetic variable overflow."
  set { s with exprMap := newExprMap, varExprs := newVarExprs }
  return newVar


-- | Assert a predicate holds using the given expression to refer to the
-- proof.
def assertPred (origin:Origin) (proof:Expr) (prop:Pred) : ArithM Unit := do
  let a := { origin := origin, proof := proof, prop := prop }
  modifyGet fun s => ((), { s with assertions := s.assertions.push a })

end ArithSolver