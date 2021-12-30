/-
This module defines the state used to represent a system of linear integer equations
 and comparisons.
-/
import Std.Data.HashMap
import Lean.Meta
import ArithSolver.Array

open Lean (Expr FVarId Name)
open Std (HashMap)

namespace ArithSolver

-- | A variabe
structure Var where
  (index : UInt32)
  deriving BEq, Hashable, Repr

namespace Var

-- | "Variable" that denotes constant one.
protected def one : Var := ⟨0⟩

instance : OfNat Var 1 := ⟨Var.one⟩

protected def toString : Var → String
| ⟨0⟩ => "one"
| ⟨v⟩ => "v" ++ toString v

instance : ToString Var := ⟨Var.toString⟩

instance : Inhabited Var := ⟨Var.one⟩

instance : LT Var where
  lt a b := LT.lt a.index b.index

instance (a b : Var) : Decidable (LT.lt a b) :=
  inferInstanceAs (Decidable (LT.lt a.index b.index))

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
  deriving BEq, Hashable, Repr

namespace Poly

-- | Create polynomial denoting constant zero.
def zero : Poly := ⟨#[]⟩

instance : Inhabited Poly := ⟨zero⟩

-- | Create polynomial denoting constant zero.
def one : Poly := ⟨#[(1, Var.one)]⟩

-- | @add p i _ v@ returns poly denoting @p + i*v@.
def add : ∀(p:Poly) (m:Int), Var → Poly
| ⟨a⟩, q, v =>
  let rec loop : ∀(i : Nat), Poly
      | 0 => ⟨a.insertAt 0 (q, v)⟩
      | Nat.succ i =>
        let (p,u) := a[i]
        if u < v then
          ⟨a.insertAt (i+1) (q,v)⟩
        else if v < u then
          loop i
        else -- v = u
          let q := p+q
          if q = 0 then
            ⟨a.eraseIdx i⟩
          else
            ⟨a.set! i (q,v)⟩
  loop a.size

protected def toString : Poly → String
| ⟨a⟩ =>
  let scalarProd : Int × Var → String
        | (m,v) => s!"{m}*{v}"
  let firstScalarProd : Int × Var → String
        | (m, ⟨0⟩) => toString m
        | p => scalarProd p
  let polyIns := λ(e:String) h => s!"{e} + {scalarProd h}"
  a[1:].foldl polyIns (firstScalarProd a[0])

instance : ToString Poly where
  toString := Poly.toString

end Poly

-- | Assertion added
structure Assertion where
  -- Identifies the free variable in the initial context used to generate this one.
  -- Used to allow deleting original proposition from local context.
  origin : Option FVarId
  -- The free variable used to identify the assertion in the local context
  -- generated for the assertion.
  name : Name
  proof : Expr
  prop : Pred

-- def int1Lit : Expr := mkApp (mkConst ``Int.ofNat) (mkLit (Literal.natVal 1))

-- Definition associated with a variable.
inductive Decl
| uninterp : Expr → Decl
| poly : Poly → Decl
deriving BEq, Hashable

namespace Decl

protected def toString : Decl → String
| uninterp e => s!"uninterp {e}"
| poly p => s!"poly {p}"

instance : ToString Decl where
  toString := Decl.toString

instance : Inhabited Decl := ⟨uninterp arbitrary⟩

end Decl

structure State where
  -- Map from expressions (which should have type 'Int') to the theor
  -- variable associated with it.
  exprMap : HashMap Decl Var := Std.mkHashMap
  -- Map from variables (which should have type 'Int') to the expression
  -- associated with it.
  varExprs : Array Decl := #[Decl.poly Poly.one]
  -- Predicates asserted to be true.
  assertions : Array Assertion := #[]

namespace State

-- | Return proofs associated with assertions.
def proofs (s:State) : Array Expr := s.assertions.map Assertion.proof

end State

end ArithSolver