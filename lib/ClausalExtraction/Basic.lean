/-
This module defines the state used to represent a system of linear integer equations
 and comparisons.
-/
import Std.Data.HashMap
import Lean.Meta
import ClausalExtraction.Array

open Lean (Expr MetaM)
open Std (HashMap)

namespace ClausalExtraction

-- | A theory variable
structure TheoryVar where
  index : UInt32
  deriving BEq, Hashable, Repr

namespace TheoryVar

protected def ofNat (n:Nat) :TheoryVar := ⟨UInt32.ofNat n⟩

protected def toNat (v:TheoryVar) : Nat := v.index.toNat

instance : Inhabited TheoryVar := ⟨⟨0⟩⟩

protected def toString (v:TheoryVar) : String := "v" ++ toString v.index

instance : ToString TheoryVar where
  toString := TheoryVar.toString

instance : LT TheoryVar where
  lt a b := LT.lt a.index b.index

instance (a b : TheoryVar) : Decidable (LT.lt a b) :=
  inferInstanceAs (Decidable (LT.lt a.index b.index))

end TheoryVar

-- | A theory predicate
structure TheoryPred where
  index : UInt32

namespace TheoryPred

def ofNat (n:Nat) : TheoryPred := ⟨UInt32.ofNat n⟩

def toNat (p:TheoryPred) : Nat := p.index.toNat

def max : Nat := UInt32.size

protected def toString (v:TheoryPred) : String := "p" ++ toString v.index

instance : ToString TheoryPred := ⟨TheoryPred.toString⟩

end TheoryPred

-- | A reference to a solver for a specific theory.
structure TheoryRef where
  index : UInt8
  deriving DecidableEq

namespace TheoryRef

protected def ofNat (n:Nat) : TheoryRef := ⟨UInt8.ofNat n⟩

protected def toNat (r:TheoryRef) : Nat := r.index.toNat

protected def max : TheoryRef := ⟨16⟩
protected def uninterpreted : TheoryRef := ⟨0⟩

protected def toString (v:TheoryRef) : String := "t" ++ toString v.index

instance : ToString TheoryRef := ⟨TheoryRef.toString⟩

end TheoryRef

-- | A variable that is a theory variable in a specific theory.
structure Var where
  (index : UInt64)
  deriving BEq, Hashable, Inhabited, Repr

namespace Var

protected def mkVar (t:TheoryRef) (r:TheoryVar) : Var :=
  ⟨OfNat.ofNat (r.index <<< (4:UInt32)).toNat ||| OfNat.ofNat t.index.toNat⟩

protected def theory (v:Var) : TheoryRef := ⟨OfNat.ofNat (v.index &&& 0xf).toNat⟩

protected def theoryVar (p:Var) : TheoryVar := ⟨OfNat.ofNat (p.index >>> (4:UInt64)).toNat⟩

protected def toString (v:Var) : String :=
  toString (v.theoryVar) ++ ":" ++ toString (v.theory)

instance : ToString Var := ⟨Var.toString⟩

instance : LT Var where
  lt a b := LT.lt a.index b.index

instance (a b : Var) : Decidable (LT.lt a b) :=
  inferInstanceAs (Decidable (LT.lt a.index b.index))

end Var

structure Pred where
  index : UInt64
  deriving Inhabited

namespace Pred

protected def mkPred (t:TheoryRef) (r:TheoryPred) : Pred :=
  ⟨OfNat.ofNat (r.index <<< (4:UInt32)).toNat ||| OfNat.ofNat t.index.toNat⟩

def theory (p:Pred) : TheoryRef := ⟨OfNat.ofNat (p.index &&& 0xf).toNat⟩

def theoryPred (p:Pred) : TheoryPred := ⟨OfNat.ofNat (p.index >>> (4:UInt64)).toNat⟩

protected def toString (p:Pred) : String :=
  toString (p.theoryPred) ++ ":" ++ toString (p.theory)

instance : ToString Pred := ⟨Pred.toString⟩

end Pred

-- A variable, expression and equality proof returned from
-- creating a variable.
structure VarDefinition (α:Type) where
  -- The value identifying the variable.
  var : α
  -- The expression that the variable will evaluate to.
  varExpr : Expr
  -- An equality proof showing the variable is equivalent to the
  -- original expression.
  eq : Expr

structure TheoryOps where
  varExpr : (Var → IO Expr) → TheoryVar → IO Expr
  predExpr : (Var → IO Expr) → TheoryPred → IO Expr
  deriving Inhabited

/-
This defines an abstract interface used to define theory-specific
transformations.

-/
structure SolverServices where
  -- Return the expression associated with a variable.
  varExpr {} : Var → IO Expr
  -- Return a variable associated with an expression that is not
  -- interpeted by the current theory.
  exprVar {} : Expr → MetaM (VarDefinition Var)
  deriving Inhabited

abbrev SolverM := ReaderT SolverServices MetaM

def getVarForExpr (e:Expr) : SolverM (VarDefinition Var) := do
  (← read).exprVar e

@[reducible]
def TermRecognizer := Expr → SolverM (VarDefinition TheoryVar)

structure TermRecognizerPair where
  theoryRef : TheoryRef
  function : TermRecognizer

namespace TermRecognizerPair

instance : BEq TermRecognizerPair where
  beq := fun x y => false

end TermRecognizerPair

-- | A rule that given a proposition, tries to produce a predicate
-- and a function expression that transforms proofs of the original
-- proposition into proofs of the predicate.
structure  PredRule where
  theoryRef : TheoryRef
  action : Expr → SolverM (Option (TheoryPred × Expr))

namespace PredRule

instance : BEq PredRule where
  beq := fun x y => false

end PredRule



end ClausalExtraction