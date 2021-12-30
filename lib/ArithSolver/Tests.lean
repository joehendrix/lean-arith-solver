/-Tests cases for zify
-/
import ArithSolver.ToPoly

open ArithSolver

-- Structure for test cases to hide theorems from to_poly
structure Hide (P:Prop) := { value : P }

def test_false_goal (a b : Nat) (p:False) : False := by
  to_poly
  exact p

def test_nonneg_assumption (x y : Int) (p : Int.NonNeg (x + y)) (q: False) : False := by
  to_poly
  exact q

theorem test_le_goal  (x y:Nat) (p:Hide (¬Int.NonNeg (-1 + -1 * Int.ofNat y))) : Int.ofNat x ≤ Int.ofNat x + Int.ofNat y := by
  to_poly
  exact p.value negGoal


def test_eq_goal (x:Int) (p : Hide (-1 * y + 1 * x = 0)) : x = y := by
  to_poly
  exact (negGoal p.value)

def test_ne_goal (x:Int) (p : Hide (¬(-1 * y + 1 * x = 0))) : x ≠ y := by
  to_poly
  exact p.value negGoal

/-
-- TODO.  FIXME.  This runs forever
def test_eq_assumption (q:1 + 2 = 3): False := by
  to_poly
  admit
-/

/- TODO: Exlore additional test cases
def test_not_goal (a b : Nat) : ¬(a > b) := by
  to_poly

def test_nat_gt_goal (a b : Nat) : (a > b) := by
  to_poly

def test_nat_lt_goal (a b : Nat) : (a < b) := by
  to_poly

def test_nat_eq_goal (a b : Nat) : (a = b) := by
  to_poly
-/