/-Tests cases for zify
-/
import ClausalExtraction.ToPoly

open ClausalExtraction

-- Structure for test cases to hide theorems from to_poly
structure Hide (P:Prop) := { value : P }

def test_false_goal (p:Hide False) : False := by
  to_poly
  exact p.value

def test_uninterp_goal (p:Hide False) : Hide True := by
  to_poly
  exact p.value

-- TODO: FIXME
--theorem test_le_nat_goal  (x y:Nat) (p:Hide (¬Int.NonNeg (-1 + -1 * y))) : x ≤ x + y := by
--  to_poly
--  exact p.value negGoal


theorem test_le_int_goal (x y:Int) (p:Hide (¬Int.NonNeg (-1 + -1 * y))) : x ≤ x + y := by
  to_poly
  exact p.value negGoal

def test_eq_goal (x:Int) (p : Hide (1 * x + -1 * y = 0)) : x = y := by
  to_poly
  exact (negGoal p.value)

def test_ne_goal (x:Int) (p : Hide (¬(x + -y = 0))) : x ≠ y := by
  to_poly
  simp only [Int.one_mul, Int.neg_one_mul] at negGoal
  exact p.value negGoal

def test_ground_goal : 1 + 2 = 3 := by
  to_poly
  contradiction

def test_ground_assumption (q:1 + 2 = 4): False := by
  to_poly
  contradiction

/- TODO: Exlore additional test cases
def test_not_goal (a b : Nat)
     (p:Hide (Int.NonNeg (1 * OfNat.ofNat a + -1 * OfNat.ofNat (b + 1))))
     : ¬(a > b) := by
  to_poly

def test_nat_gt_goal (a b : Nat) : (a > b) := by
  to_poly

def test_nat_lt_goal (a b : Nat) : (a < b) := by
  to_poly

def test_nat_eq_goal (a b : Nat) : (a = b) := by
  to_poly
-/