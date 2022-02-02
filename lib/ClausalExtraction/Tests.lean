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


theorem test_int_le_goal (x y:Int) (p:Hide (¬Int.NonNeg (-1 + -1 * y))) : x ≤ x + y := by
  to_poly
  exact p.value negGoal

def test_int_eq_goal (x y:Int) (p : Hide (0 + 1 * x + -1 * y = 0)) : x = y := by
  to_poly
  exact (negGoal p.value)

def test_int_ne_goal (x y:Int) (p : Hide (¬(0 + x + -y = 0))) : x ≠ y := by
  to_poly
  simp only [Int.one_mul, Int.neg_one_mul] at negGoal
  exact p.value negGoal

def test_ground_goal : 1 + 2 = 3 := by
  to_poly
  contradiction

def test_ground_assumption (q:1 + 2 = 4): False := by
  to_poly
  contradiction

def test_nat_not_gt_goal (a b : Nat)
     (p:Hide (¬ Int.NonNeg (-1 + 1 * OfNat.ofNat a + -1 * OfNat.ofNat b)))
     : ¬(a > b) := by
  to_poly
  exact p.value negGoal

def test_nat_add_gt_goal (a b c : Nat)
     (p:Hide (¬ Int.NonNeg (0 + 1 * OfNat.ofNat c + -1 * OfNat.ofNat a + -1 * OfNat.ofNat b)))
     : a + b > c := by
  to_poly
  exact p.value negGoal

def test_nat_eq_goal (a b : Nat)
    (p:Hide (0 + 1 * OfNat.ofNat a + -1 * OfNat.ofNat b = 0))
    : (a = b) := by
  to_poly
  exact negGoal p.value