/-
This defines additional operations that could go into Lean's nat definitions.
-/
namespace Nat

protected
theorem zero_sub (n : Nat) : 0 - n = 0 := by
  induction n with
  | zero => rfl
  | succ n ind => simp [sub_succ, ind]

protected
theorem sub_is_zero_is_le {m n : Nat} : m ≤ n ↔ m - n = 0 := by
  revert m
  induction n with
  | zero =>
    intros m
    cases m with
    | zero =>
      simp [Nat.le.refl]
    | succ m =>
      simp
      intro p
      cases p
  | succ n ind =>
    intros m
    cases m with
    | zero =>
      simp [Nat.zero_sub, Nat.zero_le]
    | succ m =>
      simp [succ_sub_succ]
      apply Iff.intro
      case succ.succ.mp =>
        exact λp => ind.mp (Nat.le_of_succ_le_succ p)
      case succ.succ.mpr =>
        exact λp => Nat.succ_le_succ (ind.mpr p)

theorem lt_of_sub_succ {n m k:Nat} (p:n - m = Nat.succ k) : m < n := by
  revert n
  induction m with
  | zero =>
    intros n p
    simp at p
    simp [p]
    exact Nat.succ_le_succ (Nat.zero_le _)
  | succ m ind =>
    intros n p
    cases n with
    | zero =>
      simp [Nat.zero_sub] at p
    | succ n =>
      simp [succ_sub_succ] at p
      exact Nat.succ_lt_succ (ind p)


-- These theorems are intended to rewrite to a mixture of additions and
-- subtractions into one sum minus another sum.

theorem sub_sub_lassoc (x y z:Nat) : x - y - z = x - (y + z) := by
  revert y z
  induction x with
  | zero =>
    intro y z
    simp [Nat.zero_sub]
  | succ x ind =>
    intro y z
    match y with
    | 0 =>
      simp [Nat.sub_zero]
    | succ y =>
      simp [succ_sub_succ, succ_add]
      exact ind _ _

protected
theorem succ_sub {x y :Nat} (p:y ≤ x) : Nat.succ (x - y) = Nat.succ x - y := by
  revert x
  induction y with
  | zero =>
    intro x
    simp [Nat.sub_zero]
  | succ y ind =>
    intro x p
    match x with
    | 0 =>
      contradiction
    | succ x =>
      simp only [succ_sub_succ]
      apply ind (le_of_succ_le_succ p)

theorem sub_is_zero {m n:Nat} (p : m ≤ n) : m - n = 0 := by
  revert n
  induction m with
  | zero =>
    intro n p
    exact (Nat.zero_sub _)
  | succ m ind =>
    intro n p
    cases n with
    | zero =>
      contradiction
    | succ n =>
      rw [succ_sub_succ]
      exact ind (le_of_succ_le_succ p)

theorem sub_sub_rassoc (x:Nat) {y z:Nat} (p:y >= z) : x - (y - z) = x + z - y := by
  revert x y
  induction z with
  | zero =>
    intro x y p
    rfl
  | succ z ind =>
    intro x y p
    cases y with
    | zero =>
      contradiction
    | succ y =>
      simp only [Nat.add_succ, Nat.succ_sub_succ]
      exact ind _ (Nat.le_of_succ_le_succ p)

theorem sub_add_lassoc {x y:Nat} (p:x >= y) (z:Nat) : (x - y) + z = (x + z) - y := by
  revert x z
  induction y with
  | zero =>
    intro x p z
    rfl
  | succ y ind =>
    intro x p z
    cases x with
    | zero =>
      contradiction
    | succ x =>
      simp only [Nat.succ_add, Nat.succ_sub_succ]
      apply ind (Nat.le_of_succ_le_succ p)

theorem add_sub (x:Nat) {y z:Nat} (p:y >= z) : x + (y - z) = x + y - z := by
  simp only [Nat.add_comm x (y - z), sub_add_lassoc p, Nat.add_comm y x]

theorem mul_sub (x y z:Nat) : x * (y - z) = x * y - x * z := by
  cases Nat.lt_or_ge y z with
  | inl y_lt_z =>
    have g : y ≤ z := Nat.le_of_lt y_lt_z
    have h : x * y ≤ x * z := Nat.mul_le_mul_left x g
    simp [sub_is_zero g, sub_is_zero h]
  | inr y_ge_z =>
    induction x with
    | zero =>
      have h : ∀x, zero * x = 0 := Nat.zero_mul
      simp only [h]
    | succ x ind =>
      simp only [Nat.succ_mul, ind]
      have ge : x * y ≥ x * z := Nat.mul_le_mul_left x y_ge_z
      simp only [sub_add_lassoc ge]
      simp only [add_sub _ y_ge_z]
      simp only [sub_sub_lassoc, Nat.add_comm]

theorem add_sub_add_self (x y z : Nat) : (x + z) - (y + z) = x - y := by
  rw [Nat.add_comm y z, (Nat.sub_sub_lassoc _ _ _).symm]
  rw [(Nat.sub_sub_rassoc x (@Nat.le.refl z)).symm]
  rw [Nat.sub_self, Nat.sub_zero]

theorem succ_pred {x:Nat} (p:x > 0) : succ (pred x) = x := by
  cases x with
  | succ x => rfl
  | zero => contradiction

end Nat