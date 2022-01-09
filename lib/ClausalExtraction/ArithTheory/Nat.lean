/-
This defines additional operations that could go into Lean's nat definitions.
-/
namespace Nat

theorem succ_pred {x:Nat} (p:x > 0) : succ (pred x) = x := by
  cases x with
  | succ x => rfl
  | zero => contradiction

section BasicSubtraction

protected
theorem zero_sub (n : Nat) : 0 - n = 0 := by
  induction n with
  | zero => rfl
  | succ n ind => simp [sub_succ, ind]

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

end BasicSubtraction

section BasicLe

theorem succ_le_zero (m:Nat) : succ m ≤ 0 ↔ False :=
  Iff.intro (not_succ_le_zero m) False.elim

theorem succ_le_succ_simp (m n:Nat) : succ m ≤ succ n ↔ m ≤ n :=
  Iff.intro le_of_succ_le_succ succ_le_succ

theorem succ_le_pred (m n:Nat) : succ m ≤ pred n ↔ succ (succ m) ≤ n :=
  match n with
  | 0 => by
    simp only [succ_le_zero, pred]
  | succ n => by
    simp only [pred, succ_le_succ_simp, iff_self]

theorem succ_le_sub (m n p:Nat) : succ m ≤ n - p ↔ succ (m + p) ≤ n := by
  revert m n
  have h : zero = 0 := rfl
  induction p with
  | zero =>
    intro m n
    simp only [h, Nat.sub_zero, Nat.add_zero]
    apply Iff.intro id id
  | succ p ind =>
    intro m n
    cases n with
    | zero =>
      simp only [h, Nat.zero_sub, succ_le_zero]
    | succ n =>
      rw [succ_sub_succ, succ_le_succ_simp]
      apply ind

protected
theorem sub_is_zero_is_le (m n : Nat) : m - n = 0 ↔ m ≤ n := by
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
      simp [ind, succ_le_succ_simp]

protected
theorem sub_is_zero {m n:Nat} (p : m ≤ n) : m - n = 0 :=
  (Nat.sub_is_zero_is_le _ _).mpr p

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

end BasicLe


-- These theorems are intended to rewrite to a mixture of additions and
-- subtractions into one sum minus another sum.
section SubAddRewriting

protected
theorem sub_sub_left (x y z:Nat) : (x - y) - z = x - (y + z) := by
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
theorem sub_sub_right {y z:Nat} (p:y >= z) (x:Nat) : x - (y - z) = (x + z) - y := by
  revert x y
  induction z with
  | zero =>
    intro y p x
    rfl
  | succ z ind =>
    intro y p x
    cases y with
    | zero =>
      contradiction
    | succ y =>
      simp only [Nat.add_succ, Nat.succ_sub_succ]
      exact ind (Nat.le_of_succ_le_succ p) _

protected
theorem add_sub_left {x y:Nat} (p:x >= y) (z:Nat) : (x - y) + z = (x + z) - y := by
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

protected
theorem add_sub_right {y z:Nat} (p:y >= z) (x:Nat) : x + (y - z) = x + y - z := by
  simp only [Nat.add_comm x (y - z), Nat.add_sub_left p, Nat.add_comm y x]

protected
theorem mul_sub (x y z:Nat) : x * (y - z) = x * y - x * z := by
  cases Nat.lt_or_ge y z with
  | inl y_lt_z =>
    have g : y ≤ z := Nat.le_of_lt y_lt_z
    have h : x * y ≤ x * z := Nat.mul_le_mul_left x g
    simp only [Nat.sub_is_zero g, Nat.sub_is_zero h, Nat.mul_zero]
  | inr y_ge_z =>
    induction x with
    | zero =>
      have h : ∀x, zero * x = 0 := Nat.zero_mul
      simp only [h]
    | succ x ind =>
      simp only [Nat.succ_mul, ind]
      have ge : x * y ≥ x * z := Nat.mul_le_mul_left x y_ge_z
      simp only [Nat.add_sub_left ge]
      simp only [Nat.add_sub_right y_ge_z]
      simp only [Nat.sub_sub_left, Nat.add_comm]

end SubAddRewriting

protected
theorem add_sub_add_self (x y z : Nat) : (x + z) - (y + z) = x - y := by
  rw [Nat.add_comm y z, (Nat.sub_sub_left _ _ _).symm]
  rw [(Nat.sub_sub_right (@Nat.le.refl z) x).symm]
  rw [Nat.sub_self, Nat.sub_zero]

protected
theorem le_sub_simp {n p:Nat} (g:n ≥ p) (m:Nat) : m ≤ n - p ↔ m + p ≤ n := by
  simp only [(Nat.sub_is_zero_is_le _ _).symm]
  simp only [Nat.sub_sub_right g, iff_self]

protected
theorem sub_le_simp (m n p:Nat) : m - n ≤ p ↔ m ≤ n + p := by
  simp only [(Nat.sub_is_zero_is_le _ _).symm]
  simp only [Nat.sub_sub_left, iff_self]

protected
theorem sub_lt_simp {m n:Nat} (a:m ≥ n) (p:Nat) : m - n < p ↔ m < n + p := by
  have lt_is_le : ∀(x y:Nat), x < y ↔ Nat.succ x ≤ y := fun x y => Iff.intro id id
  simp only [lt_is_le, Nat.succ_sub a]
  simp only [Nat.sub_le_simp, iff_self]

end Nat