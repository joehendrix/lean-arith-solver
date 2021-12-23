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

/-
protected
theorem sub_is_zero_of_le {m n : Nat} (p:m ≤ n) : m - n = 0 := by 
  revert m
  induction n with
  | zero => 
    intros m p
    cases m with
    | zero => exact (Nat.zero_sub _)
    | succ m => 
      cases p
  | succ n ind => 
    intros m p
    cases m with
    | zero => exact (Nat.zero_sub _)
    | succ m =>
      simp [succ_sub_succ]
      exact (ind (Nat.le_of_succ_le_succ p))
-/

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

theorem sub_sub_lassoc (x y z:Nat) : x - y - z = x - (y + z) := by
  admit

theorem sub_sub_rassoc (x:Nat) {y z:Nat} (p:y >= z) : x - (y - z) = x + z - y := by
  admit

theorem add_sub (x:Nat) {y z:Nat} (p:y >= z) : x + (y - z) = x + y - z := by
  admit

end Nat