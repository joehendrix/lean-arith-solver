/-
This defines additional operations used to normalize inequalitis.
-/
import ClausalExtraction.ArithTheory.Nat

namespace Int

-- Thoems only about subNatNat and nat-level operations
-- We make these private as the intention is that users should not need to directly
-- work with subNatNat
section subNatNat

private
theorem subNatNat.is_ofNat {x y:Nat} (p:y ≤ x) : subNatNat x y = ofNat (x - y) := by
  simp [subNatNat]
  have h : y - x = 0 := by simp only [Nat.sub_is_zero_is_le, p]
  simp [h]

private theorem subNatNat.is_negSucc {x y:Nat} (p:x < y) : subNatNat x y = negSucc (y - Nat.succ x) := by
  generalize g: y - x = y_sub_x
  cases y_sub_x with
  | zero =>
    have h : Nat.zero = 0 := rfl
    simp only [h, Nat.sub_is_zero_is_le] at g
    exact (False.elim (Nat.not_le_of_gt p g))
  | succ y_sub_x =>
    simp only [subNatNat, g, Nat.sub_succ, Nat.pred]

private
theorem succ_subNatNat_succ (x y : Nat) : subNatNat (Nat.succ x) (Nat.succ y) = subNatNat x y := by
  match Nat.lt_or_ge x y with
  | Or.inr p =>
    have q := Nat.succ_le_succ p
    simp [subNatNat.is_ofNat, p, q, Nat.succ_sub_succ]
  | Or.inl p =>
    have q := Nat.succ_lt_succ p
    simp [subNatNat.is_negSucc, p, q, Nat.succ_sub_succ]

private
theorem subNatNat_self (x:Nat) : subNatNat x x = 0 := by
  induction x with
  | zero => rfl
  | succ x ind => simp [succ_subNatNat_succ, ind]

private
theorem subNatNat_zero (x : Nat) : subNatNat x 0 = ofNat x := by
  simp [subNatNat.is_ofNat, Nat.zero_le]

private
theorem zero_subNatNat_succ (x:Nat) : subNatNat 0 (Nat.succ x) = Int.negSucc x := by
  simp [subNatNat.is_negSucc, Nat.zero_lt_succ, Nat.succ_sub_succ, Nat.sub_zero]

private
theorem subNatNat_sub_lhs (p : x ≥ y) (z:Nat) : subNatNat (x - y) z = subNatNat x (y + z) := by
  match Nat.lt_or_ge x (y+z) with
  | Or.inr q =>
    have r : x - y ≥ z := by simp only [Nat.le_sub_simp p, Nat.add_comm]; exact q
    simp only [subNatNat.is_ofNat q, subNatNat.is_ofNat r]
    simp only [Nat.sub_sub_left]
  | Or.inl q =>
    have r : x - y < z := by simp only [Nat.sub_lt_simp p]; exact q
    simp only [subNatNat.is_negSucc q, subNatNat.is_negSucc r]
    simp only [negSucc.injEq, Nat.sub_succ]
    simp only [Nat.sub_sub_right p]
    rw [Nat.add_comm z y]

private
theorem subNatNat_sub {y z :Nat} (p : z ≤ y) (x:Nat) : subNatNat x (y - z) = subNatNat (x + z) y := by
  match Nat.lt_or_ge (x+z) y with
  | Or.inr q =>
    have r : y - z ≤ x := by
      simp only [Nat.sub_le_simp, Nat.add_comm z x]
      exact q
    simp only [subNatNat.is_ofNat q, subNatNat.is_ofNat r]
    simp only [Nat.sub_sub_right p]
  | Or.inl q =>
    have r : Nat.succ x ≤ y - z := by
      simp only [Nat.le_sub_simp, p, Nat.succ_add]
      exact q
    simp only [subNatNat.is_negSucc q, subNatNat.is_negSucc r, Nat.sub_succ]
    simp only [Nat.sub_sub_left, Nat.add_comm]

private
theorem subNatNat_zero_implies_equal {x y :Nat} (q:Int.subNatNat x y = 0) : x = y := by
  simp [Int.subNatNat] at q
  have p : y - x = 0 := by
    generalize g:y-x=z
    cases z with
    | zero => rfl
    | succ z => simp [g] at q
  simp only [OfNat.ofNat, p, ofNat.injEq] at q
  revert y
  induction x with
  | zero =>
    intros y p q
    exact p.symm
  | succ x ind =>
    intros y
    cases y with
    | zero =>
      intros p q
      simp [Nat.sub_zero] at q
    | succ y =>
      simp [Nat.succ_sub_succ]
      exact (@ind y)

private
theorem subNatNat_eq_zero (x y :Nat) : (Int.subNatNat x y = 0) = (x = y) := by
  apply propext
  apply Iff.intro subNatNat_zero_implies_equal
  intro eq
  simp only [eq, subNatNat_self]

private
theorem nonNeg_subNatNat (m n : Nat) : NonNeg (subNatNat m n) = (n <= m) := by
  apply propext
  apply Iff.intro
  case a.mp =>
    intro p
    match Nat.lt_or_ge m n with
    | Or.inr q =>
      exact q
    | Or.inl q =>
      simp [subNatNat.is_negSucc q] at p
      contradiction
  case a.mpr =>
    intro le
    simp [subNatNat.is_ofNat le]
    exact (NonNeg.mk _)


end subNatNat

section Addition

private theorem ofNat_add_ofNat (m n : Nat) : ofNat m + ofNat n = ofNat (m + n) := by rfl

private theorem ofNat_add_negSucc (m n : Nat) : ofNat m + negSucc n = subNatNat m (Nat.succ n) := by rfl

private theorem negSucc_add_ofNat (m n : Nat) : negSucc m + ofNat n = subNatNat n (Nat.succ m) := by rfl

private theorem negSucc_add_negSucc (m n : Nat) : negSucc m + negSucc n = negSucc (Nat.succ (m + n)) := by rfl

@[simp]
theorem zero_add (x : Int) : 0 + x = x :=
  match x with
  | ofNat n => congrArg ofNat (Nat.zero_add _)
  | negSucc n => rfl

@[simp]
theorem add_zero (x : Int) : x + 0 = x :=
  match x with
  | ofNat n => Eq.refl (ofNat n)
  | negSucc n => Eq.refl (negSucc n)

theorem add_comm (x y : Int) : x + y = y + x := by
  cases x <;> cases y <;> simp only
    [ofNat_add_ofNat, ofNat_add_negSucc,
     negSucc_add_ofNat, negSucc_add_negSucc,
     Nat.add_comm]

private
theorem ofNat_add_subNatNat (x y z:Nat)
  : ofNat x + subNatNat y z = subNatNat (x + y) z := by
    match Nat.lt_or_ge y z with
    | Or.inl p =>
      rw [subNatNat.is_negSucc p, ofNat_add_negSucc, Nat.succ_sub p, Nat.succ_sub_succ]
      exact (subNatNat_sub (Nat.le_of_lt p) _)
    | Or.inr p =>
      have q : x + y ≥ z := Nat.le_trans p (Nat.le_add_left y x)
      rw [subNatNat.is_ofNat p, ofNat_add_ofNat]
      rw [subNatNat.is_ofNat q, ofNat.injEq]
      exact (Nat.add_sub_right p _)

private
theorem subNatNat_add_ofNat (x y z:Nat) : subNatNat x y + ofNat z = subNatNat (x + z) y := by
  simp only [add_comm, ofNat_add_subNatNat, Nat.add_comm]

private
theorem negSucc_add_subNatNat (x y z:Nat) : negSucc x + subNatNat y z = subNatNat y (Nat.succ (x + z)) := by
  match Nat.lt_or_ge y z with
  | Or.inr p =>
    rw [subNatNat.is_ofNat p, negSucc_add_ofNat]
    simp only [subNatNat_sub_lhs p, Nat.add_succ, Nat.add_comm]
  | Or.inl p =>
    rw [subNatNat.is_negSucc p, negSucc_add_negSucc]
    have r : y < x + z := Nat.le_trans p (Nat.le_add_left z x)
    have q : y < Nat.succ (x + z) := Nat.le.step r
    rw [subNatNat.is_negSucc q, negSucc.injEq]
    rw [Nat.add_sub_right p]
    rw [Nat.succ_sub r]

private
theorem subNatNat_add_negSucc (x y z:Nat)
  : subNatNat x y + negSucc z = subNatNat x (Nat.succ (y + z)) := by
  simp only [add_comm, negSucc_add_subNatNat, Nat.add_comm]

private theorem subNatNat_add_subNatNat (a b c d:Nat)
  : subNatNat a b + subNatNat c d = subNatNat (a + c) (b + d) := by
  match Nat.lt_or_ge a b with
  | Or.inr a_ge_b =>
    simp only [subNatNat.is_ofNat a_ge_b]
    match Nat.lt_or_ge c d with
    | Or.inr c_ge_d =>
      have ge : a + c ≥ b + d := Nat.add_le_add a_ge_b c_ge_d
      rw [subNatNat.is_ofNat c_ge_d, subNatNat.is_ofNat ge]
      rw [ofNat_add_ofNat, ofNat.injEq]
      rw [Nat.add_sub_left a_ge_b]
      rw [Nat.add_sub_right c_ge_d]
      simp only [Nat.sub_sub_left, Nat.add_comm]
    | Or.inl c_lt_d =>
      simp only [subNatNat.is_negSucc c_lt_d]
      simp only [ofNat_add_negSucc]
      simp only [Nat.succ_sub c_lt_d, Nat.succ_sub_succ]
      simp only [subNatNat_sub (Nat.le_of_lt c_lt_d)]
      simp only [Nat.add_sub_left a_ge_b]
      have ac_ge_b : a+c ≥ b := Nat.le_trans a_ge_b (Nat.le_add_right a c)
      simp only [subNatNat_sub_lhs ac_ge_b]
  | Or.inl a_lt_b =>
    simp only [subNatNat.is_negSucc a_lt_b]
    match Nat.lt_or_ge c d with
    | Or.inr c_ge_d =>
      simp only [subNatNat.is_ofNat c_ge_d, negSucc_add_ofNat]
      simp only [Nat.succ_sub a_lt_b, Nat.succ_sub_succ]
      simp only [subNatNat_sub_lhs c_ge_d]
      simp only [Nat.add_sub_right (Nat.le_of_lt a_lt_b)]
      have db_ge_a : d + b >= a :=
             Nat.le_trans (Nat.le_of_lt a_lt_b) (Nat.le_add_left b d)
      simp only [subNatNat_sub db_ge_a]
      simp only [Nat.add_comm]
    | Or.inl c_lt_d =>
      have lt : a + c < b + d := Nat.add_lt_add a_lt_b c_lt_d
      simp only [subNatNat.is_negSucc c_lt_d, subNatNat.is_negSucc lt]
      rw [negSucc_add_negSucc, negSucc.injEq]
      simp only [Nat.add_sub_left a_lt_b]
      simp only [Nat.add_sub_right c_lt_d]
      simp only [Nat.sub_sub_left, Nat.succ_add, Nat.add_succ, Nat.add_comm c a]
      rw [Nat.sub_succ, Nat.sub_succ]
      have gt1 : Nat.pred (b + d - (a + c)) > 0 := by
            apply Nat.lt_of_succ_le
            simp only [Nat.succ_le_pred, Nat.succ_le_sub, Nat.succ_add, Nat.zero_add]
            rw [(Nat.add_succ _ c).symm, (Nat.succ_add a _).symm]
            exact Nat.add_le_add a_lt_b c_lt_d
      simp only [Nat.succ_pred gt1]

theorem add_assoc (x y z : Int) : x + y + z = x + (y + z) := by
  cases x <;> cases y <;> cases z <;>  simp only
    [ofNat_add_ofNat, ofNat_add_negSucc, negSucc_add_ofNat, negSucc_add_negSucc,
      ofNat_add_subNatNat, subNatNat_add_ofNat,
      subNatNat_add_negSucc, negSucc_add_subNatNat,
      Nat.succ_add, Nat.add_succ, Nat.add_assoc]

end Addition

-- Just desugar negOfNat into subNatNat
section negOfNat

private
theorem negOfNat_is_subNatNat (x:Nat) : negOfNat x = subNatNat 0 x := by
  cases x with
  | zero => rfl
  | succ x => rfl

end negOfNat

section Negation

@[simp]
theorem neg_zero : - (0:Int) = 0 := by rfl

private
theorem neg_ofNat (n:Nat) : -ofNat n = subNatNat 0 n := negOfNat_is_subNatNat n

private
theorem neg_negSucc (n:Nat) : -negSucc n = ofNat (n+1) := by rfl

private
theorem neg_subNatNat (m n: Nat) : - (subNatNat m n) = subNatNat n m := by
  match Nat.lt_or_ge m n with
  | Or.inl p =>
    have q : m ≤ n := Nat.le_of_lt p
    simp only [subNatNat.is_negSucc p, subNatNat.is_ofNat q, neg_negSucc]
    simp only [Nat.add_sub_left p, Nat.succ_sub_succ]
  | Or.inr p =>
    simp only [subNatNat.is_ofNat p, neg_ofNat]
    simp only [subNatNat_sub p, Nat.zero_add]

theorem neg_add (x y : Int) : -(x + y) = -x + -y := by
  cases x <;> cases y <;> simp only
         [ofNat_add_ofNat, ofNat_add_negSucc, negSucc_add_ofNat, negSucc_add_negSucc,
          neg_ofNat, neg_negSucc,
          subNatNat_add_subNatNat, subNatNat_add_ofNat, ofNat_add_subNatNat,
          neg_subNatNat,
          Nat.zero_add, Nat.add_zero, Nat.add_succ, Nat.succ_add]

end Negation

section Subtraction

theorem sub_to_add_neg (x : Int) : x - y = x + -y := by rfl

theorem sub_self (x : Int) : x - x = 0 := by
  simp only [sub_to_add_neg]
  cases x with
  | ofNat x =>
    simp only [neg_ofNat, negOfNat_is_subNatNat, ofNat_add_subNatNat, Nat.add_zero,
               subNatNat_self]
  | negSucc x =>
    simp only [neg_negSucc, negSucc_add_ofNat, Nat.add_succ, Nat.add_zero,
               subNatNat_self]

theorem sub_eq_zero_implies_eq {x y : Int} (q : x - y = 0) : x = y := by
  cases x with
  | ofNat x =>
    cases y with
    | ofNat y =>
      simp only [sub_to_add_neg, neg_ofNat, ofNat_add_subNatNat, Nat.add_zero, subNatNat_eq_zero] at q
      simp only [q]
    | negSucc y =>
      simp only [sub_to_add_neg, neg_negSucc, ofNat_add_ofNat] at q
      simp only [Nat.add_succ, OfNat.ofNat, ofNat.injEq] at q
  | negSucc x =>
    cases y with
    | ofNat y =>
      simp only [sub_to_add_neg, neg_ofNat, negSucc_add_subNatNat, subNatNat_eq_zero] at q
    | negSucc y =>
      simp only [sub_to_add_neg, neg_negSucc, negSucc_add_ofNat, succ_subNatNat_succ,
                 subNatNat_eq_zero] at q
      simp only [q]

end Subtraction

protected theorem lt_or_ge (x y : Int) : x < y ∨ x ≥ y := by
  have h : -1 = Int.negSucc 0 := rfl
  have succ_le : ∀(a b), (Nat.succ a ≤ b) = (a < b) := by
        intros a b
        exact propext (Iff.intro id id)
  simp only [LT.lt, Int.lt, LE.le, GE.ge, Int.le, sub_to_add_neg, neg_add, h]
  cases x <;> cases y <;> simp only
    [ neg_ofNat, neg_negSucc,
      ofNat_add_ofNat, ofNat_add_negSucc, ofNat_add_subNatNat,
      negSucc_add_ofNat, negSucc_add_subNatNat, subNatNat_add_negSucc,
      NonNeg.mk,
      succ_subNatNat_succ, subNatNat_zero,
      Nat.add_zero, Nat.add_succ,
      nonNeg_subNatNat, succ_le, Nat.lt_or_ge,
      or_true, true_or
    ]

section Multiplication

private theorem ofNat_mul_ofNat (m n : Nat) : ofNat m * ofNat n = ofNat (m * n) := by rfl

private theorem ofNat_mul_negSucc (m n : Nat) : ofNat m * negSucc n = subNatNat 0 (m * Nat.succ n) :=
  negOfNat_is_subNatNat (m * Nat.succ n)

private theorem negSucc_mul_ofNat (m n : Nat) : negSucc m * ofNat n = subNatNat 0 (Nat.succ m * n) :=
  negOfNat_is_subNatNat (Nat.succ m * n)

private theorem negSucc_mul_negSucc (m n : Nat) : negSucc m * negSucc n = ofNat (Nat.succ m * Nat.succ n) := by rfl

theorem zero_mul (x:Int) : 0 * x = 0 := by
  simp only [OfNat.ofNat]
  cases x <;> simp only [ofNat_mul_ofNat, ofNat_mul_negSucc, Nat.zero_mul]

theorem one_mul (x:Int) : 1 * x = x := by
  simp only [OfNat.ofNat]
  cases x <;> simp only [ofNat_mul_ofNat, ofNat_mul_negSucc, Nat.one_mul, zero_subNatNat_succ]

theorem mul_comm (x y : Int) : x * y = y * x := by
  cases x <;> cases y <;> simp only
    [ ofNat_mul_ofNat, ofNat_mul_negSucc, negSucc_mul_ofNat, negSucc_mul_negSucc,
      Nat.mul_comm
    ]

theorem mul_zero (x : Int) : x * 0 = 0 := by simp [mul_comm x 0, zero_mul]

theorem mul_one (x : Int) : x * 1 = x := by simp [mul_comm x 1, one_mul]

private
theorem ofNat_mul_subNatNat (x y z : Nat) : ofNat x * subNatNat y z = subNatNat (x * y) (x * z) :=
  match Nat.lt_or_ge y z with
  | Or.inr p => by
    have q : x*y ≥ x*z := Nat.mul_le_mul_left x p
    simp only [subNatNat.is_ofNat, p, q, ofNat_mul_ofNat, Nat.mul_sub ]
  | Or.inl p =>
    match Nat.eq_zero_or_pos x with
    | Or.inl x_eq_zero => by
      simp only [x_eq_zero, Nat.zero_mul]
      exact zero_mul (subNatNat y z)
    | Or.inr x_pos => by
      have q : x*y < x*z := Nat.mul_lt_mul_of_pos_left p x_pos
      simp only [subNatNat.is_negSucc p, subNatNat.is_negSucc q, ofNat_mul_negSucc]
      have r : x * z ≥ (x * y + x) := by
        simp only [(Nat.mul_succ x y).symm]
        exact Nat.mul_le_mul_left x p
      simp only [
        Nat.add_sub_left r,
        Nat.mul_succ, Nat.mul_sub,  Nat.add_sub_add_self ]
      rw [subNatNat_sub (Nat.le_of_lt q), Nat.zero_add, subNatNat.is_negSucc q]

private
theorem negSucc_mul_subNatNat (x y z : Nat) : negSucc x * subNatNat y z = subNatNat (Nat.succ x * z) (Nat.succ x * y) :=
  match Nat.lt_or_ge y z with
  | Or.inr p => by
    have q : Nat.succ x*y ≥ Nat.succ x*z := Nat.mul_le_mul_left (Nat.succ x) p
    simp only [subNatNat.is_ofNat, p, q]
    simp only [negSucc_mul_ofNat, Nat.mul_sub]
    simp only [subNatNat_sub q, Nat.zero_add]
  | Or.inl p => by
    have q : Nat.succ x*y < Nat.succ x*z := Nat.mul_lt_mul_of_pos_left p (Nat.zero_lt_succ x)
    simp only [subNatNat.is_negSucc p, subNatNat.is_ofNat (Nat.le_of_lt q)]
    simp only [negSucc_mul_negSucc, Nat.succ_sub p, Nat.succ_sub_succ]
    simp only [Nat.mul_sub]

private
theorem subNatNat_mul_ofNat (x y z : Nat) : subNatNat x y * ofNat z = subNatNat (x * z) (y * z) := by
  simp [mul_comm, ofNat_mul_subNatNat, Nat.mul_comm]

private
theorem subNatNat_mul_negSucc (x y z : Nat) : subNatNat x y * negSucc z = subNatNat (y * Nat.succ z) (x * Nat.succ z)  := by
  simp [mul_comm, negSucc_mul_subNatNat, Nat.mul_comm]

theorem neg_one_mul (x:Int) : -1 * x = -x := by
  simp only [OfNat.ofNat]
  have h : Nat.succ 0 = 1 := rfl
  cases x <;> simp only
    [neg_ofNat, negSucc_mul_ofNat, negSucc_mul_negSucc, h, neg_negSucc,
     subNatNat_mul_ofNat, subNatNat_mul_negSucc,
     Nat.zero_mul, Nat.one_mul, subNatNat_zero
     ]

theorem mul_assoc (x y z : Int) : x * y * z = x * (y * z) := by
  cases x <;> cases y <;> cases z <;> simp only
    [ ofNat_mul_ofNat, ofNat_mul_negSucc, negSucc_mul_ofNat, negSucc_mul_negSucc,
      ofNat_mul_subNatNat, subNatNat_mul_ofNat,
      negSucc_mul_subNatNat, subNatNat_mul_negSucc,
      subNatNat_zero,
      Nat.mul_assoc, Nat.mul_zero, Nat.zero_mul]

theorem add_mul (x y z : Int) : (x + y) * z = x * z + y * z := by
  cases x <;> cases y <;> cases z <;> simp only
    [ ofNat_add_ofNat, ofNat_mul_ofNat,
      ofNat_add_negSucc, ofNat_mul_negSucc,
      negSucc_add_ofNat, negSucc_mul_ofNat,
      negSucc_add_negSucc, negSucc_mul_negSucc,
      ofNat_add_subNatNat, subNatNat_add_ofNat, subNatNat_add_subNatNat,
      subNatNat_mul_ofNat, subNatNat_mul_negSucc,
      (Nat.add_mul _ _ _).symm,
      Nat.succ_add, Nat.add_succ, Nat.zero_add, Nat.add_zero
    ]

theorem mul_add  (x y z : Int) : x * (y + z) = x * y + x * z := by
  cases x <;> cases y <;> cases z <;> simp only
    [ ofNat_add_ofNat, ofNat_mul_ofNat,
      ofNat_add_negSucc, ofNat_mul_negSucc,
      negSucc_add_ofNat, negSucc_mul_ofNat,
      negSucc_add_negSucc, negSucc_mul_negSucc,
      ofNat_add_subNatNat, subNatNat_add_ofNat, subNatNat_add_subNatNat,
      ofNat_mul_subNatNat, negSucc_mul_subNatNat,
      (Nat.mul_add _ _ _).symm,
      Nat.succ_add, Nat.add_succ, Nat.zero_add, Nat.add_zero
    ]

theorem neg_mul (x y : Int) : -(x * y) = -x * y := by
  cases x <;> cases y <;> simp only
    [ neg_ofNat, neg_negSucc,
      ofNat_mul_ofNat,
      ofNat_mul_negSucc,
      negSucc_mul_ofNat,
      negSucc_mul_negSucc,
      subNatNat_mul_ofNat,
      subNatNat_mul_negSucc,
      neg_subNatNat,
      subNatNat_zero,
      Nat.zero_mul
    ]

theorem mul_neg (x y : Int) : x * -y = -x * y := by
  cases x <;> cases y <;> simp only
    [ neg_ofNat, neg_negSucc,
      ofNat_mul_ofNat,
      negSucc_mul_ofNat,
      ofNat_mul_negSucc,
      ofNat_mul_subNatNat,
      subNatNat_mul_ofNat,
      subNatNat_mul_negSucc,
      negSucc_mul_subNatNat,
      subNatNat_zero,
      Nat.zero_mul, Nat.mul_zero, Nat.add_succ, Nat.add_zero
    ]

end Multiplication

section NeZero
-- Special cases

theorem neg_ne_zero {x:Int} : x ≠ 0 → -x ≠ 0 := by
  intro p eq
  apply p; clear p
  revert eq
  match x with
  | ofNat 0 =>
    simp
  | ofNat (Nat.succ x) =>
    simp only [neg_ofNat]
    intro p
    simp only [subNatNat_eq_zero] at p
  | negSucc x =>
    intro eq
    simp [OfNat.ofNat, neg_negSucc, Nat.add_succ, Nat.add_zero] at eq

theorem mul_ne_zero {x y:Int} : x ≠ 0 → y ≠ 0 → x * y ≠ 0 :=
  have h : ∀(n:Nat), ofNat (Nat.succ n) ≠ 0 := by
    intro n
    simp [OfNat.ofNat]
  match x, y with
  | ofNat 0, y  => by
    intro ne
    contradiction
  | _, 0 => by
    intro _ ne
    simp only [] at ne
  | ofNat (Nat.succ x), ofNat (Nat.succ y) => by
    intros p q
    simp only [ofNat_mul_ofNat, Nat.succ_mul, Nat.add_succ, OfNat.ofNat, ne_eq, ofNat.injEq]
  | ofNat (Nat.succ x), negSucc y => by
    intros p q eq
    simp only [ofNat_mul_negSucc, negOfNat_is_subNatNat] at eq
    simp only [subNatNat_eq_zero] at eq
    simp only [Nat.succ_mul, Nat.add_succ, OfNat.ofNat] at eq
  | negSucc x, ofNat (Nat.succ y) => by
    intros p q eq
    simp only [negSucc_mul_ofNat, negOfNat_is_subNatNat, subNatNat_eq_zero] at eq
    simp only [Nat.succ_mul, Nat.add_succ, OfNat.ofNat] at eq
  | negSucc x, negSucc y => by
    intros p q
    simp only [negSucc_mul_negSucc, Nat.succ_mul, Nat.add_succ, OfNat.ofNat, ne_eq, ofNat.injEq]

end NeZero

section Comparison

theorem nonNeg_of_nat_le {x y : Nat} (p : x ≤ y)
  : NonNeg (OfNat.ofNat y - OfNat.ofNat x) := by
  simp [OfNat.ofNat, Int.sub_to_add_neg]
  simp only [neg_ofNat]
  simp only [ofNat_add_subNatNat, Nat.add_zero]
  simp only [subNatNat.is_ofNat p]
  apply NonNeg.mk

end Comparison

end Int