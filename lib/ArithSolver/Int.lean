/-
This defines additional operations used to normalize inequalitis.
-/
import ArithSolver.Nat

namespace Int

-- Thoems only about subNatNat and nat-level operations
-- We make these private as the intention is that users should not need to directly
-- work with subNatNat
section subNatNat

private
theorem subNatNat.is_ofNat {x y:Nat} (p:y ≤ x) : subNatNat x y = ofNat (x - y) := by
  simp [subNatNat]
  have h:y -x = 0 := Nat.sub_is_zero_is_le.mp p
  simp [h]

private theorem subNatNat.is_negSucc {x y:Nat} (p:x < y) : subNatNat x y = negSucc (y - Nat.succ x) := by
  generalize g: y - x = y_sub_x
  cases y_sub_x with
  | zero =>
    have h : y ≤ x := Nat.sub_is_zero_is_le.mpr g
    have q : ¬(y ≤ x) := Nat.not_le_of_gt p
    contradiction
  | succ y_sub_x =>
    simp only [subNatNat, g, Nat.sub_succ, Nat.pred]

private
theorem succ_subNatNat_succ (x y : Nat) : subNatNat (Nat.succ x) (Nat.succ y) = subNatNat x y := by
  match Nat.lt_or_ge x y with
  | Or.inl p =>
    have q := Nat.succ_lt_succ p
    simp [subNatNat.is_negSucc, p, q, Nat.succ_sub_succ]
  | Or.inr p =>
    have q := Nat.succ_le_succ p
    simp [subNatNat.is_ofNat, p, q, Nat.succ_sub_succ]

private
theorem subNatNat_self (x:Nat) : subNatNat x x = 0 := by
  induction x with
  | zero => rfl
  | succ x ind => simp [succ_subNatNat_succ, ind]

private
theorem zero_subNatNat_succ (x:Nat) : subNatNat 0 (Nat.succ x) = Int.negSucc x := by
  simp [subNatNat.is_negSucc, Nat.zero_lt_succ, Nat.succ_sub_succ, Nat.sub_zero]

private
theorem subNat_sub_rhs {y z :Nat} (p : z ≤ y) (x:Nat) : subNatNat x (y - z) = subNatNat (x + z) y := by
  match Nat.lt_or_ge (x+z) y with
  | Or.inl q =>
    have r : Nat.succ x ≤ y - z := by
      have q2 : Nat.succ (x+z) ≤ y := q
      simp only [Nat.sub_is_zero_is_le, Nat.sub_sub_rassoc _ p, Nat.succ_add]
      simp only [Nat.sub_is_zero_is_le] at q2
      exact q2
    simp only [subNatNat.is_negSucc q, subNatNat.is_negSucc r, Nat.sub_succ]
    simp only [Nat.sub_sub_lassoc, Nat.add_comm]
  | Or.inr q =>
    have r : y - z ≤ x := by
      simp [Nat.sub_is_zero_is_le]
      simp [Nat.sub_is_zero_is_le] at q
      simp [Nat.sub_sub_lassoc, Nat.add_comm z x]
      exact q
    simp only [subNatNat.is_ofNat q, subNatNat.is_ofNat r]
    simp only [Nat.sub_sub_rassoc _ p]

private
theorem subNatNat_zero_implies_equal {x y :Nat} (q:Int.subNatNat x y = 0) : x = y := by
  simp [Int.subNatNat] at q
  have p : y - x = 0 := by
    generalize g:y-x=z
    cases z with
    | zero => rfl
    | succ z => simp [g] at q
  simp [p, OfNat.ofNat] at q
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

private
theorem ofNat_add_subNatNat (x y z:Nat)
  : ofNat x + subNatNat y z = subNatNat (x + y) z := by
    match Nat.lt_or_ge y z with
    | Or.inl p =>
      simp only [subNatNat.is_negSucc p, ofNat_add_negSucc, Nat.succ_sub p, Nat.succ_sub_succ]
      simp only [subNat_sub_rhs (Nat.le_of_lt p)]
    | Or.inr p =>
      simp only [subNatNat.is_ofNat p, ofNat_add_ofNat]
      have q : x + y ≥ z := Nat.le_trans p (Nat.le_add_left y x)
      simp only [subNatNat.is_ofNat q, Nat.add_sub _ p]

private
theorem subNatNat_add_ofNat (x y z:Nat) : subNatNat x y + ofNat z = subNatNat (x + z) y := by
  simp [subNatNat]
  generalize g:y-x=j
  cases j with
  | zero =>
    have q : y <= x := Nat.sub_is_zero_is_le.mpr g
    simp [Eq.symm (Nat.sub_sub_lassoc _ _ _), g, Nat.zero_sub, ofNat_add_ofNat,
          Nat.sub_add_lassoc _ q]
  | succ j =>
    simp [negSucc_add_ofNat, subNatNat, g.symm]
    have q := Nat.sub_sub_lassoc y x z
    have h : x ≤ y := Nat.le_of_lt (Nat.lt_of_sub_succ g)
    have r := Nat.sub_sub_rassoc z h
    have s := Nat.add_comm z x
    simp [q, r, s]

private
theorem negSucc_add_subNatNat (x y z:Nat) : negSucc x + subNatNat y z = subNatNat y (Nat.succ (x + z)) := by
  simp [subNatNat]
  generalize g:z-y=j
  cases j with
  | zero =>
    simp [negSucc_add_ofNat, subNatNat]
    have h : z ≤ y := Nat.sub_is_zero_is_le.mpr g
    have p := Nat.sub_sub_rassoc (Nat.succ x) h
    have q := Nat.sub_sub_lassoc
    have r := Nat.add_comm z (Nat.succ x)
    simp [p, Nat.succ_add, q, r]
  | succ j =>
    rw [negSucc_add_negSucc]
    have p : Nat.succ (x + j) = x + (z- y) := by
      simp [(Nat.add_succ _ _).symm, g.symm]
    rw [p]
    have q :  Nat.succ (x + z) - y = Nat.succ (x + (z - y)) := by
      have h : y ≤ z := Nat.le_of_lt (Nat.lt_of_sub_succ g)
      have h2 : y ≤ x + z := Nat.le_trans h (Nat.le_add_left z x)
      simp [Nat.add_sub _ h, Nat.succ_sub h2]
    simp [q]

private
theorem subNatNat_add_negSucc (x y z:Nat)
  : subNatNat x y + negSucc z = subNatNat x (Nat.succ (y + z)) := by
  simp [subNatNat]
  generalize g:y-x=j
  cases j with
  | zero =>
    simp [ofNat_add_negSucc, subNatNat]
    have g : Nat.succ z - (x - y) = Nat.succ (y + z) - x := by
      have h : y ≤ x := Nat.sub_is_zero_is_le.mpr g
      have p := Nat.sub_sub_rassoc (Nat.succ z) h
      simp [p, Nat.succ_add, Nat.add_comm z y]
    have h : x - y - Nat.succ z = x - Nat.succ (y + z) := by
      simp [Nat.sub_sub_lassoc, Nat.add_succ]
    simp [g, h]
  | succ j =>
    simp [negSucc_add_negSucc]
    have p : x ≤ y := Nat.le_of_lt (Nat.lt_of_sub_succ g)
    have h : Nat.succ (y + z) - x = Nat.succ ((y+z) - x) := by
      have q : x ≤ y + z := Nat.le_trans p (Nat.le_add_right y z)
      have r := Nat.succ_sub q
      simp [r]
    simp [h, (Nat.succ_add j z).symm, g.symm]
    have q := @Nat.sub_add_lassoc y x z p
    exact q

private theorem subNatNat_add_subNatNat (a b c d:Nat)
  : subNatNat a b + subNatNat c d = subNatNat (a + c) (b + d) := by admit

theorem add_comm (x y : Int) : x + y = y + x := by
  cases x <;> cases y <;> simp only
    [ofNat_add_ofNat, ofNat_add_negSucc,
     negSucc_add_ofNat, negSucc_add_negSucc,
     Nat.add_comm]

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
    simp only [Nat.sub_add_lassoc _ p, Nat.succ_sub_succ]
  | Or.inr p =>
    simp only [subNatNat.is_ofNat p, neg_ofNat]
    simp only [subNat_sub_rhs p, Nat.zero_add]

theorem neg_add (x y : Int) : -(x + y) = -x + -y := by
  cases x <;> cases y <;>
    simp only
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
      simp only [sub_to_add_neg, neg_ofNat, ofNat_add_subNatNat, Nat.add_zero] at q
      simp only [subNatNat_zero_implies_equal q]
    | negSucc y =>
      simp only [sub_to_add_neg, neg_negSucc, ofNat_add_ofNat] at q
      apply Int.noConfusion q
      intro r
      apply Nat.noConfusion r
  | negSucc x =>
    cases y with
    | ofNat y =>
      simp only [sub_to_add_neg, neg_ofNat, negSucc_add_subNatNat] at q
      have p := subNatNat_zero_implies_equal q
      contradiction
    | negSucc y =>
      simp only [sub_to_add_neg, neg_negSucc, negSucc_add_ofNat, succ_subNatNat_succ] at q
      have r := subNatNat_zero_implies_equal q
      simp only [r]

end Subtraction

protected theorem lt_or_ge (x y : Int) : x < y ∨ x ≥ y := by admit

section Multiplication

private theorem ofNat_mul_ofNat (m n : Nat) : ofNat m * ofNat n = ofNat (m * n) := by rfl

private theorem ofNat_mul_negSucc (m n : Nat) : ofNat m * negSucc n = negOfNat (m * Nat.succ n) := by rfl

private theorem negSucc_mul_ofNat (m n : Nat) : negSucc m * ofNat n = negOfNat (Nat.succ m * n) := by rfl

private theorem negSucc_mul_negSucc (m n : Nat) : negSucc m * negSucc n = ofNat (Nat.succ m * Nat.succ n) := by rfl

theorem zero_mul (x:Int) : 0 * x = 0 := by
  simp only [HMul.hMul, Mul.mul]
  cases x <;> simp only [Int.mul, Nat.zero_mul]

theorem mul_zero : ∀ (x : Int), x * 0 = 0 := by admit

theorem one_mul (x:Int) : 1 * x = x := by
  simp only [HMul.hMul, Mul.mul]
  cases x <;> simp only [Int.mul, negOfNat, Nat.one_mul]


theorem mul_one (x:Int) : x * 1 = x := by admit

theorem mul_comm : ∀ (x y : Int), x * y = y * x := by admit

theorem mul_assoc : ∀ (x y z : Int), x * y * z = x * (y * z) := by admit

private
theorem subNatNat_mul_ofNat (x y z : Nat) : subNatNat x y * ofNat z = subNatNat (x * z) (y * z) := by
  admit

private
theorem subNatNat_mul_negsucc (x y z : Nat) : subNatNat x y * negSucc z = subNatNat (y * Nat.succ z) (x * Nat.succ z)  := by
  admit

theorem add_mul (x y z : Int) : (x + y) * z = x * z + y * z := by
  cases x <;> cases y <;> cases z <;>
    simp only [ofNat_add_ofNat, ofNat_mul_ofNat,
               ofNat_add_negSucc, ofNat_mul_negSucc,
               negSucc_add_ofNat, negSucc_mul_ofNat,
               negSucc_add_negSucc, negSucc_mul_negSucc,
               negOfNat_is_subNatNat,
               ofNat_add_subNatNat,
               subNatNat_add_ofNat,
               subNatNat_add_subNatNat,
               subNatNat_mul_ofNat, subNatNat_mul_negsucc,
               (Nat.add_mul _ _ _).symm,
               Nat.succ_add, Nat.add_succ,
               Nat.zero_add, Nat.add_zero
               ]

theorem mul_add : ∀ (x y z : Int), x * (y + z) = x * y + x * z := by admit

theorem neg_mul (x y : Int) : -(x * y) = -x * y := sorry

theorem mul_neg (x y : Int) : x * -y = -x * y := by
  admit

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
    have q := subNatNat_zero_implies_equal p
    contradiction
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
    simp only [] at ne
  | _, 0 => by
    intro _ ne
    simp only [] at ne
  | ofNat (Nat.succ x), ofNat (Nat.succ y) => by
    intros p q
    simp [ofNat_mul_ofNat, Nat.succ_mul, Nat.add_succ, OfNat.ofNat]
  | ofNat (Nat.succ x), negSucc y => by
    intros p q eq
    simp only [ofNat_mul_negSucc, negOfNat_is_subNatNat] at eq
    have r := subNatNat_zero_implies_equal eq
    simp only [Nat.succ_mul, Nat.add_succ, OfNat.ofNat] at r
  | negSucc x, ofNat (Nat.succ y) => by
    intros p q eq
    simp only [negSucc_mul_ofNat, negOfNat_is_subNatNat] at eq
    have r := subNatNat_zero_implies_equal eq
    simp only [Nat.succ_mul, Nat.add_succ, OfNat.ofNat] at r
  | negSucc x, negSucc y => by
    intros p q
    simp [negSucc_mul_negSucc, Nat.succ_mul, Nat.add_succ, OfNat.ofNat]

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
