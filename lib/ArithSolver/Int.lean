/-
This defines additional operations used to normalize inequalitis.
-/
import ArithSolver.Nat

namespace Int

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
    simp [subNatNat]
    generalize g: z - y = z_sub_y
    cases z_sub_y with
    | zero =>
      simp [ofNat_add_ofNat, Nat.add_sub]
      rw [Nat.add_comm x y]
      simp [(Nat.sub_sub_lassoc _ _ _).symm, g, Nat.zero_sub]
      rw [Nat.add_comm y x]
      apply Nat.add_sub
      exact (Nat.sub_is_zero_is_le.mpr g)
    | succ j =>
      simp [ofNat_add_negSucc, subNatNat]
      simp [g.symm]
      rw [Nat.add_comm x y, Nat.sub_sub_lassoc]
      have p := Nat.le_of_lt (Nat.lt_of_sub_succ g)
      have r := Nat.sub_sub_rassoc x p
      rw [r, Nat.add_comm y x]

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

section Negation

@[simp]
theorem neg_zero : - (0:Int) = 0 := by rfl

theorem neg_ofNat (n:Nat) : -ofNat n = negOfNat n := by rfl

theorem neg_negSucc (n:Nat) : -negSucc n = ofNat (n+1) := by rfl

private
theorem negOfNat_add_ofNat  (x y:Nat)
  : negOfNat x + ofNat y = subNatNat y x := by
  cases x <;>
    simp [negOfNat, subNatNat, Nat.zero_sub, negSucc_add_ofNat]

private
theorem ofNat_add_negOfNat  (x y:Nat)
  : ofNat x + negOfNat y = subNatNat x y := by
  cases y <;>
    simp [negOfNat, subNatNat, Nat.zero_sub, ofNat_add_negSucc]

theorem negOfNat_add_negOfNat (x y : Nat)
  : negOfNat x + negOfNat y = negOfNat (x + y) := by
  cases x <;> cases y <;>
    simp [negOfNat, Nat.add_succ, Nat.succ_add,
          negSucc_add_negSucc]

theorem neg_subNatNat (m n: Nat) : - (subNatNat m n) = subNatNat n m := by
  cases m with
  | zero =>
    simp [subNatNat]
    cases n with
    | zero =>
      simp
    | succ n =>
      simp [neg_negSucc, Nat.add_succ, negOfNat, Nat.zero_sub]
  | succ m =>
    simp [subNatNat]
    generalize g:n-m.succ=n_sub_m
    cases n_sub_m with
    | zero =>
      simp [neg_ofNat]
      generalize m.succ-n=m_sub_n
      cases m_sub_n with
      | zero =>
        simp [negOfNat]
      | succ m_sub_n =>
        simp [negOfNat]
    | succ n_sub_m =>
      generalize h:m.succ-n=m_sub_n
      cases m_sub_n with
      | zero =>
        simp [neg_negSucc]
      | succ m_sub_n =>
        have r : Nat.succ m ≤ n:= Nat.le_of_lt (Nat.lt_of_sub_succ g)
        have s : ¬ (Nat.succ m ≤ n) := Nat.not_le_of_gt (Nat.lt_of_sub_succ h)
        exact False.elim (s r)

theorem neg_add (x y : Int) : -(x + y) = -x + -y := by
  cases x <;> cases y <;> simp
    [ofNat_add_ofNat, ofNat_add_negSucc, negSucc_add_ofNat, negSucc_add_negSucc,
     neg_ofNat, neg_negSucc,
     Nat.add_succ, Nat.add_zero, Nat.succ_add,
     neg_subNatNat,
     negOfNat_add_ofNat, ofNat_add_negOfNat, negOfNat_add_negOfNat
    ]

end Negation

section Subtraction

theorem sub_self (x : Int) : x - x = 0 := sorry

theorem sub_to_add_neg (x : Int) : x - y = x + -y := by rfl

theorem ofNat_sub_ofNat (x y : Nat) : ofNat x - ofNat y = subNatNat x y := sorry
theorem ofNat_sub_negSucc (x y : Nat) : ofNat x - negSucc y = ofNat (x + (y + 1)) := sorry
theorem negSucc_sub_ofNat (x y : Nat) : negSucc x - ofNat y = negSucc (x + y) := sorry
theorem negSucc_sub_negSucc (x y : Nat) : negSucc x - negSucc y = subNatNat y x := sorry

theorem subNatNat_sub_ofNat (x y z : Nat) : subNatNat x y - ofNat z = subNatNat x (y+z) := sorry

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

theorem sub_eq_zero_implies_eq {x y : Int} (q : x - y = 0) : x = y := by
  cases x with
  | ofNat x =>
    cases y with
    | ofNat y =>
      simp [Int.ofNat_sub_ofNat] at q
      simp [subNatNat_zero_implies_equal q]
    | negSucc y =>
      simp only [Int.ofNat_sub_negSucc, OfNat.ofNat, Nat.add_succ] at q
      apply Int.noConfusion q
      intro r
      apply Nat.noConfusion r
  | negSucc x =>
    cases y with
    | ofNat y =>
      simp only [Int.negSucc_sub_ofNat, OfNat.ofNat, Nat.add_succ] at q
    | negSucc y =>
      simp [Int.negSucc_sub_negSucc] at q
      simp [subNatNat_zero_implies_equal q]

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
               ofNat_add_negOfNat,
               negOfNat_add_ofNat,
               negOfNat_add_negOfNat,
               subNatNat_mul_ofNat, subNatNat_mul_negsucc,
               (Nat.add_mul _ _ _).symm,
               Nat.succ_add, Nat.add_succ
               ]

theorem mul_add : ∀ (x y z : Int), x * (y + z) = x * y + x * z := by admit

theorem neg_mul (x y : Int) : -(x * y) = -x * y := sorry

theorem mul_neg (x y : Int) : x * -y = -x * y := sorry

theorem mul_sub : ∀ (x y z : Int), x * (y - z) = x * y - x * z := by admit

end Multiplication

section NeZero
-- Special cases

theorem neg_ne_zero {x:Int} : x ≠ 0 → -x ≠ 0 := sorry
theorem mul_ne_zero {x y:Int} : x ≠ 0 → y ≠ 0 → x * y ≠ 0 := sorry

end NeZero

end Int
