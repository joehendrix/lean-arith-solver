import ArithSolver.Nat

namespace Int

theorem ofNat_zero : ofNat 0 = 0 := by rfl

theorem ofNat_succ {m : Nat} : ofNat (Nat.succ m) = ofNat m + 1 := by rfl

#print Int.add

theorem ofNat_add_ofNat (m n : Nat) : ofNat m + ofNat n = ofNat (m + n) := by rfl

theorem ofNat_add_negSucc (m n : Nat) : ofNat m + negSucc n = subNatNat m (Nat.succ n) := by rfl

theorem negSucc_add_ofNat (m n : Nat) : negSucc m + ofNat n = subNatNat n (Nat.succ m) := by rfl

theorem negSucc_add_negSucc (m n : Nat) : negSucc m + negSucc n = negSucc (Nat.succ (m + n)) := by rfl

@[simp]
theorem add_zero (x : Int) : x + 0 = x :=
  match x with
  | ofNat n => Eq.refl (ofNat n)
  | negSucc n => Eq.refl (negSucc n)

@[simp]
theorem zero_add (x : Int) : 0 + x = x :=
  match x with
  | ofNat n => congrArg ofNat (Nat.zero_add _)
  | negSucc n => rfl

theorem sub_add_neg (x : Int) : x - y = x + -y := by rfl

theorem negOfNat_zero : negOfNat 0 = 0 := by rfl

theorem negOfNat_succ : negOfNat (Nat.succ n) = negSucc n := by rfl

@[simp]
theorem neg_zero : - (0:Int) = 0 := by rfl

theorem neg_ofNat (n:Nat) : -ofNat n = negOfNat n := by rfl

theorem neg_negSucc (n:Nat) : -negSucc n = ofNat (n+1) := by rfl

theorem neg_subNatNat (m n: Nat) : - (subNatNat m n) = subNatNat n m := by
  cases m with
  | zero =>
    simp [ofNat_zero]
    simp [subNatNat]
    cases n with
    | zero =>
      simp
    | succ n =>
      simp [neg_negSucc, Nat.add_succ, sub_add_neg, negOfNat_zero, Nat.zero_sub]
  | succ m =>
    simp [HSub.hSub, Sub.sub, Int.sub]
    simp [neg_ofNat, negOfNat_succ]
    simp [HAdd.hAdd, Add.add, Int.add]
    simp [subNatNat]
    generalize g:n-m.succ=n_sub_m
    cases n_sub_m with
    | zero =>
      simp [neg_ofNat]
      generalize m.succ-n=m_sub_n
      cases m_sub_n with
      | zero =>
        simp [negOfNat_succ]
      | succ m_sub_n =>
        simp [negOfNat_succ]
    | succ n_sub_m =>
      generalize h:m.succ-n=m_sub_n
      cases m_sub_n with
      | zero =>
        simp [neg_negSucc]
      | succ m_sub_n =>
        have r : Nat.succ m ≤ n:= Nat.le_of_lt (Nat.lt_of_sub_succ g)
        have s : ¬ (Nat.succ m ≤ n) := Nat.not_le_of_gt (Nat.lt_of_sub_succ h)
        exact False.elim (s r)

theorem neg_add (x y : Int) : -(x + y) = -x + -y :=
  match x, y with
  | 0, y => by
    simp only [Int.zero_add, Int.neg_zero]
  | ofNat (Nat.succ x), ofNat 0 => by rfl
  | ofNat (Nat.succ x), ofNat (Nat.succ y) => by
    simp only [ofNat_add_ofNat, Int.neg_ofNat, Nat.succ_add]
    simp only [negOfNat_succ, negSucc_add_negSucc, Nat.add_succ]
  | ofNat (Nat.succ x), negSucc y => by
    apply neg_subNatNat
  | negSucc x, 0 => by simp
  | negSucc x, ofNat (Nat.succ y) => by
    apply neg_subNatNat
  | negSucc x, negSucc y => by
    simp only [negSucc_add_negSucc, neg_negSucc, ofNat_add_ofNat]
    simp only [Nat.add_succ, Nat.succ_add, Nat.add_zero]

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

theorem zero_mul (x:Int) : 0 * x = 0 := sorry

theorem one_mul (x:Int) : 1 * x = x := sorry

theorem add_mul (n m k : Int) : (n + m) * k = n * k + m * k := sorry

-- This section contains theorems that turn comparisons into normal forms.
section predicateToNonNeg

theorem nonNeg_of_le {x y : Int} (p : x ≤ y) : NonNeg (y + -x) := p

theorem nonNeg_of_lt {x y : Int} (p : x < y) : NonNeg (y + -x + -1) := by
  have q := nonNeg_of_le p
  simp [neg_add, (add_assoc _ _ _).symm] at q
  exact q

theorem nonNeg_of_ge {x y : Int} (p : x ≥ y) : NonNeg (x + -y) := p

theorem nonNeg_of_gt {x y : Int} (p : x > y) : NonNeg (x + -y + -1) := nonNeg_of_lt p

theorem nonNeg_of_le_Nat {m n : Nat} (p : m ≤ n) : NonNeg (ofNat n + -ofNat m) := by
  cases m with
  | zero =>
    exact NonNeg.mk n
  | succ m =>
    simp only [neg_ofNat, negOfNat_succ]
    simp only [HAdd.hAdd, Add.add, Int.add]
    have q := Nat.sub_is_zero_is_le.mp p
    simp only [subNatNat, q]
    exact NonNeg.mk _

theorem nonNeg_of_lt_Nat {m n : Nat} (p : m < n) : NonNeg (ofNat n + -ofNat m + -1) := by
  have q := nonNeg_of_le_Nat p
  simp only [ofNat_succ, neg_add] at q
  simp only [add_assoc, q]

theorem nonNeg_of_ge_Nat {x y : Nat} (p : x ≥ y) : NonNeg (ofNat x + -ofNat y) :=
  nonNeg_of_le_Nat p

theorem nonNeg_of_gt_Nat {x y : Nat} (p : x > y) : NonNeg (ofNat x + -ofNat y + -1) :=
  nonNeg_of_lt_Nat p

end predicateToNonNeg

end Int
