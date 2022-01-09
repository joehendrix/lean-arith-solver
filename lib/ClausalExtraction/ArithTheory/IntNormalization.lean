/-
This contains the definitions related to numeric expression
normalization.
-/
import ClausalExtraction.ArithTheory.ArithM

open Lean
open Lean.Meta

namespace ClausalExtraction

namespace ArithTheory

section Lemmas
private
theorem sum0Lemma (p q v:Int) : p*v + q*v = (p+q)*v := Eq.symm (Int.add_mul _ _ _)

private
theorem sumLemma (r p q v:Int) : (r + p*v) + q*v = r + (p+q)*v := by
  apply Eq.trans (Int.add_assoc r _ _)
  apply congrArg (fun y => r + y)
  exact sum0Lemma _ _ _

private
theorem cancel0Lemma {p q:Int} (h : p+q = 0) (v:Int) : p*v + q*v = 0 := by
  apply Eq.trans (sum0Lemma p q v)
  exact @Eq.substr Int (λx => x * v = 0) _ _ h (Int.zero_mul v)

example        : (64:Int) + -64 = 0   := @cancel0Lemma (64) (-64) (@rfl Int 0) 1
example        : (-64:Int) + 64 = 0   := @cancel0Lemma (-64) (64) (@rfl Int 0) 1
example (v:Int): -64 * v + 64 * v = 0 := @cancel0Lemma (-64) 64   (@rfl Int 0) v
example (v:Int): 64 * v + -64 * v = 0 := @cancel0Lemma (64) (-64) (@rfl Int 0) v

private
theorem cancelLemma (r p q v:Int) (h : p+q = 0) : (r + p*v) + q*v = r := by
  apply Eq.trans (Int.add_assoc r _ _)
  exact Eq.trans (cancel0Lemma h v ▸ rfl) (Int.add_zero r)

private
theorem polyProofAddContextLemma {x c a:Int} (h:x + c = a) (y:Int)
  : (x + y) + c = a + y := by
  simp [h.symm, Int.add_assoc, Int.add_comm y c]

end Lemmas

-- polyProofAddContext s x c a h poly idx where h is a proof of "x + c = a" returns
-- a proof "(x + poly[idx] + poly[idx+1] + ..) + c = a + poly[idx] + poly[idx+1] + .."
private
def polyProofAddContext (ref:IO.Ref State) (f:Var → IO IntExpr) (x c a:IntExpr) (h:Expr) (poly:Poly) (idx:Nat) : IO Expr := do
  let mut x := x
  let mut a := a
  let mut h := h
  for p in poly.elements[idx:] do
    let y ← scalarProd ref f p
    h := mkAppN (mkConst ``polyProofAddContextLemma) #[x, c, a, h, y]
    x := x + y
    a := a + y
  pure h

-- | @addProof f p m v@ returns proof showing that
-- @p.expr + firstScalarProd f (m, v) = (p.add m v).expr@.
private
def polyAddProof (ref:IO.Ref State) (f:Var → IO IntExpr) : ∀(poly:Poly) (q:Int), q ≠ 0 → TheoryVar → IO Expr
| poly, q, g, v => do
  let c ← scalarProd ref f (q,v)
  let rec loop : ∀(i : Nat), IO Expr
      | 0 => do
        if poly.elements.size = 0 then
          -- Prove (0:Int) + firstScalarProd f (q,v) = firstScalarProd f (q,v)
          mkApp (mkConst `Int.zero_add) c
        else
          let x ← scalarProd ref f poly.elements[0]
          let a := c + x
          let h := mkAppN (mkConst `Int.add_comm) #[x, c]
          polyProofAddContext ref f x c a h poly 1
      | Nat.succ i => do
        let (p,u) := poly.elements[i]
        if u < v then
          let x ← polyExpr ref f poly (limit := i+1)
          let a := x + c
          let h := mkAppN (mkConst ``Eq.refl [levelOne]) #[intExpr, a]
          polyProofAddContext ref f x c a h poly (i+1)
        else if v < u then
          loop i
        else -- v = u
          if p+q = 0 then
            if i = 0 then
              let x ← scalarProd ref f poly.elements[0]
              let a := (0 : Int)
              let rflExpr := mkAppN (mkConst ``rfl [levelOne]) #[intExpr, intZeroExpr]
              -- Create proof: -q*v + q*v = 0.
              let h := mkAppN (mkConst ``cancel0Lemma) #[ (-q : Int), q, rflExpr, ← thvarExpr ref f v]
              polyProofAddContext ref f x c a h poly (i+1)
            else
              let a ← polyExpr ref f poly i
              let x := a + (← scalarProd ref f poly.elements[i])
              let rflExpr := mkAppN (mkConst ``rfl [levelOne]) #[intExpr, intZeroExpr]
              -- Create proof: (r + -q*v) + q*v = r.
              let h := mkAppN (mkConst ``cancelLemma) #[a, (-q : Int), q, ← thvarExpr ref f v, rflExpr]
              polyProofAddContext ref f x c a h poly (i+1)
          else
            if i = 0 then
              let x ← scalarProd ref f poly.elements[0]
              let a ← scalarProd ref f (p+q, v)
              --  Create proof (p*v) + (q*v) = (p+q) * v
              let h := mkAppN (mkConst ``sum0Lemma) #[p, q, ← thvarExpr ref f v]
              polyProofAddContext ref f x c a h poly (i+1)
            else
              let r ← polyExpr ref f poly i
              let x := r + (←scalarProd ref f poly.elements[i])
              let a := r + (←scalarProd ref f (p+q, v))
              let h := mkAppN (mkConst ``sumLemma) #[r, p, q, ←thvarExpr ref f v]
              polyProofAddContext ref f x c a h poly (i+1)
  loop poly.elements.size

-- @polyAddProof s poly q _ v@ returns a proof that
--   @poly.expr varExpr s + firstScalarProd s.varExpr (m, v) = (poly.add m v).expr s.varExpr@.
def getPolyAddProof (poly:Poly) (q:Int) (q_ne:q ≠ 0) (v:TheoryVar) : ArithM Expr := do
  let svc ← (read : SolverM _)
  let ref ← read
  let f (v:Var) := IntExpr.mk <$> svc.varExpr v
  polyAddProof ref f poly q q_ne v

section Normalization

def matchBinOp (f tp : Expr) (e:Expr) : MetaM (Option (Expr × Expr)) := do
  let x ← mkFreshExprMVar tp
  let y ← mkFreshExprMVar tp
  pure $ if ← isDefEq (mkAppN f #[x, y]) e then some (x, y) else none

def matchUnaryOp (f tp : Expr) (e:Expr) : MetaM (Option Expr) := do
  let x ← mkFreshExprMVar tp
  let d := mkApp f x
  pure $ if ← isDefEq d e then some x else none

def matchIntLit (e:Expr) : MetaM (Option Int) := do
  let x ← mkFreshExprMVar natExpr
  let e ← whnf e
  if ← isDefEq (mkApp (mkConst `Int.ofNat) x) e then
    match ← whnf x with
    | Expr.lit (Literal.natVal n) _ => return (some n)
    | _ => pure ()
  if ← isDefEq (mkApp (mkConst `Int.negSucc) x) e then
    match ← whnf x with
    | Expr.lit (Literal.natVal n) _ => return (some (-(n+1)))
    | _ => pure ()
  pure none

theorem add_poly_lemma {m x y a b c:Int}  (g : a + m*x = b) (h : b + m*y = c) : a + m*(x+y) = c := by
  rw [h.symm, g.symm, Int.mul_add, Int.add_assoc]
theorem sub_poly_lemma {m x y a b c:Int}  (g : a + m*x = b) (h : b + -m*y = c) : a + m*(x-y) = c := by
  rw [h.symm, g.symm]
  rw [Int.sub_to_add_neg, Int.mul_add, Int.mul_neg, Int.add_assoc]
theorem neg_poly_lemma {m x a b:Int}  (g : a + (-m)*x = b) : a + m*(-x) = b := by
  rw [g.symm, Int.mul_neg]

private theorem mul_zero_lhs_poly_lemma {m y a:Int} : a + m*(0*y) = a := by
  simp only [Int.zero_mul, Int.mul_zero, Int.add_zero]
private theorem mul_zero_rhs_poly_lemma (m x a:Int): a + m*(x*0) = a := by
  simp only [Int.add_zero, Int.mul_zero]

private theorem mul_lhs_poly_lemma {m x y a b:Int} (g: a + (m*x)*y = b) : a + m*(x*y) = b := by
  rw [Int.mul_assoc] at g
  exact g
private theorem mul_rhs_poly_lemma {m x y a b:Int} (g: a + (m*y)*x = b) : a + m*(x*y) = b := by
  rw [Int.mul_assoc, Int.mul_comm y x] at g
  exact g

theorem uninterpVarLemma {e v a m b:Int} (eq:e = v) (pr:a + m * v = b) : a + m * e = b := by
  rw [eq]
  exact pr

structure AddResult where
  poly : Poly
  polyExpr : Expr
  equivProof : Expr

-- | @appendAddExpr poly m e@ returns poly equivalent to `poly + m*e` along with proof that that
-- poly.expr + m*e = ret.expr
private
partial def appendAddExprFromInt (m:Int) (m_ne:m ≠ 0) (e:Expr) (poly:Poly) : ArithM AddResult := do
  match ← matchIntLit e with
  | none => pure ()
  | some x =>
    let r ←
      if x_ne : x = 0 then
        let aexpr ← getPolyExpr poly
        let pr := mkAppN (mkConst ``rfl [levelOne]) #[intExpr, aexpr]
        pure {
          poly := poly
          polyExpr := ← getPolyExpr poly
          equivProof := pr
        }
      else
        let y := m * x
        -- pr: poly + m * x * 1 = r
        let pr ← getPolyAddProof poly y (Int.mul_ne_zero m_ne x_ne) oneVar
        let poly := poly.add y oneVar
        return {
          poly := poly,
          polyExpr := ← getPolyExpr poly,
          equivProof := pr
        }
    return r
  -- Match addition
  let aexpr ← getPolyExpr poly
  match ← matchBinOp intAddConst intExpr e with
  | none => pure ()
  | some (x, y) => do
    let { poly := poly, polyExpr := bexpr, equivProof := x_pr }
          ← appendAddExprFromInt m m_ne x poly
    let { poly := poly, polyExpr := cexpr, equivProof := y_pr }
          ← appendAddExprFromInt m m_ne y poly
    let pr := mkAppN (mkConst ``add_poly_lemma) #[m, x, y, aexpr, bexpr, cexpr, x_pr, y_pr]
    return { poly := poly, polyExpr := ← getPolyExpr poly, equivProof := pr }

  -- Match sub
  match ← matchBinOp intSubConst intExpr e with
  | none => pure ()
  | some (x, y) => do
    let { poly := poly, polyExpr := bexpr, equivProof := x_pr }
          ← appendAddExprFromInt m m_ne x poly
    let bexpr ← getPolyExpr poly
    let { poly := poly, polyExpr := cexpr, equivProof := y_pr }
          ← appendAddExprFromInt (- m) (Int.neg_ne_zero m_ne) y poly
    let pr := mkAppN (mkConst ``sub_poly_lemma) #[m, x, y, aexpr, bexpr, cexpr, x_pr, y_pr]
    return { poly := poly, polyExpr := ← getPolyExpr poly, equivProof := pr }

  -- Match negation
  let negExpr := mkAppN (mkConst ``Neg.neg [levelZero]) #[intExpr, mkConst ``Int.instNegInt]
  match ← matchUnaryOp intNegConst intExpr e with
  | none => pure ()
  | some x => do
    let { poly := poly, polyExpr := bexpr, equivProof := x_pr }
          ← appendAddExprFromInt (-m) (Int.neg_ne_zero m_ne) x poly
    let pr := mkAppN (mkConst ``neg_poly_lemma) #[m, x, aexpr, bexpr, x_pr]
    return { poly := poly, polyExpr := ← getPolyExpr poly, equivProof := pr }

  -- Match scalar multiplication
  match ← matchBinOp intMulConst intExpr e with
  | none => pure ()
  | some (x, y) => do
    -- Match first term is int literal.
    match ← matchIntLit x with
    | none => pure ()
    | some xn =>
      let r ←
        if xn_ne:xn = 0 then
          let pr := mkAppN (mkConst ``mul_zero_lhs_poly_lemma) #[m, y, aexpr]
          -- aexpr + m*(0*y) = aexpr
          pure { poly := poly, polyExpr := aexpr, equivProof := pr }
        else
          -- y_eq: aexpr + (m*x)*y = poly'.expr
          let { poly := poly, polyExpr := bexpr, equivProof := y_pr }
                ← appendAddExprFromInt (m * xn) (Int.mul_ne_zero m_ne xn_ne) y poly
          let pr := mkAppN (mkConst ``mul_lhs_poly_lemma) #[m, x, y, aexpr, bexpr, y_pr]
          pure { poly := poly, polyExpr := bexpr, equivProof := pr }
      return r
    -- Match second term is int literal.
    match ← matchIntLit y with
    | none => pure ()
    | some yn =>
      let r ←
        if n_ne:yn = 0 then
          let pr := mkAppN (mkConst ``mul_zero_rhs_poly_lemma) #[m, x, aexpr]
          pure { poly := poly, polyExpr := aexpr, equivProof := pr }
        else
          let { poly := poly, polyExpr := bexpr, equivProof := x_pr }
                ← appendAddExprFromInt (m * yn) (Int.mul_ne_zero m_ne n_ne) x poly
          let { poly := poly, polyExpr := bexpr, equivProof := x_pr }
                ← appendAddExprFromInt (m * yn) (Int.mul_ne_zero m_ne n_ne) x poly
          let pr := mkAppN (mkConst ``mul_rhs_poly_lemma) #[m, x, y, aexpr, bexpr, x_pr]
          pure { poly := poly, polyExpr := bexpr, equivProof := pr }
      return r

  let e ← instantiateMVars e
  let (v, vExpr, eq) ← do
        let r ← getVarForExpr e
        pure (← getUninterpVar r.var, r.varExpr, r.eq)
  let pr ← getPolyAddProof poly m m_ne v
  let poly := poly.add m v
  let bexpr ← getPolyExpr poly
  let pr := mkAppN (mkConst ``uninterpVarLemma) #[e, vExpr, aexpr, m, bexpr, eq, pr]
  pure { poly := poly, polyExpr := bexpr, equivProof := pr }

theorem purifyIntLemmaPoly {x y:Int} (p:0 + 1 * x = y) : x = y := by
  simp [Int.zero_add, Int.one_mul] at p
  exact p

theorem purifyIntLemmaVar {x y:Int} (p:0 + 1 * x = 1 * y) : x = y :=
  Eq.trans (purifyIntLemmaPoly p) (Int.one_mul y)

-- | This traverses an expression (which should have type int) to normalize
-- the expression.  It produces a variable along with a proof that
-- e = v.expr
def purifyIntExpr (e:Expr) : ArithM (VarDefinition TheoryVar) := do
  let e ← instantiateMVars e
  let one_ne : (1:Int) ≠ 0 := by simp only [ne_eq]
  let r ← appendAddExprFromInt 1 one_ne e Poly.zero
  -- pr  has type" 0 + 1 * e = p.expr"
--  let { poly := p, polyExpr := pexpr := equivProof := pr} := r

  match r.poly with
  | ⟨#[(1, v)]⟩ => do
    -- Make pr have type e = v
    let ve ← getThvarExpr v
    let pr := mkAppN (mkConst ``purifyIntLemmaVar) #[e, ve, r.equivProof]
    pure {var := v, varExpr := ve, eq := r.equivProof }
  | p => do
    let v ← getPolyVar p
    -- Make pr have type e = v
    let pr := mkAppN (mkConst ``purifyIntLemmaPoly) #[e, r.polyExpr, r.equivProof]
    pure {var := v, varExpr := r.polyExpr, eq := pr }

end Normalization

def ops (r:IO.Ref State) : TheoryOps :=
  { varExpr := mthvarExpr r,
    predExpr := ArithTheory.predExpr r
  }

section PredicateNormalizationLemmas

theorem nat_lt_prop {x y : Nat} (p : x < y)
  : Int.NonNeg (OfNat.ofNat y - OfNat.ofNat (x + 1)) := Int.nonNeg_of_nat_le p
def nat_ge_prop {x y : Nat} (p : x ≥ y) := Int.nonNeg_of_nat_le p
def nat_gt_prop {x y : Nat} (p : x > y) := Int.nonNeg_of_nat_le p

theorem nat_not_le_prop {x y : Nat} (p : ¬(x ≤ y)) : Int.NonNeg (OfNat.ofNat x - OfNat.ofNat (y + 1)) :=
  match Nat.lt_or_ge y x with
  | Or.inl q => Int.nonNeg_of_nat_le q
  | Or.inr q => False.elim (p q)
theorem nat_not_lt_prop {x y : Nat} (p : ¬(x < y))
  : Int.NonNeg (OfNat.ofNat x - OfNat.ofNat y) :=
  match Nat.lt_or_ge x y with
  | Or.inl q => False.elim (p q)
  | Or.inr q => Int.nonNeg_of_nat_le q
def nat_not_ge_prop {x y : Nat} (p : ¬(x ≥ y)) := nat_not_le_prop p
def nat_not_gt_prop {x y : Nat} (p : ¬(x > y)) := nat_not_lt_prop p

theorem int_le_prop {x y : Int} (p : x ≤ y) : Int.NonNeg (y - x) := p
theorem int_lt_prop {x y : Int} (p : x < y) : Int.NonNeg (y - (x + 1)) := p
def int_ge_prop {x y : Int} (p : x ≥ y) := int_le_prop p
def int_gt_prop {x y : Int} (p : x > y) := int_lt_prop p

theorem int_not_le_prop {x y : Int} (p : ¬(x ≤ y))
  : Int.NonNeg (x - (y + 1)) :=
  match Int.lt_or_ge y x with
  | Or.inl q => int_lt_prop q
  | Or.inr q => False.elim (p q)

theorem int_not_lt_prop {x y : Int} (p : ¬(x < y))
  : Int.NonNeg (x - y) :=
  match Int.lt_or_ge x y with
  | Or.inl q => False.elim (p q)
  | Or.inr q => int_le_prop q
def int_not_ge_prop {x y : Int} (p : ¬(x ≥ y)) := int_not_le_prop p
def int_not_gt_prop {x y : Int} (p : ¬(x > y)) := int_not_lt_prop p

theorem int_eq_prop (x y : Int) (p : x = y)
  : x - y = 0 := by simp [p, Int.sub_self]

theorem nat_eq_prop {x y : Nat} (p : x = y)
  : @OfNat.ofNat Int x _ - OfNat.ofNat y = 0 := by
    apply int_eq_prop
    simp only [OfNat.ofNat, p]

theorem int_not_eq_prop {x y : Int} (p : ¬(x = y))  : ¬(x - y = 0) := by
  intro q
  apply p (Int.sub_eq_zero_implies_eq q)

theorem nat_not_eq_prop {x y : Nat} (p : ¬(x = y))
  : ¬(@OfNat.ofNat Int x _ - OfNat.ofNat y = 0) := by
  apply int_not_eq_prop
  simp only [OfNat.ofNat, Int.ofNat.injEq]
  exact p

def transformerNames : Array Name :=
  #[
    ``nat_eq_prop,
    ``nat_lt_prop,
    ``Int.nonNeg_of_nat_le,
    ``nat_gt_prop,
    ``nat_ge_prop,
    ``nat_not_eq_prop,
    ``nat_not_lt_prop,
    ``nat_not_le_prop,
    ``nat_not_gt_prop,
    ``nat_not_ge_prop,
    ``int_eq_prop,
    ``int_lt_prop,
    ``int_le_prop,
    ``int_gt_prop,
    ``int_ge_prop,
    ``int_not_eq_prop,
    ``int_not_lt_prop,
    ``int_not_le_prop,
    ``int_not_gt_prop,
    ``int_not_ge_prop
  ]

end PredicateNormalizationLemmas

-- Lemma used for convert proofs from one type of predicate to another.
private theorem intNonNeg_lemma {x y :Int} (eq:x = y) (p:Int.NonNeg x) : Int.NonNeg y := eq.subst p
private theorem intEq0_lemma {x y :Int} (eq:x = y) (p:x = 0) : y = 0 := @Eq.subst Int (λd => d = 0) _ _ eq p
private theorem intNe0_lemma {x y :Int} (eq:x = y) (p:¬(x = 0)) : ¬(y = 0) := @Eq.subst Int (λd => ¬(d = 0)) _ _ eq p

-- | Match `(Int.NonNeg e) and return proof term and property.
def matchIntNonNeg (r:IO.Ref ArithTheory.State)  (prop : Expr) : SolverM (Option (TheoryPred × Expr)) := do
  let mvar ← mkFreshExprMVar intExpr MetavarKind.natural `n
  unless ← isDefEq (mkIntNonNegExpr mvar) prop do
    return none
  let res ← purifyIntExpr mvar r
  let pred ← getTheoryPred (Pred.IsGe0 res.var) r
  let proofFn := mkAppN (mkConst ``intNonNeg_lemma) #[mvar, ← getThvarExpr res.var r, res.eq]
  return (some (pred, proofFn))

def matchIntEq0 (r:IO.Ref ArithTheory.State) (prop : Expr) : SolverM (Option (TheoryPred × Expr)) := do
  let mvar ← mkFreshExprMVar intExpr MetavarKind.natural `n
  unless ← isDefEq (mkIntEq0Expr mvar) prop do
    return none
  let res ← purifyIntExpr mvar r
  let proofFn := mkAppN (mkConst ``intEq0_lemma) #[mvar, ← getThvarExpr res.var r, res.eq]
  return (some (← getTheoryPred (Pred.IsEq0 res.var) r, proofFn))

def matchNotIntEq0 (r:IO.Ref ArithTheory.State) (prop : Expr) : SolverM (Option (TheoryPred × Expr)) := do
  let mvar ← mkFreshExprMVar intExpr MetavarKind.natural `n
  unless ← isDefEq (mkApp (mkConst ``Not) (mkIntEq0Expr mvar)) prop do
    return none
  let res ← purifyIntExpr mvar r
  let proofFn := mkAppN (mkConst ``intNe0_lemma) #[mvar, ← getThvarExpr res.var r, res.eq]
  return (some (← getTheoryPred (Pred.IsNe0 res.var) r, proofFn))

end ArithTheory
end ClausalExtraction