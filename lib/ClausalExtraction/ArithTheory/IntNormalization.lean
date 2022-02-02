/-
This contains the definitions related to numeric expression
normalization.
-/
import ClausalExtraction.ArithTheory.ArithM
import ClausalExtraction.SimpRule
import Lean

open Lean
open Lean.Meta

namespace ClausalExtraction

namespace ArithTheory

-- | Create an int
def mkIntRefl (e:IntExpr) : Expr := mkApp (mkApp (mkConst ``rfl [levelOne]) intExpr) e


def getVarExprFn : ArithM (TheoryVar → IO IntExpr) := do
  let svc ← (read : SolverM _)
  let ref ← read
  pure (thvarExpr ref svc.varExpr)

-- @polyAddProof s poly q _ v@ returns a proof that
--   @poly.expr varExpr s + firstScalarProd s.varExpr (m, v) = (poly.add m v).expr s.varExpr@.
def getPolyAddProof (poly:Poly) (q:Int) (q_ne:q ≠ 0) (v:TheoryVar) : ArithM Expr := do
  let svc ← (read : SolverM _)
  let ref ← read
  Poly.addProof (thvarExpr ref svc.varExpr) poly q q_ne v

section Normalization

def matchBinOp (f tp : Expr) (e:Expr) : MetaM (Option (Expr × Expr)) := do
  let x ← mkFreshExprMVar tp
  let y ← mkFreshExprMVar tp
  pure $ if ← isDefEq (mkAppN f #[x, y]) e then some (x, y) else none

def matchUnaryOp (f tp : Expr) (e:Expr) : MetaM (Option Expr) := do
  let x ← mkFreshExprMVar tp
  let d := mkApp f x
  pure $ if ← isDefEq d e then some x else none

def matchOfNatNatLit (e:Expr) : MetaM (Option Nat) := do
  let acts : List (Expr → MetaM (Option Nat)) := [
    matchrule `(@OfNat.ofNat Nat $(x) _) => do
      match ← whnf x with
      | Expr.lit (Literal.natVal n) _ => pure (some n)
      | _ => pure none
   ]
  for act in acts do
    match ← act e with
    | some n =>
       return n
    | none => pure ()
  pure none

def matchIntLit (e:Expr) : MetaM (Option Int) := do
  let acts := [
    matchrule `(Int.ofNat $(x)) => do
      match ← whnf x with
      | Expr.lit (Literal.natVal n) _ => pure (some (n:Int))
      | _ => pure none,
    matchrule `(Int.negSucc $(x)) => do
      match ← whnf x with
      | Expr.lit (Literal.natVal n) _ => pure (some (Int.negSucc n))
      | _ => pure none
   ]
  for act in acts do
    match ← act e with
    | some n => return n
    | none => pure ()
  pure none

def matchOfNatofNatInt : Expr → MetaM (Option Expr) :=
  matchrule `(@OfNat.ofNat Int $(n) _) => pure (some n)

theorem int_add_poly_lemma {m x y a b c:Int}  (g : a + m*x = b) (h : b + m*y = c) : a + m*(x+y) = c := by
  rw [h.symm, g.symm, Int.mul_add, Int.add_assoc]

theorem nat_add_poly_lemma {m:Int} {x y:Nat} {a b c:Int}
    (g : a + m*OfNat.ofNat x = b) (h : b + m*OfNat.ofNat y = c) : a + m * OfNat.ofNat (x+y) = c := by
  apply int_add_poly_lemma g h

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

theorem uninterpIntLemma {e v a m b:Int} (eq:e = v) (pr:a + m * v = b) : a + m * e = b := by
  rw [eq]
  exact pr

theorem uninterpNatLemma {e v : Nat} {a m b:Int} (eq:e = v) (pr:a + m * OfNat.ofNat v = b) : a + m * OfNat.ofNat e = b := by
  rw [eq]
  exact pr

structure AddResult where
  poly : Poly
  polyExpr : Expr
  equivProof : Expr

-- | @appendAddExprFromNat poly m _ e@ returns poly equivalent to `poly + m*OfNat.ofNat e` along with
--  proof that that poly.expr + m*e = ret.expr
private
partial def appendAddExprFromNat (m:Int) (m_ne:m ≠ 0) (e:Expr) (poly:Poly) : ArithM AddResult := do
  let varExpr ← getVarExprFn
  let aexpr ← poly.expr varExpr
  match ← matchOfNatNatLit e with
  | some x => do
    let r ←
      if xpr : (OfNat.ofNat x : Int) = 0 then
        let aexpr ← getPolyExpr poly
        let pr := mkIntRefl aexpr
        pure {
          poly := poly
          polyExpr := ← getPolyExpr poly
          equivProof := pr
        }
      else
        let y := m * x
        let svc ← (read : SolverM _)
        let pr ← Poly.addcProof varExpr poly y (Int.mul_ne_zero m_ne xpr)
        let poly := poly.addc y
        pure {
          poly := poly,
          polyExpr := ← getPolyExpr poly,
          equivProof := pr
        }
    return r
  | _ => pure ()

  -- Match addition
  let natAddConst : Expr :=
        let f := mkConst ``HAdd.hAdd [levelZero, levelZero, levelZero]
        let inst := mkAppN (mkConst ``instHAdd [levelZero]) #[natExpr, mkConst ``instAddNat]
        mkAppN f #[natExpr, natExpr, natExpr, inst]
  match ← matchBinOp natAddConst natExpr e with
  | none => pure ()
  | some (x, y) => do
    let { poly := poly, polyExpr := bexpr, equivProof := x_pr }
          ← appendAddExprFromNat m m_ne x poly
    let { poly := poly, polyExpr := cexpr, equivProof := y_pr }
          ← appendAddExprFromNat m m_ne y poly
    let pr := mkAppN (mkConst ``nat_add_poly_lemma) #[m, x, y, aexpr, bexpr, cexpr, x_pr, y_pr]
    return { poly := poly, polyExpr := ← getPolyExpr poly, equivProof := pr }


  let ⟨v, vExpr, eq⟩ ← getVarForExpr e
  let v ← getTheoryVar (Decl.uninterpNat v)
  let pr ← poly.addProof varExpr m m_ne v
  let poly := poly.add m v
  let bexpr ← poly.expr varExpr
  let pr := mkAppN (mkConst ``uninterpNatLemma) #[e, vExpr, aexpr, m, bexpr, eq, pr]
  return { poly := poly, polyExpr := bexpr, equivProof := pr }

-- | @appendAddExprFromInt poly m _ e@ returns poly equivalent to `poly + m*e` along with proof that that
-- poly.expr + m*e = ret.expr
private
partial def appendAddExprFromInt (m:Int) (m_ne:m ≠ 0) (e:Expr) (poly:Poly) : ArithM AddResult := do
  let e ← instantiateMVars e
  let varExpr ← getVarExprFn

  match ← matchIntLit e with
  | none => pure ()
  | some x =>
    let r ←
      if xpr : x = 0 then
        let aexpr ← getPolyExpr poly
        let pr := mkIntRefl aexpr
        pure {
          poly := poly
          polyExpr := ← getPolyExpr poly
          equivProof := pr
        }
      else
        let y := m * x
        -- pr: poly + m * x * 1 = r
        let svc ← (read : SolverM _)
        let pr ← Poly.addcProof varExpr poly y (Int.mul_ne_zero m_ne xpr)
        let poly := poly.addc y
        pure {
          poly := poly,
          polyExpr := ← getPolyExpr poly,
          equivProof := pr
        }
    return r

  -- Match addition
  let aexpr ← poly.expr varExpr
  match ← matchBinOp intAddConst intExpr e with
  | none => pure ()
  | some (x, y) => do
    let { poly := poly, polyExpr := bexpr, equivProof := x_pr }
          ← appendAddExprFromInt m m_ne x poly
    let { poly := poly, polyExpr := cexpr, equivProof := y_pr }
          ← appendAddExprFromInt m m_ne y poly
    let pr := mkAppN (mkConst ``int_add_poly_lemma) #[m, x, y, aexpr, bexpr, cexpr, x_pr, y_pr]
    return { poly := poly, polyExpr := ← getPolyExpr poly, equivProof := pr }

  -- Match sub
  match ← matchBinOp intSubConst intExpr e with
  | none => pure ()
  | some (x, y) => do
    let { poly := poly, polyExpr := bexpr, equivProof := x_pr }
          ← appendAddExprFromInt m m_ne x poly
    let bexpr ← poly.expr varExpr
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

  match ← matchOfNatofNatInt e with
  | none => pure ()
  | some e => do
    return ← appendAddExprFromNat m m_ne e poly

  let ⟨v, vExpr, eq⟩ ← getVarForExpr e
  let v ← getTheoryVar (Decl.uninterpInt v)
  let pr ← getPolyAddProof poly m m_ne v
  let poly := poly.add m v
  let bexpr ← getPolyExpr poly
  let pr := mkAppN (mkConst ``uninterpIntLemma) #[e, vExpr, aexpr, m, bexpr, eq, pr]
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

-- | Match `(Int.NonNeg e) and return proof term and property.
def matchIntNonNeg2 (r:IO.Ref ArithTheory.State) : Expr → SolverM (Option (TheoryPred × Expr)) :=
  matchrule `(Int.NonNeg $(mvar)) => do
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