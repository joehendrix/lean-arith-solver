/-
This contains the definitions related to numeric expression
normalization.
-/
import ArithSolver.ArithM

open Lean
open Lean.Meta

namespace ArithSolver
namespace State

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

-- polyProofAddContext s x c a h poly idx where h is a proof of "x + c = a" returns
-- a proof "(x + poly[idx] + poly[idx+1] + ..) + c = a + poly[idx] + poly[idx+1] + .."
private
def polyProofAddContext (s:State) (x c a:IntExpr) (h:Expr) (poly:Poly) (idx:Nat) : Expr := Id.run do
  let mut x := x
  let mut a := a
  let mut h := h
  for p in poly.elements[idx:] do
    let y := s.scalarProd p
    h := mkAppN (mkConst ``polyProofAddContextLemma) #[x, c, a, h, y]
    x := x + y
    a := a + y
  pure h

-- | @addProof f p m v@ returns proof showing that
-- @p.expr + firstScalarProd f (m, v) = (p.add m v).expr@.
private
def polyAddProof (s:State) : ∀(poly:Poly) (q:Int), q ≠ 0 → Var → Expr
| poly, q, g, v =>
  let c := s.scalarProd (q,v)
  let rec loop : ∀(i : Nat), Expr
      | 0 =>
        if poly.elements.size = 0 then
          -- Prove (0:Int) + firstScalarProd f (q,v) = firstScalarProd f (q,v)
          mkApp (mkConst `Int.zero_add) c
        else Id.run do
          let x := s.scalarProd poly.elements[0]
          let a := c + x
          let h := mkAppN (mkConst `Int.add_comm) #[x, c]
          polyProofAddContext s x c a h poly 1
      | Nat.succ i =>
        let (p,u) := poly.elements[i]
        if u < v then
          let x := s.polyExpr poly (limit := i+1)
          let a := x + c
          let h := mkAppN (mkConst ``Eq.refl [levelOne]) #[intExpr, a]
          polyProofAddContext s x c a h poly (i+1)
        else if v < u then
          loop i
        else -- v = u
          if p+q = 0 then
            if i = 0 then
              let x := s.scalarProd poly.elements[0]
              let a := (0 : Int)
              let rflExpr := mkAppN (mkConst ``rfl [levelOne]) #[intExpr, intZeroExpr]
              -- Create proof: -q*v + q*v = 0.
              let h := mkAppN (mkConst ``cancel0Lemma) #[ (-q : Int), q, rflExpr, s.varExpr v]
              polyProofAddContext s x c a h poly (i+1)
            else
              let a := s.polyExpr poly i
              let x := a + s.scalarProd poly.elements[i]
              let rflExpr := mkAppN (mkConst ``rfl [levelOne]) #[intExpr, intZeroExpr]
              -- Create proof: (r + -q*v) + q*v = r.
              let h := mkAppN (mkConst ``cancelLemma) #[a, (-q : Int), q, s.varExpr v, rflExpr]
              polyProofAddContext s x c a h poly (i+1)
          else
            if i = 0 then
              let x := s.scalarProd poly.elements[0]
              let a := s.scalarProd (p+q, v)
              --  Create proof (p*v) + (q*v) = (p+q) * v
              let h := mkAppN (mkConst ``sum0Lemma) #[p, q, s.varExpr v]
              polyProofAddContext s x c a h poly (i+1)
            else
              let r := s.polyExpr poly i
              let x := r + s.scalarProd poly.elements[i]
              let a := r + s.scalarProd (p+q, v)
              let h := mkAppN (mkConst ``sumLemma) #[r, p, q, s.varExpr v]
              polyProofAddContext s x c a h poly (i+1)
  loop poly.elements.size

end State

-- @polyAddProof s poly q _ v@ returns a proof that
--   @poly.expr varExpr s + firstScalarProd s.varExpr (m, v) = (poly.add m v).expr s.varExpr@.
def polyAddProof (poly:Poly) (q:Int) (q_ne:q ≠ 0) (v:Var) : ArithM Expr := do
  let s ← get
  pure $ s.polyAddProof poly q q_ne v

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

-- | @appendAddExpr poly m e@ returns poly equivalent to `poly + m*e` along with proof that that
-- poly.expr + m*e = ret.expr
private
partial def appendAddExprFromInt (m:Int) (m_ne:m ≠ 0) (e:Expr) (poly:Poly)
   : ArithM (Poly × Expr) := do

  match ← matchIntLit e with
  | none => pure ()
  | some x =>
    let r ←
      if x_ne : x = 0 then
        let aexpr ← polyExpr poly
        let pr := mkAppN (mkConst ``rfl [levelOne]) #[intExpr, aexpr]
        pure (poly, pr)
      else
        let y := m * x
        -- p + m * x * 1 = return
        let pr ← polyAddProof poly y (Int.mul_ne_zero m_ne x_ne) Var.one
        pure (poly.add y Var.one, pr)
    return r

  -- Match add
  match ← matchBinOp intAddConst intExpr e with
  | none => pure ()
  | some (x, y) => do
    let aexpr ← polyExpr poly
    let (poly, x_pr) ← appendAddExprFromInt m m_ne x poly
    let bexpr ← polyExpr poly
    let (poly, y_pr) ← appendAddExprFromInt m m_ne y poly
    let cexpr ← polyExpr poly
    let pr := mkAppN (mkConst ``add_poly_lemma) #[m, x, y, aexpr, bexpr, cexpr, x_pr, y_pr]
    return (poly, pr)

  -- Match sub
--  let subExpr := mkAppN (mkConst ``Sub.sub [levelZero]) #[intExpr, mkConst ``Int.instSubInt]
--  let subExpr := mkConst ``Int.sub
  match ← matchBinOp intSubConst intExpr e with
  | none =>
    pure ()
  | some (x, y) => do
    let aexpr ← polyExpr poly
    let (poly, x_pr) ← appendAddExprFromInt m m_ne x poly
    let bexpr ← polyExpr poly
    let (poly, y_pr) ← appendAddExprFromInt (- m) (Int.neg_ne_zero m_ne) y poly
    let cexpr ← polyExpr poly
    let pr := mkAppN (mkConst ``sub_poly_lemma) #[m, x, y, aexpr, bexpr, cexpr, x_pr, y_pr]
    return (poly, pr)

  -- Match negation
  let negExpr := mkAppN (mkConst ``Neg.neg [levelZero]) #[intExpr, mkConst ``Int.instNegInt]
  match ← matchUnaryOp negExpr intExpr e with
  | none => pure ()
  | some x => do
    let aexpr ← polyExpr poly
    let (poly, x_pr) ← appendAddExprFromInt (-m) (Int.neg_ne_zero m_ne) x poly
    let bexpr ← polyExpr poly
    let pr := mkAppN (mkConst ``neg_poly_lemma) #[m, x, aexpr, bexpr, x_pr]
    return (poly, pr)

  -- Match scalar multiplication
  match ← matchBinOp intMulConst intExpr e with
  | none => pure ()
  | some (x, y) => do
    let aexpr ← polyExpr poly
    match ← matchIntLit x with
    | none =>
      pure ()
    | some xn =>
      let r ←
        if xn_ne:xn = 0 then
          let pr := mkAppN (mkConst ``mul_zero_lhs_poly_lemma) #[m, y, aexpr]
          -- aexpr + m*(0*y) = aexpr
          pure (poly, pr)
        else
          -- y_eq: aexpr + (m*x)*y = poly'.expr
          let (poly, y_eq) ← appendAddExprFromInt (m * xn) (Int.mul_ne_zero m_ne xn_ne) y poly
          let bexpr ← polyExpr poly
          let pr := mkAppN (mkConst ``mul_lhs_poly_lemma) #[m, x, y, aexpr, bexpr]
          pure (poly, pr)
      return r
    match ← matchIntLit y with
    | none =>
      pure ()
    | some yn =>
      let r ←
        if n_ne:yn = 0 then
          let pr := mkAppN (mkConst ``mul_zero_rhs_poly_lemma) #[m, x, aexpr]
          pure (poly, pr)
        else
          let (p, x_eq) ← appendAddExprFromInt (m * yn) (Int.mul_ne_zero m_ne n_ne) x poly
          let bexpr ← polyExpr poly
          let pr := mkAppN (mkConst ``mul_rhs_poly_lemma) #[m, x, y, aexpr, bexpr]
          pure (poly, pr)
      return r
    pure ()

  let v ← getUninterpVar (← instantiateMVars e)
  let pr ← polyAddProof poly m m_ne v
  pure (poly.add m v, pr)

theorem purifyIntLemmaPoly {x y:Int} (p:0 + 1 * x = y) : x = y := by
  simp [Int.zero_add, Int.one_mul] at p
  exact p

theorem purifyIntLemmaVar {x y:Int} (p:0 + 1 * x = 1 * y) : x = y :=
  Eq.trans (purifyIntLemmaPoly p) (Int.one_mul y)

-- | This traverses an expression (which should have type int) to normalize
-- the expression.  It produces a variable along with a proof that
-- e = v.expr
def purifyIntExpr (e:Expr) : ArithM (Var × Expr) := do
  have g : 1 ≠ 0 := by
    apply Nat.noConfusion
  have one_ne : (1:Int) ≠ 0 := λx => Int.noConfusion x g
  let e ← instantiateMVars e
  let (p,pr) ← appendAddExprFromInt 1 one_ne e Poly.zero
  -- pr  has type" 0 + 1 * e = p.expr"
  match p with
  | ⟨#[(1, v)]⟩ => do
    -- Make pr have type e = v
    let pr := mkAppN (mkConst ``purifyIntLemmaVar) #[e, ← varExpr v, pr]
    pure (v, pr)
  | otherwise => do
    let v ← getPolyVar p
    -- Make pr have type e = v
    let pr := mkAppN (mkConst ``purifyIntLemmaPoly) #[e, ← polyExpr p, pr]
    pure (v, pr)

end Normalization

end ArithSolver