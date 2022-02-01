/-
This defines the ArithM monad basic operations used to generate a system of
numerical equations from a Lean local context.
-/
import ClausalExtraction.Basic
import ClausalExtraction.ArithTheory.Int

open Lean -- (Expr levelZero levelOne mkApp mkAppN mkConst mkRawNatLit)
open Std (HashMap)

namespace ClausalExtraction

namespace ArithTheory

section ExpressionUtils

def natExpr : Expr := mkConst ``Nat
def intExpr := mkConst ``Int

private def notExpr : Expr := mkConst ``Not

def intAddConst : Expr :=
  let f := mkConst ``HAdd.hAdd [levelZero, levelZero, levelZero]
  let inst := mkAppN (mkConst ``instHAdd [levelZero]) #[intExpr, mkConst ``Int.instAddInt]
  mkAppN f #[intExpr, intExpr, intExpr, inst]

def intSubConst : Expr :=
  let f := mkConst ``HSub.hSub [levelZero, levelZero, levelZero]
  let inst := mkAppN (mkConst ``instHAdd [levelZero]) #[intExpr, mkConst ``Int.instSubInt]
  mkAppN f #[intExpr, intExpr, intExpr, inst]

def intMulConst : Expr :=
  let f := mkConst ``HMul.hMul [levelZero, levelZero, levelZero]
  let inst := mkAppN (mkConst ``instHMul [levelZero]) #[intExpr, mkConst ``Int.instMulInt]
  mkAppN f #[intExpr, intExpr, intExpr, inst]

def intNegConst : Expr :=
  let f := mkConst ``Neg.neg [levelZero]
  let inst := mkConst ``Int.instNegInt
  mkAppN f #[intExpr, inst]

-- A structure used to denote an integer expression
structure IntExpr where
  toExpr : Expr
  deriving BEq, Hashable, Inhabited

namespace IntExpr

instance : Coe IntExpr Expr where
  coe := IntExpr.toExpr

instance : Add IntExpr where
  add := λx y => IntExpr.mk (mkAppN intAddConst #[x, y])

end IntExpr

-- Create a nat as an int
def mkOfNat (n:Expr) : IntExpr :=
  let ofNat := mkConst ``OfNat.ofNat [levelZero]
  let inst := mkConst ``Int.instOfNatInt
  IntExpr.mk (mkAppN ofNat #[intExpr, n, mkApp inst n])

-- Create a nat lit as an int
def natLitAsIntExpr (n:Nat) : IntExpr := mkOfNat (mkRawNatLit n)

def mkIntLit : Int → IntExpr
| Int.ofNat n => natLitAsIntExpr n
| Int.negSucc n => IntExpr.mk (mkApp intNegConst (natLitAsIntExpr (n+1)))

instance : Coe Int IntExpr where
  coe := mkIntLit

def intZeroExpr : IntExpr := mkIntLit 0

private def intNonNegExpr : Expr := mkConst ``Int.NonNeg
def mkIntNonNegExpr (e:Expr) : Expr := mkApp intNonNegExpr e

private def intEqExpr : Expr := mkApp (mkConst ``Eq [levelOne]) (mkConst ``Int)
def mkIntEq0Expr (e:Expr) : Expr := mkAppN intEqExpr #[e, intZeroExpr]

end ExpressionUtils

-- Represents a polynomial.
structure Poly where
  -- Poly should be a sorted array of non-zero integers and variable pairs.
  elements : Array (Int × TheoryVar)
  deriving BEq, Hashable, Repr

namespace Poly

-- | Create polynomial denoting constant zero.
protected def const (z:Int) : Poly := ⟨#[(z, ⟨0⟩)]⟩

-- | Create polynomial denoting constant zero.
protected def zero : Poly := Poly.const 0

-- | Create polynomial denoting constant zero.
protected def one : Poly := Poly.const 1

instance : Inhabited Poly := ⟨Poly.zero⟩

-- | Create polynomial denoting constant zero.
-- protected def one : Poly := ⟨#[(1, ⟨0⟩)]⟩

def addc : Poly → Int → Poly
| ⟨a⟩, q =>
  let (p,v) := a.get! 0
  ⟨a.set! 0 (p+q, v)⟩

-- | @add p i _ v@ returns poly denoting @p + i*v@.
def add : Poly → Int → TheoryVar → Poly
| ⟨a⟩, q, v =>
  let rec loop : ∀(i : Nat), Poly
      | 0 => ⟨a.insertAt 1 (q, v)⟩
      | Nat.succ i =>
        let (p,u) := a[i+1]
        if v < u then
          loop i
        else if u < v then
          ⟨a.insertAt (i+2) (q,v)⟩
        else -- v = u
          let q := p+q
          if q = 0 then
            ⟨a.eraseIdx (i+1)⟩
          else
            ⟨a.set! (i+1) (q,v)⟩
  loop (a.size-1)

protected def toString : Poly → String
| ⟨a⟩ =>
  let scalarProd : Int × TheoryVar → String
        | (m,v) => s!"{m}*{v}"
  let firstScalarProd : Int × TheoryVar → String
        | (m, _) => toString m
  let polyIns := λ(e:String) h => s!"{e} + {scalarProd h}"
  a[1:].foldl polyIns (firstScalarProd a[0])

instance : ToString Poly where
  toString := Poly.toString

def scalarProd (f: v → IO IntExpr) : Int × v → IO IntExpr
| (m,  v) => do IntExpr.mk (mkAppN intMulConst #[m, ← f v])

-- | Create an reflexivity proof from the int expression.
def mkIntRefl (e:IntExpr) : Expr := mkApp (mkApp (mkConst ``rfl [levelOne]) intExpr) e

-- | Map polynomial to expression given mapping from variables
-- to expressions.
-- The optional parameter allowss this to to only take the first n elements.
protected
def expr (poly:Poly) (f: TheoryVar → IO IntExpr) (limit: optParam Nat (poly.elements.size - 1)) : IO IntExpr := do
  if poly.elements.size = 0 then
    panic! "Empty polyExpr"
  if limit ≥ poly.elements.size then
    panic! "polyExpr given bad limit."
  let mut e : IntExpr ← poly.elements[0].fst
  for p in poly.elements[1:limit+1] do
    e := e + (← scalarProd f p)
  pure e

private
theorem polyProofAddContextLemma {c x a:Int} (h:x + c = a) (y:Int)
  : (x + y) + c = a + y := by
  simp [h.symm, Int.add_assoc, Int.add_comm y c]

-- polyProofAddContext s x c a h poly idx where h is a proof of "x + c = a" returns
-- a proof "(x + poly[idx] + poly[idx+1] + ..) + c = a + poly[idx] + poly[idx+1] + .."
private
def polyProofAddContext (f:TheoryVar → IO IntExpr) (x c a:IntExpr) (h:Expr) (poly:Poly) (idx:Nat) : IO Expr := do
  let mut x := x
  let mut a := a
  let mut h := h
  let pr := mkApp (mkConst ``polyProofAddContextLemma) c
  for p in poly.elements[idx:] do
    let y ← scalarProd f p
    h := mkAppN pr #[x, a, h, y]
    x := x + y
    a := a + y
  pure h

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

end Lemmas

def addcProof (f:TheoryVar → IO IntExpr) (poly:Poly) (c:Int) (g:c ≠ 0) : IO Expr := do
  let x := poly.elements[0].fst
  let a := x + c
  let h := mkIntRefl a
  polyProofAddContext f x c a h poly 1

-- | @addProof f p m v@ returns proof showing that
-- @p.expr + scalarProd f (m, v) = (p.add m v).expr@.
def addProof (f:TheoryVar → IO IntExpr) : ∀(poly:Poly) (q:Int), q ≠ 0 → TheoryVar → IO Expr
| poly, q, g, v => do
  let c ← scalarProd f (q, v)
  let rec loop : ∀(i : Nat), IO Expr
      | 0 => do
        -- Handle case where var is zero.
        let x : IntExpr := poly.elements[0].fst
        let a := x + c
        let h := mkIntRefl a
        polyProofAddContext f x c a h poly 1
      | Nat.succ i => do
        let (p,u) := poly.elements[i+1]
        if v < u then
          loop i
        else if u < v then
          let x ← poly.expr f (limit := i+1)
          let a := x + c
          let h := mkIntRefl a
          polyProofAddContext f x c a h poly (i+2)
        else -- v = u
          if p+q = 0 then
            let a ← poly.expr f (limit := i)
            let x := a + (← scalarProd f (p,u))
            let rflExpr := mkIntRefl intZeroExpr
            -- Create proof: (a + -q*v) + q*v = a.
            let h := mkAppN (mkConst ``cancelLemma) #[a, (-q : Int), q, ← f v, rflExpr]
            polyProofAddContext f x c a h poly (i+2)
          else
            let r ← poly.expr f (limit := i)
            let x := r + (←scalarProd f (p, u))
            let a := r + (←scalarProd f (p+q, u))
            let h := mkAppN (mkConst ``sumLemma) #[r, p, q, ←f v]
            polyProofAddContext f x c a h poly (i+2)
  loop (poly.elements.size - 1)

end Poly

-- Definition associated with a variable.
inductive Decl
  -- A int variable from another theory.
| uninterpInt : Var → Decl
  -- A nat variable from another theory.
| uninterpNat : Var → Decl
  -- Theory variable is equal to polynomial.
| poly : Poly → Decl
deriving BEq, Hashable

namespace Decl

protected def toString : Decl → String
| uninterpInt v => s!"{v}"
| uninterpNat v => s!"ofNat {v}"
| poly p => s!"poly {p}"

instance : ToString Decl where
  toString := Decl.toString

instance : Inhabited Decl := ⟨uninterpInt arbitrary⟩

end Decl

-- | An atomic predicate
inductive Pred where
-- This denotes a proof of the form (v = 0)
| IsEq0 : TheoryVar → Pred
-- This denotes a proof of the form (Not (v = 0))
| IsNe0 : TheoryVar → Pred
-- This denotes a proof of the form (Int.NonNeg v)
| IsGe0 : TheoryVar → Pred
  deriving Inhabited

namespace Pred

protected def toString : Pred → String
| IsEq0 v => s!"IsEq0 {v}"
| IsNe0 v => s!"IsNe0 {v}"
| IsGe0 v => s!"IsGe0 {v}"

instance : ToString Pred := ⟨Pred.toString⟩

end Pred

def oneVar : TheoryVar := ⟨0⟩

structure State : Type where

  exprMap : HashMap Decl TheoryVar := Std.mkHashMap.insert (Decl.poly Poly.one) oneVar
  vars : Array Decl := #[Decl.poly Poly.one]
  preds : Array Pred := #[]

section

variable (r:IO.Ref State)
variable (f: Var → IO Expr)

-- | Return Lean expression associated with IntExpr
partial def thvarExpr (v:TheoryVar) : IO IntExpr := do
  let s ← r.get
  if p : v.toNat < s.vars.size then
    match s.vars.get ⟨v.toNat, p⟩  with
    | Decl.uninterpInt v => do
      IntExpr.mk <$> f v
    | Decl.uninterpNat v => do
      mkOfNat <$> f v
    | Decl.poly p => p.expr (thvarExpr)
  else
    panic! s!"Invalid theory variable index {v} (max = {s.vars.size})"

end

abbrev ArithM := ReaderT (IO.Ref State) SolverM

-- | Return a theory variable associated with the given uninterpreted Lean expression.
def getTheoryVar (d:Decl) : ArithM TheoryVar := do
  let r ← read
  let s ← r.get
  match s.exprMap.find? d with
  | none => pure ()
  | some v => return v
  let newVar := ⟨OfNat.ofNat s.vars.size⟩
  if (newVar.index : UInt32) = 0 then
    throwError m!"Only 2^32 arithmetic variables allowed."
  r.set
    { s with exprMap := s.exprMap.insert d newVar,
             vars := s.vars.push d }
  return newVar

-- | Return a theory variable associated with the given uninterpreted Lean expression.
def getPolyVar (p:Poly) : ArithM TheoryVar := getTheoryVar (Decl.poly p)

def getThvarExpr (v:TheoryVar) : ArithM IntExpr := do
  let svc ← (read : SolverM _)
  let r ← read
  thvarExpr r svc.varExpr v

-- | Return expression associated with in solver.
def getPolyExpr (poly:Poly) : ArithM IntExpr := do
  let svc ← (read : SolverM _)
  let r ← read
  let f (v:TheoryVar) : IO IntExpr := thvarExpr r svc.varExpr v
  poly.expr f

def getTheoryPred (p:Pred) : ArithM TheoryPred := do
  let r ← read
  let s ← r.get
  if TheoryPred.max ≤ s.preds.size then
    throwError "Only 2^32 arithmetic variables allowed."
  let n := TheoryPred.ofNat (s.preds.size)
  r.set { s with preds := s.preds.push p }
  pure n

def mthvarExpr (r: IO.Ref State) (f : Var → IO Expr)  (thv : TheoryVar) : IO Expr := do
  IntExpr.toExpr <$> thvarExpr r f thv

def predExpr (r : IO.Ref State) (f : Var → IO Expr) (idx : TheoryPred) : IO Expr := do
  let s ← r.get
  if lt : idx.toNat < s.preds.size  then
    match s.preds.get ⟨idx.toNat, lt⟩  with
    | Pred.IsEq0 v => mkIntEq0Expr <$> mthvarExpr r f v
    | Pred.IsNe0 v => mkApp notExpr <$> (mkIntEq0Expr <$> mthvarExpr r f v)
    | Pred.IsGe0 v => mkIntNonNegExpr <$> mthvarExpr r f v
  else
    panic s!"Invalid predicate index {idx} (max = {s.preds.size})"

end ArithTheory

end ClausalExtraction