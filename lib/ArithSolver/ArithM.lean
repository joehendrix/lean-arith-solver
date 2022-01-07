/-
This defines the ArithM monad basic operations used to generate a system of
numerical equations from a Lean local context.
-/
import ArithSolver.Basic
import ArithSolver.Int

open Lean
open Std (HashMap)

namespace ArithSolver

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

-- Create a nat lit as an int
def natLitAsIntExpr (n:Nat) : IntExpr :=
  let z := mkRawNatLit n
  let ofNat := mkConst ``OfNat.ofNat [levelZero]
  let inst := mkConst ``Int.instOfNatInt
  IntExpr.mk (mkAppN ofNat #[intExpr, z, mkApp inst z])

def mkIntLit : Int → IntExpr
| Int.ofNat n => natLitAsIntExpr n
| Int.negSucc n => IntExpr.mk (mkApp intNegConst (natLitAsIntExpr (n+1)))

instance : Coe Int IntExpr where
  coe := fun x => mkIntLit x

def intZeroExpr : IntExpr := natLitAsIntExpr 0

private def intNonNegExpr : Expr := mkConst ``Int.NonNeg
def mkIntNonNegExpr (e:Expr) : Expr := mkApp intNonNegExpr e

private def intEqExpr : Expr := mkApp (mkConst ``Eq [levelOne]) (mkConst ``Int)
def mkIntEq0Expr (e:Expr) : Expr := mkAppN intEqExpr #[e, intZeroExpr]

end ExpressionUtils

-- Represents a polynomial.
structure Poly where
  -- Poly should be a sorted array of non-zero integers and variable pairs.
  -- The
  elements : Array (Int × TheoryVar)
  deriving BEq, Hashable, Repr

namespace Poly

-- | Create polynomial denoting constant zero.
def zero : Poly := ⟨#[]⟩

instance : Inhabited Poly := ⟨zero⟩

-- | Create polynomial denoting constant zero.
protected def one : Poly := ⟨#[(1, ⟨0⟩)]⟩

-- | @add p i _ v@ returns poly denoting @p + i*v@.
def add : ∀(p:Poly) (m:Int), TheoryVar → Poly
| ⟨a⟩, q, v =>
  let rec loop : ∀(i : Nat), Poly
      | 0 => ⟨a.insertAt 0 (q, v)⟩
      | Nat.succ i =>
        let (p,u) := a[i]
        if u < v then
          ⟨a.insertAt (i+1) (q,v)⟩
        else if v < u then
          loop i
        else -- v = u
          let q := p+q
          if q = 0 then
            ⟨a.eraseIdx i⟩
          else
            ⟨a.set! i (q,v)⟩
  loop a.size

protected def toString : Poly → String
| ⟨a⟩ =>
  let scalarProd : Int × TheoryVar → String
        | (m,v) => s!"{m}*{v}"
  let firstScalarProd : Int × TheoryVar → String
        | (m, ⟨0⟩) => toString m
        | p => scalarProd p
  let polyIns := λ(e:String) h => s!"{e} + {scalarProd h}"
  a[1:].foldl polyIns (firstScalarProd a[0])

instance : ToString Poly where
  toString := Poly.toString

end Poly

-- Definition associated with a variable.
inductive Decl
  -- Theory variable is equal to the expression.
| uninterp : Var → Decl
  -- Theory variable is equal to polynomial.
| poly : Poly → Decl
deriving BEq, Hashable

namespace Decl

protected def toString : Decl → String
| uninterp v => s!"uninterp {v}"
| poly p => s!"poly {p}"

instance : ToString Decl where
  toString := Decl.toString

instance : Inhabited Decl := ⟨uninterp arbitrary⟩

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

mutual

variable (r:IO.Ref State)
variable (f: Var → IO IntExpr)

partial def scalarProd : Int × TheoryVar → IO IntExpr
| (m, ⟨0⟩) => m
| (m,  v) => do IntExpr.mk (mkAppN intMulConst #[m, ← thvarExpr v])

-- | Map polynomial to expression given mapping from variables
-- to expressions.
-- The optional parameter allowss this to to only take the first n elements.
partial def polyExpr (poly:Poly) (limit: optParam Nat (poly.elements.size)) : IO IntExpr := do
  if limit > poly.elements.size then
    panic! "polyExpr given bad limit."
  if limit = 0 then
    (0 : Int)
  else do
    let mut e ← scalarProd poly.elements[0]
    for p in poly.elements[1:limit] do
      e := e + (← scalarProd p)
    pure e

-- | Return Lean expression associated with IntExpr
partial def thvarExpr (v:TheoryVar) : IO IntExpr := do
  let s ← r.get
  if p : v.toNat < s.vars.size then
    match s.vars.get ⟨v.toNat, p⟩  with
    | Decl.uninterp v => do
      f v
    | Decl.poly p => polyExpr p
  else
    panic! s!"Invalid theory variable index {v} (max = {s.vars.size})"

end

abbrev ArithM := ReaderT (IO.Ref State) SolverM

-- | Return a theory variable associated with the given uninterpreted Lean expression.
private def getVar (d:Decl) : ArithM TheoryVar := do
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
def getUninterpVar (v:Var) : ArithM TheoryVar := getVar (Decl.uninterp v)

-- | Return a theory variable associated with the given uninterpreted Lean expression.
def getPolyVar (p:Poly) : ArithM TheoryVar := getVar (Decl.poly p)


/-
-- | Assert a predicate holds using the given expression to refer to the
-- proof.
def assertPred (origin:Option FVarId) (userName:Name) (proof:Expr) (prop:Pred) : ArithM Solver Unit := do
  let a := { origin := origin, name := userName, proof := proof, prop := prop }
  modifyGet fun s => ((), { s with assertions := s.assertions.push a })
-/

def getThvarExpr (v:TheoryVar) : ArithM IntExpr := do
  let svc ← (read : SolverM _)
  let f (v:Var) : IO IntExpr := IntExpr.mk <$> svc.varExpr v
  let r ← read
  thvarExpr r f v

-- | Return expression associated with in solver.
def getPolyExpr (poly:Poly) : ArithM IntExpr := do
  let svc ← (read : SolverM _)
  let f (v:Var) : IO IntExpr := IntExpr.mk <$> svc.varExpr v
  let r ← read
  polyExpr r f poly

def getTheoryPred (p:Pred) : ArithM TheoryPred := do
  let r ← read
  let s ← r.get
  if TheoryPred.max ≤ s.preds.size then
    throwError "Only 2^32 arithmetic variables allowed."
  let n := TheoryPred.ofNat (s.preds.size)
  r.set { s with preds := s.preds.push p }
  pure n

def mthvarExpr (r: IO.Ref State) (f : Var → IO Expr)  (thv : TheoryVar) : IO Expr := do
  IntExpr.toExpr <$> thvarExpr r (fun v => IntExpr.mk <$> f v) thv

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

end ArithSolver