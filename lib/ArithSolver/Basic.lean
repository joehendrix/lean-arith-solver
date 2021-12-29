import Std.Data.HashMap
import Lean.Meta
import ArithSolver.Int

open Lean
open Std (HashMap)

namespace Array
instance {α} [Hashable α] : Hashable (Array α) where
  hash
  | ⟨l⟩ => Hashable.hash l

end Array

namespace ArithSolver

private def intExpr := mkConst ``Int

def intAddExpr : Expr :=
  let f := mkConst ``HAdd.hAdd [levelZero, levelZero, levelZero]
  let inst := mkAppN (mkConst ``instHAdd [levelZero]) #[intExpr, mkConst ``Int.instAddInt]
  mkAppN f #[intExpr, intExpr, intExpr, inst]

def intSubExpr : Expr :=
  let f := mkConst ``HSub.hSub [levelZero, levelZero, levelZero]
  let inst := mkAppN (mkConst ``instHAdd [levelZero]) #[intExpr, mkConst ``Int.instSubInt]
  mkAppN f #[intExpr, intExpr, intExpr, inst]

def intMulExpr : Expr :=
  let f := mkConst ``HMul.hMul [levelZero, levelZero, levelZero]
  let inst := mkAppN (mkConst ``instHMul [levelZero]) #[intExpr, mkConst ``Int.instMulInt]
  mkAppN f #[intExpr, intExpr, intExpr, inst]

def intNegExpr : Expr :=
  let f := mkConst ``Neg.neg [levelZero]
  let inst := mkConst ``Int.instNegInt
  mkAppN f #[intExpr, inst]

-- def intMulExpr : Expr :=
--   mkApp (mkApp (mkConst ``Mul.mul [levelZero]) intExpr) (mkConst ``Int.instMulInt)

private def intOfNatExpr : Expr := mkConst ``Int.ofNat
private def intNegSuccExpr : Expr := mkConst ``Int.negSucc

def intNonNegExpr : Expr := mkConst ``Int.NonNeg
private def intNonNegMkExpr : Expr := mkConst ``Int.NonNeg.mk

-- Create a nat lit as an int
def natLitAsIntExpr (n:Nat) : Expr :=
  let z := mkRawNatLit n
  let ofNat := mkConst ``OfNat.ofNat [levelZero]
  let inst := mkConst ``Int.instOfNatInt
  mkAppN ofNat #[intExpr, z, mkApp inst z]

def mkIntLit : Int → Expr
| Int.ofNat n => natLitAsIntExpr n
| Int.negSucc n => mkApp intNegExpr (natLitAsIntExpr (n+1))

def intZeroExpr := natLitAsIntExpr 0

def notExpr : Expr := mkConst ``Not

def intEqExpr : Expr := mkApp (mkConst ``Eq [levelOne]) (mkConst ``Int)

def mkIntEq0Expr (e:Expr) : Expr :=
  mkAppN intEqExpr #[e, intZeroExpr]

def mkIntNonNegExpr (e:Expr) : Expr := mkApp intNonNegExpr e

-- | A variabe
structure Var where
  (index : UInt32)
  deriving BEq, Hashable, Repr

namespace Var

-- | "Variable" that denotes constant one.
protected def constOne : Var := ⟨0⟩

instance : ToString Var := ⟨λv => "v" ++ toString v.index⟩

instance : Inhabited Var := ⟨Var.constOne⟩

instance : LT Var where
  lt a b := LT.lt a.index b.index

instance (a b : Var) : Decidable (LT.lt a b) :=
  inferInstanceAs (Decidable (LT.lt a.index b.index))

end Var

-- | An atomic predicate
inductive Pred where
-- This denotes a proof of the form (v = 0)
| IsEq0 : Var → Pred
-- This denotes a proof of the form (Not (v = 0))
| IsNe0 : Var → Pred
-- This denotes a proof of the form (Int.NonNeg v)
| IsGe0 : Var → Pred

-- Represents a polynomial.
structure Poly where
  -- Poly should be a sorted array of non-zero integers and variable pairs.
  -- The
  elements : Array (Int × Var)
  deriving BEq, Hashable, Repr

namespace Poly


def scalarProd (f:Var → Expr) : Int × Var → Expr
| (m,  v) => mkAppN intMulExpr #[mkIntLit m, f v]

def firstScalarProd (f: Var → Expr) : Int × Var → Expr
| (m, ⟨0⟩) => mkIntLit m
| p => scalarProd f p

-- | Create polynomial denoting constant zero.
def zero : Poly := ⟨#[]⟩

instance : Inhabited Poly := ⟨zero⟩

-- | Create polynomial denoting constant zero.
def one : Poly := ⟨#[(1, Var.constOne)]⟩

-- | @add p i _ v@ returns poly denoting @p + i*v@.
def add : ∀(p:Poly) (m:Int), Var → Poly
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

--theorem zero_mv : 0 + m*v =

-- | Map polynomial to expression given mapping from variables
-- to expressions.
def buildExpr (f:Var → Expr) (e:Expr) (poly:Subarray (Int × Var)) : Expr := Id.run do
  let mut e := e
  for p in poly do
    e := mkAppN intAddExpr #[e, scalarProd f p]
  pure e

-- | Map polynomial to expression given mapping from variables
-- to expressions.
def expr (f:Var → Expr) : Poly → Expr
| ⟨#[]⟩ => intZeroExpr
| ⟨a⟩ => buildExpr f (firstScalarProd f a[0]) a[1:]


theorem buildProofLemma {x c a:Int} (h:x + c = a) (y:Int)
  : (x + y) + c = a + y := sorry

-- buildProof f x c a h rest where h is a proof of "x + c = a" returns
-- a proof "buildExpr f x rest + c = buildExpr f a rest"
def buildProof (f:Var → Expr) (x c a h :Expr) (rest:Subarray (Int × Var)) : Expr := Id.run do
  let mut x := x
  let mut a := a
  let mut h := h
  for p in rest do
    let y := scalarProd f p
    h := mkAppN (mkConst ``buildProofLemma) #[x,c, a, h, y]
    x := mkAppN intAddExpr #[x, y]
    a := mkAppN intAddExpr #[a, y]
  pure h


-- | Map polynomial to expression given mapping from variables
-- to expressions.
def sexpr (f:Var → Expr) (a:Array (Int × Var)) (i:Nat) : Expr :=
  if i = 0 then
    intZeroExpr
  else
    buildExpr f (firstScalarProd f a[0]) a[1:i]

theorem sum0Lemma (p q v:Int) : p*v + q*v = (p+q)*v := Eq.symm (Int.add_mul _ _ _)

theorem sumLemma (r p q v:Int) : (r + p*v) + q*v = r + (p+q)*v := by
  apply Eq.trans (Int.add_assoc r _ _)
  apply congrArg (fun y => r + y)
  exact sum0Lemma _ _ _

-- @mkSum0Proof f p q v@ with "p + q ≠ 0" produces a proof that
--   firstScalarProd f (p,v) + firstScalarProd (q,v) = firstScalarProd f (p+q, v)
def mkSum0Proof (f : Var → Expr) (p q:Int) (v:Var) : Expr :=
  mkAppN (mkConst ``sum0Lemma) #[ mkIntLit p, mkIntLit q, f v]

-- @mkSumProof f poly i p q v@ with "p + q ≠ 0" and i > 0 produces a proof that
--   expr f ⟨poly[0:i].toArray.push (p,v)⟩ + firstScalarProd (q,v) = expr f ⟨poly[0:i].toArray.push (p+q, v)⟩
def mkSumProof (f : Var → Expr) (poly:Array (Int × Var)) (i:Nat) (p q:Int) (v:Var) : Expr :=
  let r := sexpr f poly i
  mkAppN (mkConst ``sumLemma) #[r, mkIntLit p, mkIntLit q, f v]

theorem cancel0Lemma {p q:Int} (h : p+q = 0) (v:Int) : p*v + q*v = 0 := by
  apply Eq.trans (sum0Lemma p q v)
  exact @Eq.substr Int (λx => x * v = 0) _ _ h (Int.zero_mul v)

example        : (64:Int) + -64 = 0   := @cancel0Lemma (64) (-64) (@rfl Int 0) 1
example        : (-64:Int) + 64 = 0   := @cancel0Lemma (-64) (64) (@rfl Int 0) 1
example (v:Int): -64 * v + 64 * v = 0 := @cancel0Lemma (-64) 64   (@rfl Int 0) v
example (v:Int): 64 * v + -64 * v = 0 := @cancel0Lemma (64) (-64) (@rfl Int 0) v

-- @mkCancel0Proof f q v@ produces a proof that
--  firstScalarProd f (-q,v) + firstScalarProd (q,v) = intZeroExpr
def mkCancel0Proof (f : Var → Expr) (q:Int) (v:Var) : Expr :=
  let rflExpr := mkAppN (mkConst ``rfl [levelOne]) #[intExpr, intZeroExpr]
  mkAppN (mkConst ``cancel0Lemma) #[ mkIntLit (-q), mkIntLit q, rflExpr, f v]

theorem cancelLemma (r p q v:Int) (h : p+q = 0) : (r + p*v) + q*v = r := by
  apply Eq.trans (Int.add_assoc r _ _)
  exact Eq.trans (cancel0Lemma h v ▸ rfl) (Int.add_zero r)


-- @mkCancelProof f poly i q v@ with i > 0 produces a proof that
--  (expr f poly[0:i] + -q * v⟩) + scalarProd (q,v) = sexpr f poly[0:i]
def mkCancelProof (f : Var → Expr) (poly:Array (Int × Var)) (i:Nat) (q:Int) (v:Var) : Expr :=
  let r := sexpr f poly i
  let rflExpr := mkAppN (mkConst ``rfl [levelOne]) #[intExpr, intZeroExpr]
  mkAppN (mkConst ``cancelLemma) #[r, mkIntLit (-q), mkIntLit q, f v, rflExpr]

-- | @addProof f p m v@ returns proof showing that
-- @p.expr + firstScalarProd f (m, v) = (p.add m v).expr@.
def addProof (f:Var → Expr) : ∀(poly:Poly) (q:Int), q ≠ 0 → Var → Expr
| ⟨poly⟩, q, g, v =>
  let c := firstScalarProd f (q,v)
  let rec loop : ∀(i : Nat), Expr
      | 0 =>
        if poly.size = 0 then
          -- Prove (0:Int) + firstScalarProd f (q,v) = firstScalarProd f (q,v)
          mkApp (mkConst `Int.zero_add) c
        else Id.run do
          let x := scalarProd f poly[0]
          let a := mkAppN intAddExpr #[c, x]
          let h := mkAppN (mkConst `Int.add_comm) #[x, c]
          buildProof f x c a h poly[1:]
      | Nat.succ i =>
        let (p,u) := poly[i]
        if u < v then
          let x := buildExpr f (firstScalarProd f poly[0]) poly[1:i+1]
          let a := mkAppN intAddExpr #[x, c]
          let h := mkAppN (mkConst ``Eq.refl [levelOne]) #[intExpr, a]
          buildProof f x c a h poly[i+1:]
        else if v < u then
          loop i
        else -- v = u
          if p+q = 0 then
            if i = 0 then
              let a := intZeroExpr
              let x := firstScalarProd f poly[0]
              let h := mkCancel0Proof f q v
              buildProof f x c a h poly[i+1:]
            else
              let a := sexpr f poly i
              let x := mkAppN intAddExpr #[a, scalarProd f poly[i]]
              let h := mkCancelProof f poly i q v
              buildProof f x c a h poly[i+1:]
          else
            if i = 0 then
              let x := firstScalarProd f poly[0]
              let a := firstScalarProd f (p+q, v)
              let h := mkSum0Proof f p q v
              buildProof f x c a h poly[i+1:]
            else
              let x0 := sexpr f poly i
              let x := mkAppN intAddExpr #[x0, scalarProd f poly[i]]
              let a := mkAppN intAddExpr #[x0, scalarProd f (p+q, v)]
              let h := mkSumProof f poly i p q v
              buildProof f x c a h poly[i+1:]
  loop poly.size

protected def toString : Poly → String
| ⟨a⟩ =>
  let scalarProd : Int × Var → String
--          | (1, v) => varExpr s v
--          | (-1, v) => mkApp intNegExpr (varExpr s v)
        | (m,v) => s!"{m}*{v}"
  let firstScalarProd : Int × Var → String
        | (m, ⟨0⟩) => toString m
        | p => scalarProd p
  let polyIns := λ(e:String) h => s!"{e} + {scalarProd h}"
  a[1:].foldl polyIns (firstScalarProd a[0])

instance : ToString Poly where
  toString := Poly.toString

end Poly

-- | Identifies the origin of an assertion
inductive Assertion.Origin
-- | A local context with the given name, user name and the new name.
| localContext : FVarId → Name → FVarId → Origin
-- Assertion came from negating a goal with proofs using the new name
| negGoal : FVarId → Origin
-- Assertion came from a natural number from an uninterpreted declaration.
| uninterpNat : Origin

-- | Assertion added
structure Assertion where
  origin : Assertion.Origin
  proof : Expr
  prop : Pred

-- def int1Lit : Expr := mkApp (mkConst ``Int.ofNat) (mkLit (Literal.natVal 1))

-- Definition associated with a variable.
inductive Decl
| uninterp : Expr → Decl
| poly : Poly → Decl
deriving BEq, Hashable

namespace Decl

protected def toString : Decl → String
| uninterp e => s!"uninterp {e}"
| poly p => s!"poly {p}"

instance : ToString Decl where
  toString := Decl.toString

instance : Inhabited Decl := ⟨uninterp arbitrary⟩

end Decl

structure State where
  -- Map from expressions (which should have type 'Int') to the theor
  -- variable associated with it.
  exprMap : HashMap Decl Var := Std.mkHashMap
  -- Map from variables (which should have type 'Int') to the expression
  -- associated with it.
  varExprs : Array Decl := #[Decl.poly Poly.one]
  -- Predicates asserted to be true.
  assertions : Array Assertion := #[]

namespace State

partial def varExpr (s:State) (v:Var) : Expr :=
  match s.varExprs.get! v.index.toNat with
  | Decl.uninterp e => e
  | Decl.poly p => p.expr (varExpr s)

def predExpr (s:State) : Pred → Expr
| Pred.IsEq0 v => mkIntEq0Expr (s.varExpr v)
| Pred.IsNe0 v => mkApp notExpr (mkIntEq0Expr (s.varExpr v))
| Pred.IsGe0 v => mkApp intNonNegExpr (s.varExpr v)

end State

abbrev ArithM  := StateRefT State MetaM

@[inline] def ArithM.run (m : ArithM α) (s : State := {}) : MetaM (α × State) :=
  StateRefT'.run m s

-- | Return a theory variable associated with the given uninterpreted Lean expression.
def mkDeclVar (d:Decl) : ArithM Var := do
  let s ← get
  match s.exprMap.find? d with
  | none => pure ()
  | some v => return v
  IO.println $ s!"Creating variable {d}"
  let newVar := ⟨OfNat.ofNat s.varExprs.size⟩
  let newExprMap  := s.exprMap.insert d newVar
  let newVarExprs := s.varExprs.push d
  if (OfNat.ofNat s.varExprs.size : UInt32) = 0 then
    throwError m!"Arithmetic variable overflow."
  set { s with exprMap := newExprMap, varExprs := newVarExprs }
  return newVar

-- | Return a theory variable associated with the given uninterpreted Lean expression.
def getUninterpVar (e:Expr) : ArithM Var := do
  mkDeclVar (Decl.uninterp (← Meta.instantiateMVars e))

-- | Assert a predicate holds using the given expression to refer to the
-- proof.
def assertPred (origin:Assertion.Origin) (proof:Expr) (prop:Pred) : ArithM Unit := do
  let a := { origin := origin, proof := proof, prop := prop }
  modifyGet fun s => ((), { s with assertions := s.assertions.push a })

-- @polyAddProof s poly q _ v@ returns a proof that
--   @poly.expr varExpr s + firstScalarProd s.varExpr (m, v) = (poly.add m v).expr s.varExpr@.
def varAddProof (poly:Poly) (q:Int) (q_ne:q ≠ 0) (v:Var) : ArithM Expr := do
  let s ← get
  pure $ Poly.addProof (s.varExpr) poly q q_ne v


-- @polyAddProof s poly q _ v@ returns a proof that
--   @poly.expr varExpr s + firstScalarProd s.varExpr (m, v) = (poly.add m v).expr s.varExpr@.
def polyAddProof (poly:Poly) (q:Int) (q_ne:q ≠ 0) (v:Var) : ArithM Expr := do
  let s ← get
  pure $ Poly.addProof (s.varExpr) poly q q_ne v


/-
structure Equiv where
  -- New type representation
  newInt : Expr
  -- An equality
  eqProof : Expr

def Poly.mkEquiv : Poly → MetaM Equiv := sorry

-- structure PolyV (v:Int) where
--  sorry : Int

def processAdd (p m u v a b : Int)
  (g: p + m * u = a)
  (h: a + m * v = b)
  : p + m * (u+v) = b := sorry

def processSub (p m u v a b : Int)
  (g: p + m * u = a)
  (h: a + (-m) * v = b)
  : p + m * (u-v) = b := sorry

-- def pushLeftAdd (z x y : Int) : BinPoly z m (x + y) → BinPoly z m x
-/


end ArithSolver