/-
This defines the ArithM monad basic operations used to generate a system of
numerical equations from a Lean local context.
-/
import ArithSolver.Basic
import ArithSolver.Int

open Lean

namespace ArithSolver

private def notExpr : Expr := mkConst ``Not

private def intExpr := mkConst ``Int

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
  deriving Inhabited

instance : Coe IntExpr Expr where
  coe := IntExpr.toExpr

instance : Add IntExpr where
  add := λx y => IntExpr.mk (mkAppN intAddConst #[x, y])

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

private def intZeroExpr : IntExpr := natLitAsIntExpr 0

private def intNonNegExpr : Expr := mkConst ``Int.NonNeg
def mkIntNonNegExpr (e:Expr) : Expr := mkApp intNonNegExpr e

private def intEqExpr : Expr := mkApp (mkConst ``Eq [levelOne]) (mkConst ``Int)
def mkIntEq0Expr (e:Expr) : Expr := mkAppN intEqExpr #[e, intZeroExpr]

namespace State

def scalarProd (f:Var → IntExpr) : Int × Var → IntExpr
| (m, ⟨0⟩) => m
| (m,  v) => IntExpr.mk (mkAppN intMulConst #[m, f v])

-- | Map polynomial to expression given mapping from variables
-- to expressions.
def buildExpr (f:Var → IntExpr) (e:IntExpr) (poly:Subarray (Int × Var)) : IntExpr := Id.run do
  let mut e := e
  for p in poly do
    e := e + scalarProd f p
  pure e

-- | Map polynomial to expression given mapping from variables
-- to expressions.
def sexpr (f:Var → IntExpr) (a:Array (Int × Var)) (i:Nat) : IntExpr :=
  if i = 0 then
    (0 : Int)
  else
    buildExpr f (scalarProd f a[0]) a[1:i]

mutual

-- | Map polynomial to expression given mapping from variables
-- to expressions.
partial def polyExpr (s:State) (p:Poly) : IntExpr := sexpr s.varExpr p.elements p.elements.size

partial def varExpr (s:State) (v:Var) : IntExpr :=
  match s.varExprs.get! v.index.toNat with
  | Decl.uninterp e => IntExpr.mk e
  | Decl.poly p => polyExpr s p

end

theorem sum0Lemma (p q v:Int) : p*v + q*v = (p+q)*v := Eq.symm (Int.add_mul _ _ _)

-- @mkSum0Proof f p q v@ with "p + q ≠ 0" produces a proof that
--   firstScalarProd f (p,v) + firstScalarProd (q,v) = firstScalarProd f (p+q, v)
def mkSum0Proof (f : Var → IntExpr) (p q:Int) (v:Var) : Expr :=
  mkAppN (mkConst ``sum0Lemma) #[ p, q, f v]

theorem sumLemma (r p q v:Int) : (r + p*v) + q*v = r + (p+q)*v := by
  apply Eq.trans (Int.add_assoc r _ _)
  apply congrArg (fun y => r + y)
  exact sum0Lemma _ _ _

-- @mkSumProof f poly i p q v@ with "p + q ≠ 0" and i > 0 produces a proof that
--   expr f ⟨poly[0:i].toArray.push (p,v)⟩ + firstScalarProd (q,v) = expr f ⟨poly[0:i].toArray.push (p+q, v)⟩
def mkSumProof (f : Var → IntExpr) (poly:Array (Int × Var)) (i:Nat) (p q:Int) (v:Var) : Expr :=
  let r := sexpr f poly i
  mkAppN (mkConst ``sumLemma) #[r, p, q, f v]

theorem cancel0Lemma {p q:Int} (h : p+q = 0) (v:Int) : p*v + q*v = 0 := by
  apply Eq.trans (sum0Lemma p q v)
  exact @Eq.substr Int (λx => x * v = 0) _ _ h (Int.zero_mul v)

example        : (64:Int) + -64 = 0   := @cancel0Lemma (64) (-64) (@rfl Int 0) 1
example        : (-64:Int) + 64 = 0   := @cancel0Lemma (-64) (64) (@rfl Int 0) 1
example (v:Int): -64 * v + 64 * v = 0 := @cancel0Lemma (-64) 64   (@rfl Int 0) v
example (v:Int): 64 * v + -64 * v = 0 := @cancel0Lemma (64) (-64) (@rfl Int 0) v

-- @mkCancel0Proof f q v@ produces a proof that
--  firstScalarProd f (-q,v) + firstScalarProd (q,v) = intZeroExpr
def mkCancel0Proof (f : Var → IntExpr) (q:Int) (v:Var) : Expr :=
  let rflExpr := mkAppN (mkConst ``rfl [levelOne]) #[intExpr, intZeroExpr]
  mkAppN (mkConst ``cancel0Lemma) #[ (-q : Int), q, rflExpr, f v]

theorem cancelLemma (r p q v:Int) (h : p+q = 0) : (r + p*v) + q*v = r := by
  apply Eq.trans (Int.add_assoc r _ _)
  exact Eq.trans (cancel0Lemma h v ▸ rfl) (Int.add_zero r)

-- @mkCancelProof f poly i q v@ with i > 0 produces a proof that
--  (expr f poly[0:i] + -q * v⟩) + scalarProd (q,v) = sexpr f poly[0:i]
def mkCancelProof (f : Var → IntExpr) (poly:Array (Int × Var)) (i:Nat) (q:Int) (v:Var) : Expr :=
  let r := sexpr f poly i
  let rflExpr := mkAppN (mkConst ``rfl [levelOne]) #[intExpr, intZeroExpr]
  mkAppN (mkConst ``cancelLemma) #[r, (-q : Int), q, f v, rflExpr]

def predExpr (s:State) : Pred → Expr
| Pred.IsEq0 v => mkIntEq0Expr (s.varExpr v)
| Pred.IsNe0 v => mkApp notExpr (mkIntEq0Expr (s.varExpr v))
| Pred.IsGe0 v => mkIntNonNegExpr (s.varExpr v)

-- | Add assertions to local context.
-- Return new local context along with array of free variables identifying assertions.
def addAssertions (s : State) (lctx:LocalContext) : MetaM (LocalContext × Array Expr) := do
  let mut lctx := lctx
  let mut fvars : Array Expr := #[]
  for a in s.assertions do
    let newVar ← mkFreshFVarId
    fvars := fvars.push (mkFVar newVar)
    match a.origin with
    | some prevVar =>
      lctx := lctx.erase prevVar
    | none =>
      pure ()
    lctx := lctx.mkLocalDecl newVar a.name (s.predExpr a.prop)
  pure (lctx, fvars)

theorem buildProofLemma {x c a:Int} (h:x + c = a) (y:Int)
  : (x + y) + c = a + y := by
  simp [h.symm, Int.add_assoc, Int.add_comm y c]

-- buildProof f x c a h rest where h is a proof of "x + c = a" returns
-- a proof "buildExpr f x rest + c = buildExpr f a rest"
def buildProof (f:Var → IntExpr) (x c a:IntExpr) (h:Expr) (rest:Subarray (Int × Var)) : Expr := Id.run do
  let mut x := x
  let mut a := a
  let mut h := h
  for p in rest do
    let y := scalarProd f p
    h := mkAppN (mkConst ``buildProofLemma) #[x, c, a, h, y]
    x := x + y
    a := a + y
  pure h

-- | @addProof f p m v@ returns proof showing that
-- @p.expr + firstScalarProd f (m, v) = (p.add m v).expr@.
def polyAddProof (s:State) : ∀(poly:Poly) (q:Int), q ≠ 0 → Var → Expr
| ⟨poly⟩, q, g, v =>
  let c := scalarProd s.varExpr (q,v)
  let rec loop : ∀(i : Nat), Expr
      | 0 =>
        if poly.size = 0 then
          -- Prove (0:Int) + firstScalarProd f (q,v) = firstScalarProd f (q,v)
          mkApp (mkConst `Int.zero_add) c
        else Id.run do
          let x := scalarProd s.varExpr poly[0]
          let a := c + x
          let h := mkAppN (mkConst `Int.add_comm) #[x, c]
          buildProof s.varExpr x c a h poly[1:]
      | Nat.succ i =>
        let (p,u) := poly[i]
        if u < v then
          let x := sexpr s.varExpr poly (i+1)
          let a := x + c
          let h := mkAppN (mkConst ``Eq.refl [levelOne]) #[intExpr, a]
          buildProof s.varExpr x c a h poly[i+1:]
        else if v < u then
          loop i
        else -- v = u
          if p+q = 0 then
            if i = 0 then
              let x := scalarProd s.varExpr poly[0]
              let a := (0 : Int)
              let h := mkCancel0Proof s.varExpr q v
              buildProof s.varExpr x c a h poly[i+1:]
            else
              let a := sexpr s.varExpr poly i
              let x := a + scalarProd s.varExpr poly[i]
              let h := mkCancelProof s.varExpr poly i q v
              buildProof s.varExpr x c a h poly[i+1:]
          else
            if i = 0 then
              let x := scalarProd s.varExpr poly[0]
              let a := scalarProd s.varExpr (p+q, v)
              let h := mkSum0Proof s.varExpr p q v
              buildProof s.varExpr x c a h poly[i+1:]
            else
              let x0 := sexpr s.varExpr poly i
              let x := x0 + scalarProd s.varExpr poly[i]
              let a := x0 + scalarProd s.varExpr (p+q, v)
              let h := mkSumProof s.varExpr poly i p q v
              buildProof s.varExpr x c a h poly[i+1:]
  loop poly.size

end State

abbrev ArithM  := StateRefT State MetaM

@[inline] def ArithM.run (m : ArithM α) (s : State := {}) : MetaM (α × State) :=
  StateRefT'.run m s

-- | Return a theory variable associated with the given uninterpreted Lean expression.
private def getDeclVar (d:Decl) : ArithM Var := do
  let s ← get
  match s.exprMap.find? d with
  | none => pure ()
  | some v => return v
  let newVar := ⟨OfNat.ofNat s.varExprs.size⟩
  let newExprMap  := s.exprMap.insert d newVar
  let newVarExprs := s.varExprs.push d
  if (OfNat.ofNat s.varExprs.size : UInt32) = 0 then
    throwError m!"Only 2^32 arithmetic variables allowed."
  set { s with exprMap := newExprMap, varExprs := newVarExprs }
  return newVar

-- | Return a theory variable associated with the given uninterpreted Lean expression.
def getUninterpVar (e:Expr) : ArithM Var := getDeclVar (Decl.uninterp e)

-- | Return a theory variable associated with the given uninterpreted Lean expression.
def getPolyVar (p:Poly) : ArithM Var := getDeclVar (Decl.poly p)

-- | Assert a predicate holds using the given expression to refer to the
-- proof.
def assertPred (origin:Option FVarId) (userName:Name) (proof:Expr) (prop:Pred) : ArithM Unit := do
  let a := { origin := origin, name := userName, proof := proof, prop := prop }
  modifyGet fun s => ((), { s with assertions := s.assertions.push a })

--
def varExpr (v:Var) : ArithM IntExpr := do
  let s ← get
  pure $ s.varExpr v

def polyExpr (poly:Poly) : ArithM IntExpr := do
  let s ← get
  pure $ s.polyExpr poly

-- @polyAddProof s poly q _ v@ returns a proof that
--   @poly.expr varExpr s + firstScalarProd s.varExpr (m, v) = (poly.add m v).expr s.varExpr@.
def polyAddProof (poly:Poly) (q:Int) (q_ne:q ≠ 0) (v:Var) : ArithM Expr := do
  let s ← get
  pure $ s.polyAddProof poly q q_ne v

end ArithSolver