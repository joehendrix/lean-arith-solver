import ArithSolver.Basic
import ArithSolver.Notation
import Lean

open Lean
open Lean.Meta
open Lean.Elab.Tactic

namespace ArithSolver

private def natExpr := mkConst ``Nat
private def intExpr := mkConst ``Int
private def ofNatExpr : Expr := mkConst ``Int.ofNat
private def intNonNegMkExpr : Expr := mkConst ``Int.NonNeg.mk

/-

theorem nat_lt_by_contra {m n : Nat} (p : ¬ (n ≤ m)) : m < n :=
   Nat.gt_of_not_le p

theorem nat_gt_by_contra {m n : Nat} (p : ¬ (m ≤ n)) : m > n :=
  nat_lt_by_contra p

theorem nat_eq_by_contra {m n : Nat} (p : ¬ (m < n ∨ n < m)) : m = n :=
  match Nat.lt_or_ge n m with
  | Or.inl q => False.elim (p (Or.inr q))
  | Or.inr q =>
    match Nat.eq_or_lt_of_le q with
    | Or.inl q => q
    | Or.inr q => False.elim (p (Or.inl q))

theorem int_lt_by_contra {x y : Int} (p : ¬ (Int.NonNeg (x - y))) : x < y := by
  admit

theorem int_gt_by_contra {x y : Int} (p : ¬ (Int.NonNeg (y - x))) : x > y :=
  int_lt_by_contra p

theorem nat_le {m n:Nat} : m ≤ n → Int.NonNeg (Int.ofNat n + -Int.ofNat m) := by
  admit

theorem nat_lt {m n:Nat} : m < n → Int.NonNeg (Int.ofNat n + -Int.ofNat m - 1) := by
  intro p
  have q := nat_le p
  simp [Int.neg_ofNat] at q

  admit


theorem nat_gt : m > n → Int.NonNeg ()
-/

-- | An assumption in the goal
structure NegatedGoal where
  -- The proposition we can assume
  assumptionProp : Expr
  -- An expression referencing the input proof.
  assumptionProof : FVarId

-- | This intrudces a lambda and replaces the free var fvar having type atp in proof with a bound variable
def bindAssumption (fvar : FVarId) (prop proof : Expr) : Expr :=
  mkLambda `negGoal BinderInfo.default prop (proof.abstract #[mkFVar fvar])

-- | An assumption in the goal
structure Assumption where
  -- The property we can assume
  prop : Expr
  -- An expression referencing the input proof.
  proof : Expr

-- | Given a proposition equivalent to λ(x:P) => False, this returns type p
def parseNegatedGoal (tactic:Name) (goalId:MVarId) (ptp:Expr) : MetaM Expr := do
  match ptp with
  | Expr.forallE an atp (Expr.const ``False [] fd) ad => do
    pure atp
  | Expr.app (Expr.const ``Not [] _) atp _ => do
    pure atp
  | _ =>
    throwTacticEx tactic goalId m!"Expected negation input goal to be False instance of {indentExpr ptp}"

structure Goal where
  -- Callback that adds assumptions to local context and returns
  -- proof obligations.
  onAddAssumptions : MetaM (List MVarId)
  -- Callback that given a proof of false produces a proof of the goal.
  onVerify : Expr → MetaM Unit

-- | This represents a functions of the form ∀(args), P → Q
structure Transformer where
  -- Meta variables created for arguments
  -- These should all be resolved by matching against P or Q.
  arguments : Array Expr
  -- Binders for arguments (binders.size = arguments.size)
  binders : Array BinderInfo
  -- The assumption proposition P
  assumptionType : Expr
  -- | The result proposition Q
  resultType : Expr

-- | This constructs a transformer from a term denoing an inference rule.
def mkTransformer (proof:Expr) (maxVars?:Option Nat): MetaM Transformer := do
  -- Get variables and type of proof
  let (vars, binders, resultType) ← forallMetaTelescopeReducing (← inferType proof) maxVars?
  if vars.size = 0 then
    throwError m!"Expected predicate with at least one argument {indentExpr proof}."
  let avar := vars.back.mvarId!
  let some avarDecl ← (← getMCtx).findDecl? avar
    | throwError "unknown goal {avar.name}"
  pure {
      arguments := vars.pop,
      binders := binders.pop,
      assumptionType := avarDecl.type,
      resultType := resultType
    }

def resolveTransformerArgs (proofExpr:Expr) (t:Transformer) : MetaM Bool := do
  for v in t.arguments, b in t.binders do
    if ← isExprMVarAssigned v.mvarId! then
      continue
    let tp := ← inferType v
    match b with
    | BinderInfo.instImplicit =>
      -- Synthesize class instance
      let classType ← inferType v
      let classVal  ← synthInstance classType
      unless (← isDefEq v classVal) do
        return false
    | _ =>
      throwError m!"Unresolved transformer argument in {indentExpr proofExpr}"
  return true

-- | Match `(Int.NonNeg e) and return e
def matchIntNonNeg (e:Expr) : MetaM (Option Expr) := do
  let mvar ← mkFreshExprMVar intExpr MetavarKind.natural `n
  pure $ if ← isDefEq (mkApp intNonNegExpr mvar) e then some mvar else none

def matchIntEq0 (e:Expr) : MetaM (Option Expr) := do
  let mvar ← mkFreshExprMVar intExpr MetavarKind.natural `n
  pure $ if ← isDefEq (mkIntEq0Expr mvar) e then some mvar else none

def matchNotIntEq0 (e:Expr) : MetaM (Option Expr) := do
  let mvar ← mkFreshExprMVar intExpr MetavarKind.natural `n
  if ← isDefEq (mkApp (mkConst ``Not) (mkIntEq0Expr mvar)) e then
    pure $ some mvar
  else
    none

def propExpr : Expr := mkSort levelZero

def matchNot (e:Expr) : MetaM (Option Expr) := do
  let mvar ← mkFreshExprMVar propExpr MetavarKind.natural `a
  let p := mkApp (mkConst ``Not) mvar
  pure $ if ← isDefEq p e then mvar else none

theorem nat_eq_prop {x y : Nat} (p : x = y)
  : OfNat.ofNat x - OfNat.ofNat y = 0 := sorry
theorem nat_lt_prop {x y : Nat} (p : x < y)
  : Int.NonNeg (OfNat.ofNat y - OfNat.ofNat x - 1) := sorry
theorem nat_le_prop {x y : Nat} (p : x ≤ y)
  : Int.NonNeg (OfNat.ofNat y - OfNat.ofNat x) := sorry
theorem nat_gt_prop {x y : Nat} (p : x > y)
  : Int.NonNeg (OfNat.ofNat x - OfNat.ofNat y - 1) := sorry
theorem nat_ge_prop {x y : Nat} (p : x ≥ y)
  : Int.NonNeg (OfNat.ofNat x - OfNat.ofNat y) := sorry

theorem nat_not_eq_prop (x y : Nat) (p : ¬(x = y))
  : ¬(Int.ofNat x - Int.ofNat y = 0) := sorry
theorem nat_not_lt_prop {x y : Nat} (p : ¬(x < y))
  : Int.NonNeg (OfNat.ofNat x - OfNat.ofNat y) := sorry
theorem nat_not_le_prop {x y : Nat} (p : ¬(x ≤ y))
  : Int.NonNeg (OfNat.ofNat x - OfNat.ofNat y - 1) := sorry
theorem nat_not_gt_prop {x y : Nat} (p : ¬(x > y))
  : Int.NonNeg (OfNat.ofNat y - OfNat.ofNat x) := sorry
theorem nat_not_ge_prop {x y : Nat} (p : ¬(x ≥ y))
  : Int.NonNeg (OfNat.ofNat y - OfNat.ofNat x - 1) := sorry

theorem int_eq_prop (x y : Int) (p : x = y)
  : x - y = 0 := sorry
theorem int_lt_prop {x y : Int} (p : x < y)
  : Int.NonNeg (y - x - 1) := sorry
theorem int_le_prop {x y : Int} (p : x ≤ y)
  : Int.NonNeg (y - x) := sorry
theorem int_gt_prop {x y : Int} (p : x > y)
  : Int.NonNeg (x - y - 1) := sorry
theorem int_ge_prop {x y : Int} (p : x ≥ y)
  : Int.NonNeg (x - y) := sorry

theorem int_not_eq_prop {x y : Int} (p : ¬(x = y))
  : ¬(x - y = 0) := sorry
theorem int_not_lt_prop {x y : Int} (p : ¬(x < y))
  : Int.NonNeg (x - y) := sorry
theorem int_not_le_prop {x y : Int} (p : ¬(x ≤ y))
  : Int.NonNeg (x - y - 1) := sorry
theorem int_not_gt_prop {x y : Int} (p : ¬(x > y))
  : Int.NonNeg (y - x) := sorry
theorem int_not_ge_prop {x y : Int} (p : ¬(x ≥ y))
  : Int.NonNeg (y - x - 1) := sorry

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

theorem neg_ne_zero {x:Int} : x ≠ 0 → -x ≠ 0 := sorry
theorem mul_ne_zero {x y:Int} : x ≠ 0 → y ≠ 0 → x * y ≠ 0 := sorry

theorem add_poly_lemma {m x y a b c:Int}  (g : a + m*x = b) (h : b + m*y = c) : a + m*(x+y) = c := sorry
theorem sub_poly_lemma {m x y a b c:Int}  (g : a + m*x = b) (h : b + -m*y = c) : a + m*(x-y) = c := sorry
theorem neg_poly_lemma {m x a b:Int}  (g : a + (-m)*x = b) : a + m*(-x) = b := sorry

-- | @appendAddExpr poly m e@ returns poly equivalent to `poly + m*e` along with proof that that
-- poly.expr + m*e = ret.expr
partial def appendAddExprFromInt (m:Int) (m_ne:m ≠ 0) (e:Expr) (poly:Poly)
   : ArithM (Poly × Expr) := do

  match ← matchIntLit e with
  | none => pure ()
  | some x =>
    let s ← get
    let r ←
      if x_ne : x = 0 then
        let n := Poly.expr s.varExpr poly
        let pr := mkAppN (mkConst ``rfl [levelOne]) #[intExpr, n]
        pure (poly, pr)
      else
        let y := m * x
        -- p + m * x * 1 = return
        let pr := Poly.addProof (s.varExpr) poly y (mul_ne_zero m_ne x_ne) Var.constOne
        pure (poly.add y Var.constOne, pr)
    return r

  -- Match add
  match ← matchBinOp intAddExpr intExpr e with
  | none => pure ()
  | some (x, y) => do
    let s ← get
    let mexpr := mkIntLit m
    let aexpr := Poly.expr s.varExpr poly
    let (poly, x_pr) ← appendAddExprFromInt m m_ne x poly
    let bexpr := Poly.expr s.varExpr poly
    let (poly, y_pr) ← appendAddExprFromInt m m_ne y poly
    let cexpr := Poly.expr s.varExpr poly
    let pr := mkAppN (mkConst ``add_poly_lemma) #[mexpr, x, y, aexpr, bexpr, cexpr, x_pr, y_pr]
    return (poly, pr)

  -- Match sub
--  let subExpr := mkAppN (mkConst ``Sub.sub [levelZero]) #[intExpr, mkConst ``Int.instSubInt]
--  let subExpr := mkConst ``Int.sub
  match ← matchBinOp intSubExpr intExpr e with
  | none =>
    pure ()
  | some (x, y) => do
    let s ← get
    let mexpr := mkIntLit m
    let aexpr := Poly.expr s.varExpr poly
    let (poly, x_pr) ← appendAddExprFromInt m m_ne x poly
    let bexpr := Poly.expr s.varExpr poly
    let (poly, y_pr) ← appendAddExprFromInt (- m) (neg_ne_zero m_ne) y poly
    let cexpr := Poly.expr s.varExpr poly
    let pr := mkAppN (mkConst ``sub_poly_lemma) #[mexpr, x, y, aexpr, bexpr, cexpr, x_pr, y_pr]
    return (poly, pr)

  -- Match negation
  let negExpr := mkAppN (mkConst ``Neg.neg [levelZero]) #[intExpr, mkConst ``Int.instNegInt]
  match ← matchUnaryOp negExpr intExpr e with
  | none => pure ()
  | some x => do
    let s ← get
    let mexpr := mkIntLit m
    let aexpr := Poly.expr s.varExpr poly
    let (poly, x_pr) ← appendAddExprFromInt (-m) (neg_ne_zero m_ne) x poly
    let bexpr := Poly.expr s.varExpr poly
    let pr := mkAppN (mkConst ``neg_poly_lemma) #[mexpr, x, aexpr, bexpr, x_pr]
    return (poly, pr)

  -- Match scalar multiplication
  /-
  match ← matchBinOp intMulExpr intExpr e with
  | none => pure ()
  | some (x, y) => do
    match ← matchIntLit x with
    | none =>
      pure ()
    | some xn =>
      let r ←
        if xn_ne:xn = 0 then
          pure (poly, sorry)
        else
          let (p, y_eq) ← appendAddExprFromInt (m * xn) (mul_ne_zero m_ne xn_ne) y poly
          pure (poly, sorry)
      return r
    match ← matchIntLit y with
    | none =>
      pure ()
    | some n =>
      let r ←
        if n_ne:n = 0 then
          pure (poly, sorry)
        else
          let (p, x_eq) ← appendAddExprFromInt (m * n) (mul_ne_zero m_ne n_ne) x poly
          pure (poly, sorry)
      return r
    pure ()
-/

  let v ← getUninterpVar e
  let pr ← polyAddProof poly m m_ne v
  pure (poly.add m v, pr)

theorem purifyIntLemmaPoly {x y:Int} (p:0 + 1 * x = y) : x = y := sorry

theorem purifyIntLemmaVar {x y:Int} (p:0 + 1 * x = 1 * y) : x = y :=
  Eq.trans (purifyIntLemmaPoly p) (Int.one_mul y)

-- | This traverses an expression (which should have type int) to normalize
-- the expression.  It produces a variable along with a proof that
-- e = v.expr
def purifyIntExpr (e:Expr) : ArithM (Var × Expr) := do
  have g : 1 ≠ 0 := by
    apply Nat.noConfusion
  have one_ne : (1:Int) ≠ 0 := λx => Int.noConfusion x g
  let (p,pr) ← appendAddExprFromInt 1 one_ne e Poly.zero
  -- pr  has type" 0 + 1 * e = p.expr"
  match p with
  | ⟨#[(1, v)]⟩ => do
    let s ← get
    -- Make pr have type e = v
    let pr := mkAppN (mkConst ``purifyIntLemmaVar) #[e, s.varExpr v, pr]
    pure (v, pr)
  | otherwise => do
    let v ← mkDeclVar (Decl.poly p)
    -- Make pr have type e = v
    let s ← get
    let pr := mkAppN (mkConst ``purifyIntLemmaPoly) #[e, Poly.expr s.varExpr p, pr]
    pure (v, pr)

theorem substIntNonNeg {x y:Int} (p:Int.NonNeg x) (eq:x = y) : Int.NonNeg y := eq ▸ p

theorem intNonNeg_lemma {x y :Int} : x = y → Int.NonNeg x → Int.NonNeg y := sorry
theorem intEq0_lemma {x y :Int} : x = y → x = 0 → y = 0 := sorry
theorem intNe0_lemma {x y :Int} : x = y → ¬(x = 0) → ¬(y = 0) := sorry


-- | Analyze a proof and a proposition to produce a Linear arith predicate along with a proof
-- that of the predicate.
partial def extractPropPred (proof:Expr) (prop:Expr) : ArithM (Option (Expr × Pred)) := do
  -- Check if prop matches (Int.NonNeg e)
  match ← matchIntNonNeg prop with
  | none => pure ()
  | some e =>
    let (v, pr) ← purifyIntExpr e
    let s ← get
    IO.println s!"Asserting non neg:\n  proof = {←instantiateMVars proof}"
    let proof2 := mkAppN (mkConst ``intNonNeg_lemma) #[e, s.varExpr v, pr, proof]
    return (some (proof2, Pred.IsGe0 v))
  -- Check if prop match (e = Int.ofNat 0)
  match ← matchIntEq0 prop with
  | none => pure ()
  | some e =>
    let (v, pr) ← purifyIntExpr e
    let s ← get
    let proof := mkAppN (mkConst ``intEq0_lemma) #[e, s.varExpr v, pr, proof]
    return (some (proof, Pred.IsEq0 v))
  match ← matchNotIntEq0 prop with
  | none => pure ()
  | some e =>
    let (v, pr) ← purifyIntExpr e
    let s ← get
    let proof := mkAppN (mkConst ``intNe0_lemma) #[e, s.varExpr v, pr, proof]
    return (some (proof, Pred.IsNe0 v))
  let mkTrans (nm:Name) (m:optParam (Option Nat) none) : Expr × Option Nat := (mkConst nm, m)
  -- Create list of transformers to apply
  let transformers : Array (Expr × Option Nat) := #[
          mkTrans ``nat_eq_prop,
          mkTrans ``nat_lt_prop,
          mkTrans ``nat_le_prop,
          mkTrans ``nat_gt_prop,
          mkTrans ``nat_ge_prop,
          mkTrans ``nat_not_eq_prop (some 3),
          mkTrans ``nat_not_lt_prop,
          mkTrans ``nat_not_le_prop,
          mkTrans ``nat_not_gt_prop,
          mkTrans ``nat_not_ge_prop,
          mkTrans ``int_eq_prop,
          mkTrans ``int_lt_prop,
          mkTrans ``int_le_prop,
          mkTrans ``int_gt_prop,
          mkTrans ``int_ge_prop,
          mkTrans ``int_not_eq_prop (some 3),
          mkTrans ``int_not_lt_prop,
          mkTrans ``int_not_le_prop,
          mkTrans ``int_not_gt_prop,
          mkTrans ``int_not_ge_prop
        ]
  let mut found : Option (Expr × Expr) := none
  -- Iterate through list looking for first match
  for (rule,max) in transformers do
    -- Get variables and type of proof
    let t ← mkTransformer rule max
    unless ← isDefEq t.assumptionType prop do
      continue
    unless ← resolveTransformerArgs rule t do
      continue
    IO.println s!"Propagating:\n  source = {←instantiateMVars proof}"
    found := (mkApp (mkAppN rule t.arguments) proof, t.resultType)
    break
  match found with
  | none =>
    IO.println s!"Drop assertion {← instantiateMVars prop}"
    pure none
  | some (proof, prop) => do
    IO.println s!"  result = {←instantiateMVars proof}"
    extractPropPred proof prop

-- | See if we can add the local declaration to the arithmetic unit.
-- proof is a term of type prop.
def processAssumptionProp (origin : Assertion.Origin) (proof:Expr) (prop:Expr) : ArithM Unit := do
  match ← extractPropPred proof prop with
  | none => do
    IO.println s!"Drop assertion {← instantiateMVars prop}"
  | some (proof, pred) => do
    assertPred origin proof pred

def processDecls (lctx:LocalContext) : ArithM Unit := do
  let mut seenFirst := false
  for md in lctx.decls do
    -- Skip first declaration (as it corresponds to initial goal for
    -- recursive purposes)
    unless seenFirst do
      seenFirst := true
      continue
    -- Skip if declaration has been deleted.
    let some d ← pure md
         | continue
    IO.println s!"Decl {d.type}"
    -- TODO: Figure out how to support let declarations
    if d.isLet then
      continue
    -- If we have a natural number, then declare it.
    if ← isDefEq d.type natExpr then
      let e := mkApp ofNatExpr (mkFVar d.fvarId)
      let v ← getUninterpVar e
      -- Assert v is non negative
      assertPred Assertion.Origin.uninterpNat (mkApp intNonNegMkExpr e) (Pred.IsGe0 v)
      continue
    -- If we have a natural number, then declare it.
    if ← isDefEq d.type intExpr then
      let v ← getUninterpVar (mkFVar d.fvarId)
      continue
    -- If this is a proposition then try assuming it.
    if ← isDefEq (← inferType d.type) propExpr then do
      let fvar := ← mkFreshFVarId
      processAssumptionProp (Assertion.Origin.localContext d.fvarId d.userName fvar) (mkFVar fvar) d.type

-- | Add assertions to local context.
def addAssertions (lctx:LocalContext) (s : State) : LocalContext := Id.run do
  let mut lctx := lctx
  for a in s.assertions do
    match a.origin with
    | Assertion.Origin.localContext prevVar userName newVar =>
      lctx := lctx.erase prevVar
      lctx := lctx.mkLocalDecl newVar userName (s.predExpr a.prop)
--      lctx := lctx.mkLetDecl newVar userName (s.predExpr a.prop) a.proof
    | Assertion.Origin.negGoal fvar =>
      lctx := lctx.mkLocalDecl fvar `negGoal (s.predExpr a.prop)
--      lctx := lctx.mkLetDecl fvar `negGoal2 (s.predExpr a.prop) a.proof
    | Assertion.Origin.uninterpNat =>
      pure ()
  pure lctx

-- Negating goal

theorem decidable_by_contra {P:Prop} [h:Decidable P] (q : ∀(ng:¬ P), False) : P :=
  match h with
  | isFalse h => False.elim (q h)
  | isTrue h => h

def falseExpr : Expr := mkConst ``False

def negateArithGoal (tactic:Name) (goalId:MVarId) : ArithM Goal := do
  let md ← getMVarDecl goalId
  processDecls md.lctx
  if ← isDefEq md.type (mkConst ``False) then
    let s ← get
    IO.println s! "Extracted {s.assertions.size} assertions."
    return {
      onAddAssumptions := do
        let lctx := addAssertions (← getLCtx) s
        let tag   ← getMVarTag goalId
        withReader (fun ctx => { ctx with lctx := lctx }) do
          let proof ← mkFreshExprSyntheticOpaqueMVar falseExpr tag
          assignExprMVar goalId proof
          pure [proof.mvarId!]
      onVerify := assignExprMVar goalId
    }
  match ← matchNot md.type with
  | none => pure ()
  | some atp => do
    let fvar := ← mkFreshFVarId
    processAssumptionProp (Assertion.Origin.negGoal fvar) (mkFVar fvar) atp
    let s ← get
    IO.println s! "Extracted {s.assertions.size} assertions."
    -- Create verification
    return {
        onAddAssumptions := do
          let lctx := addAssertions (← getLCtx) s
          let tag   ← getMVarTag goalId
          withReader (fun ctx => { ctx with lctx := lctx }) do
            let proof ← mkFreshExprSyntheticOpaqueMVar falseExpr tag
            assignExprMVar goalId <| bindAssumption fvar atp proof
            pure [proof.mvarId!]
        onVerify := λproof => do
          -- Generate proof to pass into proof expr
          assignExprMVar goalId <| bindAssumption fvar atp proof
        }

  let decideByContraExpr := mkConst ``decidable_by_contra
  let target := md.type
  -- Get variables and type of proof
  let t ← mkTransformer decideByContraExpr none
  unless ← isDefEq t.resultType target do
    throwTacticEx tactic goalId m!"Goal must be a proposition."
  unless ← resolveTransformerArgs decideByContraExpr t do
    throwTacticEx tactic goalId m!"Unexpected decidable "
  let decideByContraExpr := mkAppN decideByContraExpr t.arguments
  -- Get negated goal from assumption type
  let prop ← parseNegatedGoal tactic goalId t.assumptionType
  -- Create free variable for representing assumption
  let fvar := ← mkFreshFVarId
  -- Pvar is a metavariable of type "prop -> False"
  let assumptionProof ←
        match ← extractPropPred (mkBVar 0) prop with
        | none => do
          throwError "Could not extract prop"
        | some (proof, pred) => do
          assertPred (Assertion.Origin.negGoal fvar) proof pred
          pure proof
  let s ← get

  -- Create verification
  pure $ {
      onAddAssumptions := do
        let lctx := addAssertions (← getLCtx) s
        let falseExpr := mkConst ``False
        withReader (fun ctx => { ctx with lctx := lctx }) do
          IO.println s!"tryNegateGoal onAddAssumptions"
          let tag   ← getMVarTag goalId
          let goalProof ← mkFreshExprSyntheticOpaqueMVar falseExpr tag
          -- Make lambda that takes proof with the inferred type and produces false.
          let goalLambda ← mkLambdaFVars #[mkFVar fvar] goalProof
          -- Instantiate lambda with the proof we have
          let goalRes := mkApp goalLambda assumptionProof
          let contraArg := mkLambda Name.anonymous BinderInfo.default prop goalRes
          assignExprMVar goalId $ mkApp decideByContraExpr contraArg
          pure [goalProof.mvarId!]
      onVerify := λgoalProof => do
        -- Generate proof to pass into proof expr
        let goalRes := goalProof.replaceFVar (mkFVar fvar) assumptionProof
        let contraArg := mkLambda Name.anonymous BinderInfo.default prop goalRes
        assignExprMVar goalId $ mkApp decideByContraExpr contraArg
      }

syntax (name := zify) "zify" : tactic

 --OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)

@[tactic zify] def evalZify : Tactic := fun stx => do
  liftMetaTactic fun mvarId => do
    checkNotAssigned mvarId `zify
    let (goal, _) ← (negateArithGoal `zify mvarId).run
    let r@([goalId]) ← goal.onAddAssumptions
      | throwError "Expected more goals"
    pure r

end ArithSolver

-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a))
def test_false_goal (a b : Nat) (p:False) : False := by
  zify
  exact p

-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a))
def test_nonneg_assumption (x y : Int) (p : Int.NonNeg (x + y)) : False := by
  zify

-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a))
def test_eq0_assumption (x : Int) (p : x = 0): False := by
  zify


theorem test_le_proof (y:Nat) : ¬Int.NonNeg (-1 + -1 * Int.ofNat y) := sorry


-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a))
theorem test_le_assumption2 (x y:Nat) : Int.ofNat x ≤ Int.ofNat x + Int.ofNat y := by
  zify
  let r := test_le_proof y negGoal
  exact r


/-
-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a))
def test_eq_assumption (x:Int) : x = y := by
  zify
  admit
-/
-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a))
--def test_eq_assumption (x y : Int) (p : y + x = y) (q:1 + 2 = 3): False := by
--  zify

/-
-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a))
def test_not_goal (a b : Nat) : ¬(a > b) := by
  zify

-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a))
def test_nat_gt_goal (a b : Nat) : (a > b) := by
  zify

-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a))
def test_nat_lt_goal (a b : Nat) : (a < b) := by
  zify

-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a))
def test_nat_eq_goal (a b : Nat) : (a = b) := by
  zify
-/

--#print test_nat_gt_goal.proof_1