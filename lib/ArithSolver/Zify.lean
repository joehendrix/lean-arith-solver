import ArithSolver.Basic
import ArithSolver.Notation
import Lean

open Lean
open Lean.Meta
open Lean.Elab.Tactic

namespace ArithSolver

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
  -- Metavariable to represent proof of P
  assumptionVar : Expr
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
  let avar := vars.back
  let some avarDecl ← (← getMCtx).findDecl? avar.mvarId!
    | throwError "unknown goal {avar.mvarId!.name}"
  pure {
      arguments := vars.pop,
      binders := binders.pop,
      assumptionVar := avar,
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

private def natExpr := mkConst ``Nat
private def intExpr := mkConst ``Int
private def ofNatExpr : Expr := mkConst ``Int.ofNat
private def intNonNegMkExpr : Expr := mkConst ``Int.NonNeg.mk

-- | Match `(Int.NonNeg e) and return e
def matchIntNonNeg (e:Expr) : MetaM (Option Expr) := do
  let mvar ← mkFreshExprMVar intExpr MetavarKind.natural `n
  pure $ if ← isDefEq (mkIntNonNegExpr mvar) e then mvar else none

def matchIntEq0 (e:Expr) : MetaM (Option Expr) := do
  let mvar ← mkFreshExprMVar intExpr MetavarKind.natural `n
  pure $ if ← isDefEq (mkIntEq0Expr mvar) e then mvar else none

def matchNotIntEq0 (e:Expr) : MetaM (Option Expr) := do
  let mvar ← mkFreshExprMVar intExpr MetavarKind.natural `n
  pure $ if ← isDefEq (mkApp (mkConst ``Not) (mkIntEq0Expr mvar)) e then mvar else none


def propExpr : Expr := mkSort levelZero

def matchNot (e:Expr) : MetaM (Option Expr) := do
  let mvar ← mkFreshExprMVar propExpr MetavarKind.natural `a
  let p := mkApp (mkConst ``Not) mvar
  pure $ if ← isDefEq p e then mvar else none

theorem nat_eq_prop {x y : Nat} (p : x = y) : OfNat.ofNat x + -(OfNat.ofNat y) = 0 := sorry
theorem nat_lt_prop {x y : Nat} (p : x < y)
  : Int.NonNeg (OfNat.ofNat y + -(OfNat.ofNat x) + -1) := sorry
theorem nat_le_prop {x y : Nat} (p : x ≤ y)
  : Int.NonNeg (OfNat.ofNat y + -(OfNat.ofNat x)) := sorry
theorem nat_gt_prop {x y : Nat} (p : x > y)
  : Int.NonNeg (OfNat.ofNat x + -(OfNat.ofNat y) + -1) := sorry
theorem nat_ge_prop {x y : Nat} (p : x ≥ y)
  : Int.NonNeg (OfNat.ofNat x + -(OfNat.ofNat y)) := sorry

theorem nat_not_eq_prop (x y : Nat) (p : ¬(x = y)) : ¬(Int.ofNat x + -(Int.ofNat y) = 0) := sorry

theorem nat_not_lt_prop {x y : Nat} (p : ¬(x < y))
  : Int.NonNeg (OfNat.ofNat x + -(OfNat.ofNat y)) := sorry
theorem nat_not_le_prop {x y : Nat} (p : ¬(x ≤ y))
  : Int.NonNeg (OfNat.ofNat x + -(OfNat.ofNat y) + -1) := sorry
theorem nat_not_gt_prop {x y : Nat} (p : ¬(x > y))
  : Int.NonNeg (OfNat.ofNat y + -(OfNat.ofNat x)) := sorry
theorem nat_not_ge_prop {x y : Nat} (p : ¬(x ≥ y))
  : Int.NonNeg (OfNat.ofNat y + -(OfNat.ofNat x) + -1) := sorry

theorem int_eq_prop (x y : Int) (p : x = y) : x + -y = 0 := sorry
theorem int_lt_prop {x y : Int} (p : x < y)
  : Int.NonNeg (y + -x + -1) := sorry
theorem int_le_prop {x y : Int} (p : x ≤ y)
  : Int.NonNeg (y + -x) := sorry
theorem int_gt_prop {x y : Int} (p : x > y)
  : Int.NonNeg (x + -y + -1) := sorry
theorem int_ge_prop {x y : Int} (p : x ≥ y)
  : Int.NonNeg (x + -y) := sorry

theorem int_not_eq_prop {x y : Int} (p : ¬(x = y)) : ¬(x + -y = 0) := sorry
theorem int_not_lt_prop {x y : Int} (p : ¬(x < y))
  : Int.NonNeg (x + -y) := sorry
theorem int_not_le_prop {x y : Int} (p : ¬(x ≤ y))
  : Int.NonNeg (x + -y + -1) := sorry
theorem int_not_gt_prop {x y : Int} (p : ¬(x > y))
  : Int.NonNeg (y + -x) := sorry
theorem int_not_ge_prop {x y : Int} (p : ¬(x ≥ y))
  : Int.NonNeg (y + -x + -1) := sorry


-- | See if we can add the local declaration to the arithmetic unit.
partial def processAssumptionProp (origin : Origin) (proof:Expr) (prop:Expr) : ArithM Unit := do
  -- Check if prop matches (Int.NonNeg e)
  match ← matchIntNonNeg prop with
  | none => pure ()
  | some e => do
    let v ← getUninterpVar e
    assertPred origin proof (Pred.IsGe0 v)
    return ()
  -- Check if prop match (e = Int.ofNat 0)
  match ← matchIntEq0 prop with
  | none => pure ()
  | some e => do
    let v ← getUninterpVar e
    assertPred origin proof (Pred.IsEq0 v)
    return ()
  match ← matchNotIntEq0 prop with
  | none => pure ()
  | some e => do
    let v ← getUninterpVar e
    assertPred origin proof (Pred.IsNe0 v)
    return ()

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
          mkTrans ``int_not_eq_prop,
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
    found := (mkApp (mkAppN rule t.arguments) proof, t.resultType)
    break
  match found with
  | none =>
    IO.println s!"Drop assertion {← instantiateMVars prop}"
    pure ()
  | some (proof, prop) =>
    processAssumptionProp origin proof prop

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
    -- TODO: Figure out how to support let declarations
    if d.isLet then
      continue
    -- If we have a natural number, then declare it.
    if ← isDefEq d.type natExpr then
      let e := mkApp ofNatExpr (mkFVar d.fvarId)
      let v ← getUninterpVar e
      -- Assert v is non negative
      assertPred Origin.uninterpNat (mkApp intNonNegMkExpr e) (Pred.IsGe0 v)
      continue
    -- If we have a natural number, then declare it.
    if ← isDefEq d.type intExpr then
      let v ← getUninterpVar (mkFVar d.fvarId)
      continue
    -- If this is a proposition then try assuming it.
    if ← isDefEq (← inferType d.type) propExpr then do
      let fvar := ← mkFreshFVarId
      processAssumptionProp (Origin.localContext d.fvarId d.userName fvar) (mkFVar fvar) d.type

def addAssertions (lctx:LocalContext) (s : State) : MetaM LocalContext := do
  let mut lctx := lctx
  for a in s.assertions do
    match a.origin with
    | Origin.localContext prevVar userName newVar =>
      lctx := lctx.erase prevVar
      lctx := lctx.mkLocalDecl newVar userName (s.predExpr a.prop)
    | Origin.negGoal fvar =>
      lctx := lctx.mkLocalDecl fvar `negGoal (s.predExpr a.prop)
    | Origin.uninterpNat =>
      pure ()
  pure lctx

-- Negating goal

-- | This negates the goal
def tryNegateGoal (tactic:Name) (goalId:MVarId) (target:Expr) (proofExpr:Expr) : ArithM (Option Goal) := do
  -- Get variables and type of proof
  let t ← mkTransformer proofExpr none
  unless ← isDefEq t.resultType target do
    return none
  unless ← resolveTransformerArgs proofExpr t do
    return none
  let pvar := t.assumptionVar
  -- Create free variable for representing proposition
  let fvar := ← mkFreshFVarId
  -- Get negated goal from assumption type
  let prop ← parseNegatedGoal tactic goalId t.assumptionType
  processAssumptionProp (Origin.negGoal fvar) (mkFVar fvar) prop
  let s ← get
  IO.println s! "negateGoal: {s.assertions.size} assertions."
  -- Create verification
  pure $ some {
      onAddAssumptions := do
        let lctx ← addAssertions (← getLCtx) s
        let falseExpr := mkConst ``False
        withReader (fun ctx => { ctx with lctx := lctx }) do
          let tag   ← getMVarTag goalId
          let proof ← mkFreshExprSyntheticOpaqueMVar falseExpr tag
          assignExprMVar pvar.mvarId! (bindAssumption fvar prop proof)
          assignExprMVar goalId (mkApp (mkAppN proofExpr t.arguments) pvar)
          pure [proof.mvarId!]
      onVerify := λproof => do
        -- Generate proof to pass into proof expr
        let newVal := bindAssumption fvar prop proof
        assignExprMVar pvar.mvarId! newVal
        assignExprMVar goalId (mkApp (mkAppN proofExpr t.arguments) pvar)
      }

theorem decidable_by_contra {P:Prop} [h:Decidable P] (q : ¬ P → False) : P :=
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
        let lctx ← addAssertions (← getLCtx) s
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
    processAssumptionProp (Origin.negGoal fvar) (mkFVar fvar) atp
    let s ← get
    IO.println s! "Extracted {s.assertions.size} assertions."
    -- Create verification
    return {
        onAddAssumptions := do
          let lctx ← addAssertions (← getLCtx) s
          let tag   ← getMVarTag goalId
          withReader (fun ctx => { ctx with lctx := lctx }) do
            let proof ← mkFreshExprSyntheticOpaqueMVar falseExpr tag
            assignExprMVar goalId <| bindAssumption fvar atp proof
            pure [proof.mvarId!]
        onVerify := λproof => do
          -- Generate proof to pass into proof expr
          assignExprMVar goalId <| bindAssumption fvar atp proof
        }
  let proofExpr := mkConst ``decidable_by_contra
  let target := md.type
  match ← tryNegateGoal tactic goalId md.type proofExpr with
  | none =>
    throwTacticEx tactic goalId m!"Unexpected goal tactic type{indentExpr md.type}"
  | some goal =>
    return goal

syntax (name := zify) "zify" : tactic

@[tactic zify] def evalZify : Tactic := fun stx => do
  liftMetaTactic fun mvarId => do
    checkNotAssigned mvarId `zify
    let some mvarDecl ← (← getMCtx).findDecl? mvarId
      | throwError "unknown goal {mvarId.name}"
    let (goal, s) ← (negateArithGoal `zify mvarId).run
    let r@([goalId]) ← goal.onAddAssumptions
      | throwError "Expected more goals"
    let some mvarDecl ← (← getMCtx).findDecl? goalId
      | throwError "unknown goal {goalId.name}"
    pure r

end ArithSolver

-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a))
def test_false_goal (a b : Nat) : False := by
  zify

-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a))
def test_nonneg_assumption (x : Int) (p : Int.NonNeg x): False := by
  zify

-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a))
def test_eq0_assumption (x : Int) (p : x = 0): False := by
  zify

-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a))
def test_eq_assumption (x y : Int) (p : x = y): False := by
  zify

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

set_option pp.all true

#print test_nat_gt_goal.proof_1
