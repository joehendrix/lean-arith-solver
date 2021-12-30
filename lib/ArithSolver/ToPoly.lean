import ArithSolver.IntNormalization
import Lean

open Lean
open Lean.Meta
open Lean.Elab.Tactic

namespace ArithSolver

private def ofNatExpr : Expr := mkConst ``Int.ofNat
private def intNonNegMkExpr : Expr := mkConst ``Int.NonNeg.mk
private def propExpr : Expr := mkSort levelZero

-- | Given a proposition equivalent to λ(x:P) => False, this returns type p
def parseNegatedGoal (tactic:Name) (goalId:MVarId) (ptp:Expr) : MetaM Expr := do
  match ptp with
  | Expr.forallE an atp (Expr.const ``False _ _) ad => do
    pure atp
  | Expr.app (Expr.const ``Not [] _) atp _ => do
    pure atp
  | _ =>
    throwTacticEx tactic goalId m!"Expected negation input goal to be False instance of {indentExpr ptp}"

def falseExpr : Expr := mkConst ``False

structure Goal where
  -- Given a proof from the solver
  onMkProof : Expr → Expr

def Goal.onAddAssumptions (g:Goal) (goalId:MVarId) (s:State) : MetaM (List MVarId) := do
  let tag   ← getMVarTag goalId
  let lctx ← getLCtx
  let (lctx, fvars) ← s.addAssertions lctx
  withReader (fun ctx => { ctx with lctx := lctx }) $ do
    let solverGoal ← mkFreshExprSyntheticOpaqueMVar falseExpr tag
    -- Turn goal into lambda with free variables from assertions
    let fn ← Meta.mkLambdaFVars fvars solverGoal
    -- Assign goal
    assignExprMVar goalId (g.onMkProof (mkAppN fn s.proofs))
    pure [solverGoal.mvarId!]

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
  pure $ if ← isDefEq (mkIntNonNegExpr mvar) e then some mvar else none

def matchIntEq0 (e:Expr) : MetaM (Option Expr) := do
  let mvar ← mkFreshExprMVar intExpr MetavarKind.natural `n
  pure $ if ← isDefEq (mkIntEq0Expr mvar) e then some mvar else none

def matchNotIntEq0 (e:Expr) : MetaM (Option Expr) := do
  let mvar ← mkFreshExprMVar intExpr MetavarKind.natural `n
  if ← isDefEq (mkApp (mkConst ``Not) (mkIntEq0Expr mvar)) e then
    pure $ some mvar
  else
    none

def matchNot (e:Expr) : MetaM (Option Expr) := do
  let mvar ← mkFreshExprMVar propExpr MetavarKind.natural `a
  let p := mkApp (mkConst ``Not) mvar
  pure $ if ← isDefEq p e then mvar else none


theorem nat_le_prop {x y : Nat} (p : x ≤ y)
  : Int.NonNeg (OfNat.ofNat y - OfNat.ofNat x) := by
  simp [OfNat.ofNat]
  simp [Int.ofNat_sub_ofNat, Int.subNatNat_sub_ofNat]
  have q : x-y = 0 := Nat.sub_is_zero_is_le.mp p
  simp [Int.subNatNat, q]
  apply Int.NonNeg.mk

theorem nat_lt_prop {x y : Nat} (p : x < y)
  : Int.NonNeg (OfNat.ofNat y - OfNat.ofNat x - 1) := by
    have q := nat_le_prop p
    simp only [OfNat.ofNat, Int.ofNat_sub_ofNat, Int.subNatNat_sub_ofNat]
    simp only [OfNat.ofNat, Int.ofNat_sub_ofNat] at q
    exact q
def nat_ge_prop {x y : Nat} (p : x ≥ y) := nat_le_prop p
def nat_gt_prop {x y : Nat} (p : x > y) := nat_lt_prop p

theorem nat_not_le_prop {x y : Nat} (p : ¬(x ≤ y))
  : Int.NonNeg (OfNat.ofNat x - OfNat.ofNat y - 1) := sorry
theorem nat_not_lt_prop {x y : Nat} (p : ¬(x < y))
  : Int.NonNeg (OfNat.ofNat x - OfNat.ofNat y) := sorry
def nat_not_ge_prop {x y : Nat} (p : ¬(x ≥ y)) := nat_not_le_prop p
def nat_not_gt_prop {x y : Nat} (p : ¬(x > y)) := nat_not_lt_prop p

theorem int_eq_prop (x y : Int) (p : x = y)
  : x - y = 0 := by simp [p, Int.sub_self]
theorem nat_eq_prop {x y : Nat} (p : x = y)
  : (OfNat.ofNat x : Int) - OfNat.ofNat y = 0 := by
    apply int_eq_prop; rw [p]


theorem int_le_prop {x y : Int} (p : x ≤ y)
  : Int.NonNeg (y - x) := sorry
theorem int_lt_prop {x y : Int} (p : x < y)
  : Int.NonNeg (y - x - 1) := sorry
def int_ge_prop {x y : Int} (p : x ≥ y) := int_le_prop p
def int_gt_prop {x y : Int} (p : x > y) := int_lt_prop p


private
theorem subNatNat_zero_implies_equal {x y :Nat} (q:Int.subNatNat x y = 0) : x = y := by
  simp [Int.subNatNat] at q
  have p : y - x = 0 := by
    generalize g:y-x=z
    cases z with
    | zero => rfl
    | succ z => simp [g] at q
  simp [p, OfNat.ofNat] at q
  revert y
  induction x with
  | zero =>
    intros y p q
    exact p.symm
  | succ x ind =>
    intros y
    cases y with
    | zero =>
      intros p q
      simp [Nat.sub_zero] at q
    | succ y =>
      simp [Nat.succ_sub_succ]
      exact (@ind y)

theorem int_not_eq_prop {x y : Int} (p : ¬(x = y))  : ¬(x - y = 0) := by
  intro q
  apply p; clear p
  cases x with
  | ofNat x =>
    cases y with
    | ofNat y =>
      simp [Int.ofNat_sub_ofNat] at q
      simp [subNatNat_zero_implies_equal q]
    | negSucc y =>
      simp only [Int.ofNat_sub_negSucc, OfNat.ofNat, Nat.add_succ] at q
      apply Int.noConfusion q
      intro r
      apply Nat.noConfusion r
  | negSucc x =>
    cases y with
    | ofNat y =>
      simp only [Int.negSucc_sub_ofNat, OfNat.ofNat, Nat.add_succ] at q
    | negSucc y =>
      simp [Int.negSucc_sub_negSucc] at q
      simp [subNatNat_zero_implies_equal q]

theorem int_not_le_prop {x y : Int} (p : ¬(x ≤ y))
  : Int.NonNeg (x - y - 1) := sorry
theorem int_not_lt_prop {x y : Int} (p : ¬(x < y))
  : Int.NonNeg (x - y) := sorry
def int_not_ge_prop {x y : Int} (p : ¬(x ≥ y)) := int_not_le_prop p
def int_not_gt_prop {x y : Int} (p : ¬(x > y)) := int_not_lt_prop p


theorem nat_not_eq_prop {x y : Nat} (p : ¬(x = y))
  : ¬(Int.ofNat x - Int.ofNat y = 0) := by
  apply int_not_eq_prop
  simp [p]

-- Lemma used for convert proofs from one type of predicate to another.
private theorem intNonNeg_lemma {x y :Int} (eq:x = y) (p:Int.NonNeg x) : Int.NonNeg y := eq.subst p
private theorem intEq0_lemma {x y :Int} (eq:x = y) (p:x = 0) : y = 0 := @Eq.subst Int (λd => d = 0) _ _ eq p
private theorem intNe0_lemma {x y :Int} (eq:x = y) (p:¬(x = 0)) : ¬(y = 0) := @Eq.subst Int (λd => ¬(d = 0)) _ _ eq p

-- | Analyze a proof and a proposition to produce a Linear arith predicate along with a proof
-- that of the predicate.
partial def extractPropPred (proof:Expr) (prop:Expr) : ArithM (Option (Expr × Pred)) := do
  -- Check if prop matches (Int.NonNeg e)
  match ← matchIntNonNeg prop with
  | none => pure ()
  | some e =>
    let (v, pr) ← purifyIntExpr e
    IO.println s!"Asserting non neg:\n  proof = {←instantiateMVars proof}"
    let proof2 := mkAppN (mkConst ``intNonNeg_lemma) #[e, ← varExpr v, pr, proof]
    return (some (proof2, Pred.IsGe0 v))
  -- Check if prop match (e = Int.ofNat 0)
  match ← matchIntEq0 prop with
  | none => pure ()
  | some e =>
    let (v, pr) ← purifyIntExpr e
    let proof := mkAppN (mkConst ``intEq0_lemma) #[e, ← varExpr v, pr, proof]
    return (some (proof, Pred.IsEq0 v))
  match ← matchNotIntEq0 prop with
  | none => pure ()
  | some e =>
    let (v, pr) ← purifyIntExpr e
    let proof := mkAppN (mkConst ``intNe0_lemma) #[e, ← varExpr v, pr, proof]
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
    IO.println s!"Applying {rule}:\n  Args: {t.arguments}\n  Proof: {proof}"
    found := (mkApp (mkAppN rule t.arguments) proof, t.resultType)
    break
  match found with
  | none =>
    pure none
  | some (proof, prop) => do
    extractPropPred proof prop

-- | See if we can add the local declaration to the arithmetic unit.
-- proof is a term of type prop.
def processAssumptionProp (origin : Option FVarId) (name:Name) (proof:Expr) (prop:Expr) : ArithM Unit := do
  match ← extractPropPred proof prop with
  | none => do
    pure ()
  | some (proof, pred) => do
    assertPred origin name proof pred

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
      let v ← getUninterpVar (mkApp ofNatExpr (mkFVar d.fvarId))
      -- Assert v is non negative
      let proof := mkApp intNonNegMkExpr (mkFVar d.fvarId)
      assertPred none (d.userName ++ "isGe0") proof (Pred.IsGe0 v)
      continue
    -- If we have a natural number, then declare it.
    if ← isDefEq d.type intExpr then
      let v ← getUninterpVar (mkFVar d.fvarId)
      continue
    -- If this is a proposition then try assuming it.
    if ← isDefEq (← inferType d.type) propExpr then do
      processAssumptionProp (some d.fvarId) d.userName (mkFVar d.fvarId) d.type

-- Negating goal

theorem decidable_by_contra {P:Prop} [h:Decidable P] (q : ∀(ng:¬ P), False) : P :=
  match h with
  | isFalse h => False.elim (q h)
  | isTrue h => h

def negateArithGoal (tactic:Name) (goalId:MVarId) : ArithM Goal := do
  let md ← getMVarDecl goalId
  processDecls md.lctx
  if ← isDefEq md.type falseExpr then
    return { onMkProof := id }
  match ← matchNot md.type with
  | none => pure ()
  | some prop => do
    processAssumptionProp none `negGoal (mkBVar 0) prop
    -- Create verification
    return { onMkProof := mkLambda Name.anonymous BinderInfo.default prop }
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
  -- Pvar is a metavariable of type "prop -> False"
  processAssumptionProp none `negGoal (mkBVar 0) prop
  pure $ {
      onMkProof := fun goalProof =>
        mkApp decideByContraExpr (mkLambda Name.anonymous BinderInfo.default prop goalProof)
      }

syntax (name := to_poly) "to_poly" : tactic

@[tactic to_poly] def evalToPoly : Tactic := fun stx => do
  liftMetaTactic fun mvarId => do
    checkNotAssigned mvarId `zify
    let (goal, s) ← (negateArithGoal `zify mvarId).run
    let r@([goalId]) ← goal.onAddAssumptions mvarId s
      | throwError "Expected more goals"
    pure r

end ArithSolver