/-
This module defines operations for constructing a
linear arithmetic state form a Lean context while
ensuring Lean proofs can be constructed from SAT check.
-/
import ArithSolver.IntNormalization
import Lean

open Lean
open Lean.Meta
open Lean.Elab.Tactic

namespace ArithSolver

private def ofNatExpr : Expr := mkConst ``Int.ofNat
private def intNonNegMkExpr : Expr := mkConst ``Int.NonNeg.mk
private def propExpr : Expr := mkSort levelZero

def falseExpr : Expr := mkConst ``False

structure Goal where
  -- Given a proof from the solver
  onMkProof : Expr → Expr

def Goal.onAddAssumptions (tactic:Name) (g:Goal) (goalId:MVarId) (s:State) : MetaM (List MVarId) := do
  checkNotAssigned goalId tactic
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
def mkTransformer (proof:Expr) : MetaM Transformer := do
  -- Get variables and type of proof
  let (vars, binders, resultType) ← forallMetaTelescope (← inferType proof)
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

end PredicateNormalizationLemmas

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
    let proof := mkAppN (mkConst ``intNonNeg_lemma) #[e, ← varExpr v, pr, proof]
    return (some (proof, Pred.IsGe0 v))
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
  let mkTrans (nm:Name) : Expr := mkConst nm
  -- Create list of transformers to apply
  let transformers : Array Expr := #[
          mkTrans ``nat_eq_prop,
          mkTrans ``nat_lt_prop,
          mkTrans ``Int.nonNeg_of_nat_le,
          mkTrans ``nat_gt_prop,
          mkTrans ``nat_ge_prop,
          mkTrans ``nat_not_eq_prop,
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
  for rule in transformers do
    -- Get variables and type of proof
    let t ← mkTransformer rule
    unless ← isDefEq t.assumptionType prop do
      continue
    unless ← resolveTransformerArgs rule t do
      continue
    found := (mkApp (mkAppN rule t.arguments) proof, t.resultType)
    break
  match found with
  | none =>
    pure none
  | some (proof, prop) => do
    extractPropPred proof prop

-- | See if we can add the local declaration to the arithmetic unit.
-- proof is a term of type prop.
def processAssumptionProp (origin : Option FVarId) (name:Name) (proof:Expr) (prop:Expr) : ArithM Bool := do
  match ← extractPropPred proof prop with
  | none => do
    pure false
  | some (proof, pred) => do
    assertPred origin name proof pred
    pure true

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
      let _ ← processAssumptionProp (some d.fvarId) d.userName (mkFVar d.fvarId) d.type

-- Negating goal

theorem decidable_by_contra {P:Prop} [h:Decidable P] (q : ¬¬P) : P :=
  match h with
  | isFalse h => False.elim (q h)
  | isTrue h => h

def analyzeGoal (tactic:Name) (goalId:MVarId) (target:Expr) : ArithM Goal := do
  -- If goal is already false, then just negate it.
  if ← isDefEq target falseExpr then
    return { onMkProof := id }

  -- If goal has form `Not p` then we can diretly process property.
  match ← matchNot target with
  | some prop => do
    if ← processAssumptionProp none `negGoal (mkBVar 0) prop then
      return { onMkProof := mkLambda Name.anonymous BinderInfo.default prop }
  -- Goal is not a negation, so we seeing if we can extract a predicate from
  -- negated goal and then use decidable_by_contra to get proof of negation
  -- of target.
  | none =>
    let prop := mkApp (mkConst ``Not) target
    if ← processAssumptionProp none `negGoal (mkBVar 0) prop then
      let some classVal ← synthInstance? (mkApp (mkConst ``Decidable) target)
          | throwTacticEx tactic goalId "Could not synthesize Decidable instance for proposition:."
      let decideByContraExpr := mkAppN (mkConst ``decidable_by_contra) #[target, classVal]
      return {
          onMkProof := fun goalProof =>
            mkApp decideByContraExpr (mkLambda Name.anonymous BinderInfo.default prop goalProof)
          }

  -- In final case, we just ignore the goal and try to prove a contradiction from assumptions
  -- alone.
  match ← inferType target with
  | Expr.sort lvl _ =>
    pure { onMkProof := fun goalProof =>
      mkAppN (mkConst ``False.elim [lvl]) #[target, goalProof]
    }
  | _ =>
    throwTacticEx tactic goalId "Expected a type."

def mkArithGoal (tactic:Name) (goalId:MVarId) : MetaM (Goal × State) := ArithM.run do
  withMVarContext goalId do
    let md ← getMVarDecl goalId
    processDecls md.lctx
    analyzeGoal tactic goalId md.type

syntax (name := to_poly) "to_poly" : tactic

@[tactic to_poly] def evalToPoly : Tactic := fun stx => do
  liftMetaTactic fun mvarId => do
    let (goal, s) ← mkArithGoal `to_poly mvarId
    let r@([goalId]) ← goal.onAddAssumptions `to_poly mvarId s
      | throwError "Expected more goals"
    pure r

end ArithSolver