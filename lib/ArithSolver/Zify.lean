import Lean
open Lean
open Lean.Meta
open Lean.Elab.Tactic

namespace Nat
--theorem gt_of_not_le {m n : Nat} (p : m ≤ n → False) : m > n :=
--  match lt_or_ge n m  with
 -- | Or.inl h => h
 -- | Or.inr h => False.elim (p h)
end Nat

namespace Int

@[simp]
theorem add_zero (n : Int) : n + 0 = n := by
  admit

theorem ofNat_succ {m : Nat} : Int.ofNat (Nat.succ m) = Int.ofNat m + 1 := by rfl

theorem le_ofNat_toNonNeg {m n : Nat} (p : m ≤ n) : Int.NonNeg (Int.ofNat n - Int.ofNat m) := by
  admit


end Int
--syntax "[" term,* "]"  : term


namespace ArithSolver

inductive Constraint where
| NatGt : Expr → Expr → Constraint


syntax "[exprApp|" sepBy1(term, ", ") "]" : term

macro_rules
  | `([exprApp| $elems,* ]) => do
    let rec loop (l:List Syntax) (skip:Bool) (result: Syntax) : MacroM Syntax := do
          match l, skip with
          | [], _ => pure result
          | h :: r, true => loop r false result
          | h :: r, false => loop r true (← ``(Expr.app $result $h _))
    match elems.elemsAndSeps.toList with
    | [] => do
      throw Macro.Exception.unsupportedSyntax
    | h :: r => do
      loop r true h


syntax "binRel[" term "," term  "," term "," term "]" : term
macro_rules
  | `(binRel[ $op, $cl, $lhs, $rhs]) => `([exprApp| Expr.const $op _ _, _, Expr.const $cl _ _, $lhs, $rhs])

syntax (name := zify) "zify" : tactic

def mkAuxNameImp (binderName : Name) : MetaM (Name × List Name) := do
    let binderName ← mkFreshUserName binderName
    pure (binderName, [])

theorem nat_gt_by_contra (m n : Nat) (p : ¬ (Int.NonNeg (Int.ofNat n - Int.ofNat m))) : m > n := by
  exact Nat.gt_of_not_le (λr => p (Int.le_ofNat_toNonNeg r))

theorem nat_lt_by_contra (m n : Nat) (p : ¬ (Int.NonNeg (Int.ofNat m - Int.ofNat n))) : m < n := by
  exact Nat.gt_of_not_le (λr => p (Int.le_ofNat_toNonNeg r))

def appendParentTag (mvarId : MVarId) (newMVars : Array Expr) (binderInfos : Array BinderInfo) : MetaM Unit := do
  let parentTag ← getMVarTag mvarId
  if newMVars.size == 1 then
    -- if there is only one subgoal, we inherit the parent tag
    setMVarTag newMVars[0].mvarId! parentTag
  else
    unless parentTag.isAnonymous do
      newMVars.size.forM fun i => do
        let newMVarId := newMVars[i].mvarId!
        unless (← isExprMVarAssigned newMVarId) do
          unless binderInfos[i].isInstImplicit do
            let currTag ← getMVarTag newMVarId
            setMVarTag newMVarId (appendTag parentTag currTag)

def intType : Expr := mkConst ``Int []
def intSubClass : Expr := mkAppN (mkConst ``instHSub [levelZero]) #[intType, mkConst `Int.instSubInt]

def intSub (m n : Expr) : Expr := 
  let hSub := mkConst `HSub.hSub [levelZero, levelZero, levelZero]
  mkAppN hSub #[intType, intType, intType, intSubClass, m, n]

def intOfNat : Expr → Expr := mkApp (mkConst ``Int.ofNat)

-- | An assumption in the goal
structure Assumption where
  -- The property we can assume
  prop : Expr
  -- An expression referencing the input proof.
  proof : Expr
  

-- | An assumption in the goal
structure NegatedGoal where
  -- The proposition we can assume
  assumptionProp : Expr
  -- An expression referencing the input proof.
  assumptionProof : FVarId
  mkResult : (Expr → Expr)

def parseNegatedGoal (tactic:Name) (goalId:MVarId) (pvar:Expr) : MetaM NegatedGoal := do
  let ptp ← inferType pvar
  let ptp ← instantiateMVars ptp
  match ptp with
  | Expr.forallE an atp (Expr.const ``False [] fd) ad => do
    let fvar := ← mkFreshFVarId
    let mkResult (proof : Expr) :=
          mkLambda `negGoal BinderInfo.default atp (proof.replaceFVarId fvar (mkBVar 0))
    pure { assumptionProp := atp, assumptionProof := fvar, mkResult := mkResult }
  | Expr.app (Expr.const ``Not [] nd) atp ad => do
    let fvar := ← mkFreshFVarId
    let mkResult (proof : Expr) :=
          mkLambda `negGoal BinderInfo.default atp (proof.replaceFVarId fvar (mkBVar 0))
    pure { assumptionProp := atp, assumptionProof := fvar, mkResult := mkResult }
  | _ => 
    throwTacticEx tactic goalId m!"Expected negation input goal to be False instance of {indentExpr ptp}"

-- | Add assumption to local const
def addNegatedGoalToLocalContext (lctx:LocalContext) (name:Name) (ng:NegatedGoal) : LocalContext := Id.run do
  pure $ lctx.mkLocalDecl ng.assumptionProof name ng.assumptionProp

structure Goal where
  assumptions : Array Assumption
  -- Callback that adds assumptions to local context and returns
  -- proof obligations.
  onAddAssumptions : MetaM (List MVarId)
  -- Callback that given a proof of false produces a proof of the goal.
  onVerify : Expr → MetaM Expr


-- | This negates the goal 
def tryNegateGoal (tactic:Name) (goalId:MVarId) (targetType:Expr) (proofExpr:Expr) : MetaM (Option Goal) := do
  -- Get variables and type of proof
  let (vars, _, eType) ← forallMetaTelescopeReducing (← inferType proofExpr)

  if not (← isDefEq eType targetType) then
    pure none
  else
    let isUnassigned (mvar:Expr) := not <$> isExprMVarAssigned mvar.mvarId!
    let unassigned ← vars.filterM isUnassigned
    if unassigned.size ≠ 1 then
      throwTacticEx tactic goalId m!"Expected single proof obligation in falsification {indentExpr proofExpr}"
    let pvar := unassigned[0]
    -- Generate negated goal from unassigned proof
    let ng ← parseNegatedGoal tactic goalId pvar
    -- Define assumption
    let a := { prop := ng.assumptionProp, proof := mkFVar ng.assumptionProof }
    -- Create verification
    pure $ some { 
        assumptions := #[a],
        onAddAssumptions := do
          let lctx ← getLCtx
          let lctx := addNegatedGoalToLocalContext lctx `negGoal ng
          let falseExpr := mkConst ``False
          withReader (fun ctx => { ctx with lctx := lctx }) do
            let tag   ← getMVarTag goalId
            let proof ← mkFreshExprSyntheticOpaqueMVar falseExpr tag
            let newVal ← ng.mkResult proof
            assignExprMVar pvar.mvarId! newVal
            assignExprMVar goalId (mkAppN proofExpr vars)
            pure [proof.mvarId!]
        onVerify := λproof => do
          -- Generate proof to pass into proof expr
          let newVal ← ng.mkResult proof
          assignExprMVar pvar.mvarId! newVal
          pure (mkAppN proofExpr vars)
        }


def negateArithGoal (tactic:Name) (goalId:MVarId) : MetaM Goal := do
  let md ← getMVarDecl goalId
  let targetType ← instantiateMVars md.type
  let targetTypeNumArgs ← getExpectedNumArgs targetType
  if targetTypeNumArgs ≠ 0 then
    throwTacticEx `zify goalId m!"Expected target to have no arguments {indentExpr targetType}."
  
  match targetType with
  | Expr.const ``False [] _ => do
    pure { 
      assumptions := #[]
      onAddAssumptions := pure [goalId]
      onVerify := pure
    }
  | otherwise => do
    let mut result := none
    let goalNegations := #[mkConst ``nat_gt_by_contra, mkConst ``nat_lt_by_contra]
    for proofExpr in goalNegations do
      match ← tryNegateGoal tactic goalId targetType proofExpr with
      | none => pure ()
      | some goal => do
        result := some goal
        break
    match result with
    | some g => pure g
    | none => 
      throwTacticEx tactic goalId m!"Unexpected goal tactic type{indentExpr targetType}"

@[tactic zify] def evalZify : Tactic := fun stx => do
  liftMetaTactic fun mvarId => do
    checkNotAssigned mvarId `zify
    let goal ← negateArithGoal `zify mvarId
    -- let ax := mkAppN (mkConst `sorryAx [levelZero]) #[mkConst ``False, mkConst ``Bool.false]
    -- assignExprMVar  mvarId (← goal.onVerify ax)
    -- pure []
    goal.onAddAssumptions

end ArithSolver

-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a)) 
def test_nat_gt_goal (a b : Nat) : (a > b) := by
  zify

-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a)) 
def test_nat_lt_goal (a b : Nat) : (a < b) := by
  zify

-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a)) 
def test_false_goal (a b : Nat) : False := by
  zify


set_option pp.all true

#print test.proof_1
  --contradict

--  injections
--  admit
