import ClausalExtraction.Context

open Lean
open Lean.Meta

namespace ClausalExtraction

section ExpressionUtils

private def propExpr : Expr := mkSort levelZero

def exprHead : Expr → Option Name
| Expr.bvar .. => none
-- FIXME: Figure out if we want to see through free variables with let bindings in local context.
| Expr.fvar .. => none
| Expr.mvar .. => none
| Expr.sort .. => none
| Expr.const nm .. => nm
| Expr.app f a .. => exprHead f
| Expr.lam .. => none
| Expr.forallE .. => none
-- FIXME: Figure out if we want to see through let bindings.
| Expr.letE .. => none
| Expr.lit .. =>  none
-- FIXME: Figure out if ignoring metadata is always ok.
| Expr.mdata  _ x .. => exprHead x
 -- FIXME: Figure out if we want to see through projections.
| Expr.proj n i s .. => none

end ExpressionUtils

def falseExpr : Expr := mkConst ``False

-- | Assertion added
structure Assertion where
  -- Identifies the free variable in the initial context used to generate this one.
  -- Used to allow deleting original proposition from local context.
  origin : Option FVarId
  -- The free variable used to identify the assertion in the local context
  -- generated for the assertion.
  name : Name
  -- Predicate that was asserted.
  pred : Pred
  -- A proof of the predicate in the context of the original goal.
  --
  -- N.B. It may be ideal to explore if we can defer producing this until needed.
  proof : Expr

namespace Assertion

instance : Inhabited Assertion := ⟨
     { origin := arbitrary,
       name := arbitrary,
       pred := arbitrary,
       proof := arbitrary,
     }
  ⟩

end Assertion


structure State where
  -- Predicates asserted to be true.
  assertions : Array Assertion := #[]

namespace State

-- | Return proofs associated with assertions.
def proofs (s:State) : Array Expr := s.assertions.map Assertion.proof

end State

/--
This contains the inferred satisfiability problem from a lean proof.
-/
structure SatProblem where
  -- Identifier of original goal to prove
  goalId : MVarId
  -- Context used to convert to a decision proedure
  context : Context
  -- Assumptions inferred
  state : State
  -- Given a proof from the solver this constructs a proof of the goal.
  onMkProof : Expr → Expr

namespace SatProblem

-- | Add assertions to local context.
-- Return new local context along with array of free variables identifying assertions.
def adjustLocalContext (ctx:Context) (s:State) (lctx:LocalContext) : MetaM (LocalContext × Array Expr) := do
  let mut lctx := lctx
  let mut fvars : Array Expr := #[]
  for a in s.assertions do
    let newVar ← mkFreshFVarId
    fvars := fvars.push (mkFVar newVar)
    match a.origin with
    | some prevVar =>
      -- FIXME: Make sure erasing the previous declaration does not break things.
      lctx := lctx.erase prevVar
    | none =>
      pure ()
    let e ← ctx.predExpr a.pred
    lctx := lctx.mkLocalDecl newVar a.name e
  pure (lctx, fvars)

/-
This does the work of actually applying the normalization procedure to the problem.

It is setup as an extra step so that a decision procedure could be tried before
committing to using the normalization procedure.
-/
def apply (g:SatProblem) : MetaM (List MVarId) := do
  let tag   ← getMVarTag g.goalId
  let lctx ← getLCtx
  let (lctx, fvars) ← adjustLocalContext g.context g.state lctx
  withReader (fun ctx => { ctx with lctx := lctx }) $ do
    let solverSatProblem ← mkFreshExprSyntheticOpaqueMVar falseExpr tag
    -- Turn goal into lambda with free variables from assertions
    let fn ← Meta.mkLambdaFVars fvars solverSatProblem
    -- Assign goal
    assignExprMVar g.goalId (g.onMkProof (mkAppN fn g.state.proofs))
    pure [solverSatProblem.mvarId!]

end SatProblem

def matchNot (e:Expr) : MetaM (Option Expr) := do
  let mvar ← mkFreshExprMVar propExpr MetavarKind.natural `a
  let p := mkApp (mkConst ``Not) mvar
  pure $ if ← isDefEq p e then mvar else none

-- | See if we can add the local declaration to the arithmetic unit.
-- proof is a term of type prop.
def tryAddPred (ctx:Context)
                 (r:IO.Ref State)
                 (origin : Option FVarId)
                 (name:Name)
                 (proof:Expr)
                 (prop:Expr) : MetaM Bool := do
  let rules ← ctx.propTheoryMap.getMatch prop
  for t in rules do
    match ← t.action prop ctx.services with
    | none => pure ()
    | some (p, proofFn) => do
      let pred := Pred.mkPred t.theoryRef p
      let a := { origin := origin, name := name, proof := mkApp proofFn proof, pred := pred }
      r.modify $ λs => { s with assertions := s.assertions.push a }
      return true
  return false

theorem decidable_by_contra {P:Prop} [h:Decidable P] (q : ¬¬P) : P :=
  match h with
  | isFalse h => False.elim (q h)
  | isTrue h => h

def processDecls (ctx:Context) (r:IO.Ref State) (lctx:LocalContext) : MetaM Unit := do
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
    -- FIXME: Figure out how to support let declarations
    if d.isLet then
      continue
    -- If this is a proposition then try assuming it.
    if ← isDefEq (← inferType d.type) propExpr then do
      let _ ← tryAddPred ctx r (some d.fvarId) d.userName (mkFVar d.fvarId) d.type

-- | This analyze the goal of the problem.
def analyzeSatProblem (ctx:Context) (r : IO.Ref State) (tactic:Name) (goalId:MVarId) (target:Expr)
   : MetaM (Expr → Expr) := do
  -- If goal is already false, then just negate it.
  if ← isDefEq target falseExpr then
    return id
  -- If goal has form `Not p` then we can diretly process property.
  match ← matchNot target with
  | some prop => do
    if ← tryAddPred ctx r none `negGoal (mkBVar 0) prop then
      return (mkLambda Name.anonymous BinderInfo.default prop)
  -- Goal is not a negation, so we seeing if we can extract a predicate from
  -- negated goal and then use decidable_by_contra to get proof of negation
  -- of target.
  | none =>
    let prop := mkApp (mkConst ``Not) target
    if ← tryAddPred ctx r none `negGoal (mkBVar 0) prop then
      let some classVal ← synthInstance? (mkApp (mkConst ``Decidable) target)
          | throwTacticEx tactic goalId "Could not synthesize Decidable instance for proposition:."
      let decideByContraExpr := mkAppN (mkConst ``decidable_by_contra) #[target, classVal]
      return (fun goalProof => mkApp decideByContraExpr (mkLambda Name.anonymous BinderInfo.default prop goalProof))

  -- In final case, we just ignore the goal and try to prove a contradiction from assumptions
  -- alone.
  match ← inferType target with
  | Expr.sort lvl _ =>
    pure (mkApp (mkApp (mkConst ``False.elim [lvl]) target))
  | _ =>
    throwTacticEx tactic goalId "Expected a type."

def mkGoal (ctx:Context) (tactic:Name) (goalId:MVarId) : MetaM SatProblem := do
  withMVarContext goalId do
    let md ← getMVarDecl goalId
    let stateRef ← IO.mkRef {}
    processDecls ctx stateRef md.lctx
    let fn ← analyzeSatProblem ctx stateRef tactic goalId md.type
    let s ← stateRef.get
    pure { goalId := goalId, context := ctx, state := s, onMkProof := fn }

end ClausalExtraction
