import ClausalExtraction.ArithTheory.IntNormalization
import ClausalExtraction.Context

open Lean
open Lean.Meta

namespace ClausalExtraction

namespace ArithTheory

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

-- Utility that adds a proposition recognizer based on a transformer.
def mkTermTrans (thref:TheoryRef) (termRules:DiscrTree PredRule) (ctx:Context) (nm:Name) : MetaM Context := do
  let ruleExpr := mkConst nm
  let trans ← mkTransformer ruleExpr
  let action := fun (prop:Expr) => do
            let trans ← mkTransformer ruleExpr
            unless ← isDefEq trans.assumptionType prop do
              return none
            unless ← resolveTransformerArgs ruleExpr trans do
              return none
            let propProofFn := mkAppN ruleExpr trans.arguments
            let rules ← termRules.getMatch trans.resultType
            for t in rules do
              match ← t.action trans.resultType with
              | none => pure ()
              | some (pred, nextProofFn) => do
                let finalProofFn :=
                      mkLambda Name.anonymous BinderInfo.default prop
                        (mkApp nextProofFn (mkApp propProofFn (mkBVar 0)))
                return (some (pred, finalProofFn))
            return none
  ctx.addPropRecognizer trans.assumptionType thref action

def addArithTheory (ctx:Context) : MetaM Context := do
    let ref ← IO.mkRef {}
    -- Declare theory
    let (ctx, arithTheoryRef) := ctx.addTheory (ArithTheory.ops ref)
    -- Add recognizers
    let m ← mkFreshExprMVar natExpr MetavarKind.natural `m
    let x ← mkFreshExprMVar intExpr MetavarKind.natural `x
    let y ← mkFreshExprMVar intExpr MetavarKind.natural `y
    let e := mkAppN intAddConst #[x, y]
    let ctx ← ctx.assocExprToTheory e arithTheoryRef (λe => purifyIntExpr e ref)
    let e := mkAppN intSubConst #[x, y]
    let ctx ← ctx.assocExprToTheory e arithTheoryRef (λe => purifyIntExpr e ref)
    let e := mkAppN intMulConst #[x, y]
    let ctx ← ctx.assocExprToTheory e arithTheoryRef (λe => purifyIntExpr e ref)
    let e := mkAppN intNegConst #[x]
    let ctx ← ctx.assocExprToTheory e arithTheoryRef (λe => purifyIntExpr e ref)
    -- Add of nat operation
    let e := mkOfNat m
    let ctx ← ctx.assocExprToTheory e arithTheoryRef (λe => purifyIntExpr e ref)
    -- Add fundamental recognizers
    let ctx ← ctx.addPropRecognizer (mkIntNonNegExpr x) arithTheoryRef (matchIntNonNeg ref)
    let ctx ← ctx.addPropRecognizer (mkIntEq0Expr x) arithTheoryRef (matchIntEq0 ref)
    let ctx ← ctx.addPropRecognizer (mkApp (mkConst ``Not) (mkIntEq0Expr x)) arithTheoryRef (matchNotIntEq0 ref)
    -- Add final recognizers
    (ArithTheory.transformerNames.foldlM (mkTermTrans arithTheoryRef ctx.propTheoryMap) ctx : MetaM Context)

end ArithTheory

end ClausalExtraction