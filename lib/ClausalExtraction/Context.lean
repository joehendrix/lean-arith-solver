import ClausalExtraction.Basic
import ClausalExtraction.ConstantTheory

import Lean.Meta.DiscrTree

open Lean
open Lean.Meta (DiscrTree)

namespace ClausalExtraction

/-
This define the static components used to analyze expressions.
-/
structure Context where
  -- An array of theory operation.
  theories : Array TheoryOps
  -- Recognizes terms and generates theory variables for them.
  termRecognizerMap : DiscrTree TermRecognizerPair
  -- Theory for constants created because term is not recognized.
  constantTheory : TheoryRef
  -- State used for creating constants.
  constantState : IO.Ref ConstantTheory.State
  -- Used to map propositions to rules to apply.
  propTheoryMap : DiscrTree PredRule

namespace Context

def addTheory (ctx:Context) (ops:TheoryOps) : Context × TheoryRef :=
  ({ctx with theories := ctx.theories.push ops }, TheoryRef.ofNat ctx.theories.size)

def assocExprToTheory (ctx:Context) (e:Expr) (th:TheoryRef) (recog:TermRecognizer)
    : MetaM Context := do
  let m ← ctx.termRecognizerMap.insert e ⟨th,recog⟩
  pure { ctx with termRecognizerMap := m }

def addPropRecognizer (ctx:Context) (pat:Expr) (th:TheoryRef) (action : Expr → SolverM (Option (TheoryPred × Expr)))
   : MetaM Context := do
   let m ← ctx.propTheoryMap.insert pat ⟨th, action⟩
   pure { ctx with propTheoryMap := m }

partial def varExpr (ctx:Context) (v:Var) : IO Expr := do
  let th := ctx.theories[v.theory.toNat]
  th.varExpr (varExpr ctx) v.theoryVar

def predExpr (ctx:Context) (p:Pred) : IO Expr := do
  let ref := p.theory.toNat
  if h : ref < ctx.theories.size then
    let ops := (ctx.theories.get ⟨ref, h⟩)
    let e ← ops.predExpr (ctx.varExpr) p.theoryPred
    pure e
  else
    panic! "Invalid theory index."

mutual

-- | Create a variable for the current expression from a theory.
--
-- The source theory is the theory that initiated the request from a variable.
-- If the expression head is assigned to this theory, then we ensure this is an
-- uninterpreted symbol.
partial
def exprVar (ctx:Context) (e:Expr) : MetaM (VarDefinition Var) := do
  -- Get theory associated with head symbol.
  let l ← ctx.termRecognizerMap.getMatch e
  if l.size > 1 then
    throwError "Multiple matches in theory map."
  if p : 0 < l.size then
    let v := l.get ⟨0, p⟩
    let r ← v.function e (services ctx)
    pure { r with var := Var.mkVar v.theoryRef r.var }
  else
    let th := ctx.constantTheory
    let thv ← ConstantTheory.exprVar ctx.constantState e
    let eq ← ConstantTheory.mkRflProof e
    pure { var := Var.mkVar th thv, varExpr := e, eq := eq }

partial
def services (ctx:Context) : SolverServices := {
    varExpr := varExpr ctx,
    exprVar := exprVar ctx,
  }

end

def init : IO Context := do
  let constRef ← IO.mkRef {}
  let uninterpTheory := ConstantTheory.ops constRef

  pure {
    theories := #[uninterpTheory],
    termRecognizerMap := {},
    constantTheory := ⟨0⟩,
    constantState := constRef,
    propTheoryMap := {},
  }

end Context


end ClausalExtraction