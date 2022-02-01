/-
This module defines operations for constructing a
linear arithmetic state form a Lean context while
ensuring Lean proofs can be constructed from SAT check.
-/
import ClausalExtraction.ArithTheory
import ClausalExtraction.State
import Lean.Elab.Tactic

open Lean.Meta (checkNotAssigned)
open Lean.Elab.Tactic (Tactic liftMetaTactic)

namespace ClausalExtraction

syntax (name := to_poly) "to_poly" : tactic

@[tactic to_poly] def evalToPoly : Tactic := fun stx => do
  let ctx ← Context.init
  let ctx ← ArithTheory.addArithTheory ctx
  liftMetaTactic fun mvarId => do
    let goal ← mkGoal ctx `to_poly mvarId
    checkNotAssigned mvarId `to_poly
    let r@([goalId]) ← goal.apply
      | throwError "Expected more goals"
    pure r

end ClausalExtraction