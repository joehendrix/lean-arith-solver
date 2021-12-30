import ArithSolver.ArithM
import ArithSolver.Notation
import Lean

open Lean
open Lean.Meta
open Lean.Elab.Tactic

namespace ArithSolver

private def natExpr : Expr := mkConst ``Nat
private def intExpr : Expr := mkConst ``Int
private def ofNatExpr : Expr := mkConst ``Int.ofNat
private def intNonNegMkExpr : Expr := mkConst ``Int.NonNeg.mk
private def propExpr : Expr := mkSort levelZero

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

-- | An assumption in the goal
structure Assumption where
  -- The property we can assume
  prop : Expr
  -- An expression referencing the input proof.
  proof : Expr

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
    let g ← mkFreshExprSyntheticOpaqueMVar falseExpr tag
    -- Turn goal into lambda with free variables from assertions
    let fn ← Meta.mkLambdaFVars fvars g
    -- Assign goal
    assignExprMVar goalId (mkAppN fn s.proofs)
    pure [g.mvarId!]

def Goal.onVerify (g:Goal) (goalId:MVarId) (s:State) (goalProof:Expr) : MetaM Unit := do
  assignExprMVar goalId (g.onMkProof goalProof)

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

theorem mul_zero_lhs_poly_lemma {m y a:Int} : a + m*(0*y) = a := sorry
theorem mul_zero_rhs_poly_lemma (m x a:Int): a + m*(x*0) = a := sorry

theorem mul_lhs_poly_lemma {m x y a b:Int} (g: a + (m*x)*y = b) : a + m*(x*y) = b := sorry
theorem mul_rhs_poly_lemma {m x y a b:Int} (g: a + (m*y)*x = b) : a + m*(x*y) = b := sorry

-- | @appendAddExpr poly m e@ returns poly equivalent to `poly + m*e` along with proof that that
-- poly.expr + m*e = ret.expr
partial def appendAddExprFromInt (m:Int) (m_ne:m ≠ 0) (e:Expr) (poly:Poly)
   : ArithM (Poly × Expr) := do

  match ← matchIntLit e with
  | none => pure ()
  | some x =>
    let r ←
      if x_ne : x = 0 then
        let aexpr ← polyExpr poly
        let pr := mkAppN (mkConst ``rfl [levelOne]) #[intExpr, aexpr]
        pure (poly, pr)
      else
        let y := m * x
        -- p + m * x * 1 = return
        let pr ← polyAddProof poly y (mul_ne_zero m_ne x_ne) Var.one
        pure (poly.add y Var.one, pr)
    return r

  -- Match add
  match ← matchBinOp intAddConst intExpr e with
  | none => pure ()
  | some (x, y) => do
    let aexpr ← polyExpr poly
    let (poly, x_pr) ← appendAddExprFromInt m m_ne x poly
    let bexpr ← polyExpr poly
    let (poly, y_pr) ← appendAddExprFromInt m m_ne y poly
    let cexpr ← polyExpr poly
    let pr := mkAppN (mkConst ``add_poly_lemma) #[m, x, y, aexpr, bexpr, cexpr, x_pr, y_pr]
    return (poly, pr)

  -- Match sub
--  let subExpr := mkAppN (mkConst ``Sub.sub [levelZero]) #[intExpr, mkConst ``Int.instSubInt]
--  let subExpr := mkConst ``Int.sub
  match ← matchBinOp intSubConst intExpr e with
  | none =>
    pure ()
  | some (x, y) => do
    let aexpr ← polyExpr poly
    let (poly, x_pr) ← appendAddExprFromInt m m_ne x poly
    let bexpr ← polyExpr poly
    let (poly, y_pr) ← appendAddExprFromInt (- m) (neg_ne_zero m_ne) y poly
    let cexpr ← polyExpr poly
    let pr := mkAppN (mkConst ``sub_poly_lemma) #[m, x, y, aexpr, bexpr, cexpr, x_pr, y_pr]
    return (poly, pr)

  -- Match negation
  let negExpr := mkAppN (mkConst ``Neg.neg [levelZero]) #[intExpr, mkConst ``Int.instNegInt]
  match ← matchUnaryOp negExpr intExpr e with
  | none => pure ()
  | some x => do
    let aexpr ← polyExpr poly
    let (poly, x_pr) ← appendAddExprFromInt (-m) (neg_ne_zero m_ne) x poly
    let bexpr ← polyExpr poly
    let pr := mkAppN (mkConst ``neg_poly_lemma) #[m, x, aexpr, bexpr, x_pr]
    return (poly, pr)

  -- Match scalar multiplication
  match ← matchBinOp intMulConst intExpr e with
  | none => pure ()
  | some (x, y) => do
    let aexpr ← polyExpr poly
    match ← matchIntLit x with
    | none =>
      pure ()
    | some xn =>
      let r ←
        if xn_ne:xn = 0 then
          let pr := mkAppN (mkConst ``mul_zero_lhs_poly_lemma) #[m, y, aexpr]
          -- aexpr + m*(0*y) = aexpr
          pure (poly, pr)
        else
          -- y_eq: aexpr + (m*x)*y = poly'.expr
          let (poly, y_eq) ← appendAddExprFromInt (m * xn) (mul_ne_zero m_ne xn_ne) y poly
          let bexpr ← polyExpr poly
          let pr := mkAppN (mkConst `mul_lhs_poly_lemma) #[m, x, y, aexpr, bexpr]
          pure (poly, pr)
      return r
    match ← matchIntLit y with
    | none =>
      pure ()
    | some yn =>
      let r ←
        if n_ne:yn = 0 then
          let pr := mkAppN (mkConst ``mul_zero_rhs_poly_lemma) #[m, x, aexpr]
          pure (poly, pr)
        else
          let (p, x_eq) ← appendAddExprFromInt (m * yn) (mul_ne_zero m_ne n_ne) x poly
          let bexpr ← polyExpr poly
          let pr := mkAppN (mkConst `mul_rhs_poly_lemma) #[m, x, y, aexpr, bexpr]
          pure (poly, pr)
      return r
    pure ()

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
  let e ← instantiateMVars e
  let (p,pr) ← appendAddExprFromInt 1 one_ne e Poly.zero
  -- pr  has type" 0 + 1 * e = p.expr"
  match p with
  | ⟨#[(1, v)]⟩ => do
    -- Make pr have type e = v
    let pr := mkAppN (mkConst ``purifyIntLemmaVar) #[e, ← varExpr v, pr]
    pure (v, pr)
  | otherwise => do
    let v ← getPolyVar p
    -- Make pr have type e = v
    let pr := mkAppN (mkConst ``purifyIntLemmaPoly) #[e, ← polyExpr p, pr]
    pure (v, pr)

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
    let fvar ← mkFreshFVarId
    processAssumptionProp none `negGoal (mkFVar fvar) prop
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
  -- Create verification
  pure $ {
      onMkProof := fun goalProof =>
        mkApp decideByContraExpr (mkLambda Name.anonymous BinderInfo.default prop goalProof)
      }

syntax (name := zify) "zify" : tactic

 --OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)

@[tactic zify] def evalZify : Tactic := fun stx => do
  liftMetaTactic fun mvarId => do
    checkNotAssigned mvarId `zify
    let (goal, s) ← (negateArithGoal `zify mvarId).run
    let r@([goalId]) ← goal.onAddAssumptions mvarId s
      | throwError "Expected more goals"
    pure r

end ArithSolver

-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a))
def test_false_goal (a b : Nat) (p:False) : False := by
  zify
  exact p

-- (p : Int.NonNeg (Int.ofNat b - Int.ofNat a))
def test_nonneg_assumption (x y : Int) (p : Int.NonNeg (x + y)) (q: False) : False := by
  zify
  exact q

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