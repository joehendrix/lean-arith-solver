import ArithSolver.Basic

open Lean
open Std(HashMap)

namespace ArithSolver

namespace ConstantTheory

structure State where
  -- Maps expressions to theory variable and cached refl proof.
  exprMap : HashMap Expr (TheoryVar × Expr) := Std.mkHashMap
  values : Array Expr := #[]

def exprVar (r:IO.Ref State) (e:Expr) : MetaM (ExprEvalResult TheoryVar) := do
  let s ← r.get
  match s.exprMap.find? e with
  | none => pure ()
  | some (v,pr) =>
    return { var := v, varExpr := e , eq := pr }
  let v := TheoryVar.ofNat s.values.size
  let tp ← Meta.inferType e
  let lvl : Level ←
        match ← Meta.inferType tp with
        | Expr.sort lvl .. => pure lvl
        | utp => throwError s!"Could not determine level of {utp}"
  let pr : Expr := mkAppN (mkConst `rfl [lvl]) #[tp, e]
  r.set { exprMap := s.exprMap.insert e (v, pr), values := s.values.push e }
  return { var := v, varExpr := e, eq := pr }

def varExpr (r:IO.Ref State) (f : Var → IO Expr) (v:TheoryVar) : IO Expr := do
  pure (←r.get).values[v.toNat]

def predExpr (f : Var → IO Expr) (p:TheoryPred) : IO Expr :=
  panic! "Constant theory has no predicates."


def ops (r:IO.Ref State) : TheoryOps :=
  { varExpr := varExpr r,
    predExpr := predExpr,
    exprVar := fun e => exprVar r e
    }

end ConstantTheory

end ArithSolver