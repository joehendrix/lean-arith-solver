import ClausalExtraction.Basic

open Lean
open Std(HashMap)

namespace ClausalExtraction

namespace ConstantTheory

structure State where
  -- Maps expressions to theory variable and cached refl proof.
  exprMap : HashMap Expr TheoryVar := Std.mkHashMap
  values : Array Expr := #[]

def mkRflProof (e:Expr) : MetaM Expr := do
  let tp ← Meta.inferType e
  let lvl : Level ←
        match ← Meta.inferType tp with
        | Expr.sort lvl .. => pure lvl
        | utp => throwError s!"Could not determine level of {utp}"
  pure <| mkAppN (mkConst `rfl [lvl]) #[tp, e]

def exprVar (r:IO.Ref State) (e:Expr) : MetaM TheoryVar := do
  let s ← r.get
  match s.exprMap.find? e with
  | some v =>
    pure v
  | none =>
    let v := TheoryVar.ofNat s.values.size
    r.set { exprMap := s.exprMap.insert e v, values := s.values.push e }
    pure v

def varExpr (r:IO.Ref State) (f : Var → IO Expr) (v:TheoryVar) : IO Expr := do
  pure (←r.get).values[v.toNat]

def predExpr (f : Var → IO Expr) (p:TheoryPred) : IO Expr :=
  panic! "Constant theory has no predicates."


def ops (r:IO.Ref State) : TheoryOps :=
  { varExpr := varExpr r,
    predExpr := predExpr,
    }

end ConstantTheory

end ClausalExtraction