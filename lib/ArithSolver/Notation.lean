import Lean
open Lean

syntax "exprApp[" sepBy1(term, ", ") "]" : term

macro_rules
  | `(exprApp[ $elems,* ]) => do
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
  | `(binRel[ $op, $cl, $lhs, $rhs]) => `(exprApp[ Expr.const $op _ _, _, Expr.const $cl _ _, $lhs, $rhs])