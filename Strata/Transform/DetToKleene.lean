/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.KleeneStmt

/-! # Deterministic-to-Kleene Transformation

Returns `none` if the input contains `.exit`, `.funcDecl`, or `.typeDecl`
statements, which have no Kleene counterpart. -/

public section

open Imperative
mutual

/-- Deterministic-to-Kleene transformation for a single statement.
    Returns `none` for unsupported constructs. -/
def StmtToKleeneStmt {P : PureExpr} [Imperative.HasBool P] [HasNot P]
  (st : Imperative.Stmt P (Cmd P)) :
  Option (Imperative.KleeneStmt P (Cmd P)) :=
  match st with
  | .cmd cmd => some (.cmd cmd)
  | .block _ bss _ => BlockToKleeneStmt bss
  | .ite cond tss ess md => do
    let t ← BlockToKleeneStmt tss
    let e ← BlockToKleeneStmt ess
    match cond with
    | .det c =>
      return .choice
        (.seq (.assume "true_cond" c md) t)
        (.seq (.assume "false_cond" (Imperative.HasNot.not c) md) e)
    | .nondet =>
      return .choice t e
  | .loop guard _measure _inv bss md => do
    let b ← BlockToKleeneStmt bss
    match guard with
    | .det g => return .loop (.seq (.assume "guard" g md) b)
    | .nondet => return .loop b
  | .typeDecl _ _ => none
  | .exit _ _ => none
  | .funcDecl _ _ => none

/-- Deterministic-to-Kleene transformation for a block.
    Returns `none` if any statement is unsupported. -/
def BlockToKleeneStmt {P : Imperative.PureExpr} [Imperative.HasBool P] [HasNot P]
  (ss : Imperative.Block P (Cmd P)) :
  Option (Imperative.KleeneStmt P (Cmd P)) :=
  match ss with
  | [] => some (.assert "$__skip" Imperative.HasBool.tt .empty)
  | s :: ss => do
    let s' ← StmtToKleeneStmt s
    let rest ← BlockToKleeneStmt ss
    return .seq s' rest
end

end
