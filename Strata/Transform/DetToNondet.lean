/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.NondetStmt
public import Strata.Languages.Core.StatementType

/-! # Deterministic-to-Nondeterministic Transformation

Returns `none` if the input contains `.exit`, `.funcDecl`, or `.typeDecl`
statements, which have no nondeterministic counterpart. -/

public section

open Imperative
mutual

/-- Deterministic-to-nondeterministic transformation for a single statement.
    Returns `none` for unsupported constructs. -/
def StmtToNondetStmt {P : PureExpr} [Imperative.HasBool P] [HasNot P]
  (st : Imperative.Stmt P (Cmd P)) :
  Option (Imperative.NondetStmt P (Cmd P)) :=
  match st with
  | .cmd cmd => some (.cmd cmd)
  | .block _ bss _ => BlockToNondetStmt bss
  | .ite cond tss ess md => do
    let t ← BlockToNondetStmt tss
    let e ← BlockToNondetStmt ess
    return .choice
      (.seq (.assume "true_cond" cond md) t)
      (.seq (.assume "false_cond" (Imperative.HasNot.not cond) md) e)
  | .loop guard _measure _inv bss md => do
    let b ← BlockToNondetStmt bss
    return .loop (.seq (.assume "guard" guard md) b)
  | .typeDecl _ _ => none
  | .exit _ _ => none
  | .funcDecl _ _ => none

/-- Deterministic-to-nondeterministic transformation for a block.
    Returns `none` if any statement is unsupported. -/
def BlockToNondetStmt {P : Imperative.PureExpr} [Imperative.HasBool P] [HasNot P]
  (ss : Imperative.Block P (Cmd P)) :
  Option (Imperative.NondetStmt P (Cmd P)) :=
  match ss with
  | [] => some (.assert "$__skip" Imperative.HasBool.tt .empty)
  | s :: ss => do
    let s' ← StmtToNondetStmt s
    let rest ← BlockToNondetStmt ss
    return .seq s' rest
end

end
