/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.NondetStmt
public import Strata.Languages.Core.StatementType

/-! # Deterministic-to-Nondeterministic Transformation -/

public section

open Imperative
mutual

/-- Deterministic-to-nondeterministic transformation for a single
(deterministic) statement -/
def StmtToNondetStmt {P : PureExpr} [Imperative.HasBool P] [HasNot P]
  (st : Imperative.Stmt P (Cmd P)) :
  Imperative.NondetStmt P (Cmd P) :=
  match st with
  | .cmd    cmd => .cmd cmd
  | .block  _ bss _ => BlockToNondetStmt bss
  | .ite    cond tss ess md =>
    match cond with
    | .det c =>
      .choice
        (.seq (.assume "true_cond" c md) (BlockToNondetStmt tss))
        (.seq ((.assume "false_cond" (Imperative.HasNot.not c) md)) (BlockToNondetStmt ess))
    | .nondet =>
      .choice (BlockToNondetStmt tss) (BlockToNondetStmt ess)
  | .loop   guard _measure _inv bss md =>
    match guard with
    | .det g => .loop (.seq (.assume "guard" g md) (BlockToNondetStmt bss))
    | .nondet => .loop (BlockToNondetStmt bss)
  | .typeDecl _ md => (.assume "skip" Imperative.HasBool.tt md)
  | .exit _ md => (.assume "skip" Imperative.HasBool.tt md)
  | .funcDecl _ md => (.assume "skip" Imperative.HasBool.tt md)

/-- Deterministic-to-nondeterministic transformation for multiple
(deterministic) statements -/
def BlockToNondetStmt {P : Imperative.PureExpr} [Imperative.HasBool P] [HasNot P]
  (ss : Imperative.Block P (Cmd P)) :
  Imperative.NondetStmt P (Cmd P) :=
  match ss with
  | [] => (.assume "skip" Imperative.HasBool.tt .empty)
  | s :: ss => .seq (StmtToNondetStmt s) (BlockToNondetStmt ss)
end

end
