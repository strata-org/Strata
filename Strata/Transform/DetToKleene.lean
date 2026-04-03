/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.KleeneStmt
public import Strata.Languages.Core.StatementType

/-! # Deterministic-to-Kleene Transformation -/

public section

open Imperative
mutual

/-- Deterministic-to-Kleene transformation for a single
(deterministic) statement -/
def StmtToKleeneStmt {P : PureExpr} [Imperative.HasBool P] [HasNot P]
  (st : Imperative.Stmt P (Cmd P)) :
  Imperative.KleeneStmt P (Cmd P) :=
  match st with
  | .cmd    cmd => .cmd cmd
  | .block  _ bss _ => BlockToKleeneStmt bss
  | .ite    cond tss ess md =>
    .choice
      (.seq (.assume "true_cond" cond md) (BlockToKleeneStmt tss))
      (.seq ((.assume "false_cond" (Imperative.HasNot.not cond) md)) (BlockToKleeneStmt ess))
  | .loop   guard _measure _inv bss md =>
    .loop (.seq (.assume "guard" guard md) (BlockToKleeneStmt bss))
  | .typeDecl _ md => (.assume "skip" Imperative.HasBool.tt md)
  | .exit _ md => (.assume "skip" Imperative.HasBool.tt md)
  | .funcDecl _ md => (.assume "skip" Imperative.HasBool.tt md)

/-- Deterministic-to-Kleene transformation for multiple
(deterministic) statements -/
def BlockToKleeneStmt {P : Imperative.PureExpr} [Imperative.HasBool P] [HasNot P]
  (ss : Imperative.Block P (Cmd P)) :
  Imperative.KleeneStmt P (Cmd P) :=
  match ss with
  | [] => (.assume "skip" Imperative.HasBool.tt .empty)
  | s :: ss => .seq (StmtToKleeneStmt s) (BlockToKleeneStmt ss)
end

end
