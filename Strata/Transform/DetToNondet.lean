/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.NondetStmt
import Strata.Languages.Boogie.StatementType

/-! # Deterministic-to-Nondeterministic Transformation -/

open Imperative
mutual

/-- Deterministic-to-nondeterministic transformation for a single
(deterministic) statement -/
def StmtToNondetStmt {P : PureExpr} [Imperative.HasBool P] [HasNot P]
  (st : Imperative.Stmt P (Cmd P)) :
  Imperative.NondetStmt P (Cmd P) :=
  match st with
  | .cmd    cmd => .cmd cmd
  | .block  _ ⟨ bss ⟩ _ => StmtsToNondetStmt bss
  | .ite    cond ⟨ tss ⟩ ⟨ ess ⟩ md =>
    .choice
      (.seq (.assume "true_cond" cond md) (StmtsToNondetStmt tss))
      (.seq ((.assume "false_cond" (Imperative.HasNot.not cond) md)) (StmtsToNondetStmt ess))
  | .loop   guard _measure _inv ⟨ bss ⟩ md =>
    .loop (.seq (.assume "guard" guard md) (StmtsToNondetStmt bss))
  | .goto _ _ => (.assume "skip" Imperative.HasBool.tt)

/-- Deterministic-to-nondeterministic transformation for multiple
(deterministic) statements -/
def StmtsToNondetStmt {P : Imperative.PureExpr} [Imperative.HasBool P] [HasNot P]
  (ss : Imperative.Stmts P (Cmd P)) :
  Imperative.NondetStmt P (Cmd P) :=
  match ss with
  | [] => (.assume "skip" Imperative.HasBool.tt)
  | s :: ss => .seq (StmtToNondetStmt s) (StmtsToNondetStmt ss)
end
