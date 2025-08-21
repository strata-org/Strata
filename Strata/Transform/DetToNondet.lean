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
def StmtToNondetStmt {P : PureExpr} [Imperative.HasBool P] [Imperative.HasBoolNeg P]
  (st : Imperative.Stmt P (Cmd P)) :
  Imperative.NondetStmt P (Cmd P) :=
  match st with
  | .cmd    cmd => .cmd cmd
  | .block  _ b _ => StmtsToNondetStmt b.ss
  | .ite    cond  thenb elseb md =>
    .choice
      (.seq (.assume "true_cond" cond md) (StmtsToNondetStmt thenb.ss))
      (.seq ((.assume "false_cond" (Imperative.HasBoolNeg.neg cond) md)) (StmtsToNondetStmt elseb.ss))
  | .loop   guard _measure _inv body md =>
    .loop (.seq (.assume "guard" guard md) (StmtsToNondetStmt body.ss))
  | .goto _ _ => (.assume "skip" Imperative.HasBool.tt)
  termination_by (sizeOf st)
  decreasing_by all_goals simp [sizeOf] <;> omega

/-- Deterministic-to-nondeterministic transformation for multiple
(deterministic) statements -/
def StmtsToNondetStmt {P : Imperative.PureExpr} [Imperative.HasBool P] [Imperative.HasBoolNeg P]
  (ss : Imperative.Stmts P (Cmd P)) :
  Imperative.NondetStmt P (Cmd P) :=
  match ss with
  | [] => (.assume "skip" Imperative.HasBool.tt)
  | s :: ss => .seq (StmtToNondetStmt s) (StmtsToNondetStmt ss)
  termination_by (sizeOf ss)
  decreasing_by all_goals simp [sizeOf]; omega
end
