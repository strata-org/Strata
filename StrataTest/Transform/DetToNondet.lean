/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.DetToNondet
import Strata.Languages.Core.StatementSemantics
import Strata.Languages.Core.ProgramType
import Strata.Languages.Core.ProgramWF
import Strata.DL.Lambda.IntBoolFactory

open Core

/-! ## Deterministic-to-Nondeterministic Examples -/
section NondetExamples

open Imperative

def NondetTest1 : Stmt Expression (Cmd Expression) :=
  .ite (.det Core.true) [.cmd $ .set "x" .nondet .empty ] [.cmd $ .set "y" .nondet .empty ] .empty

def NondetTest1Ans : Option (NondetStmt Expression (Cmd Expression)) :=
  .some (.choice
    (.seq (.cmd (.assume "true_cond" Core.true .empty)) (.seq (.cmd $ .set "x" .nondet .empty) (.assert "$__skip" Imperative.HasBool.tt .empty)))
    (.seq (.cmd (.assume "false_cond" Core.false .empty)) (.seq (.cmd $ .set "y" .nondet .empty) (.assert "$__skip" Imperative.HasBool.tt .empty))))

-- #eval toString $ Std.format (StmtToNondetStmt NondetTest1)
-- #eval toString $ Std.format NondetTest1Ans

/-- info: true -/
#guard_msgs in
#eval (toString $ Std.format (StmtToNondetStmt NondetTest1)) == (toString $ Std.format NondetTest1Ans)

end NondetExamples
