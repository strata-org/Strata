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
  .ite (Core.true) [.cmd $ .havoc "x" ] [.cmd $ .havoc "y" ]

def NondetTest1Ans : NondetStmt Expression (Cmd Expression) :=
  .choice
    (.seq (.cmd (.assume "true_cond" Core.true)) (.seq (.cmd $ .havoc "x") (.assume "skip" Imperative.HasBool.tt)))
    (.seq (.cmd (.assume "false_cond" Core.false)) (.seq (.cmd $ .havoc "y") (.assume "skip" Imperative.HasBool.tt)))


-- #eval toString $ Std.format (StmtToNondetStmt NondetTest1)
-- #eval toString $ Std.format NondetTest1Ans

/-- info: true -/
#guard_msgs in
#eval (toString $ Std.format (StmtToNondetStmt NondetTest1)) == (toString $ Std.format NondetTest1Ans)

end NondetExamples
