/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.DetToKleene
import Strata.Languages.Core.StatementSemantics
import Strata.Languages.Core.ProgramType
import Strata.Languages.Core.ProgramWF
import Strata.DL.Lambda.IntBoolFactory

open Core

/-! ## Deterministic-to-Kleene Examples -/
section KleeneExamples

open Imperative

def KleeneTest1 : Stmt Expression (Cmd Expression) :=
  .ite (Core.true) [.cmd $ .havoc "x" .empty ] [.cmd $ .havoc "y" .empty ] .empty

def KleeneTest1Ans : KleeneStmt Expression (Cmd Expression) :=
  .choice
    (.seq (.cmd (.assume "true_cond" Core.true .empty)) (.seq (.cmd $ .havoc "x" .empty) (.assume "skip" Imperative.HasBool.tt .empty)))
    (.seq (.cmd (.assume "false_cond" Core.false .empty)) (.seq (.cmd $ .havoc "y" .empty) (.assume "skip" Imperative.HasBool.tt .empty)))


-- #eval toString $ Std.format (StmtToKleeneStmt KleeneTest1)
-- #eval toString $ Std.format KleeneTest1Ans

/-- info: true -/
#guard_msgs in
#eval (toString $ Std.format (StmtToKleeneStmt KleeneTest1)) == (toString $ Std.format KleeneTest1Ans)

end KleeneExamples
