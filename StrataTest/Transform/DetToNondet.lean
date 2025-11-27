/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.DetToNondet
import Strata.Languages.Boogie.StatementSemantics
import Strata.Languages.Boogie.ProgramType
import Strata.Languages.Boogie.ProgramWF
import Strata.DL.Lambda.IntBoolFactory

open Boogie

/-! ## Deterministic-to-Nondeterministic Examples -/
section NondetExamples

open Imperative

def NondetTest1 : Stmt Expression (Cmd Expression) :=
  .ite (Boogie.true) {ss :=
    [.cmd $ .havoc "x" ]
    } {ss :=
    [.cmd $ .havoc "y" ]
    }

def NondetTest1Ans : NondetStmt Expression (Cmd Expression) :=
  .choice
    (.seq (.cmd (.assume "true_cond" Boogie.true)) (.seq (.cmd $ .havoc "x") (.assume "skip" Imperative.HasBool.tt)))
    (.seq (.cmd (.assume "false_cond" Boogie.false)) (.seq (.cmd $ .havoc "y") (.assume "skip" Imperative.HasBool.tt)))


-- #eval toString $ Std.format (StmtToNondetStmt NondetTest1)
-- #eval toString $ Std.format NondetTest1Ans

/-- info: true -/
#guard_msgs in
#eval (toString $ Std.format (StmtToNondetStmt NondetTest1)) == (toString $ Std.format NondetTest1Ans)

end NondetExamples
