/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
meta import Strata.Transform.DetToKleene
meta import Strata.Languages.Core.StatementSemantics
meta import Strata.Languages.Core.ProgramType
meta import Strata.Languages.Core.ProgramWF
meta import Strata.DL.Lambda.IntBoolFactory


meta section

open Core

/-! ## Deterministic-to-Kleene Examples -/
section KleeneExamples

open Imperative

def KleeneTest1 : Stmt Expression (Cmd Expression) :=
  .ite (.det Core.true) [.cmd $ .set "x" .nondet .empty ] [.cmd $ .set "y" .nondet .empty ] .empty

def KleeneTest1Ans : Option (KleeneStmt Expression (Cmd Expression)) :=
  .some (.choice
    (.seq (.cmd (.assume "true_cond" Core.true .empty)) (.seq (.cmd $ .set "x" .nondet .empty) (.assert "$__skip" Imperative.HasBool.tt .empty)))
    (.seq (.cmd (.assume "false_cond" Core.false .empty)) (.seq (.cmd $ .set "y" .nondet .empty) (.assert "$__skip" Imperative.HasBool.tt .empty))))

-- #eval toString $ Std.format (StmtToKleeneStmt KleeneTest1)
-- #eval toString $ Std.format KleeneTest1Ans

/-- info: true -/
#guard_msgs in
#eval (toString $ Std.format (StmtToKleeneStmt KleeneTest1)) == (toString $ Std.format KleeneTest1Ans)

end KleeneExamples
