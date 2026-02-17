/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.CmdEval

/-! ## Tests for CmdEval -/

namespace Core
open Lambda Imperative
open Std (ToFormat Format format)
open LExpr.SyntaxMono LTy.Syntax Core.Syntax

private def testProgram1 : Cmds Expression :=
  [.init "x" t[int] eb[#0],
   .set "x" eb[#10],
   .assert "x_value_eq" eb[x == #10]]

/--
error: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-/
#guard_msgs in
#eval format $ Imperative.Cmds.eval (Env.init (empty_factory := true)) testProgram1

private def testProgram2 : Cmds Expression :=
  [.init "x" t[int] eb[(y : int)],
   .assert "x_eq_12" eb[x == #12]]

/--
error: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.
-/
#guard_msgs in
#eval format $ Imperative.Cmds.eval (Env.init (empty_factory := true)) testProgram2

end Core
