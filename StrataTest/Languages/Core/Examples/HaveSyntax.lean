/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
---------------------------------------------------------------------
open Strata
open StrataDDM (Program)

/-!
# `have` concrete-syntax test

Exercises the Core DDM `have x : T = v in body` binding syntax, which desugars
(via `LExpr.mkHave`) to the abstraction application `(fun x : T => body) v`.
Covers a single binding and a nested one.
-/

private def havePgm : Program :=
#strata
program Core;

procedure TestHave()
spec {
  ensures true;
}
{
  assert [single]: have x : int = 1 in x + x == 2;
  assert [nested]: have x : int = 1 in have y : int = 2 in x + y == 3;
};
#end

/--
info: true
-/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram havePgm) |>.snd |>.isEmpty

/--
info:
Obligation: single
Property: assert
Result: ✅ pass

Obligation: nested
Property: assert
Result: ✅ pass

Obligation: TestHave_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify havePgm (options := .quiet)

end
