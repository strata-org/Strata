/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! A `return` short-circuits the rest of the body: the `assert false == true`
    after the `return` must never be evaluated, so no assertion failure fires on
    either interpreter (no annotation).

    Only the standalone Laurel interpreter runs this. Both verification and the
    Laurel→Core interpret path statically reject `assert false == true` as `dead
    code after 'return'` (verify as a diagnostic, translate as a hard error), a
    static check the runtime never reaches — so this test, which is about the
    interpreter's runtime short-circuiting, runs the Laurel interpreter only.

    Verification would fail here: it statically flags the `assert false == true`
    after the `return` as a `dead code after 'return'` diagnostic, which has no
    matching annotation in this file and so is why `skipVerification := true`. -/

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := false } <|
#strata
program Laurel;
procedure earlyReturn(b: bool) returns (r: bool)
  opaque
{
  return b;
  assert false == true
};

procedure runEarlyReturn()
  entry
  opaque
{
  var r: bool := earlyReturn(true);
  assert r == true
};
#end
