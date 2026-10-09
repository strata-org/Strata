/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! A `return` short-circuits the rest of the body: on the `b` path the
    `assert !b` after the `return` must never be evaluated, so no assertion failure
    fires (no annotation). The `return` sits in a branch so the statements after it
    are reachable on the other path; resolution rejects code after an
    unconditional `return` as dead. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure earlyReturn(b: bool) returns (r: bool)
  opaque
  ensures r == b
{
  if b then {
    return b
  };
  assert !b;
  r := b
};

procedure runEarlyReturn()
  entry
  opaque
{
  var r: bool := earlyReturn(true);
  assert r == true
};
#end
