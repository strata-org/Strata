/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

-- A transparent function with a local variable. Without the inlining pass,
-- the `var x := 3` would reach the Core schema translation and be rejected.
#guard_msgs (drop info) in
#eval testLaurel <|
#strata
program Laurel;
procedure foo(): int
{
  var x: int := 3;
  var y: int := x + 1;
  return y + x
};

procedure caller() opaque {
  var r: int := foo();
  assert r == 7
};
#end
