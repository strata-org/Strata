/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Transparent procedure assert fires under Execute mode

A transparent single-output procedure whose body contains `assert false`.
Under `.Execute` mode the call goes through the actual body, so the assert
fires. Under `.Verify` mode, `TransparencyPass` would redirect the call to
a `$asFunction` twin with asserts stripped — silently swallowing the failure.

This test pins the harness to `.Execute` mode: if someone accidentally
reverts to `.Verify`, the annotation below stops matching and the build
breaks. -/

#eval testLaurelMultiple <|
#strata
program Laurel;

procedure transparentWithAssert(): int
{
  assert false;
//^^^^^^^^^^^^ error: assertion does not hold
  return 0
};

procedure caller()
  entry
  opaque
{
  var x: int := transparentWithAssert();
  assert x == 0
};
#end
