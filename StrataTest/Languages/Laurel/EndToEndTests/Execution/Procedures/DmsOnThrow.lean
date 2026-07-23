/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Regression: collected assertion failures surface in non-assertion errors

When a guard-assert (precondition check) fails and is collected via
`continuePastAssert`, a subsequent stuck expression triggers a non-assertion
error. The thrown message must include the collected assertion failure(s) so the
root cause is visible — not just the secondary stuck-expression error.

This exercises the `dms`-on-throw branch in `runLaurelInterpretCore`. -/

private def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

#eval do
  let block : StrataDDM.SourcedProgram :=
    #strata
    program Laurel;
    procedure pureDiv(x: int, y: int): int
      requires y != 0
    {
      return x / y
    };

    procedure root() entry opaque {
      var z: int := pureDiv(10, 0);
    //^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
      assert z == 5
    //^^^^^^^^^^^^^ error: assertion does not hold
    };
    #end
  try
    testLaurelMultiple block
  catch e =>
    let msg := toString e
    unless hasSubstr msg "raised a non-assertion error" do
      throw <| IO.userError s!"expected 'raised a non-assertion error' in:\n{msg}"
    unless hasSubstr msg "collected assertion failures before the error:" do
      throw <| IO.userError s!"expected 'collected assertion failures' in:\n{msg}"
    unless hasSubstr msg "precondition does not hold" do
      throw <| IO.userError s!"expected 'precondition does not hold' in:\n{msg}"
