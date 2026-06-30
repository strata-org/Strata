/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the contract pass (`lowerContracts`) respects the lowering mode of
each pre/postcondition, controlled by the `free` and `checked` clause keywords:

  - plain `requires`/`ensures` (mode `Both`)  — lowered to both an assertion
    and an assumption at the natural sites;
  - `free  requires`/`free  ensures` (mode `Assume`) — assumption only;
  - `checked requires`/`checked ensures` (mode `Assert`) — assertion only.

For a precondition the natural assertion site is the call site and the natural
assumption site is the implementation body; for a postcondition the natural
assumption site is the call site (the body assertion of an opaque postcondition
happens later, when ensures clauses are lowered to Core checks). The expected
output below pins which `assume`/`assert` statements appear for each mode.
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.ContractPass
import Strata.Languages.Laurel.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

private def parseAndLower (program : StrataDDM.Program) : IO Program := do
  let laurelProgram ← translateLaurel program
  let result := resolve laurelProgram
  pure (lowerContracts result.program).1

private def printLowered (program : StrataDDM.Program) : IO Unit := do
  let lowered ← parseAndLower program
  for proc in lowered.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## All three modes on both pre- and postconditions

`callee` carries one precondition and one postcondition in each mode; `caller`
invokes it so the call-site checks are generated too. In the lowered output:

  - the body of `callee` assumes the `Both` and `free` preconditions, but not
    the `checked` one (assert-only preconditions are not assumed in the body);
  - `caller` asserts the `Both` and `checked` preconditions before the call,
    but not the `free` one (free preconditions are never checked at call sites);
  - `caller` assumes the `Both` and `free` postconditions after the call, but
    not the `checked` one (assert-only postconditions are not assumed). -/

/--
info: function callee$pre0(x: int)
  returns ($result: bool)
x > 0;
function callee$pre1(x: int)
  returns ($result: bool)
x > 1;
function callee$pre2(x: int)
  returns ($result: bool)
x > 2;
function callee$post0(x: int, r$out: int)
  returns ($result: bool)
r$out > 0;
function callee$post1(x: int, r$out: int)
  returns ($result: bool)
r$out > 1;
function callee$post2(x: int, r$out: int)
  returns ($result: bool)
r$out > 2;
procedure callee(x: int)
  returns (r: int)
  opaque
  ensures r > 0
  free ensures r > 1
  checked ensures r > 2
{
  assume callee$pre0(x);
  assume callee$pre1(x);
  {
    r := x
  }
};
procedure caller()
  returns (r: int)
  opaque
{
  var $cp_0: int := 5;
  assert callee$pre0($cp_0) summary "precondition";
  assert callee$pre2($cp_0) summary "precondition";
  r := callee($cp_0);
  assume callee$post0($cp_0, r);
  assume callee$post1($cp_0, r)
};
-/
#guard_msgs in
#eval printLowered
#strata
program Laurel;
procedure callee(x: int) returns (r: int)
  requires x > 0
  free requires x > 1
  checked requires x > 2
  opaque
  ensures r > 0
  free ensures r > 1
  checked ensures r > 2
{
  r := x
};

procedure caller() returns (r: int)
opaque
{
  r := callee(5)
};
#end

end Strata.Laurel
