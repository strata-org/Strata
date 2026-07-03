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
assumption site is the implementation body. For a postcondition the natural
assumption site is the call site and the natural assertion site is the end of
the implementation body. The contract pass fully lowers both: it removes the
`requires`/`ensures` clauses from the procedure and replaces them with explicit
assumptions and assertions (through generated `$pre`/`$post` helper functions),
so no `ensures` clause survives on a procedure with an implementation.

Because a postcondition's helper reads the procedure's inputs in their entry
state (where `old(...)` resolves), the body snapshots each input into a `$cp_*`
temporary before any mutation and passes the snapshot as the helper's input
argument. The expected output below pins which `assume`/`assert` statements
appear for each mode at each site.
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
  pure (lowerContracts result.program)

private def printLowered (program : StrataDDM.Program) : IO Unit := do
  let lowered ← parseAndLower program
  for proc in lowered.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## All three modes on both pre- and postconditions

`callee` carries one precondition and one postcondition in each mode; `caller`
invokes it so the call-site checks are generated too. In the lowered output:

  - the body of `callee` assumes the `Both` and `free` preconditions, but not
    the `checked` one (assert-only preconditions are not assumed in the body);
  - the body of `callee` asserts the `Both` and `checked` postconditions at the
    end, but not the `free` one (assume-only postconditions are not checked) —
    and no `ensures` clause remains on `callee`;
  - `caller` asserts the `Both` and `checked` preconditions before the call,
    but not the `free` one (free preconditions are never checked at call sites);
  - `caller` assumes the `Both` and `free` postconditions after the call, but
    not the `checked` one (assert-only postconditions are not assumed). -/

/--
info: procedure callee$pre0(x: int)
  returns ($result: bool)
{
  $result := x > 0;
  exit $return
}$return;
procedure callee$pre1(x: int)
  returns ($result: bool)
{
  $result := x > 1;
  exit $return
}$return;
procedure callee$pre2(x: int)
  returns ($result: bool)
{
  $result := x > 2;
  exit $return
}$return;
procedure callee$post0(x: int, r$out: int)
  returns ($result: bool)
{
  assume x > 0;
  assume x > 1;
  assume x > 2;
  $result := r$out > 0;
  exit $return
}$return;
procedure callee$post1(x: int, r$out: int)
  returns ($result: bool)
{
  assume x > 0;
  assume x > 1;
  assume x > 2;
  $result := r$out > 1;
  exit $return
}$return;
procedure callee$post2(x: int, r$out: int)
  returns ($result: bool)
{
  assume x > 0;
  assume x > 1;
  assume x > 2;
  $result := r$out > 2;
  exit $return
}$return;
procedure callee(x: int)
  returns (r: int)
  opaque
{
  var $cp_0: int := x;
  assume callee$pre0(x);
  assume callee$pre1(x);
  {
    r := x
  };
  assert callee$post0($cp_0, r) summary "postcondition";
  assert callee$post2($cp_0, r) summary "postcondition"
};
procedure caller()
  returns (r: int)
  opaque
{
  var $cp_1: int := 5;
  assert callee$pre0($cp_1) summary "precondition";
  assert callee$pre2($cp_1) summary "precondition";
  r := callee($cp_1);
  assume callee$post0($cp_1, r);
  assume callee$post1($cp_1, r)
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
