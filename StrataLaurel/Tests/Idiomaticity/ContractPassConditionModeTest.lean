/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
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
state (where `old(...)` resolves), the body snapshots each input into a `$inputCopy*`
temporary before any mutation and passes the snapshot as the helper's input
argument. The expected output below pins which `assume`/`assert` statements
appear for each mode at each site.

A condition may rely on earlier ones to be well-formed, so each helper assumes
the conditions that precede it: `$pre_i` assumes `requires` clauses `0 … i-1`, and
`$post_i` assumes all the preconditions plus `ensures` clauses `0 … i-1`.
-/

meta import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.ContractPass

open Strata
open StrataTest.Util

namespace Strata.Laurel

/-- Parse, resolve, run `contractPass`, print the lowered program. `prelude := false`:
    `Contracts` lowers every procedure's pre/postconditions into `$pre`/`$post`
    helpers, so with the prelude present the output would gain a `$pre` helper for
    every operator wrapper that has one. The snippets below are therefore written
    with no operators at all — every condition is a plain `bool` parameter or the
    `bool` output — so they resolve without the prelude. -/
private meta def printLowered := runPassForIdiomaticity contractPass (prelude := false)

/-! ## All three modes on both pre- and postconditions

`callee` carries one precondition and one postcondition in each mode; `caller`
invokes it so the call-site checks are generated too. The conditions are bare
`bool` references rather than comparisons, because an operator is a call to a
prelude wrapper and this test runs without the prelude (see `printLowered`); the
postconditions reuse `b` and `c` so that the *mode* is the only thing that
differs between `free requires b` and `free ensures b`, and the golden shows the
two landing at different sites. In the lowered output:

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
info: procedure callee$pre0(a: bool, b: bool, c: bool): bool
{
  $result := a;
  exit $return
}$return;
procedure callee$pre1(a: bool, b: bool, c: bool): bool
{
  assume a;
  $result := b;
  exit $return
}$return;
procedure callee$pre2(a: bool, b: bool, c: bool): bool
{
  assume a;
  assume b;
  $result := c;
  exit $return
}$return;
procedure callee$post0(a: bool, b: bool, c: bool, r$out: bool): bool
{
  assume a;
  assume b;
  assume c;
  $result := r$out;
  exit $return
}$return;
procedure callee$post1(a: bool, b: bool, c: bool, r$out: bool): bool
{
  assume a;
  assume b;
  assume c;
  assume r$out;
  $result := b;
  exit $return
}$return;
procedure callee$post2(a: bool, b: bool, c: bool, r$out: bool): bool
{
  assume a;
  assume b;
  assume c;
  assume r$out;
  assume b;
  $result := c;
  exit $return
}$return;
procedure callee(a: bool, b: bool, c: bool)
  returns (r: bool)
  opaque
{
  var $inputCopy0: bool := a;
  var $inputCopy1: bool := b;
  var $inputCopy2: bool := c;
  assume callee$pre0(a, b, c);
  assume callee$pre1(a, b, c);
  {
    r := a
  };
  assert callee$post0($inputCopy0, $inputCopy1, $inputCopy2, r) summary "postcondition";
  assert callee$post2($inputCopy0, $inputCopy1, $inputCopy2, r) summary "postcondition"
};
procedure caller()
  returns (r: bool)
  opaque
{
  var $inputCopy3: bool := true;
  var $inputCopy4: bool := true;
  var $inputCopy5: bool := true;
  assert callee$pre0($inputCopy3, $inputCopy4, $inputCopy5) summary "precondition";
  assert callee$pre2($inputCopy3, $inputCopy4, $inputCopy5) summary "precondition";
  r := callee($inputCopy3, $inputCopy4, $inputCopy5);
  assume callee$post0($inputCopy3, $inputCopy4, $inputCopy5, r);
  assume callee$post1($inputCopy3, $inputCopy4, $inputCopy5, r)
};
-/
#guard_msgs in
#eval printLowered <|
#strata
program Laurel;
procedure callee(a: bool, b: bool, c: bool) returns (r: bool)
  requires a
  free requires b
  checked requires c
  opaque
  ensures r
  free ensures b
  checked ensures c
{
  r := a
};

procedure caller() returns (r: bool)
opaque
{
  r := callee(true, true, true)
};
#end

end Strata.Laurel
