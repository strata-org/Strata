/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Correct heap mutating value return -/

#eval testLaurelExecution {}
#strata
program Laurel;
composite Container {
  var value: int
}

procedure setAndReturn(c: Container, x: int) returns (r: int)
  opaque
  ensures r == x
  modifies c
{
  c#value := x;
  return x
};
#end

/-! ## Buggy: postcondition r == x + 1 cannot hold when r := x -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Container {
  var value: int
}

procedure setAndReturnBuggy(c: Container, x: int) returns (r: int)
  opaque
  ensures r == x + 1
//        ^^^^^^^^^^ error: postcondition could not be proved
  modifies c
{
  c#value := x;
  return x
};
#end

/-! ## The short `: T` return form, with a heap `modifies`

The two cases above use the explicit `returns (r: T)` form. The short `: T` form is
the same program, but its value output is named `$result` — also the spelling
`EliminateExceptions` prefers for the `Result` carrier it injects into a *throwing*
procedure. A throwing procedure's normal frame is guarded with
`Result..isGood(<carrier>)`, so inferring "this procedure throws" from that name
would misread these procedures, which do not throw and carry no `Result`: their
frame would be guarded by a `Result..isGood` that does not resolve, surfacing as
`'Result..isGood' is not defined`.

A heap `modifies` is what makes `ModifiesClauses` build a frame at all, so it is
required to reach that misfire — hence these live here, with the rest of the
heap-mutating value returns, rather than with the exception tests. Nothing here
mentions exceptions; that is the point. The `isGood` guard exists only where
`EliminateExceptions` attached it — on the modifies groups of a procedure it
actually lowered — so a procedure the pass never touched is not mistaken for one
it did.

Note the clause order: `ensures` must precede `modifies`, or it is a parse error
rather than a test of any of this. -/

#eval testLaurelExecution {}
#strata
program Laurel;

composite Container {
  var value: int
}

procedure shortFormSetAndReturn(c: Container, x: int): int
  opaque
  ensures $result == x
  modifies c
{
  c#value := x;
  return x
};
#end

/-! ## The short form returning a *user* datatype named `Result`

A program that uses no exceptions may declare its own type named `Result` — only an
exception-using one has the name reserved (`validateExceptionLowerability`). So the
output's *type* is no more evidence of the lowering than its name is: `bump` below has
an output named `$result` *and* typed `Result<…>`, and still nothing here throws. This
exercises the recorded-carrier path rather than either signature test.

The constructors are deliberately `Good`/`Bad`, so `Result..isGood` genuinely resolves
in this program. That makes a misfire here *silent* rather than a loud internal error:
the frame would be built, well-formed, and merely guarded by `Result..isGood($result)`.
Since `bump` returns `Bad`, that guard is false and the frame collapses to nothing, so
a caller cannot conclude that `other`, which `bump` never names in its `modifies`, kept
its value. The assertion below is the observable consequence, and it needs a *caller*
to expose it; the frame is what one procedure promises another.

The assertion must hold. The caller allocates both objects with `new` rather than
taking them as parameters, so they are provably distinct — two parameters of the same
type may alias, which would make the assertion unprovable for a reason unrelated to
the frame. -/

#eval testLaurelExecution {}
#strata
program Laurel;

composite Container {
  var value: int
}

datatype Result<Val, Err> {
  Good(value: Val),
  Bad(err: Err)
}

procedure bump(c: Container): Result<int, bool>
  opaque
  modifies c
{
  c#value := 1;
  return Bad(true)
};

procedure bumpCaller()
  opaque
{
  var c: Container := new Container;
  var other: Container := new Container;
  var seen: int := other#value;
  var r: Result<int, bool> := bump(c);
  // `bump` may change only `c`, so `other` is untouched across the call.
  assert other#value == seen
};
#end
