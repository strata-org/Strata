/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! A postcondition is checked on exit from the procedure that declares it, and a
false one is reported at the `ensures` clause by the verifier and by both
interpreters. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure positive() returns (r: int)
  opaque
  ensures r > 0
//        ^^^^^ error: postcondition does not hold
{
  r := 0
};

procedure main()
  entry
  opaque
{
  var r: int := positive()
};
#end

/-! `old(e)` reads `e` in the state the procedure was entered with, so `bump`'s
postcondition holds only if `old` sees the heap from before the write. The Core
interpreter does not reduce `old` of a field read, so this block runs the verifier
and the Laurel interpreter. -/

#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
composite Counter {
  var n: int
}

procedure bump(c: Counter)
  opaque
  ensures c#n == old(c#n) + 1
  modifies c
{
  c#n := c#n + 1
};

procedure main()
  entry
  opaque
  modifies *
{
  var c: Counter := new Counter;
  c#n := 0;
  bump(c);
  assert c#n == 1
};
#end

/-! `old` is Core's two-state `old`: it reads file-scope globals, as well as the
heap, as they were on entry. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
var g: int := 0

procedure inc()
  opaque
  ensures g == old(g) + 1
{
  g := g + 1
};

procedure main()
  entry
  opaque
{
  inc();
  assert g == 1
};
#end

/-! An object the procedure allocated does not exist in the entry state, so
`old` of a read through it is an error rather than a value. -/

/-- error: `old(...)` reads an object allocated after the procedure was entered [in mk]
-/
#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true } <|
#strata
program Laurel;
composite Counter {
  var n: int
}

procedure mk() returns (c: Counter)
  opaque
  ensures old(c#n) == 0
{
  c := new Counter;
  c#n := 1
};

procedure main()
  entry
  opaque
  modifies *
{
  var c: Counter := mk()
};
#end

/-! `old` of an in-out parameter is its value on entry. The Core interpreter does
not run an in-out call, so this block runs the verifier and the Laurel
interpreter. -/

#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure inc(x: int) returns (x: int)
  opaque
  ensures x == old(x) + 1
{
  x := x + 1
};

procedure main()
  entry
  opaque
{
  var y: int := 4;
  y := inc(y);
  assert y == 5
};
#end

