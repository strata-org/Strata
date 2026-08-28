/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
## A nested call in a multi-target assigned call gets its own hidden globals

`GlobalParameterization` intercepts `assign x, y := f(...)` before the traversal reaches
the call, so it is responsible for the arguments too: an argument may itself be a call
that needs hidden globals threaded, and nothing else will reach it. Transforming the
arguments with anything less than the full transform leaves such a call at its source
arity, and the mismatch is reported against the compiler
(`expected 'Heap', got 'Composite'`) rather than the program.

The shape below is the one that detects it, and it is reachable only through `$heap`:
`writes2` has two value outputs and writes a field, `readsField` reads one, and the
resolution guards that reject the equivalent shape over a user global do not apply to a
global synthesized after they run.
-/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var v: int }
procedure readsField(c: C) returns (r: int) { return c#v };
procedure writes2(c: C, n: int) returns (a: int, b: int)
  opaque
  ensures a == 1
  ensures b == 2
  modifies c
{
  c#v := n;
  a := 1;
  b := 2
};
procedure caller(c: C)
  opaque
  modifies c
{
  var x: int := 0;
  var y: int := 0;
  assign x, y := writes2(c, readsField(c));
  assert x == 1
};
#end
