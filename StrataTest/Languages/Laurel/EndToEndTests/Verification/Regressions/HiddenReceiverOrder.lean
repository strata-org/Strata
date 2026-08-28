/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
## Hidden receivers precede source receivers in a multi-target assigned call

`GlobalParameterization` threads hidden state — a file-scope global, and `$heap`, which
is one — as an inout parameter, and `transformAssignWithCall` merges the hidden receivers
into a multi-target assignment's existing target list. That order must match the order
the callee's outputs are assembled in:

```
outputs := hidden globals ++ proc.outputs
```

Hidden first, unconditionally; `emitStaticCall` orders its own receivers the same way.
Place a hidden receiver after an explicit-inout receiver instead and the two disagree,
so the receivers bind to the wrong outputs: here `$heap` and `c` swap, giving
`expected '(int, Heap, int)', got '(Heap, int, int)'`.

The mismatch is only loud because `Heap` and `int` differ. Two hidden globals of the same
type as the inout would be assigned each other's values silently, which is why the shape
below — an explicit inout, a field write, and a second output — is worth pinning.

Reachable only through `$heap`: resolution rejects a call to a global-*writing* procedure
that also has an explicit inout output, and those checks run on user source only, before
`$heap` exists.
-/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;

composite Box { var v: int }

// Explicit inout `c` (an output whose name is also an input), hidden `$heap` (the
// field write), and an ordinary output `a`. The call site below therefore has both
// a source-written inout receiver and a hidden receiver to order.
procedure writesFieldAndInout(c: int, bx: Box) returns (c: int, a: int)
  opaque
  ensures c == 7
  ensures a == 1
  modifies bx
{
  bx#v := 100;
  c := 7;
  a := 1
};

procedure callsIt() returns (r: int)
  opaque
  ensures r == 8
{
  var bx: Box := new Box;
  var c: int := 0;
  var a: int := 0;
  assign c, a := writesFieldAndInout(c, bx);
  assert c == 7;
  assert a == 1;
  r := c + a
};
#end
