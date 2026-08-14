/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! A heap-writing call as an argument to a heap-reading call: `peek` samples
    the heap after `bump` ran, so it sees 1 while receiving bump's return 0. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Counter {
  var value: int
}
procedure bump(c: Counter) returns (r: int)
  opaque
  ensures c#value == old(c#value) + 1
  ensures r == old(c#value)
  modifies c
{
  c#value := c#value + 1;
  return c#value - 1
};
procedure peek(c: Counter, x: int) returns (r: int)
  opaque
  ensures r == c#value * 10 + x;
procedure evaluationOrder(c: Counter)
  opaque
  modifies c
{
  c#value := 0;
  var got: int := peek(c, bump(c));
  assert got == 10;
  assert c#value == 1
};
#end

/-! An effectful cast target is captured once, then reused for the type check and
    result. Evaluating `makeBase` twice would increment `counter#value` twice. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Base {
}
composite Counter {
  var value: int
}
procedure makeBase(counter: Counter) returns (r: Base)
  opaque
  ensures counter#value == old(counter#value) + 1
  ensures r is Base
  modifies counter
{
  counter#value := counter#value + 1;
  return new Base
};
procedure castOnce(counter: Counter)
  opaque
  modifies counter
{
  counter#value := 0;
  var result: Base := makeBase(counter) as Base;
  assert result is Base;
  assert counter#value == 1
};
#end
