/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Allocation vs. the per-yield environment havoc.

  * **Positive (fresh-after-yield):** the yield havoc assumes the
    allocation counter is monotone (the env allocates but never
    deallocates), so an object allocated *after* a yield is provably
    distinct from references held *before* it — writing the fresh
    object cannot clobber rely-preserved state.

  * **Negative (private allocation):** an object allocated *before* a
    yield is still clobbered by the havoc, even though it never escapes
    to the environment. Framing unescaped allocations requires an
    escape/reachability discipline that v1 does not have; relies cannot
    express it either (body locals are not in scope in a rely clause).
    This pins the known incompleteness.
-/

import StrataTest.Languages.Laurel.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util.Concurrency

/-! ## Positive: fresh allocation after a yield cannot alias pre-yield state. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine freshAfterYield(s: Cell)
  relies old(s#x) == s#x
  modifies *
{
  s#x := 5;
  yield;
  var b: Cell := new Cell;
  b#x := 0;
  assert s#x == 5
};
#end

/-! ## Negative: a pre-yield private allocation is havoced at the yield. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine privateAllocLost()
  modifies *
{
  var a: Cell := new Cell;
  a#x := 5;
  yield;
  assert a#x == 5
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end
