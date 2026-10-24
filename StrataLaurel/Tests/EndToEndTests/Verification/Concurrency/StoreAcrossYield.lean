/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
A store evaluates its receiver before its value, also when the value yields: the environment may
replace `s#r` while the coroutine is suspended, and `s#r#x := { yield; 5 }` still stores into the
box `s#r` held before the yield. Likewise the resume gives the `resumes` binding `w` a new value,
and `w#x := { yield; 5 }` stores into the box `w` held before the yield.
-/

import StrataLaurel.Tests.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util StrataTest.Util.Concurrency

#eval testLaurelVerification (options := coroutineOptions) <|
#strata
program Laurel;

composite Cell {
  var x: int
  var r: Cell
}

coroutine storeGoesToTheBoxBeforeTheYield(s: Cell, b: Cell)
  modifies *
{
  s#r := b;
  s#r#x := { yield; 5 };
  assert b#x == 5
};

coroutine storeGoesToTheResumedBoxBeforeTheYield() resumes (w: Cell)
  modifies *
{
  var a: Cell := w;
  w#x := { yield; 5 };
  assert a#x == 5
};
#end
