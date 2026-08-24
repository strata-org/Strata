/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
The guarantee is checked on the final `resume -> halt` segment, not only at
yields. The generated opaque `resume` advertises `G` as an unguarded
postcondition, so a coroutine that honored `G` at every yield but broke it
after the last one would let a caller assume a fact nothing proved.

  * **Negative (coroutine alone):** code after the last `yield` violates `G`
    and is rejected at the exit assert.
  * **Negative (with caller):** the same coroutine, resumed twice by a caller
    that asserts the broken fact. The rejection comes from the *coroutine's*
    exit assert, not from the caller's `assert` — the opaque resume's
    postcondition is by construction, so a caller-side obligation can never
    disprove it. What this pins is that the unsound conclusion no longer
    slips through: the program as a whole is rejected.
  * **Positive (honors G on the final segment):** a coroutine whose
    post-yield tail respects `G` still verifies, and the caller soundly uses
    the guarantee.
-/

import StrataTest.Languages.Laurel.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util.Concurrency

/-! ## Negative: tail after the last yield breaks the guarantee. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine breaker(s: Cell)
  requires s#x == 0
  guarantees old(s#x) <= s#x
//           ^^^^^^^^^^^^^^^ error: coroutine exit: guarantee does not hold
  modifies *
{
  s#x := s#x + 1;
  yield;
  s#x := 0 - 10
};
#end

/-! ## Negative: the caller cannot assume the broken guarantee. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine breaker2(s: Cell)
  requires s#x == 0
  guarantees old(s#x) <= s#x
//           ^^^^^^^^^^^^^^^ error: coroutine exit: guarantee does not hold
  modifies *
{
  s#x := s#x + 1;
  yield;
  s#x := 0 - 10
};

procedure main()
  opaque
  modifies *
{
  var s: Cell := new Cell;
  s#x := 0;
  var co: breaker2 := breaker2(s);
  resume(co);
  resume(co);
  assert s#x >= 0
};
#end

/-! ## Positive: the final segment honors the guarantee. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine keeper(s: Cell)
  requires s#x == 0
  relies old(s#x) == s#x
  guarantees old(s#x) <= s#x
  modifies *
{
  s#x := s#x + 1;
  yield;
  s#x := s#x + 1
};

procedure mainOk()
  opaque
  modifies *
{
  var s: Cell := new Cell;
  s#x := 0;
  var co: keeper := keeper(s);
  resume(co);
  resume(co);
  assert s#x >= 0
};
#end
