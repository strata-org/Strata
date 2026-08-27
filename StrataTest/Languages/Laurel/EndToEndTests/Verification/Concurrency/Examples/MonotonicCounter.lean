/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataTest.Languages.Laurel.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util.Concurrency


def prog :=
#strata

program Laurel;

composite Cell { var x: int }

coroutine incMonotonic(s: Cell)
  requires s#x == 0
  relies old(s#x) <= s#x
  guarantees old(s#x) < s#x
  modifies s
{
  while (true)
      invariant oldGuarantee(s#x) <= s#x
  {
    s#x := s#x + 1;
    yield
  }
};

#end

#eval testCoroutine <| prog

/-! ## Two coroutines with incompatible contracts.

`incMonotonic` relies on `old(s#x) <= s#x` (the environment never decreases the
counter). `dec` GUARANTEES `old(s#x) > s#x` (it strictly decreases it). If both
ran against the same `s`, `dec`'s step would break `inc`'s rely — the two
contracts are mutually incompatible.

Question: does `incMonotonic` still verify?
-/

def progTwo :=
#strata

program Laurel;

composite Cell { var x: int }

coroutine incMonotonic(s: Cell)
  requires s#x == 0
  relies old(s#x) <= s#x
  guarantees old(s#x) < s#x
  modifies s
{
  while (true)
      invariant oldGuarantee(s#x) <= s#x
  {
    s#x := s#x + 1;
    yield
  }
};

coroutine dec(s: Cell)
  relies old(s#x) >= s#x
  guarantees old(s#x) > s#x
  modifies s
{
  while (true)
      invariant oldGuarantee(s#x) >= s#x
  {
    s#x := s#x - 1;
    yield
  }
};

#end

#eval testCoroutine <| progTwo
