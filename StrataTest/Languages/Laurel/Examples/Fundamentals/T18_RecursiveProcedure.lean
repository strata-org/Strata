/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
A recursive function over a recursive datatype.
The `isRecursive` flag should be inferred automatically from the self-call.
-/

#eval testLaurel
#strata
program Laurel;
datatype IntList {
  Nil(),
  Cons(head: int, tail: IntList)
}

procedure listLen(xs: IntList): int
{
  return if IntList..isNil(xs) then 0
  else 1 + listLen(IntList..tail!(xs))
};

procedure testListLen()
  opaque
{
  var xs: IntList := Cons(1, Cons(2, Nil()));
  assert listLen(xs) == 2
};

// Mutual recursion
procedure listLenEven(xs: IntList): bool
{
  return if IntList..isNil(xs) then true
  else listLenOdd(IntList..tail!(xs))
};

procedure listLenOdd(xs: IntList): bool
{
  return if IntList..isNil(xs) then false
  else listLenEven(IntList..tail!(xs))
};

procedure testMutualRecursion()
  opaque
{
  var xs: IntList := Cons(1, Cons(2, Nil()));
  assert listLenEven(xs) == true
};
#end
