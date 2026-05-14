/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

/-
A recursive function over a recursive datatype.
The `isRecursive` flag should be inferred automatically from the self-call.
-/
def program := r"
datatype IntList {
  Nil(),
  Cons(head: int, tail: IntList)
}

function listLen(xs: IntList): int {
  if IntList..isNil(xs) then 0
  else 1 + listLen(IntList..tail!(xs))
};

procedure testListLen()
  opaque
{
  var xs: IntList := Cons(1, Cons(2, Nil()));
  assert listLen(xs) == 2
};

// Mutual recursion
function listLenEven(xs: IntList): bool {
  if IntList..isNil(xs) then true
  else listLenOdd(IntList..tail!(xs))
};

function listLenOdd(xs: IntList): bool {
  if IntList..isNil(xs) then false
  else listLenEven(IntList..tail!(xs))
};

procedure testMutualRecursion()
  opaque
{
  var xs: IntList := Cons(1, Cons(2, Nil()));
  assert listLenEven(xs) == true
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "RecursiveFunction" program 14 processLaurelFile

end Strata.Laurel
