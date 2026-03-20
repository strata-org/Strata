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

procedure testListLen() {
  var xs: IntList := Cons(1, Cons(2, Nil()));
  assert listLen(xs) == 2
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "RecursiveFunction" program 14 processLaurelFile

end Strata.Laurel
