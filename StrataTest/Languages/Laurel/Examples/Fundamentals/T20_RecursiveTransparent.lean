/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

/-
Recursive transparent procedures. The transparency pass produces a recursive
function (`$asFunction`) for each transparent procedure and ties them via a
free postcondition.
-/
def recursiveTransparentProgram := r"
// Recursion on a datatype
datatype IntList {
  Nil(),
  Cons(head: int, tail: IntList)
}

procedure listSum(xs: IntList): int
{
  if IntList..isNil(xs) then 0
  else IntList..head!(xs) + listSum(IntList..tail!(xs))
};

procedure testListSum() opaque {
  var xs: IntList := Cons(1, Cons(2, Cons(3, Nil())));
  assert listSum(xs) == 6
};

// Recursion on a number
procedure factorial(n: int): int
{
  if n == 0 then 1
  else n * factorial(n - 1)
};

procedure testFactorial() opaque {
  assert factorial(0) == 1;
  assert factorial(3) == 6
};
"

-- TODO: This test currently does not pass due to a bug where the generated
-- $asFunction is not placed in a recFuncBlock, causing a Core type checking error.
-- #guard_msgs(drop info, error) in
-- #eval testInputWithOffset "RecursiveTransparent" recursiveTransparentProgram 14 processLaurelFile

end Laurel
