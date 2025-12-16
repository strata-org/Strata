/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Laurel

def program := r"
procedure guards(a: int): int
{
  var b := a + 2;
  if (b > 2) {
      var c := b + 3;
      if (c > 3) {
          return c + 4;
      }
      var d := c + 5;
      return d + 6;
  }
  var e := b + 1;
  e
}

procedure dag(a: int): int
{
  var b: int;

  if (a > 0) {
    b := 1;
  }
  b
}
"

#eval! testInputWithOffset "ControlFlow" program 15 processLaurelFile

/-
Translation towards expression form:

function guards(a: int): int {
  var b = a + 2;
  if (b > 2) {
      var c = b + 3;
      if (c > 3) {
        c + 4;
      } else {
        var d = c + 5;
        d + 6;
      }
  } else {
    var e = b + 1;
    e
  }
}

To translate towards SMT we only need to apply something like WP calculus.
 Here's an example of what that looks like:

function dag(a: int): int {
  (
    assume a > 0;
    assume b == 1;
    b;
  )
  OR
  (
    assume a <= 0;
    assume b == 2;
    b;
  )
}
-/
