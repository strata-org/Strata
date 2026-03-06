/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata
namespace Laurel

def program := r"
procedure guards(a: int) returns (r: int)
{
  var b: int := a + 2;
  if (b > 2) {
      var c: int := b + 3;
      if (c > 3) {
          return c + 4;
      }
      var d: int := c + 5;
      return d + 6;
  }
  var e: int := b + 1;
  assert e <= 3;
    assert e < 3;
//  ^^^^^^^^^^^^^ error: assertion does not hold
  return e;
}

procedure dag(a: int) returns (r: int)
{
  var b: int;

  if (a > 0) {
    b := 1;
  }
  assert if (a > 0) { b == 1 } else { true };
    assert if (a > 0) { b == 2 } else { true };
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
// duplicates due to VCG path duplication (#419):
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
  return b;
}
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "ControlFlow" program 14 processLaurelFile
