/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def arrayProgram := r"
// Basic read/write
procedure basicReadWrite() {
  var a: Array<int> := [1, 2, 3];
  a[0] := 42;
  assert a[0] == 42
};

// Length
procedure length() {
  var a: Array<int> := [10, 20, 30];
  assert Sequence.length(a) == 3
};

// Empty array
procedure emptyArray() {
  var a: Array<int> := [];
  assert Sequence.length(a) == 0
};

// Array in contracts
procedure arrayContract(a: Array<int>)
  requires Sequence.length(a) > 0
{
  var x: int := a[0];
  assert x == Sequence.select(a, 0)
};

// Multiple writes
procedure multipleWrites() {
  var a: Array<int> := [0, 0, 0];
  a[0] := 10;
  a[1] := 20;
  a[2] := 30;
  assert a[0] == 10;
  assert a[1] == 20;
  assert a[2] == 30
};

// Aliasing: mutation through one reference visible through another
procedure aliasing() {
  var a: Array<int> := [1, 2, 3];
  var b: Array<int> := a;
  b[0] := 99;
  assert a[0] == 99
};

// Failing assertion
procedure failingAssert() {
  var a: Array<int> := [1, 2, 3];
  assert a[0] == 999
//^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "Arrays" arrayProgram 14 processLaurelFile

end Laurel
end Strata
