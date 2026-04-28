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
  assert Array.length(a) == 3
};

// Empty array
procedure emptyArray() {
  var a: Array<int> := [];
  assert Array.length(a) == 0
};

// Array in contracts
procedure arrayContract(a: Array<int>)
  requires Array.length(a) > 0
{
  var x: int := a[0];
  assert x == a[0]
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

// Array in a loop: zero-fill
procedure arrayLoop() {
  var a: Array<int> := [1, 2, 3];
  var i: int := 0;
  while (i < 3)
    invariant 0 <= i && i <= 3
    invariant Array.length(a) == 3
    invariant forall(j: int) => 0 <= j && j < i ==> a[j] == 0
  {
    a[i] := 0;
    i := i + 1
  };
  assert a[0] == 0;
  assert a[1] == 0;
  assert a[2] == 0
};

// Inter-procedural: callee modifies array
procedure setFirst(a: Array<int>, v: int)
  requires Array.length(a) > 0
  opaque
  ensures a[0] == v
  modifies a
{
  a[0] := v
};

procedure callSetFirst() {
  var a: Array<int> := [1, 2, 3];
  setFirst(a, 42);
  assert a[0] == 42
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "Arrays" arrayProgram 14 processLaurelFile

end Laurel
end Strata
