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

-- Negative cases: misuses of Array<T> flagged by ValidateSubscriptUsage.

def arrayFuncUpdateProgram := r"
// Diagnostic 1: functional update on Array<T>
procedure arrayFuncUpdate() {
  var a: Array<int> := [1, 2, 3];
  var b: Array<int> := a[0 := 99]
//                     ^^^^^^^^^^ error: not supported on `Array
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "ArrayFuncUpdate" arrayFuncUpdateProgram 14 processLaurelFile

def arrayLengthWrongArgProgram := r"
// Diagnostic 3: Array.length on a non-Array argument
procedure arrayLengthWrongArg() {
  var s: Seq<int> := [1, 2, 3];
  assert Array.length(s) == 3
//       ^^^^^^^^^^^^^^^ error: requires an argument of type
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "ArrayLengthWrongArg" arrayLengthWrongArgProgram 14 processLaurelFile

def arrayNonIntElementProgram := r"
// Diagnostic 4: Array<T> with T other than int
procedure arrayNonIntElement() {
  var a: Array<bool> := [true, false]
//       ^^^^^^^^^^^ error: currently only supported
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "ArrayNonIntElement" arrayNonIntElementProgram 14 processLaurelFile

end Laurel
end Strata
