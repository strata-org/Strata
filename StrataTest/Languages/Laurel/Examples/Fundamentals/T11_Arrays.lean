/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples
open StrataTest.Util
namespace Strata.Laurel

def program := r"
procedure getFirst(arr: Array<int>, len: int) returns (r: int)
  requires len > 0
ensures r == arr[0]
{
  return arr[0];
}

procedure sumTwo(arr: Array<int>, len: int) returns (r: int)
  requires len >= 2
  ensures r == arr[0] + arr[1]
{
  return arr[0] + arr[1];
}

// Test passing arrays to other procedures
constrained int32 = x: int where x >= -2147483648 && x <= 2147483647 witness 0
procedure helper(arr: Array<int32>): int32
  requires Array.Length(arr) > 0
{ return 0; }
procedure callWithArray(arr: Array<int32>): int32
  requires Array.Length(arr) > 0
{
  var x: int32 := helper(arr);
  return x;
}
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "Arrays" program 5 processLaurelFile

end Strata.Laurel
