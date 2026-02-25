/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples
open StrataTest.Util
namespace Strata.Laurel

def arrayEdgeCasesProgram := r"
constrained int32 = x: int where x >= -2147483648 && x <= 2147483647 witness 0

// Array of constrained element type — constraint on accessed elements
procedure constrainedElements(arr: Array<int32>)
  requires Array.Length(arr) > 0
  ensures arr[0] >= -2147483648
{
  assert arr[0] >= -2147483648;
}

// Empty prefix — Seq.Take with 0
procedure emptyPrefix(arr: Array<int>, len: int, target: int)
  requires len >= 0
  ensures !Seq.Contains(Seq.Take(Seq.From(arr), 0), target)
{}

// Suffix via Seq.Drop
procedure suffixDrop(arr: Array<int>, len: int, target: int) returns (r: bool)
  requires len >= 0
  ensures r == Seq.Contains(Seq.Drop(Seq.From(arr), 0), target)
{
  return Seq.Contains(Seq.From(arr), target);
}
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "ArrayEdgeCases" arrayEdgeCasesProgram 5 processLaurelFile

end Strata.Laurel
