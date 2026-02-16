/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples
open StrataTest.Util
namespace Strata.Laurel

def program := r"
procedure containsTarget(arr: Array<int>, len: int, target: int) returns (r: bool)
  requires len >= 0
  ensures r == Seq.Contains(Seq.From(arr), target)
{
  return Seq.Contains(Seq.From(arr), target);
}

procedure containsInPrefix(arr: Array<int>, len: int, n: int, target: int) returns (r: bool)
  requires len >= 0
  requires n >= 0
  requires n <= len
  ensures r == Seq.Contains(Seq.Take(Seq.From(arr), n), target)
{
  return Seq.Contains(Seq.Take(Seq.From(arr), n), target);
}
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "Sequences" program 5 processLaurelFile

end Strata.Laurel
