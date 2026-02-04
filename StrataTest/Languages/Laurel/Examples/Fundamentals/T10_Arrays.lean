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
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "Arrays" program 5 processLaurelFile

end Strata.Laurel
