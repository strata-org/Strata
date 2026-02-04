import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples
open StrataTest.Util
namespace Strata.Laurel

def program := r"
procedure test(x: int)
requires forall(i: int) => i >= 0
ensures exists(j: int) => j == x
{}

procedure multiContract(x: int) returns (r: int)
requires x >= 0
requires x <= 100
ensures r >= x
ensures r <= x + 10
{
    return x + 5;
}
"

#guard_msgs(drop info) in
#eval testInputWithOffset "Contracts" program 5 processLaurelFile

end Strata.Laurel
