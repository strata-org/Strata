import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples
open StrataTest.Util
namespace Strata.Laurel

def program := r"
procedure test(x: int)
requires forall(i: int) => i >= 0
ensures exists(j: int) => j == x
{}
"

#guard_msgs(drop info) in
#eval testInputWithOffset "T5_Quantifiers" program 5 processLaurelFile

end Strata.Laurel
