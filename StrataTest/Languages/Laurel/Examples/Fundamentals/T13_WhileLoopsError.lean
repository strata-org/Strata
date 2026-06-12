/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataTest.Util.TestDiagnostics
meta import all StrataTest.Languages.Laurel.TestExamples

meta section

open StrataTest.Util

namespace Strata
namespace Laurel

def badInitialInvariantProgram := r"
procedure badInitialInvariant()
  opaque
{
    var i: int := -1;
    while(i < 10)
      invariant i >= 0
//              ^^^^^^ error: assertion does not hold
    {
        i := i + 1
    }
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "BadInitialInvariant" badInitialInvariantProgram 40 processLaurelFile

def secondInvariantFailsProgram := r"
procedure secondInvariantFails()
  opaque
{
    var i: int := 0;
    var j: int := -1;
    while(i < 10)
      invariant i >= 0
      invariant j >= 0
//              ^^^^^^ error: assertion does not hold
    {
        i := i + 1;
        j := j + 1
    }
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "SecondInvariantFails" secondInvariantFailsProgram 60 processLaurelFile

def forSecondInvFailsProgram := r"
procedure forSecondInvFails()
  opaque
{
    var j: int := -1;
    for(var i: int := 0; i < 10; i := i + 1)
      invariant i >= 0
      invariant j >= 0
//              ^^^^^^ error: assertion does not hold
    {
        j := j + 1
    }
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "ForSecondInvFails" forSecondInvFailsProgram 60 processLaurelFile

end Laurel
