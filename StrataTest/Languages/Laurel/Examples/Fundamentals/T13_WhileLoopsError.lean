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

/-
  Regression test for per-invariant source ranges in loop-invariant
  diagnostics (LoopElim threads each invariant's provenance through the loop
  metadata; see `MetaData.getInvariantProvenances` / `LoopElim.invMd`).

  Before that fix, a failing loop invariant was reported at the whole loop's
  source range. These tests pin the diagnostic to the specific invariant: the
  caret must land on the failing `invariant` expression, not the loop or the
  other (passing) invariant.
-/

-- A single loop invariant that does not hold on entry. The diagnostic must
-- point at the invariant expression `i >= 0`, not at the `while` loop.
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

-- Two invariants where the first holds on entry but the second does not. The
-- diagnostic must point at the failing second invariant `j >= 0` specifically,
-- demonstrating per-invariant (not loop-wide) source attribution.
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

end Laurel
