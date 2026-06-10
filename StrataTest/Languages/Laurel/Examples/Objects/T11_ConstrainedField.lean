/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
Test: constrained types as composite fields. Verifies that heap
parameterization resolves constrained types to their base type for boxing.
-/

meta import all StrataTest.Util.TestDiagnostics
meta import all StrataTest.Languages.Laurel.TestExamples

meta section

open StrataTest.Util
open Strata

namespace Strata.Laurel

def constrainedFieldTest := r"
constrained nat = x: int where x >= 0 witness 0

composite Counter {
  var count: nat
}

procedure setCount(c: Counter)
  opaque
  ensures c#count >= 0
  modifies c
{
  c#count := 1
};

// Error: assigning -1 to a nat field violates the constraint
procedure setCountInvalid(c: Counter)
  opaque
  modifies c
{
  c#count := -1
//^^^^^^^^^^^^^ error: assertion does not hold
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "ConstrainedField" constrainedFieldTest 23 processLaurelFile

end Laurel
