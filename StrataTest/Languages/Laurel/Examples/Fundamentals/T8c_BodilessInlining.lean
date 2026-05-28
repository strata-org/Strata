/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.SimpleAPI
import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

/-! # Bodiless Procedure Inlining Test

Verifies that inlining a bodiless Laurel procedure does not introduce
`assume false`. Previously, bodiless procedures had `assume false` as their
body, so inlining would make everything after the call trivially provable.
Now the body assumes the postconditions instead, so `assert false` after
the inlined call is correctly rejected. -/

namespace Strata.Laurel.BodilessInliningTest

open StrataTest.Util
open Strata

private def laurelSource := "
procedure bodilessProcedure() returns (r: int)
  opaque
  ensures r > 0
;

procedure caller()
  opaque
{
  var x: int := bodilessProcedure();
  assert x > 0;
  assert false
//^^^^^^^^^^^^ error: assertion could not be proved
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "Postconditions" laurelSource 23
  (fun p => processLaurelFileWithOptions { translateOptions := { inlineFunctionsWhenPossible := true} } p)

end Strata.Laurel.BodilessInliningTest
