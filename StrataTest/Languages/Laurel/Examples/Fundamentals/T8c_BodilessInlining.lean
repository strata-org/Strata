/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.SimpleAPI

/-! # Bodiless Procedure Inlining Test

Verifies that inlining a bodiless Laurel procedure does not introduce
`assume false`. Previously, bodiless procedures had `assume false` as their
body, so inlining would make everything after the call trivially provable.
Now the body assumes the postconditions instead, so `assert false` after
the inlined call is correctly rejected. -/

namespace Strata.Laurel.BodilessInliningTest

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
};
"

/-- info: "assert(161): ❌ fail" -/
#guard_msgs in
#eval show IO String from do
  let laurelProg ← Strata.parseLaurelText "test.laurel" laurelSource
  let coreProg ← match ← Strata.laurelToCore laurelProg with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"Translation failed: {e}")
  let inlined ← match Strata.Core.inlineProcedures coreProg {} with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"Inlining failed: {e}")
  let vcResults ←
    EIO.toIO (fun e => IO.Error.userError e)
      (Strata.Core.verifyProgram inlined
        { Core.VerifyOptions.default with verbose := .quiet }
        (proceduresToVerify := some ["caller"]))
  -- Collect only failing results
  let failures := vcResults.filter fun vcr =>
    match vcr.outcome with
    | .ok o => o.validityProperty != .unsat
    | .error _ => true
  let mut output := ""
  for vcr in failures do
    output := output ++ s!"{vcr.obligation.label}: {vcr.formatOutcome}"
  return output

end Strata.Laurel.BodilessInliningTest
