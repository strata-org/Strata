/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.SimpleAPI

/-!
# Inline Assertion Metadata Test

Verifies that inlining a procedure call preserves assertion metadata:
the inlined assertion should carry the call site as the primary location
and the original assertion location as a related location.
-/

namespace Core.InlineAssertionMetadata.Tests

open Imperative

private def inlineAssertPgm : Strata.Program :=
#strata
program Core;
procedure callee() {
  assert [willFail]: false;
};
procedure caller() {
  call callee();
};
#end

/-- info: "willFail: ❌ fail\n Assertion is 52 characters after the related location" -/
#guard_msgs in
#eval show IO String from do
  let (coreProg, _) := Strata.Core.getProgram inlineAssertPgm
  let inlined ← match Strata.Core.inlineProcedures coreProg {} with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"Inlining failed: {e}")
  let vcResults ←
    EIO.toIO (fun e => IO.Error.userError e)
      (Strata.Core.verifyProgram inlined
        { Core.VerifyOptions.default with verbose := .quiet }
        (proceduresToVerify := some ["caller"]))
  let mut output := ""
  for vcr in vcResults do
    output := output ++ s!"{vcr.obligation.label}: {vcr.formatOutcome}"
    match Imperative.getFileRange vcr.obligation.metadata with
    | some primary =>
      let related := Imperative.getRelatedFileRanges vcr.obligation.metadata
      for r in related do
        let delta := primary.range.start.byteIdx - r.range.start.byteIdx
        output := output ++ s!"\n Assertion is {delta} characters after the related location"
    | none => pure ()
  return output

end Core.InlineAssertionMetadata.Tests
