/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier

/-!
# B3 Verifier Integration Tests

Tests for the B3 verifier interface.
These tests require `b3` to be available in PATH and will fail if it's not found.
-/

namespace StrataTest.B3

open Strata.B3

/-- Test that b3 is available - fails if not found -/
def testB3Available : IO Unit := do
  let available ← isAvailable
  if !available then
    throw (IO.userError "ERROR: b3 is not available in PATH. Please ensure b3 is accessible before running tests.")
  IO.println "✓ b3 is available"

/-- Test verifying a simple B3 program from text -/
def testVerifySimpleText : IO Unit := do
  let program := "
procedure Test() {
  check true
}
"

  let result ← verifyText program
  match result with
  | .success output =>
    IO.println "✓ Simple text verification succeeded"
    IO.println s!"Output: {output.take 100}..."
  | .error msg =>
    throw (IO.userError s!"Simple text verification failed: {msg}")

/-- Test verifying the Simple.b3 example file -/
def testVerifySimpleFile : IO Unit := do
  let filePath := "Examples/Simple.b3"

  let result ← verify filePath
  match result with
  | .success output =>
    IO.println s!"✓ File verification succeeded: {filePath}"
    IO.println s!"Output preview: {output.take 200}..."
  | .error msg =>
    throw (IO.userError s!"File verification failed: {msg}")

/-- Test verifying with proof obligations shown -/
def testVerifyWithProofObligations : IO Unit := do
  let program := "
procedure TestWithSpec(x: int)
  requires x > 0
  ensures x > 0
{
  check x > 0
}
"

  let result ← verifyText program (showProofObligations := true)
  match result with
  | .success output =>
    IO.println "✓ Verification with proof obligations succeeded"
    -- Check if output contains proof obligation text
    let parts := output.splitOn "Proof obligation"
    let hasProofObligation := parts.length > 1
    if hasProofObligation then
      IO.println "  (Proof obligations were shown in output)"
    IO.println s!"Output preview: {output.take 300}..."
  | .error msg =>
    throw (IO.userError s!"Verification with proof obligations failed: {msg}")

/-- Test parse-only mode -/
def testParseOnly : IO Unit := do
  let program := "
procedure ParseTest() {
  var x: int
  x := 42
}
"

  -- Write to temp file for parse test
  let tempFile := "test_parse_temp.b3"
  IO.FS.writeFile tempFile program

  let result ← parseOnly tempFile

  -- Clean up
  try
    IO.FS.removeFile tempFile
  catch _ =>
    pure ()  -- Ignore cleanup errors

  match result with
  | .success _ =>
    IO.println "✓ Parse-only test succeeded"
  | .error msg =>
    throw (IO.userError s!"Parse-only test failed: {msg}")

/-- Test error handling for invalid B3 program -/
def testInvalidProgram : IO Unit := do
  let invalidProgram := "
procedure Invalid {
  this is not valid B3 syntax !!!
}
"

  let result ← verifyText invalidProgram
  match result with
  | .success output =>
    -- B3 may return success exit code but include error messages in output
    let parts := output.toLower.splitOn "error"
    if parts.length > 1 then
      IO.println "✓ Invalid program correctly failed (error in output)"
      IO.println s!"  Error preview: {output.take 150}..."
    else
      throw (IO.userError "Invalid program should have failed but succeeded")
  | .error msg =>
    IO.println "✓ Invalid program correctly failed"
    IO.println s!"  Error preview: {msg.take 150}..."

/-- Run all B3 verifier tests -/
def runAllTests : IO Unit := do
  IO.println "\n=== B3 Verifier Integration Tests ==="
  IO.println ""

  testB3Available
  IO.println ""

  testVerifySimpleText
  IO.println ""

  testVerifySimpleFile
  IO.println ""

  testVerifyWithProofObligations
  IO.println ""

  testParseOnly
  IO.println ""

  testInvalidProgram
  IO.println ""

  IO.println "=== B3 Tests Complete ==="

end StrataTest.B3

/-- Main entry point for running tests -/
def main : IO Unit := do
  StrataTest.B3.runAllTests
