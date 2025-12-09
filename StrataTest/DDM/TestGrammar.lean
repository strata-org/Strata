/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.Parser
import Strata.DDM.Format

open Strata

namespace StrataTest.DDM

/-- Normalize whitespace in a string by splitting on whitespace and rejoining with single spaces -/
def normalizeWhitespace (s : String) : String :=
  let words := s.splitOn.filter (·.isEmpty.not)
  " ".intercalate words

/-- Result of a grammar test -/
structure GrammarTestResult where
  parseSuccess : Bool
  formatted : String
  normalizedMatch : Bool
  errorMessages : List String := []

/-- Test parsing and formatting a file with a given dialect.

    Takes:
    - loader: The dialect loader containing all required dialects
    - dialectName: Name of the dialect (for the "program" header)
    - filePath: Path to the source file to test

    Returns:
    - GrammarTestResult with parse/format results -/
def testGrammarFile (loader : Elab.LoadedDialects) (dialectName : String) (filePath : String) : IO GrammarTestResult := do
  let fileContent ← IO.FS.readFile filePath

  -- Add program header to the content
  let content := s!"program {dialectName};\n\n" ++ fileContent

  -- Create InputContext from the file content
  let inputCtx := Strata.Parser.stringInputContext filePath content

  -- Create empty Lean environment
  let leanEnv ← Lean.mkEmptyEnvironment 0

  -- Parse using the dialect
  let ddmResult := Elab.elabProgram loader leanEnv inputCtx

  match ddmResult with
  | Except.error messages =>
    let errorMsgs ← messages.toList.mapM (fun msg => msg.toString)
    return {
      parseSuccess := false
      formatted := ""
      normalizedMatch := false
      errorMessages := errorMsgs
    }
  | Except.ok ddmProgram =>
    -- Format the DDM program back to a string
    let formatted := ddmProgram.format.render

    -- Normalize whitespace in both strings
    let normalizedInput := normalizeWhitespace content
    let normalizedOutput := normalizeWhitespace formatted

    -- Compare
    let isMatch := normalizedInput == normalizedOutput

    return {
      parseSuccess := true
      formatted := formatted
      normalizedMatch := isMatch
      errorMessages := []
    }

/-- Print detailed test results -/
def printTestResult (filePath : String) (result : GrammarTestResult) (showFormatted : Bool := true) : IO Unit := do
  IO.println s!"=== Testing {filePath} ===\n"

  if !result.parseSuccess then
    IO.println s!"✗ Parse failed: {result.errorMessages.length} error(s)"
    for msg in result.errorMessages do
      IO.println s!"  {msg}"
  else
    IO.println "✓ Parse succeeded!\n"

    if showFormatted then
      IO.println "=== Formatted output ===\n"
      IO.println result.formatted

    IO.println "\n=== Comparison ===\n"
    if result.normalizedMatch then
      IO.println "✓ Formatted output matches input (modulo whitespace)!"
    else
      IO.println "✗ Formatted output differs from input"
      IO.println "(This is expected when comments are present in the source)"

end StrataTest.DDM