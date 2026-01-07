/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.Parser
import Strata.DDM.Format

open Strata

namespace StrataTest.DDM

/-- Remove C-style comments (// and /* */) from a string -/
def stripComments (s : String) : String :=
  let rec stripMultiLine (str : String) (startIdx : Nat) (acc : String) : String :=
    if startIdx >= str.length then acc
    else
      let remaining := str.drop startIdx
      match remaining.splitOn "/*" with
      | [] => acc
      | [rest] => acc ++ rest
      | beforeComment :: afterStart =>
        let afterStartStr := "/*".intercalate afterStart
        match afterStartStr.splitOn "*/" with
        | [] => acc ++ beforeComment
        | afterComment :: _ =>
          let newIdx := startIdx + beforeComment.length + 2 + afterComment.length + 2
          stripMultiLine str newIdx (acc ++ beforeComment)
  termination_by str.length - startIdx

  let withoutMultiLine := stripMultiLine s 0 ""
  let lines := withoutMultiLine.splitOn "\n"
  let withoutSingleLine := lines.map fun line =>
    match line.splitOn "//" with
    | [] => line
    | first :: _ => first
  "\n".intercalate withoutSingleLine

/-- Normalize whitespace in a string by splitting on whitespace and rejoining with single spaces -/
def normalizeWhitespace (s : String) : String :=
  let words := (s.splitToList Char.isWhitespace).filter (·.isEmpty.not)
  " ".intercalate words

/-- Result of a grammar test -/
structure GrammarTestResult where
  parseSuccess : Bool
  normalizedInput : String
  normalizedOutput : String
  normalizedMatch : Bool
  errorMessages : List String := []

/-- Test parsing and formatting a file with a given dialect.

    Takes:
    - dialect: The dialect to use for parsing
    - filePath: Path to the source file to test

    Returns:
    - GrammarTestResult with parse/format results -/
def testGrammarFile (dialect: Dialect) (filePath : String) : IO GrammarTestResult := do
  try
    let loaded := .ofDialects! #[initDialect, dialect]
    let (inputContext, ddmProgram) ← Strata.Elab.parseStrataProgramFromDialect loaded dialect.name filePath
    let formatted := ddmProgram.format.render
    let normalizedInput := normalizeWhitespace <| stripComments <|
      s!"program {dialect.name}; " ++ inputContext.inputString
    let normalizedOutput := normalizeWhitespace formatted

    let isMatch := normalizedInput == normalizedOutput

    return {
      parseSuccess := true
      normalizedInput := normalizedInput
      normalizedOutput := normalizedOutput
      normalizedMatch := isMatch
      errorMessages := []
    }
  catch e =>
    return {
      parseSuccess := false
      normalizedInput := ""
      normalizedOutput := ""
      normalizedMatch := false
      errorMessages := [toString e]
    }

def printTestResult (result : GrammarTestResult) (showFormatted : Bool := true) : IO Unit := do

  if !result.parseSuccess then
    IO.println s!"✗ Parse failed: {result.errorMessages.length} error(s)"
    for msg in result.errorMessages do
      IO.println s!"  {msg}"
  else
    IO.println "✓ Parse succeeded!\n"

    if showFormatted then
      IO.println "=== Formatted input ===\n"
      IO.println result.normalizedInput
      IO.println "=== Formatted output ===\n"
      IO.println result.normalizedOutput

    IO.println "\n=== Comparison ===\n"
    if result.normalizedMatch then
      IO.println "✓ Formatted output matches input (modulo whitespace)!"
    else
      IO.println "✗ Formatted output differs from input"
      IO.println "(This is expected when comments are present in the source)"

end StrataTest.DDM
