/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Grammar.LaurelParser
import Strata.Languages.Laurel.LaurelToBoogieTranslator
import Strata.DL.Imperative.MetaData

namespace Laurel

open Laurel.Parser
open Boogie (VCResult)
open Imperative (MetaData)

/-- A diagnostic expectation parsed from source comments -/
structure DiagnosticExpectation where
  line : Nat
  colStart : Nat
  colEnd : Nat
  level : String
  message : String
  deriving Repr, BEq

/-- Parse diagnostic expectations from source file comments.
    Format: `--  ^^^^^^ error: message` on the line after the problematic code -/
def parseDiagnosticExpectations (content : String) : List DiagnosticExpectation := Id.run do
  let lines := content.splitOn "\n"
  let mut expectations := []

  for i in [0:lines.length] do
    let line := lines[i]!
    -- Check if this is a comment line with diagnostic expectation
    if line.trimLeft.startsWith "--" then
      let trimmed := line.trimLeft.drop 2  -- Remove "--"
      -- Find the caret sequence
      let caretStart := trimmed.find (· == '^')
      if caretStart.byteIdx < trimmed.length then
        -- Count carets
        let mut caretEnd := caretStart
        while caretEnd.byteIdx < trimmed.length && trimmed.get caretEnd == '^' do
          caretEnd := caretEnd + ⟨1⟩

        -- Get the message part after carets
        let afterCarets := trimmed.drop caretEnd.byteIdx |>.trim
        if afterCarets.length > 0 then
          -- Parse level and message
          match afterCarets.splitOn ":" with
          | level :: messageParts =>
            let level := level.trim
            let message := (": ".intercalate messageParts).trim

            -- Calculate column positions (carets are relative to line start including comment spacing)
            let commentPrefix := line.takeWhile (fun c => c == ' ' || c == '\t')
            let caretColStart := commentPrefix.length + caretStart.byteIdx
            let caretColEnd := commentPrefix.length + caretEnd.byteIdx

            -- The diagnostic is on the previous line
            if i > 0 then
              expectations := expectations.append [{
                line := i,  -- 1-indexed line number (the line before the comment)
                colStart := caretColStart,
                colEnd := caretColEnd,
                level := level,
                message := message
              }]
          | [] => pure ()

  expectations

/-- Extract file range information from VCResult metadata -/
def extractFileRange (vcr : VCResult) : Option (Nat × Nat × Nat × Nat) := do
  let fileRangeElem ← vcr.obligation.metadata.findElem MetaData.fileRange
  match fileRangeElem.value with
  | .fileRange m =>
    return (m.start.line, m.start.column, m.ending.line, m.ending.column)
  | _ => none

/-- Check if one string contains another as a substring -/
def stringContains (haystack : String) (needle : String) : Bool :=
  needle.isEmpty || (haystack.splitOn needle).length > 1

/-- Check if a VCResult matches a DiagnosticExpectation -/
def matchesDiagnostic (vcr : VCResult) (exp : DiagnosticExpectation) : Bool :=
  match extractFileRange vcr with
  | none => false
  | some (startLine, startCol, endLine, endCol) =>
    -- Check if the range matches
    startLine == exp.line &&
    startCol == exp.colStart &&
    endLine == exp.line &&
    endCol == exp.colEnd &&
    -- Check if the label contains the expected message
    stringContains vcr.obligation.label exp.message

def testAssertFalse : IO Unit := do
  let content <- IO.FS.readFile "Strata/Languages/Laurel/Examples/Fundamentals/AssertFalse.lr.st"

  -- Parse diagnostic expectations from comments
  let expectations := parseDiagnosticExpectations content
  let expectedErrors := expectations.filter (fun e => e.level == "error")

  match parseProgram content with
  | Except.error err =>
    IO.println s!"Parse failed: {err}"
  | Except.ok prog =>
    IO.println "Parse succeeded"
    let results <- verify "cvc5" prog

    -- Get failed VCResults
    let failedResults := results.filter (fun r =>
      match r.result with
      | .sat _ => true  -- sat means failed (counterexample exists)
      | _ => false
    )

    -- Check if all expected errors are matched
    let mut allMatched := true
    let mut unmatchedExpectations := []

    for exp in expectedErrors do
      let matched := failedResults.any (fun vcr => matchesDiagnostic vcr exp)
      if !matched then
        allMatched := false
        unmatchedExpectations := unmatchedExpectations.append [exp]

    -- Check if there are unexpected failures
    let mut unmatchedResults := []
    for vcr in failedResults do
      let matched := expectedErrors.any (fun exp => matchesDiagnostic vcr exp)
      if !matched then
        allMatched := false
        unmatchedResults := unmatchedResults.append [vcr]

    -- Report results
    if allMatched && failedResults.size == expectedErrors.length then
      IO.println s!"✓ Test passed: All {expectedErrors.length} error(s) matched"
      -- Print details of matched expectations
      for exp in expectedErrors do
        IO.println s!"  - Line {exp.line}, Col {exp.colStart}-{exp.colEnd}: {exp.message}"
    else
      IO.println s!"✗ Test failed: Mismatched diagnostics"
      IO.println s!"\nExpected {expectedErrors.length} error(s), got {failedResults.size} failure(s)"

      if unmatchedExpectations.length > 0 then
        IO.println s!"\nUnmatched expected diagnostics:"
        for exp in unmatchedExpectations do
          IO.println s!"  - Line {exp.line}, Col {exp.colStart}-{exp.colEnd}: {exp.message}"

      if unmatchedResults.length > 0 then
        IO.println s!"\nUnexpected failures:"
        for vcr in unmatchedResults do
          match extractFileRange vcr with
          | some (startLine, startCol, _endLine, endCol) =>
            IO.println s!"  - Line {startLine}, Col {startCol}-{endCol}: {vcr.obligation.label}"
          | none =>
            IO.println s!"  - (no location): {vcr.obligation.label}"

#eval! testAssertFalse

end Laurel
