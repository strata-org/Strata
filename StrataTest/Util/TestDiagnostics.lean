/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier
import Lean.Elab.Command

open Strata
open String
open Lean Elab
namespace StrataTest.Util

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
    if line.trimLeft.startsWith "//" then
      let trimmed := line.trimLeft.drop 2  -- Remove "//"
      -- Find the caret sequence
      let caretStart := trimmed.find (· == '^')
      let mut currentCaret := caretStart
      while not (Pos.Raw.atEnd trimmed currentCaret) && (Pos.Raw.get trimmed currentCaret) == '^' do
        currentCaret := Pos.Raw.next trimmed currentCaret

      -- Get the message part after carets
      let afterCarets := trimmed.drop currentCaret.byteIdx |>.trim
      if afterCarets.length > 0 then
        -- Parse level and message
        match afterCarets.splitOn ":" with
        | level :: messageParts =>
          let level := level.trim
          let message := (": ".intercalate messageParts).trim

          -- Calculate column positions (carets are relative to line start including comment spacing)
          let commentPrefix := (line.takeWhile (fun c => c == ' ' || c == '\t')).length + "//".length
          let caretColStart := commentPrefix + caretStart.byteIdx
          let caretColEnd := commentPrefix + currentCaret.byteIdx

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

/-- Check if one string contains another as a substring -/
def stringContains (haystack : String) (needle : String) : Bool :=
  needle.isEmpty || (haystack.splitOn needle).length > 1

/-- Check if a Diagnostic matches a DiagnosticExpectation -/
def matchesDiagnostic (diag : Diagnostic) (exp : DiagnosticExpectation) : Bool :=
  diag.start.line == exp.line &&
  diag.start.column == exp.colStart &&
  diag.ending.line == exp.line &&
  diag.ending.column == exp.colEnd &&
  stringContains diag.message exp.message

/-- Generic test function for files with diagnostic expectations.
    Takes a function that processes a file path and returns a list of diagnostics. -/
def testInputContext (input : Parser.InputContext) (process : Lean.Parser.InputContext -> IO (Array Diagnostic)) : IO Unit := do

  -- Parse diagnostic expectations from comments
  let expectations := parseDiagnosticExpectations input.inputString
  let expectedErrors := expectations.filter (fun e => e.level == "error")

  -- Get actual diagnostics from the language-specific processor
  let diagnostics <- process input

  -- Check if all expected errors are matched
  let mut allMatched := true
  let mut unmatchedExpectations := []

  for exp in expectedErrors do
    let matched := diagnostics.any (fun diag => matchesDiagnostic diag exp)
    if !matched then
      allMatched := false
      unmatchedExpectations := unmatchedExpectations.append [exp]

  -- Check if there are unexpected diagnostics
  let mut unmatchedDiagnostics := []
  for diag in diagnostics do
    let matched := expectedErrors.any (fun exp => matchesDiagnostic diag exp)
    if !matched then
      allMatched := false
      unmatchedDiagnostics := unmatchedDiagnostics.append [diag]

  -- Report results
  if allMatched && diagnostics.size == expectedErrors.length then
    IO.println s!"✓ Test passed: All {expectedErrors.length} error(s) matched"
    -- Print details of matched expectations
    for exp in expectedErrors do
      IO.println s!"  - Line {exp.line}, Col {exp.colStart}-{exp.colEnd}: {exp.message}"
  else
    IO.println s!"✗ Test failed: Mismatched diagnostics"
    IO.println s!"\nExpected {expectedErrors.length} error(s), got {diagnostics.size} diagnostic(s)"

    if unmatchedExpectations.length > 0 then
      IO.println s!"\nUnmatched expected diagnostics:"
      for exp in unmatchedExpectations do
        IO.println s!"  - Line {exp.line}, Col {exp.colStart}-{exp.colEnd}: {exp.message}"

    if unmatchedDiagnostics.length > 0 then
      IO.println s!"\nUnexpected diagnostics:"
      for diag in unmatchedDiagnostics do
        IO.println s!"  - Line {diag.start.line}, Col {diag.start.column}-{diag.ending.column}: {diag.message}"
    throw (IO.userError "Test failed")

def testInput (filename: String) (input : String) (process : Lean.Parser.InputContext -> IO (Array Diagnostic)) : IO Unit :=
  testInputContext (Parser.stringInputContext filename input) process

/-- Test input with line offset - reports diagnostic line numbers offset by the given amount -/
def testInputWithOffset (filename: String) (input : String) (lineOffset : Nat)
    (process : Lean.Parser.InputContext -> IO (Array Diagnostic)) : IO Unit := do

  let inputContext := Parser.stringInputContext filename input

  -- Parse diagnostic expectations from comments
  let expectations := parseDiagnosticExpectations input
  let expectedErrors := expectations.filter (fun e => e.level == "error")

  -- Get actual diagnostics from the language-specific processor
  let diagnostics <- process inputContext

  -- Check if all expected errors are matched
  let mut allMatched := true
  let mut unmatchedExpectations := []

  for exp in expectedErrors do
    let matched := diagnostics.any (fun diag => matchesDiagnostic diag exp)
    if !matched then
      allMatched := false
      unmatchedExpectations := unmatchedExpectations.append [exp]

  -- Check if there are unexpected diagnostics
  let mut unmatchedDiagnostics := []
  for diag in diagnostics do
    let matched := expectedErrors.any (fun exp => matchesDiagnostic diag exp)
    if !matched then
      allMatched := false
      unmatchedDiagnostics := unmatchedDiagnostics.append [diag]

  -- Report results with adjusted line numbers
  if allMatched && diagnostics.size == expectedErrors.length then
    IO.println s!"✓ Test passed: All {expectedErrors.length} error(s) matched"
    -- Print details of matched expectations with offset line numbers
    for exp in expectedErrors do
      IO.println s!"  - Line {exp.line + lineOffset}, Col {exp.colStart}-{exp.colEnd}: {exp.message}"
  else
    IO.println s!"✗ Test failed: Mismatched diagnostics"
    IO.println s!"\nExpected {expectedErrors.length} error(s), got {diagnostics.size} diagnostic(s)"

    if unmatchedExpectations.length > 0 then
      IO.println s!"\nUnmatched expected diagnostics:"
      for exp in unmatchedExpectations do
        IO.println s!"  - Line {exp.line + lineOffset}, Col {exp.colStart}-{exp.colEnd}: {exp.message}"

    if unmatchedDiagnostics.length > 0 then
      IO.println s!"\nUnexpected diagnostics:"
      for diag in unmatchedDiagnostics do
        IO.println s!"  - Line {diag.start.line + lineOffset}, Col {diag.start.column}-{diag.ending.column}: {diag.message}"
    throw (IO.userError "Test failed")

end StrataTest.Util
