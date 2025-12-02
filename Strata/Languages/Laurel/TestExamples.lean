/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Grammar.LaurelParser
import Strata.Languages.Laurel.LaurelToBoogieTranslator

namespace Laurel

open Laurel.Parser

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
      if caretStart < trimmed.length then
        -- Count carets
        let mut caretEnd := caretStart
        while caretEnd < trimmed.length && trimmed.get caretEnd == '^' do
          caretEnd := caretEnd + 1

        -- Get the message part after carets
        let afterCarets := trimmed.drop caretEnd |>.trim
        if afterCarets.length > 0 then
          -- Parse level and message
          match afterCarets.splitOn ":" with
          | level :: messageParts =>
            let level := level.trim
            let message := (": ".intercalate messageParts).trim

            -- Calculate column positions (carets are relative to line start including comment spacing)
            let commentPrefix := line.takeWhile (· == ' ' || · == '\t')
            let caretColStart := commentPrefix.length + caretStart
            let caretColEnd := commentPrefix.length + caretEnd

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

    -- Count failed assertions
    let failedCount := results.foldl (fun count r =>
      match r.result with
      | .failed _ => count + 1
      | _ => count
    ) 0

    -- Check if results match expectations
    if failedCount == expectedErrors.size then
      IO.println s!"✓ Test passed: {failedCount} assertion(s) failed as expected"
      -- Print details of expectations
      for exp in expectedErrors do
        IO.println s!"  - Line {exp.line}: {exp.level}: {exp.message}"
    else
      IO.println s!"✗ Test failed: Expected {expectedErrors.size} error(s), but got {failedCount}"
      IO.println s!"\nExpected diagnostics:"
      for exp in expectedErrors do
        IO.println s!"  - Line {exp.line}: {exp.level}: {exp.message}"
      IO.println s!"\nVerification results:"
      IO.println s!"{results}"

#eval! testAssertFalse

end Laurel
