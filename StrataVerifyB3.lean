/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.Program
import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.DDM.Elab

/-!
# B3 Verifier Executable

Command-line tool to verify B3 programs using Z3.

Usage: StrataVerifyB3 <file.b3.st>
-/

def exitFailure {α} (message : String) : IO α := do
  IO.eprintln message
  IO.Process.exit 1

def main (args : List String) : IO Unit := do
  match args with
  | [filepath] => do
      -- Read and parse B3 file
      let bytes ← IO.FS.readBinFile filepath
      let contents ← match String.fromUTF8? bytes with
        | some s => pure s
        | none => exitFailure s!"File {filepath} contains invalid UTF-8"

      let leanEnv ← Lean.mkEmptyEnvironment 0
      let inputContext := Strata.Parser.stringInputContext ⟨filepath⟩ contents

      -- Parse header
      let (header, errors, startPos) := Strata.Elab.elabHeader leanEnv inputContext
      if errors.size > 0 then
        for err in errors do
          IO.eprintln s!"Parse error: {← err.data.toString}"
        IO.Process.exit 1

      -- Ensure it's a program (not dialect definition)
      let .program _ dialectName := header
        | exitFailure "Expected B3 program, got dialect definition"

      -- Load B3CST dialect
      let b3Dialect := Strata.B3CST
      let dialects := Strata.Elab.LoadedDialects.builtin.addDialect! b3Dialect

      -- Verify dialect name matches
      if dialectName != b3Dialect.name then
        exitFailure s!"Expected dialect {b3Dialect.name}, got {dialectName}"

      let .isTrue mem := inferInstanceAs (Decidable (dialectName ∈ dialects.dialects))
        | exitFailure "Internal error: dialect not found after adding"

      -- Parse program
      let prog ← match Strata.Elab.elabProgramRest dialects leanEnv inputContext dialectName mem startPos with
        | .ok program => pure program
        | .error errors =>
            for err in errors do
              IO.eprintln s!"Parse error: {← err.data.toString}"
            IO.Process.exit 1

      -- Convert to B3 AST
      let ast ← match Strata.B3.Verifier.programToB3AST prog with
        | Except.error msg => exitFailure s!"Failed to convert to B3 AST: {msg}"
        | Except.ok ast => pure ast

      -- Verify with Z3
      let solver ← Strata.B3.Verifier.createInteractiveSolver "z3"
      let reports ← Strata.B3.Verifier.verify ast solver

      -- Display results
      for report in reports do
        IO.println s!"\nProcedure: {report.procedureName}"
        for (result, diagnosis) in report.results do
          let marker := if result.result.isError then "✗" else "✓"
          let description := match result.result with
            | .error .counterexample => "counterexample found"
            | .error .unknown => "unknown"
            | .error .refuted => "refuted"
            | .success .verified => "verified"
            | .success .reachable => "reachable"
            | .success .reachabilityUnknown => "reachability unknown"
          IO.println s!"  {marker} {description}"

          -- Show diagnosis if available
          match diagnosis with
          | some diag =>
              if !diag.diagnosedFailures.isEmpty then
                IO.println "  Diagnosed failures:"
                for failure in diag.diagnosedFailures do
                  let formatted := Strata.B3.Verifier.formatExpression prog failure.expression B3.ToCSTContext.empty
                  IO.println s!"    - {formatted}"
          | none => pure ()

  | _ => exitFailure "Usage: StrataVerifyB3 <file.b3.st>"
