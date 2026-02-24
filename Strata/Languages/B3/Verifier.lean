/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.ToCore
import Strata.Languages.B3.Format
import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.Conversion
import Strata.Languages.Core.CoreSMT
import Strata.DL.SMT.Solver

open Strata
open Strata.SMT

/-!
# B3 Verifier

Converts B3 programs to Core and verifies them using the CoreSMT verifier.
-/

namespace B3.Verifier

/-- Parse DDM program to B3 AST -/
def programToB3AST (prog : Program) : Except String (B3AST.Program SourceRange) := do
  let [op] ← pure prog.commands.toList
    | .error "Expected single program command"
  if op.name.name != "command_program" then
    .error s!"Expected command_program, got {op.name.name}"
  let [ArgF.op progOp] ← pure op.args.toList
    | .error "Expected single program argument"
  let cstProg ← B3CST.Program.ofAst progOp
  let (ast, errors) := B3.programFromCST B3.FromCSTContext.empty cstProg
  if !errors.isEmpty then
    .error s!"CST to AST conversion errors: {errors}"
  else
    .ok ast

-- Minimal type stubs for B3 verifier API compatibility
structure VerificationReport where
  label : String
  outcome : Core.Outcome
  deriving Repr

structure ProcedureReport where
  procedureName : String
  results : List (VerificationReport × Option Unit)
  deriving Repr

/-- Convert Core VCResult to B3 VerificationReport -/
private def vcResultToVerificationReport (vcResult : Core.VCResult) : VerificationReport :=
  { label := vcResult.obligation.label
    outcome := vcResult.result }

/-- Convert B3 program to Core and verify via CoreSMT pipeline -/
def programToSMT (prog : B3AST.Program SourceRange) (solver : Solver) : IO (List ProcedureReport) := do
  let convResult := B3.ToCore.convertProgram prog
  if !convResult.errors.isEmpty then
    let msg := convResult.errors.map toString |> String.intercalate "\n"
    throw (IO.userError s!"Conversion errors:\n{msg}")
  let coreStmts := convResult.value
  let solverInterface ← SMT.mkCvc5Solver
  let config : Core.CoreSMT.CoreSMTConfig := { accumulateErrors := true }
  let state := Core.CoreSMT.CoreSMTState.init solverInterface config
  let (_, _, results) ← Core.CoreSMT.verify state Core.Env.init coreStmts
  let reports := results.map vcResultToVerificationReport
  return [{ procedureName := "main", results := reports.map (·, none) }]

def programToSMTWithoutDiagnosis (prog : B3AST.Program SourceRange) (solver : Solver) : IO (List (Except String VerificationReport)) := do
  let reports ← programToSMT prog solver
  return reports.flatMap (fun r => r.results.map (fun (vr, _) => .ok vr))

end B3.Verifier

