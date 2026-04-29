/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
import Strata.Transform.ProcedureInlining

public section

namespace Core

/-- Which procedures to verify: all user procedures, only roots,
    or only the main function. -/
inductive EntryPoint where
  /-- Only `__main__` -/
  | main
  /-- User procedures not reachable from other user procedures (handles SCCs
      by choosing the alphabetically smallest member as representative) -/
  | roots
  /-- All user procedures -/
  | all
  deriving Repr, DecidableEq

instance : Inhabited EntryPoint where
  default := .roots

def EntryPoint.ofString? (s : String) : Option EntryPoint :=
  match s with
  | "main" => some .main
  | "roots" => some .roots
  | "all" => some .all
  | _ => none

def EntryPoint.options : String :=
  "'main' (main function only), 'roots' (user procs not reachable from others), or 'all' (all user procs)"

/-- Determine which procedures to verify based on the entry-point mode.
    - `.main`: only `__main__`
    - `.roots`: user procedures not reachable from other user procedures,
      or for those mutually recursive, the representative user procedures
      chosen by their alphabetically smallest member.
    - `.all`: all user procedures -/
private def determineProceduresToVerify
    (coreProgram : Program) (userProcNames : List String)
    (entryPoint : EntryPoint) : List String :=
  match entryPoint with
  | .main => ["__main__"]
  | .all => userProcNames
  | .roots =>
    let cg := coreProgram.toProcedureCG
    let userSet := Std.HashSet.ofList userProcNames
    (cg.computeRoots (preferredRoots := userProcNames)).filter userSet.contains

/-- Choose the entry procedures to verify and build the corresponding inline
    phases for bug-finding mode. Returns `(proceduresToVerify, inlinePhases)`. -/
def chooseEntryProceduresAndBuildInlinePhases
    (coreProgram : Program) (userProcNames : List String)
    (entryPoint : EntryPoint)
    : (List String) × PipelinePhase :=
  let proceduresToVerify := determineProceduresToVerify coreProgram userProcNames entryPoint
  let entrySet := Std.HashSet.ofList proceduresToVerify
  let inlinePhases : PipelinePhase :=
    procedureInliningPipelinePhase
      { doInline := fun caller callee a =>
          (match caller with | some c => entrySet.contains c | none => false)
          && doInlineNonRecursive callee a
        maxIters := some 10 }
  (proceduresToVerify, inlinePhases)

end Core
