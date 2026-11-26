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
    or only the main function. In every mode, each opaque user procedure with a body is verified
    on its own too, since its callers know it only through its contract.

    This is the *verifier's* entry-point selector — it decides which
    procedures the SMT verifier targets. It has no relation to the
    concrete-interpreter entry marker (`Procedure.isInterpretEntry` /
    `Imperative.MetaData.interpretEntry` / `Program.runEntry` /
    `Program.entryProcedures`), which is a distinct notion introduced for
    `laurelInterpret`. -/
inductive EntryPoint where
  /-- `__main__`, and every opaque user procedure with a body -/
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
  "'main' (main function only), 'roots' (user procs not reachable from others), or 'all' (all user procs); \
    every opaque user proc with a body is verified too"

/-- The user procedures `userProcNames` of `coreProgram` that are opaque and have a body
    (`Body.isOpaqueWithBody`), in the order of `userProcNames`. A caller knows such a
    procedure only through its contract, so inlining it into a caller does not check its body,
    and it must be verified on its own. -/
private def opaqueUserProcsWithBody (coreProgram : Program) (userProcNames : List String) :
    List String :=
  let opaqueNames := Std.HashSet.ofList <| coreProgram.decls.filterMap fun d => match d with
    | .proc p _ => if p.body.isOpaqueWithBody then some p.header.name.name else none
    | _ => none
  userProcNames.filter opaqueNames.contains

/-- Determine which procedures to verify based on the entry-point mode. In every mode, each
    user procedure that is opaque and has a body is verified too (`opaqueUserProcsWithBody`).
    - `.main`: `__main__`
    - `.roots`: user procedures not reachable from other user procedures,
      or for those mutually recursive, the representative user procedures
      chosen by their alphabetically smallest member.
    - `.all`: all user procedures -/
private def determineProceduresToVerify
    (coreProgram : Program) (userProcNames : List String)
    (entryPoint : EntryPoint) : List String :=
  let entries := match entryPoint with
    | .main => ["__main__"]
    | .all => userProcNames
    | .roots =>
      let cg := coreProgram.toProcedureCG
      let userSet := Std.HashSet.ofList userProcNames
      (cg.computeRoots (preferredRoots := userProcNames)).filter userSet.contains
  let entrySet := Std.HashSet.ofList entries
  entries ++ (opaqueUserProcsWithBody coreProgram userProcNames).filter (!entrySet.contains ·)

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
