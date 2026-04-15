/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.Languages.Core.Core
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.ProgramType
import Strata.Languages.Core.ProgramWF
import Strata.Languages.Core.Verifier
import Strata.Transform.CoreTransform
import Strata.Transform.CallElim
import Strata.Transform.FilterProcedures
import Strata.Transform.PrecondElim
import Strata.Transform.LoopElim
import Strata.Transform.ProcedureInlining

open Core
open Core.Transform
open Strata
open Lambda

/-! ## A place to apply Property-Based Testing: CachedAnalyses validation

Core transformations keeps CachedAnalyses behind the scene because some
analysis results can be too expensive to reconstruct from scratch.

The representative (and only) example is a call graph. Building a call graph
is expensive because it has to traverse the whole instructions of program.

For this reason, transformations have to carefully modify the CallGraph
data struture so that only impacted edges are incrementarily updated.

`Strata/Transform/CoreTransform.lean`

However, this wasn't being seriously tested. We can do property-based testing
because the specification is clear:

**Given a program transformation T and program P,
  the cached call graph after T(P) is equal to the call graph built fresnly
  from the output program T(P).**

Claude generated random 50 `.core.st` programs per pass at
`StrataTest/Transform/CachedAnalysesTestInputs/<pass>/`.
This will do the check.
-/


section CachedAnalysesTest

-- -----------------------------------------------------------------------
-- File I/O helpers and test runners (skip)
-- -----------------------------------------------------------------------

/-- Parse a `.core.st` file into a `Core.Program`. -/
private def parseCoreFile (path : System.FilePath) : IO Core.Program := do
  let text ← IO.FS.readFile path
  let inputCtx := Lean.Parser.mkInputContext text path.toString
  let dctx := Elab.LoadedDialects.builtin
  let dctx := dctx.addDialect! Core
  let leanEnv ← Lean.mkEmptyEnvironment 0
  match Strata.Elab.elabProgram dctx leanEnv inputCtx with
  | .error errors =>
    let msgs ← errors.toList.mapM (·.toString)
    throw (IO.userError s!"Parse error in {path}: {String.intercalate "; " msgs}")
  | .ok pgm =>
    let (program, errs) := Core.getProgram pgm inputCtx
    if errs.isEmpty then
      return program
    else
      throw (IO.userError s!"Translation error in {path}: {errs.toList}")

/-- List all `.core.st` files in a directory, sorted by name. -/
private def listCoreFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  let entries ← dir.readDir
  let files := entries.toList
    |>.filter (fun e => e.fileName.endsWith ".core.st")
    |>.map (fun e => e.path)
  return files.mergeSort (toString · < toString ·)

private def inputDir (pass : String) : System.FilePath :=
  "StrataTest" / "Transform" / "CachedAnalysesTestInputs" / pass

/-- Run a checker on all `.core.st` files in a directory.
    `check` is called with each parsed program and should return
    `.ok true` (pass), `.ok false` (mismatch), or `.error` (transform error). -/
private def runDirBatch (name : String) (dir : System.FilePath)
    (check : Core.Program → Except String Bool) : IO String := do
  let files ← listCoreFiles dir
  let mut passed := 0
  let mut failed := 0
  let mut errored := 0
  for file in files do
    match ← (do let p ← parseCoreFile file; pure (check p)) |>.toBaseIO with
    | .ok (.ok true) => passed := passed + 1
    | .ok (.ok false) => failed := failed + 1
    | .ok (.error _) | .error _ => errored := errored + 1
  return s!"{name}: {passed} passed, {failed} failed, {errored} errored (of {files.length})"


-- -----------------------------------------------------------------------
-- The executable validator
-- -----------------------------------------------------------------------

/-- Check whether a `PipelinePhase` preserves `CachedAnalyses` for program `P`. -/
def checkCachedAnalyses (T : PipelinePhase) (P : Core.Program)
    (baseState : CoreTransformState := .emp) : Except String Bool :=

  -- Step 1. Set up the initial call graph cache
  let initCG := P.toProcedureCG
  let initState : CoreTransformState :=
    { baseState with
      cachedAnalyses := { callGraph := .some initCG } }

  -- Step 2. Run the transformation
  match (T.transform P).run initState with
  | (.ok (_changed, P'), finalState) =>

    -- Step 3. Check the output call graph
    match finalState.cachedAnalyses.callGraph with
    | .some finalCG =>
      let expectedCG := P'.toProcedureCG
      .ok (finalCG.beq expectedCG)
    | .none => .ok false
  | (.error msg, _) => .error msg

/--
info: FilterProcedures: 50 passed, 0 failed, 0 errored (of 50)
CallElim: 50 passed, 0 failed, 0 errored (of 50)
PrecondElim: 50 passed, 0 failed, 0 errored (of 50)
LoopElim: 50 passed, 0 failed, 0 errored (of 50)
ProcedureInlining: 50 passed, 0 failed, 0 errored (of 50)
-/
#guard_msgs in
#eval do
  let precondState : CoreTransformState :=
    { CoreTransformState.emp with factory := .some Core.Factory }
  let tests : Array (String × (Core.Program → Except String Bool)) := #[
    ("FilterProcedures", fun p =>
      let firstProc := p.decls.filterMap (fun d =>
        match d with | Decl.proc proc _ => some (CoreIdent.toPretty proc.header.name) | _ => none)
      let targets := match firstProc with | [] => [] | h :: _ => [h]
      checkCachedAnalyses (filterProceduresPipelinePhase targets) p),
    ("CallElim",            fun p => checkCachedAnalyses callElimPipelinePhase p),
    ("PrecondElim",         fun p => checkCachedAnalyses precondElimPipelinePhase p precondState),
    ("LoopElim",            fun p => checkCachedAnalyses loopElimPipelinePhase p),
    ("ProcedureInlining",   fun p => checkCachedAnalyses (procedureInliningPipelinePhase {}) p)
  ]
  let results ← tests.mapM fun (name, check) =>
    runDirBatch name (inputDir name) check
  IO.println (String.intercalate "\n" results.toList)



/-- The property-based testing version for CallElim! -/
theorem callElimPreservesCachedAnalyses (P P' : Core.Program)
    (changed : Bool) (finalState : CoreTransformState)
    (baseState : CoreTransformState := .emp)
    (hRun : (callElimPipelinePhase.transform P).run
      { baseState with cachedAnalyses := { callGraph := .some (P.toProcedureCG) } }
      = (.ok (changed, P'), finalState)) :
    finalState.cachedAnalyses.callGraph = .some (P'.toProcedureCG) := by
  -- sorry!
  sorry


end CachedAnalysesTest
