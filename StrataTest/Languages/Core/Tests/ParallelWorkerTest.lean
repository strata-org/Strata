/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)
open Strata.Pipeline (PipelineContext)

/-! ## Test: parallel solver workers do not share mutable state unsafely

`parallelWorkers > 1` runs several worker tasks in one process. These tests run
the full `Core.verify` pipeline against a real solver and pin
what the workers must and must not share with each other and with the caller:

* The obligation counter is shared, and each claim of a number is atomic, so
  every obligation gets its own SMT query file even when labels repeat.
* Each worker gets a `PipelineContext.fork` of the caller's context, so what a
  discharge function emits (diagnostics, JSONL metrics) still reaches the caller
  and carries the caller's phase path (`vcDischarge`).
-/

namespace Strata

/-- Eight obligations that all carry the label `same`; the odd ones fail. A
    shared label is what makes a duplicated counter value collide on a file
    name (`same_<n>.smt2`). Each goes through an uninterpreted `f` so the
    solver, not the partial evaluator, decides it. -/
private def sameLabelProgram : Program :=
#strata
program Core;
function f (x : int) : int;
procedure P0() { assume [h]: f(0) == 0; assert [same]: 0 == f(0); };
procedure P1() { assume [h]: f(1) == 1; assert [same]: f(1) == 0; };
procedure P2() { assume [h]: f(2) == 2; assert [same]: 2 == f(2); };
procedure P3() { assume [h]: f(3) == 3; assert [same]: f(3) == 0; };
procedure P4() { assume [h]: f(4) == 4; assert [same]: 4 == f(4); };
procedure P5() { assume [h]: f(5) == 5; assert [same]: f(5) == 0; };
procedure P6() { assume [h]: f(6) == 6; assert [same]: 6 == f(6); };
procedure P7() { assume [h]: f(7) == 7; assert [same]: f(7) == 0; };
#end

private def parallelOptions (dir : System.FilePath) : Core.VerifyOptions :=
  { Core.VerifyOptions.quiet with parallelWorkers := 4, vcDirectory := some dir }

/-! ### Every obligation gets its own query file

`vcDirectory` keeps the files (`verifyProgram` otherwise deletes its temp dir).
With a racy counter two obligations can get the same number, write the same
file and solve each other's query; then fewer than eight files survive and a
failing obligation can be reported as passing. -/
/-- info: files=8 passed=4 failed=4 -/
#guard_msgs in
#eval show IO Unit from do
  IO.FS.withTempDir fun dir => do
    let results ← Core.verify sameLabelProgram (options := parallelOptions dir)
    let files := (← dir.readDir).filter (·.path.extension == some "smt2")
    let passed := (results.filter (·.isSuccess)).size
    let failed := (results.filter (·.isNotSuccess)).size
    IO.println s!"files={files.size} passed={passed} failed={failed}"

/-! ### Worker diagnostics and metrics reach the caller

A discharge function that emits one warning per obligation, through the
`PipelineContext` it is handed, then defers to the default backend so the
`runSolver` phase runs and records a timing metric. -/
private def warnThenDischarge : Core.MkDischargeFn :=
  fun options counter tempDir vars md label termCache captured pctx =>
    fun assumptions obligation ctx sat valid varDefs varDecls => do
      let warn : Pipeline.PipelineM Unit :=
        Pipeline.emitMessage { category := "probe", impact := .internalWarning } label
      let _ ← (warn.run pctx).toBaseIO
      Core.mkDischargeFn options counter tempDir vars md label termCache captured pctx
        assumptions obligation ctx sat valid varDefs varDecls

/-- info: messages=8 tagged=8 runSolverMetrics=8 -/
#guard_msgs in
#eval show IO Unit from do
  IO.FS.withTempDir fun dir => do
    let metricsPath := dir / "metrics.jsonl"
    let pctx ← IO.FS.withFile metricsPath .write fun h => do
      let pctx ← PipelineContext.create (outputMode := .quiet) (metricsHandle := some h)
      let _ ← Core.verify sameLabelProgram (options := parallelOptions (dir / "vcs"))
        (mkDischarge := warnThenDischarge) (pipelineCtx := some pctx)
      pure pctx
    let msgs := (← pctx.getMessages).filter (·.kind.category == "probe")
    let tagged := (msgs.filter (·.phase.display == "vcDischarge")).size
    let metrics ← IO.FS.lines metricsPath
    let runSolver := (metrics.filter fun l =>
      (l.splitOn "\"phase\":\"vcDischarge.runSolver\"").length > 1).size
    IO.println s!"messages={msgs.size} tagged={tagged} runSolverMetrics={runSolver}"

/-! ### Concurrent runs sharing a directory each get their own verdicts

Two programs whose obligations carry the same labels, so both runs name their query files
`same_0.smt2` to `same_3.smt2`: every obligation of the first holds and every one of the second
fails. They are verified at the same time, several times over, into one `vcDirectory`. A run
that solved the other's query would report a verdict of the other program. -/

/-- Four obligations labeled `same` that hold. -/
private def sameLabelPasses : Program :=
#strata
program Core;
function g (x : int) : int;
procedure Q0() { assume [h]: g(0) == 0; assert [same]: g(0) == 0; };
procedure Q1() { assume [h]: g(1) == 1; assert [same]: g(1) == 1; };
procedure Q2() { assume [h]: g(2) == 2; assert [same]: g(2) == 2; };
procedure Q3() { assume [h]: g(3) == 3; assert [same]: g(3) == 3; };
#end

/-- Four obligations labeled `same` that fail. -/
private def sameLabelFails : Program :=
#strata
program Core;
function g (x : int) : int;
procedure Q0() { assume [h]: g(0) == 0; assert [same]: g(0) == 1; };
procedure Q1() { assume [h]: g(1) == 1; assert [same]: g(1) == 2; };
procedure Q2() { assume [h]: g(2) == 2; assert [same]: g(2) == 3; };
procedure Q3() { assume [h]: g(3) == 3; assert [same]: g(3) == 4; };
#end

/-- info: passing run: 32 of 32 passed; failing run: 32 of 32 failed; leftover hidden files: 0 -/
#guard_msgs in
#eval show IO Unit from do
  IO.FS.withTempDir fun dir => do
    let options := { Core.VerifyOptions.quiet with vcDirectory := some dir }
    let mut passed := 0
    let mut failed := 0
    for _ in [0:8] do
      let a ← IO.asTask (Core.verify sameLabelPasses (options := options))
      let b ← IO.asTask (Core.verify sameLabelFails (options := options))
      let ra ← IO.ofExcept a.get
      let rb ← IO.ofExcept b.get
      passed := passed + (ra.filter (·.isSuccess)).size
      failed := failed + (rb.filter (·.isFailure)).size
    let hidden := (← dir.readDir).filter (·.fileName.startsWith ".")
    IO.println s!"passing run: {passed} of 32 passed; failing run: {failed} of 32 failed; \
      leftover hidden files: {hidden.size}"

end Strata
