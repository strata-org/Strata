/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataTest.Util.TestDiagnostics
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
meta import StrataDDM.Util.IO
meta import Strata.Languages.Laurel.Grammar.LaurelGrammar
meta import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
meta import Strata.Languages.Laurel.LaurelCompilationPipeline

/-!
# `verifyToMetrics` plumbing test

Exercises `verifyToMetrics`, which re-exposes data the existing verify wrappers
discard: the pass-side `Statistics` (dropped by the thin `translate` wrapper) and
the per-obligation verdicts. This is the first executable step of the
polymorphism differential-harness, buildable on the current branch with no Core change.

Hard-asserted (throw on regression): translation succeeds, VCs are produced
(`numVCs > 0`), exactly one obligation fails (`numFailures == 1`), `coreStats` is
non-empty, and `vcDischargeMs` is present. The per-obligation verdicts and the
re-surfaced `passStats` are rendered into the printed summary for inspection but are
NOT asserted here — `passStats` is empty for this trivial program (no stat-recording
pass fires), and the verdict surface is covered by `VerifyMetricsCorpusTest`'s
serialize/diff path.
-/

meta section

open StrataTest.Util
open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)
open Lean.Parser (InputContext)

namespace Strata.Laurel

/-- Parse a Laurel source string and run `verifyToMetrics` on it. -/
def metricsOf (input : InputContext) : IO VerifyMetrics := do
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name input
  let uri := Strata.Uri.file input.fileName
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error transErrors => throw (IO.userError s!"Translation errors: {transErrors}")
  | .ok laurelProgram => Laurel.verifyToMetrics laurelProgram default

/-- A tiny program with one passing obligation and one failing obligation, so
    the verdict surface is non-trivial. -/
def metricsProgram := r"
procedure passes()
  opaque
{
    assert 1 + 1 == 2
};

procedure fails()
  opaque
{
    assert 1 + 1 == 3
};
"

/-- #1349 guard-confirmation scenario (cherry-picked onto this branch):
    datatype `==`/`!=` inside a *heap-writing* procedure. The `new C` makes `cmp`
    a heap writer, so `HeapParameterization` descends into the body and reaches
    the equality arm. Without the `isDatatype` guard this fails Core type checking
    (`Impossible to unify (arrow Composite int) …`); with the guard, datatype
    equality falls through to structural comparison and both asserts verify. -/
def datatypeEqHeapProgram := r"
composite C { var x: int }
datatype Pair { MkPair(a: int, b: int) }

procedure cmpEq()
  opaque
{
    var c: C := new C;
    var p1: Pair := MkPair(1, 2);
    var p2: Pair := MkPair(1, 2);
    assert p1 == p2
};

procedure cmpNeq()
  opaque
{
    var c: C := new C;
    var p1: Pair := MkPair(1, 2);
    var p2: Pair := MkPair(3, 4);
    assert p1 != p2
};
"

/-- Render one obligation outcome as pass / fail / error. Mirrors
    `VCResult.isSuccess`: a query can complete (`Except.ok`) yet the obligation
    be invalid (`o.isPass = false`), so the `Except` tag alone is NOT the verdict. -/
def renderOutcome (outcome : Except Core.VCError Core.VCOutcome) : String :=
  match outcome with
  | .ok o => if o.isPass then "pass" else "fail"
  | .error _ => "error"

/-- Report a compact, deterministic summary of the surfaced metrics. -/
def summarizeMetrics (m : VerifyMetrics) : String :=
  let verdictLine := m.verdicts.foldl
    (fun acc (label, outcome) => acc ++ s!"  {label}: {renderOutcome outcome}\n") ""
  s!"translated: {m.translated}\n" ++
  s!"numVCs: {m.numVCs}\n" ++
  s!"numFailures: {m.numFailures}\n" ++
  s!"passStats keys: {m.passStats.data.size}\n" ++
  s!"coreStats keys: {m.coreStats.data.size}\n" ++
  s!"vcDischargeMs present: {m.vcDischargeMs.isSome}\n" ++
  s!"verdicts:\n{verdictLine}"

/-- Run the harness on the sample program, print the summary, then hard-assert the
    checkable signals: translation succeeded, VCs were produced, exactly one
    obligation failed, `coreStats` is non-empty, and `vcDischargeMs` is present.
    The verdict surface and `passStats` appear in the printed summary only (see the
    module doc for why neither is asserted here). -/
def runMetricsTest : IO Unit := do
  let input := StrataDDM.Parser.stringInputContext "VerifyMetrics" metricsProgram
  let m ← metricsOf input
  IO.println (summarizeMetrics m)
  -- Hard assertions (throw on regression) independent of the printed surface.
  unless m.translated do throw (IO.userError "expected translation to succeed")
  unless m.numVCs > 0 do throw (IO.userError "expected at least one VC")
  -- The discriminating check: the failing obligation is detected as a failure
  -- even though its SMT query completed (Except.ok). This is exactly the
  -- verdict signal the differential harness compares across solutions.
  unless m.numFailures == 1 do throw (IO.userError s!"expected exactly 1 failure, got {m.numFailures}")
  -- Note: `passStats` is now SURFACED (previously discarded by `translate`); its
  -- emptiness is program-dependent (this trivial program triggers no stat-
  -- recording passes), so we assert the field is reachable, not that it is full.
  -- `coreStats` carries the evaluator statistics (numObligations, ITE-branch
  -- divergence, …) that `Core.verify` discarded. A real verification run populates
  -- them, so non-empty here confirms the Core-side plumbing.
  unless m.coreStats.data.size > 0 do
    throw (IO.userError "expected non-empty coreStats (Core-stats plumbing)")
  -- The vcDischarge wall-clock is consumed from the pipeline's existing per-phase
  -- metrics. A real (non-checkOnly) run emits the record, so it must be present
  -- here — confirms the metricsHandle threading works.
  unless m.vcDischargeMs.isSome do
    throw (IO.userError "expected vcDischargeMs (timing plumbing)")

#guard_msgs (drop info, error) in
#eval runMetricsTest

/-- Guard-confirmation: the #1349 cherry-pick makes datatype `==`/`!=` inside a
    heap-writing procedure verify. Both obligations must PASS (zero failures);
    without the guard they would not even translate. This is the harness's first
    real use — confirming a cherry-picked dependency did what it claimed. -/
def runDatatypeEqGuardTest : IO Unit := do
  let input := StrataDDM.Parser.stringInputContext "DatatypeEqHeap" datatypeEqHeapProgram
  let m ← metricsOf input
  IO.println (summarizeMetrics m)
  unless m.translated do
    throw (IO.userError "guard missing? datatype == in heap-writer failed to translate")
  unless m.numVCs > 0 do throw (IO.userError "expected VCs from the heap-writer procs")
  -- The guard's payload: structural datatype equality verifies — zero failures.
  -- Without #1349 these would fail Core type checking (no clean verdict at all).
  unless m.numFailures == 0 do
    throw (IO.userError s!"expected 0 failures (structural datatype eq), got {m.numFailures}")

#guard_msgs (drop info, error) in
#eval runDatatypeEqGuardTest

end Strata.Laurel
