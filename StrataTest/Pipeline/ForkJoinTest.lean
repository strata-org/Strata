/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Pipeline.Context

/-! ## `PipelineContext.fork` / `joinForks` tests

A worker that runs on a fork must report what it would report running on the
parent itself, except that it never prints phase lines to stdout:

1. A fork of a `.verbose` context echoes its diagnostics to stderr, and prints
   no `[start]`/`[end]` lines.
2. After `joinForks`, the parent's `--metrics` JSONL has the same shape as a
   sequential run: the enclosing phase still gets its `unattributed` entry, and
   repeated phases aggregated at a fork's root are flushed under the parent's
   phase path.
-/

open Strata.Pipeline

meta def probe : MessageKind := { category := "probe", impact := .internalWarning }

meta def emitOn (ctx : PipelineContext) (msg : String) : IO Unit := do
  let _ ← ((emitMessage probe msg : PipelineM Unit).run ctx).toBaseIO

meta def hasSubstr (s sub : String) : Bool := (s.splitOn sub).length > 1

/-! ### Test 1: a verbose fork echoes diagnostics but prints no phase lines -/

/-- info: echo=true phaseLines=false parentMessages=1 -/
#guard_msgs in
#eval show IO Unit from do
  let parent ← PipelineContext.create (outputMode := .verbose) (profilePipeline := false)
  let fork ← parent.fork
  let (out, ()) ← IO.FS.withIsolatedStreams (isolateStderr := true) do
    fork.withPhase "p" (m := IO) do emitOn fork "hello"
  let msgs ← parent.getMessages
  IO.println s!"echo={hasSubstr out "[internalWarning]"} \
    phaseLines={hasSubstr out "[start]" || hasSubstr out "[end]"} \
    parentMessages={msgs.size}"

/-! ### Test 2: forked and sequential runs emit the same metric phases -/

/-- The `phase` field of a JSONL metric line. -/
meta def phaseOf (line : String) : Option String := do
  let rest ← (line.splitOn "\"phase\":\"")[1]?
  (rest.splitOn "\"").head?

/-- Phases named in the JSONL metrics written while running `body` on a fresh
    quiet context, in order, deduplicated. -/
meta def metricPhases (body : PipelineContext → IO Unit) : IO (List String) :=
  IO.FS.withTempFile fun h path => do
    let ctx ← PipelineContext.create (outputMode := .quiet) (metricsHandle := some h)
    body ctx
    h.flush
    let lines ← IO.FS.lines path
    return (lines.toList.filterMap phaseOf).eraseDups

/-- Work one worker does per obligation: a mode-N phase, and a repeated phase
    directly at the worker's root. -/
meta def obligationWork (ctx : PipelineContext) : IO Unit := do
  ctx.withPhase "writeSMTLib" (m := IO) do IO.sleep 5
  ctx.withRepeatedPhase "evalDischarge" (m := IO) do IO.sleep 5

/--
info: sequential: [vcDischarge.writeSMTLib, vcDischarge.evalDischarge, vcDischarge.unattributed, vcDischarge]
forked: [vcDischarge.writeSMTLib, vcDischarge.evalDischarge, vcDischarge.unattributed, vcDischarge]
-/
#guard_msgs in
#eval show IO Unit from do
  let sequential ← metricPhases fun ctx =>
    ctx.withPhase "vcDischarge" (m := IO) do
      for _ in List.range 2 do obligationWork ctx
  let forked ← metricPhases fun ctx =>
    ctx.withPhase "vcDischarge" (m := IO) do
      let forks ← (List.range 2).mapM fun _ => (ctx.fork : BaseIO _)
      let start ← IO.monoNanosNow
      let tasks ← forks.mapM fun f => IO.asTask (prio := .dedicated) (obligationWork f)
      for t in tasks do let _ ← IO.ofExcept t.get
      ctx.joinForks forks ((← IO.monoNanosNow) - start)
  IO.println s!"sequential: {sequential}"
  IO.println s!"forked: {forked}"

/-! ### Test 3: the parent's `unattributed` is its time outside the worker pool

The parent sleeps 100ms, then two forks each spend 200ms in a phase at the same
time, so `vcDischarge` takes about 300ms and its `unattributed` residual should
be about 100ms. If the parent were credited with the sum of the forks' times
(400ms) instead of the pool's wall-clock span (200ms), the residual would be
`300 - 400`, which truncates to 0; if it were credited with nothing, there
would be no `unattributed` entry at all. The bounds are loose so a loaded build
host does not make the test flaky. -/

/-- The number after `"<field>":` in a JSONL metric line. -/
meta def numField (line field : String) : Option Nat := do
  let rest ← (line.splitOn s!"\"{field}\":")[1]?
  (rest.takeWhile Char.isDigit).toNat?

/-- `end_ms - start_ms` of the first metric line for `phase`. -/
meta def durationMs (lines : Array String) (phase : String) : Option Nat := do
  let line ← lines.find? (phaseOf · == some phase)
  return (← numField line "end_ms") - (← numField line "start_ms")

/-- info: unattributed=present outsidePool=true belowTotal=true -/
#guard_msgs in
#eval show IO Unit from do
  let lines ← IO.FS.withTempFile fun h path => do
    let ctx ← PipelineContext.create (outputMode := .quiet) (metricsHandle := some h)
    ctx.withPhase "vcDischarge" (m := IO) do
      IO.sleep 100
      let forks ← (List.range 2).mapM fun _ => (ctx.fork : BaseIO _)
      let start ← IO.monoNanosNow
      let tasks ← forks.mapM fun f =>
        IO.asTask (prio := .dedicated) (f.withPhase "writeSMTLib" (m := IO) do IO.sleep 200)
      for t in tasks do let _ ← IO.ofExcept t.get
      ctx.joinForks forks ((← IO.monoNanosNow) - start)
    h.flush
    IO.FS.lines path
  let total := (durationMs lines "vcDischarge").getD 0
  match durationMs lines "vcDischarge.unattributed" with
  | none => IO.println "unattributed=missing"
  | some residual =>
    IO.println s!"unattributed=present outsidePool={decide (residual ≥ 50)} \
      belowTotal={decide (residual < total)}"
