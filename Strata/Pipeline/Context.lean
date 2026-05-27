/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages
import Lean.Data.Json.Printer
import all StrataDDM.Util.String

namespace Strata.Pipeline

/-- Print to stdout and flush. -/
def printlnFlush (msg : String) : BaseIO Unit := do
  let _ ← (do IO.println msg; (← IO.getStdout).flush : IO Unit).toBaseIO

/-- Output verbosity mode for the pipeline. -/
public inductive OutputMode where
  | quiet
  | default
  | profile
  | verbose
  deriving BEq, DecidableEq, Repr

/-- Aggregated data for a single repeated phase (recursive for arbitrary nesting). -/
structure RepeatedPhaseData where
  count : Nat
  totalNs : Nat
  /-- Aggregated timings for nested subphases, in first-seen order. -/
  children : Array (String × RepeatedPhaseData) := #[]
  deriving Inhabited

namespace RepeatedPhaseData

/-- Merge `incoming` children into `existing`, summing counts/totals for
    matching names and recursively merging their children. -/
partial def mergeChildren (existing incoming : Array (String × RepeatedPhaseData))
    : Array (String × RepeatedPhaseData) :=
  incoming.foldl (init := existing) fun acc (name, data) =>
    match acc.findIdx? (·.1 == name) with
    | some idx =>
      let (_, prev) := acc[idx]!
      acc.modify idx fun _ => (name, {
        count := prev.count + data.count,
        totalNs := prev.totalNs + data.totalNs,
        children := mergeChildren prev.children data.children })
    | none => acc.push (name, data)

end RepeatedPhaseData

/-- Upsert a repeated phase entry: find by name in the array, merge elapsed
    and children, or append a new entry. -/
def addRepeatedEntry (arr : Array (String × RepeatedPhaseData))
    (name : String) (elapsed : Nat) (children : Array (String × RepeatedPhaseData))
    : Array (String × RepeatedPhaseData) :=
  match arr.findIdx? (·.1 == name) with
  | some idx =>
    let (_, prev) := arr[idx]!
    arr.modify idx fun _ => (name, {
      count := prev.count + 1,
      totalNs := prev.totalNs + elapsed,
      children := RepeatedPhaseData.mergeChildren prev.children children })
  | none => arr.push (name, { count := 1, totalNs := elapsed, children })

/-- Per-phase scoped state: saved on phase entry, restored on exit.
    Bundled into a single ref to ensure atomic save/restore. -/
structure PhaseState where
  repeatedPhases : Array (String × RepeatedPhaseData) := #[]
  messageCounts : Std.HashMap String Nat := {}
  deriving Inhabited

/-- Pipeline context carrying immutable config and mutable state as individual IORefs.
    This design allows any monad with BaseIO access to use pipeline capabilities
    by passing a PipelineContext value directly.

    **Phase tracking state machine:**

    The phase system operates in two modes controlled by `repeatedDepthRef`:
    - Mode N (normal, depth = 0): `withPhase` records individual timing entries
      and prints `[start]`/`[end]` in profile mode.
    - Mode R (repeated, depth > 0): `withPhase` silently aggregates timing into
      `phaseStateRef.repeatedPhases` — no print, no individual `timingRef` entry.

    `withRepeatedPhase` increments `repeatedDepthRef` on entry and decrements on
    exit.  `withPhase` never changes the depth.

    **Invariants:**
    - `currentPhaseRef` always reflects the innermost active scope's full path.
    - `phaseStateRef` is scoped: saved on entry, restored on exit of both
      `withPhase` and `withRepeatedPhase` — no cross-scope leakage.
    - In mode R, all timing flows through `phaseStateRef.repeatedPhases` only;
      `timingRef` is not touched until the enclosing mode-N `withPhase` flushes.

    **Thread safety:** PipelineContext is NOT thread-safe.  The phase-tracking
    refs assume single-threaded sequential access.  Concurrent `withPhase` or
    `withRepeatedPhase` calls on the same context will corrupt state. -/
public structure PipelineContext where
  private mk ::
  outputMode : OutputMode
  private pipelineStartTime : Nat
  private profilePipeline : Bool := true
  private messagesRef : IO.Ref (Array PipelineMessage)
  private toolErrorsRef : IO.Ref (Array PipelineMessage)
  private userCodeErrorsRef : IO.Ref (Array PipelineMessage)
  /-- Full path of the innermost active phase. Managed via `push`/`pop`
      by `withPhase` and `withRepeatedPhase` — `emitMessage` stamps this
      on each diagnostic. -/
  private currentPhaseRef : IO.Ref Phase
  /-- Nesting depth of `withRepeatedPhase` scopes. When > 0, `withPhase`
      aggregates silently instead of recording individual timing entries. -/
  private repeatedDepthRef : IO.Ref Nat
  /-- Per-phase scoped state (repeated subphases + message counts).
      Saved and cleared on phase entry, restored on exit — each phase
      sees only its own data. -/
  private phaseStateRef : IO.Ref PhaseState
  /-- Caller-owned handle for JSONL metrics. The pipeline appends and flushes
      per record but does not open or close the handle. -/
  private metricsHandle : Option IO.FS.Handle := none

namespace PipelineContext

/-- Create a fresh PipelineContext with new state refs. -/
public def create
    (outputMode : OutputMode := .default)
    (profilePipeline : Bool := true)
    (metricsHandle : Option IO.FS.Handle := none) : BaseIO PipelineContext := do
  let startTime ← IO.monoNanosNow
  let messagesRef ← IO.mkRef (α := Array PipelineMessage) #[]
  let toolErrorsRef ← IO.mkRef (α := Array PipelineMessage) #[]
  let userCodeErrorsRef ← IO.mkRef (α := Array PipelineMessage) #[]
  let currentPhaseRef ← IO.mkRef (α := Phase) default
  let repeatedDepthRef ← IO.mkRef 0
  let phaseStateRef ← IO.mkRef (α := PhaseState) {}
  return { outputMode, pipelineStartTime := startTime, profilePipeline,
           messagesRef, toolErrorsRef, userCodeErrorsRef,
           currentPhaseRef, repeatedDepthRef, phaseStateRef, metricsHandle }

/-- All accumulated pipeline messages. -/
public def getMessages (ctx : PipelineContext) : BaseIO (Array PipelineMessage) :=
  ctx.messagesRef.get

/-- Messages with `.internalError` or `.configurationError` impact.
    These represent tool bugs or invalid invocations that we must fix. -/
public def getToolErrors (ctx : PipelineContext) : BaseIO (Array PipelineMessage) :=
  ctx.toolErrorsRef.get

/-- Messages with `.userCodeIssue` impact.
    These represent definite errors in the user's Python source code. -/
public def getUserCodeErrors (ctx : PipelineContext) : BaseIO (Array PipelineMessage) :=
  ctx.userCodeErrorsRef.get

/-- Write a JSONL metric record to the metrics file (if open) and flush. -/
public def emitMetric (ctx : PipelineContext) (json : Lean.Json) : BaseIO Unit := do
  if let some h := ctx.metricsHandle then
    let _ ← (do h.putStrLn json.compress; h.flush : IO Unit).toBaseIO

/-- Get elapsed nanoseconds since pipeline start. -/
public def elapsedNs (ctx : PipelineContext) : BaseIO Nat := do
  let now ← IO.monoNanosNow
  return now - ctx.pipelineStartTime

/-- Common entry logic for `withPhase`: push the subphase name onto
    `currentPhaseRef`, save and clear scoped phase state. -/
def enterPhase (ctx : PipelineContext) (name : String)
    : BaseIO PhaseState := do
  ctx.currentPhaseRef.modify (·.subphase name)
  ctx.phaseStateRef.modifyGet fun ps => (ps, {})

/-- Recursively print `[profile]` lines and emit JSONL metrics for aggregated
    repeated phases. `parentPhase` is the phase under which these entries
    are nested. -/
partial def flushRepeatedEntries (ctx : PipelineContext)
    (parentPhase : Phase) (entries : Array (String × RepeatedPhaseData))
    : BaseIO Unit := do
  if entries.isEmpty then return
  let childIndent := String.replicate (parentPhase.depth * 2) ' '
  for (name, data) in entries do
    let subphase := parentPhase.subphase name
    if ctx.outputMode == .profile || ctx.outputMode == .verbose then
      let avg := if data.count > 0 then nsToMs (data.totalNs / data.count) else 0
      let timeSuffix :=
        if ctx.profilePipeline then
          s!" (×{data.count}, total: {nsToMs data.totalNs}ms, avg: {avg}ms)"
        else
          ""
      printlnFlush s!"{childIndent}[profile] {name}{timeSuffix}"
    ctx.emitMetric (Lean.Json.mkObj [
      ("type", .str "timing"), ("phase", .str subphase.display),
      ("start_ms", .num 0), ("end_ms", .num (nsToMs data.totalNs)),
      ("count", .num data.count)])
    flushRepeatedEntries ctx subphase data.children

/-- Mode-N entry: print [start] and return the start time. -/
def enterPhaseNormal (ctx : PipelineContext) : BaseIO Nat := do
  let phase ← ctx.currentPhaseRef.get
  let startNs ← ctx.elapsedNs
  if ctx.outputMode == .profile || ctx.outputMode == .verbose then
    let indent := String.replicate ((phase.depth - 1) * 2) ' '
    let timeSuffix := if ctx.profilePipeline then s!" (time: {nsToMs startNs}ms)" else ""
    printlnFlush s!"{indent}[start] {phase.leaf}{timeSuffix}"
  return startNs

/-- End the current phase in mode N: flush aggregated repeated subphases,
    emit timing metric, print [end]/[warnings], then pop phase and restore state. -/
def exitPhaseNormal (ctx : PipelineContext)
    (saved : PhaseState) (startNs : Nat) : BaseIO Unit := do
  let currentPhase ← ctx.currentPhaseRef.modifyGet fun p => (p, p.pop)
  let ps ← ctx.phaseStateRef.modifyGet fun ps => (ps, saved)
  flushRepeatedEntries ctx currentPhase ps.repeatedPhases
  let now ← ctx.elapsedNs
  ctx.emitMetric (Lean.Json.mkObj [
    ("type", .str "timing"),
    ("phase", .str currentPhase.display),
    ("start_ms", .num (nsToMs startNs)),
    ("end_ms", .num (nsToMs now))])
  if ctx.outputMode == .profile || ctx.outputMode == .verbose then
    let indent := String.replicate ((currentPhase.depth - 1) * 2) ' '
    let timeSuffix := if ctx.profilePipeline then s!" (time: {nsToMs now}ms)" else ""
    printlnFlush s!"{indent}[end] {currentPhase.leaf}{timeSuffix}"
    unless ps.messageCounts.isEmpty do
      let parts := ps.messageCounts.toArray.map fun (cat, n) => s!"{n} {cat}"
      let summary := String.intercalate ", " parts.toList
      printlnFlush s!"{indent}[warnings] {currentPhase.leaf}: {summary}"

/-- Mode-R exit for `withPhase`: accumulate elapsed time and nested children
    into the saved repeated-phases array, then pop phase and restore state. -/
def exitPhaseRepeated (ctx : PipelineContext)
    (saved : PhaseState) (startNs : Nat) : BaseIO Unit := do
  let now ← IO.monoNanosNow
  let elapsed := now - startNs
  let currentPhase ← ctx.currentPhaseRef.modifyGet fun p => (p, p.pop)
  ctx.phaseStateRef.modify fun ps =>
    let children := ps.repeatedPhases
    { saved with
      repeatedPhases :=
        addRepeatedEntry saved.repeatedPhases currentPhase.leaf elapsed children }

/-- Run an action as a named subphase of the current phase.
    Nesting is determined by call structure — at the root the phase is
    top-level, inside another `withPhase` it becomes a child.

    Outside a repeated phase: pushes a timing entry to `timingRef`,
    prints `[start]`/`[end]` in profile/verbose mode, and flushes any
    aggregated repeated subphases on exit.

    Inside a repeated phase (i.e. the action may run many times):
    silently accumulates elapsed time into the enclosing
    `repeatedPhasesRef`.  No print, no individual timing entry. -/
@[noinline]
public def withPhase {m α} [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (ctx : PipelineContext) (name : String) (action : m α) : m α := do
  let inRepeatedCnt ← ctx.repeatedDepthRef.get (m := BaseIO)
  if inRepeatedCnt > 0 then
    let saved ← ctx.enterPhase name
    let startNs ← IO.monoNanosNow
    try
      action
    finally
      ctx.exitPhaseRepeated saved startNs
  else
    let saved ← ctx.enterPhase name
    let startNs ← ctx.enterPhaseNormal
    try
      action
    finally
      ctx.exitPhaseNormal saved startNs

/-- Run an action as a repeated subphase. Instead of recording individual
    timing entries, accumulates count and total duration into the parent's
    repeated-phases array. When the parent phase ends, the aggregated results
    are flushed as single timing entries. Silent per-iteration.

    Sets `currentPhaseRef` so nested `emitMessage` calls get the correct
    phase tag.  Increments `repeatedDepthRef` so nested `withPhase` calls
    aggregate silently.  Saves/restores `phaseStateRef` for child
    isolation. -/
@[noinline]
public def withRepeatedPhase {m α} [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (ctx : PipelineContext) (name : String) (action : m α) : m α := do
  let saved ← ctx.enterPhase name
  ctx.repeatedDepthRef.modify (m := BaseIO) (· + 1)
  let startNs ← IO.monoNanosNow
  try
    action
  finally
    ctx.repeatedDepthRef.modify (m := BaseIO) (· - 1)
    ctx.exitPhaseRepeated saved startNs

/-- Time a pure expression as a repeated subphase. The `@[noinline]`
    attribute prevents the compiler from hoisting `expr` outside the
    timing window. Use this instead of `withRepeatedPhase` when the work
    being timed is a pure (non-monadic) expression. -/
@[noinline]
public def withRepeatedPhasePure {α} (ctx : PipelineContext) (name : String)
    (expr : Unit → α) : BaseIO α := do
  ctx.withRepeatedPhase (m := ReaderT Unit BaseIO) name (pure ∘ expr) ()

end PipelineContext

/-- The pipeline monad: a reader over PipelineContext with EIO Unit.
    Computations accumulate diagnostic messages in PipelineContext.messagesRef.
    `emitMessageAndAbort` throws `()` to abort, but multiple messages (including
    multiple error-impact messages) may accumulate before or across aborts.
    The caller of `PipelineM.run` is responsible for inspecting the accumulated
    messages and the outcome to determine the appropriate exit code. -/
public abbrev PipelineM := ReaderT PipelineContext (EIO Unit)

/-- Get the current phase from the pipeline context. -/
public def getPhase : PipelineM Phase := do
  let ctx ← read
  ctx.currentPhaseRef.get

/-- PipelineM wrapper for withPhase. -/
@[noinline]
public def withPhase {α} (name : String) (action : PipelineM α) : PipelineM α := do
  let ctx ← read
  ctx.withPhase name (action.run ctx)

/-- Append a pre-built PipelineMessage, emit metrics, and print in verbose mode.
    Also buckets the message into specialized refs by impact. Does not throw. -/
public def addMessage (msg : Pipeline.PipelineMessage) : Pipeline.PipelineM Unit := do
  let ctx ← read
  ctx.messagesRef.modify (·.push msg)
  ctx.phaseStateRef.modify fun ps =>
    { ps with messageCounts := ps.messageCounts.alter msg.kind.category fun mv => some (mv.getD 0 + 1) }
  match msg.kind.impact with
  | .internalError | .configurationError => ctx.toolErrorsRef.modify (·.push msg)
  | .userCodeIssue => ctx.userCodeErrorsRef.modify (·.push msg)
  | _ => pure ()
  let mut fields : List (String × Lean.Json) := [
    ("type", .str "diagnostic"), ("phase", .str msg.phase.display),
    ("file", .str msg.file.toString), ("category", .str msg.kind.category),
    ("impact", .str (toString msg.kind.impact)), ("message", .str msg.message)]
  unless msg.loc == default do
    fields := fields ++ [("start", .num msg.loc.start.byteIdx), ("stop", .num msg.loc.stop.byteIdx)]
  ctx.emitMetric (Lean.Json.mkObj fields)
  if ctx.outputMode == .verbose then
    let tag := toString msg.kind.impact
    let indent := String.replicate ((msg.phase.depth - 1) * 2) ' '
    let _ ← (do IO.eprintln s!"{indent}[{tag}] {msg.file}: {msg.message}"; (← IO.getStderr).flush : IO Unit).toBaseIO

/-- Emit a diagnostic message and continue. Tags with current phase.
    The impact classification is for downstream consumers — callers may
    accumulate multiple fatal-impact messages before aborting. -/
public def emitMessage (kind : Pipeline.MessageKind) (message : String)
    (file : System.FilePath := default) (loc : SourceRange := default) : Pipeline.PipelineM Unit := do
  let phase ← getPhase
  addMessage { file, loc, phase, kind, message }

/-- Emit a diagnostic message and abort the pipeline.
    Polymorphic return type allows use in expression position. -/
public def emitMessageAndAbort (kind : Pipeline.MessageKind) (message : String)
    (file : System.FilePath) (loc : SourceRange := default) : Pipeline.PipelineM α := do
  emitMessage kind message file loc
  throw ()

/-- All messages with a given impact. -/
public def getMessagesByImpact (impact : MessageImpact) : PipelineM (Array PipelineMessage) := do
  let ctx ← read
  let msgs ← ctx.messagesRef.get
  return msgs.filter (·.kind.impact == impact)

/-- Whether any accumulated message has the given impact. -/
public def hasImpact (impact : MessageImpact) : PipelineM Bool := do
  let ctx ← read
  let msgs ← ctx.messagesRef.get
  return msgs.any (·.kind.impact == impact)

end Strata.Pipeline
