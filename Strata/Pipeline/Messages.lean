/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Util.SourceRange
import Lean.Data.Json.Basic
import Lean.Data.Json.Printer
import all Strata.DDM.Util.String

public section
namespace Strata.Pipeline

/-- Print to stdout and flush. -/
private def printlnFlush (msg : String) : BaseIO Unit := do
  let _ ← (do IO.println msg; (← IO.getStdout).flush : IO Unit).toBaseIO

/-- Nanoseconds to milliseconds with rounding. -/
def nsToMs (ns : Nat) : Nat := (ns + 500000) / 1000000

/-- A phase represents a position in the phase hierarchy.
    Top-level phases have a single entry; subphases have multiple.
    Ordering is determined by position in the timing array, not by name. -/
structure Phase where
  path : Array String := #[]
  deriving BEq, DecidableEq, Hashable, Repr, Inhabited

namespace Phase

def base (name : String) : Phase :=
  { path := #[name] }

def pop (p : Phase) : Phase := { path := p.path.pop }

def subphase (parent : Phase) (name : String) : Phase :=
  { path := parent.path.push name }

def depth (p : Phase) : Nat := p.path.size

def leaf (p : Phase) : String :=
  match p.path.back? with
  | some name => name
  | none => "<unknown>"

def display (p : Phase) : String :=
  String.intercalate "." p.path.toList

end Phase

instance : ToString Phase where
  toString p := p.display

/-- How severe / actionable is this message? -/
inductive MessageImpact where
  /-- An unexpected failure that prevented some output from being generated
      (e.g., a malformed overload entry that was skipped). -/
  | internalError
  /-- An unexpected condition that did not prevent output, but may indicate
      a tool bug worth investigating. -/
  | internalWarning
  /-- A known, documented limitation that may cause specs to be incomplete
      or imprecise. -/
  | knownLimitation
  /-- An issue detected in the user's Python source code. -/
  | userCodeIssue
  /-- The tool was invoked with invalid arguments or the on-disk pyspecs
      are invalid (e.g., missing module, unreadable file). -/
  | configurationError
  deriving BEq, DecidableEq, Hashable, Ord, Repr

/--
Whether this impact level typically warrants aborting the pipeline.

N.B. Pipeline steps may want a custom abort strategy rather than
relying on this predicate.
-/
def MessageImpact.isFatal : MessageImpact → Bool
  | .internalError => true
  | .configurationError => true
  | .internalWarning => false
  | .knownLimitation => false
  | .userCodeIssue => true

instance : ToString MessageImpact where
  toString
    | .internalError => "internalError"
    | .internalWarning => "internalWarning"
    | .knownLimitation => "knownLimitation"
    | .userCodeIssue => "userCodeIssue"
    | .configurationError => "configurationError"

/-- A categorized message kind with category and impact.
    The phase is derived from pipeline context at emit time. -/
structure MessageKind where
  category : String
  impact : MessageImpact
  deriving BEq, DecidableEq, Hashable, Ord, Repr

instance : ToString MessageKind where
  toString mk := mk.category

namespace MessageKind

-- Type translation warnings
def unsupportedUnion : MessageKind :=
  { category := "unsupportedUnion", impact := .knownLimitation }
def unsupportedOptionalFloat : MessageKind :=
  { category := "unsupportedOptionalFloat", impact := .knownLimitation }
def unsupportedOptionalList : MessageKind :=
  { category := "unsupportedOptionalList", impact := .knownLimitation }
def unsupportedOptionalDict : MessageKind :=
  { category := "unsupportedOptionalDict", impact := .knownLimitation }
def unsupportedOptionalAny : MessageKind :=
  { category := "unsupportedOptionalAny", impact := .knownLimitation }
def unsupportedOptionalBytes : MessageKind :=
  { category := "unsupportedOptionalBytes", impact := .knownLimitation }

-- Internal type errors
def typeError : MessageKind :=
  { category := "typeError", impact := .internalWarning }

-- Precondition warnings
def placeholderExpr : MessageKind :=
  { category := "placeholderExpr", impact := .knownLimitation }
def floatLiteral : MessageKind :=
  { category := "floatLiteral", impact := .knownLimitation }
def isinstanceUnsupported : MessageKind :=
  { category := "isinstanceUnsupported", impact := .knownLimitation }
def forallListUnsupported : MessageKind :=
  { category := "forallListUnsupported", impact := .knownLimitation }
def forallDictUnsupported : MessageKind :=
  { category := "forallDictUnsupported", impact := .knownLimitation }

-- Declaration warnings
def missingMethodSelf : MessageKind :=
  { category := "missingMethodSelf", impact := .internalWarning }
def kwargsExpansionError : MessageKind :=
  { category := "kwargsExpansionError", impact := .internalWarning }
def postconditionUnsupported : MessageKind :=
  { category := "postconditionUnsupported", impact := .knownLimitation }

-- Overload dispatch warnings (in PySpec-to-Laurel phase)
def overloadNoArgs : MessageKind :=
  { category := "overloadNoArgs", impact := .internalError }
def overloadArgArity : MessageKind :=
  { category := "overloadArgArity", impact := .internalError }
def overloadArgNotStringLiteral : MessageKind :=
  { category := "overloadArgNotStringLiteral", impact := .internalError }
def overloadReturnArity : MessageKind :=
  { category := "overloadReturnArity", impact := .internalError }
def overloadReturnNotClass : MessageKind :=
  { category := "overloadReturnNotClass", impact := .internalError }
def overloadParamNameDisagreement : MessageKind :=
  { category := "overloadParamNameDisagreement", impact := .internalError }

-- PySpec parsing phase
def pySpecParsingError : MessageKind :=
  { category := "error", impact := .internalError }
def pySpecParsingWarning : MessageKind :=
  { category := "warning", impact := .knownLimitation }
def pySpecReadError : MessageKind :=
  { category := "readError", impact := .configurationError }

-- PySpec-to-Laurel assembly phase
def functionSignatureError : MessageKind :=
  { category := "functionSignatureError", impact := .internalError }
def typeNameCollision : MessageKind :=
  { category := "typeNameCollision", impact := .internalError }
def procedureNameCollision : MessageKind :=
  { category := "procedureNameCollision", impact := .internalError }

-- Module resolution phase
def invalidModuleName : MessageKind :=
  { category := "invalidModuleName", impact := .configurationError }
def missingPySpecModule : MessageKind :=
  { category := "missingPySpecModule", impact := .configurationError }

-- Overload resolution phase
def overloadResolveWarning : MessageKind :=
  { category := "resolveWarning", impact := .internalWarning }

-- Laurel lowering phase
def laurelLoweringWarning : MessageKind :=
  { category := "warning", impact := .internalWarning }
def laurelLoweringError : MessageKind :=
  { category := "error", impact := .internalError }
def laurelLoweringNotImpl : MessageKind :=
  { category := "notYetImplemented", impact := .knownLimitation }
def laurelLoweringUserError : MessageKind :=
  { category := "userError", impact := .userCodeIssue }

-- Laurel-to-Core translation phase
def laurelToCoreWarning : MessageKind :=
  { category := "warning", impact := .internalWarning }
def laurelToCoreError : MessageKind :=
  { category := "error", impact := .internalError }
def laurelToCoreNotImpl : MessageKind :=
  { category := "notYetImplemented", impact := .knownLimitation }
def laurelToCoreUserError : MessageKind :=
  { category := "userError", impact := .userCodeIssue }

-- Core transforms phase
def coreTransformWarning : MessageKind :=
  { category := "warning", impact := .internalWarning }
def coreTransformError : MessageKind :=
  { category := "error", impact := .internalError }
def coreTransformNotImpl : MessageKind :=
  { category := "notYetImplemented", impact := .knownLimitation }
def coreTransformUserError : MessageKind :=
  { category := "userError", impact := .userCodeIssue }

-- Verification phase
def verificationWarning : MessageKind :=
  { category := "warning", impact := .internalWarning }
def verificationError : MessageKind :=
  { category := "error", impact := .internalError }
def verificationTimeout : MessageKind :=
  { category := "solverTimeout", impact := .knownLimitation }

end MessageKind

/-- A located, categorized pipeline message. -/
structure PipelineMessage where
  file : System.FilePath
  loc : SourceRange
  phase : Phase
  kind : MessageKind
  message : String

instance : ToString PipelineMessage where
  toString m := s!"{m.file}: {m.phase}.{m.kind}: {m.message}"

/-- Output verbosity mode for the pipeline. -/
inductive OutputMode where
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
private def addRepeatedEntry (arr : Array (String × RepeatedPhaseData))
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
private structure PhaseState where
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
structure PipelineContext where
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
def create (outputMode : OutputMode := .default)
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
def getMessages (ctx : PipelineContext) : BaseIO (Array PipelineMessage) :=
  ctx.messagesRef.get

/-- Messages with `.internalError` or `.configurationError` impact.
    These represent tool bugs or invalid invocations that we must fix. -/
def getToolErrors (ctx : PipelineContext) : BaseIO (Array PipelineMessage) :=
  ctx.toolErrorsRef.get

/-- Messages with `.userCodeIssue` impact.
    These represent definite errors in the user's Python source code. -/
def getUserCodeErrors (ctx : PipelineContext) : BaseIO (Array PipelineMessage) :=
  ctx.userCodeErrorsRef.get

/-- Write a JSONL metric record to the metrics file (if open) and flush. -/
public def emitMetric (ctx : PipelineContext) (json : Lean.Json) : BaseIO Unit := do
  if let some h := ctx.metricsHandle then
    let _ ← (do h.putStrLn json.compress; h.flush : IO Unit).toBaseIO

/-- Get elapsed nanoseconds since pipeline start. -/
def elapsedNs (ctx : PipelineContext) : BaseIO Nat := do
  let now ← IO.monoNanosNow
  return now - ctx.pipelineStartTime

/-- Common entry logic for `withPhase`: push the subphase name onto
    `currentPhaseRef`, save and clear scoped phase state. -/
private def enterPhase (ctx : PipelineContext) (name : String)
    : BaseIO PhaseState := do
  ctx.currentPhaseRef.modify (·.subphase name)
  ctx.phaseStateRef.modifyGet fun ps => (ps, {})

/-- Recursively print `[profile]` lines and emit JSONL metrics for aggregated
    repeated phases. `parentPhase` is the phase under which these entries
    are nested. -/
private partial def flushRepeatedEntries (ctx : PipelineContext)
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
private def enterPhaseNormal (ctx : PipelineContext) : BaseIO Nat := do
  let phase ← ctx.currentPhaseRef.get
  let startNs ← ctx.elapsedNs
  if ctx.outputMode == .profile || ctx.outputMode == .verbose then
    let indent := String.replicate ((phase.depth - 1) * 2) ' '
    let timeSuffix := if ctx.profilePipeline then s!" (time: {nsToMs startNs}ms)" else ""
    printlnFlush s!"{indent}[start] {phase.leaf}{timeSuffix}"
  return startNs

/-- End the current phase in mode N: flush aggregated repeated subphases,
    emit timing metric, print [end]/[warnings], then pop phase and restore state. -/
private def exitPhaseNormal (ctx : PipelineContext)
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
private def exitPhaseRepeated (ctx : PipelineContext)
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
abbrev PipelineM := ReaderT PipelineContext (EIO Unit)

/-- Get the current phase from the pipeline context. -/
public def getPhase : PipelineM Phase := do
  let ctx ← read
  ctx.currentPhaseRef.get

/-- PipelineM wrapper for withPhase. -/
@[noinline]
public def withPhase (name : String) (action : PipelineM α) : PipelineM α := do
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
end
