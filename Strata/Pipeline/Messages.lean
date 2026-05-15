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

/-- Whether this impact level represents an error (vs a warning). -/
def MessageImpact.isError : MessageImpact → Bool
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

/-- Timing entry for a single phase.
    For aggregated repeated phases: `start_ns` = 0, `end_ns` = total duration,
    `count` > 1. Duration = `end_ns.getD start_ns - start_ns`. -/
structure PhaseTimingEntry where
  phase : Phase
  start_ns : Nat
  end_ns : Option Nat := none
  timeout : Bool := false
  count : Nat := 1

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

/-- Pipeline context carrying immutable config and mutable state as individual IORefs.
    This design allows any monad with BaseIO access to use pipeline capabilities
    by passing a PipelineContext value directly.

    **Phase tracking state machine:**

    The phase system operates in two modes controlled by `insideRepeatedRef`:
    - Mode N (normal): `withPhase` records individual timing entries and prints
      `[start]`/`[end]` in profile mode.
    - Mode R (repeated): `withPhase` silently aggregates timing into the
      enclosing `repeatedPhasesRef` — no print, no individual `timingRef` entry.

    `withRepeatedPhase` always transitions to mode R, saves/restores all
    phase-tracking refs, and on exit merges accumulated children back into
    the parent's `repeatedPhasesRef`.  `withPhase` never changes the mode.

    **Invariants:**
    - `currentPhaseRef` always reflects the innermost active scope's full path.
    - `repeatedPhasesRef` is scoped: saved on entry, restored on exit of both
      `withPhase` and `withRepeatedPhase` — no cross-scope leakage.
    - In mode R, all timing flows through `repeatedPhasesRef` only; `timingRef`
      is not touched until the enclosing mode-N `withPhase` flushes.

    **Thread safety:** PipelineContext is NOT thread-safe.  The phase-tracking
    refs assume single-threaded sequential access.  Concurrent `withPhase` or
    `withRepeatedPhase` calls on the same context will corrupt state. -/
structure PipelineContext where
  private mk ::
  outputMode : OutputMode
  private pipelineStartTime : Nat
  private skipTiming : Bool := false
  private messagesRef : IO.Ref (Array PipelineMessage)
  private toolErrorsRef : IO.Ref (Array PipelineMessage)
  private userCodeErrorsRef : IO.Ref (Array PipelineMessage)
  private timingRef : IO.Ref (Array PhaseTimingEntry)
  private currentPhaseRef : IO.Ref Phase
  private insideRepeatedRef : IO.Ref Bool
  private messageCountAtPhaseStartRef : IO.Ref Nat
  private repeatedPhasesRef : IO.Ref (Array (String × RepeatedPhaseData))
  private metricsHandle : Option IO.FS.Handle := none

namespace PipelineContext

/-- Create a fresh PipelineContext with new state refs. -/
def create (outputMode : OutputMode := .default)
    (skipTiming : Bool := false)
    (metricsHandle : Option IO.FS.Handle := none) : BaseIO PipelineContext := do
  let startTime ← IO.monoNanosNow
  let messagesRef ← IO.mkRef (α := Array PipelineMessage) #[]
  let toolErrorsRef ← IO.mkRef (α := Array PipelineMessage) #[]
  let userCodeErrorsRef ← IO.mkRef (α := Array PipelineMessage) #[]
  let timingRef ← IO.mkRef (α := Array PhaseTimingEntry) #[]
  let currentPhaseRef ← IO.mkRef (α := Phase) default
  let insideRepeatedRef ← IO.mkRef false
  let messageCountAtPhaseStartRef ← IO.mkRef 0
  let repeatedPhasesRef ← IO.mkRef (α := Array (String × RepeatedPhaseData)) #[]
  return { outputMode, pipelineStartTime := startTime, skipTiming,
           messagesRef, toolErrorsRef, userCodeErrorsRef, timingRef,
           currentPhaseRef, insideRepeatedRef, messageCountAtPhaseStartRef,
           repeatedPhasesRef, metricsHandle }

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

/-- All timing entries recorded during the pipeline. -/
def getTimingEntries (ctx : PipelineContext) : BaseIO (Array PhaseTimingEntry) :=
  ctx.timingRef.get

/-- Write a JSONL metric record to the metrics file (if open) and flush. -/
public def emitMetric (ctx : PipelineContext) (json : Lean.Json) : BaseIO Unit := do
  if let some h := ctx.metricsHandle then
    let _ ← (do h.putStrLn json.compress; h.flush : IO Unit).toBaseIO

/-- Get elapsed nanoseconds since pipeline start. -/
def elapsedNs (ctx : PipelineContext) : BaseIO Nat := do
  let now ← IO.monoNanosNow
  return now - ctx.pipelineStartTime

/-- Saved state for `withPhase`, captured on entry and used to restore on exit. -/
private structure PhaseSavedState where
  inRepeated : Bool
  parent : Phase
  savedRepeated : Array (String × RepeatedPhaseData)
  startNs : Nat

/-- Save phase state, set up the new phase, record timing and print [start].
    In mode R (insideRepeated), suppresses output and timingRef push. -/
private def startPhase (ctx : PipelineContext) (name : String) : BaseIO PhaseSavedState := do
  let inRepeated ← ctx.insideRepeatedRef.get
  let parent ← ctx.currentPhaseRef.get
  let savedRepeated ← ctx.repeatedPhasesRef.get
  ctx.repeatedPhasesRef.set #[]
  let startNs ← IO.monoNanosNow
  let phase := parent.subphase name
  let now ← ctx.elapsedNs
  ctx.currentPhaseRef.set phase
  let messages ← ctx.messagesRef.get
  ctx.messageCountAtPhaseStartRef.set messages.size
  unless inRepeated do
    ctx.timingRef.modify (·.push { phase, start_ns := now })
    if ctx.outputMode == .profile || ctx.outputMode == .verbose then
      let indent := String.replicate ((phase.depth - 1) * 2) ' '
      let timeSuffix := if ctx.skipTiming then "" else s!" (time: {nsToMs now}ms)"
      printlnFlush s!"{indent}[start] {phase.leaf}{timeSuffix}"
  return { inRepeated, parent, savedRepeated, startNs }

/-- Recursively flush `RepeatedPhaseData` entries to `timingRef` and print
    `[profile]` lines. `parentPhase` is the phase under which these entries
    are nested. -/
private partial def flushRepeatedEntries (ctx : PipelineContext)
    (parentPhase : Phase) (entries : Array (String × RepeatedPhaseData))
    : BaseIO Unit := do
  if entries.isEmpty then return
  let childIndent := String.replicate (parentPhase.depth * 2) ' '
  for (name, data) in entries do
    let subphase := parentPhase.subphase name
    ctx.timingRef.modify (·.push { phase := subphase, start_ns := 0,
                                    end_ns := some data.totalNs, count := data.count })
    if ctx.outputMode == .profile || ctx.outputMode == .verbose then
      let avg := if data.count > 0 then nsToMs (data.totalNs / data.count) else 0
      let timeSuffix := if ctx.skipTiming then ""
        else s!" (×{data.count}, total: {nsToMs data.totalNs}ms, avg: {avg}ms)"
      printlnFlush s!"{childIndent}[profile] {name}{timeSuffix}"
    ctx.emitMetric (Lean.Json.mkObj [
      ("type", .str "timing"), ("phase", .str subphase.display),
      ("start_ms", .num 0), ("end_ms", .num (nsToMs data.totalNs)),
      ("count", .num data.count)])
    flushRepeatedEntries ctx subphase data.children

/-- End the current phase in mode N: flush aggregated repeated subphases,
    record end time, print [warnings] summary in profile mode. -/
private def endPhaseNormal (ctx : PipelineContext) : BaseIO Unit := do
  let currentPhase ← ctx.currentPhaseRef.get
  let timing ← ctx.timingRef.get
  let parentIdx := timing.size - 1
  let repeated ← ctx.repeatedPhasesRef.get
  flushRepeatedEntries ctx currentPhase repeated
  let now ← ctx.elapsedNs
  let timing ← ctx.timingRef.get
  if h : parentIdx < timing.size then
    let parent := timing[parentIdx]
    ctx.timingRef.set (timing.modify parentIdx fun e => { e with end_ns := some now })
    ctx.emitMetric (Lean.Json.mkObj [
      ("type", .str "timing"),
      ("phase", .str currentPhase.display),
      ("start_ms", .num (nsToMs parent.start_ns)),
      ("end_ms", .num (nsToMs now))])
  if ctx.outputMode == .profile || ctx.outputMode == .verbose then
    let messages ← ctx.messagesRef.get
    let msgStart ← ctx.messageCountAtPhaseStartRef.get
    let newMsgs := messages.extract msgStart messages.size
    let indent := String.replicate ((currentPhase.depth - 1) * 2) ' '
    let timeSuffix := if ctx.skipTiming then "" else s!" (time: {nsToMs now}ms)"
    printlnFlush s!"{indent}[end] {currentPhase.leaf}{timeSuffix}"
    if ctx.outputMode == .profile && newMsgs.size > 0 then
      let counts : Std.HashMap String Nat := newMsgs.foldl (init := {})
        fun acc msg => acc.alter msg.kind.category fun mv => some (mv.getD 0 + 1)
      let parts := counts.toArray.map fun (cat, n) => s!"{n} {cat}"
      let summary := String.intercalate ", " parts.toList
      printlnFlush s!"{indent}[warnings] {currentPhase.leaf}: {summary}"

/-- End the current phase in mode R: accumulate elapsed time and nested
    children into the parent's `repeatedPhasesRef`. No print, no timingRef.
    Returns the merged repeated-phases array for the parent. -/
private def endPhaseRepeated (ctx : PipelineContext) (st : PhaseSavedState)
    : BaseIO (Array (String × RepeatedPhaseData)) := do
  let currentPhase ← ctx.currentPhaseRef.get
  let children ← ctx.repeatedPhasesRef.get
  let now ← IO.monoNanosNow
  let elapsed := now - st.startNs
  return addRepeatedEntry st.savedRepeated currentPhase.leaf elapsed children

private def PhaseSavedState.restore (st : PhaseSavedState) (ctx : PipelineContext) : BaseIO Unit := do
  let repeatedPhases ←
    if st.inRepeated then ctx.endPhaseRepeated st
    else do ctx.endPhaseNormal; pure st.savedRepeated
  ctx.currentPhaseRef.set st.parent
  ctx.repeatedPhasesRef.set repeatedPhases
  let msgs ← ctx.messagesRef.get
  ctx.messageCountAtPhaseStartRef.set msgs.size

/-- Run an action as a named subphase of the current phase. Nesting is
    determined by call structure — at the root the phase is top-level,
    inside a withPhase it becomes a child.

    In mode N: records timing, prints [start]/[end] in profile/verbose mode.
    In mode R: silently aggregates timing into the parent's repeatedPhasesRef.

    Restores parent on completion (even if the action throws). -/
@[noinline]
public def withPhase {m α} [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (ctx : PipelineContext) (name : String) (action : m α) : m α := do
  let st ← ctx.startPhase name
  try
    action
  finally
    st.restore ctx

/-- Saved state for `withRepeatedPhase`, captured on entry and used to restore on exit. -/
private structure RepeatedSavedState where
  name : String
  parent : Phase
  savedInsideRepeated : Bool
  savedRepeated : Array (String × RepeatedPhaseData)
  startNs : Nat

/-- Save phase state, set up a repeated subphase, enter mode R.
    Suppresses output — timing is aggregated into the parent on restore. -/
private def startRepeatedPhase (ctx : PipelineContext) (name : String) : BaseIO RepeatedSavedState := do
  let parent ← ctx.currentPhaseRef.get
  let savedInsideRepeated ← ctx.insideRepeatedRef.get
  let savedRepeated ← ctx.repeatedPhasesRef.get
  ctx.currentPhaseRef.set (parent.subphase name)
  ctx.insideRepeatedRef.set true
  ctx.repeatedPhasesRef.set #[]
  let startNs ← IO.monoNanosNow
  return { name, parent, savedInsideRepeated, savedRepeated, startNs }

@[inline] private def RepeatedSavedState.restore (st : RepeatedSavedState) (ctx : PipelineContext) : BaseIO Unit := do
  let t2 ← IO.monoNanosNow
  let elapsed := t2 - st.startNs
  let children ← ctx.repeatedPhasesRef.get
  ctx.currentPhaseRef.set st.parent
  ctx.insideRepeatedRef.set st.savedInsideRepeated
  ctx.repeatedPhasesRef.set (addRepeatedEntry st.savedRepeated st.name elapsed children)

/-- Run an action as a repeated subphase. Instead of recording individual
    timing entries, accumulates count and total duration into the parent's
    `repeatedPhasesRef`. When the parent phase ends, the aggregated results
    are flushed as single timing entries. Silent per-iteration.

    Sets `currentPhaseRef` so nested `emitMessage` calls get the correct
    phase tag.  Sets `insideRepeatedRef` to true so nested `withPhase` calls
    aggregate silently.  Saves/restores `repeatedPhasesRef` for child
    isolation. -/
@[noinline]
public def withRepeatedPhase {m α} [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (ctx : PipelineContext) (name : String) (action : m α) : m α := do
  let st ← ctx.startRepeatedPhase name
  try
    action
  finally
    st.restore ctx

/-- Time a pure expression as a repeated subphase. The `@[noinline]`
    attribute prevents the compiler from hoisting `expr` outside the
    timing window. Use this instead of `withRepeatedPhase` when the work
    being timed is a pure (non-monadic) expression. -/
@[noinline]
public def withRepeatedPhasePure {α} [Inhabited α]
    (ctx : PipelineContext) (name : String) (expr : Unit → α) : BaseIO α := do
  ctx.withRepeatedPhase name (m := BaseIO) (pure (expr ()))

end PipelineContext

/-- The pipeline monad: a reader over PipelineContext with EIO Unit.
    Computations accumulate diagnostic messages in PipelineContext.messagesRef.
    `emitFatalMessage` throws `()` to abort, but multiple messages (including
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
    let tag := if msg.kind.impact.isError then "error" else "warning"
    let indent := String.replicate ((msg.phase.depth - 1) * 2) ' '
    let _ ← (do IO.eprintln s!"{indent}[{tag}] {msg.file}: {msg.message}"; (← IO.getStderr).flush : IO Unit).toBaseIO

/-- Emit a diagnostic message and continue. Tags with current phase. -/
public def emitMessage (kind : Pipeline.MessageKind) (message : String)
    (file : System.FilePath := default) (loc : SourceRange := default) : Pipeline.PipelineM Unit := do
  let phase ← (← read) |>.currentPhaseRef.get
  addMessage { file, loc, phase, kind, message }

/-- Emit a diagnostic message and abort the pipeline.
    Polymorphic return type allows use in expression position. -/
public def emitFatalMessage (kind : Pipeline.MessageKind) (message : String)
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
