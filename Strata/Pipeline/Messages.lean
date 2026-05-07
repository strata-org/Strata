/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Util.SourceRange
import all Strata.DDM.Util.String

public section
namespace Strata.Pipeline

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

/-- Whether this impact level should abort the pipeline. Fatal impacts
    indicate that the pipeline output would be incomplete or incorrect. -/
def MessageImpact.isFatal : MessageImpact → Bool
  | .internalError => true
  | .configurationError => true
  | .internalWarning => false
  | .knownLimitation => false
  | .userCodeIssue => false

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
  { category := "invalidModuleName", impact := .internalWarning }
def missingAutoResolvedPySpec : MessageKind :=
  { category := "missingAutoResolvedPySpec", impact := .knownLimitation }
def missingDispatchModule : MessageKind :=
  { category := "missingDispatchModule", impact := .configurationError }
def missingExplicitPySpec : MessageKind :=
  { category := "missingExplicitPySpec", impact := .configurationError }

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

/-- Pipeline context carrying immutable config and mutable state as individual IORefs.
    This design allows any monad with BaseIO access to use pipeline capabilities
    by passing a PipelineContext value directly. -/
public structure PipelineContext where
  outputMode : OutputMode
  pipelineStartTime : Nat
  skipTiming : Bool := false
  messagesRef : IO.Ref (Array PipelineMessage)
  timingRef : IO.Ref (Array PhaseTimingEntry)
  currentPhaseRef : IO.Ref Phase
  messageCountAtPhaseStartRef : IO.Ref Nat
  repeatedPhasesRef : IO.Ref (Std.HashMap String (Nat × Nat))

/-- The pipeline monad: a reader over PipelineContext with EIO Unit.
    Fatal messages abort by throwing `()`. Callers that want to continue
    despite abort can catch the exception. -/
public abbrev PipelineM := ReaderT PipelineContext (EIO Unit)

/-- Nanoseconds to milliseconds with rounding. -/
def nsToMs (ns : Nat) : Nat := (ns + 500000) / 1000000

/-- Get elapsed nanoseconds since pipeline start. -/
def PipelineContext.elapsedNs (ctx : PipelineContext) : BaseIO Nat := do
  let now ← IO.monoNanosNow
  return now - ctx.pipelineStartTime

/-- Print to stdout and flush. -/
private def printlnFlush (msg : String) : BaseIO Unit := do
  let _ ← (do IO.println msg; (← IO.getStdout).flush : IO Unit).toBaseIO

/-- End the current phase: flush aggregated repeated subphases, record end time,
    print [warnings] summary in profile mode. -/
def PipelineContext.endCurrentPhase (ctx : PipelineContext) : BaseIO Unit := do
  let currentPhase ← ctx.currentPhaseRef.get
  if currentPhase.path.isEmpty then return
  -- Flush aggregated repeated subphases
  let repeated ← ctx.repeatedPhasesRef.get
  if !repeated.isEmpty then
    let childIndent := String.replicate (currentPhase.depth * 2) ' '
    for (name, count, totalNs) in repeated.toArray do
      let subphase := currentPhase.subphase name
      ctx.timingRef.modify (·.push { phase := subphase, start_ns := 0, end_ns := some totalNs, count })
      if ctx.outputMode == .profile || ctx.outputMode == .verbose then
        let avg := if count > 0 then nsToMs (totalNs / count) else 0
        let timeSuffix := if ctx.skipTiming then ""
          else s!" (×{count}, total: {nsToMs totalNs}ms, avg: {avg}ms)"
        printlnFlush s!"{childIndent}[profile] {name}{timeSuffix}"
    ctx.repeatedPhasesRef.set {}
  let now ← ctx.elapsedNs
  let timing ← ctx.timingRef.get
  if h : timing.size > 0 then
    let lastIdx := timing.size - 1
    let last := timing[lastIdx]
    ctx.timingRef.set (timing.set lastIdx { last with end_ns := some now })
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
  ctx.currentPhaseRef.set {}

/-- Start a new phase: record timing and print [start] in profile/verbose mode. -/
private def PipelineContext.startPhase (ctx : PipelineContext) (phase : Phase) : BaseIO Unit := do
  let now ← ctx.elapsedNs
  ctx.timingRef.modify (·.push { phase, start_ns := now })
  ctx.currentPhaseRef.set phase
  let messages ← ctx.messagesRef.get
  ctx.messageCountAtPhaseStartRef.set messages.size
  if ctx.outputMode == .profile || ctx.outputMode == .verbose then
    let indent := String.replicate ((phase.depth - 1) * 2) ' '
    let timeSuffix := if ctx.skipTiming then "" else s!" (time: {nsToMs now}ms)"
    printlnFlush s!"{indent}[start] {phase.leaf}{timeSuffix}"

/-- Run an action as a named subphase of the current phase. Nesting is
    determined by call structure — at the root the phase is top-level,
    inside a withPhase it becomes a child. Records timing, prints
    [start]/[end] in profile/verbose mode. Restores parent on completion
    (even if the action throws). -/
@[noinline]
public def PipelineContext.withPhase {m α} [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (ctx : PipelineContext) (name : String) (action : m α) : m α := do
  let parent ← (ctx.currentPhaseRef.get : BaseIO _)
  let savedRepeated ← (ctx.repeatedPhasesRef.get : BaseIO _)
  (ctx.repeatedPhasesRef.set {} : BaseIO _)
  (ctx.startPhase (parent.subphase name) : BaseIO _)
  try
    action
  finally
    (ctx.endCurrentPhase : BaseIO _)
    (ctx.currentPhaseRef.set parent : BaseIO _)
    (ctx.repeatedPhasesRef.set savedRepeated : BaseIO _)
    -- Advance parent's message start so it only reports messages added after this child
    let msgs ← (ctx.messagesRef.get : BaseIO _)
    (ctx.messageCountAtPhaseStartRef.set msgs.size : BaseIO _)

/-- PipelineM wrapper for withPhase. -/
@[noinline]
public def withPhase (name : String) (action : PipelineM α) : PipelineM α := do
  let ctx ← read
  ctx.withPhase name (action.run ctx)

/-- Run an action as a repeated subphase. Instead of recording individual
    timing entries, accumulates count and total duration into the parent's
    `repeatedPhasesRef`. When the parent phase ends, the aggregated results
    are flushed as single timing entries. Silent per-iteration. -/
@[noinline]
public def PipelineContext.withRepeatedPhase {m α} [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (ctx : PipelineContext) (name : String) (action : m α) : m α := do
  let t1 ← (IO.monoNanosNow : BaseIO _)
  try
    action
  finally
    let t2 ← (IO.monoNanosNow : BaseIO _)
    let elapsed := t2 - t1
    (ctx.repeatedPhasesRef.modify fun m =>
      m.alter name fun
        | some (count, total) => some (count + 1, total + elapsed)
        | none => some (1, elapsed) : BaseIO _)

/-- Get the current phase from the pipeline context. -/
public def getPhase : PipelineM Phase := do
  let ctx ← read
  ctx.currentPhaseRef.get

/-- Create a fresh PipelineContext with new state refs. -/
public def PipelineContext.create (outputMode : OutputMode := .default)
    (skipTiming : Bool := false) : BaseIO PipelineContext := do
  let startTime ← IO.monoNanosNow
  let messagesRef ← IO.mkRef #[]
  let timingRef ← IO.mkRef #[]
  let currentPhaseRef ← IO.mkRef {}
  let messageCountAtPhaseStartRef ← IO.mkRef 0
  let repeatedPhasesRef ← IO.mkRef {}
  return { outputMode, pipelineStartTime := startTime, skipTiming,
           messagesRef, timingRef,
           currentPhaseRef, messageCountAtPhaseStartRef, repeatedPhasesRef }

end Strata.Pipeline
end
