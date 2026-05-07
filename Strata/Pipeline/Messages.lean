/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Util.SourceRange
import all Strata.DDM.Util.String

public section
namespace Strata.Pipeline

/-- A single component in a phase path. -/
structure PhaseName where
  name : String
  index : Nat
  deriving BEq, DecidableEq, Hashable, Repr, Inhabited

instance : ToString PhaseName where
  toString pn := pn.name

instance : Ord PhaseName where
  compare a b := compare a.index b.index

/-- A phase represents a position in the phase hierarchy.
    Top-level phases have a single entry; subphases have multiple. -/
structure Phase where
  path : Array PhaseName := #[]
  deriving BEq, DecidableEq, Hashable, Repr, Inhabited

namespace Phase

def base (name : String) (index : Nat) : Phase :=
  { path := #[⟨name, index⟩] }

def subphase (parent : Phase) (name : String) (index : Nat) : Phase :=
  { path := parent.path.push ⟨name, index⟩ }

def depth (p : Phase) : Nat := p.path.size

def leaf (p : Phase) : String :=
  match p.path.back? with
  | some pn => toString pn
  | none => "<unknown>"

def display (p : Phase) : String :=
  String.intercalate "." (p.path.toList.map toString)

end Phase

instance : ToString Phase where
  toString p := p.display

instance : Ord Phase where
  compare a b :=
    let rec go (i : Nat) : Ordering :=
      if h₁ : i < a.path.size then
        if h₂ : i < b.path.size then
          match compare a.path[i] b.path[i] with
          | .eq => go (i + 1)
          | ord => ord
        else .gt
      else if i < b.path.size then .lt
      else .eq
    go 0

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

/-- Timing entry for a single phase. -/
structure PhaseTimingEntry where
  phase : Phase
  start_ns : Nat
  end_ns : Option Nat := none
  timeout : Bool := false

/-- Pipeline context carrying immutable config and mutable state as individual IORefs.
    This design allows any monad with BaseIO access to use pipeline capabilities
    by passing a PipelineContext value directly. -/
public structure PipelineContext where
  outputMode : OutputMode
  pipelineStartTime : Nat
  skipTiming : Bool := false
  messagesRef : IO.Ref (Array PipelineMessage)
  shouldAbortRef : IO.Ref Bool
  timingRef : IO.Ref (Array PhaseTimingEntry)
  currentPhaseRef : IO.Ref Phase
  messageCountAtPhaseStartRef : IO.Ref Nat

/-- The pipeline monad: a reader over PipelineContext with BaseIO. -/
public abbrev PipelineM := ReaderT PipelineContext BaseIO

/-- Nanoseconds to milliseconds with rounding. -/
def nsToMs (ns : Nat) : Nat := (ns + 500000) / 1000000

/-- Get elapsed nanoseconds since pipeline start. -/
def PipelineContext.elapsedNs (ctx : PipelineContext) : BaseIO Nat := do
  let now ← IO.monoNanosNow
  return now - ctx.pipelineStartTime

/-- Print to stderr and flush. -/
private def eprintlnFlush (msg : String) : BaseIO Unit := do
  let _ ← (do IO.eprintln msg; (← IO.getStderr).flush : IO Unit).toBaseIO

/-- End the current phase: record end time, print [warnings] summary in profile mode. -/
def PipelineContext.endCurrentPhase (ctx : PipelineContext) : BaseIO Unit := do
  let currentPhase ← ctx.currentPhaseRef.get
  if currentPhase.path.isEmpty then return
  let now ← ctx.elapsedNs
  let timing ← ctx.timingRef.get
  if h : timing.size > 0 then
    let lastIdx := timing.size - 1
    let last := timing[lastIdx]
    ctx.timingRef.set (timing.set lastIdx { last with end_ns := some now })
  if ctx.outputMode == .profile then
    let messages ← ctx.messagesRef.get
    let msgStart ← ctx.messageCountAtPhaseStartRef.get
    let newMsgs := messages.extract msgStart messages.size
    if newMsgs.size > 0 then
      let counts : Std.HashMap String Nat := newMsgs.foldl (init := {})
        fun acc msg => acc.alter msg.kind.category fun mv => some (mv.getD 0 + 1)
      let parts := counts.toArray.map fun (cat, n) => s!"{n} {cat}"
      let summary := String.intercalate ", " parts.toList
      let indent := String.replicate ((currentPhase.depth - 1) * 2) ' '
      eprintlnFlush s!"{indent}[warnings] {currentPhase.leaf}: {summary}"

/-- Start a new phase. Implicitly ends the previous phase at the same or deeper depth. -/
public def PipelineContext.startPhase (ctx : PipelineContext) (phase : Phase) : BaseIO Unit := do
  let currentPhase ← ctx.currentPhaseRef.get
  if currentPhase.path.size >= phase.path.size then
    ctx.endCurrentPhase
  let now ← ctx.elapsedNs
  ctx.timingRef.modify (·.push { phase, start_ns := now })
  ctx.currentPhaseRef.set phase
  let messages ← ctx.messagesRef.get
  ctx.messageCountAtPhaseStartRef.set messages.size
  if ctx.outputMode == .profile || ctx.outputMode == .verbose then
    let indent := String.replicate ((phase.depth - 1) * 2) ' '
    let timeSuffix := if ctx.skipTiming then "" else s!" (time: {nsToMs now}ms)"
    eprintlnFlush s!"{indent}[start] {phase.leaf}{timeSuffix}"

/-- PipelineM wrapper for startPhase. -/
public def startPhase (phase : Phase) : PipelineM Unit := do
  let ctx ← read
  ctx.startPhase phase


/-- Create a fresh PipelineContext with new state refs. -/
public def PipelineContext.create (outputMode : OutputMode := .default)
    (skipTiming : Bool := false) : BaseIO PipelineContext := do
  let startTime ← IO.monoNanosNow
  let messagesRef ← IO.mkRef #[]
  let shouldAbortRef ← IO.mkRef false
  let timingRef ← IO.mkRef #[]
  let currentPhaseRef ← IO.mkRef {}
  let messageCountAtPhaseStartRef ← IO.mkRef 0
  return { outputMode, pipelineStartTime := startTime, skipTiming,
           messagesRef, shouldAbortRef, timingRef,
           currentPhaseRef, messageCountAtPhaseStartRef }

end Strata.Pipeline
end
