/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelCompilationPipeline
public import StrataCortex.Implementation.Pipeline
public import Strata.Languages.Cortex.Interpreter
public import Strata.Languages.Cortex.DirectInterpreter
public import Strata.Languages.Cortex.LowerCTE
public import Strata.Languages.Cortex.Cleanup
public import Strata.Languages.Cortex.LowerDispatch
public import Strata.Languages.Cortex.LowerGlobals
public import Strata.Languages.Cortex.FieldCasts

namespace Cortex

open Strata Strata.Laurel

open Cortex.Interp

public section

def cortexStopMessage : StopReason → String
  | .engine .replayFuelExhausted => "resource-limit: out of fuel"
  | .engine .callDepthExceeded => "resource-limit: the call-depth limit was exceeded"
  | .engine r => r.describe
  | .stop summary => summary
  | .lowering msg => s!"lowering: {msg}"
  | .typeError msg => s!"type error: {msg}"
  | .notLowered c => s!"`{c}` was not lowered"
  | .exceptionsUnsupported => "exceptions are not supported"
  | .inoutArgumentMismatch n => s!"call of {n}: an inout argument is not the variable its result is assigned to"
  | .procedureWithoutBody n => s!"entry procedure {n} has no body"
  | .invalidDatatypes msg => s!"invalid datatypes: {msg}"
  | .at _ r => cortexStopMessage r

/-- Where a run stopped (`StopReason.locate`), when that has a source location. -/
def stopLocation : StopReason → Option Strata.FileRange
  | .at md _ => Imperative.getFileRange md
  | _ => none

/-- Whether `r` is one of the interpreter's bounds, its fuel or its call depth, running out. -/
def isResourceLimit : StopReason → Bool
  | .engine .replayFuelExhausted | .engine .callDepthExceeded => true
  | .at _ r => isResourceLimit r
  | _ => false

/-- Whether `r` is a stop, a frontend's (`stopSummary?`) or a resource limit: a run that a stop ends has no verdict.
Any other reason is an interpreter error. -/
def isStop : StopReason → Bool
  | .stop _ => true
  | .at _ r => isStop r
  | r => isResourceLimit r

/-- What running the `entry` procedures of a program on the Cortex interpreter
produced. -/
structure InterpretOutcome where
  /-- The failed assertions, the uncaught exceptions, the stops and the places of the interpreter errors, each
  reported once. -/
  diagnostics : Array Message := #[]
  /-- The entry procedures in which a check failed at a source location. A failed check is a verdict even when a stop
  ends the run later: the run reached it before using anything it has no model of. -/
  failed : Array String := #[]
  /-- The entry procedures that a stop ended. -/
  stops : Array String := #[]
  /-- The entry procedures that ended on an interpreter error, could not evaluate an assertion, or failed or stopped
  without a source location, each with the reason. -/
  errors : Array (String × String) := #[]

/-- How a run of a program's entry procedures ended. -/
inductive RunOutcome where
  | passed
  | stopped
  | failed
  | error
  deriving DecidableEq, Repr

/-- How the run ended: the worst of its entries, an interpreter error before a failed check, and a failed check
before a stop. -/
def InterpretOutcome.outcome (o : InterpretOutcome) : RunOutcome :=
  if !o.errors.isEmpty then .error
  else if !o.failed.isEmpty then .failed
  else if !o.stops.isEmpty then .stopped
  else .passed

/-- Run every `entry` procedure of `m` on the Cortex interpreter, after the
cleanup passes and the lowerings of `Cortex.Interp.lower`, giving
each procedure and each call `fuel` steps. With `cleanup := false` the cleanup
passes are skipped, for comparing the two runs. The error is the reason a pass
rejected the program. -/
def interpretProgram (m : Cortex.UnorderedProgram) (fuel : Nat) (cleanup : Bool := true) :
    Except String InterpretOutcome := do
  let m ← if cleanup then (Cortex.Cleanup.run m).mapError (s!"Cleanup: {·}") else pure m
  let entries := m.procedures.filter isEntry
  let prepared ← match prepare m with
    | .ok m => pure (some m)
    | .error (.lowering e) => throw s!"lowering: {e}"
    | .error _ => pure none
  let mut out : Array Message := #[]
  let mut errors : Array (String × String) := #[]
  let mut failed : Array String := #[]
  let mut stops : Array String := #[]
  for p in entries do
    let (result, trace) : Except StopReason Config × Trace :=
      if p.body.isNone then (.error (.procedureWithoutBody p.name), []) else
      match prepared with
      | some m => runPreparedTraced m fuel p.name
      | none => match runEntry m fuel p with
        | .ok r => (.ok r.final, r.trace)
        | .error e => (.error e, [])
    if let .error e := result then
      unless isStop e do
        errors := errors.push (p.name, cortexStopMessage e)
        if let some fr := stopLocation e then
          out := out.push (Message.withRange fr s!"the interpreter fails here: {cortexStopMessage e}")
        continue
    if unevaluated trace > 0 then
      errors := errors.push (p.name, "an assertion could not be evaluated")
    let mut checkFailed := false
    for (md, summary) in failures trace do
      match Imperative.getFileRange md with
      | some fr =>
        out := out.push (Message.withRange fr s!"{summary} does not hold")
        checkFailed := true
      | none => errors := errors.push (p.name, s!"{summary} does not hold, at a check with no source location")
    if let .error e := result then
      -- A stop is reported where it happened, after the checks that failed before it. A resource limit that nothing
      -- located, such as the fuel running out at a lowering's jump, is the entry's.
      match (stopLocation e).orElse fun _ => if isResourceLimit e then Imperative.getFileRange p.md else none with
      | some fr =>
        out := out.push (Message.withRange fr s!"the run stops here: {cortexStopMessage e}")
        stops := stops.push p.name
      | none => errors := errors.push (p.name, s!"{cortexStopMessage e}, at a stop with no source location")
    if checkFailed then
      failed := failed.push p.name
  return { diagnostics := out.toList.eraseDups.toArray, failed, stops, errors := errors.toList.eraseDups.toArray }

def directStopMessage : DirectInterp.StopReason → String
  | .fuelExhausted => "out of fuel"
  | .noChoice => "no value to choose"
  | .missingBlock l => s!"missing block {l}"
  | .expressionDidNotEvaluate => "an expression did not evaluate"
  | .expressionWasNotBoolean => "a branch condition was not a Boolean"
  | .unknownProcedure n => s!"unknown procedure {n}"
  | .procedureWithoutBody n => s!"entry procedure {n} has no body"
  | .unknownComposite n => s!"unknown composite {n}"
  | .unknownField f => s!"unknown field {f.owner}.{f.field}"
  | .notAReference => "not a reference"
  | .danglingReference => "dangling reference"
  | .missingObjectField f => s!"object has no field {f.owner}.{f.field}"
  | .illTypedValue => "ill-typed value"
  | .notAValue => "not a value"
  | .undefinedVariable => "undefined variable"
  | .variableAlreadyDefined => "variable already defined"
  | .variableNotDefined => "variable not defined"
  | .arityMismatch => "arity mismatch"
  | .aliasedResults => "aliased call results"
  | .exceptionWithoutType => "thrown value has no runtime type"
  | .calleeDidNotTerminate n => s!"callee {n} did not terminate"
  | .invalidDatatypes msg => s!"invalid datatypes: {msg}"
  | .notAnArray => "not an array"
  | .negativeArrayLength n => s!"array length {n} is negative"
  | .arrayLengthOverLimit n limit => s!"array length {n} is over the interpreter's limit of {limit}"
  | .indexOutOfRange i n => s!"index {i} is out of range for an array of length {n}"
  | .elementTypeMismatch t a =>
    s!"array type {Std.format a} is not a subtype of (Array {Std.format (t : Lambda.LTy)})"
  | .elementNotAReference a => s!"the elements of array type {Std.format a} are not references"
  | .at _ r => directStopMessage r

/-- Where a run of the direct interpreter stopped (`DirectInterp.StopReason.locate`), when that has a source
location. -/
def directStopLocation : DirectInterp.StopReason → Option Strata.FileRange
  | .at md _ => Imperative.getFileRange md
  | _ => none

/-- Run every `entry` procedure of `m` on the direct Cortex interpreter (`Cortex.DirectInterp`),
after the cleanup, LowerDispatch, LowerGlobals, FieldCasts and LowerCTE: a debugging aid, to
compare with `interpretProgram`. -/
def interpretProgramDirect (m : Cortex.UnorderedProgram) (fuel : Nat) (cleanup : Bool := true) :
    Except String InterpretOutcome := do
  let m ← if cleanup then (Cortex.Cleanup.run m).mapError (s!"Cleanup: {·}") else pure m
  let m ← (Cortex.LowerDispatch.run m >>= Cortex.LowerGlobals.run >>= Cortex.FieldCasts.run
    >>= Cortex.LowerCTE.runWith true).mapError (s!"lowering: {·}")
  let mut out : Array Message := #[]
  let mut errors : Array (String × String) := #[]
  for p in m.procedures do
    unless DirectInterp.isEntry p do continue
    match DirectInterp.runEntry m fuel p with
    | .error e =>
      errors := errors.push (p.name, directStopMessage e)
      -- An interpreter error is also reported where it happened, when that has a source range.
      if let some fr := directStopLocation e then
        out := out.push (Message.withRange fr s!"the interpreter fails here: {directStopMessage e}")
    | .ok (final, trace) =>
      if DirectInterp.unevaluated trace > 0 then
        errors := errors.push (p.name, "an assertion could not be evaluated")
      let escaped := match final with
        | .raised ρ v md =>
          let fallback := match dynType ρ.heap v with
            | some ty => s!"uncaught exception '{Std.format ty}' is not thrown"
            | none => "uncaught exception is not thrown"
          [(md, ((md : Cortex.MD).getPropertySummary).getD fallback)]
        | _ => []
      -- A failure without a source range cannot be reported where it is, and dropping it would end the run as a pass:
      -- it ends the entry as an error.
      for (md, summary) in DirectInterp.failures trace ++ escaped do
        match Imperative.getFileRange md with
        | some fr => out := out.push (Message.withRange fr s!"{summary} does not hold")
        | none => errors := errors.push (p.name, s!"{summary} does not hold, at a check with no source location")
  return { diagnostics := out.toList.eraseDups.toArray, errors := errors.toList.eraseDups.toArray }

/-- Run every `entry` procedure of a Laurel program on the Cortex interpreter,
as `interpretProgram` does. The error is the reason the program could not be
run at all: it does not resolve, Cortex does not accept it, or it has no
`entry` procedure. -/
def interpretEntries (program : LaurelProgram) (fuel : Nat := 10000)
    (options : LaurelTranslateOptions := {}) : Except String InterpretOutcome := do
  let (resolved, model, _) ← match resolveLaurel options program with
    | .ok r => pure r
    | .error ds => throw s!"Laurel resolution failed: {ds.map (·.message)}"
  let (mod?, diags) := FromLaurel.run model resolved options.overflowChecks (uncheck := false)
  let some m := mod?
    | throw s!"Laurel to Cortex translation failed: {diags.map (·.message)}"
  unless m.procedures.any isEntry do
    throw "no entry point found: mark a procedure with `entry` in the Laurel source, or pass --entry <proc>"
  interpretProgram m fuel

/-- The diagnostics of `interpretEntries`, or, when it has `errors`, one error that
covers them. -/
def interpretLaurel (program : LaurelProgram) (fuel : Nat := 10000) :
    IO (Except String (Array Message)) := do
  match interpretEntries program fuel with
  | .error e => return .error e
  | .ok outcome =>
    if outcome.errors.isEmpty then return .ok outcome.diagnostics
    let errors := outcome.errors.toList.map fun (name, reason) => s!"'{name}': {reason}"
    return .error s!"{String.intercalate "; " errors} (diagnostics: {outcome.diagnostics.toList.map (·.message)})"

/-- Run the `entry` procedures of a wire program on the Cortex interpreter, as
`interpretProgram` does. The error is the reason the wire program is not a
Cortex program. -/
def interpretWire (program : Wire.Program) (fuel : Nat) : Except String InterpretOutcome := do
  let m ← (wireToCortex program).mapError (s!"invalid Cortex program: {·}")
  interpretProgram m fuel

end

end Cortex
