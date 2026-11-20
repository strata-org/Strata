/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelCompilationPipeline
public import StrataCortex.Implementation.Pipeline
public import Strata.Languages.Cortex.Interpreter
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
  | .at _ r => cortexStopMessage r

/-- Where a run stopped (`StopReason.locate`), when that has a source location. -/
def stopLocation : StopReason → Option Strata.FileRange
  | .at md _ => Imperative.getFileRange md
  | _ => none

/-- What running the `entry` procedures of a program on the Cortex interpreter
produced. -/
structure InterpretOutcome where
  /-- The failed assertions, the uncaught exceptions and the places of the interpreter errors, each reported once. -/
  diagnostics : Array Message := #[]
  /-- The entry procedures that ended on an interpreter error, could not evaluate an assertion, or failed without a
  source location, each with the reason. -/
  errors : Array (String × String) := #[]

/-- Run every `entry` procedure of `m` on the Cortex interpreter, after the
cleanup passes, LowerDispatch, LowerGlobals, FieldCasts and LowerCTE, giving
each procedure and each call `fuel` steps. With `cleanup := false` the cleanup
passes are skipped, for comparing the two runs. The error is the reason a pass
rejected the program. -/
def interpretProgram (m : Cortex.UnorderedProgram) (fuel : Nat) (cleanup : Bool := true) :
    Except String InterpretOutcome := do
  let m ← if cleanup then (Cortex.Cleanup.run m).mapError (s!"Cleanup: {·}") else pure m
  let m ← (Cortex.LowerDispatch.run m >>= Cortex.LowerGlobals.run >>= Cortex.FieldCasts.run
    >>= Cortex.LowerCTE.runWith true).mapError (s!"lowering: {·}")
  let mut out : Array Message := #[]
  let mut errors : Array (String × String) := #[]
  for p in m.procedures do
    unless isEntry p do continue
    match runEntry m fuel p with
    | .error e =>
      errors := errors.push (p.name, cortexStopMessage e)
      -- An interpreter error is also reported where it happened, when that has a source range.
      if let some fr := stopLocation e then
        out := out.push (Message.withRange fr s!"the interpreter fails here: {cortexStopMessage e}")
    | .ok (final, trace) =>
      if unevaluated trace > 0 then
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
      for (md, summary) in failures trace ++ escaped do
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
