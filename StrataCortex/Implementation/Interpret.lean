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
  | .unknownArrayType n => s!"unknown array type {n}"
  | .negativeArrayLength n => s!"array length {n} is negative"
  | .indexOutOfRange i n => s!"index {i} is out of range for an array of length {n}"
  | .elementTypeMismatch t a => s!"element type {Std.format (t : Lambda.LTy)} does not match array type {a}"

/-- What running the `entry` procedures of a program on the Cortex interpreter
produced. -/
structure InterpretOutcome where
  /-- The failed assertions and uncaught exceptions, each reported once. -/
  diagnostics : Array Message := #[]
  /-- The entry procedures that did not run to completion, each with the reason. -/
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
  let mut seen : Std.HashSet Message := {}
  let mut errors : Array (String × String) := #[]
  for p in m.procedures do
    unless isEntry p do continue
    match runEntry m fuel p with
    | .error e => errors := errors.push (p.name, cortexStopMessage e)
    | .ok (final, trace) =>
      if unevaluated trace > 0 then
        errors := errors.push (p.name, "an assertion could not be evaluated")
      -- A failed check without a source range is in a helper procedure, whose
      -- precondition reports the failure at the call.
      let msgs := (failures trace).filterMap fun (md, summary) =>
        (Imperative.getFileRange md).map fun fr => Message.withRange fr s!"{summary} does not hold"
      let msgs := match final with
        | .raised ρ v md =>
          let fallback := match dynType ρ.heap v with
            | some ty => s!"uncaught exception '{ty}' is not thrown"
            | none => "uncaught exception is not thrown"
          let summary := ((md : Cortex.MD).getPropertySummary).getD fallback
          match Imperative.getFileRange (md : Cortex.MD) with
          | some fr => msgs ++ [Message.withRange fr s!"{summary} does not hold"]
          | none => msgs ++ [Message.fromString s!"'{p.name}': {summary} does not hold"]
        | _ => msgs
      for dm in msgs do
        unless seen.contains dm do
          out := out.push dm
          seen := seen.insert dm
  return { diagnostics := out, errors }

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

/-- The diagnostics of `interpretEntries`, or one error that also covers every
entry procedure that did not run to completion. -/
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
