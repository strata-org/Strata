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
public import Strata.Languages.Core.ProgramEval

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
  | .procedureWithoutBody n => s!"call to procedure {n}, which has no body"
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

def interpretableCore (core : _root_.Core.Program) : Except String _root_.Core.Program := do
  let core ← match _root_.Core.typeCheck _root_.Core.VerifyOptions.quiet core with
    | .ok prog => pure prog
    | .error e => throw s!"Core type checking failed: {e.message}"
  return _root_.Core.Program.inlineBodiedFunctions core

def toInterpretableCore (options : LaurelTranslateOptions) (program : LaurelProgram) :
    Except String _root_.Core.Program := do
  let core ← match translate options program with
    | (some core, _) => pure core
    | (none, diags) => throw s!"Laurel to Core translation failed: {diags.map (·.message)}"
  interpretableCore core

/-- Run every entry procedure of `m` on the Cortex interpreter, after the cleanup passes,
LowerDispatch, LowerGlobals, FieldCasts and LowerCTE. With `cleanup := false` the cleanup
passes are skipped, for comparing the two runs.
Returns the failed checks as diagnostics, and the runs that stopped or left an
assertion unevaluated as errors. -/
def interpretProgram (m : Cortex.UnorderedProgram) (fuel : Nat) (cleanup : Bool := true) :
    Except String (Array Message × Array String) := do
  let m ← if cleanup then
      match Cortex.Cleanup.run m with
      | .ok m => pure m
      | .error e => throw s!"Cleanup: {e}"
    else pure m
  let m ← match Cortex.LowerDispatch.run m >>= Cortex.LowerGlobals.run >>= Cortex.FieldCasts.run >>= Cortex.LowerCTE.runWith true with
    | .ok m => pure m
    | .error e => throw s!"lowering: {e}"
  let mut out : Array Message := #[]
  let mut seen : Std.HashSet Message := {}
  let mut errors : Array String := #[]
  for p in m.procedures do
    unless isEntry p do continue
    match runEntry m fuel p with
    | .error e => errors := errors.push s!"'{p.name}': {cortexStopMessage e}"
    | .ok (final, trace) =>
      if unevaluated trace > 0 then
        errors := errors.push s!"'{p.name}': an assertion could not be evaluated"
      let fs := failures trace
      let msgs := fs.filterMap fun (md, summary) =>
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
  return (out, errors)

def interpretLaurel (program : LaurelProgram) (fuel : Nat := 10000) :
    IO (Except String (Array Message)) := do
  let (resolved, model, _) ← match resolveLaurel {} program with
    | .ok r => pure r
    | .error ds => return .error s!"Laurel resolution failed: {ds.map (·.message)}"
  let (mod?, diags) := FromLaurel.run model resolved (uncheck := false)
  match mod? with
  | none => return .error s!"Laurel to Cortex translation failed: {diags.map (·.message)}"
  | some m =>
    match interpretProgram m fuel with
    | .error e => return .error e
    | .ok (out, errors) =>
      if errors.isEmpty then return .ok out
      return .error s!"{String.intercalate "; " errors.toList} (diagnostics: {out.toList.map (·.message)})"

/-- Run a wire program's entry procedures on the Cortex interpreter. -/
def interpretWire (program : Wire.Program) (fuel : Nat) : Except String (Array Message × Array String) := do
  match program.withPreludes >>= Wire.Program.toCortex with
  | .error e => throw s!"invalid Cortex program: {e}"
  | .ok m => interpretProgram m fuel

end

end Cortex
