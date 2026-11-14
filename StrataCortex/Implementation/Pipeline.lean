/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelCompilationPipeline
public import StrataLaurel.Implementation.InferThrows
public import StrataCortex.Implementation.FromLaurel
public import Strata.Languages.Cortex.Pipeline
public import Strata.Languages.Cortex.Wire
public import Strata.Languages.Cortex.JavaPrelude

namespace Cortex

open Strata Strata.Laurel

public section

def resolveLaurel (options : LaurelTranslateOptions) (program : LaurelProgram) :
    Except (List Message) (LaurelProgram × SemanticModel × List Message) :=
  let dollar := validateNoDollarNames program
  if dollar.any (·.kind != .warning) then .error dollar else
  let program := { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures
    types := coreDefinitionsForLaurel.types ++ program.types }
  let result := resolveWithInferredThrows program (gradualTypes := options.gradualTypes)
    (realizeCoercion := options.realizeCoercion) (toBool := options.toBool)
    (reservedNames := options.reservedNames)
    -- An entry procedure may use a global of a constrained type here. The Laurel pipeline
    -- enforces such a global's constraint through contracts on the procedures that take it
    -- as a hidden parameter, and an entry procedure takes none, so it refuses that use.
    -- `LowerCTE` instead checks the constraint in the body: where the global is
    -- initialized, at each assignment and around each call, which an entry procedure has.
    (entryConstrainedGlobals := true)
  let errs := result.errors.toList
  if errs.any (·.kind != .warning) then .error errs else
  if !programTouchesStack result.program then .ok (result.program, result.model, errs) else
  let (eliminated, stackDiags) := eliminateStack result.program (exprReadsHeap result.model.heapReaders)
    (some result.model.heapWriters)
  if !stackDiags.isEmpty then .error (errs ++ stackDiags) else
  let again := resolveWithInferredThrows eliminated (gradualTypes := options.gradualTypes)
    (realizeCoercion := options.realizeCoercion) (toBool := options.toBool)
    (reservedNames := options.reservedNames) (entryConstrainedGlobals := true)
  let errs' := again.errors.toList
  let all := errs ++ errs'.filter (!errs.contains ·)
  if errs'.any (·.kind != .warning) then .error all else .ok (again.program, again.model, all)

/-- Translate a Laurel program to Cortex. There is no Cortex program when the
Laurel program does not resolve or Cortex does not accept it; the messages say
why. -/
def toCortex (options : LaurelTranslateOptions) (program : LaurelProgram) :
    Option UnorderedProgram × List Message :=
  match resolveLaurel options program with
  | .error ds => (none, ds)
  | .ok (resolved, model, ds) =>
    match FromLaurel.run model resolved options.overflowChecks with
    | (none, d) =>
      let all := ds ++ d
      (none, if all.isEmpty then [Message.fromString "Laurel to Cortex translation failed" MessageKind.strataBug] else all)
    | (some m, d) => (some m, ds ++ d)

/-- Translate a Laurel program to Core through Cortex. Procedure bodies are
Core CFG bodies, which Core can type-check and print. The verifier
(`Core.verify`) and the evaluator behind `Core.Program.interpretEntries` accept
only structured bodies, so they do not run the result. -/
def translate (options : LaurelTranslateOptions) (program : LaurelProgram) :
    Option Core.Program × List Message :=
  if options.passes.isSome then
    (none, [Message.fromString "--phases and --skip-phases select Laurel phases, which the Cortex pipeline does not run"
      MessageKind.userError])
  else
  match toCortex options program with
  | (none, ds) => (none, ds)
  | (some m, ds) =>
    match toCoreProgram m with
    | .ok core => (some core, ds)
    | .error e => (none, ds ++ [Message.fromString s!"Cortex lowering failed: {e}" MessageKind.strataBug])

/-- The Cortex program that a wire program describes, with the preludes it
names. -/
def wireToCortex (program : Wire.Program) : Except String UnorderedProgram :=
  program.withPreludes >>= Wire.Program.toCortex

end

end Cortex
