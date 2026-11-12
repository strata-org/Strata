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
public import Strata.Transform.ProcedureInlining
import Strata.DL.Imperative.StmtCFGCallSemantics

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

/-- Replace each call to a procedure named in `names` by the body of that procedure.

    A Cortex procedure has no postcondition, so the Core procedure made from it has none,
    and a caller verified against it learns nothing from a call: every variable the callee
    may write is arbitrary afterwards. Inlining is what lets a caller rely on what a named
    procedure does.

    A procedure that can reach itself through calls is left as a call, since inlining it
    would not end.

    Core checks a callee's preconditions at the call, and the inliner copies only the body.
    So each call that is inlined is first preceded by an `assert` of every checked
    precondition of its callee, with the call's arguments for the parameters and the call's
    location, which is what Core would have checked at the call, and an `assume` of it,
    which is what the callee's body had on entry.

    A call that throws assigns none of its results, and the Cortex interpreter runs it so;
    the inlined body of a callee that can throw would hand the caller the values its
    outputs had at the `throw`. So the results of such a call, other than `$callThrown`
    and `$callExc`, go to fresh temporaries, and each target gets its temporary only
    when the call did not throw. An in-out argument is kept: a callee's write to one is
    visible to the caller also when the callee throws. -/
def inlineProcedures (names : List String) (core : Core.Program) : Except String Core.Program :=
  if names.isEmpty then .ok core else
  let cg := core.toProcedureCG
  let inlined := fun (callee : String) => names.contains callee && !cg.isRecursive callee
  let doInline := fun (_ : Option String) (callee : String) (_ : Core.Transform.CachedAnalyses) =>
    inlined callee
  let exnOuts := [LowerExceptions.callThrown, LowerExceptions.callExc]
  let prepareCall : Core.Statement → Core.Transform.CoreTransformM (Option (List Core.Statement))
    | .cmd (.call callee callArgs md) => do
      if !inlined callee then return none
      let some proc := Core.Program.Procedure.find? core ⟨callee, ()⟩ | return none
      let n ← Core.Transform.bumpCounter "cortexInline"
      let checks := (Imperative.Calls.checksAtCall md proc.spec.preconditions).filter fun (_, c) =>
        c.attr matches .Default
      let σ := (proc.header.inputs.map (·.1.name)).zip (Imperative.Calls.getInputExprs callArgs)
      -- The assert checks the precondition; the assume then gives the inlined body the fact,
      -- as the callee's entry would have.
      let asserts : List Core.Statement := checks.flatMap fun (label, c) =>
        let cond := substFvars σ c.expr
        [.cmd (.cmd (.assert s!"$pre{n}_{label}" cond c.md)),
         .cmd (.cmd (.assume s!"$pre{n}_{label}_assumed" cond c.md))]
      let results := Imperative.CallArg.resultArgs callArgs
      let throws := results.any fun | .outArg x => x.name == LowerExceptions.callThrown | _ => false
      let renames : List (String × String × Lambda.LMonoTy) :=
        if !throws then [] else
        (results.zip (proc.header.outputs.map (·.2))).zipIdx.filterMap fun
          | ((.outArg x, ty), i) =>
            if exnOuts.contains x.name then none else some (x.name, s!"$inlineResult{n}_{i}", ty)
          | _ => none
      if checks.isEmpty && renames.isEmpty then return none
      let callArgs := callArgs.map fun
        | .outArg x => match renames.find? (·.1 == x.name) with
          | some (_, tmp, _) => .outArg ⟨tmp, ()⟩
          | none => .outArg x
        | a => a
      let inits : List Core.Statement := renames.map fun (_, tmp, ty) =>
        .cmd (.cmd (.init ⟨tmp, ()⟩ (mono ty) .nondet md))
      let thrown := mkFvar LowerExceptions.callThrown
      let copies : List Core.Statement := renames.map fun (x, tmp, _) =>
        .cmd (.cmd (.set ⟨x, ()⟩ (.det (.ite () thrown (mkFvar x) (mkFvar tmp))) md))
      return some (asserts ++ inits ++ [.cmd (.call callee callArgs md)] ++ copies)
    | _ => return none
  match Core.Transform.run core (fun p => do
      let (_, p) ← Core.Transform.runProgram prepareCall p
      Core.Transform.runProgramUntil (Core.ProcedureInlining.inlineCallCmd (doInline := doInline)) p) with
  | .ok (_, p) => .ok p
  | .error e => .error s!"{e.message}"

/-- Translate a Laurel program to Core through Cortex. With `cfg`, procedure
bodies are Core CFG bodies; otherwise they are structured. The verifier
(`Core.verify`) and the evaluator behind `Core.Program.interpretEntries` accept
only structured bodies. -/
def translate (options : LaurelTranslateOptions) (program : LaurelProgram) (cfg : Bool := false)
    (inline : List String := []) :
    Option Core.Program × List Message :=
  if options.passes.isSome then
    (none, [Message.fromString "--phases and --skip-phases select Laurel phases, which the Cortex pipeline does not run"
      MessageKind.userError])
  else if cfg && !inline.isEmpty then
    (none, [Message.fromString "--inline-procedures works on structured bodies, which the CFG translation does not produce"
      MessageKind.userError])
  else
  match resolveLaurel options program with
  | .error ds => (none, ds)
  | .ok (resolved, model, ds) =>
    match FromLaurel.run model resolved options.overflowChecks with
    | (none, d) =>
      let all := ds ++ d
      (none, if all.isEmpty then [Message.fromString "Laurel to Cortex translation failed" MessageKind.strataBug] else all)
    | (some m, d) =>
      match (if cfg then toCoreProgramCFG m else toCoreProgram m >>= inlineProcedures inline) with
      | .ok core => (some core, ds ++ d)
      | .error e => (none, ds ++ d ++ [Message.fromString s!"Cortex lowering failed: {e}" MessageKind.strataBug])

def runCoreVerify (core : Core.Program) (options : LaurelVerifyOptions) :
    IO (Except Message Core.VCResults) := do
  let verifyOptions := effectiveCoreVerifyOptions options
  let runner tempDir : IO (Except Message Core.VCResults) :=
    (_root_.Core.verify core tempDir verifyOptions).toBaseIO
  match verifyOptions.vcDirectory with
  | .none => IO.FS.withTempDir runner
  | .some p => IO.FS.createDirAll ⟨p.toString⟩; runner ⟨p.toString⟩

def verifyToVcResults (program : LaurelProgram) (options : LaurelVerifyOptions := default)
    (inline : List String := []) :
    IO (Option Core.VCResults × List Message) := do
  let (core?, diags) := translate options.translateOptions program (inline := inline)
  match core? with
  | none => return (none, diags)
  | some core =>
    match ← runCoreVerify core options with
    | .ok results => return (some results, diags)
    | .error dm => return (none, diags ++ [dm])

def verifyCoreToMessages (core : Core.Program) (diags : List Message) (options : LaurelVerifyOptions) :
    IO (Array Message) := do
  match ← runCoreVerify core options with
  | .error dm => return (diags ++ [dm]).toArray
  | .ok results =>
    let phases := _root_.Core.coreAbstractedPhases (options := effectiveCoreVerifyOptions options)
    return (diags ++ results.mergeByAssertion.toList.filterMap (Strata.toMessage · phases)).toArray

def verifyToMessages (program : LaurelProgram) (options : LaurelVerifyOptions := default)
    (inline : List String := []) :
    IO (Array Message) := do
  let (core?, diags) := translate options.translateOptions program (inline := inline)
  match core? with
  | none => return diags.toArray
  | some core => verifyCoreToMessages core diags options

/-- `inline` names the procedures whose calls are replaced by their bodies; see `inlineProcedures`. -/
def wireToCore (program : Wire.Program) (inline : List String := []) : Except Message Core.Program :=
  match program.withPreludes >>= Wire.Program.toCortex with
  | .error e => .error (Message.fromString s!"invalid Cortex program: {e}" MessageKind.userError)
  | .ok m => match toCoreProgram m >>= inlineProcedures inline with
    | .ok core => .ok core
    | .error e => .error (Message.fromString s!"Cortex lowering failed: {e}" MessageKind.strataBug)

def verifyWireToMessages (program : Wire.Program) (options : LaurelVerifyOptions := default)
    (inline : List String := []) : IO (Array Message) := do
  match wireToCore program inline with
  | .error dm => return #[dm]
  | .ok core => verifyCoreToMessages core [] options

end

end Cortex
