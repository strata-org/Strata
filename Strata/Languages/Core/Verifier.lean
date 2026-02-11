/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.Options
import Strata.Languages.Core.CallGraph
import Strata.Languages.Core.SMTEncoder
import Strata.DL.Imperative.MetaData
import Strata.DL.Imperative.SMTUtils
import Strata.DL.SMT.CexParser
import Strata.DDM.AST
import Strata.Transform.CallElim
import Strata.Transform.FilterProcedures

---------------------------------------------------------------------

namespace Strata.SMT.Encoder

open Strata.SMT.Encoder
open Strata

-- Derived from Strata.SMT.Encoder.encode.
def encodeCore (ctx : Core.SMT.Context) (prelude : SolverM Unit) (ts : List Term) :
  SolverM (List String × EncoderState) := do
  Solver.reset
  Solver.setLogic "ALL"
  prelude
  let _ ← ctx.sorts.mapM (fun s => Solver.declareSort s.name s.arity)
  ctx.emitDatatypes
  let (_ufs, estate) ← ctx.ufs.mapM (fun uf => encodeUF uf) |>.run EncoderState.init
  let (_ifs, estate) ← ctx.ifs.mapM (fun fn => encodeFunction fn.uf fn.body) |>.run estate
  let (_axms, estate) ← ctx.axms.mapM (fun ax => encodeTerm False ax) |>.run estate
  for id in _axms do
    Solver.assert id
  let (ids, estate) ← ts.mapM (encodeTerm False) |>.run estate
  for id in ids do
    Solver.assert id
  let ids := estate.ufs.values
  return (ids, estate)

end Strata.SMT.Encoder

---------------------------------------------------------------------

namespace Core.SMT
open Std (ToFormat Format format)
open Lambda Strata.SMT
-- (TODO) Use DL.Imperative.SMTUtils.

abbrev SMTModel := Map (IdentT LMonoTy Visibility) String

def SMTModel.format (model : SMTModel) : Format :=
  match model with
  | [] => ""
  | [((k, _), v)] => f!"({k}, {v})"
  | ((k, _), v) :: rest =>
    (f!"({k}, {v}) ") ++ SMTModel.format rest

instance : ToFormat SMTModel where
  format := SMTModel.format

/--
Find the Id for the SMT encoding of `x`.
-/
def getSMTId (x : (IdentT LMonoTy Visibility)) (ctx : SMT.Context) (E : EncoderState)
    : Except Format String := do
  match x with
  | (var, none) => .error f!"Expected variable {var} to be annotated with a type!"
  | (var, some ty) => do
    -- NOTE: OK to use Env.init here because ctx should already contain datatypes
    let (ty', _) ← LMonoTy.toSMTType Env.init ty ctx
    let key : Strata.SMT.UF := { id := var.name, args := [], out := ty' }
    .ok (E.ufs[key]!)

def getModel (m : String) : Except Format (List Strata.SMT.CExParser.KeyValue) := do
  let cex ← Strata.SMT.CExParser.parseCEx m
  return cex.pairs

def processModel
  (vars : List (IdentT LMonoTy Visibility)) (cexs : List Strata.SMT.CExParser.KeyValue)
  (ctx : SMT.Context) (E : EncoderState) :
  Except Format SMTModel := do
  match vars with
  | [] => return []
  | var :: vrest =>
    let id ← getSMTId var ctx E
    let value ← findModelValue id cexs
    let pair := (var, value)
    let rest ← processModel vrest cexs ctx E
    .ok (pair :: rest)
  where findModelValue id cexs : Except Format String :=
    match cexs.find? (fun p => p.key == id) with
    | none => .error f!"Cannot find model for id: {id}"
    | some p => .ok p.value

inductive Result where
  -- Also see Strata.SMT.Decision.
  | sat (m : SMTModel)
  | unsat
  | unknown
  | err (msg : String)
deriving DecidableEq, Repr

def Result.isSat (r : Result) : Bool :=
  match r with | .sat _ => true | _ => false

def Result.formatWithVerbose (r : Result) (verbose : Bool) : Format :=
  match r with
  | .sat m  =>
    if (not verbose) || m.isEmpty then
      f!"sat"
    else f!"sat\nModel: {m}"
  | .unsat => f!"unsat"
  | .unknown => f!"unknown"
  | .err msg => f!"err {msg}"

instance : ToFormat Result where
  format r := r.formatWithVerbose true

def Result.formatModelIfSat (r : Result) (verbose : Bool) : Format :=
  match r with
  | .sat m =>
    if (not verbose) || m.isEmpty then
      f!""
    else
      f!"\nModel:\n{m}"
  | _ => f!""

def runSolver (solver : String) (args : Array String) : IO IO.Process.Output := do
  let output ← IO.Process.output {
    cmd := solver
    args := args
  }
  -- dbg_trace f!"runSolver: exitcode: {repr output.exitCode}\n\
  --                         stderr: {repr output.stderr}\n\
  --                         stdout: {repr output.stdout}"
  return output

def solverResult (vars : List (IdentT LMonoTy Visibility)) (output : IO.Process.Output)
    (ctx : SMT.Context) (E : EncoderState) (smtsolver : String) :
  Except Format Result := do
  let stdout := output.stdout
  let pos := stdout.find (· == '\n')
  let verdict := stdout.extract stdout.startPos pos |>.trimAscii
  let rest := stdout.extract pos stdout.endPos
  match verdict with
  | "sat"     =>
    let rawModel ← getModel rest
    -- We suppress any model processing errors.
    -- Likely, these would be because of the suboptimal implementation
    -- of the model parser, which shouldn't hold back useful
    -- feedback (i.e., problem was `sat`) from the user.
    match (processModel vars rawModel ctx E) with
    | .ok model => .ok (.sat model)
    | .error _model_err => (.ok (.sat []))
  | "unsat"   =>  .ok .unsat
  | "unknown" =>  .ok .unknown
  | _     =>
    let stderr := output.stderr
    let hasExecError := (stderr.splitOn "could not execute external process").length > 1
    let hasFileError := (stderr.splitOn "No such file or directory").length > 1
    let suggestion := if (hasExecError || hasFileError) && smtsolver == defaultSolver then s!" \nEnsure {defaultSolver} is on your PATH or use --solver to specify another SMT solver." else ""
    .error s!"stderr:{stderr}{suggestion}\nsolver stdout: {output.stdout}\n"

def getSolverPrelude : String → SolverM Unit
| "z3" => do
  -- These options are set by the standard Boogie implementation and are
  -- generally good for the Boogie dialect, too, though we may want to
  -- have more fine-grained criteria for when to use them.
  Solver.setOption "smt.mbqi" "false"
  Solver.setOption "auto_config" "false"
| "cvc5" => return ()
| _ => return ()

def getSolverFlags (options : Options) (solver : String) : Array String :=
  let produceModels :=
    match solver with
    | "cvc5" => #["--produce-models"]
    -- No need to specify -model for Z3 because we already have `get-value`
    -- in the generated SMT file.
    | _ => #[]
  let setTimeout :=
    match solver with
    | "cvc5" => #[s!"--tlimit={options.solverTimeout*1000}"]
    | "z3" => #[s!"-T:{options.solverTimeout}"]
    | _ => #[]
  produceModels ++ setTimeout

def dischargeObligation
  (options : Options)
  (vars : List (IdentT LMonoTy Visibility)) (smtsolver filename : String)
  (terms : List Term) (ctx : SMT.Context)
  : IO (Except Format (SMT.Result × EncoderState)) := do
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.write
  let solver ← Solver.fileWriter handle
  let prelude := getSolverPrelude smtsolver
  let (ids, estate) ← Strata.SMT.Encoder.encodeCore ctx prelude terms solver
  let _ ← solver.checkSat ids -- Will return unknown for Solver.fileWriter
  if options.verbose > .normal then IO.println s!"Wrote problem to {filename}."
  let flags := getSolverFlags options smtsolver
  let output ← runSolver smtsolver (#[filename] ++ flags)
  match SMT.solverResult vars output ctx estate smtsolver with
  | .error e => return .error e
  | .ok result => return .ok (result, estate)

end Core.SMT
---------------------------------------------------------------------

namespace Core
open Imperative Lambda Strata.SMT
open Std (ToFormat Format format)
open Strata

/--
Analysis outcome of a verification condition.
-/
inductive Outcome where
  | pass
  | fail
  | unknown
  | implementationError (e : String)
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Outcome where
  format vr := match vr with
    | .pass => "✅ pass"
    | .fail => "❌ fail"
    | .unknown => "🟡 unknown"
    | .implementationError e => s!"🚨 Implementation Error! {e}"

/--
A collection of all information relevant to a verification condition's
analysis.
-/
structure VCResult where
  obligation : Imperative.ProofObligation Expression
  smtResult : SMT.Result := .unknown
  result : Outcome := .unknown
  estate : EncoderState := EncoderState.init
  verbose : VerboseMode := .normal

/--
Map the result from an SMT backend engine to an `Outcome`.
-/
def smtResultToOutcome (r : SMT.Result) (isCover : Bool) : Outcome :=
  match r with
  | .unknown => .unknown
  | .unsat =>
    if isCover then .fail else .pass
  | .sat _ =>
    if isCover then .pass else .fail
  | .err e => .implementationError e

instance : ToFormat VCResult where
  format r := f!"Obligation: {r.obligation.label}\n\
                 Property: {r.obligation.property}\n\
                 Result: {r.result}\
                 {r.smtResult.formatModelIfSat true}"

def VCResult.isSuccess (vr : VCResult) : Bool :=
  match vr.result with | .pass => true | _ => false

def VCResult.isFailure (vr : VCResult) : Bool :=
  match vr.result with | .fail => true | _ => false

def VCResult.isUnknown (vr : VCResult) : Bool :=
  match vr.result with | .unknown => true | _ => false

def VCResult.isImplementationError (vr : VCResult) : Bool :=
  match vr.result with | .implementationError _ => true | _ => false

def VCResult.isNotSuccess (vcResult : Core.VCResult) :=
  !Core.VCResult.isSuccess vcResult

abbrev VCResults := Array VCResult

def VCResults.format (rs : VCResults) : Format :=
  let rsf := rs.map (fun r => f!"{Format.line}{r}")
  Format.joinSep rsf.toList Format.line

instance : ToFormat VCResults where
  format := VCResults.format

instance : ToString VCResults where
  toString rs := toString (VCResults.format rs)

/--
Preprocess a proof obligation before handing it off to a backend engine.
-/
def preprocessObligation (obligation : ProofObligation Expression) (p : Program)
    (options : Options) : EIO DiagnosticModel (ProofObligation Expression × Option VCResult) := do
  match obligation.property with
  | .cover =>
    if obligation.obligation.isFalse then
      -- If PE determines that the consequent is false, then we can immediately
      -- report a failure.
      let result := { obligation, result := .fail, verbose :=  options.verbose }
      return (obligation, some result)
    else
      return (obligation, none)
  | .assert =>
    if obligation.obligation.isTrue then
      -- We don't need the SMT solver if PE (partial evaluation) is enough to
      -- reduce the consequent to true.
      let result := { obligation, result := .pass, verbose := options.verbose }
      return (obligation, some result)
    else if obligation.obligation.isFalse && obligation.assumptions.isEmpty then
      -- If PE determines that the consequent is false and the path conditions
      -- are empty, then we can immediately report a verification failure. Note
      -- that we go to the SMT solver if the path conditions aren't empty --
      -- after all, the path conditions could imply false, which the PE isn't
      -- capable enough to infer.
      let prog := f!"\n\nEvaluated program:\n{p}"
      dbg_trace f!"\n\nObligation {obligation.label}: failed!\
                   \n\nResult obtained during partial evaluation.\
                   {if options.verbose >= .normal then prog else ""}"
      let result := { obligation, result := .fail, verbose := options.verbose }
      return (obligation, some result)
    else if options.removeIrrelevantAxioms then
      -- We attempt to prune the path conditions by excluding all irrelevant
      -- axioms w.r.t. the consequent to reduce the size of the proof
      -- obligation.
      let cg := Program.toFunctionCG p
      let fns := obligation.obligation.getOps.map CoreIdent.toPretty
      let relevant_fns := (fns ++ (CallGraph.getAllCalleesClosure cg fns)).dedup
      let irrelevant_axs := Program.getIrrelevantAxioms p relevant_fns
      let new_assumptions := Imperative.PathConditions.removeByNames obligation.assumptions irrelevant_axs
      return ({ obligation with assumptions := new_assumptions }, none)
    else
      return (obligation, none)

/--
Invoke a backend engine and get the analysis result for a
given proof obligation.
-/
def getObligationResult (terms : List Term) (ctx : SMT.Context)
    (obligation : ProofObligation Expression) (p : Program)
    (smtsolver : String) (options : Options) (counter : IO.Ref Nat)
    (tempDir : System.FilePath) : EIO DiagnosticModel VCResult := do
  let prog := f!"\n\nEvaluated program:\n{p}"
  let counterVal ← counter.get
  counter.set (counterVal + 1)
  let filename := tempDir / s!"{obligation.label}_{counterVal}.smt2"
  let ans ←
      IO.toEIO
        (fun e => DiagnosticModel.fromFormat f!"{e}")
        (SMT.dischargeObligation options
          (ProofObligation.getVars obligation) smtsolver
            filename.toString
          terms ctx)
  match ans with
  | .error e =>
    dbg_trace f!"\n\nObligation {obligation.label}: SMT Solver Invocation Error!\
                 \n\nError: {e}\
                 {if options.verbose >= .normal then prog else ""}"
    .error <| DiagnosticModel.fromFormat e
  | .ok (smt_result, estate) =>
    let result :=  { obligation,
                     result := smtResultToOutcome smt_result (obligation.property == .cover)
                     smtResult := smt_result,
                     estate,
                     verbose := options.verbose }
    return result

def verifySingleEnv (smtsolver : String) (pE : Program × Env) (options : Options)
    (counter : IO.Ref Nat) (tempDir : System.FilePath) :
    EIO DiagnosticModel VCResults := do
  let (p, E) := pE
  match E.error with
  | some err =>
    .error <| DiagnosticModel.fromFormat s!"🚨 Error during evaluation!\n\
              {format err}\n\n\
              Evaluated program: {p}\n\n"
  | _ =>
    let mut results := (#[] : VCResults)
    for obligation in E.deferred do
      let (obligation, maybeResult) ← preprocessObligation obligation p options
      if h : maybeResult.isSome then
        let result := Option.get maybeResult h
        results := results.push result
        if result.isSuccess then
          -- No need to use the SMT solver.
          continue
        if (result.isFailure || result.isImplementationError) then
          if options.verbose >= .normal then
            let prog := f!"\n\nEvaluated program:\n{p}"
            dbg_trace f!"\n\nResult: {result}\n{prog}"
          if options.stopOnFirstError then break else continue
      -- For `unknown` results, we appeal to the SMT backend below.
      let maybeTerms := ProofObligation.toSMTTerms E obligation
      match maybeTerms with
      | .error err =>
        let err := f!"SMT Encoding Error! " ++ err
        let result := { obligation,
                        result := .implementationError (toString err),
                        verbose := options.verbose }
        if options.verbose >= .normal then
          let prog := f!"\n\nEvaluated program:\n{p}"
          dbg_trace f!"\n\nResult: {result}\n{prog}"
        results := results.push result
        if options.stopOnFirstError then break
      | .ok (terms, ctx) =>
        let result ← getObligationResult terms ctx obligation p smtsolver options
                      counter tempDir
        results := results.push result
        if result.isNotSuccess then
        if options.verbose >= .normal then
          let prog := f!"\n\nEvaluated program:\n{p}"
          dbg_trace f!"\n\nResult: {result}\n{prog}"
          if options.stopOnFirstError then break
    return results

def verify (smtsolver : String) (program : Program)
    (tempDir : System.FilePath)
    (proceduresToVerify : Option (List String) := none)
    (options : Options := Options.default)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default)
    : EIO DiagnosticModel VCResults := do
  let finalProgram ← match proceduresToVerify with
    | none => .ok program  -- Verify all procedures (default).
    | some procs =>
       -- Verify specific procedures. By default, we apply the call elimination
       -- transform to the targeted procedures to inline the contracts of any
       -- callees. Call elimination is applied once, since once is enough to
       -- replace all calls with contracts.
      let passes := fun prog => do
        let prog ← FilterProcedures.run prog procs
        let (_changed,prog) ← CallElim.callElim' prog
        let prog ← FilterProcedures.run prog procs
        return prog
      let res := Transform.run program passes
      match res with
      | .ok prog => .ok prog
      | .error e => .error (DiagnosticModel.fromFormat f!"❌ Transform Error. {e}")
  match Core.typeCheckAndPartialEval options finalProgram moreFns with
  | .error err =>
    .error { err with message := s!"❌ Type checking error.\n{err.message}" }
  | .ok pEs =>
    let counter ← IO.toEIO (fun e => DiagnosticModel.fromFormat f!"{e}") (IO.mkRef 0)
    let VCss ← if options.checkOnly then
                 pure []
               else
                 (List.mapM (fun pE => verifySingleEnv smtsolver pE options counter tempDir) pEs)
    .ok VCss.toArray.flatten

end Core
---------------------------------------------------------------------

namespace Strata

open Lean.Parser
open Strata (DiagnosticModel FileRange)

def typeCheck (ictx : InputContext) (env : Program) (options : Options := Options.default)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default) :
  Except DiagnosticModel Core.Program := do
  let (program, errors) := TransM.run ictx (translateProgram env)
  if errors.isEmpty then
    -- dbg_trace f!"AST: {program}"
    Core.typeCheck options program moreFns
  else
    .error <| DiagnosticModel.fromFormat s!"DDM Transform Error: {repr errors}"

def Core.getProgram
  (p : Strata.Program)
  (ictx : InputContext := Inhabited.default) : Core.Program × Array String :=
  TransM.run ictx (translateProgram p)

def verify
    (smtsolver : String) (env : Program)
    (ictx : InputContext := Inhabited.default)
    (proceduresToVerify : Option (List String) := none)
    (options : Options := Options.default)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default)
    (tempDir : Option String := .none)
    : IO Core.VCResults := do
  let (program, errors) := Core.getProgram env ictx
  if errors.isEmpty then
    let runner tempDir :=
      EIO.toIO (fun dm => IO.Error.userError (toString (dm.format (some ictx.fileMap))))
                  (Core.verify smtsolver program tempDir proceduresToVerify options moreFns)
    match tempDir with
    | .none =>
      IO.FS.withTempDir runner
    | .some p =>
      IO.FS.createDirAll ⟨p⟩
      runner ⟨p⟩
  else
    panic! s!"DDM Transform Error: {repr errors}"

def toDiagnosticModel (vcr : Core.VCResult) : Option DiagnosticModel := do
  match vcr.result with
  | .pass => none  -- Verification succeeded, no diagnostic
  | result =>
    let message := match result with
      | .fail => "assertion does not hold"
      | .unknown => "assertion could not be proved"
      | .implementationError msg => s!"verification error: {msg}"
      | _ => panic "impossible"

    let .some fileRangeElem := vcr.obligation.metadata.findElem Imperative.MetaData.fileRange
      | some {
          fileRange := default
          message := s!"Internal error: diagnostics without position! obligation label: {repr vcr.obligation.label}"
        }

    let result := match fileRangeElem.value with
      | .fileRange fileRange =>
        some {
          fileRange := fileRange
          message := message
        }
      | _ =>
        some {
          fileRange := default
          message := s!"Internal error: diagnostics without position! Metadata value for fileRange key was not a fileRange. obligation label: {repr vcr.obligation.label}"
        }
    result

structure Diagnostic where
  start : Lean.Position
  ending : Lean.Position
  message : String
  deriving Repr, BEq

def DiagnosticModel.toDiagnostic (files: Map Strata.Uri Lean.FileMap) (dm: DiagnosticModel): Diagnostic :=
  let fileMap := (files.find? dm.fileRange.file).get!
  let startPos := fileMap.toPosition dm.fileRange.range.start
  let endPos := fileMap.toPosition dm.fileRange.range.stop
  {
    start := { line := startPos.line, column := startPos.column }
    ending := { line := endPos.line, column := endPos.column }
    message := dm.message
  }

def Core.VCResult.toDiagnostic (files: Map Strata.Uri Lean.FileMap) (vcr : Core.VCResult) : Option Diagnostic := do
  let modelOption := toDiagnosticModel vcr
  modelOption.map (fun dm => dm.toDiagnostic files)

end Strata

---------------------------------------------------------------------
