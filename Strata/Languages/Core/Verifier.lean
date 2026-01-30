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
deriving DecidableEq, Repr, Inhabited

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
  return output

-- def readLinesUntilVerdict (lines : List String) : List String × List String :=


def parseVerdictWithModel (vars : List (IdentT LMonoTy Visibility))
    (verdict model : String) (ctx : SMT.Context) (E : EncoderState) :
    Except Format Result := do
  match verdict with
  | "sat"     =>
    let rawModel ← getModel model
    -- We suppress any model processing errors.
    -- Likely, these would be because of the suboptimal implementation
    -- of the model parser, which shouldn't hold back useful
    -- feedback (i.e., problem was `sat`) from the user.
    match (processModel vars rawModel ctx E) with
    | .ok model => .ok (.sat model)
    | .error _model_err => (.ok (.sat []))
  | "unsat"   =>  .ok .unsat
  | _ =>  .ok .unknown

partial def parseVerdictsWithModel (vars : List (IdentT LMonoTy Visibility))
    (lines : List String) (ctx : SMT.Context) (E : EncoderState) :
    Except Format (List Result) := do
  dbg_trace f!"lines: {lines}"
  match lines with
  | [] =>
    .ok []
  | verdict :: model :: rest =>
    if !isVerdict verdict then
      .error f!"SMT Solver Error! Ill-formed verdict: {verdict}"
    else
      let (modelStr, restLines) := if isVerdict model then ("", model :: rest) else (model, rest)
      let result ← parseVerdictWithModel vars verdict modelStr ctx E
      let restResult ← parseVerdictsWithModel vars restLines ctx E
      return (result :: restResult)
  | verdict :: rest =>
    if !isVerdict verdict then
      .error f!"SMT Solver Error! Ill-formed verdict: {verdict}"
    else
      let result ← parseVerdictWithModel vars verdict "" ctx E
      let restResult ← parseVerdictsWithModel vars rest ctx E
      return (result :: restResult)
  where isVerdict (s : String) : Bool :=
    s ∈ ["unsat", "sat", "unknown"]

/--
Parse SMT solver output from (possibly) multiple `check-sat` calls.
Returns a list of results in order, where each result corresponds to one
`check-sat`.
-/
def solverResults (vars : List (IdentT LMonoTy Visibility))
    (output : IO.Process.Output) (ctx : SMT.Context) (E : EncoderState) :
    Except Format (List Result) := do
  let lines := (output.stdout.splitOn "\n").map String.trim
  let lines := lines.filter (fun s => !s.isEmpty)
  parseVerdictsWithModel vars lines ctx E |>.mapError
      (fun e => f!"{e}\nStdErr: {output.stderr}\nExit Code: {output.exitCode}")

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
    -- Running cvc5 with `--incremental` is okay even if we have only one
    -- check-sat in the SMTLib file.
    | "cvc5" => #["--incremental", "--produce-models"]
    -- No need to specify -model for Z3 because we already have `get-value`
    -- in the generated SMT file.
    | _ => #[]
  let setTimeout :=
    match solver with
    | "cvc5" => #[s!"--tlimit={options.solverTimeout*1000}"]
    | "z3" => #[s!"-T:{options.solverTimeout}"]
    | _ => #[]
  produceModels ++ setTimeout

open Strata.SMT.Encoder in
-- Derived from Strata.SMT.Encoder.encode.
def encodeObligation (ctx : Core.SMT.Context) (prelude : SolverM Unit)
    (ob : SMT.Obligation) : SolverM EncoderState := do
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
  let estate ←
    if ob.checkAssumptionsSat then do
      let (assumption_ids, estate) ← ob.assumptions.mapM (encodeTerm False) |>.run estate
      for id in assumption_ids do
        Solver.assert id
      Solver.checkSat
      if !estate.ufs.values.isEmpty then Solver.getValue estate.ufs.values
      let (conclusion_id, estate) ← (encodeTerm False ob.obligation) |>.run estate
      Solver.assert conclusion_id
      Solver.checkSat
      if !estate.ufs.values.isEmpty then Solver.getValue estate.ufs.values
      pure estate
    else do
      let terms := ob.assumptions ++ [ob.obligation]
      let (ids, estate) ← terms.mapM (encodeTerm False) |>.run estate
      for id in ids do
        Solver.assert id
      Solver.checkSat
      if !estate.ufs.values.isEmpty then Solver.getValue estate.ufs.values
      pure estate
  return estate

def dischargeObligation
  (options : Options)
  (vars : List (IdentT LMonoTy Visibility)) (smtsolver filename : String)
  (ob : SMT.Obligation) (ctx : SMT.Context)
  : IO (Except Format (List SMT.Result × EncoderState)) := do
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.write
  let solver ← Solver.fileWriter handle
  let prelude := getSolverPrelude smtsolver
  let estate ← encodeObligation ctx prelude ob solver
  if options.verbose > .normal then IO.println s!"Wrote problem to {filename}."
  let flags := getSolverFlags options smtsolver
  let output ← runSolver smtsolver (#[filename] ++ flags)
  match SMT.solverResults vars output ctx estate with
  | .error e => return .error e
  | .ok results => return .ok (results, estate)

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
  -- `.none` when the proof obligation doesn't require assumption sat checks.
  assumptionsSat : Option Outcome := .none
  assumptionSatSMTResult : SMT.Result := .unknown
  result : Outcome := .unknown
  smtResult : SMT.Result := .unknown
  estate : EncoderState := EncoderState.init
  verbose : VerboseMode := .normal

/--
Map the result from an SMT backend engine to an `Outcome`.
-/
def smtResultToOutcome (r : SMT.Result) (satIsPass : Bool) : Outcome :=
  match r with
  | .unknown => .unknown
  | .unsat =>
    if satIsPass then .fail else .pass
  | .sat _ =>
    if satIsPass then .pass else .fail
  | .err e => .implementationError e

instance : ToFormat VCResult where
  format r :=
  let assumptionCheckResult :=
    match r.assumptionsSat with
    | .none => f!""
    | some r => f!"Assumptions Sat Check: {r}\n"
  f!"Obligation: {r.obligation.label}\n\
                 Property: {r.obligation.property}\n\
                 {assumptionCheckResult}\
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
  -- First, we check whether we can return a result immediately based on
  -- satisfiability of assumptions alone.
  let checkAssumptionsStatus :=
    match obligation.checkAssumptionsSat with
    | true =>
      if obligation.assumptions.isEmpty then
        -- No assumptions to check; can process consequent next.
        some Outcome.pass
      else if obligation.assumptions.flatten.any (fun (_, e) => e.isFalse) then
        -- Unsat assumptions; can exit early.
        some Outcome.fail
      else -- Exit to use a backend solver.
        some Outcome.unknown
    | false =>
      -- Assumption satisfiability check not requested.
      -- Can process consequent next.
      .none
  match checkAssumptionsStatus with
  | some .fail => -- Exit early.
    let result := { obligation,
                    assumptionsSat := checkAssumptionsStatus,
                    result := (match obligation.property with
                              | .assert => .pass
                              | .cover => .fail),
                    verbose := options.verbose }
    return (obligation, some result)
  | .some .unknown =>
    -- Exit early. We need a backend solver for further processing.
    return (obligation, none)
  | _ => -- Continue preprocessing.
    match obligation.property with
    | .cover =>
      if obligation.obligation.isFalse then
        -- If PE determines that the consequent is false, then the cover fails.
        let result := { obligation,
                        assumptionsSat := checkAssumptionsStatus,
                        result := .fail, verbose := options.verbose }
        return (obligation, some result)
      else
        return (obligation, none)
    | .assert =>
      if obligation.obligation.isTrue then
        -- We don't need the SMT solver if PE (partial evaluation) is enough to
        -- reduce the consequent to true.
        let result := { obligation,
                        assumptionsSat := checkAssumptionsStatus,
                        result := .pass, verbose := options.verbose }
        return (obligation, some result)
      else if obligation.obligation.isFalse && obligation.assumptions.isEmpty then
        -- If PE determines that the consequent is false and the path conditions
        -- are empty (i.e., satisfiable), then we can immediately report a
        -- verification failure. Note that we go to the SMT solver if the path
        -- conditions aren't empty -- after all, the path conditions could imply
        -- false, which the PE isn't capable enough to infer.
        let prog := f!"\n\nEvaluated program:\n{p}"
        dbg_trace f!"\n\nObligation {obligation.label}: failed!\
                     \n\nResult obtained during partial evaluation.\
                     {if options.verbose >= .normal then prog else ""}"
        let result := { obligation,
                        assumptionsSat := checkAssumptionsStatus,
                        result := .fail,
                        verbose := options.verbose }
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
def getObligationResult (ob : SMT.Obligation) (ctx : SMT.Context)
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
          ob ctx)
  match ans with
  | .error e =>
    dbg_trace f!"\n\nObligation {obligation.label}: SMT Solver Invocation Error!\
                 \n\nError: {e}\
                 {if options.verbose >= .normal then prog else ""}"
    .error <| DiagnosticModel.fromFormat e
  | .ok (smt_results, estate) =>

    let (assumptions_sat_res, assumptions_solver_res, obligation_res) ←
      if ob.checkAssumptionsSat then
        if h1 : smt_results.length == 2 then
          .ok (some (smtResultToOutcome (smt_results[0]'(by grind)) true),
               smt_results[0]'(by grind),
               smt_results[1]'(by grind))
        else
          let f :=
            f!"🚨 SMT Solver Implementation Error! Expected 2 results \
                (assumptions sat check and main obligation check), \
                but got {smt_results.length} results instead."
          dbg_trace f!"\n\nObligation {obligation.label}: {f}\
                       {if options.verbose >= .normal then prog else ""}"
          .error <| DiagnosticModel.fromFormat f
      else if h2 : smt_results.length == 1 then
        .ok (none, .unknown, smt_results[0]'(by grind))
      else
        let f :=
          f!"🚨 SMT Solver Implementation Error! Expected 1 result (main obligation check), \
              but got {smt_results.length} results instead."
        dbg_trace f!"\n\nObligation {obligation.label}: {f}\
                     {if options.verbose >= .normal then prog else ""}"
        .error <| DiagnosticModel.fromFormat f
    let result :=  { obligation,
                     assumptionsSat := assumptions_sat_res
                     assumptionSatSMTResult := assumptions_solver_res,
                     result := smtResultToOutcome obligation_res (obligation.property == .cover)
                     smtResult := obligation_res,
                     estate,
                     verbose := options.verbose }
    return result

def verifySingleEnv (smtsolver : String) (pE : Program × Env) (options : Options)
    (counter : IO.Ref Nat) (tempDir : System.FilePath) :
    EIO DiagnosticModel VCResults := do
  dbg_trace f!"Verify single env: {pE.snd.deferred}\n"
  let (p, E) := pE
  match E.error with
  | some err =>
    .error <| DiagnosticModel.fromFormat s!"🚨 Error during evaluation!\n\
              {format err}\n\n\
              Evaluated program: {p}\n\n"
  | _ =>
    let mut results := (#[] : VCResults)
    for obligation in E.deferred do
      -- `options.checkAssumptionsSat := true` is a global setting that overrides
      -- per-obligation assumption satisfiability setting (`false` by default).
      let obligation := if options.checkAssumptionsSat then
        { obligation with checkAssumptionsSat := true }
      else
        obligation
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
      let maybeOb := ProofObligation.toSMTObligation E obligation
      match maybeOb with
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
      | .ok (ob, ctx) =>
        let result ← getObligationResult ob ctx obligation p smtsolver options
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
    (options : Options := Options.default)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default)
    : EIO DiagnosticModel VCResults := do
  match Core.typeCheckAndPartialEval options program moreFns with
  | .error err =>
    .error { err with message := s!"❌ Error.\n{err.message}" }
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
    (options : Options := Options.default)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default)
    (tempDir : Option String := .none)
    : IO Core.VCResults := do
  let (program, errors) := Core.getProgram env ictx
  if errors.isEmpty then
    -- dbg_trace f!"AST: {program}"
    let runner tempDir :=
      EIO.toIO (fun dm => IO.Error.userError (toString (dm.format (some ictx.fileMap))))
                  (Core.verify smtsolver program tempDir options moreFns)
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
    let fileRangeElem ← vcr.obligation.metadata.findElem Imperative.MetaData.fileRange
    match fileRangeElem.value with
    | .fileRange fileRange =>
      let message := match result with
        | .fail => "assertion does not hold"
        | .unknown => "assertion could not be proved"
        | .implementationError msg => s!"verification error: {msg}"
        | _ => panic "impossible"

      some (DiagnosticModel.withRange fileRange message)
    | _ => none

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
