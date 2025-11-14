/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.DDMTransform.Translate
import Strata.Languages.Boogie.Options
import Strata.Languages.Boogie.CallGraph
import Strata.Languages.Boogie.SMTEncoder
import Strata.DL.Imperative.SMTUtils
import Strata.DL.SMT.CexParser

---------------------------------------------------------------------

namespace Strata.SMT.Encoder

open Strata.SMT.Encoder

-- Derived from Strata.SMT.Encoder.encode.
def encodeBoogie (ctx : Boogie.SMT.Context) (prelude : SolverM Unit) (ts : List Term) :
  SolverM (List String × EncoderState) := do
  Solver.reset
  Solver.setLogic "ALL"
  prelude
  let _ ← ctx.sorts.mapM (fun s => Solver.declareSort s.name s.arity)
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

namespace Boogie
open Std (ToFormat Format format)
open Lambda Strata.SMT

-- (TODO) Use DL.Imperative.SMTUtils.

abbrev CounterEx := Map (IdentT Visibility) String

def CounterEx.format (cex : CounterEx) : Format :=
  match cex with
  | [] => ""
  | [((k, _), v)] => f!"({k}, {v})"
  | ((k, _), v) :: rest =>
    (f!"({k}, {v}) ") ++ CounterEx.format rest

instance : ToFormat CounterEx where
  format := CounterEx.format

/--
Find the Id for the SMT encoding of `x`.
-/
def getSMTId (x : (IdentT Visibility)) (ctx : SMT.Context) (E : EncoderState) : Except Format String := do
    match x with
    | (var, none) => .error f!"Expected variable {var} to be annotated with a type!"
    | (var, some ty) => do
      let (ty', _) ← LMonoTy.toSMTType ty ctx
      let key : Strata.SMT.UF := { id := var.name, args := [], out := ty' }
      .ok (E.ufs[key]!)

def getModel (m : String) : Except Format (List Strata.SMT.CExParser.KeyValue) := do
  let cex ← Strata.SMT.CExParser.parseCEx m
  return cex.pairs

def processModel
  (vars : List (IdentT Visibility)) (cexs : List Strata.SMT.CExParser.KeyValue)
  (ctx : SMT.Context) (E : EncoderState) :
  Except Format CounterEx := do
  match vars with
  | [] => return []
  | var :: vrest =>
    let id ← getSMTId var ctx E
    let value ← findCExValue id cexs
    let pair := (var, value)
    let rest ← processModel vrest cexs ctx E
    .ok (pair :: rest)
  where findCExValue id cexs : Except Format String :=
    match cexs.find? (fun p => p.key == id) with
    | none => .error f!"Cannot find model for id: {id}"
    | some p => .ok p.value

inductive Result where
  -- Also see Strata.SMT.Decision.
  | sat (cex : CounterEx)
  | unsat
  | unknown
  | err (msg : String)
deriving DecidableEq, Repr

instance : ToFormat Result where
  format r := match r with
    | .sat cex  => f!"failed\nCEx: {cex}"
    | .unsat => f!"verified"
    | .unknown => f!"unknown"
    | .err msg => f!"err {msg}"

def VC_folder_name: String := "vcs"

def runSolver (solver : String) (args : Array String) : IO String := do
  let output ← IO.Process.output {
    cmd := solver
    args := args
  }
  -- dbg_trace f!"runSolver: exitcode: {repr output.exitCode}\n\
  --                         stderr: {repr output.stderr}\n\
  --                         stdout: {repr output.stdout}"
  return output.stdout

def solverResult (vars : List (IdentT Visibility)) (ans : String) (ctx : SMT.Context) (E : EncoderState) :
  Except Format Result := do
  let pos := (ans.find (fun c => c == '\n')).byteIdx
  let verdict := (ans.take pos).trim
  let rest := ans.drop pos
  match verdict with
  | "sat"     =>
    let rawModel ← getModel rest
    let model ← processModel vars rawModel ctx E
    .ok (.sat model)
  | "unsat"   =>  .ok .unsat
  | "unknown" =>  .ok .unknown
  | _     =>  .error ans

structure VCResult where
  obligation : Imperative.ProofObligation Expression
  result : Result := .unknown
  estate : EncoderState := EncoderState.init

instance : ToFormat VCResult where
  format r := f!"Obligation: {r.obligation.label}\n\
                 Result: {r.result}"
                --  EState : {repr r.estate.terms}

abbrev VCResults := Array VCResult

def VCResults.format (rs : VCResults) : Format :=
  let rsf := rs.map (fun r => f!"{Format.line}{r}")
  Format.joinSep rsf.toList Format.line

instance : ToFormat VCResults where
  format := VCResults.format

instance : ToString VCResults where
  toString rs := toString (VCResults.format rs)

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
    | "z3" => #[s!"-t:{options.solverTimeout*1000}"]
    | _ => #[]
  produceModels ++ setTimeout

def dischargeObligation
  (options : Options)
  (vars : List (IdentT Visibility)) (smtsolver filename : String)
  (terms : List Term) (ctx : SMT.Context)
  : IO (Except Format (Result × EncoderState)) := do
  if !(← System.FilePath.isDir VC_folder_name) then
    let _ ← IO.FS.createDir VC_folder_name
  let filename := s!"{VC_folder_name}/{filename}"
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.write
  let solver ← Solver.fileWriter handle
  let prelude := getSolverPrelude smtsolver
  let (ids, estate) ← Strata.SMT.Encoder.encodeBoogie ctx prelude terms solver
  let _ ← solver.checkSat ids -- Will return unknown for Solver.fileWriter
  if options.verbose then IO.println s!"Wrote problem to {filename}."
  let flags := getSolverFlags options smtsolver
  let solver_out ← runSolver smtsolver (#[filename] ++ flags)
  match solverResult vars solver_out ctx estate with
  | .error e => return .error e
  | .ok result => return .ok (result, estate)

def verifySingleEnv (smtsolver : String) (pE : Program × Env) (options : Options) :
    EIO Format VCResults := do
  let (p, E) := pE
  match E.error with
  | some err =>
    .error s!"[Strata.Boogie] Error during evaluation!\n\
              {format err}\n\n\
              Evaluated program: {p}\n\n"
  | _ =>
    let mut results := (#[] : VCResults)
    for obligation in E.deferred do
      -- We don't need the SMT solver if PE (partial evaluation) is enough to
      -- reduce the consequent to true.
      if obligation.obligation.isTrue then
        results := results.push { obligation, result := .unsat }
        continue
      -- If PE determines that the consequent is false and the path conditions
      -- are empty, then we can immediate report a verification failure. Note
      -- that we go to the SMT solver if the path conditions aren't empty --
      -- after all, the path conditions could imply false, which the PE isn't
      -- capable enough to infer.
      if obligation.obligation.isFalse && obligation.assumptions.isEmpty then
        let prog := f!"\n\nEvaluated program:\n{p}"
        dbg_trace f!"\n\nObligation {obligation.label}: failed!\
                     \n\nResult obtained during partial evaluation.\
                     {if options.verbose then prog else ""}"
        results := results.push { obligation, result := .sat .empty }
        if options.stopOnFirstError then break
      let obligation :=
      if options.removeIrrelevantAxioms then
        -- We attempt to prune the path conditions by excluding all irrelevant
        -- axioms w.r.t. the consequent to reduce the size of the proof
        -- obligation.
        let cg := Program.toFunctionCG p
        let fns := obligation.obligation.getOps.map BoogieIdent.toPretty
        let relevant_fns := (fns ++ (CallGraph.getAllCalleesClosure cg fns)).dedup
        let irrelevant_axs := Program.getIrrelevantAxioms p relevant_fns
        let new_assumptions := Imperative.PathConditions.removeByNames obligation.assumptions irrelevant_axs
        { obligation with assumptions := new_assumptions }
      else
        obligation
      -- At this point, we solely rely on the SMT backend.
      let maybeTerms := ProofObligation.toSMTTerms E obligation
      match maybeTerms with
      | .error err =>
        let msg := s!"[Error] SMT Encoding error for obligation {format obligation.label}: \n\
                     {err}\n\n\
                     Evaluated program: {p}\n\n"
        let _ ← dbg_trace msg
        results := results.push { obligation, result := .err msg }
        if options.stopOnFirstError then break
      | .ok (terms, ctx) =>
        -- let ufids := (ctx.ufs.map (fun f => f.id))
        -- let ufs := f!"Uninterpreted Functions:{Format.line}\
        --              {Std.Format.joinSep ufids.toList Std.Format.line}\
        --              {Format.line}"
        -- let ifids := ctx.ifs.map (fun f => f.uf.id)
        -- let ifs := f!"Interpreted Functions:{Format.line}\
        --            {Std.Format.joinSep ifids.toList Std.Format.line}\
        --            {Format.line}"
        -- if !(ufids.isEmpty && ifids.isEmpty) then dbg_trace f!"{ufs}{ifs}"
        -- let rand_suffix ← IO.rand 0 0xFFFFFFFF
        let ans ←
            IO.toEIO
              (fun e => f!"{e}")
              (dischargeObligation options
                (ProofObligation.getVars obligation) smtsolver
                  (Imperative.smt2_filename obligation.label)
                terms ctx)
        match ans with
        | .ok (result, estate) =>
           results := results.push { obligation, result, estate }
           if result ≠ .unsat then
            let prog := f!"\n\nEvaluated program:\n{p}"
            dbg_trace f!"\n\nObligation {obligation.label}: could not be proved!\
                         \n\nResult: {result}\
                         {if options.verbose then prog else ""}"
           if options.stopOnFirstError then break
        | .error e =>
           results := results.push { obligation, result := .err (toString e) }
           let prog := f!"\n\nEvaluated program:\n{p}"
           dbg_trace f!"\n\nObligation {obligation.label}: solver error!\
                        \n\nError: {e}\
                        {if options.verbose then prog else ""}"
           if options.stopOnFirstError then break
    return results

def verify (smtsolver : String) (program : Program) (options : Options := Options.default) : EIO Format VCResults := do
  match Boogie.typeCheckAndPartialEval options program with
  | .error err =>
    .error f!"[Strata.Boogie] Type checking error: {format err}"
  | .ok pEs =>
    let VCss ← if options.checkOnly then
                 pure []
               else
                 (List.mapM (fun pE => verifySingleEnv smtsolver pE options) pEs)
    .ok VCss.toArray.flatten

end Boogie

---------------------------------------------------------------------

namespace Strata

def Boogie.getProgram (p : Strata.Program) : Boogie.Program × Array String :=
  TransM.run (translateProgram p)

def typeCheck (env : Program) (options : Options := Options.default) :
  Except Std.Format Boogie.Program := do
  let (program, errors) := Boogie.getProgram env
  if errors.isEmpty then
    -- dbg_trace f!"AST: {program}"
    Boogie.typeCheck options program
  else
    .error s!"DDM Transform Error: {repr errors}"

def verify (smtsolver : String) (env : Program)
    (options : Options := Options.default) : IO Boogie.VCResults := do
  let (program, errors) := Boogie.getProgram env
  if errors.isEmpty then
    -- dbg_trace f!"AST: {program}"
    EIO.toIO (fun f => IO.Error.userError (toString f))
                (Boogie.verify smtsolver program options)
  else
    panic! s!"DDM Transform Error: {repr errors}"

end Strata

---------------------------------------------------------------------
