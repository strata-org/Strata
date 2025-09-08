/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.DDMTransform.Translate
import Strata.Languages.Boogie.Options
import Strata.Languages.Boogie.SMTEncoder
import Strata.DL.Imperative.SMTUtils
import Strata.DL.SMT.CexParser

---------------------------------------------------------------------

namespace Strata.SMT.Encoder

open Strata.SMT.Encoder

-- Derived from Strata.SMT.Encoder.encode.
def encodeBoogie (ctx : Boogie.SMT.Context) (ts : List Term) :
  SolverM (List String × EncoderState) := do
  Solver.reset
  Solver.setLogic "ALL"
  let _ ← ctx.sorts.mapM (fun s => Solver.declareSort s.name s.arity)
  let (_ufs, estate) ← ctx.ufs.mapM (fun uf => encodeUF uf) |>.run EncoderState.init
  let (_ifs, estate) ← ctx.ifs.mapM (fun fn => encodeFunction fn.uf fn.body) |>.run estate
  let (_axms, estate) ← ctx.axms.mapM (fun ax => encodeTerm False ax) |>.run estate
  for id in _axms do
    Solver.assert id
  let (ids, estate) ← ts.mapM (encodeTerm False) |>.run estate
  for id in ids do
    Solver.assert id
  let ids := (estate.terms.filter (fun t _ => t.isVar)).values
  return (ids, estate)

end Strata.SMT.Encoder

---------------------------------------------------------------------

namespace Boogie
open Std (ToFormat Format format)
open Lambda Strata.SMT

-- (TODO) Use DL.Imperative.SMTUtils.

abbrev CounterEx := Map (IdentT BoogieIdent) String

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
def getSMTId (x : (IdentT BoogieIdent)) (ctx : SMT.Context) (E : EncoderState) : Except Format String := do
    match x with
    | (var, none) => .error f!"Expected variable {var} to be annotated with a type!"
    | (var, some ty) => do
      let (ty', _) ← LMonoTy.toSMTType ty ctx
      let key := Term.var (TermVar.mk false var.2 ty')
      .ok E.terms[key]!

def getModel (m : String) : Except Format (List Strata.SMT.CExParser.KeyValue) := do
  let cex ← Strata.SMT.CExParser.parseCEx m
  return cex.pairs

def processModel
  (vars : List (IdentT BoogieIdent)) (cexs : List Strata.SMT.CExParser.KeyValue)
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

def solverResult (vars : List (IdentT BoogieIdent)) (ans : String) (ctx : SMT.Context) (E : EncoderState) :
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
  | other     =>  .error other

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

def dischargeObligation
  (options : Options)
  (vars : List (IdentT BoogieIdent)) (smtsolver filename : String)
  (terms : List Term) (ctx : SMT.Context)
  : IO (Except Format (Result × EncoderState)) := do
  if !(← System.FilePath.isDir VC_folder_name) then
    let _ ← IO.FS.createDir VC_folder_name
  let filename := s!"{VC_folder_name}/{filename}"
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.write
  let solver ← Solver.fileWriter handle
  let (ids, estate) ← Strata.SMT.Encoder.encodeBoogie ctx terms solver
  let _ ← solver.checkSat ids -- Will return unknown for Solver.fileWriter
  if options.verbose then IO.println s!"Wrote problem to {filename}."
  let produce_models ←
    if smtsolver.endsWith "z3" then
      -- No need to specify -model because we already have `get-value` in the
      -- generated SMT file.
      .ok ""
    else if smtsolver.endsWith "cvc5" then
      .ok "--produce-models"
    else
      return .error f!"Unsupported SMT solver: {smtsolver}"
  let timeout ←
    if smtsolver.endsWith "z3" then
      .ok s!"-t:{options.solverTimeout*1000}"
    else if smtsolver.endsWith "cvc5" then
      .ok  s!"--tlimit={options.solverTimeout*1000}"
    else
      return .error f!"Unsupported SMT solver: {smtsolver}"
  let solver_out ← runSolver smtsolver #[filename, produce_models, timeout]
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

def verify (smtsolver : String) (env : Program)
    (options : Options := Options.default) : IO Boogie.VCResults := do
  let (program, errors) := TransM.run (translateProgram env)
  if errors.isEmpty then
    -- dbg_trace f!"AST: {program}"
    EIO.toIO (fun f => IO.Error.userError (toString f))
                (Boogie.verify smtsolver program options)
  else
    panic! s!"DDM Transform Error: {repr errors}"

end Strata

---------------------------------------------------------------------
