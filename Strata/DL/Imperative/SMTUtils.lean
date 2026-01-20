/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.SMT
import Strata.DL.Imperative.PureExpr
import Strata.DL.Imperative.EvalContext

namespace Imperative
open Std (ToFormat Format format)
---------------------------------------------------------------------

/--
A counterexample derived from an SMT solver is a map from an identifier
to a string.
-/
abbrev CounterEx (Ident : Type) := Map Ident String

def CounterEx.format {Ident} [ToFormat Ident] (cex : CounterEx Ident) : Format :=
  match cex with
  | [] => ""
  | [(id, v)] => f!"({id}, {v})"
  | (id, v) :: rest =>
    (f!"({id}, {v}) ") ++ CounterEx.format rest

instance {Ident} [ToFormat Ident] : ToFormat (CounterEx Ident) where
  format := CounterEx.format

/--
Result from an SMT solver.
-/
inductive Result (Ident : Type) where
  -- Also see Strata.SMT.Decision.
  | sat (cex : CounterEx Ident)
  | unsat
  | unknown
  | err (msg : String)
  deriving DecidableEq

instance {Ident} [ToFormat Ident] : ToFormat (Result Ident) where
  format r := match r with
    | .sat cex  =>
      if cex.isEmpty then
        f!"failed\nNo counterexample available."
      else
        f!"failed\nCounterexample: {cex}"
    | .unsat => f!"verified"
    | .unknown => f!"unknown"
    | .err msg => f!"err {msg}"

/--
SMT solver's `result` along with an SMT encoder state `estate` for a given
verification condition `obligation`.
-/
structure VCResult (P : Imperative.PureExpr) where
  obligation : Imperative.ProofObligation P
  result : Result P.TypedIdent := .unknown
  estate : Strata.SMT.EncoderState := Strata.SMT.EncoderState.init

instance [ToFormat (Result P.TypedIdent)] : ToFormat (VCResult P) where
  format r := f!"Obligation: {r.obligation.label}\n\
                 Result: {r.result}"
                --  EState : {repr r.estate.terms}

/--
An array of `VCResult`s.
-/
abbrev VCResults (P : Imperative.PureExpr) := Array (VCResult P)

def VCResults.format [ToFormat (VCResult P)] (rs : VCResults P) : Format :=
  let rsf := rs.map (fun r => f!"{Format.line}{r}")
  Format.joinSep rsf.toList Format.line

instance [ToFormat (VCResult P)] : ToFormat (VCResults P) where
  format := VCResults.format

instance [ToFormat (VCResult P)] : ToString (VCResults P) where
  toString rs := toString (VCResults.format rs)


/--
Find the Id for the SMT encoding of the variable `x` in the SMT encoder state `E`.
-/
def getSMTId {Ident Ty} [ToFormat Ident]
    (typedVarToSMTFn : Ident → Ty → Except Format (String × Strata.SMT.TermType))
    (x : Ident) (ty : Option Ty) (E : Strata.SMT.EncoderState) :
    Except Format String := do
  match (x, ty) with
  | (var, none) => .error f!"Expected type-annotated variable {var}!"
  | (var, some ty) => do
    let (var', ty') ← typedVarToSMTFn var ty
    let key : Strata.SMT.UF := { id := var', args := [], out := ty' }
    .ok (E.ufs[key]!)

def getModel (m : String) : Except Format (List Strata.SMT.CExParser.KeyValue) := do
  let cex ← Strata.SMT.CExParser.parseCEx m
  return cex.pairs

def processModel {P : PureExpr} [ToFormat P.Ident]
    (typedVarToSMTFn : P.Ident → P.Ty → Except Format (String × Strata.SMT.TermType))
    (vars : List P.TypedIdent) (cexs : List Strata.SMT.CExParser.KeyValue)
    (E : Strata.SMT.EncoderState) : Except Format (CounterEx P.TypedIdent) := do
  match vars with
  | [] => return []
  | (var, ty) :: vrest =>
    let id ← @getSMTId P.Ident P.Ty _ typedVarToSMTFn var ty E
    let value ← findCExValue id cexs
    let pair := ((var, ty), value)
    let rest ← processModel typedVarToSMTFn vrest cexs E
    .ok (pair :: rest)
  where findCExValue id cexs : Except Format String :=
    match cexs.find? (fun p => p.key == id) with
    | none => .error f!"Cannot find model for id: {id}"
    | some p => .ok p.value

def runSolver (solver : String) (args : Array String) : IO IO.Process.Output := do
  let output ← IO.Process.output {
    cmd := solver
    args := args
  }
  -- dbg_trace f!"runSolver: exitcode: {repr output.exitCode}\n\
  --                         stderr: {repr output.stderr}\n\
  --                         stdout: {repr output.stdout}"
  return output

def solverResult {P : PureExpr} [ToFormat P.Ident]
    (typedVarToSMTFn : P.Ident → P.Ty → Except Format (String × Strata.SMT.TermType))
    (vars : List P.TypedIdent) (output : IO.Process.Output)
    (E : Strata.SMT.EncoderState) : Except Format (Result P.TypedIdent) := do
  let stdout := output.stdout
  let pos := (stdout.find (fun c => c == '\n' || c == '\r')).byteIdx
  let verdict := stdout.take pos
  let rest := stdout.drop pos
  match verdict with
  | "sat"     =>
    let rawModel ← getModel rest
    let model ← processModel typedVarToSMTFn vars rawModel E
    .ok (.sat model)
  | "unsat"   =>  .ok .unsat
  | "unknown" =>  .ok .unknown
  | _     =>  .error s!"stderr:{output.stderr}\nsolver stdout: {output.stdout}\n"

def dischargeObligation {P : PureExpr} [ToFormat P.Ident]
  (encodeTerms : List Strata.SMT.Term → Strata.SMT.SolverM (List String × Strata.SMT.EncoderState))
  (typedVarToSMTFn : P.Ident → P.Ty → Except Format (String × Strata.SMT.TermType))
  (vars : List P.TypedIdent) (smtsolver filename : String)
  (terms : List Strata.SMT.Term) :
  IO (Except Format (Result P.TypedIdent × Strata.SMT.EncoderState)) := do
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.write
  let solver ← Strata.SMT.Solver.fileWriter handle
  let (ids, estate) ← encodeTerms terms solver
  let _ ← solver.checkSat ids -- Will return unknown for Solver.fileWriter
  let produce_models ←
    if smtsolver.endsWith "z3" then
      -- No need to specify -model because we already have `get-value` in the
      -- generated SMT file.
      .ok ""
    else if smtsolver.endsWith "cvc5" then
      .ok "--produce-models"
    else
      return .error f!"Unsupported SMT solver: {smtsolver}"
  let solver_output ← runSolver smtsolver #[filename, produce_models]
  match solverResult typedVarToSMTFn vars solver_output estate with
  | .error e => return .error e
  | .ok result => return .ok (result, estate)

---------------------------------------------------------------------
end Imperative
