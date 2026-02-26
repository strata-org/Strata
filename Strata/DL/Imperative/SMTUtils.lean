/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.SMT
import Strata.DL.Imperative.PureExpr
import Strata.DL.Imperative.EvalContext

namespace Imperative
open Std (ToFormat Format format)

namespace SMT
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
  deriving DecidableEq, Repr

def Result.isSat {T} (r : Result T) : Bool :=
  match r with | .sat _ => true | _ => false

def Result.formatWithVerbose {Ident} [ToFormat Ident]
  (r : Result Ident) (verbose : Bool) : Format :=
  match r with
  | .sat m  =>
    if (not verbose) || m.isEmpty then
      f!"sat"
    else f!"sat\nModel: {m}"
  | .unsat => f!"unsat"
  | .unknown => f!"unknown"
  | .err msg => f!"err {msg}"

instance {Ident} [ToFormat Ident]: ToFormat (Result Ident) where
  format r := r.formatWithVerbose true

def Result.formatModelIfSat {Ident} [ToFormat Ident]
  (r : Result Ident) (verbose : Bool) : Format :=
  match r with
  | .sat m =>
    if (not verbose) || m.isEmpty then
      f!""
    else
      f!"\nModel:\n{m}"
  | _ => f!""


/--
Find the Id for the SMT encoding of the variable `x` in the SMT encoder state `E`.
-/
def getSMTId {Ident Ty} [ToFormat Ident]
    (typedVarToSMTFn : Ident → Ty → Except Format (String × Strata.SMT.TermType))
    (x : Ident) (ty : Option Ty) (E : Strata.SMT.EncoderState) :
    Except Format String := do
  match (x, ty) with
  | (var, none) => .error f!"Expected variable {var} to be annotated with a type!"
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
    (E : Strata.SMT.EncoderState) : Except Format (CounterEx P.Ident) := do
  match vars with
  | [] => return []
  | (var, ty) :: vrest =>
    let id ← @getSMTId P.Ident P.Ty _ typedVarToSMTFn var ty E
    let value ← findCExValue id cexs
    let pair := (var, value)
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

/--
Interprets the output of SMT solver.

When `reachCheck` is `true`, the solver output contains two verdict lines:
the first is the reachability check result (are the path-condition assumptions
satisfiable?), and the second is the proof check result. The reachability
result is returned as `some Result`; when `reachCheck` is `false`, it is
`none`.
-/
def solverResult {P : PureExpr} [ToFormat P.Ident]
    (typedVarToSMTFn : P.Ident → P.Ty → Except Format (String × Strata.SMT.TermType))
    (vars : List P.TypedIdent) (output : IO.Process.Output)
    (E : Strata.SMT.EncoderState) (smtsolver : String)
    (reachCheck : Bool := false)
    : Except Format (Option (Result P.Ident) × Result P.Ident) := do
  let stdout := output.stdout
  -- When reachCheck is true, the first line of stdout is the reachability
  -- verdict; strip it and parse it separately.
  let (reachResult, proofStdout) := if reachCheck then
    let pos := stdout.find (· == '\n')
    let reachVerdictStr := (stdout.extract stdout.startPos pos).trimAscii
    let reachResult : Result P.Ident := match reachVerdictStr with
      | "sat" => .sat []
      | "unsat" => .unsat
      | _ => .unknown
    let remaining := (stdout.extract pos stdout.endPos).drop 1
    (some reachResult, remaining)
  else
    (none, stdout)
  -- Parse the proof verdict from the (possibly trimmed) stdout
  let pos := proofStdout.find (· == '\n')
  let verdict := proofStdout.extract proofStdout.startPos pos |>.trimAscii
  let rest := proofStdout.extract pos proofStdout.endPos
  match verdict with
  | "sat"     =>
    let rawModel ← getModel rest
    -- We suppress any model processing errors.
    -- Likely, these would be because of the suboptimal implementation
    -- of the model parser, which shouldn't hold back useful
    -- feedback (i.e., problem was `sat`) from the user.
    match (processModel typedVarToSMTFn vars rawModel E) with
    | .ok model => .ok (reachResult, .sat model)
    | .error _model_err => .ok (reachResult, .sat [])
  | "unsat"   => .ok (reachResult, .unsat)
  | "unknown" => .ok (reachResult, .unknown)
  | _     =>
    let stderr := output.stderr
    let hasExecError := stderr.contains "could not execute external process"
    let hasFileError := stderr.contains "No such file or directory"
    let suggestion :=
      if (hasExecError || hasFileError) && smtsolver == defaultSolver then
        s!" \nEnsure {defaultSolver} is on your PATH or use --solver to specify another SMT solver."
      else ""
    .error s!"stderr:{stderr}{suggestion}\nsolver stdout: {output.stdout}\n"

def addLocationInfo {P : PureExpr} [BEq P.Ident]
  (md : Imperative.MetaData P) (message : String × String)
  : Strata.SMT.SolverM Unit := do
  match Imperative.getFileRange md with
    | .some fileRange => do
      Strata.SMT.Solver.setInfo "file" s!"\"{format fileRange.file}\""
      Strata.SMT.Solver.setInfo "start" s!"{fileRange.range.start}"
      Strata.SMT.Solver.setInfo "stop" s!"{fileRange.range.stop}"
      -- TODO: the following should probably be stored in metadata so it can be
      -- set in an application-specific way.
      Strata.SMT.Solver.setInfo message.fst message.snd
    | .none => pure ()

/--
Writes the proof obligation to file, discharge the obligation using SMT solver,
and parse the output of the SMT solver.

When `reachCheck` is `true`, the generated SMT file will contain two
`(check-sat)` commands (one for reachability, one for the proof obligation),
and the return value includes the reachability decision.
-/
def dischargeObligation {P : PureExpr} [ToFormat P.Ident] [BEq P.Ident]
  (encodeSMT : Strata.SMT.SolverM (List String × Strata.SMT.EncoderState))
  (typedVarToSMTFn : P.Ident → P.Ty → Except Format (String × Strata.SMT.TermType))
  (vars : List P.TypedIdent)
  (md : Imperative.MetaData P)
  (smtsolver filename : String)
  (solver_options : Array String) (printFilename : Bool)
  (reachCheck : Bool := false) :
  IO (Except Format (Option (Result P.Ident) × Result P.Ident × Strata.SMT.EncoderState)) := do
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.write
  let solver ← Strata.SMT.Solver.fileWriter handle

  let (ids, estate) ← encodeSMT solver
  (addLocationInfo md ("sat-message", s!"\"Assertion cannot be proven\"")) solver

  let _ ← solver.checkSat ids -- Will return unknown for Solver.fileWriter
  if printFilename then IO.println s!"Wrote problem to {filename}."

  let solver_output ← runSolver smtsolver (#[filename] ++ solver_options)
  match solverResult typedVarToSMTFn vars solver_output estate smtsolver (reachCheck := reachCheck) with
  | .error e => return .error e
  | .ok (reachDecision, result) => return .ok (reachDecision, result, estate)

---------------------------------------------------------------------
end SMT


/--
SMT solver's `result` along with an SMT encoder state `estate` for a given
verification condition `obligation`.
Currently, this data structure is only used in the Arith example of StrataTest.
-/
structure VCResult (P : Imperative.PureExpr) where
  obligation : Imperative.ProofObligation P
  result : SMT.Result P.Ident := .unknown
  estate : Strata.SMT.EncoderState := Strata.SMT.EncoderState.init

instance [ToFormat (SMT.Result P.Ident)] [ToFormat (SMT.CounterEx P.Ident)]
  : ToFormat (VCResult P) where
  format r :=
    let result_fmt := match r.result with
      | .sat cex  =>
        if cex.isEmpty then
          f!"failed\nNo counterexample available."
        else
          f!"failed\nCounterexample: {cex}"
      | .unsat => f!"verified"
      | .unknown => f!"unknown"
      | .err msg => f!"err {msg}"
    f!"Obligation: {r.obligation.label}\n\
                 Result: {result_fmt}"

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

end Imperative
