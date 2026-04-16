/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.SMT
import Strata.DL.SMT.DDMTransform.Parse
import Strata.DL.SMT.DDMTransform.Translate
import Strata.DDM.Elab
import Strata.DDM.Format
public import Strata.DL.Imperative.PureExpr
public import Strata.DL.Imperative.EvalContext

namespace Imperative
open Std (ToFormat Format format)

namespace SMT

public section
---------------------------------------------------------------------

/--
A model derived from an SMT solver is a map from an identifier
to an `SMT.Term`.
-/
@[expose] abbrev Model (Ident : Type) := Map Ident Strata.SMT.Term

/-- Backward-compatible alias. -/
@[deprecated Model (since := "2026-04-03")] abbrev CounterEx := @Model

/-- Render an `SMT.Term` to a string via the SMTDDM translation. -/
private def termToString (t : Strata.SMT.Term) : String :=
  match Strata.SMTDDM.termToString t with
  | .ok s => s
  | .error _ => repr t |>.pretty

def Model.format {Ident} [ToFormat Ident] (m : Model Ident) : Format :=
  match m with
  | [] => ""
  | [(id, v)] => f!"({id}, {termToString v})"
  | (id, v) :: rest =>
    (f!"({id}, {termToString v}) ") ++ Model.format rest

instance {Ident} [ToFormat Ident] : ToFormat (Model Ident) where
  format := Model.format

/--
Result from an SMT solver.
-/
inductive Result (Ident : Type) where
  -- Also see Strata.SMT.Decision.
  | sat (model : Model Ident)
  | unsat
  | unknown (candidateModel : Option (Model Ident) := none)
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
  | .unknown m =>
    match m with
    | some model =>
      if (not verbose) || model.isEmpty then
        f!"unknown"
      else f!"unknown\nCandidate model: {model}"
    | none => f!"unknown"
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

def runSolver (solver : String) (args : Array String) : IO IO.Process.Output := do
  let output ← IO.Process.output {
    cmd := solver
    args := args
  }
  -- dbg_trace f!"runSolver: exitcode: {repr output.exitCode}\n\
  --                         stderr: {repr output.stderr}\n\
  --                         stdout: {repr output.stdout}"
  return output

---------------------------------------------------------------------
-- SMTDDM-based parsing
---------------------------------------------------------------------

/--
Parse a verdict line ("sat", "unsat", "unknown") via the SMTResponse DDM
dialect. Returns `some .sat`, `some .unsat`, `some .unknown`, or `none`
on parse/conversion failure.
-/
private def parseVerdict (line : String) : IO (Option (Result PUnit)) := do
  let inputCtx := Strata.Parser.stringInputContext "solver" (line ++ "\n")
  let prg ←
    try Strata.Elab.parseStrataProgramFromDialect
          Strata.SMTResponseDDM.smtResponseDialects "SMTResponse" inputCtx
    catch _ => return none
  if prg.commands.isEmpty then return none
  let op := prg.commands[0]!
  match Strata.SMTResponseDDM.Command.ofAst op with
  | .ok (.specific_success_response _ (.ssr_check_sat _ (.csr_sat _)))     => return some (.sat [])
  | .ok (.specific_success_response _ (.ssr_check_sat _ (.csr_unsat _)))   => return some .unsat
  | .ok (.specific_success_response _ (.ssr_check_sat _ (.csr_unknown _))) => return some .unknown
  | _ => return none

/--
Parse a `(get-value ...)` model response using the SMTResponse DDM dialect.
Uses `parseCategoryFromDialect` targeting `SMTResponse.GetValueResponse`
directly, which avoids the ambiguity that arises when parsing at the
`Command` level.

Returns a list of (key-string, value-Term) pairs on success.
-/
def parseModelDDM (modelStr : String) : IO (List (String × Strata.SMT.Term)) := do
  let inputCtx := Strata.Parser.stringInputContext "solver-model" modelStr
  let op ←
    try Strata.Elab.parseCategoryFromDialect
          Strata.SMTResponseDDM.smtResponseDialects q`SMTResponse.GetValueResponse inputCtx
    catch _ => return []
  match Strata.SMTResponseDDM.GetValueResponse.ofAst op with
  | .ok (.get_value_response _ vps) =>
    let pairs ← vps.val.toList.filterMapM fun vp =>
      match vp with
      | .valuation_pair _ t1 t2 => do
        match Strata.SMTResponseDDM.translateFromDDMTermToUntyped t2 with
        | .ok t2' =>
          return .some (Strata.SMTResponseDDM.formatArg (.op (Strata.SMTResponseDDM.Term.toAst t1)),
                  t2')
        | .error _ =>
          -- The model has an SMT expression (e.g., (lambda ...)) which cannot
          -- be represented in Strata.SMT.Term. Filter out this variable from
          -- the model.
          return .none
    return pairs
  | .error _ => return []

/--
Process a parsed model (list of key-string / value-Term pairs) against the
expected variables, matching each variable's SMT-encoded name to its
value in the model.
-/
def processModel {P : PureExpr} [ToFormat P.Ident]
    (typedVarToSMTFn : P.Ident → P.Ty → Except Format (String × Strata.SMT.TermType))
    (vars : List P.TypedIdent) (pairs : List (String × Strata.SMT.Term))
    (E : Strata.SMT.EncoderState) : Except Format (Model P.Ident) := do
  match vars with
  | [] => return []
  | (var, ty) :: vrest =>
    let id ← @getSMTId P.Ident P.Ty _ typedVarToSMTFn var ty E
    let value ← findValue id pairs
    let rest ← processModel typedVarToSMTFn vrest pairs E
    .ok ((var, value) :: rest)
  where findValue id pairs : Except Format Strata.SMT.Term :=
    match pairs.find? (fun p => p.fst == id) with
    | none => .error f!"Cannot find model for id: {id}"
    | some p => .ok p.snd

/--
Interprets the output of SMT solver.

When two-sided checking is enabled, the solver output contains two verdict lines:
the first is the satisfiability check result (can the property be true?),
and the second is the validity check result (can the property be false?).
The satisfiability result is returned as the first element of the pair;
the validity result is the second element.

When only one check is enabled, the other is returned as `unknown`.
-/
def solverResult {P : PureExpr} [ToFormat P.Ident]
    (typedVarToSMTFn : P.Ident → P.Ty → Except Format (String × Strata.SMT.TermType))
    (vars : List P.TypedIdent) (output : IO.Process.Output)
    (E : Strata.SMT.EncoderState) (smtsolver : String)
    (satisfiabilityCheck validityCheck : Bool)
    : IO (Except Format (Result P.Ident × Result P.Ident)) := do
  let stdout := output.stdout

  -- Helper to parse a single verdict and model
  -- Skip lines until we find a verdict (sat/unsat/unknown) or run out of input.
  -- This is needed because get-value commands in the file may produce error
  -- output when the preceding check-sat returned unsat.
  let skipToNextVerdict (input : String) : String :=
    let lines := input.splitOn "\n"
    let rest := lines.dropWhile (fun l =>
      let t := l.trimAscii.toString
      t != "sat" && t != "unsat" && t != "unknown" && !t.isEmpty)
    "\n".intercalate rest

  let parseVerdict (input : String) : IO (Option (Result P.Ident × String)) := do
    let pos := input.find (· == '\n')
    let verdict := input.extract input.startPos pos |>.trimAscii.toString
    let rest := (input.extract pos input.endPos |>.drop 1).toString
    match verdict with
    | "sat" =>
      let rawModel ← parseModelDDM rest
      match (processModel typedVarToSMTFn vars rawModel E) with
      | .ok model => return some (.sat model, skipToNextVerdict rest)
      | .error _ => return some (.sat [], skipToNextVerdict rest)
    | "unsat" => return some (.unsat, skipToNextVerdict rest)
    | "unknown" => return some (.unknown, skipToNextVerdict rest)
    | _ => return none

  -- Parse results based on which checks are enabled
  match ← (if satisfiabilityCheck then parseVerdict stdout else pure (some (.unknown, stdout))) with
  | some (satResult, remaining) =>
    match ← (if validityCheck then parseVerdict remaining else pure (some (.unknown, remaining))) with
    | some (validityResult, _) => return .ok (satResult, validityResult)
    | none =>
      let stderr := output.stderr
      let hasExecError := stderr.contains "could not execute external process"
      let hasFileError := stderr.contains "No such file or directory"
      let suggestion :=
        if (hasExecError || hasFileError) && smtsolver == Core.defaultSolver then
          s!" \nEnsure {Core.defaultSolver} is on your PATH or use --solver to specify another SMT solver."
        else ""
      return .error s!"stderr:{stderr}{suggestion}\nsolver stdout: {output.stdout}\n"
  | none =>
    let stderr := output.stderr
    let hasExecError := stderr.contains "could not execute external process"
    let hasFileError := stderr.contains "No such file or directory"
    let suggestion :=
      if (hasExecError || hasFileError) && smtsolver == Core.defaultSolver then
        s!" \nEnsure {Core.defaultSolver} is on your PATH or use --solver to specify another SMT solver."
      else ""
    return .error s!"stderr:{stderr}{suggestion}\nsolver stdout: {output.stdout}\n"

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

When two-sided checking is enabled, the generated SMT file will contain two
`(check-sat-assuming)` commands, one for `P ∧ Q` and one for `P ∧ ¬Q`,
and the return value includes both decisions.
-/
def dischargeObligation {P : PureExpr} [ToFormat P.Ident] [BEq P.Ident]
  (encodeSMT : Strata.SMT.SolverM (List String × Strata.SMT.EncoderState))
  (typedVarToSMTFn : P.Ident → P.Ty → Except Format (String × Strata.SMT.TermType))
  (vars : List P.TypedIdent)
  (smtsolver filename : String)
  (solver_options : Array String) (printFilename : Bool)
  (satisfiabilityCheck validityCheck : Bool)
  (skipSolver : Bool := false) :
  IO (Except Format (Result P.Ident × Result P.Ident × Strata.SMT.EncoderState)) := do
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.write
  let solver ← Strata.SMT.Solver.fileWriter handle

  -- encodeSMT (which calls encodeCore) emits check-sat commands internally
  let ((_ids, estate), _solverState) ← encodeSMT.run solver

  if printFilename then IO.println s!"Wrote problem to {filename}."

  if skipSolver then
    return .ok (.unknown, .unknown, estate)

  let solver_output ← runSolver smtsolver (#[filename] ++ solver_options)
  match ← solverResult typedVarToSMTFn vars solver_output estate smtsolver satisfiabilityCheck validityCheck with
  | .error e => return .error e
  | .ok (satResult, validityResult) => return .ok (satResult, validityResult, estate)

---------------------------------------------------------------------
end -- public section
end SMT

public section

/--
SMT solver's `result` along with an SMT encoder state `estate` for a given
verification condition `obligation`.
Currently, this data structure is only used in the Arith example of StrataTest.
-/
structure VCResult (P : Imperative.PureExpr) where
  obligation : Imperative.ProofObligation P
  result : SMT.Result P.Ident := .unknown
  estate : Strata.SMT.EncoderState := Strata.SMT.EncoderState.init

instance [ToFormat (SMT.Result P.Ident)] [ToFormat (SMT.Model P.Ident)]
  : ToFormat (VCResult P) where
  format r :=
    let result_fmt := match r.result with
      | .sat model  =>
        if model.isEmpty then
          f!"failed\nNo model available."
        else
          f!"failed\nModel: {model}"
      | .unsat => f!"verified"
      | .unknown _ => f!"unknown"
      | .err msg => f!"err {msg}"
    f!"Obligation: {r.obligation.label}\n\
                 Result: {result_fmt}"

/--
An array of `VCResult`s.
-/
@[expose] abbrev VCResults (P : Imperative.PureExpr) := Array (VCResult P)

def VCResults.format [ToFormat (VCResult P)] (rs : VCResults P) : Format :=
  let rsf := rs.map (fun r => f!"{Format.line}{r}")
  Format.joinSep rsf.toList Format.line

instance [ToFormat (VCResult P)] : ToFormat (VCResults P) where
  format := VCResults.format

instance [ToFormat (VCResult P)] : ToString (VCResults P) where
  toString rs := toString (VCResults.format rs)

end -- public section
end Imperative
