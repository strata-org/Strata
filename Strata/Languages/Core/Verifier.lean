/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.Options
import Strata.Languages.Core.CallGraph
import Strata.Languages.Core.SMTEncoder
import Strata.DL.Imperative.MetaData
import Strata.DL.Imperative.SMTUtils
import Strata.DL.SMT.CexParser
import Strata.DDM.AST
import Strata.Transform.CallElim
import Strata.Transform.FilterProcedures
import Strata.Transform.PrecondElim

---------------------------------------------------------------------

namespace Strata.SMT.Encoder

open Strata.SMT.Encoder
open Strata

-- Derived from Strata.SMT.Encoder.encode.
def encodeCore (ctx : Core.SMT.Context) (prelude : SolverM Unit)
    (assumptionTerms : List Term) (obligationTerm : Term)
    (md : Imperative.MetaData Core.Expression)
    (satisfiabilityCheck validityCheck : Bool) :
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
  -- Assert assumption terms
  let (assumptionIds, estate) ← assumptionTerms.mapM (encodeTerm False) |>.run estate
  for id in assumptionIds do
    Solver.assert id
  -- Encode the obligation term (but don't assert it)
  let (obligationId, estate) ← (encodeTerm False obligationTerm) |>.run estate

  -- Choose encoding strategy: use check-sat-assuming only when doing both checks
  let bothChecks := satisfiabilityCheck && validityCheck
  
  if bothChecks then
    -- Two-sided check: use check-sat-assuming for both Q and ¬Q
    if satisfiabilityCheck then
      Solver.comment "Satisfiability check (can property be true?)"
      Imperative.SMT.addLocationInfo (P := Core.Expression) (md := md)
        (message := ("sat-message", s!"\"Property can be satisfied\""))
      let _ ← Solver.checkSatAssuming [obligationId] []

    if validityCheck then
      Solver.comment "Validity check (can property be false?)"
      Imperative.SMT.addLocationInfo (P := Core.Expression) (md := md)
        (message := ("unsat-message", s!"\"Property is always true\""))
      let negObligationId := s!"(not {obligationId})"
      let _ ← Solver.checkSatAssuming [negObligationId] []
  else
    -- Single check: use assert + check-sat (matches pre-PR behavior)
    if satisfiabilityCheck then
      Solver.comment "Satisfiability check (can property be true?)"
      Imperative.SMT.addLocationInfo (P := Core.Expression) (md := md)
        (message := ("sat-message", s!"\"Property can be satisfied\""))
      Solver.assert obligationId
      let _ ← Solver.checkSat []
    else if validityCheck then
      Solver.comment "Validity check (can property be false?)"
      Imperative.SMT.addLocationInfo (P := Core.Expression) (md := md)
        (message := ("unsat-message", s!"\"Property is always true\""))
      -- obligationId is already the negation of the property, so assert it directly
      Solver.assert obligationId
      let _ ← Solver.checkSat []

  let ids := estate.ufs.values
  return (ids, estate)

end Strata.SMT.Encoder

---------------------------------------------------------------------

namespace Core.SMT
open Std (ToFormat Format format)
open Lambda Strata.SMT

private def typedVarToSMTFn (ctx : SMT.Context) (id : Core.Expression.Ident)
  (ty : Core.Expression.Ty) := do
    -- Type of identifier has to be monotye
    let some mty := LTy.toMonoType? ty | .error s!"not monotype: {id}"
    let (ty', _) ← LMonoTy.toSMTType Env.init mty ctx
    return (id.name, ty')

abbrev Result := Imperative.SMT.Result (Core.Expression.Ident)

def getSolverPrelude : String → SolverM Unit
| "z3" => do
  -- These options are set by the standard Boogie implementation and are
  -- generally good for the Boogie dialect, too, though we may want to
  -- have more fine-grained criteria for when to use them.
  Solver.setOption "smt.mbqi" "false"
  Solver.setOption "auto_config" "false"
| "cvc5" => return ()
| _ => return ()

def getSolverFlags (options : Options) : Array String :=
  let produceModels :=
    match options.solver with
    | "cvc5" => #["--produce-models"]
    -- No need to specify -model for Z3 because we already have `get-value`
    -- in the generated SMT file.
    | _ => #[]
  let setTimeout :=
    match options.solver with
    | "cvc5" => #[s!"--tlimit={options.solverTimeout*1000}"]
    | "z3" => #[s!"-T:{options.solverTimeout}"]
    | _ => #[]
  produceModels ++ setTimeout

def dischargeObligation
  (options : Options)
  (vars : List Expression.TypedIdent)
  (md : Imperative.MetaData Expression)
  (filename : String)
  (assumptionTerms : List Term)
  (obligationTerm : Term)
  (ctx : SMT.Context)
  (satisfiabilityCheck validityCheck : Bool)
  : IO (Except Format (SMT.Result × SMT.Result × EncoderState)) := do
  -- CVC5 requires --incremental for multiple (check-sat) commands
  let baseFlags := getSolverFlags options
  let needsIncremental := satisfiabilityCheck && validityCheck
  let solverFlags :=
    if needsIncremental && options.solver == "cvc5" && !baseFlags.contains "--incremental" then
      baseFlags ++ #["--incremental"]
    else
      baseFlags
  Imperative.SMT.dischargeObligation
    (P := Core.Expression)
    (Strata.SMT.Encoder.encodeCore ctx (getSolverPrelude options.solver)
      assumptionTerms obligationTerm md satisfiabilityCheck validityCheck)
    (typedVarToSMTFn ctx)
    vars
    md
    options.solver
    filename
    solverFlags (options.verbose > .normal)
    satisfiabilityCheck validityCheck

end Core.SMT
---------------------------------------------------------------------

namespace Core
open Imperative Lambda Strata.SMT
open Std (ToFormat Format format)
open Strata

/--
Analysis outcome of a verification condition based on two SMT queries.
-/
structure VCOutcome where
  satisfiabilityProperty : SMT.Result
  validityProperty : SMT.Result
  deriving Repr

instance : Inhabited VCOutcome where
  default := { satisfiabilityProperty := .unknown, validityProperty := .unknown }

namespace VCOutcome

-- Nine base outcome cases (one per combination)

def passAndReachable (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .sat _, .unsat => true
  | _, _ => false

def alwaysFalseAndReachable (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .unsat, .sat _ => true
  | _, _ => false

def indecisiveAndReachable (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .sat _, .sat _ => true
  | _, _ => false

def unreachable (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .unsat, .unsat => true
  | _, _ => false

def satisfiableValidityUnknown (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .sat _, .unknown => true
  | _, _ => false

def alwaysFalseReachabilityUnknown (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .unsat, .unknown => true
  | _, _ => false

def canBeFalseAndReachable (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .unknown, .sat _ => true
  | _, _ => false

def passReachabilityUnknown (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .unknown, .unsat => true
  | _, _ => false

def unknown (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .unknown, .unknown => true
  | _, _ => false

-- Derived predicates (cross-cutting properties)

def isPass (o : VCOutcome) : Bool :=
  match o.validityProperty with
  | .unsat => true
  | _ => false

def isSatisfiable (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty with
  | .sat _ => true
  | _ => false

def isAlwaysFalse (o : VCOutcome) : Bool :=
  o.alwaysFalseAndReachable || o.alwaysFalseReachabilityUnknown

def isAlwaysTrue (o : VCOutcome) : Bool :=
  o.isPass

def isReachable (o : VCOutcome) : Bool :=
  o.passAndReachable || o.alwaysFalseAndReachable || o.indecisiveAndReachable

-- Backward compatibility aliases (old names with "is" prefix)
def isPassAndReachable := passAndReachable
def isRefutedAndReachable := alwaysFalseAndReachable
def isIndecisiveAndReachable := indecisiveAndReachable
def isUnreachable := unreachable
def isSatisfiableValidityUnknown := satisfiableValidityUnknown
def isAlwaysFalseReachabilityUnknown := alwaysFalseReachabilityUnknown
def isCanBeFalseAndReachable := canBeFalseAndReachable
def isPassReachabilityUnknown := passReachabilityUnknown
def isUnknown := unknown
def isRefuted := alwaysFalseAndReachable
def isRefutedIfReachable := alwaysFalseReachabilityUnknown
def isIndecisive := indecisiveAndReachable
def isAlwaysTrueIfReachable := passReachabilityUnknown
def isPassIfReachable := passReachabilityUnknown
def isAlwaysFalseIfReachable := alwaysFalseReachabilityUnknown
def isReachableAndCanBeFalse := canBeFalseAndReachable

def label (o : VCOutcome) : String :=
  if o.passAndReachable then "pass and reachable from declaration entry"
  else if o.alwaysFalseAndReachable then "refuted and reachable from declaration entry"
  else if o.indecisiveAndReachable then "indecisive and reachable from declaration entry"
  else if o.unreachable then "unreachable"
  else if o.satisfiableValidityUnknown then "satisfiable"
  else if o.alwaysFalseReachabilityUnknown then "refuted if reachable"
  else if o.canBeFalseAndReachable then "reachable from declaration entry and can be false"
  else if o.passReachabilityUnknown then "pass if reachable"
  else "unknown"

def emoji (o : VCOutcome) : String :=
  if o.passAndReachable then "✅"
  else if o.alwaysFalseAndReachable then "❌"
  else if o.indecisiveAndReachable then "🔶"
  else if o.unreachable then "⛔"
  else if o.satisfiableValidityUnknown then "➕"
  else if o.alwaysFalseReachabilityUnknown then "✖️"
  else if o.canBeFalseAndReachable then "➖"
  else if o.passReachabilityUnknown then "✔️"
  else "❓"

end VCOutcome

instance : ToFormat VCOutcome where
  format o := s!"{o.emoji} {o.label}"

/--
A collection of all information relevant to a verification condition's
analysis.
-/
structure VCResult where
  obligation : Imperative.ProofObligation Expression
  outcome : Except String VCOutcome := .error "not yet computed"
  estate : EncoderState := EncoderState.init
  verbose : VerboseMode := .normal

instance : ToFormat VCResult where
  format r :=
    match r.outcome with
    | .error e => f!"Obligation: {r.obligation.label}\nImplementation Error: {e}"
    | .ok outcome =>
      let models := match outcome.satisfiabilityProperty, outcome.validityProperty with
        | .sat m1, .sat m2 =>
          if r.verbose >= VerboseMode.models then
            if !m1.isEmpty && !m2.isEmpty then
              f!"\nModel (property true): {m1}\nModel (property false): {m2}"
            else if !m1.isEmpty then
              f!"\nModel (property true): {m1}"
            else if !m2.isEmpty then
              f!"\nModel (property false): {m2}"
            else ""
          else ""
        | .sat m, _ =>
          if r.verbose >= VerboseMode.models && !m.isEmpty then
            f!"\nModel (property true): {m}"
          else ""
        | _, .sat m =>
          if r.verbose >= VerboseMode.models && !m.isEmpty then
            f!"\nModel (property false): {m}"
          else ""
        | _, _ => ""
      f!"Obligation: {r.obligation.label}\nProperty: {r.obligation.property}\nResult: {outcome}{models}"

def VCResult.isSuccess (vr : VCResult) : Bool :=
  match vr.outcome with
  | .ok o => o.isPass
  | .error _ => false

def VCResult.isFailure (vr : VCResult) : Bool :=
  match vr.outcome with
  | .ok o => o.isRefuted || o.isIndecisive
  | .error _ => false

def VCResult.isUnknown (vr : VCResult) : Bool :=
  match vr.outcome with
  | .ok o => o.isUnknown
  | .error _ => false

def VCResult.isImplementationError (vr : VCResult) : Bool :=
  match vr.outcome with
  | .error _ => true
  | .ok _ => false

def VCResult.isNotSuccess (vcResult : Core.VCResult) :=
  !Core.VCResult.isSuccess vcResult

def VCResult.isUnreachable (vr : VCResult) : Bool :=
  match vr.outcome with
  | .ok o => o.isUnreachable
  | .error _ => false

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
      let outcome := VCOutcome.mk .unsat (.sat [])
      let result := { obligation, outcome := .ok outcome, verbose := options.verbose }
      return (obligation, some result)
    else
      return (obligation, none)
  | .assert =>
    if obligation.obligation.isTrue then
      -- We don't need the SMT solver if PE (partial evaluation) is enough to
      -- reduce the consequent to true.
      let outcome := VCOutcome.mk (.sat []) .unsat
      let result := { obligation, outcome := .ok outcome, verbose := options.verbose }
      return (obligation, some result)
    else if obligation.obligation.isFalse && obligation.assumptions.isEmpty then
      -- If PE determines that the consequent is false and the path conditions
      -- are empty, then we can immediately report a verification failure. Note
      -- that we go to the SMT solver if the path conditions aren't empty --
      -- after all, the path conditions could imply false, which the PE isn't
      -- capable enough to infer.
      let prog := f!"\n\n[DEBUG] Evaluated program:\n{Core.formatProgram p}"
      dbg_trace f!"\n\nObligation {obligation.label}: failed!\
                   \n\nResult obtained during partial evaluation.\
                   {if options.verbose >= .normal then prog else ""}"
      let outcome := VCOutcome.mk .unsat (.sat [])
      let result := { obligation, outcome := .ok outcome, verbose := options.verbose }
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
def getObligationResult (assumptionTerms : List Term) (obligationTerm : Term)
    (ctx : SMT.Context)
    (obligation : ProofObligation Expression) (p : Program)
    (options : Options) (counter : IO.Ref Nat)
    (tempDir : System.FilePath) (satisfiabilityCheck validityCheck : Bool)
    : EIO DiagnosticModel VCResult := do
  let prog := f!"\n\n[DEBUG] Evaluated program:\n{Core.formatProgram p}"
  let counterVal ← counter.get
  counter.set (counterVal + 1)
  let filename := tempDir / s!"{obligation.label}_{counterVal}.smt2"
  let varsInObligation := ProofObligation.getVars obligation
  -- All variables in ProofObligation must have been typed.
  let typedVarsInObligation ← varsInObligation.mapM
    (fun (v,ty) => do
      match ty with
      | .some ty => return (v,LTy.forAll [] ty)
      | .none => throw (DiagnosticModel.fromMessage s!"{v} untyped"))
  let ans ←
      IO.toEIO
        (fun e => DiagnosticModel.fromFormat f!"{e}")
        (SMT.dischargeObligation options
            typedVarsInObligation
            obligation.metadata
            filename.toString
          assumptionTerms obligationTerm ctx satisfiabilityCheck validityCheck)
  match ans with
  | .error e =>
    dbg_trace f!"\n\nObligation {obligation.label}: SMT Solver Invocation Error!\
                 \n\nError: {e}\
                 {if options.verbose >= .normal then prog else ""}"
    .error <| DiagnosticModel.fromFormat e
  | .ok (satResult, validityResult, estate) =>
    let outcome := VCOutcome.mk satResult validityResult
    let result := { obligation,
                    outcome := .ok outcome,
                    estate,
                    verbose := options.verbose }
    return result

def verifySingleEnv (pE : Program × Env) (options : Options)
    (counter : IO.Ref Nat) (tempDir : System.FilePath) :
    EIO DiagnosticModel VCResults := do
  let (p, E) := pE
  match E.error with
  | some err =>
    .error <| DiagnosticModel.fromFormat s!"🚨 Error during evaluation!\n\
              {format err}\n\n\
              [DEBUG] Evaluated program: {Core.formatProgram p}\n\n"
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
            let prog := f!"\n\n[DEBUG] Evaluated program:\n{Core.formatProgram p}"
            dbg_trace f!"\n\nResult: {result}\n{prog}"
          if options.stopOnFirstError then break else continue
      -- For `unknown` results, we appeal to the SMT backend below.
      let maybeTerms := ProofObligation.toSMTTerms E obligation SMT.Context.default options.useArrayTheory
      match maybeTerms with
      | .error err =>
        let err := f!"SMT Encoding Error! " ++ err
        let result := { obligation,
                        outcome := .error (toString err),
                        verbose := options.verbose }
        if options.verbose >= .normal then
          let prog := f!"\n\n[DEBUG] Evaluated program:\n{Core.formatProgram p}"
          dbg_trace f!"\n\nResult: {result}\n{prog}"
        results := results.push result
        if options.stopOnFirstError then break
      | .ok (assumptionTerms, obligationTerm, ctx) =>
        -- Determine which checks to perform based on metadata or check mode/amount
        let (satisfiabilityCheck, validityCheck) :=
          if Imperative.MetaData.hasFullCheck obligation.metadata then
            (true, true)  -- fullCheck annotation: always run both
          else
            -- Derive checks from check mode and amount
            match options.checkMode, options.checkAmount, obligation.property with
            | _, .full, _ => (true, true)  -- Full: both checks
            | .deductive, .minimal, .assert => (false, true)  -- Deductive needs validity
            | .deductive, .minimal, .cover => (true, false)   -- Cover uses satisfiability
            | .bugFinding, .minimal, .assert => (true, false) -- Bug finding needs satisfiability
            | .bugFinding, .minimal, .cover => (true, false)  -- Cover uses satisfiability
        let result ← getObligationResult assumptionTerms obligationTerm ctx obligation p options
                      counter tempDir satisfiabilityCheck validityCheck
        results := results.push result
        if result.isNotSuccess then
          if options.verbose >= .normal then
            let prog := f!"\n\n[DEBUG] Evaluated program:\n{Core.formatProgram p}"
            dbg_trace f!"\n\nResult: {result}\n{prog}"
          if options.stopOnFirstError then break
    return results

/-- Run the Strata Core verification pipeline on a program: transform,
type-check, partially evaluate, and discharge proof obligations via SMT.
All program-wide transformations that occur before any analyses
(including type inference) should be placed here. -/
def verify (program : Program)
    (tempDir : System.FilePath)
    (proceduresToVerify : Option (List String) := none)
    (options : Options := Options.default)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default)
    : EIO DiagnosticModel VCResults := do
  let factory ← EIO.ofExcept (Core.Factory.addFactory moreFns)
  let runPrecondElim := fun prog => do
    let (_changed, prog) ← PrecondElim.precondElim prog factory
    return prog
  let finalProgram ← match proceduresToVerify with
    | none =>
      match Transform.run program runPrecondElim with
      | .ok prog => .ok prog
      | .error e => .error (DiagnosticModel.fromFormat f!"❌ Transform Error. {e}")
    | some procs =>
       -- Verify specific procedures. By default, we apply the call elimination
       -- transform to the targeted procedures to inline the contracts of any
       -- callees. Call elimination is applied once, since once is enough to
       -- replace all calls with contracts.
      let passes := fun prog => do
        let prog ← FilterProcedures.run prog procs
        let (_changed,prog) ← CallElim.callElim' prog
        let prog ← FilterProcedures.run prog procs
        let prog ← runPrecondElim prog
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
                 (List.mapM (fun pE => verifySingleEnv pE options counter tempDir) pEs)
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
    (env : Program)
    (ictx : InputContext := Inhabited.default)
    (proceduresToVerify : Option (List String) := none)
    (options : Options := Options.default)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default)
    : IO Core.VCResults := do
  let (program, errors) := Core.getProgram env ictx
  if errors.isEmpty then
    let runner tempDir :=
      EIO.toIO (fun dm => IO.Error.userError (toString (dm.format (some ictx.fileMap))))
                  (Core.verify program tempDir proceduresToVerify options moreFns)
    match options.vcDirectory with
    | .none =>
      IO.FS.withTempDir runner
    | .some p =>
      IO.FS.createDirAll ⟨p.toString⟩
      runner ⟨p.toString⟩
  else
    panic! s!"DDM Transform Error: {repr errors}"

def toDiagnosticModel (vcr : Core.VCResult) : Option DiagnosticModel :=
  let fileRange := (Imperative.getFileRange vcr.obligation.metadata).getD default
  match vcr.outcome with
  | .error msg => some { fileRange, message := s!"analysis error: {msg}" }
  | .ok outcome =>
    let message? : Option String :=
      if vcr.obligation.property == .cover then
        if outcome.isPass then none
        else if outcome.isRefuted then some "cover property is not satisfiable"
        else if outcome.isIndecisive then some "cover property is indecisive"
        else if outcome.isUnreachable then some "cover property is unreachable"
        else if outcome.isSatisfiable then none
        else if outcome.isRefutedIfReachable then some "cover property is not satisfiable if reachable"
        else if outcome.isReachableAndCanBeFalse then some "cover property can be false"
        else if outcome.isAlwaysTrueIfReachable then none
        else some "cover property could not be checked"
      else
        if outcome.isPass then none
        else if outcome.isRefuted then some "assertion does not hold"
        else if outcome.isIndecisive then some "assertion is indecisive (true or false depending on inputs)"
        else if outcome.isUnreachable then some "assertion holds vacuously (path unreachable)"
        else if outcome.isSatisfiable then none
        else if outcome.isRefutedIfReachable then some "assertion does not hold if reachable"
        else if outcome.isReachableAndCanBeFalse then some "assertion can be false"
        else if outcome.isAlwaysTrueIfReachable then none
        else some "assertion could not be proved"
    message?.map fun message => { fileRange, message }

structure Diagnostic where
  start : Lean.Position
  ending : Lean.Position
  message : String
  deriving Repr, BEq

def DiagnosticModel.toDiagnostic (files: Map Strata.Uri Lean.FileMap) (dm: DiagnosticModel): Diagnostic :=
  let fileMap := (files.find? dm.fileRange.file).getD (panic s!"Could not find {repr dm.fileRange.file} in {repr files.keys} when converting model '{dm}' to a diagnostic")
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
