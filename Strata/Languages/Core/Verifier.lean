/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.DDMTransform.Translate
public import Strata.Languages.Core.DDMTransform.ASTtoCST
public import Strata.Languages.Core.Options
public import Strata.Languages.Core.CallGraph
public import Strata.Languages.Core.SMTEncoder
public import Strata.DL.Imperative.MetaData
public import Strata.DL.Imperative.SMTUtils
public import Strata.DDM.AST
import Strata.Transform.CallElim
import Strata.Transform.FilterProcedures
import Strata.Transform.PrecondElim
public import Strata.Transform.IrrelevantAxioms
import Strata.Util.Profile

---------------------------------------------------------------------

namespace Strata.SMT.Encoder

open Strata.SMT.Encoder
open Strata

public section

/-- Encode a verification condition into SMT-LIB format.

This function encodes the path conditions (P) and obligation (Q) into SMT,
then emits check-sat commands to determine satisfiability and/or validity.

When both checks are requested, uses check-sat-assuming for efficiency:
- Satisfiability: (check-sat-assuming (Q)) tests if P ∧ Q is satisfiable
- Validity: (check-sat-assuming ((not Q))) tests if P ∧ ¬Q is satisfiable

When only one check is requested, uses assert + check-sat:
- For satisfiability: (assert Q) (check-sat) tests P ∧ Q
- For validity: (assert (not Q)) (check-sat) tests P ∧ ¬Q

Note: The obligation term Q is encoded without negation. Negation is applied
when needed for the validity check (line 64 for check-sat-assuming, line 77 for assert).
-/
def encodeCore (ctx : Core.SMT.Context) (prelude : SolverM Unit)
    (assumptionTerms : List Term) (obligationTerm : Term)
    (md : Imperative.MetaData Core.Expression)
    (satisfiabilityCheck validityCheck : Bool) :
    SolverM (List String × EncoderState) := do
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
  -- Encode the obligation term Q (not negated)
  let (obligationId, estate) ← (encodeTerm False obligationTerm) |>.run estate

  let ids := estate.ufs.toList.filterMap fun (uf, id) =>
    if uf.args.isEmpty then some id else none

  -- Choose encoding strategy: use check-sat-assuming only when doing both checks
  let bothChecks := satisfiabilityCheck && validityCheck

  if bothChecks then
    -- Satisfiability check: P ∧ Q satisfiable?
    Solver.comment "Satisfiability"
    Imperative.SMT.addLocationInfo (P := Core.Expression) (md := md)
      (message := ("sat-message", s!"\"Property can be satisfied\""))
    let obligationStr ← Solver.termToSMTString obligationId
    let _ ← Solver.checkSatAssuming [obligationStr] ids

    -- Validity check: P ∧ ¬Q satisfiable?
    Solver.comment "Validity"
    Imperative.SMT.addLocationInfo (P := Core.Expression) (md := md)
      (message := ("unsat-message", s!"\"Property is always true\""))
    let negObligationStr := s!"(not {obligationStr})"
    let _ ← Solver.checkSatAssuming [negObligationStr] ids
  else
    if satisfiabilityCheck then
      -- P ∧ Q satisfiable?
      Solver.comment "Satisfiability"
      Imperative.SMT.addLocationInfo (P := Core.Expression) (md := md)
        (message := ("sat-message", s!"\"Property can be satisfied\""))
      Solver.assert obligationId
      let _ ← Solver.checkSat ids
    else if validityCheck then
      -- P ∧ ¬Q satisfiable?
      Solver.comment "Validity"
      Imperative.SMT.addLocationInfo (P := Core.Expression) (md := md)
        (message := ("unsat-message", s!"\"Property is always true\""))
      Solver.assert (← encodeTerm False (Factory.not obligationTerm) |>.run estate).1
      let _ ← Solver.checkSat ids

  -- Emit the "message" metadata field at the very end (once per obligation).
  match md.findElem Imperative.MetaData.message with
  | some elem =>
    let msg := toString (Std.format elem.value) |>.replace "\\" "\\\\" |>.replace "\"" "\\\""
    Solver.setInfo "final-message" s!"\"{msg}\""
  | none => pure ()

  return (ids, estate)

end -- public section
end Strata.SMT.Encoder

---------------------------------------------------------------------

namespace Core.SMT
open Std (ToFormat Format format)
open Lambda Strata.SMT

public section

private def typedVarToSMTFn (ctx : SMT.Context) (id : Core.Expression.Ident)
  (ty : Core.Expression.Ty) := do
    -- Type of identifier has to be monotye
    let some mty := LTy.toMonoType? ty | .error s!"not monotype: {id}"
    let (ty', _) ← LMonoTy.toSMTType Env.init mty ctx
    return (id.name, ty')

@[expose] abbrev Result := Imperative.SMT.Result (Core.Expression.Ident)

def getSolverPrelude : String → SolverM Unit
| "z3" => do
  -- These options are set by the standard Boogie implementation and are
  -- generally good for the Boogie dialect, too, though we may want to
  -- have more fine-grained criteria for when to use them.
  Solver.setOption "smt.mbqi" "false"
  Solver.setOption "auto_config" "false"
| "cvc5" => return ()
| _ => return ()

def getSolverFlags (options : VerifyOptions) : Array String :=
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
  (options : VerifyOptions)
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
    options.solver
    filename
    solverFlags (options.verbose > .normal)
    satisfiabilityCheck validityCheck
    (skipSolver := options.skipSolver)

end -- public section
end Core.SMT
---------------------------------------------------------------------

namespace Core
open Imperative Lambda Strata.SMT
open Std (ToFormat Format format)
open Strata

public section

/-- A solver log entry recording the SMT result after a specific pipeline phase. -/
structure SolverPhaseLog where
  /-- Name of the pipeline phase that produced this entry. -/
  phase : String
  /-- The SMT result after this phase's validation. -/
  result : SMT.Result
  deriving Repr, BEq

/-- Validate a model against all phases for a given obligation. Phases are
    recorded top-down, so we reverse them to validate from the last
    (innermost) phase first. Returns the adjusted result and a log of
    intermediate results per phase, ordered outermost-first (deepest phase
    closest to SMT at the end).

    Each phase independently validates the model when it has a validator.
    A phase with `modelToValidate` can demote `.sat m` to `.unknown (some m)`
    (when the model fails validation) or promote `.unknown (some m)` back to
    `.sat m` (when the model passes validation against the pre-phase
    semantics). This means phases are not cascading — each validating
    phase makes its own decision based on the model. -/
def AbstractedPhase.validateModel (phases : List AbstractedPhase)
    (result : SMT.Result)
    (obligation : ProofObligation Expression)
    : SMT.Result × List SolverPhaseLog :=
  -- Process phases innermost-first; accumulate log entries in reverse
  let (finalResult, revLog) := phases.reverse.foldl (init := (result, [])) fun (r, log) p =>
    let validation := p.getValidation obligation
    let r' := match r, validation with
      | .sat m, .modelToValidate f => if f m then .sat m else .unknown (some m)
      | .unknown (some m), .modelToValidate f => if f m then .sat m else .unknown (some m)
      -- .unknown none or .modelPreserving: pass through unchanged
      | _, _ => r
    (r', { phase := p.name, result := r' } :: log)
  -- Reverse log so outermost is first, deepest is last
  (finalResult, revLog.reverse)

/--
Analysis outcome of a verification condition based on two SMT queries:
  - satisfiabilityProperty: result of checking P ∧ Q  (is the property satisfiable given the path condition?)
  - validityProperty:       result of checking P ∧ ¬Q (can the property be false given the path condition?)

The 9 possible outcomes and their interpretations.
For cover statements, any outcome where P ∧ Q is sat displays as ✅ (cover satisfied).
Unreachable covers display as ❌ (error) instead of ⛔ (warning).

  Emoji  Label                                          P ∧ Q    P ∧ ¬Q   Reachable  Deductive  BugFinding  BugFinding+Complete  Meaning
  -----  ---------------------------------------------  -------  -------  ---------  ---------  ----------  -------------------  -------
  ✅     always true and is reachable                   sat      unsat    yes        pass       pass        pass                 Property always true, reachable from declaration entry
  ❌     always false and is reachable                  unsat    sat      yes        error      error       error                Property always false, reachable from declaration entry
  🔶     can be both true and false and is reachable    sat      sat      yes        error      note        error                Reachable, solver found models for both the property and its negation
  ⛔     unreachable                                    unsat    unsat    no         warning    error       error                Dead code, path unreachable
  ➕     can be true and is reachable                   sat      unknown  yes        error      note        note                 Property can be true and is reachable, unknown if always true
  ✖️     always false if reached                        unsat    unknown  unknown    error      error       error                Property always false if reached, unknown if reachable
  ➖     can be false and is reachable                  unknown  sat      yes        error      note        error                Property can be false and is reachable, unknown if always false
  ✔️     always true if reached                         unknown  unsat    unknown    pass       pass        pass                 Property always true if reached, unknown if reachable
  ❓     unknown                                        unknown  unknown  unknown    error      note        note                 Both checks inconclusive
-/
structure VCOutcome where
  satisfiabilityProperty : SMT.Result
  validityProperty : SMT.Result
  /-- Ordered log of solver results: the raw solver results followed by
      per-phase adjusted results (e.g. sat→unknown when a phase cannot
      validate the model). Consumed by future diagnostic and traceability
      tooling. -/
  solverLog : List SolverPhaseLog := []
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

def canBeTrueOrFalseAndIsReachable (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .sat _, .sat _ => true
  | _, _ => false

def unreachable (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .unsat, .unsat => true
  | _, _ => false

def satisfiableValidityUnknown (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .sat _, .unknown _ => true
  | _, _ => false

def alwaysFalseReachabilityUnknown (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .unsat, .unknown _ => true
  | _, _ => false

def canBeFalseAndIsReachable (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .unknown _, .sat _ => true
  | _, _ => false

def passReachabilityUnknown (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .unknown _, .unsat => true
  | _, _ => false

def unknown (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .unknown _, .unknown _ => true
  | _, _ => false

/-- True when either SMT property is `.err` (solver returned an error on
    a specific check, as opposed to the outer `VCResult.outcome` being
    `.error` due to an encoding failure). -/
def hasSMTError (o : VCOutcome) : Bool :=
  match o.satisfiabilityProperty, o.validityProperty with
  | .err _, _ | _, .err _ => true
  | _,      _             => false

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
  o.passAndReachable || o.alwaysFalseAndReachable || o.canBeTrueOrFalseAndIsReachable

-- Backward compatibility aliases (old names with "is" prefix)
def isPassAndReachable := passAndReachable
def isRefutedAndReachable := alwaysFalseAndReachable
def isCanBeTrueOrFalseAndIsReachable := canBeTrueOrFalseAndIsReachable
def isUnreachable := unreachable
def isSatisfiableValidityUnknown := satisfiableValidityUnknown
def isAlwaysFalseReachabilityUnknown := alwaysFalseReachabilityUnknown
def isCanBeFalseAndReachable := canBeFalseAndIsReachable
def isPassReachabilityUnknown := passReachabilityUnknown
def isUnknown := unknown
def isRefuted := alwaysFalseAndReachable
def isRefutedIfReachable := alwaysFalseReachabilityUnknown
def isCanBeTrueOrFalse := canBeTrueOrFalseAndIsReachable
def isAlwaysTrueIfReachable := passReachabilityUnknown
def isPassIfReachable := passReachabilityUnknown
def isAlwaysFalseIfReachable := alwaysFalseReachabilityUnknown
def isReachableAndCanBeFalse := canBeFalseAndIsReachable

/-- Select the pass or fail message based on check mode and property type.
    In deductive mode, unreachable paths pass or fail depending on the property;
    in other modes, unreachable always fails. -/
private def unreachableMsg (checkMode : VerificationMode) (passWhenUnreachable : Bool)
    (passMsg failMsg : α) : α :=
  match checkMode with
  | .deductive => if passWhenUnreachable then passMsg else failMsg
  | _ => failMsg

def label (o : VCOutcome) (property : Imperative.PropertyType)
    (checkLevel : CheckLevel) (checkMode : VerificationMode) : String :=
  -- Unreachable is detected when both checks ran (via fullCheck annotation or full level)
  if o.unreachable then
    unreachableMsg checkMode property.passWhenUnreachable
      "pass (❗path unreachable)" "fail (❗path unreachable)"
  -- Simplified labels for minimal check level
  else if checkLevel == .minimal then
    match property, checkMode with
    | .assert, .deductive | .divisionByZero, .deductive =>
      -- Validity check only: unsat=pass, sat=fail, unknown=unknown
      match o.validityProperty with
      | .unsat => "pass"
      | .sat _ => "fail"
      | .unknown _ => "unknown"
      | .err _ => "unknown"
    | .assert, .bugFinding | .assert, .bugFindingAssumingCompleteSpec
    | .divisionByZero, .bugFinding | .divisionByZero, .bugFindingAssumingCompleteSpec =>
      -- Satisfiability check only: sat=satisfiable, unsat=fail, unknown=unknown
      match o.satisfiabilityProperty with
      | .sat _ => "satisfiable"
      | .unsat => "fail"
      | .unknown _ => "unknown"
      | .err _ => "unknown"
    | .cover, _ =>
      -- Satisfiability check only: sat=pass, unsat=fail, unknown=unknown
      match o.satisfiabilityProperty with
      | .sat _ => "pass"
      | .unsat => "fail"
      | .unknown _ => "unknown"
      | .err _ => "unknown"
  -- MinimalVerbose and Full: detailed labels with unreachable indicator
  else
    -- For cover: satisfiability sat means the cover is satisfied (pass)
    if property == .cover && o.isSatisfiable then "satisfiable and reachable from declaration entry"
    else if o.passAndReachable then "always true and is reachable from declaration entry"
    else if o.alwaysFalseAndReachable then "always false and is reachable from declaration entry"
    else if o.canBeTrueOrFalseAndIsReachable then "can be both true and false and is reachable from declaration entry"
    else if o.satisfiableValidityUnknown then "can be true and is reachable from declaration entry"
    else if o.alwaysFalseReachabilityUnknown then "always false if reached"
    else if o.canBeFalseAndIsReachable then "can be false and is reachable from declaration entry"
    else if o.passReachabilityUnknown then "always true if reached"
    else "unknown"

def emoji (o : VCOutcome) (property : Imperative.PropertyType)
    (checkLevel : CheckLevel) (checkMode : VerificationMode) : String :=
  -- Unreachable is detected when both checks ran
  if o.unreachable then
    unreachableMsg checkMode property.passWhenUnreachable "✅" "❌"
  -- Simplified emojis for minimal check level
  else if checkLevel == .minimal then
    match property, checkMode with
    | .assert, .deductive | .divisionByZero, .deductive =>
      -- Validity check only: unsat=✅, sat=❌, unknown=❓
      match o.validityProperty with
      | .unsat => "✅"
      | .sat _ => "❌"
      | .unknown _ => "❓"
      | .err _ => "❓"
    | .assert, .bugFinding | .assert, .bugFindingAssumingCompleteSpec
    | .divisionByZero, .bugFinding | .divisionByZero, .bugFindingAssumingCompleteSpec =>
      -- Satisfiability check only: sat=❓ (satisfiable), unsat=❌, unknown=❓
      match o.satisfiabilityProperty with
      | .sat _ => "❓"  -- Different meaning: satisfiable but don't know if always true
      | .unsat => "❌"
      | .unknown _ => "❓"
      | .err _ => "❓"
    | .cover, _ =>
      -- Satisfiability check only: sat=✅, unsat=❌, unknown=❓
      match o.satisfiabilityProperty with
      | .sat _ => "✅"
      | .unsat => "❌"
      | .unknown _ => "❓"
      | .err _ => "❓"
  -- MinimalVerbose and Full: detailed emojis
  else
    if property == .cover && o.isSatisfiable then "✅"
    else if o.passAndReachable then "✅"
    else if o.alwaysFalseAndReachable then "❌"
    else if o.canBeTrueOrFalseAndIsReachable then "🔶"
    else if o.satisfiableValidityUnknown then "➕"
    else if o.alwaysFalseReachabilityUnknown then "✖️"
    else if o.canBeFalseAndIsReachable then "➖"
    else if o.passReachabilityUnknown then "✔️"
    else "❓"

end VCOutcome


/--
A model with values lifted to LExpr for display purposes.
This is used for formatting models in a human-readable way
using Core's expression formatter and for future use as program metadata.
-/
@[expose] abbrev LExprModel := List (Expression.Ident × LExpr CoreLParams.mono)

/-- Format a model value using the Core DDM formatter.
    Renders constructors, applications, and primitives with Core syntax
    (e.g. `Cons(0, Nil)`, `Right(true)`). -/
private def formatModelValue (e : LExpr CoreLParams.mono) : Format :=
  Core.formatExprs [e]

def LExprModel.format (model : LExprModel) : Format :=
  match model with
  | [] => ""
  | [(id, e)] => f!"({id}, {formatModelValue e})"
  | (id, e) :: rest =>
    let first := f!"({id}, {formatModelValue e}) "
    rest.foldl (fun acc (id', e') => acc ++ f!"({id'}, {formatModelValue e'}) ") first

instance : ToFormat LExprModel where
  format := LExprModel.format

/--
A collection of all information relevant to a verification condition's
analysis.
-/
structure VCResult where
  obligation : Imperative.ProofObligation Expression
  outcome : Except String VCOutcome := .error "not yet computed"
  estate : EncoderState := EncoderState.init
  verbose : VerboseMode := .normal
  checkLevel : CheckLevel := .minimal
  checkMode : VerificationMode := .deductive
  /-- model with values converted from `SMT.Term` to Core `LExpr`.
      The contents must be consistent with the outcome, if the outcome was a failure. -/
  lexprModel : LExprModel := []

/-- Mask outcome properties that were not requested.
    When PE (partial evaluation) resolves a check that wasn't requested by the
    check mode/level, we set it to `.unknown` so the label function displays
    the appropriate message for the checks that were actually requested.
    For example, in minimal deductive mode we only request validity, so if PE
    also determined satisfiability, we mask it to `.unknown`. -/
def maskOutcome (outcome : VCOutcome) (satisfiabilityCheck validityCheck : Bool) : VCOutcome :=
  if satisfiabilityCheck && validityCheck then
    outcome
  else if validityCheck && !satisfiabilityCheck then
    -- Mask to .unknown none — the solverLog preserves the original result
    { outcome with satisfiabilityProperty := .unknown }
  else if satisfiabilityCheck && !validityCheck then
    { outcome with validityProperty := .unknown }
  else
    { outcome with satisfiabilityProperty := .unknown, validityProperty := .unknown }

instance : ToFormat VCResult where
  format r :=
    match r.outcome with
    | .error e =>
      let prop := r.obligation.property
      f!"Obligation: {r.obligation.label}\nProperty: {prop}\nResult: 🚨 Implementation Error! {e}"
    | .ok outcome =>
      let modelFmt :=
        if r.verbose >= .models && !r.lexprModel.isEmpty then
          f!"\nModel:\n{r.lexprModel}"
        else f!""
      let prop := r.obligation.property
      f!"Obligation: {r.obligation.label}\nProperty: {prop}\nResult: {outcome.emoji prop r.checkLevel r.checkMode} {outcome.label prop r.checkLevel r.checkMode}{modelFmt}"

/-- Compact single-line outcome string: emoji + label
    (e.g. "✅ pass", "❌ fail"). Uses the property, check level,
    and check mode stored in the result. -/
def VCResult.formatOutcome (r : VCResult) : String :=
  let prop := r.obligation.property
  match r.outcome with
  | .ok o =>
    s!"{o.emoji prop r.checkLevel r.checkMode} \
       {o.label prop r.checkLevel r.checkMode}"
  | .error e => s!"🚨 {e}"

def VCResult.isSuccess (vr : VCResult) : Bool :=
  match vr.outcome with
  | .ok o => o.isPass
  | .error _ => false

def VCResult.isFailure (vr : VCResult) : Bool :=
  match vr.outcome with
  | .ok o => o.alwaysFalseAndReachable || o.alwaysFalseReachabilityUnknown || o.canBeTrueOrFalseAndIsReachable || o.canBeFalseAndIsReachable
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
  | .ok o => o.unreachable
  | .error _ => false

/-- True when either SMT property inside a successful outcome is `.err`.
    Complements `isImplementationError`, which covers the outer `.error` case. -/
def VCResult.hasSMTError (vr : VCResult) : Bool :=
  match vr.outcome with
  | .ok o => o.hasSMTError
  | .error _ => false

@[expose] abbrev VCResults := Array VCResult

def VCResults.format (rs : VCResults) : Format :=
  let rsf := rs.map (fun r => f!"{Format.line}{r}")
  Format.joinSep rsf.toList Format.line

instance : ToFormat VCResults where
  format := VCResults.format

instance : ToString VCResults where
  toString rs := toString (VCResults.format rs)

/--
Preprocess a proof obligation using partial evaluation (PE).
Returns PE-determined results for satisfiability and validity independently.
Each result is `some r` if PE can determine it, `none` if the solver is needed.
-/
def preprocessObligation (obligation : ProofObligation Expression) (p : Program)
    (options : VerifyOptions) (satisfiabilityCheck validityCheck : Bool)
    (axiomCache : Option IrrelevantAxioms.Cache := .none)
    : EIO DiagnosticModel (ProofObligation Expression × Option SMT.Result × Option SMT.Result) := do
  -- PE can determine satisfiability if the obligation is literally false (unsat)
  let peSatResult : Option SMT.Result :=
    if !satisfiabilityCheck then some .unknown
    else if obligation.obligation.isFalse then some .unsat
    else none
  -- PE can determine validity if the obligation is literally true (valid = unsat)
  -- or literally false with empty assumptions (invalid = sat)
  let peValResult : Option SMT.Result :=
    if !validityCheck then some .unknown
    else if obligation.obligation.isTrue then some .unsat
    else if obligation.obligation.isFalse && obligation.assumptions.isEmpty then some (.sat [])
    else none
  -- If PE resolved both, log for the assert(false) case
  if let (some _, some (.sat _)) := (peSatResult, peValResult) then
    if obligation.property == .assert then
      let prog := f!"\n\n[DEBUG] Evaluated program:\n{Core.formatProgram p}"
      dbg_trace f!"\n\nObligation {obligation.label}: failed!\
                   \n\nResult obtained during partial evaluation.\
                   {if options.verbose >= .normal then prog else ""}"
  -- Apply axiom pruning if needed.
  -- Axiom removal is unsound for cover obligations (removing axioms weakens
  -- path conditions, potentially making unreachable paths appear satisfiable).
  let obligation ←
    match options.removeIrrelevantAxioms, axiomCache, obligation.property with
    | .Off, _, _ | _, .none, _ | _, _, .cover => pure obligation
    | mode, .some cache, _ => -- All property types except `.cover`.
      if peSatResult.isSome && peValResult.isSome then pure obligation
      else do
        let consequentFns := obligation.obligation.getOps.map CoreIdent.toPretty
        let relevantFns :=
          match mode with
          | .Aggressive => consequentFns
          | .Precise =>
            -- Extract functions from non-axiom path conditions only. Axioms
            -- are excluded because including them would seed the relevant-function
            -- set with every function they mention, causing those axioms to be
            -- found trivially relevant and never removed.
            let axiomNames : List String := p.decls.filterMap (fun decl =>
              match decl with | .ax a _ => some a.name | _ => none)
            let antecedentFns :=
              (obligation.assumptions.flatten : List (String × Expression.Expr)).flatMap
                (fun (label, e) =>
                  if axiomNames.contains label then []
                  else (Lambda.LExpr.getOps e).map CoreIdent.toPretty)
            (consequentFns ++ antecedentFns).dedup
          | .Off => consequentFns  -- unreachable; handled above
        let irrelevantAxioms :=
          IrrelevantAxioms.getIrrelevantAxioms p cache relevantFns
        let newAssumptions :=
          Imperative.PathConditions.removeByNames obligation.assumptions irrelevantAxioms
        pure { obligation with assumptions := newAssumptions }
  return (obligation, peSatResult, peValResult)

/-- Keep-set filter pipeline phase: after all transforms, retains only the
    target procedures and their WF-checking procedures (generated by
    PrecondElim). Model-preserving because it only removes procedures. -/
def keepSetFilterPipelinePhase (procs : List String) : PipelinePhase :=
  modelPreservingPipelinePhase "KeepSetFilter" fun prog => do
    let keepSet := Std.HashSet.ofList
      (procs ++ procs.map PrecondElim.wfProcName)
    let result := { prog with decls := prog.decls.filter fun d =>
      match d with
      | .proc p _ => keepSet.contains (CoreIdent.toPretty p.header.name)
      | _ => true }
    return (true, result)

/-- The Core verification pipeline phases. Each entry pairs a program
    transformation with its per-obligation model validation. The pipeline
    extracts transforms from this list, and the validation extracts phases,
    ensuring they stay in sync.

    When `procs` and `factory` are provided (targeted verification), the
    pipeline includes filtering and precondition-elimination phases.
    All filter phases are model-preserving since they only remove
    information without introducing over-approximations.

    `loopElimPipelinePhase` is placed last because loop elimination happens
    during evaluation (not as a program-to-program pass), making it the
    closest phase to SMT. -/
def corePipelinePhases (procs : Option (List String) := none)
    (factory : Option (@Lambda.Factory CoreLParams) := none) : List PipelinePhase :=
  let filterPhases := match procs with
    | some ps => [filterProceduresPipelinePhase ps]
    | none => []
  let precondPhase := match factory with
    | some f => [precondElimPipelinePhase f]
    | none => []
  let keepSetPhase := match procs with
    | some ps => [keepSetFilterPipelinePhase ps]
    | none => []
  filterPhases ++ [callElimPipelinePhase] ++ precondPhase ++ keepSetPhase ++ [loopElimPipelinePhase]

/-- The abstracted phases derived from the Core pipeline phases. -/
def coreAbstractedPhases (procs : Option (List String) := none)
    (factory : Option (@Lambda.Factory CoreLParams) := none) : List AbstractedPhase :=
  (corePipelinePhases procs factory).map (·.phase)

/-- Build the solver log from raw results and phase validation logs. -/
private def buildSolverLog (satResult valResult : SMT.Result)
    (satisfiabilityCheck validityCheck : Bool)
    (satPhaseLog valPhaseLog : List SolverPhaseLog) : List SolverPhaseLog :=
  (if satisfiabilityCheck then [{ phase := "solver.sat", result := satResult }] else []) ++
  (if validityCheck then [{ phase := "solver.val", result := valResult }] else []) ++
  satPhaseLog ++ valPhaseLog

/-- Adjust an SMT result through pipeline phase validation. A `.sat` result
    may be demoted to `.unknown` if a phase cannot validate the model, and
    an `.unknown` result may be promoted back to `.sat` if a phase can
    validate the model. Returns the adjusted result and a log of
    intermediate results per phase. -/
def SMT.Result.adjustForPhases (r : SMT.Result)
    (phases : List AbstractedPhase)
    (obligation : ProofObligation Expression) : SMT.Result × List SolverPhaseLog :=
  match r with
  | .sat _ | .unknown _ => AbstractedPhase.validateModel phases r obligation
  | other => (other, [])

/--
Invoke a backend engine and get the analysis result for a
given proof obligation.
-/
def getObligationResult (assumptionTerms : List Term) (obligationTerm : Term)
    (ctx : SMT.Context)
    (obligation : ProofObligation Expression) (p : Program)
    (options : VerifyOptions) (counter : IO.Ref Nat)
    (tempDir : System.FilePath) (satisfiabilityCheck validityCheck : Bool)
    (phases : List AbstractedPhase)
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
    -- Convert unvalidated sat results to unknown when phases require validation
    let (adjSat, satPhaseLog) := satResult.adjustForPhases phases obligation
    let (adjVal, valPhaseLog) := validityResult.adjustForPhases phases obligation
    -- Build solver log: raw solver results followed by phase validation logs
    let smtLog := buildSolverLog satResult validityResult
      satisfiabilityCheck validityCheck satPhaseLog valPhaseLog
    let rawOutcome : VCOutcome := {
      satisfiabilityProperty := adjSat,
      validityProperty := adjVal,
      solverLog := smtLog }
    let outcome := maskOutcome rawOutcome satisfiabilityCheck validityCheck
    -- Extract model from sat results (using raw solver results)
    let model := match satResult, validityResult with
      | .sat m, _ => convertModel m (SMT.Context.getConstructorNames ctx)
      | _, .sat m => convertModel m (SMT.Context.getConstructorNames ctx)
      | _, _ => []
    let result := { obligation,
                    outcome := .ok outcome,
                    estate,
                    verbose := options.verbose,
                    checkLevel := options.checkLevel,
                    checkMode := options.checkMode,
                    lexprModel := model }
    return result

def verifySingleEnv (pE : Program × Env) (options : VerifyOptions)
    (counter : IO.Ref Nat) (tempDir : System.FilePath)
    (axiomCache : Option IrrelevantAxioms.Cache := .none)
    (externalPhases : List AbstractedPhase := [])
    (corePhases : List AbstractedPhase := coreAbstractedPhases) :
    EIO DiagnosticModel VCResults := do
  let (p, E) := pE
  let profile := options.profile
  match E.error with
  | some err =>
    .error <| DiagnosticModel.fromFormat s!"🚨 Error during evaluation!\n\
              {format err}\n\n\
              [DEBUG] Evaluated program: {Core.formatProgram p}\n\n"
  | _ =>
    let mut results := (#[] : VCResults)
    let mut preprocessNs : Nat := 0
    let mut smtEncodeNs : Nat := 0
    let mut solverNs : Nat := 0
    let mut peResolvedCount : Nat := 0
    for obligation in E.deferred do
      -- Determine which checks to perform based on metadata or check mode/amount
      let (satisfiabilityCheck, validityCheck) :=
        if Imperative.MetaData.hasFullCheck obligation.metadata then
          (true, true)  -- fullCheck annotation: always run both
        else
          -- Derive checks from check mode and level
          match options.checkMode, options.checkLevel, obligation.property with
          | _, .full, _ => (true, true)  -- Full: both checks
          | .bugFindingAssumingCompleteSpec, _, _ => (true, true)  -- This mode requires both checks
          | .deductive, .minimal, .assert | .deductive, .minimal, .divisionByZero => (false, true)  -- Deductive needs validity
          | .deductive, .minimalVerbose, .assert | .deductive, .minimalVerbose, .divisionByZero => (false, true)  -- Same checks as minimal
          | .deductive, .minimal, .cover => (true, false)   -- Cover uses satisfiability
          | .deductive, .minimalVerbose, .cover => (true, false)   -- Same checks as minimal
          | .bugFinding, .minimal, .assert | .bugFinding, .minimal, .divisionByZero => (true, false) -- Bug finding needs satisfiability
          | .bugFinding, .minimalVerbose, .assert | .bugFinding, .minimalVerbose, .divisionByZero => (true, false) -- Same checks as minimal
          | .bugFinding, .minimal, .cover => (true, false)  -- Cover uses satisfiability
          | .bugFinding, .minimalVerbose, .cover => (true, false)  -- Same checks as minimal
      let t0 ← IO.monoNanosNow
      let (obligation, peSatResult?, peValResult?) ← preprocessObligation obligation p options satisfiabilityCheck validityCheck axiomCache
      let t1 ← IO.monoNanosNow
      preprocessNs := preprocessNs + (t1 - t0)
      -- If PE resolved both checks, we're done, unless we always want to generate SMT queries
      if not options.alwaysGenerateSMT then
        if let (some peSat, some peVal) := (peSatResult?, peValResult?) then
          let phases := externalPhases ++ corePhases
          let (adjPeSat, satPhaseLog) := peSat.adjustForPhases phases obligation
          let (adjPeVal, valPhaseLog) := peVal.adjustForPhases phases obligation
          let peLog := buildSolverLog peSat peVal
            satisfiabilityCheck validityCheck satPhaseLog valPhaseLog
          let outcome : VCOutcome := {
            satisfiabilityProperty := adjPeSat,
            validityProperty := adjPeVal,
            solverLog := peLog }
          let result : VCResult := { obligation, outcome := .ok outcome, verbose := options.verbose,
                                      checkLevel := options.checkLevel, checkMode := options.checkMode, lexprModel := [] }
          results := results.push result
          peResolvedCount := peResolvedCount + 1
          if result.isFailure || result.isImplementationError then
            if options.verbose >= .normal then
              let prog := f!"\n\n[DEBUG] Evaluated program:\n{Core.formatProgram p}"
              dbg_trace f!"\n\nResult: {result}\n{prog}"
            if options.stopOnFirstError then break
          continue
      -- Need the solver for at least one check
      let needSatCheck := satisfiabilityCheck && peSatResult?.isNone
      let needValCheck := validityCheck && peValResult?.isNone
      let t2 ← IO.monoNanosNow
      let maybeTerms := ProofObligation.toSMTTerms E obligation { SMT.Context.default with uniqueBoundNames := options.uniqueBoundNames } options.useArrayTheory
      let t3 ← IO.monoNanosNow
      smtEncodeNs := smtEncodeNs + (t3 - t2)
      match maybeTerms with
      | .error err =>
        let err := f!"SMT Encoding Error! " ++ err
        let result := { obligation,
                        outcome := .error (toString err),
                        verbose := options.verbose,
                        checkLevel := options.checkLevel,
                        checkMode := options.checkMode,
                        lexprModel := [] }
        if options.verbose >= .normal then
          let prog := f!"\n\n[DEBUG] Evaluated program:\n{Core.formatProgram p}"
          dbg_trace f!"\n\nResult: {result}\n{prog}"
        results := results.push result
        if options.stopOnFirstError then break
      | .ok (assumptionTerms, obligationTerm, ctx) =>
        let t4 ← IO.monoNanosNow
        let result ← getObligationResult assumptionTerms obligationTerm ctx obligation p options
                      counter tempDir needSatCheck needValCheck (externalPhases ++ corePhases)
        let t5 ← IO.monoNanosNow
        solverNs := solverNs + (t5 - t4)
        -- Merge PE results with solver results
        let result := match result.outcome with
          | .ok solverOutcome =>
            let satResult := peSatResult?.getD solverOutcome.satisfiabilityProperty
            let valResult := peValResult?.getD solverOutcome.validityProperty
            { result with outcome := .ok { solverOutcome with
                satisfiabilityProperty := satResult,
                validityProperty := valResult } }
          | .error _ => result
        results := results.push result
        if result.isNotSuccess then
          if options.verbose >= .normal then
            let prog := f!"\n\n[DEBUG] Evaluated program:\n{Core.formatProgram p}"
            dbg_trace f!"\n\nResult: {result}\n{prog}"
          if options.stopOnFirstError then break
    if profile then
      let _ ← (IO.println s!"[profile]     Preprocess obligations: {nsToMs preprocessNs}ms" |>.toBaseIO)
      let _ ← (IO.println s!"[profile]     SMT encoding: {nsToMs smtEncodeNs}ms" |>.toBaseIO)
      let _ ← (IO.println s!"[profile]     Solver/file writing: {nsToMs solverNs}ms" |>.toBaseIO)
      let _ ← (IO.println s!"[profile]     Obligations: {E.deferred.size} total, {peResolvedCount} resolved by PE" |>.toBaseIO)
    return results

/-- Run the Strata Core verification pipeline on a program: transform,
type-check, partially evaluate, and discharge proof obligations via SMT.
All program-wide transformations that occur before any analyses
(including type inference) should be placed here. -/
def verify (program : Program)
    (tempDir : System.FilePath)
    (proceduresToVerify : Option (List String) := none)
    (options : VerifyOptions := VerifyOptions.default)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default)
    (externalPhases : List AbstractedPhase := [])
    : EIO DiagnosticModel VCResults := do
  let profile := options.profile
  let factory ← EIO.ofExcept (Core.Factory.addFactory moreFns)
  let phases := coreAbstractedPhases (procs := proceduresToVerify) (factory := some factory)
  let finalProgram ← profileStep profile "  Program transformations" do
    let runPrecondElim := fun prog => do
      let (_changed, prog) ← PrecondElim.precondElim prog factory
      return prog
    match proceduresToVerify with
    | none =>
      match Transform.run program runPrecondElim with
      | .ok prog => .ok prog
      | .error e => .error (DiagnosticModel.fromFormat f!"❌ Transform Error. {e}")
    | some procs =>
       -- Verify specific procedures. All pipeline phases — including
       -- filtering, call/loop elimination, precondition elimination, and
       -- the final keep-set filter — are defined in `corePipelinePhases`.
       -- Each phase pairs its transform with its model validation,
       -- ensuring they stay in sync.
      let pipelinePhases := corePipelinePhases (procs := some procs) (factory := some factory)
      let passes := fun prog => do
        let mut current := prog
        for pp in pipelinePhases do
          let (_changed, next) ← pp.transform current
          current := next
        return current
      let res := Transform.run program passes
      match res with
      | .ok prog => .ok prog
      | .error e => .error (DiagnosticModel.fromFormat f!"❌ Transform Error. {e}")
  -- Build the axiom relevance cache once (post-transform, so declarations are
  -- stable). The cache is reused across all verification environments and goals.
  let axiomCache? ← profileStep profile "  Build axiom relevance cache" do
    pure (if options.removeIrrelevantAxioms == .Off then .none
          else .some (IrrelevantAxioms.Cache.build finalProgram))
  let pEs ← profileStep profile "  Type check and partial eval" do
    match Core.typeCheckAndPartialEval options finalProgram moreFns with
    | .error err =>
      .error { err with message := s!"❌ Type checking error.\n{err.message}" }
    | .ok pEs => .ok pEs
  let counter ← IO.toEIO (fun e => DiagnosticModel.fromFormat f!"{e}") (IO.mkRef 0)
  let VCss ← profileStep profile "  VC discharge" do
    if options.checkOnly then
      pure []
    else
      (List.mapM (fun pE => verifySingleEnv pE options counter tempDir axiomCache? externalPhases phases) pEs)
  .ok VCss.toArray.flatten

end -- public section
end Core
---------------------------------------------------------------------

namespace Strata

open Lean.Parser
open Strata (DiagnosticModel FileRange)

public section

def typeCheck (ictx : InputContext) (env : Program) (options : Core.VerifyOptions := Core.VerifyOptions.default)
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

/-- Front-end phase: any translation from a source language to Core may
    introduce over-approximations. Until front-ends can validate models or
    determine that an assertion is unaffected, all sat results are converted
    to unknown. -/
def frontEndPhase : Core.AbstractedPhase where
  name := "FrontEnd"
  getValidation _ := .modelToValidate (fun _ => /- TODO -/ false)

def verify
    (env : Program)
    (ictx : InputContext := Inhabited.default)
    (proceduresToVerify : Option (List String) := none)
    (options : Core.VerifyOptions := Core.VerifyOptions.default)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default)
    (externalPhases : List Core.AbstractedPhase := [])
    : IO Core.VCResults := do
  let (program, errors) := Core.getProgram env ictx
  if errors.isEmpty then
    let runner tempDir :=
      EIO.toIO (fun dm => IO.Error.userError (toString (dm.format (some ictx.fileMap))))
                  (Core.verify program tempDir proceduresToVerify options moreFns
                    (externalPhases := externalPhases))
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
  | .error msg => some { fileRange, message := s!"analysis error: {msg}", type := DiagnosticType.StrataBug }
  | .ok outcome =>
    let message? : Option String :=
      if vcr.obligation.property == .cover then
        let description := vcr.obligation.metadata.getPropertySummary.getD "cover property"
        if outcome.isSatisfiable || outcome.passReachabilityUnknown then none
        else if outcome.unreachable then some s!"{description} is unreachable"
        else if outcome.isPass then none
        else some s!"{description} is not satisfiable"
      else
        let description := vcr.obligation.metadata.getPropertySummary.getD "assertion"
        if outcome.unreachable then some s!"{description} holds vacuously (path unreachable)"
        else if outcome.isPass || outcome.isSatisfiable || outcome.passReachabilityUnknown then none
        else if outcome.alwaysFalseAndReachable || outcome.canBeTrueOrFalseAndIsReachable || outcome.canBeFalseAndIsReachable then
          some s!"{description} does not hold"
        else some s!"{description} could not be proved"
    message?.map fun message => { fileRange, message, type := DiagnosticType.UserError }

structure Diagnostic where
  start : Lean.Position
  ending : Lean.Position
  message : String
  type : DiagnosticType
  deriving Repr, BEq

def DiagnosticModel.toDiagnostic (files: Map Strata.Uri Lean.FileMap) (dm: DiagnosticModel): Diagnostic :=
  let fileMap := (files.find? dm.fileRange.file).getD
    (dbg_trace s!"Could not find {repr dm.fileRange.file} in {repr files.keys} when converting model '{dm}' to a diagnostic"; default)
  let startPos := fileMap.toPosition dm.fileRange.range.start
  let endPos := fileMap.toPosition dm.fileRange.range.stop
  {
    start := { line := startPos.line, column := startPos.column }
    ending := { line := endPos.line, column := endPos.column }
    message := dm.message
    type := dm.type
  }

def Core.VCResult.toDiagnostic (files: Map Strata.Uri Lean.FileMap) (vcr : Core.VCResult) : Option Diagnostic := do
  let modelOption := toDiagnosticModel vcr
  modelOption.map (fun dm => dm.toDiagnostic files)

end -- public section
end Strata

---------------------------------------------------------------------
