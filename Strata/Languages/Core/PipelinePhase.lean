/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Pipeline.Messages
public import Strata.Transform.CoreTransform
public import Strata.DL.Imperative.SMTUtils
public import Strata.DL.Imperative.Counterexample.Run
public import Strata.DL.Imperative.Counterexample.BackLink
public import Strata.Languages.Core.Counterexample.RunTarget
public import Strata.Languages.Core.DDMTransform.ASTtoCST
public import Strata.Languages.Core.ProgramFactProps
public import Strata.Languages.Core.ProgramFactSetProps
public import Strata.Languages.Core.ProcedureUnit
public import Strata.Languages.Core.Interpreter
public import Strata.Util.DecidableEqProps

/-! # Pipeline Phase Definitions for Model Validation

This module defines the types used to describe how verification pipeline
phases affect model soundness. Individual transform passes define their
own pipeline phases using these types, ensuring that the soundness
annotation lives next to the transform implementation.

The import of `Core.Interpreter` is public because the types of
`RuntimeBackLink`'s constructors mention `BackLink Expression Command Command`, whose
`InterpLang Expression` instance the interpreter provides, so that instance has to be
reachable wherever `RuntimeBackLink` is used. It therefore puts `Core.Env` in scope: a
consumer inside `namespace Core` writes `Imperative.Env` for the imperative execution
environment, since a bare `Env` there is `Core.Env`. -/

namespace Core
open Imperative Lambda

public section

/-- Describes whether a pipeline phase preserves models or requires validation. -/
inductive ModelValidation where
  /-- The phase preserves models — sat results are sound. -/
  | modelPreserving
  /-- The phase may introduce spurious models. The function returns the model to
      report when the model is valid (the model itself, or one the validation
      refined, such as with the values of a run it found), and `none` when it is not.
      `holds` says which query the model is of: the check holding (the
      satisfiability query, `P ∧ Q`) or failing (the validity query, `P ∧ ¬Q`). -/
  | modelToValidate (validate : (holds : Bool) → Imperative.SMT.Model Expression.Ident →
      Option (Imperative.SMT.Model Expression.Ident))
  /-- The obligation's path carries markers of the phase, each placed under the branch guards
      `guards` lists for it (`markerGuards`; an empty list for a marker on every path). A model
      can reach a marker unless it falsifies one of the marker's guards; a `sat` result whose
      model can reach one of the markers is not sound. A model that reaches none of them is
      passed through, never promoted. -/
  | markersOnPath (guards : List (List Expression.Expr))

/-- A phase in the verification pipeline. Each phase determines per-obligation
    whether its models need validation, based on whether the obligation is
    in the path of something abstracted by this phase. -/
structure AbstractedPhase where
  /-- Canonical name of this phase. Used in solver logs, telemetry,
      `--keep-all-files` filenames, and as the phase's user-facing name in
      the `transform` command's `--pass` flag. By convention camelCase,
      e.g. `loopElim`. -/
  name : String
  /-- Given an obligation, determine the model validation for this phase. -/
  getValidation : ProofObligation Expression → ModelValidation := fun _ => .modelPreserving
  /-- A validation that also reads the program the phase was given, for a phase that
      checks a model against that program (by replaying it, say). When the pipeline
      records the phase's input (`runTransformsRecording`), the verifier uses it in place
      of `getValidation` (`AbstractedPhase.onInput`); `getValidation` serves the callers
      that do not record inputs. -/
  getValidationOn : Option (Program → ProofObligation Expression → ModelValidation) := none
  /-- The phase, when it changes the program, may abstract some code without a
      labelled assumption on its paths (call elimination, whose call to a callee without
      postconditions is a bare `havoc`). A later phase's `getValidationOn` would run that
      abstraction as if it were the program, so after such a phase has changed the
      program `runTransformsRecording` records no input, and the later phase validates
      with `getValidation`. -/
  leavesUnmarkedAbstractions : Bool := false
  /-- The label prefixes of the assumptions `getValidation` looks for
      (`obligationHasLabelPrefix`), for a phase that rebuilds obligations and must
      keep those labels on their paths (the passive VC phase). -/
  validationPrefixes : List String := []
  /-- Given an obligation label, return a human-readable description for
      diagnostics (e.g. "precondition 'nat'"). Returns `none` when the
      label does not belong to this phase. -/
  getAssertDescription : String → Option String := fun _ => none

/-- The phase, validating models against `input`, the program it was given, when it has
    such a validation (`getValidationOn`). -/
def AbstractedPhase.onInput (p : AbstractedPhase) (input : Program) : AbstractedPhase :=
  match p.getValidationOn with
  | some f => { p with getValidation := f input }
  | none => p

/-- True when the label of an assumption in the obligation's path conditions
    starts with the given string, indicating the obligation went through that
    transform. Only assumptions are read: a marker is an assumption, while the
    names of variable declarations and `distinct` facts come from the program. -/
def obligationHasLabelPrefix (obligation : ProofObligation Expression)
    (pfx : String) : Bool :=
  obligation.assumptions.any fun pc =>
    pc.any fun
      | .assumption l _ => l.startsWith pfx
      | _ => false

/-- The reach condition under which `--vcgen wp` keeps a marker whose condition is `true`, when
    `e` is that marker's condition as WP keeps it: `if c then true else ¬c`, `c` being the reach
    condition (`WP.kMarkImp`). `some []` for the condition `true`, and `none` for any other
    condition. Symbolic evaluation and symbolic execution never give a marker the first form:
    every leaf of their markers' conditions is `true`. -/
def markerGuards : Expression.Expr → Option (List Expression.Expr)
  | .ite _ c (.const _ (.boolConst true))
      (.ite _ c' (.const _ (.boolConst false)) (.const _ (.boolConst true))) =>
    if c == c' then some [c] else none
  | .const _ (.boolConst true) => some []
  | _ => none

/-- The model validation of an abstraction phase whose markers are the assumptions of the
    obligation's path condition with a label that starts with one of `pfxs`. Without such an
    assumption, `modelPreserving`. Otherwise `markersOnPath` with, for each, its branch guards
    (`markerGuards`) when its label starts with one of `guarded`, whose markers have the
    condition `true`, and no guards (the marker is on every path) for any other. -/
def markerValidation (obligation : ProofObligation Expression) (pfxs : List String)
    (guarded : List String := []) : ModelValidation :=
  let guards := obligation.assumptions.flatMap fun pc => pc.filterMap fun
    | .assumption l e =>
      if !pfxs.any (l.startsWith ·) then none
      else if guarded.any (l.startsWith ·) then some ((markerGuards e).getD [])
      else some []
    | _ => none
  if guards.isEmpty then .modelPreserving else .markersOnPath guards


/-- The label of the assumption a phase places on the path of an obligation whose
    models may be spurious: a phase whose output over-approximates what the
    solver's models can represent, so that a model of the output's query need not
    be one of the input. Like every name starting with `$__`, it cannot be written
    in a user's program. The SMT back end reports a satisfiable query for a marked
    obligation as unknown, not as a counterexample. -/
def spuriousModelsLabel : String := "$__spuriousModels"

/-- The metadata field that marks a lemma, an obligation of its own with no statement to
    place a marker before: a lemma's obligation carries the lemma's metadata, so the field
    marks that obligation alone. -/
@[match_pattern]
abbrev spuriousModelsField : Imperative.MetaDataElem.Field Expression := .label spuriousModelsLabel

/-- The assumption `assume [spuriousModelsLabel]: true` that marks an obligation
    whose models may be spurious; `e` is its `true`, carrying the marking phase's
    location. -/
def spuriousModelsMarker (e : Expression.Expr) : Statement :=
  Statement.assume spuriousModelsLabel e .empty

/-- The model validation of a phase that marks obligations with
    `spuriousModelsMarker`: a model of a marked obligation is reported as unknown,
    never as a counterexample; any other obligation is unaffected. -/
def spuriousModelsValidation (obligation : ProofObligation Expression) : ModelValidation :=
  let marked := obligationHasLabelPrefix obligation spuriousModelsLabel ||
    (obligation.metadata.findElem spuriousModelsField).isSome
  if marked then .modelToValidate (fun _ _ => none)
  else .modelPreserving

/-! ## Proof obligations

A phase's `establishes` and `preserves` are claims about the program its
transform produces, and `establishes_ok` and `preserves_ok` state that those
claims hold, for every claimed fact the phase does not list in `unproved`.
Proving one relates a transform to a `Prop` about its output. Every contract
is checked for *composition*, proved or not. -/

/-- Close a contract obligation that owes nothing: every fact the phase claims is
    in its `unproved` set, which is checked by `decide`. Fails as soon as a claimed
    fact is not in `unproved`, which is the point: its proof is then owed here. -/
macro "unproved_contract" : tactic =>
  `(tactic| first
      | (intro _ _ _ _ _ _ _ f _ hu
         exact absurd Strata.Pipeline.mem_allFactSet hu)
      | (intro f _ hu
         exact absurd Strata.Pipeline.mem_allFactSet hu)
      | (intro _ _ _ _ _ _ _ f hf hu; exact absurd ((by decide : _ ⊑ _) f hf) hu)
      | (intro f hf hu; exact absurd ((by decide : _ ⊑ _) f hf) hu)
      | fail "this phase claims a fact that is not in its `unproved` set, so its \
              contract is owed a proof of it: prove the claim, or, if it is true \
              but not yet proved, add it to `unproved` with the reason.")

/-! ## Pipeline phase

A `PipelinePhase` pairs a transformation with two claims about it: whether a
model found after the phase is still a model of the program before it, and
which facts the phase may rely on and which it delivers. The first governs
soundness of *sat* results, the second whether the composition is meaningful
at all.

Two conventions for writing a contract. Use `factSet![…]`, which checks at
elaboration time that the facts are canonically ordered; a phase-producing
function may compute its contract instead, and `ValidatedPipeline.ofList` checks
whatever it is handed. And write `preserves` out fact by fact rather than as
`ProgramFactSet.all`, so that adding a fact does not silently enlarge every
phase's claim — the exception is a phase that returns its input unchanged, where
`ProgramFactSet.all` is the honest answer. -/

/-! ## Pipeline composition: runtime carriers and reverse composition

`RuntimeBackLink`, `composeRuntimeBackLinks`, and `runTransformsWithBackLinks`
are the pipeline-specific half of the back-link layer: they accumulate one
carrier per executed phase and compose the carriers in reverse.  They are
distinct from the per-transformation back-link *implementations* (in
`Strata.Languages.Core.Counterexample.BackLinkPhases`) and from the generic back-link
*specification* and `composeBackLinks` (in `Strata.DL.Imperative.Counterexample.BackLink`). -/

/-- Runtime carrier of a phase's back-link: the back-link cannot be built at the
    transform boundary, because back-links bake in the target id and the procedure
    environment `π` — both known only per failed obligation, at counterexample-lift time.
    So the carrier holds a *deferred builder* `Target → Option String → π → BackLink`,
    instantiated once the target, the name of the obligation's procedure and `π` are
    known. -/
inductive RuntimeBackLink where
  /-- A linked phase.  `build` is the deferred back-link builder, instantiated at the
      phase's *upstream* target id and at `procBelow`, the name of the obligation's
      procedure in the phase's output, passed up by the phases downstream.
      `sourceUnit downstreamTarget procBelow` is the phase's input verification unit for
      the obligation (the statement list the back-link lifts at); a recorded phase keeps a
      non-empty supplied unit, and where the supplied unit is empty it lifts at the unit
      `Program.sourceUnitFor` picks in the phase's input and output programs.
      `upstreamTarget downstreamTarget procBelow` maps the phase's downstream target id to
      the id the same obligation has in the phase's input (identity except where a phase
      synthesizes the obligation, e.g. call elimination's precondition asserts). -/
  | linked (build : Target → Option String → (String → Option Procedure) →
      BackLink Expression Command Command)
      (sourceUnit : Target → Option String → List (Stmt Expression Command) := fun _ _ => [])
      (upstreamTarget : Target → Option String → Target := fun target _ => target)
  | unavailable (phase : String)

/-- The structured body of the procedure named `n`, if the declaration is that procedure
    with a structured body. -/
@[expose] def Decl.bodyNamed (n : String) : Decl → Option (List (Stmt Expression Command))
  | .proc procedure _ =>
    if procedure.header.name.1 == n then
      match procedure.body with
      | .structured statements _ => some statements
      | .cfg _ _ | .abstract => none
    else none
  | _ => none

/-- Does the program declare a procedure named `n`? -/
@[expose] def Program.hasProc (p : Program) (n : String) : Bool :=
  p.decls.any fun d => match d with
    | .proc q _ => q.header.name.1 == n
    | _ => false

/-- The unit (`WPObl.procPassive`: preconditions assumed, body, postconditions asserted)
    of the procedure named `n`, if the declaration is that procedure with a structured
    body. -/
@[expose] def Decl.unitNamed (n : String) : Decl → Option (List (Stmt Expression Command))
  | .proc procedure _ =>
    if procedure.header.name.1 == n then
      match procedure.body with
      | .structured statements _ => some (WPObl.procPassive procedure statements)
      | .cfg _ _ | .abstract => none
    else none
  | _ => none

/-- The unit of the procedure named `n` at a phase: its contract-wrapped body
    (`Decl.unitNamed`) in the phase's `input`; for a procedure the phase generated (absent
    from its input), its unit in the phase's `output` — the *derived unit* the phase
    built.  `[]` when there is no such structured
    body.  An obligation-program procedure has an empty contract, so its unit is its
    body. -/
@[expose] def Program.unitOf (input output : Program)
    (n : String) : List (Stmt Expression Command) :=
  if input.hasProc n then (input.decls.findSome? (Decl.unitNamed n)).getD []
  else (output.decls.findSome? (Decl.unitNamed n)).getD []

/-- A phase's input verification unit for the obligation `target`, with the name of
    its procedure.  The procedure is identified by name, passed up from downstream:
    `below` is the procedure the downstream phases lift at (at the bottom, the procedure
    the verifier extracted the obligation from), and every phase keeps the name of the
    procedure it transforms, so the unit is that procedure's (`Program.unitOf`: in the
    phase's `input`, or in its `output` for a procedure the phase generated).  A
    declaration check carries its derived unit. -/
def Program.sourceUnitFor (input output : Program) (target : Target)
    (below : Option String) : List (Stmt Expression Command) × Option String :=
  match target with
  | .declCheck id => (id.unit, below)
  | _ =>
    match below with
    | none => ([], none)
    | some name => (input.unitOf output name, some name)

/-- Record a phase's input/output programs in its carrier: a linked carrier keeps a
    non-empty unit the phase supplies, and lifts at the unit
    `Program.sourceUnitFor input output` picks where the supplied unit is empty. -/
def RuntimeBackLink.withPrograms (link : RuntimeBackLink) (input output : Program) :
    RuntimeBackLink :=
  match link with
  | .linked build su upstreamTarget =>
    .linked build (fun t below =>
      let u := su t below
      if u.isEmpty then (input.sourceUnitFor output t below).1 else u) upstreamTarget
  | .unavailable phase => .unavailable phase

/-- Lift the outcome `initial`, produced at the last phase's output, back through the
    phases' carriers `links` (in execution order): instantiate each deferred builder at the
    concrete `target`/`π` (from the failed obligation) and compose in reverse; once the
    outcome is empty, or a phase is unavailable, the result is the empty outcome.  The fold
    threads the target id: each linked phase is built at its upstream id
    `upstreamTarget t procName` and at `procName` (where `t` is the id at its output and
    `procName` the name of the obligation's procedure there) and lifts at its input unit
    `sourceUnit t procName`, as `composeBackLinks` gives each link its own input unit.  The
    fold passes `procName` up unchanged while the phases find a unit for it; above a phase
    with the empty unit it passes no name, since the name then names no procedure the
    phases above transform. -/
def composeRuntimeBackLinks (target : Target) (π : String → Option Procedure)
    (links : List RuntimeBackLink) (initial : BackLinkOutcome Expression Command)
    (procName : Option String := none) :
    BackLinkOutcome Expression Command :=
  (links.reverse.foldl (init := (initial, target, procName))
      fun (outcome, tgt, procName) runtimeLink =>
    match outcome with
    | ⟨[], none⟩ => (.empty, tgt, procName)
    | _ =>
      match runtimeLink with
      | .unavailable _ => (.empty, tgt, procName)
      | .linked build sourceUnit upstreamTarget =>
        let tgt' := upstreamTarget tgt procName
        let unit := sourceUnit tgt procName
        ((build tgt' procName π).lift unit outcome, tgt',
          if unit.isEmpty then none else procName)).1

/-- A verification pipeline phase: a program transformation, its model
    validation, and its phase contract (empty by default).

    A phase a caller may select by name must also be listed in `Core.nameablePhases`.
    One that is not there is deliberately not nameable — neither `--phases` nor a
    registered pipeline entry can refer to it. -/
structure PipelinePhase where
  /-- The program-to-program transformation.
    Returns false if the output Program is identical to the input Program
    and the CoreTransformState didn't modify the factory field.
    It can conservatively return true even if they were changed, to save
    comparison cost.
  -/
  transform : Program → Transform.CoreTransformM (Bool × Program)
  /-- The model validation for this phase. -/
  phase : AbstractedPhase
  /-- Build the runtime counterexample carrier from the exact input/output of this
      transform: a *deferred* back-link builder (the concrete link needs the
      per-obligation target id and `π`, supplied at lift time).  The default is
      `unavailable`: lifting stops at this phase. -/
  buildBackLink : Program → Program → RuntimeBackLink :=
    fun _ _ => .unavailable phase.name
  /-- Facts that must hold on the input program for this phase to run. -/
  requires    : ProgramFactSet := factSet![]
  /-- Facts guaranteed to hold on the output program. -/
  establishes : ProgramFactSet := factSet![]
  /-- Facts that, if they held on the input, also hold on the output. -/
  preserves   : ProgramFactSet := factSet![]
  /-- The facts of `establishes` and `preserves` whose proof this phase does not
      give. Each must be a claim believed true, with a comment saying why it is not
      proved yet: a claim found false is fixed or dropped, never listed here. By
      default every fact, so a phase owes no proof until it lists less. A test pins what
      each shipped phase leaves unproved, so proving a fact means updating that test too. -/
  unproved : ProgramFactSet := ProgramFactSet.all
  /-- Every fact in `establishes` that is not `unproved` holds on the output.
      The shape is "any successful run of the transform on a program meeting
      `requires` produces a program on which every such fact holds." `s'` is the
      final state; `b` is the changed-flag returned by the transform. The proof is
      relative to `requires`: the facts it assumes are those the pipeline's
      bookkeeping says hold, so it is as good as the claims of the phases before it. -/
  establishes_ok :
      ∀ (p : Program) (s : Transform.CoreTransformState)
        (b : Bool) (p' : Program) (s' : Transform.CoreTransformState),
        requires.holds p →
        (transform p).run s = (.ok (b, p'), s') →
        ∀ f ∈ establishes, f ∉ unproved → f.holds p' := by unproved_contract
  /-- Every fact in `preserves` that is not `unproved`, holding on an input meeting
      `requires`, holds on the output. -/
  preserves_ok :
      ∀ (f : ProgramFact), f ∈ preserves → f ∉ unproved →
      ∀ (p : Program) (s : Transform.CoreTransformState),
        requires.holds p → f.holds p →
      ∀ (b : Bool) (p' : Program) (s' : Transform.CoreTransformState),
        (transform p).run s = (.ok (b, p'), s') →
        f.holds p' := by unproved_contract

/-- A model-preserving pipeline phase: the transform is applied but it
    cannot introduce spurious models (e.g. it only removes information). -/
def modelPreservingPipelinePhase (name : String)
    (t : Program → Transform.CoreTransformM (Bool × Program))
    («requires» establishes preserves : ProgramFactSet := factSet![]) : PipelinePhase where
  transform := t
  phase.name := name
  phase.getValidation _ := .modelPreserving
  requires := requires
  establishes := establishes
  preserves := preserves

/-- The name of the `assert` phase for a fact: `assert` followed by the fact's
    name with its first letter capitalized, so `noCFGBodies` gives
    `assertNoCFGBodies`. -/
def ProgramFact.assertPhaseName (f : ProgramFact) : String :=
  "assert" ++ (match f.name.toList with
               | [] => ""
               | c :: rest => String.ofList (c.toUpper :: rest))

/-- What the `assert` phase for `f` reports about a program `f`'s check rejects. For
    `wellFormedCalls`, the first ill-formed call, located at the call; there is one,
    since that check is `(illFormedCalls p).isEmpty`. For `noCFGBodies`, the first
    procedure with a CFG body, located at its declaration. For `noLambdas`, the first
    lambda, located where it was written, with the remedy. For the other facts, a
    message naming what is expected. -/
private def assertFailure (f : ProgramFact) (p : Program) : Strata.Message :=
  let generic :=
    Strata.Message.fromFormat f!"❌ Expected {f.name}, but the program does not satisfy it."
  match f with
  | .wellFormedCalls => (illFormedCalls p).head?.getD generic
  | .noCFGBodies =>
    let cfgProc := p.decls.findSome? fun
      | .proc q md => if q.body.isCfg then some (q.header.name.name, md) else none
      | _ => none
    match cfgProc with
    | some (name, md) => md.toDiagnostic s!"❌ Expected every procedure body to be \
        structured, but found procedure {name} with a CFG body. To verify it, pass \
        --vcgen symexec (for an acyclic one) or --vcgen usp (or uwp)."
    | none => generic
  | .noLambdas =>
    match p.firstLiveLambda? with
    | some e =>
      let msg := f!"❌ Expected no lambda, since the verification back end has no term for \
        one, but found the lambda `{Program.showLambda e}`. Run `lambdaLift` before the back end."
      match (Lambda.LExpr.metadata e).uri with
      | some uri =>
        Strata.Message.withRange { file := uri, range := (Lambda.LExpr.metadata e).range } msg
      | none => Strata.Message.fromFormat msg
    | none => generic
  | _ => generic

/-- Returns the program unchanged when `f`'s check accepts it, and otherwise reports
    `assertFailure f`. -/
def assertFact (f : ProgramFact) (hc : f.check?.isSome = true) (p : Program) :
    Transform.CoreTransformM (Bool × Program) :=
  if f.check?.get hc p then pure (false, p) else throw (assertFailure f p)

/-- A successful `assertFact` returns the program it was given, and the check
    it ran accepted that program. -/
private theorem assertFact_run {f : ProgramFact} {hc : f.check?.isSome = true}
    {p : Program}
    {s : Transform.CoreTransformState} {b : Bool} {p' : Program}
    {s' : Transform.CoreTransformState}
    (h : (assertFact f hc p).run s = (.ok (b, p'), s')) :
    p' = p ∧ f.check?.get hc p = true := by
  unfold assertFact at h
  split at h
  · rename_i hf
    refine ⟨?_, hf⟩
    simp only [ExceptT.run, pure, ExceptT.pure, ExceptT.mk, StateT.pure] at h
    injection h with hok _
    injection hok with hbp
    injection hbp with _ hp'
    exact hp'.symm
  · simp only [ExceptT.run, throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, StateT.pure] at h
    injection h with he _
    simp at he

/-- A phase that establishes `f` by running an executable check for it, so a
    fact no transform produces can still enter a pipeline honestly: a program
    the check rejects is named instead of reaching a downstream phase that
    would quietly do nothing.

    `hc` witnesses that `f` has a check, so a fact whose meaning nothing
    decides cannot be asserted — though it can still be required, established
    or preserved. Returning the program unchanged is what discharges both
    obligations and what makes `preserves` `ProgramFactSet.all`. A program the
    check rejects is reported as in `assertFact`. The phase is named
    `f.assertPhaseName`. -/
def assertFactPhase (f : ProgramFact) (hc : f.check?.isSome = true := by decide) :
    PipelinePhase where
  transform := assertFact f hc
  phase.name := f.assertPhaseName
  buildBackLink := fun _ _ => .linked (fun _tgt _n _π => {
    name := f.assertPhaseName
    lift := fun _st outcome => outcome })
  establishes := ProgramFactSet.ofList [f]
  preserves := ProgramFactSet.all
  unproved := ProgramFactSet.empty
  establishes_ok := by
    intro p s b p' s' _ hrun g hg _
    obtain ⟨rfl, hf⟩ := assertFact_run hrun
    have hg' : g = f := by
      simpa [ProgramFactSet.ofList] using ProgramFactSet.mem_ofList.mp hg
    subst hg'
    exact (ProgramFact.holds_iff_check_get hc _).mpr hf
  preserves_ok := by
    intro _ _ _ p s _ hp b p' s' hrun
    obtain ⟨rfl, _⟩ := assertFact_run hrun
    exact hp

/-- The phase that checks `f` on the program and passes it through. A fact with no
    executable check has no such phase, and `by decide` refuses it where it is written:
    `ProgramFact.assertPhase .typeAnnotated` does not compile, since confirming
    annotations are present would not establish that they are right. -/
def ProgramFact.assertPhase (f : ProgramFact) (hc : f.check?.isSome = true := by decide) :
    PipelinePhase :=
  assertFactPhase f hc

/-! ## Validated pipelines

A `ValidatedPipeline` is a pipeline known to be well-formed: every phase's
`requires` is satisfied by the facts accumulated from earlier phases. The type,
the checker and its diagnostics are language-neutral and live in
`Strata/Pipeline/PhaseContract.lean`; what belongs here is the instance saying
where a Core phase keeps its contract, and Core-side names for the results. -/

/-- A Core pipeline phase is a phase in the language-neutral sense: it has a name
    and a contract. Everything else about it — the transform, the monad, the model
    validation, the proof obligations — is Core's business and stays out of the
    checker. -/
instance : Strata.Pipeline.PhaseContract PipelinePhase ProgramFact where
  name p := p.phase.name
  requires p := p.requires
  establishes p := p.establishes
  preserves p := p.preserves

/-- A pipeline validated to compose correctly, indexed by the facts it expects at
    entry. -/
abbrev ValidatedPipeline (pre : ProgramFactSet) :=
  Strata.Pipeline.ValidatedPipeline PipelinePhase ProgramFact pre

/-- Validate a dynamically assembled phase list against the facts known to hold
    on entry. -/
abbrev ValidatedPipeline.ofListFrom (σ : ProgramFactSet) (phases : List PipelinePhase) :
    Except String (ValidatedPipeline σ) :=
  Strata.Pipeline.ValidatedPipeline.ofListFrom σ phases

/-- Validate a phase list that assumes nothing about its input program. This is
    the entry point for runtime-assembled pipelines; use
    `ValidatedPipeline.phases` to hand the result to `runTransforms`. -/
abbrev ValidatedPipeline.ofList (phases : List PipelinePhase) :
    Except String (ValidatedPipeline ProgramFactSet.empty) :=
  Strata.Pipeline.ValidatedPipeline.ofList phases

/-- Validate `phases`, and that what they establish covers what the analysis
    consuming the program needs of it. The consumer hands on no program, so it is
    not modelled as a phase; it is reported through the same diagnostic. -/
abbrev ValidatedPipeline.ofListDelivering (consumer : String) (needed : ProgramFactSet)
    (phases : List PipelinePhase) : Except String (ValidatedPipeline ProgramFactSet.empty) :=
  Strata.Pipeline.ValidatedPipeline.ofListDelivering consumer needed phases

/-- Validate `phases` against facts assumed to hold on entry, and that what they
    establish covers what `consumer` needs. The result is indexed by `σ₀`, so the
    entry facts become part of the pipeline's type. -/
abbrev ValidatedPipeline.ofListFromDelivering (σ₀ : ProgramFactSet) (consumer : String)
    (needed : ProgramFactSet) (phases : List PipelinePhase) :
    Except String (ValidatedPipeline σ₀) :=
  Strata.Pipeline.ValidatedPipeline.ofListFromDelivering σ₀ consumer needed phases

/-- The facts `p` needs that `σ` does not supply. Empty exactly when
    `p.requires ⊑ σ`; see `missingRequires_eq_nil_iff`. -/
@[expose] def PipelinePhase.missingRequires (p : PipelinePhase) (σ : ProgramFactSet) :
    List ProgramFact :=
  Strata.Pipeline.missingFacts p.requires σ


/-- Run a chain of pipeline phases on a Core program. All phases share a
    single `CoreTransformState`, so fresh variable counters accumulate across
    phases and cached analyses (e.g., call graphs) can be reused. Returns the
    transformed program together with the final transform state (statistics,
    cached analyses, etc.).

    Optional knobs:
    * `initState` — initial transform state. Use this to inject a pre-built
      `Lambda.Factory`.
    * `pipelineCtx` — when provided, each phase is wrapped in
      `withRepeatedPhasePure` for telemetry.
    * `keepAllFilesPrefix` — when provided, the program after each phase is
      written to `{prefix}.{n}.{phaseName}.core.st` (1-indexed). Creates the
      parent directory if needed.

    Also returns the input of each phase that validates models against its input
    (`AbstractedPhase.getValidationOn`), by position in `phases`, unless an earlier
    phase changed the program and may leave abstractions unmarked
    (`AbstractedPhase.leavesUnmarkedAbstractions`).

    `recordLinks` says whether the run builds the counterexample back-link carrier of each
    executed phase (`PipelinePhase.buildBackLink`). A carrier keeps its phase's input and output
    programs alive until the run returns, so a run whose links are not used passes `false`, and
    the returned list of carriers is then empty. -/
def runTransformsRecording (recordLinks : Bool) (p : Program) (phases : List PipelinePhase)
    (initState : Transform.CoreTransformState := .emp)
    (pipelineCtx : Option Strata.Pipeline.PipelineContext := none)
    (keepAllFilesPrefix : Option String := none)
    : EIO Transform.Err
        (Program × Transform.CoreTransformState × List RuntimeBackLink × List (Nat × Program)) := do
  let initState := { initState with currentProgram := .some p }
  if let some pfx := keepAllFilesPrefix then
    if let some parent := (System.FilePath.mk pfx).parent then
      IO.toEIO (fun e => Strata.Message.fromFormat f!"{e}")
        (IO.FS.createDirAll parent)
  let mut current := p
  let mut state := initState
  let mut links : List RuntimeBackLink := []
  let mut step := 0
  let mut inputs : Array (Nat × Program) := #[]
  let mut unmarked := false
  have : Inhabited (Except Transform.Err (Bool × Program) × Transform.CoreTransformState) :=
    ⟨(.error default, Transform.CoreTransformState.emp)⟩
  for (pp, i) in phases.zipIdx do
    if pp.phase.getValidationOn.isSome && !unmarked then
      inputs := inputs.push (i, current)
    let runPhase : Unit → Except Transform.Err (Bool × Program) × Transform.CoreTransformState :=
      fun () => Transform.runWith current pp.transform state
    let (result, newState) ← match pipelineCtx with
      | some pctx => pctx.withRepeatedPhasePure pp.phase.name runPhase
      | none => pure (runPhase ())
    match result with
    | .ok (changed, next) =>
      unmarked := unmarked || (changed && pp.phase.leavesUnmarkedAbstractions)
      if recordLinks then
        links := links ++ [(pp.buildBackLink current next).withPrograms current next]
      current := next
      state := newState
      step := step + 1
      if let some pfx := keepAllFilesPrefix then
        let path := s!"{pfx}.{step}.{pp.phase.name}.core.st"
        IO.toEIO (fun e => Strata.Message.fromFormat f!"{e}")
          (IO.FS.writeFile path (toString current ++ "\n"))
    | .error e => throw e
  pure (current, state, links, inputs.toList)

/-- `runTransformsRecording` with the counterexample back-link carrier of every executed phase
    recorded, one per phase in order, without the recorded inputs. -/
def runTransformsWithBackLinks (p : Program) (phases : List PipelinePhase)
    (initState : Transform.CoreTransformState := .emp)
    (pipelineCtx : Option Strata.Pipeline.PipelineContext := none)
    (keepAllFilesPrefix : Option String := none)
    : EIO Transform.Err
        (Program × Transform.CoreTransformState × List RuntimeBackLink) := do
  let (program, state, links, _) ← runTransformsRecording true p phases initState pipelineCtx
    keepAllFilesPrefix
  pure (program, state, links)

/-- `runTransformsRecording` building no counterexample back-link carrier, without the recorded
    inputs. -/
def runTransforms (p : Program) (phases : List PipelinePhase)
    (initState : Transform.CoreTransformState := .emp)
    (pipelineCtx : Option Strata.Pipeline.PipelineContext := none)
    (keepAllFilesPrefix : Option String := none) :
    EIO Transform.Err (Program × Transform.CoreTransformState) := do
  let (program, state, _, _) ← runTransformsRecording false p phases initState pipelineCtx
    keepAllFilesPrefix
  pure (program, state)

/-- `phase` turns `p` into `p'`, from transform state `s` to state `s'`. -/
@[expose] def PipelinePhase.Runs (phase : PipelinePhase)
    (s : Transform.CoreTransformState) (p : Program)
    (s' : Transform.CoreTransformState) (p' : Program) : Prop :=
  ∃ changed, (phase.transform p).run.run s = (.ok (changed, p'), s')

/-- `phase` produces `p'` from `p`, from some transformation state. -/
@[expose] def PipelinePhase.Transforms (phase : PipelinePhase) (p p' : Program) :
    Prop :=
  ∃ s changed s', (phase.transform p).run.run s = (.ok (changed, p'), s')

end -- public section

end Core
