/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Pipeline.Messages
public import Strata.Transform.CoreTransform
public import Strata.DL.Imperative.SMTUtils
public import Strata.Languages.Core.DDMTransform.ASTtoCST
public import Strata.Languages.Core.ProgramFactProps
public import Strata.Languages.Core.ProgramFactSetProps

/-! # Pipeline Phase Definitions for Model Validation

This module defines the types used to describe how verification pipeline
phases affect model soundness. Individual transform passes define their
own pipeline phases using these types, ensuring that the soundness
annotation lives next to the transform implementation. -/

namespace Core
open Imperative Lambda

public section

/-- Describes whether a pipeline phase preserves models or requires validation. -/
inductive ModelValidation where
  /-- The phase preserves models — sat results are sound. -/
  | modelPreserving
  /-- The phase may introduce spurious models. The function returns true
      when the model is valid. -/
  | modelToValidate (validate : Imperative.SMT.Model Expression.Ident → Bool)

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
  /-- Given an obligation label, return a human-readable description for
      diagnostics (e.g. "precondition 'nat'"). Returns `none` when the
      label does not belong to this phase. -/
  getAssertDescription : String → Option String := fun _ => none

/-- True when any label in the obligation's path conditions starts with the
    given string, indicating the obligation went through that transform. -/
def obligationHasLabelPrefix (obligation : ProofObligation Expression)
    (pfx : String) : Bool :=
  obligation.assumptions.any fun pc =>
    pc.any fun entry => entry.name.startsWith pfx

/-! ## Proof obligations, deferred

A phase's `establishes` and `preserves` are claims about the program its
transform produces, and `establishes_ok` and `preserves_ok` state that those
claims hold. Proving one relates a transform to a `Prop` about its output; no
production transform has such a proof yet, so contracts are checked for
*composition* while the facts themselves are declared. -/

/-- Require every phase to prove every fact it claims, whatever its own
    `PipelinePhase.provesContract` says.

    Temporary: it exists only because `true` is not yet reachable. Once
    every phase discharges its obligations, this switch and the
    `PhaseContractObligation` guard it feeds go away and the obligations become
    ordinary fields. -/
@[expose] def proveAllPhaseContracts : Bool := false

/-- A claim a phase makes about its output program: the claim itself when a
    proof is owed — `proveAllPhaseContracts` or the phase's own
    `provesContract` is `true` — and `True` otherwise.

    Guarding the obligation rather than omitting it keeps the statement
    written down and checked for well-formedness, and makes turning a phase
    from declared to proved a one-word edit. -/
@[expose] def PhaseContractObligation (provesContract : Bool) (P : Prop) : Prop :=
  if proveAllPhaseContracts || provesContract then P else True

/-- When neither the global switch nor the phase's own `provesContract` flag is
    set, the obligation is trivially satisfied. -/
theorem PhaseContractObligation.deferred {b : Bool} {P : Prop}
    (h : (proveAllPhaseContracts || b) = false) : PhaseContractObligation b P := by
  simp [PhaseContractObligation, h]

/-- An obligation that *is* owed, from a proof of the claim itself. Also
    accepted where nothing is owed, so a phase that proves its contract need
    not know which switch turned the obligation on. -/
theorem PhaseContractObligation.intro {b : Bool} {P : Prop} (h : P) : PhaseContractObligation b P := by
  unfold PhaseContractObligation; split
  · exact h
  · trivial

/-- Close a contract obligation that nobody owes yet. Fails when the phase sets
    `provesContract := true`, or when `proveAllPhaseContracts` is `true`,
    which is the point: the proof is then owed here. -/
macro "deferred_contract" : tactic =>
  `(tactic| first
      | exact PhaseContractObligation.deferred (by decide)
      | fail "this phase's contract is owed a proof, because it sets \
              `provesContract := true` or `proveAllPhaseContracts` is `true`. \
              Prove the claim and wrap it in `PhaseContractObligation.intro`.")

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

/-- A verification pipeline phase: a program transformation, its model
    validation, and its phase contract (empty by default). -/
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
  /-- Facts that must hold on the input program for this phase to run. -/
  requires    : ProgramFactSet := factSet![]
  /-- Facts guaranteed to hold on the output program. -/
  establishes : ProgramFactSet := factSet![]
  /-- Facts that, if they held on the input, also hold on the output. -/
  preserves   : ProgramFactSet := factSet![]
  /-- Whether this phase's `establishes` and `preserves` are backed by
      proofs rather than declared. Setting it to `true` demands
      `establishes_ok` and `preserves_ok` from this phase alone, so proofs
      can arrive one transform at a time. -/
  provesContract : Bool := false
  /-- Every fact in `establishes` holds on the output. Vacuously true
      when `establishes` is `factSet![]`. The shape is "any successful run
      of the transform produces a program on which every asserted fact
      holds." `s'` is the final state; `b` is the changed-flag returned
      by the transform. -/
  establishes_ok : PhaseContractObligation provesContract
      (∀ (p : Program) (s : Transform.CoreTransformState)
        (b : Bool) (p' : Program) (s' : Transform.CoreTransformState),
        (transform p).run s = (.ok (b, p'), s') →
        establishes.holds p') := by deferred_contract
  /-- Every preserved fact really is preserved when it held on the
      input. Vacuously true when `preserves` is `factSet![]`. -/
  preserves_ok : PhaseContractObligation provesContract
      (∀ (f : ProgramFact), f ∈ preserves →
      ∀ (p : Program) (s : Transform.CoreTransformState),
        f.holds p →
      ∀ (b : Bool) (p' : Program) (s' : Transform.CoreTransformState),
        (transform p).run s = (.ok (b, p'), s') →
        f.holds p') := by deferred_contract

/-- A model-preserving pipeline phase: the transform is applied but it
    cannot introduce spurious models (e.g. it only removes information). -/
def modelPreservingPipelinePhase (name : String)
    (t : Program → Transform.CoreTransformM (Bool × Program))
    (requires establishes preserves : ProgramFactSet := factSet![]) : PipelinePhase where
  transform := t
  phase.name := name
  phase.getValidation _ := .modelPreserving
  requires := requires
  establishes := establishes
  preserves := preserves

/-- Returns the program unchanged when `c` accepts it. -/
def assertFact (c : Program → Bool) (msg : String) (p : Program) :
    Transform.CoreTransformM (Bool × Program) :=
  if c p then pure (false, p) else throw (Strata.Message.fromFormat f!"{msg}")

/-- A successful `assertFact` returns the program it was given, and the check
    it ran accepted that program. -/
private theorem assertFact_run {c : Program → Bool} {msg : String} {p : Program}
    {s : Transform.CoreTransformState} {b : Bool} {p' : Program}
    {s' : Transform.CoreTransformState}
    (h : (assertFact c msg p).run s = (.ok (b, p'), s')) : p' = p ∧ c p = true := by
  unfold assertFact at h
  split at h
  · rename_i hf
    refine ⟨?_, hf⟩
    simp [ExceptT.run, ExceptT.pure, ExceptT.mk, StateT.pure, Pure.pure] at h
    injection h with hok _
    injection hok with hbp
    injection hbp with _ hp'
    exact hp'.symm
  · simp [ExceptT.run, throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure,
      StateT.pure] at h
    injection h with he _
    simp at he

/-- A phase that establishes `f` by running an executable check for it, so a
    fact no transform produces can still enter a pipeline honestly: a program
    the check rejects is named instead of reaching a downstream phase that
    would quietly do nothing.

    `hc` witnesses that `f` has a check, so a fact whose meaning nothing
    decides cannot be asserted — though it can still be required, established
    or preserved. Returning the program unchanged is what discharges both
    obligations and what makes `preserves` `ProgramFactSet.all`. -/
def assertFactPhase (name : String) (f : ProgramFact) (msg : String)
    (hc : f.check?.isSome = true := by decide) : PipelinePhase where
  transform := assertFact (f.check?.get hc) msg
  phase.name := name
  establishes := ProgramFactSet.ofList [f]
  preserves := ProgramFactSet.all
  provesContract := true
  establishes_ok := PhaseContractObligation.intro (by
    intro p s b p' s' hrun g hg
    obtain ⟨rfl, hf⟩ := assertFact_run hrun
    have hg' : g = f := by
      simpa [ProgramFactSet.ofList] using ProgramFactSet.mem_ofList.mp hg
    subst hg'
    exact (ProgramFact.holds_iff_check_get hc _).mpr hf)
  preserves_ok := PhaseContractObligation.intro (by
    intro _ _ p s hp b p' s' hrun
    obtain ⟨rfl, _⟩ := assertFact_run hrun
    exact hp)

/-- Rejects a program with a CFG procedure body, which every statement-level
    transform and symbolic evaluation need ruled out. -/
def assertNoCFGBodiesPhase : PipelinePhase :=
  assertFactPhase "assertNoCFGBodies" .noCFGBodies
    "❌ Expected every procedure body to be structured, but at least one is a CFG."

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
abbrev ValidatedPipeline (requires : ProgramFactSet) :=
  Strata.Pipeline.ValidatedPipeline PipelinePhase ProgramFact requires

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
      parent directory if needed. -/
def runTransforms (p : Program) (phases : List PipelinePhase)
    (initState : Transform.CoreTransformState := .emp)
    (pipelineCtx : Option Strata.Pipeline.PipelineContext := none)
    (keepAllFilesPrefix : Option String := none)
    : EIO Transform.Err (Program × Transform.CoreTransformState) := do
  let initState := { initState with currentProgram := .some p }
  if let some pfx := keepAllFilesPrefix then
    if let some parent := (System.FilePath.mk pfx).parent then
      IO.toEIO (fun e => Strata.Message.fromFormat f!"{e}")
        (IO.FS.createDirAll parent)
  let mut current := p
  let mut state := initState
  let mut step := 0
  have : Inhabited (Except Transform.Err Program × Transform.CoreTransformState) :=
    ⟨(.error default, Transform.CoreTransformState.emp)⟩
  for pp in phases do
    let runPhase : Unit → Except Transform.Err Program × Transform.CoreTransformState :=
      fun () =>
        Transform.runWith current (fun prog => do
          let (_, next) ← pp.transform prog
          return next) state
    let (result, newState) ← match pipelineCtx with
      | some pctx => pctx.withRepeatedPhasePure pp.phase.name runPhase
      | none => pure (runPhase ())
    match result with
    | .ok next =>
      current := next
      state := newState
      step := step + 1
      if let some pfx := keepAllFilesPrefix then
        let path := s!"{pfx}.{step}.{pp.phase.name}.core.st"
        IO.toEIO (fun e => Strata.Message.fromFormat f!"{e}")
          (IO.FS.writeFile path (toString current ++ "\n"))
    | .error e => throw e
  pure (current, state)

end -- public section

end Core
