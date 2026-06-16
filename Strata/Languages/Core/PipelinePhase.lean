/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.CoreTransform
public import Strata.DL.Imperative.SMTUtils
public import Strata.Languages.Core.DDMTransform.ASTtoCST

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
  /-- Human-readable name identifying this phase in solver logs. -/
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

/-- Registry of obligation-label families whose VCs are universally
    quantified over a spec-pinned domain. A sat counterexample to such
    an obligation is genuine regardless of havoc/inlining/translation,
    so the abstracting phases need not validate the model. -/
def universalVCRegistry : List ((String → Bool) × String) :=
  [ (fun lbl => lbl.startsWith "arbitrary_iter_maintain_invariant",
      "loop-invariant maintenance — LoopElim havoc-and-assert(I)")
  , (fun lbl => lbl.startsWith "entry_invariant",
      "loop-invariant entry — LoopElim assert(I) at loop top")
  , (fun lbl => lbl.startsWith "measure_lb",
      "termination measure ≥ 0 — LoopElim")
  , (fun lbl => lbl.startsWith "measure_decrease",
      "termination measure decreases — LoopElim, C_Simp")
  , (fun lbl => (lbl.splitOn ":postcondition").length > 1,
      "callee postcondition — LaurelToCoreTranslator")
  , (fun lbl => lbl.startsWith "callElimAssert_",
      "call-site precondition — CallElim asserts callee.requires")
  ]

def obligationLabelIsUniversal (obligation : ProofObligation Expression) : Bool :=
  universalVCRegistry.any fun (m, _) => m obligation.label

/-- A verification pipeline phase that pairs a program transformation with
    its model validation. This coupling ensures that adding a new transform
    also requires specifying its soundness annotation, and vice versa. -/
structure PipelinePhase where
  /-- The program-to-program transformation. -/
  transform : Program → Transform.CoreTransformM (Bool × Program)
  /-- The model validation for this phase. -/
  phase : AbstractedPhase

/-- A model-preserving pipeline phase: the transform is applied but it
    cannot introduce spurious models (e.g. it only removes information). -/
def modelPreservingPipelinePhase (name : String)
    (t : Program → Transform.CoreTransformM (Bool × Program)) : PipelinePhase where
  transform := t
  phase.name := name
  phase.getValidation _ := .modelPreserving

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
  if let some pfx := keepAllFilesPrefix then
    if let some parent := (System.FilePath.mk pfx).parent then
      IO.toEIO (fun e => Strata.DiagnosticModel.fromFormat f!"{e}")
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
        IO.toEIO (fun e => Strata.DiagnosticModel.fromFormat f!"{e}")
          (IO.FS.writeFile path (toString current ++ "\n"))
    | .error e => throw e
  pure (current, state)

end -- public section

end Core
