/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.Transform.Specification
public import Strata.DL.Imperative.Logic.HoareTemplate
public import Strata.DL.Imperative.Analysis.DefinitionsProps
public import Strata.DL.Imperative.Logic.TerminationProps
import all Strata.Transform.Specification
import all Strata.DL.Imperative.Logic.HoareTemplate
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.CmdSemanticsProps
import all Strata.DL.Imperative.StmtSemanticsProps
import Strata.Util.ListUtilsProps

/-! # Soundness Specification — Theorems

This module contains the theorems associated with the definitions in
`Strata.Transform.Specification`. See that file's module docstring for the
overall structure of the soundness-specification framework.

## Key results

Connecting the two assertion-validity formulations and the transform specs.
The Hoare-logic definitions and structural rules themselves live in
`Strata.DL.Imperative.Logic.HoareTemplate`; event-trace Hoare transport across
trace overapproximations lives in `Strata.Transform.SpecHoareConnection`:

- `sound_assertValid` / `sound_allAsserts` — `Sound` transports
  `AssertValidOnTracesWhen` and `AllAssertsValidOnTracesWhen`.

Canonical event-trace overapproximation properties:

- `OverapproximatesTraces.id` — identity transformation for a reflexive trace
  relation.
- `OverapproximatesTraces.rel_comp` — compose stages with different trace
  relations, producing their relational composition `RComp`.
- `overapproximatesTraces_assertValid` / `overapproximatesTraces_allAsserts` —
  transport per-identifier or whole-trace assertion validity when the trace
  relation reflects the corresponding predicate.
- `overapproximatesTracesUptoWhen_assertValid` — the per-identifier transport for
  equal initial environments and any relation between final environments.
- `OverapproximatesTracesUptoWhen.comp_trans_eq` — shared-start composition with
  stage-specific trace relations and a transitive output-state relation.
- `OverapproximatesTracesUptoWhen.mono_trace` — trace-relation weakening (`Rtrace
  ⊆ Rtrace'`), covariant.  Collapses the `RComp R R` that `comp_trans_eq` produces
  for two stages sharing a transitive trace relation `R` back to the single `R`.
- `overapproximatesTraces_stmts` — lift per-statement trace overapproximation to
  statement lists when the trace relation relates `[]` and respects append.
- `OverapproximatesTracesUptoWhen.runsOverapproximate` — trace overapproximation
  is overapproximation of runs up to the same trace relation, which carries
  deductive-verification verdicts back to the source when the relation reflects
  validity.
- `OverapproximatesTracesUptoWhen.terminatesAt` — a finishing source run has a
  finishing target run with related final environment and trace.
- `Analysis.ValidOnTracesVerifier.of_overapproximatesTraces` /
  `Analysis.ValidOnTracesVerifier.of_overapproximatesTracesUptoWhen` — a
  verifier sound for the target, after a trace-overapproximating transformation
  whose trace relation reflects assertion validity, is sound for the source;
  `Analysis.ValidOnTracesVerifier.runTransforms_of_overapproximatesTraces` and
  `Analysis.ValidOnTracesVerifier.runTransforms_of_overapproximatesTracesUpto`
  lift this to a pipeline of phases.

Properties of the `EnvStoreAgree` output relation (defined in `Specification`):

- `EnvStoreAgree_trans` — transitivity, used to chain per-pass instances.
- `envStoreAgree_of_extendsWith` — forget classified target-only bindings to
  weaken `Env.ExtendsWith` into the common `EnvStoreAgree` output relation.
-/

public section

namespace Imperative

namespace Specification

open Strata.Logic Imperative.Logic

variable {P : PureExpr} [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P] [HasSubstFvar P]
    [HasInt P] [HasIntOps P]

namespace Transform

/-! ## Connection between `Sound` and trace-native assertion validity -/

section Connection
omit [HasOps P] [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasSubstFvar P]

/-- Composing two sound transformations yields a sound composite under the same
condition interpretation. -/
theorem sound_comp (I : ConditionInterp P)
    (L₁ L₂ L₃ : EventLang P (Event P))
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    (h₁ : Sound I L₁ L₂ T₁ params₁ params₂)
    (h₂ : Sound I L₂ L₃ T₂ params₂ params₃) :
    Sound I L₁ L₃ (fun s => T₁ s >>= T₂) params₁ params₃ := by
  intro s s'' a hrun hvalid
  simp only [bind, Option.bind] at hrun
  match h1 : T₁ s with
  | some s' => rw [h1] at hrun; exact h₁ s s' a h1 (h₂ s' s'' a hrun hvalid)
  | none => rw [h1] at hrun; exact absurd hrun (by nofun)

/-- If `T` maps `s` to `s'`, soundness transports trace-native validity of an
assertion identifier from `s'` back to `s`. -/
theorem sound_assertValid (I : ConditionInterp P)
    (L₁ L₂ : EventLang P (Event P))
    (T : L₁.StmtT → Option L₂.StmtT) (a : AssertId P)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (s : L₁.StmtT) (s' : L₂.StmtT)
    (ht : T s = some s') (hsound : Sound I L₁ L₂ T params₁ params₂)
    (hvalid : AssertValidOnTracesWhen L₂ I
      (L₂.initEnvWF params₂ s') s' a) :
    AssertValidOnTracesWhen L₁ I (L₁.initEnvWF params₁ s) s a :=
  hsound s s' a ht hvalid

/-- A sound transformation transports whole-trace validity of every assertion
from the target statement back to the source statement. -/
theorem sound_allAsserts (I : ConditionInterp P)
    (L₁ L₂ : EventLang P (Event P))
    (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (s : L₁.StmtT) (s' : L₂.StmtT) (ht : T s = some s')
    (hsound : Sound I L₁ L₂ T params₁ params₂)
    (hvalid : AllAssertsValidOnTracesWhen L₂ I
      (L₂.initEnvWF params₂ s') s') :
    AllAssertsValidOnTracesWhen L₁ I
      (L₁.initEnvWF params₁ s) s := by
  intro ρ₀ cfg trace hinit htrace
  apply Trace.AssertionsValid.of_all_assertionValid I
  intro aid
  have ha := hsound s s' aid ht (fun ρ₀' cfg' trace' hinit' htrace' =>
    Trace.AssertionValid.of_assertionsValid I aid
      (hvalid ρ₀' cfg' trace' hinit' htrace'))
  exact ha ρ₀ cfg trace hinit htrace

/-- The identity transformation is sound for every event language and condition
interpretation. -/
theorem sound_id (I : ConditionInterp P) (L : EventLang P (Event P))
    (params : L.InitEnvWFParamsTy) : Sound I L L some params params := by
  intro s s' a ht hvalid; simp only [Option.some.injEq] at ht; subst ht; exact hvalid

end Connection



/-! ## Properties of the trace-overapproximation family -/

omit [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P]
  [HasSubstFvar P] [HasInt P] [HasIntOps P] in
/-- Identity transformation trace-overapproximates itself for any reflexive
trace relation. -/
theorem OverapproximatesTraces.id
    {EventT : Type _}
    (Rtrace : Relation (List EventT)) (hrefl : IsReflexive Rtrace)
    (L : EventLang P EventT) (params : L.InitEnvWFParamsTy) :
    OverapproximatesTraces Rtrace L L some params params := by
  intro st st' ht _ ρ₀ ρ₀' heq hinit
  simp only [Option.some.injEq] at ht
  subst ht
  subst heq
  refine ⟨?_, ?_, ?_, hinit⟩
  · intro cfg trace htrace
    exact ⟨cfg, trace, htrace, hrefl trace⟩
  · intro ρ' trace htrace
    exact ⟨ρ', trace, htrace, rfl, hrefl trace⟩
  · intro lbl ρ' trace htrace
    exact ⟨ρ', trace, htrace, rfl, hrefl trace⟩

omit [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P]
  [HasSubstFvar P] [HasInt P] [HasIntOps P] in
/-- Explicit trace-relation overapproximations compose by relational
composition of their trace relations. -/
theorem OverapproximatesTraces.rel_comp
    {EventT : Type _}
    (R₁ R₂ : Relation (List EventT))
    (L₁ L₂ L₃ : EventLang P EventT)
    (T₁ : L₁.StmtT → Option L₂.StmtT)
    (T₂ : L₂.StmtT → Option L₃.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy)
    (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    (h₁ : OverapproximatesTraces R₁ L₁ L₂ T₁ params₁ params₂)
    (h₂ : OverapproximatesTraces R₂ L₂ L₃ T₂ params₂ params₃) :
    OverapproximatesTraces (RComp R₁ R₂)
      L₁ L₃ (fun s => T₁ s >>= T₂) params₁ params₃ := by
  intro st st'' ht _ ρ₀ ρ₀' heq hinit
  subst heq
  simp only [bind, Option.bind] at ht
  match hmid : T₁ st with
  | none => simp [hmid] at ht
  | some st' =>
    rw [hmid] at ht
    have hr₁ := h₁ st st' hmid trivial ρ₀ ρ₀ rfl hinit
    have hr₂ := h₂ st' st'' ht trivial ρ₀ ρ₀ rfl hr₁.2.2.2
    refine ⟨?_, ?_, ?_, hr₂.2.2.2⟩
    · intro cfg trace htrace
      obtain ⟨cfg₁, trace₁, htrace₁, hrel₁⟩ := hr₁.1 cfg trace htrace
      obtain ⟨cfg₂, trace₂, htrace₂, hrel₂⟩ := hr₂.1 cfg₁ trace₁ htrace₁
      exact ⟨cfg₂, trace₂, htrace₂, ⟨trace₁, hrel₁, hrel₂⟩⟩
    · intro ρ' trace htrace
      obtain ⟨ρ₁, trace₁, htrace₁, henv₁, hrel₁⟩ := hr₁.2.1 ρ' trace htrace
      obtain ⟨ρ₂, trace₂, htrace₂, henv₂, hrel₂⟩ := hr₂.2.1 ρ₁ trace₁ htrace₁
      exact ⟨ρ₂, trace₂, htrace₂, henv₁.trans henv₂,
        ⟨trace₁, hrel₁, hrel₂⟩⟩
    · intro lbl ρ' trace htrace
      obtain ⟨ρ₁, trace₁, htrace₁, henv₁, hrel₁⟩ := hr₁.2.2.1 lbl ρ' trace htrace
      obtain ⟨ρ₂, trace₂, htrace₂, henv₂, hrel₂⟩ := hr₂.2.2.1 lbl ρ₁ trace₁ htrace₁
      exact ⟨ρ₂, trace₂, htrace₂, henv₁.trans henv₂,
        ⟨trace₁, hrel₁, hrel₂⟩⟩

omit [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P]
  [HasSubstFvar P] [HasInt P] [HasIntOps P] in
/-- A trace overapproximation with equal initial environments and any relation `Rout` between
final environments transports validity of one assertion identifier when its trace relation
reflects that validity. -/
theorem overapproximatesTracesUptoWhen_assertValid
    (I : ConditionInterp P) (Rtrace : Relation (Trace P)) (Rout : Relation (Env P))
    (L₁ L₂ : EventLang P (Event P)) (T : L₁.StmtT → Option L₂.StmtT)
    (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (hreflect : ∀ trace trace', Rtrace trace trace' → ∀ aid,
      Trace.AssertionValid P I aid trace' → Trace.AssertionValid P I aid trace)
    (hover : OverapproximatesTracesUptoWhen Rtrace (· = ·) Rout L₁ L₂ T pre params₁ params₂)
    {st : L₁.StmtT} {st' : L₂.StmtT} {aid : AssertId P}
    (ht : T st = some st') (hpre : pre st)
    (hvalid : AssertValidOnTracesWhen L₂ I
      (L₂.initEnvWF params₂ st') st' aid) :
    AssertValidOnTracesWhen L₁ I (L₁.initEnvWF params₁ st) st aid := by
  intro ρ₀ cfg trace hinit htrace
  have hr := hover st st' ht hpre ρ₀ ρ₀ rfl hinit
  obtain ⟨cfg', trace', htrace', hrel⟩ := hr.1 cfg trace htrace
  exact hreflect trace trace' hrel aid
    (hvalid ρ₀ cfg' trace' hr.2.2.2 htrace')

omit [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P]
  [HasSubstFvar P] [HasInt P] [HasIntOps P] in
/-- A trace overapproximation transports validity of one assertion identifier
when its trace relation reflects that validity. -/
theorem overapproximatesTraces_assertValid
    (I : ConditionInterp P) (Rtrace : Relation (Trace P))
    (L₁ L₂ : EventLang P (Event P)) (T : L₁.StmtT → Option L₂.StmtT)
    (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (hreflect : ∀ trace trace', Rtrace trace trace' → ∀ aid,
      Trace.AssertionValid P I aid trace' → Trace.AssertionValid P I aid trace)
    (hover : OverapproximatesTracesWhen Rtrace L₁ L₂ T pre params₁ params₂)
    {st : L₁.StmtT} {st' : L₂.StmtT} {aid : AssertId P}
    (ht : T st = some st') (hpre : pre st)
    (hvalid : AssertValidOnTracesWhen L₂ I
      (L₂.initEnvWF params₂ st') st' aid) :
    AssertValidOnTracesWhen L₁ I (L₁.initEnvWF params₁ st) st aid :=
  overapproximatesTracesUptoWhen_assertValid I Rtrace (· = ·) L₁ L₂ T pre params₁ params₂
    hreflect hover ht hpre hvalid

omit [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P]
  [HasSubstFvar P] [HasInt P] [HasIntOps P] in
/-- A trace overapproximation transports all-assert validity when its trace
relation reflects `Trace.AssertionsValid`. -/
theorem overapproximatesTraces_allAsserts
    (I : ConditionInterp P) (Rtrace : Relation (Trace P))
    (L₁ L₂ : EventLang P (Event P)) (T : L₁.StmtT → Option L₂.StmtT)
    (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (hreflect : ∀ trace trace', Rtrace trace trace' →
      Trace.AssertionsValid P I trace' → Trace.AssertionsValid P I trace)
    (hover : OverapproximatesTracesWhen Rtrace L₁ L₂ T pre params₁ params₂)
    {st : L₁.StmtT} {st' : L₂.StmtT}
    (ht : T st = some st') (hpre : pre st)
    (hvalid : AllAssertsValidOnTracesWhen L₂ I
      (L₂.initEnvWF params₂ st') st') :
    AllAssertsValidOnTracesWhen L₁ I
      (L₁.initEnvWF params₁ st) st := by
  intro ρ₀ cfg trace hinit htrace
  have hr := hover st st' ht hpre ρ₀ ρ₀ rfl hinit
  obtain ⟨cfg', trace', htrace', hrel⟩ := hr.1 cfg trace htrace
  exact hreflect trace trace' hrel
    (hvalid ρ₀ cfg' trace' hr.2.2.2 htrace')

omit [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P]
  [HasSubstFvar P] [HasInt P] [HasIntOps P] in
/-- Shared-start composition for trace overapproximations with potentially
different trace relations and a transitive outcome relation. -/
theorem OverapproximatesTracesUptoWhen.comp_trans_eq
    {EventT : Type _}
    (Rtrace₁ Rtrace₂ : Relation (List EventT)) (Rout : Relation (Env P))
    (houtTrans : IsTransitive Rout)
    (L₁ L₂ L₃ : EventLang P EventT)
    (T₁ : L₁.StmtT → Option L₂.StmtT)
    (T₂ : L₂.StmtT → Option L₃.StmtT)
    {pre₁ : L₁.StmtT → Prop} {pre₂ : L₂.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    (hpre : ∀ st st', T₁ st = some st' → pre₁ st → pre₂ st')
    (h₁ : OverapproximatesTracesUptoWhen Rtrace₁ (· = ·) Rout
      L₁ L₂ T₁ pre₁ params₁ params₂)
    (h₂ : OverapproximatesTracesUptoWhen Rtrace₂ (· = ·) Rout
      L₂ L₃ T₂ pre₂ params₂ params₃) :
    OverapproximatesTracesUptoWhen (RComp Rtrace₁ Rtrace₂) (· = ·) Rout
      L₁ L₃ (fun s => T₁ s >>= T₂) pre₁ params₁ params₃ := by
  intro st st'' ht hpre₁ ρ₀ ρ₀' heq hinit
  subst ρ₀'
  simp only [bind, Option.bind] at ht
  match hT₁ : T₁ st with
  | none => rw [hT₁] at ht; exact absurd ht (by nofun)
  | some st' =>
    rw [hT₁] at ht
    have hr₁ := h₁ st st' hT₁ hpre₁ ρ₀ ρ₀ rfl hinit
    have hr₂ := h₂ st' st'' ht (hpre st st' hT₁ hpre₁) ρ₀ ρ₀ rfl hr₁.2.2.2
    refine ⟨?_, ?_, ?_, hr₂.2.2.2⟩
    · intro cfg trace hrun
      obtain ⟨cfg₁, trace₁, hrun₁, hrel₁⟩ := hr₁.1 cfg trace hrun
      obtain ⟨cfg₂, trace₂, hrun₂, hrel₂⟩ := hr₂.1 cfg₁ trace₁ hrun₁
      exact ⟨cfg₂, trace₂, hrun₂, ⟨trace₁, hrel₁, hrel₂⟩⟩
    · intro ρ' trace hrun
      obtain ⟨ρ₁, trace₁, hrun₁, hout₁, hrel₁⟩ := hr₁.2.1 ρ' trace hrun
      obtain ⟨ρ₂, trace₂, hrun₂, hout₂, hrel₂⟩ := hr₂.2.1 ρ₁ trace₁ hrun₁
      exact ⟨ρ₂, trace₂, hrun₂, houtTrans _ _ _ hout₁ hout₂,
        ⟨trace₁, hrel₁, hrel₂⟩⟩
    · intro lbl ρ' trace hrun
      obtain ⟨ρ₁, trace₁, hrun₁, hout₁, hrel₁⟩ := hr₁.2.2.1 lbl ρ' trace hrun
      obtain ⟨ρ₂, trace₂, hrun₂, hout₂, hrel₂⟩ := hr₂.2.2.1 lbl ρ₁ trace₁ hrun₁
      exact ⟨ρ₂, trace₂, hrun₂, houtTrans _ _ _ hout₁ hout₂,
        ⟨trace₁, hrel₁, hrel₂⟩⟩

omit [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P]
  [HasSubstFvar P] [HasInt P] [HasIntOps P] in
/-- Trace-relation weakening.  `Rtrace` occurs only covariantly in
`OverapproximatesTracesUptoWhen` (it is the guarantee on the matched target
trace), so replacing it by any coarser relation `Rtrace'` (with `Rtrace ⊆
Rtrace'`) preserves the overapproximation. -/
theorem OverapproximatesTracesUptoWhen.mono_trace
    {EventT : Type _}
    {Rtrace Rtrace' : Relation (List EventT)} {Rin Rout : Relation (Env P)}
    {L₁ L₂ : EventLang P EventT} {T : L₁.StmtT → Option L₂.StmtT}
    {pre : L₁.StmtT → Prop}
    {params₁ : L₁.InitEnvWFParamsTy} {params₂ : L₂.InitEnvWFParamsTy}
    (hsub : ∀ t t', Rtrace t t' → Rtrace' t t')
    (h : OverapproximatesTracesUptoWhen Rtrace Rin Rout L₁ L₂ T pre params₁ params₂) :
    OverapproximatesTracesUptoWhen Rtrace' Rin Rout L₁ L₂ T pre params₁ params₂ := by
  intro st st' ht hpre ρ₀ ρ₀' hin hinit
  obtain ⟨hprefix, hterm, hexit, hwf⟩ := h st st' ht hpre ρ₀ ρ₀' hin hinit
  refine ⟨?_, ?_, ?_, hwf⟩
  · intro cfg trace hrun
    obtain ⟨cfg', trace', hrun', hrel⟩ := hprefix cfg trace hrun
    exact ⟨cfg', trace', hrun', hsub _ _ hrel⟩
  · intro ρ' trace hrun
    obtain ⟨ρ'', trace', hrun', hout, hrel⟩ := hterm ρ' trace hrun
    exact ⟨ρ'', trace', hrun', hout, hsub _ _ hrel⟩
  · intro lbl ρ' trace hrun
    obtain ⟨ρ'', trace', hrun', hout, hrel⟩ := hexit lbl ρ' trace hrun
    exact ⟨ρ'', trace', hrun', hout, hsub _ _ hrel⟩

/-- `EnvStoreAgree` is transitive: store agreement composes across a middle
environment. -/
theorem EnvStoreAgree_trans {P : PureExpr} {ρ₁ ρ₂ ρ₃ : Env P}
    (h₁ : EnvStoreAgree ρ₁ ρ₂) (h₂ : EnvStoreAgree ρ₂ ρ₃) :
    EnvStoreAgree ρ₁ ρ₃ :=
  StoreAgreement.trans h₁ h₂

/-- `Env.ExtendsWith` weakens to `EnvStoreAgree`: a classified environment
extension preserves store agreement on source-defined names, forgetting the
target-only register classification and factory equality.
This output-relation weakening allows composition across stages that use
different environment relations. -/
theorem envStoreAgree_of_extendsWith {P : PureExpr} {Extra : P.Ident → Prop}
    {ρ ρ' : Env P} (h : Env.ExtendsWith Extra ρ ρ') : EnvStoreAgree ρ ρ' :=
  h.2.toStoreAgreement


/-! ## Event-trace statement-list overapproximation

`overapproximatesTraces_stmts` lifts a per-statement `OverapproximatesTraces` on
`EventLang.imperativeE` to a block-level one on `EventLang.imperativeBlockE`.
It simulates arbitrary finite prefixes (for safety properties) in addition to
terminal and exiting runs.

The lift is stated against explicit, minimal laws on the trace relation
`Rtrace`: it must relate empty traces (`hnil`) and be compatible with
chronological concatenation (`happend`). Both hold for equality `(· = ·)`. -/

section TracedStructuredStmts

variable {CmdT : Type} {EventT : Type _}
    (evalCmdE : EvalCmdParamE P CmdT EventT)


omit [HasOps P] in
/-- Simulates completed runs after mapping a transform over a statement list.
Assuming `Rtrace` relates empty traces and is closed under chronological
concatenation, `Inv` holds initially and is preserved by every terminating
source statement, and `Inv` establishes the source well-formedness gate used by
the per-statement overapproximation, every terminal or exiting run of `ss` has
a run of the transformed list with the same environment and exit label and an
`Rtrace`-related trace. -/
private theorem overapproximatesTraces_stmts_aux
    (Rtrace : Relation (List EventT))
    (hnil : Rtrace [] [])
    (happend : ∀ a a' b b', Rtrace a a' → Rtrace b b' → Rtrace (a ++ b) (a' ++ b'))
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    {SParams : Type}
    (swf : SParams → Stmt P CmdT → Env P → Prop)
    (sp₁ sp₂ : SParams)
    (Inv : Env P → Prop)
    (hPres : ∀ {s : Stmt P CmdT} {ρ ρ' : Env P} {tr : List EventT}, Inv ρ →
       StepStmtStarE P evalCmdE (.stmt s ρ) tr (.terminal ρ') → Inv ρ')
    (hGate : ∀ {s : Stmt P CmdT} {ρ : Env P}, Inv ρ → swf sp₁ s ρ)
    (hsem : OverapproximatesTraces Rtrace
      (EventLang.imperativeE P CmdT evalCmdE SParams swf)
      (EventLang.imperativeE P CmdT evalCmdE SParams swf) T sp₁ sp₂)
    (ss : List (Stmt P CmdT)) :
    ∀ (ss' : List (Stmt P CmdT)), ss.mapM T = some ss' →
      ∀ (ρ₀ ρ' : Env P) (tr : List EventT), Inv ρ₀ →
        (StepStmtStarE P evalCmdE (.stmts ss ρ₀) tr (.terminal ρ') →
          ∃ tr', StepStmtStarE P evalCmdE (.stmts ss' ρ₀) tr' (.terminal ρ') ∧
            Rtrace tr tr')
        ∧
        (∀ lbl, StepStmtStarE P evalCmdE (.stmts ss ρ₀) tr (.exiting lbl ρ') →
          ∃ tr', StepStmtStarE P evalCmdE (.stmts ss' ρ₀) tr' (.exiting lbl ρ') ∧
            Rtrace tr tr') := by
  induction ss with
  | nil =>
    intro ss' hmap ρ₀ ρ' tr _
    have hss' : ss' = [] := by simpa [List.mapM_nil] using hmap
    subst hss'
    refine ⟨?_, ?_⟩
    · intro hstar
      obtain ⟨htr, hcfg⟩ := stmts_nil_runE evalCmdE hstar
      subst htr
      cases hcfg with
      | inl h => simp at h
      | inr h =>
        injection h with hρ; subst hρ
        refine ⟨[], ?_, hnil⟩
        exact ReflTransTrace.step (r := StepStmtE P evalCmdE) _ _ _ _ _
          .step_stmts_nil (.refl _)
    · intro lbl hstar
      obtain ⟨_, hcfg⟩ := stmts_nil_runE evalCmdE hstar
      cases hcfg with
      | inl h => simp at h
      | inr h => simp at h
  | cons s rest ih =>
    intro ss' hmap ρ₀ ρ' tr hwf
    obtain ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    have hsem_s := hsem s s' hs trivial ρ₀ ρ₀ rfl (hGate hwf)
    refine ⟨?_, ?_⟩
    · intro hstar
      rcases stmts_cons_headE evalCmdE hstar with ⟨hcfg, _⟩ | hseq
      · simp at hcfg
      · obtain ⟨ρ₁, tr₁, tr₂, htr, hterm_s, hterm_rest⟩ :=
          seq_reaches_terminalE evalCmdE hseq
        obtain ⟨ρ₁', trh, hrun_s', heqρ, hrelh⟩ := hsem_s.2.1 ρ₁ tr₁ hterm_s
        subst heqρ
        have hwf₁ := hPres hwf hterm_s
        obtain ⟨trt, hrun_rest', hrelt⟩ := (ih rest' hrm ρ₁ ρ' tr₂ hwf₁).1 hterm_rest
        refine ⟨trh ++ trt, ?_, ?_⟩
        · exact ReflTransTrace.trans _
            (stmts_cons_stepE evalCmdE s' rest' ρ₀ ρ₁ hrun_s') hrun_rest'
        · rw [htr]; exact happend tr₁ trh tr₂ trt hrelh hrelt
    · intro lbl hstar
      rcases stmts_cons_headE evalCmdE hstar with ⟨hcfg, _⟩ | hseq
      · simp at hcfg
      · rcases seq_reaches_exitingE evalCmdE hseq with
          hexit_s | ⟨ρ₁, tr₁, tr₂, htr, hterm_s, hexit_rest⟩
        · obtain ⟨ρ'', trh, hrun_s', heqρ, hrelh⟩ := hsem_s.2.2.1 lbl ρ' tr hexit_s
          subst heqρ
          refine ⟨trh, ?_, hrelh⟩
          have hchain :
            StepStmtStarE P evalCmdE (.stmts (s' :: rest') ρ₀)
              (([] ++ trh) ++ ([] ++ [])) (.exiting lbl ρ') :=
            ReflTransTrace.trans _
              (ReflTransTrace.step _ _ _ _ _ .step_stmts_cons
                (seq_inner_starE evalCmdE hrun_s'))
              (ReflTransTrace.step (r := StepStmtE P evalCmdE) _ _ _ _ _ .step_seq_exit (.refl _))
          simpa using hchain
        · obtain ⟨ρ₁', trh, hrun_s', heqρ, hrelh⟩ := hsem_s.2.1 ρ₁ tr₁ hterm_s
          subst heqρ
          have hwf₁ := hPres hwf hterm_s
          obtain ⟨trt, hrun_rest', hrelt⟩ := (ih rest' hrm ρ₁ ρ' tr₂ hwf₁).2 lbl hexit_rest
          refine ⟨trh ++ trt, ?_, ?_⟩
          · exact ReflTransTrace.trans _
              (stmts_cons_stepE evalCmdE s' rest' ρ₀ ρ₁ hrun_s') hrun_rest'
          · rw [htr]; exact happend tr₁ trh tr₂ trt hrelh hrelt

omit [HasOps P] in
/-- Simulates every finite prefix after mapping a transform over a statement
list. Assuming `Rtrace` relates empty traces and respects chronological
concatenation, `Inv` holds initially and is preserved by terminating source
statements, and `Inv` supplies the source well-formedness required by the
per-statement overapproximation, each prefix run from `ss` has a transformed
prefix run to some target configuration with an `Rtrace`-related trace. -/
private theorem overapproximatesTraces_stmts_prefix
    (Rtrace : Relation (List EventT))
    (hnil : Rtrace [] [])
    (happend : ∀ a a' b b', Rtrace a a' → Rtrace b b' → Rtrace (a ++ b) (a' ++ b'))
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    {SParams : Type}
    (swf : SParams → Stmt P CmdT → Env P → Prop)
    (sp₁ sp₂ : SParams)
    (Inv : Env P → Prop)
    (hPres : ∀ {s : Stmt P CmdT} {ρ ρ' : Env P} {tr : List EventT}, Inv ρ →
       StepStmtStarE P evalCmdE (.stmt s ρ) tr (.terminal ρ') → Inv ρ')
    (hGate : ∀ {s : Stmt P CmdT} {ρ : Env P}, Inv ρ → swf sp₁ s ρ)
    (hsem : OverapproximatesTraces Rtrace
      (EventLang.imperativeE P CmdT evalCmdE SParams swf)
      (EventLang.imperativeE P CmdT evalCmdE SParams swf) T sp₁ sp₂)
    (ss : List (Stmt P CmdT)) :
    ∀ (ss' : List (Stmt P CmdT)), ss.mapM T = some ss' →
      ∀ (ρ₀ : Env P) (cfg : Config P CmdT) (tr : List EventT), Inv ρ₀ →
        StepStmtStarE P evalCmdE (.stmts ss ρ₀) tr cfg →
        ∃ cfg' tr', StepStmtStarE P evalCmdE (.stmts ss' ρ₀) tr' cfg' ∧
          Rtrace tr tr' := by
  induction ss with
  | nil =>
    intro ss' hmap ρ₀ cfg tr _ hstar
    have hss' : ss' = [] := by simpa [List.mapM_nil] using hmap
    subst hss'
    obtain ⟨htr, _⟩ := stmts_nil_runE evalCmdE hstar
    subst htr
    exact ⟨_, [], .refl _, hnil⟩
  | cons s rest ih =>
    intro ss' hmap ρ₀ cfg tr hwf hstar
    obtain ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    have hsem_s := hsem s s' hs trivial ρ₀ ρ₀ rfl (hGate hwf)
    rcases stmts_cons_headE evalCmdE hstar with ⟨_, htr⟩ | hseq
    · subst htr; exact ⟨_, [], .refl _, hnil⟩
    · rcases seq_run_decomposeE evalCmdE hseq with
        ⟨inner', _, hrun_head⟩ | ⟨ρ₁, tr₁, tr₂, htr, hterm_s, hrun_tail⟩ | ⟨lbl, ρ₁, _, hexit_s⟩
      · obtain ⟨c', trh, hrun_s', hrelh⟩ := hsem_s.1 inner' tr hrun_head
        refine ⟨.seq c' rest', trh, ?_, hrelh⟩
        exact ReflTransTrace.step (r := StepStmtE P evalCmdE) _ _ _ _ _
          .step_stmts_cons
          (seq_inner_starE evalCmdE hrun_s')
      · obtain ⟨ρ₁', trh, hrun_s', heqρ, hrelh⟩ := hsem_s.2.1 ρ₁ tr₁ hterm_s
        subst heqρ
        have hwf₁ := hPres hwf hterm_s
        obtain ⟨cfg', trt, hrun_tail', hrelt⟩ := ih rest' hrm ρ₁ cfg tr₂ hwf₁ hrun_tail
        refine ⟨cfg', trh ++ trt, ?_, ?_⟩
        · exact ReflTransTrace.trans _
            (stmts_cons_stepE evalCmdE s' rest' ρ₀ ρ₁ hrun_s') hrun_tail'
        · rw [htr]; exact happend tr₁ trh tr₂ trt hrelh hrelt
      · obtain ⟨ρ₁', trh, hrun_s', heqρ, hrelh⟩ := hsem_s.2.2.1 lbl ρ₁ tr hexit_s
        subst heqρ
        refine ⟨.exiting lbl ρ₁, trh, ?_, hrelh⟩
        have hchain :
          StepStmtStarE P evalCmdE (.stmts (s' :: rest') ρ₀)
            (([] ++ trh) ++ ([] ++ [])) (.exiting lbl ρ₁) :=
          ReflTransTrace.trans _
            (ReflTransTrace.step _ _ _ _ _ .step_stmts_cons
              (seq_inner_starE evalCmdE hrun_s'))
            (ReflTransTrace.step (r := StepStmtE P evalCmdE) _ _ _ _ _ .step_seq_exit (.refl _))
        simpa using hchain

omit [HasOps P] in
/-- Lift a per-statement trace overapproximation to whole statement lists.  It
simulates every finite source prefix and every terminal/exiting run.  The
lift is mediated by an environment invariant `Inv` established at block entry
(`hGround`), preserved across each statement's terminal run (`hPres`), and
implying the per-statement source gate (`hGate`).  `Rtrace` need only satisfy the
empty-trace law `hnil` and the append-compatibility law `happend`. -/
theorem overapproximatesTraces_stmts
    (Rtrace : Relation (List EventT))
    (hnil : Rtrace [] [])
    (happend : ∀ a a' b b', Rtrace a a' → Rtrace b b' → Rtrace (a ++ b) (a' ++ b'))
    {Params : Type}
    (wf : Params → List (Stmt P CmdT) → Env P → Prop)
    (p₁ p₂ : Params)
    {SParams : Type}
    (swf : SParams → Stmt P CmdT → Env P → Prop)
    (sp₁ sp₂ : SParams)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (Inv : Env P → Prop)
    (hGround : ∀ ss ρ, wf p₁ ss ρ → Inv ρ)
    (hPres : ∀ {s : Stmt P CmdT} {ρ ρ' : Env P} {tr : List EventT}, Inv ρ →
       StepStmtStarE P evalCmdE (.stmt s ρ) tr (.terminal ρ') → Inv ρ')
    (hGate : ∀ {s : Stmt P CmdT} {ρ : Env P}, Inv ρ → swf sp₁ s ρ)
    (hWF : ∀ ss ss' ρ, ss.mapM T = some ss' → wf p₁ ss ρ → wf p₂ ss' ρ)
    (hsem : OverapproximatesTraces Rtrace
      (EventLang.imperativeE P CmdT evalCmdE SParams swf)
      (EventLang.imperativeE P CmdT evalCmdE SParams swf) T sp₁ sp₂) :
    OverapproximatesTraces Rtrace
      (EventLang.imperativeBlockE P CmdT evalCmdE ⟨Params, wf⟩)
      (EventLang.imperativeBlockE P CmdT evalCmdE ⟨Params, wf⟩)
      (fun ss => ss.mapM T) p₁ p₂ := by
  intro ss ss' hmap _ ρ₀ ρ₀' heq hwf
  subst heq
  have hInv0 := hGround ss ρ₀ hwf
  refine ⟨?_, ?_, ?_, hWF ss ss' ρ₀ hmap hwf⟩
  · intro cfg trace hrun
    exact overapproximatesTraces_stmts_prefix evalCmdE Rtrace hnil happend T
      swf sp₁ sp₂ Inv hPres hGate hsem ss ss' hmap ρ₀ cfg trace hInv0 hrun
  · intro ρ' trace hrun
    obtain ⟨tr', hrun', hrel⟩ := (overapproximatesTraces_stmts_aux evalCmdE
      Rtrace hnil happend T swf sp₁ sp₂ Inv hPres hGate hsem ss ss' hmap ρ₀ ρ' trace hInv0).1 hrun
    exact ⟨ρ', tr', hrun', rfl, hrel⟩
  · intro lbl ρ' trace hrun
    obtain ⟨tr', hrun', hrel⟩ := (overapproximatesTraces_stmts_aux evalCmdE
      Rtrace hnil happend T swf sp₁ sp₂ Inv hPres hGate hsem ss ss' hmap ρ₀ ρ' trace hInv0).2 lbl hrun
    exact ⟨ρ', tr', hrun', rfl, hrel⟩

end TracedStructuredStmts

omit [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P]
  [HasSubstFvar P] [HasInt P] [HasIntOps P] in
/-- **Trace overapproximation gives overapproximation of runs**, up to the same
    trace relation. Bounded paths are finite executions, so each source path has
    a related target path. -/
theorem OverapproximatesTracesUptoWhen.runsOverapproximate
    {EventT : Type _} {Rtrace : Relation (List EventT)} {Rin Rout : Relation (Env P)}
    {L₁ L₂ : Strata.Logic.EventLang P EventT} {T : L₁.StmtT → Option L₂.StmtT}
    {pre : L₁.StmtT → Prop} {params₁ : L₁.InitEnvWFParamsTy} {params₂ : L₂.InitEnvWFParamsTy}
    (hover : OverapproximatesTracesUptoWhen Rtrace Rin Rout L₁ L₂ T pre params₁ params₂)
    {st : L₁.StmtT} {st' : L₂.StmtT} (hT : T st = some st') (hpre : pre st)
    {ρ₀ ρ₀' : Env P} (hin : Rin ρ₀ ρ₀') (hwf : L₁.initEnvWF params₁ st ρ₀) :
    L₁.RunsOverapproximate Rtrace L₂ (L₁.stmtCfg st ρ₀) (L₂.stmtCfg st' ρ₀') := by
  intro n trace c h
  obtain ⟨c', trace', h', hrel⟩ := (hover st st' hT hpre ρ₀ ρ₀' hin hwf).1 c trace
    (Strata.Logic.EventLang.traceStar_iff_reachesWithin.mpr ⟨n, h⟩)
  obtain ⟨m, hm⟩ := Strata.Logic.EventLang.traceStar_iff_reachesWithin.mp h'
  exact ⟨m, trace', c', hm, hrel⟩

omit [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P]
  [HasSubstFvar P] [HasInt P] [HasIntOps P] in
/-- **Trace overapproximation preserves termination forward**: a source run that
    finishes, normally or by an exit, has a target run that finishes the same
    way, with a related final environment and trace. So a target with no
    finishing run has a source with none. -/
theorem OverapproximatesTracesUptoWhen.terminatesAt
    {EventT : Type _} {Rtrace : Relation (List EventT)} {Rin Rout : Relation (Env P)}
    {L₁ L₂ : Strata.Logic.EventLang P EventT} {T : L₁.StmtT → Option L₂.StmtT}
    {pre : L₁.StmtT → Prop} {params₁ : L₁.InitEnvWFParamsTy} {params₂ : L₂.InitEnvWFParamsTy}
    (hover : OverapproximatesTracesUptoWhen Rtrace Rin Rout L₁ L₂ T pre params₁ params₂)
    {st : L₁.StmtT} {st' : L₂.StmtT} (hT : T st = some st') (hpre : pre st)
    {ρ₀ ρ₀' : Env P} (hin : Rin ρ₀ ρ₀') (hwf : L₁.initEnvWF params₁ st ρ₀)
    {trace : List EventT} {ρ' : Env P} (h : L₁.TerminatesAt st ρ₀ trace ρ') :
    ∃ ρ'' trace', L₂.TerminatesAt st' ρ₀' trace' ρ'' ∧ Rout ρ' ρ'' ∧ Rtrace trace trace' := by
  obtain ⟨_, hterm, hexit, _⟩ := hover st st' hT hpre ρ₀ ρ₀' hin hwf
  rcases h with h | ⟨lbl, h⟩
  · obtain ⟨ρ'', trace', h', hout, hrel⟩ := hterm ρ' trace h
    exact ⟨ρ'', trace', .inl h', hout, hrel⟩
  · obtain ⟨ρ'', trace', h', hout, hrel⟩ := hexit lbl ρ' trace h
    exact ⟨ρ'', trace', .inr ⟨lbl, h'⟩, hout, hrel⟩

end Transform

/-! ## Verification pipelines over event traces

A verifier run after a trace-overapproximating transformation is sound for the
source when the trace relation reflects whole-trace assertion validity: every
source trace has a related target trace, the verifier makes that target trace
valid, and reflection carries validity back. Equality reflects validity
trivially. -/

namespace Analysis

open Transform Imperative.Analysis

/-
Theorem (`ValidOnTracesVerifier.of_overapproximatesTracesUptoWhen`):
  If `T` overapproximates traces up to `Rtrace`, `Rin`, `Rout` under `pre`,
  `Rtrace` reflects `Trace.AssertionsValid`, and `analyze` is a sound
  verifier for `L₂` from `L₂.initEnvWF params₂`, then `thenVerify T analyze`
  is a sound verifier for `L₁` from every environment `ρ₀` with `pre s`,
  `L₁.initEnvWF params₁ s ρ₀`, and some `ρ₀'` with `Rin ρ₀ ρ₀'`.

Proof:
  Fix `s` passing `thenVerify T analyze`, an admitted `ρ₀` with witness `ρ₀'`,
  and a source trace `trace` from `L₁.stmtCfg s ρ₀`.
  1. `T s = some s'` and `analyze s' = true`
     by `thenVerify`: a rejected statement does not pass.
  2. Some target trace `trace'` from `L₂.stmtCfg s' ρ₀'` has `Rtrace trace trace'`,
     and `L₂.initEnvWF params₂ s' ρ₀'` holds
     by the prefix and target-well-formedness clauses of `hover`.
  3. `Trace.AssertionsValid trace'`
     by `hsound` at `s'`, using 1 and 2.
  4. done
     by `hreflect` on 2 and 3.
-/
omit [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P]
  [HasSubstFvar P] [HasInt P] [HasIntOps P] in
/-- **A verifier after a transformation that overapproximates traces up to
    state relations is sound** on the source, from every well-formed entry
    environment that satisfies the precondition and is related to some target
    entry environment, provided the trace relation reflects assertion
    validity. -/
theorem ValidOnTracesVerifier.of_overapproximatesTracesUptoWhen
    {I : ConditionInterp P} {Rtrace : Relation (Trace P)} {Rin Rout : Relation (Env P)}
    {L₁ L₂ : EventLang P (Event P)} {T : L₁.StmtT → Option L₂.StmtT}
    {pre : L₁.StmtT → Prop} {params₁ : L₁.InitEnvWFParamsTy} {params₂ : L₂.InitEnvWFParamsTy}
    {analyze : L₂.StmtT → Bool}
    (hreflect : ∀ trace trace', Rtrace trace trace' →
      Trace.AssertionsValid P I trace' → Trace.AssertionsValid P I trace)
    (hover : OverapproximatesTracesUptoWhen Rtrace Rin Rout L₁ L₂ T pre params₁ params₂)
    (hsound : ValidOnTracesVerifier L₂ I (L₂.initEnvWF params₂) analyze) :
    ValidOnTracesVerifier L₁ I
      (fun s ρ₀ => pre s ∧ L₁.initEnvWF params₁ s ρ₀ ∧ ∃ ρ₀', Rin ρ₀ ρ₀')
      (thenVerify T analyze) := by
  intro s hpass ρ₀ cfg trace ⟨hpre, hwf, ρ₀', hrel⟩ htrace
  unfold thenVerify at hpass
  cases hT : T s with
  | none => rw [hT] at hpass; cases hpass
  | some s' =>
    rw [hT] at hpass
    obtain ⟨hprefix, _, _, hwf'⟩ := hover s s' hT hpre ρ₀ ρ₀' hrel hwf
    obtain ⟨cfg', trace', htrace', htr⟩ := hprefix cfg trace htrace
    exact hreflect trace trace' htr (hsound s' hpass ρ₀' cfg' trace' hwf' htrace')

omit [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P]
  [HasSubstFvar P] [HasInt P] [HasIntOps P] in
/-- **A verifier after a trace-overapproximating transformation is sound** on
    the source, from every well-formed entry environment, provided the trace
    relation reflects assertion validity. -/
theorem ValidOnTracesVerifier.of_overapproximatesTraces
    {I : ConditionInterp P} {Rtrace : Relation (Trace P)}
    {L₁ L₂ : EventLang P (Event P)} {T : L₁.StmtT → Option L₂.StmtT}
    {params₁ : L₁.InitEnvWFParamsTy} {params₂ : L₂.InitEnvWFParamsTy}
    {analyze : L₂.StmtT → Bool}
    (hreflect : ∀ trace trace', Rtrace trace trace' →
      Trace.AssertionsValid P I trace' → Trace.AssertionsValid P I trace)
    (hover : OverapproximatesTraces Rtrace L₁ L₂ T params₁ params₂)
    (hsound : ValidOnTracesVerifier L₂ I (L₂.initEnvWF params₂) analyze) :
    ValidOnTracesVerifier L₁ I (L₁.initEnvWF params₁) (thenVerify T analyze) :=
  fun s hpass ρ₀ cfg trace hwf htrace =>
    ValidOnTracesVerifier.of_overapproximatesTracesUptoWhen hreflect hover hsound
      s hpass ρ₀ cfg trace ⟨trivial, hwf, ρ₀, rfl⟩ htrace

omit [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P]
  [HasSubstFvar P] [HasInt P] [HasIntOps P] in
/-- Verifying after a list of transformations is verifying after the first, of
    verifying after the rest. -/
private theorem thenVerify_runTransforms_cons {EventT : Type _} {L : EventLang P EventT}
    (T : L.StmtT → Option L.StmtT)
    (rest : List (L.StmtT → Option L.StmtT)) (analyze : L.StmtT → Bool) :
    thenVerify (runTransforms (T :: rest)) analyze =
      thenVerify T (thenVerify (runTransforms rest) analyze) := by
  funext s
  simp only [thenVerify, runTransforms]
  cases T s <;> rfl

omit [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P]
  [HasSubstFvar P] [HasInt P] [HasIntOps P] in
/-- **A verification pipeline of trace-overapproximating phases is sound**: if
    every phase overapproximates traces up to a validity-reflecting `Rtrace`
    and the final verifier is sound, running the phases and then the verifier
    is sound, from every well-formed entry environment. -/
theorem ValidOnTracesVerifier.runTransforms_of_overapproximatesTraces
    {I : ConditionInterp P} {Rtrace : Relation (Trace P)}
    {L : EventLang P (Event P)} {params : L.InitEnvWFParamsTy} {analyze : L.StmtT → Bool}
    (hreflect : ∀ trace trace', Rtrace trace trace' →
      Trace.AssertionsValid P I trace' → Trace.AssertionsValid P I trace) :
    ∀ phases : List (L.StmtT → Option L.StmtT),
      (∀ T ∈ phases, OverapproximatesTraces Rtrace L L T params params) →
      ValidOnTracesVerifier L I (L.initEnvWF params) analyze →
      ValidOnTracesVerifier L I (L.initEnvWF params)
        (thenVerify (runTransforms phases) analyze)
  | [], _, hsound => fun s hpass => hsound s hpass
  | T :: rest, hphases, hsound => by
    rw [thenVerify_runTransforms_cons]
    exact ValidOnTracesVerifier.of_overapproximatesTraces hreflect
      (hphases T (List.mem_cons_self ..))
      (ValidOnTracesVerifier.runTransforms_of_overapproximatesTraces hreflect rest
        (fun T' h => hphases T' (List.mem_cons_of_mem _ h)) hsound)

omit [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P]
  [HasSubstFvar P] [HasInt P] [HasIntOps P] in
/-- **A verification pipeline of phases that overapproximate traces up to state
    relations is sound**, when each phase's trace relation reflects assertion
    validity and its input relation relates every source entry environment to
    some target one: running the phases and then a sound verifier is sound,
    from every well-formed entry environment. -/
theorem ValidOnTracesVerifier.runTransforms_of_overapproximatesTracesUpto
    {I : ConditionInterp P}
    {L : EventLang P (Event P)} {params : L.InitEnvWFParamsTy} {analyze : L.StmtT → Bool} :
    ∀ phases : List (L.StmtT → Option L.StmtT),
      (∀ T ∈ phases, ∃ (Rtrace : Relation (Trace P)) (Rin Rout : Relation (Env P)),
        OverapproximatesTracesUptoWhen Rtrace Rin Rout L L T (fun _ => True) params params ∧
        (∀ trace trace', Rtrace trace trace' →
          Trace.AssertionsValid P I trace' → Trace.AssertionsValid P I trace) ∧
        ∀ ρ₀, ∃ ρ₀', Rin ρ₀ ρ₀') →
      ValidOnTracesVerifier L I (L.initEnvWF params) analyze →
      ValidOnTracesVerifier L I (L.initEnvWF params)
        (thenVerify (runTransforms phases) analyze)
  | [], _, hsound => fun s hpass => hsound s hpass
  | T :: rest, hphases, hsound => by
    rw [thenVerify_runTransforms_cons]
    obtain ⟨Rtrace, Rin, Rout, hover, hreflect, htot⟩ := hphases T (List.mem_cons_self ..)
    have hrest := ValidOnTracesVerifier.runTransforms_of_overapproximatesTracesUpto rest
      (fun T' h => hphases T' (List.mem_cons_of_mem _ h)) hsound
    exact fun s hpass ρ₀ cfg trace hwf htrace =>
      ValidOnTracesVerifier.of_overapproximatesTracesUptoWhen hreflect hover hrest
        s hpass ρ₀ cfg trace ⟨trivial, hwf, htot ρ₀⟩ htrace

end Analysis

end Specification
end Imperative

end -- public section
