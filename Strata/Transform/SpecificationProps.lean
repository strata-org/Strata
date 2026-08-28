/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.Transform.Specification
public import Strata.DL.Imperative.Logic.HoareTemplate
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
`Strata.DL.Imperative.Logic.HoareTemplate`, and the bridges from them to the
reachability-based side are in `Strata.Transform.SpecHoareConnection`:

- `sound_assertValid` / `sound_allAsserts` — `Sound` implies `AssertValid`.

Properties of the `Overapproximates` family (monotonicity and composition):

- `OverapproximatesUptoWhen.mono` — coerce both relations of
  `OverapproximatesUptoWhen`: tighten the input relation (`Rin' ⊆ Rin`) and
  weaken the output relation (`Rout ⊆ Rout'`).  `OverapproximatesUptoWhen.mono_out`
  (output-only, covariant) and `OverapproximatesUptoWhen.mono_in` (input-only,
  contravariant) are its single-sided specializations.
- `overapproximatesUpto_comp` / `OverapproximatesUptoWhen.comp_eq` /
  `OverapproximatesUptoWhen.comp` / `OverapproximatesUptoWhen.comp_dense_trans` /
  `OverapproximatesUptoWhen.comp_trans_eq` / `overapproximates_comp` /
  `overapproximatesAggressively_comp` — composition of transforms under the
  various family members.
- `overapproximates_id` / `underapproximates_id` / `semanticallyEquivalent_id` —
  the identity transform inhabits each spec.
- `EnvStoreAgree_trans` — transitivity of the `EnvStoreAgree` output relation
  (defined in `Specification`), used to chain the per-pass instances.

### Key results for `OverapproximatesAggressivelyUptoWhen`

The aggressive-up-to relation (the common generalization of the faithful up-to
and equality-output aggressive relations) has these structural lemmas:
- `OverapproximatesAggressivelyUptoWhen.mono_out` — output-relation weakening.
- `OverapproximatesAggressivelyUptoWhen.comp_eq` — shared-start (`Rin = (· = ·)`)
  `RComp` composition (needs the first output relation to preserve failure-freedom).
- `OverapproximatesAggressivelyUptoWhen.comp_trans_eq` — the transitive
  shared-start combinator for chaining per-pass instances.
- `OverapproximatesAggressivelyUptoWhen.strengthen` — precondition weakening.
- `OverapproximatesUptoWhen.toAggressivelyUptoWhen` /
  `OverapproximatesAggressivelyWhen.toAggressivelyUptoWhen` — coercions from the
  faithful up-to and equality-output aggressive relations into the common one.
- `overapproximatesAggressivelyUptoWhen_eq_iff` — the `Rin = Rout = (· = ·)`
  specialization coincides with `OverapproximatesAggressivelyWhen`.
- `OverapproximatesAggressivelyWhen.comp_uptoWhen` /
  `OverapproximatesUptoWhen.comp_aggressivelyWhen` — the cross-family boundary
  joins (aggressive-first / up-to-first) for a mixed pipeline.
-/

public section

namespace Imperative

namespace Specification

open Strata.Logic Imperative.Logic

variable {P : PureExpr} [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P] [HasSubstFvar P]
    [HasInt P] [HasIntOps P]
variable (L : Lang P)



namespace Transform

/-! ## Connection between Sound, AssertValid and AllAssertsValid -/

section Connection
omit [HasOps P] [HasBoolOps P] [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasSubstFvar P]

theorem sound_comp (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    (h₁ : Sound L₁ L₂ T₁ params₁ params₂) (h₂ : Sound L₂ L₃ T₂ params₂ params₃) :
    Sound L₁ L₃ (fun s => T₁ s >>= T₂) params₁ params₃ := by
  intro s s'' a hrun hvalid
  simp [bind, Option.bind] at hrun
  match h1 : T₁ s with
  | some s' => rw [h1] at hrun; exact h₁ s s' a h1 (h₂ s' s'' a hrun hvalid)
  | none => rw [h1] at hrun; exact absurd hrun (by nofun)

theorem sound_assertValid (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (a : AssertId P)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (s : L₁.StmtT) (s' : L₂.StmtT)
    (ht : T s = some s') (hsound : Sound L₁ L₂ T params₁ params₂)
    (hvalid : AssertValidWhen L₂ (L₂.initEnvWF params₂ s') s' a) :
    AssertValidWhen L₁ (L₁.initEnvWF params₁ s) s a := hsound s s' a ht hvalid

theorem sound_allAsserts (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (s : L₁.StmtT) (s' : L₂.StmtT) (ht : T s = some s')
    (hsound : Sound L₁ L₂ T params₁ params₂)
    (hvalid : AllAssertsValidWhen L₂ (L₂.initEnvWF params₂ s') s') :
    AllAssertsValidWhen L₁ (L₁.initEnvWF params₁ s) s := fun a => hsound s s' a ht (hvalid a)

theorem sound_id (params : L.InitEnvWFParamsTy) : Sound L L some params params := by
  intro s s' a ht hvalid; simp at ht; subst ht; exact hvalid

end Connection






/-! ## Properties of the `Overapproximates` family. -/

section OverapproxProps
omit [HasOps P] [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P] [HasInt P] [HasIntOps P] [HasSubstFvar P]

theorem overapproximates_id (L₁ : Lang P) (params₁ : L₁.InitEnvWFParamsTy) :
    Overapproximates L₁ L₁ some params₁ params₁ := by
  intro st s' ht _ ρ₀ ρ₀' heq hinit
  simp at ht; subst ht; subst heq
  exact ⟨fun ρ' => ⟨fun h => ⟨ρ', rfl, h⟩, fun _ h => ⟨ρ', rfl, h⟩⟩, fun h => h, hinit⟩

/-- Composition of two overapproximations under relation composition. -/
theorem overapproximatesUpto_comp (L₁ L₂ L₃ : Lang P)
    (R₁ R₂ : Relation (Env P))
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    (h₁ : OverapproximatesUpto R₁ L₁ L₂ T₁ params₁ params₂)
    (h₂ : OverapproximatesUpto R₂ L₂ L₃ T₂ params₂ params₃) :
    OverapproximatesUpto (RComp R₁ R₂) L₁ L₃ (fun s => T₁ s >>= T₂) params₁ params₃ := by
  intro st s'' ht _ ρ₀ ρ₀'' hR hinit
  obtain ⟨ρmid, hR₁mid, hR₂mid⟩ := hR
  simp [bind, Option.bind] at ht
  match h : T₁ st with
  | some s' =>
    rw [h] at ht
    have hr₁ := h₁ st s' h trivial ρ₀ ρmid hR₁mid hinit
    have hr₂ := h₂ s' s'' ht trivial ρmid ρ₀'' hR₂mid hr₁.2.2
    refine ⟨fun ρ' => ⟨?_, ?_⟩, ?_, hr₂.2.2⟩
    · intro hstar
      obtain ⟨ρ'm, hRm, hsm⟩ := (hr₁.1 ρ').1 hstar
      obtain ⟨ρ'', hR2, hs2⟩ := (hr₂.1 ρ'm).1 hsm
      exact ⟨ρ'', ⟨ρ'm, hRm, hR2⟩, hs2⟩
    · intro lbl hstar
      obtain ⟨ρ'm, hRm, hsm⟩ := (hr₁.1 ρ').2 lbl hstar
      obtain ⟨ρ'', hR2, hs2⟩ := (hr₂.1 ρ'm).2 lbl hsm
      exact ⟨ρ'', ⟨ρ'm, hRm, hR2⟩, hs2⟩
    · intro hfail; exact hr₂.2.1 (hr₁.2.1 hfail)
  | none => rw [h] at ht; exact absurd ht (by nofun)

/-- Rewriting both relations of `OverapproximatesUptoWhen`.  The input relation
    `Rin` sits in hypothesis position (contravariant) while the output relation
    `Rout` sits in the positive position of the terminal/exiting witnesses
    (covariant), so the coercion tightens the input (`Rin' ⊆ Rin`) and weakens the
    output (`Rout ⊆ Rout'`).  The `CanFail` and target-`initEnvWF` conjuncts do not
    mention either relation, so they pass through unchanged.

    `mono_out` and `mono_in` are the single-sided specializations. -/
theorem OverapproximatesUptoWhen.mono (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    {Rin Rin' Rout Rout' : Relation (Env P)}
    (hin : ∀ a b, Rin' a b → Rin a b)
    (hout : ∀ a b, Rout a b → Rout' a b)
    (h : OverapproximatesUptoWhen Rin Rout L₁ L₂ T pre params₁ params₂) :
    OverapproximatesUptoWhen Rin' Rout' L₁ L₂ T pre params₁ params₂ := by
  intro st st' ht hpre ρ₀ ρ₀' hRin' hwf
  have hr := h st st' ht hpre ρ₀ ρ₀' (hin _ _ hRin') hwf
  refine ⟨fun ρ' => ⟨fun hstar => ?_, fun lbl hstar => ?_⟩, hr.2.1, hr.2.2⟩
  · obtain ⟨ρ'', hR, hstar'⟩ := (hr.1 ρ').1 hstar; exact ⟨ρ'', hout _ _ hR, hstar'⟩
  · obtain ⟨ρ'', hR, hstar'⟩ := (hr.1 ρ').2 lbl hstar; exact ⟨ρ'', hout _ _ hR, hstar'⟩

/-- Rewriting the *output* relation `Rout → Rout'`, holding the input relation
    `Rin` fixed.  The output relation appears only in the positive position of the
    terminal/exiting witnesses, so the change is purely monotone: `Rout ⊆ Rout'`
    suffices.  The `Rout`-covariant specialization of `mono`. -/
theorem OverapproximatesUptoWhen.mono_out (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    {Rin Rout Rout' : Relation (Env P)}
    (hout : ∀ a b, Rout a b → Rout' a b)
    (h : OverapproximatesUptoWhen Rin Rout L₁ L₂ T pre params₁ params₂) :
    OverapproximatesUptoWhen Rin Rout' L₁ L₂ T pre params₁ params₂ :=
  OverapproximatesUptoWhen.mono L₁ L₂ T pre params₁ params₂ (fun _ _ => id) hout h

/-- Rewriting the *input* relation `Rin → Rin'`, holding the output relation
    `Rout` fixed.  The input relation sits in hypothesis position, so tightening it
    (`Rin' ⊆ Rin`) is what preserves the guarantee: fewer initial pairs are
    required to be related.  The `Rin`-contravariant specialization of `mono`.

    Combined with `RComp`, this is the input-side dual of the transitivity collapse
    that `mono_out` supports: a *dense* input relation (`Rin ⊆ RComp Rin Rin`, see
    `Dense`) can be re-expressed as the two-step `RComp Rin Rin` that a composed
    transform's input relation carries. -/
theorem OverapproximatesUptoWhen.mono_in (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    {Rin Rin' Rout : Relation (Env P)}
    (hin : ∀ a b, Rin' a b → Rin a b)
    (h : OverapproximatesUptoWhen Rin Rout L₁ L₂ T pre params₁ params₂) :
    OverapproximatesUptoWhen Rin' Rout L₁ L₂ T pre params₁ params₂ :=
  OverapproximatesUptoWhen.mono L₁ L₂ T pre params₁ params₂ hin (fun _ _ => id) h

/-- **Compositionality** (shared-start form): composing two transforms that each
    run source and target from the *same* initial env (input relation `(· = ·)`)
    composes their output relations via `RComp` and keeps the shared-start input
    relation.  Pass 2's source `initEnvWF` at `ρ₀` is exactly pass 1's target
    `initEnvWF` conjunct (`hr₁.2.2`), so the intermediate initial-environment
    freshness threads through `initEnvWF` with no separate input relation or
    per-env precondition (the input `(· = ·)` collapses the RComp intermediate to
    `ρ₀` outright). -/
theorem OverapproximatesUptoWhen.comp_eq (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    {pre₁ : L₁.StmtT → Prop} {pre₂ : L₂.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    {R₁ R₂ : Relation (Env P)}
    (hpre : ∀ st st', T₁ st = some st' → pre₁ st → pre₂ st')
    (h₁ : OverapproximatesUptoWhen (· = ·) R₁ L₁ L₂ T₁ pre₁ params₁ params₂)
    (h₂ : OverapproximatesUptoWhen (· = ·) R₂ L₂ L₃ T₂ pre₂ params₂ params₃) :
    OverapproximatesUptoWhen (· = ·) (RComp R₁ R₂)
      L₁ L₃ (fun s => T₁ s >>= T₂) pre₁ params₁ params₃ := by
  intro st st'' ht hpre₁ ρ₀ ρ₀' hEq hwf
  subst hEq
  simp only [bind, Option.bind] at ht
  match hT₁ : T₁ st with
  | none => rw [hT₁] at ht; exact absurd ht (by nofun)
  | some st' =>
    rw [hT₁] at ht
    have hr₁ := h₁ st st' hT₁ hpre₁ ρ₀ ρ₀ rfl hwf
    have hr₂ := h₂ st' st'' ht (hpre st st' hT₁ hpre₁) ρ₀ ρ₀ rfl hr₁.2.2
    refine ⟨fun ρ' => ⟨fun hstar => ?_, fun lbl hstar => ?_⟩,
            fun hcf => hr₂.2.1 (hr₁.2.1 hcf), hr₂.2.2⟩
    · obtain ⟨ρ'₂, hR₁', hstar₂⟩ := (hr₁.1 ρ').1 hstar
      obtain ⟨ρ'₃, hR₂', hstar₃⟩ := (hr₂.1 ρ'₂).1 hstar₂
      exact ⟨ρ'₃, ⟨ρ'₂, hR₁', hR₂'⟩, hstar₃⟩
    · obtain ⟨ρ'₂, hR₁', hstar₂⟩ := (hr₁.1 ρ').2 lbl hstar
      obtain ⟨ρ'₃, hR₂', hstar₃⟩ := (hr₂.1 ρ'₂).2 lbl hstar₂
      exact ⟨ρ'₃, ⟨ρ'₂, hR₁', hR₂'⟩, hstar₃⟩

/-- **Compositionality** (general split-input form): composing two transforms with
    arbitrary input and output relations composes both via `RComp`.  Unlike
    `comp_eq`, the two stages need not run from the same initial env: the composed
    input relation `RComp Rin₁ Rin₂` supplies an intermediate initial env `ρmid`
    with `Rin₁ ρ₀ ρmid` and `Rin₂ ρmid ρ₀''`, and pass 2 runs from `ρmid`.  Pass
    2's source `initEnvWF` at `ρmid` is exactly pass 1's target `initEnvWF`
    conjunct (`hr₁.2.2`), so freshness threads through with no per-env
    precondition.  `comp_eq` is the `Rin₁ = Rin₂ = (· = ·)` diagonal of this. -/
theorem OverapproximatesUptoWhen.comp (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    {pre₁ : L₁.StmtT → Prop} {pre₂ : L₂.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    {Rin₁ Rin₂ Rout₁ Rout₂ : Relation (Env P)}
    (hpre : ∀ st st', T₁ st = some st' → pre₁ st → pre₂ st')
    (h₁ : OverapproximatesUptoWhen Rin₁ Rout₁ L₁ L₂ T₁ pre₁ params₁ params₂)
    (h₂ : OverapproximatesUptoWhen Rin₂ Rout₂ L₂ L₃ T₂ pre₂ params₂ params₃) :
    OverapproximatesUptoWhen (RComp Rin₁ Rin₂) (RComp Rout₁ Rout₂)
      L₁ L₃ (fun s => T₁ s >>= T₂) pre₁ params₁ params₃ := by
  intro st st'' ht hpre₁ ρ₀ ρ₀'' hRin hwf
  obtain ⟨ρmid, hRin₁, hRin₂⟩ := hRin
  simp only [bind, Option.bind] at ht
  match hT₁ : T₁ st with
  | none => rw [hT₁] at ht; exact absurd ht (by nofun)
  | some st' =>
    rw [hT₁] at ht
    have hr₁ := h₁ st st' hT₁ hpre₁ ρ₀ ρmid hRin₁ hwf
    have hr₂ := h₂ st' st'' ht (hpre st st' hT₁ hpre₁) ρmid ρ₀'' hRin₂ hr₁.2.2
    refine ⟨fun ρ' => ⟨fun hstar => ?_, fun lbl hstar => ?_⟩,
            fun hcf => hr₂.2.1 (hr₁.2.1 hcf), hr₂.2.2⟩
    · obtain ⟨ρ'₂, hR₁', hstar₂⟩ := (hr₁.1 ρ').1 hstar
      obtain ⟨ρ'₃, hR₂', hstar₃⟩ := (hr₂.1 ρ'₂).1 hstar₂
      exact ⟨ρ'₃, ⟨ρ'₂, hR₁', hR₂'⟩, hstar₃⟩
    · obtain ⟨ρ'₂, hR₁', hstar₂⟩ := (hr₁.1 ρ').2 lbl hstar
      obtain ⟨ρ'₃, hR₂', hstar₃⟩ := (hr₂.1 ρ'₂).2 lbl hstar₂
      exact ⟨ρ'₃, ⟨ρ'₂, hR₁', hR₂'⟩, hstar₃⟩

/-- **Compositionality** (fixed-relation, dense-input transitive-output form):
    composing two transforms that share a *dense* input relation `Rin` and a
    *transitive* output relation `Rout` yields a transform with the same `Rin` and
    `Rout`.  This is the `Dense`/`mono_in` consumer: `comp` produces `RComp Rin Rin`
    on the input and `RComp Rout Rout` on the output; `mono_out` collapses the
    composed output back to `Rout` via transitivity (`RComp.collapse`), and
    `mono_in` re-expresses a single `Rin`-relatedness as the two-step `RComp Rin Rin`
    the composed input carries via density (`Dense`).  `comp_trans_eq` is the
    `Rin := (· = ·)` instance (equality is dense by `Reflexive.dense`). -/
theorem OverapproximatesUptoWhen.comp_dense_trans (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    {pre₁ : L₁.StmtT → Prop} {pre₂ : L₂.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    {Rin Rout : Relation (Env P)}
    (hdense : Dense Rin) (htrans : Transitive Rout)
    (hpre : ∀ st st', T₁ st = some st' → pre₁ st → pre₂ st')
    (h₁ : OverapproximatesUptoWhen Rin Rout L₁ L₂ T₁ pre₁ params₁ params₂)
    (h₂ : OverapproximatesUptoWhen Rin Rout L₂ L₃ T₂ pre₂ params₂ params₃) :
    OverapproximatesUptoWhen Rin Rout L₁ L₃ (fun s => T₁ s >>= T₂) pre₁ params₁ params₃ :=
  OverapproximatesUptoWhen.mono_in L₁ L₃ (fun s => T₁ s >>= T₂) pre₁ params₁ params₃
    (fun a c h => hdense a c h)
    (OverapproximatesUptoWhen.mono_out L₁ L₃ (fun s => T₁ s >>= T₂) pre₁ params₁ params₃
      (fun _ _ h => RComp.collapse htrans (fun _ _ => id) (fun _ _ => id) h)
      (OverapproximatesUptoWhen.comp L₁ L₂ L₃ T₁ T₂ params₁ params₂ params₃ hpre h₁ h₂))

/-- **Compositionality** (shared-start transitive form): if the shared output
    relation `R` is *transitive* then composing two shared-start
    `OverapproximatesUptoWhen (· = ·) R` transforms yields another
    `OverapproximatesUptoWhen (· = ·) R` transform.  This is the combinator that
    threads per-stage freshness through a pipeline: because the initial
    environment is shared and each pass's target `initEnvWF` re-establishes the
    next pass's source `initEnvWF` at that env, no per-environment precondition is
    needed; transitivity collapses the `RComp`-composed output relation back to
    `R`.  The `Rin := (· = ·)` instance of `comp_dense_trans`: equality is dense
    (`Reflexive.dense`).  Only transitivity of `R` is consumed (no reflexivity of
    the *output*), so an irreflexive-but-transitive `R` — e.g. agreement modulo
    frame — composes here. -/
theorem OverapproximatesUptoWhen.comp_trans_eq (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    {pre₁ : L₁.StmtT → Prop} {pre₂ : L₂.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    {R : Relation (Env P)}
    (htrans : Transitive R)
    (hpre : ∀ st st', T₁ st = some st' → pre₁ st → pre₂ st')
    (h₁ : OverapproximatesUptoWhen (· = ·) R L₁ L₂ T₁ pre₁ params₁ params₂)
    (h₂ : OverapproximatesUptoWhen (· = ·) R L₂ L₃ T₂ pre₂ params₂ params₃) :
    OverapproximatesUptoWhen (· = ·) R L₁ L₃ (fun s => T₁ s >>= T₂) pre₁ params₁ params₃ :=
  OverapproximatesUptoWhen.comp_dense_trans L₁ L₂ L₃ T₁ T₂ params₁ params₂ params₃
    (Reflexive.dense (fun _ => rfl)) htrans hpre h₁ h₂

/-- Composition of two overapproximations. -/
theorem overapproximates_comp (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    (h₁ : Overapproximates L₁ L₂ T₁ params₁ params₂)
    (h₂ : Overapproximates L₂ L₃ T₂ params₂ params₃) :
    Overapproximates L₁ L₃ (fun s => T₁ s >>= T₂) params₁ params₃ := by
  have hcomp := overapproximatesUpto_comp L₁ L₂ L₃ (· = ·) (· = ·) T₁ T₂
    params₁ params₂ params₃ h₁ h₂
  intro st s'' ht _ ρ₀ ρ₀' heq hinit
  subst heq
  have hr := hcomp st s'' ht trivial ρ₀ ρ₀ ⟨ρ₀, rfl, rfl⟩ hinit
  refine ⟨fun ρ' => ⟨fun hstar => ?_, fun lbl hstar => ?_⟩, hr.2.1, hr.2.2⟩
  · obtain ⟨ρ'', ⟨b, hb₁, hb₂⟩, hstar''⟩ := (hr.1 ρ').1 hstar
    exact ⟨ρ'', hb₁.trans hb₂, hstar''⟩
  · obtain ⟨ρ'', ⟨b, hb₁, hb₂⟩, hstar''⟩ := (hr.1 ρ').2 lbl hstar
    exact ⟨ρ'', hb₁.trans hb₂, hstar''⟩

/-- Flat-shape accessor for `OverapproximatesAggressivelyWhen` (the diagonal
    `Rin = Rout = (· = ·)` specialization of `OverapproximatesAggressivelyUptoWhen`).
    In the up-to form the terminal/exiting guarantees carry an `∃ ρ''` at the
    equality output relation; this collapses that witness (`ρ'' = ρ'`) to the
    direct equality-output form: source `=` target initial env, and a target
    execution reaching `ρ'` itself rather than an existentially-quantified `ρ''`. -/
private theorem OverapproximatesAggressivelyWhen.flat_apply {L₁ L₂ : Lang P}
    {T : L₁.StmtT → Option L₂.StmtT} {pre : L₁.StmtT → Prop}
    {params₁ : L₁.InitEnvWFParamsTy} {params₂ : L₂.InitEnvWFParamsTy}
    (h : OverapproximatesAggressivelyWhen L₁ L₂ T pre params₁ params₂)
    (st : L₁.StmtT) (st' : L₂.StmtT) (ht : T st = some st') (hpre : pre st)
    (ρ₀ : Env P) (hwf : L₁.initEnvWF params₁ st ρ₀) :
    (∀ ρ', L₁.star (L₁.stmtCfg st ρ₀) (L₁.terminalCfg ρ') →
        CanFail L₂ st' ρ₀ ∨
        (ρ'.hasFailure = false → L₂.star (L₂.stmtCfg st' ρ₀) (L₂.terminalCfg ρ')))
      ∧
      (∀ lbl ρ', L₁.star (L₁.stmtCfg st ρ₀) (L₁.exitingCfg lbl ρ') →
        CanFail L₂ st' ρ₀ ∨
        (ρ'.hasFailure = false → L₂.star (L₂.stmtCfg st' ρ₀) (L₂.exitingCfg lbl ρ')))
      ∧
      (CanFail L₁ st ρ₀ → CanFail L₂ st' ρ₀)
      ∧
      L₂.initEnvWF params₂ st' ρ₀ := by
  have hr := h st st' ht hpre ρ₀ ρ₀ rfl hwf
  refine ⟨fun ρ' hstar => ?_, fun lbl ρ' hstar => ?_, hr.2.2.1, hr.2.2.2⟩
  · rcases (hr.1 ρ' hstar) with hcf | hstep
    · exact .inl hcf
    · exact .inr fun hf => by obtain ⟨ρ'', hEq, hs⟩ := hstep hf; subst hEq; exact hs
  · rcases (hr.2.1 lbl ρ' hstar) with hcf | hstep
    · exact .inl hcf
    · exact .inr fun hf => by obtain ⟨ρ'', hEq, hs⟩ := hstep hf; subst hEq; exact hs

/-- Composition of two aggressive overapproximations. -/
theorem overapproximatesAggressively_comp (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    (h₁ : OverapproximatesAggressively L₁ L₂ T₁ params₁ params₂)
    (h₂ : OverapproximatesAggressively L₂ L₃ T₂ params₂ params₃) :
    OverapproximatesAggressively L₁ L₃ (fun s => T₁ s >>= T₂) params₁ params₃ := by
  intro st s'' ht _ ρ₀ ρ₀' hEq hinit
  subst hEq
  simp [bind, Option.bind] at ht
  match hT₁ : T₁ st with
  | some s' =>
    rw [hT₁] at ht
    have ha₁ := OverapproximatesAggressivelyWhen.flat_apply h₁ st s' hT₁ trivial ρ₀ hinit
    have ha₂ := OverapproximatesAggressivelyWhen.flat_apply h₂ s' s'' ht trivial ρ₀ ha₁.2.2.2
    refine ⟨?_, ?_, fun hcf => ha₂.2.2.1 (ha₁.2.2.1 hcf), ha₂.2.2.2⟩
    · -- Terminal case
      intro ρ' hstar
      match ha₁.1 ρ' hstar with
      | .inl hcf₂ => exact .inl (ha₂.2.2.1 hcf₂)
      | .inr hmid =>
        by_cases hf : ρ'.hasFailure = false
        · match ha₂.1 ρ' (hmid hf) with
          | .inl hcf₃ => exact .inl hcf₃
          | .inr hstep₃ => exact .inr (fun _ => ⟨ρ', rfl, hstep₃ hf⟩)
        · exact .inr (fun hf' => absurd hf' hf)
    · -- Exiting case
      intro lbl ρ' hstar
      match ha₁.2.1 lbl ρ' hstar with
      | .inl hcf₂ => exact .inl (ha₂.2.2.1 hcf₂)
      | .inr hmid =>
        by_cases hf : ρ'.hasFailure = false
        · match ha₂.2.1 lbl ρ' (hmid hf) with
          | .inl hcf₃ => exact .inl hcf₃
          | .inr hstep₃ => exact .inr (fun _ => ⟨ρ', rfl, hstep₃ hf⟩)
        · exact .inr (fun hf' => absurd hf' hf)
  | none => rw [hT₁] at ht; exact absurd ht (by nofun)

/-! ## Composition and coercions for `OverapproximatesAggressivelyUptoWhen`

The aggressive-up-to relation is the common generalization of the faithful
up-to relation and the equality-output aggressive relation, so it inherits both
families' structural lemmas: output-relation monotonicity, `RComp`-composition,
a transitive shared-start combinator, an equality-specialization
bridge, and a coercion from the faithful up-to relation. -/

/-- Output-relation monotonicity: `Rout ⊆ Rout'` weakens the guarantee.  The
    output relation appears only positively (inside the `∃ ρ''` witness of the
    right disjunct), so the change is purely monotone. -/
theorem OverapproximatesAggressivelyUptoWhen.mono_out (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    {Rin Rout Rout' : Relation (Env P)}
    (hout : ∀ a b, Rout a b → Rout' a b)
    (h : OverapproximatesAggressivelyUptoWhen Rin Rout L₁ L₂ T pre params₁ params₂) :
    OverapproximatesAggressivelyUptoWhen Rin Rout' L₁ L₂ T pre params₁ params₂ := by
  intro st st' ht hpre ρ₀ ρ₀' hRin hwf
  have hr := h st st' ht hpre ρ₀ ρ₀' hRin hwf
  refine ⟨fun ρ' hstar => ?_, fun lbl ρ' hstar => ?_, hr.2.2.1, hr.2.2.2⟩
  · rcases (hr.1 ρ' hstar) with hcf | hstep
    · exact .inl hcf
    · refine .inr fun hf => ?_
      obtain ⟨ρ'', hR, hs⟩ := hstep hf
      exact ⟨ρ'', hout _ _ hR, hs⟩
  · rcases (hr.2.1 lbl ρ' hstar) with hcf | hstep
    · exact .inl hcf
    · refine .inr fun hf => ?_
      obtain ⟨ρ'', hR, hs⟩ := hstep hf
      exact ⟨ρ'', hout _ _ hR, hs⟩

/-- **Compositionality** (shared-start form).  Composing two shared-start
    (`Rin = (· = ·)`) aggressive-up-to transforms composes their output
    relations via `RComp` and keeps the shared-start input relation.

    The aggressive disjunction threads through composition exactly as in
    `overapproximatesAggressively_comp`, with one extra ingredient the up-to
    output relation forces: the intermediate reachable env `ρ'₂` is only
    `R₁`-*related* to the source terminal `ρ'` (not equal), so its failure flag
    is not immediately known.  Only the *failure-free* direction is consumed —
    recovering `ρ'₂.hasFailure = false` from `ρ'.hasFailure = false` on the
    failure-free branch so stage 2's reachability witness chains — so `hR₁fail`
    asks only that `R₁` **preserve failure-freedom**, not the full flag.  The
    `by_cases hf` on the *source* terminal then mirrors the equality proof.
    (A failure-flag-preserving output relation discharges this hypothesis, so a
    downstream pipeline whose environment relation preserves the flag satisfies
    it.) -/
theorem OverapproximatesAggressivelyUptoWhen.comp_eq (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    {pre₁ : L₁.StmtT → Prop} {pre₂ : L₂.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    {R₁ R₂ : Relation (Env P)}
    (hR₁fail : ∀ a b, R₁ a b → a.hasFailure = false → b.hasFailure = false)
    (hpre : ∀ st st', T₁ st = some st' → pre₁ st → pre₂ st')
    (h₁ : OverapproximatesAggressivelyUptoWhen (· = ·) R₁ L₁ L₂ T₁ pre₁ params₁ params₂)
    (h₂ : OverapproximatesAggressivelyUptoWhen (· = ·) R₂ L₂ L₃ T₂ pre₂ params₂ params₃) :
    OverapproximatesAggressivelyUptoWhen (· = ·) (RComp R₁ R₂)
      L₁ L₃ (fun s => T₁ s >>= T₂) pre₁ params₁ params₃ := by
  intro st st'' ht hpre₁ ρ₀ ρ₀' hEq hwf
  subst hEq
  simp only [bind, Option.bind] at ht
  match hT₁ : T₁ st with
  | none => rw [hT₁] at ht; exact absurd ht (by nofun)
  | some st' =>
    rw [hT₁] at ht
    have hr₁ := h₁ st st' hT₁ hpre₁ ρ₀ ρ₀ rfl hwf
    have hr₂ := h₂ st' st'' ht (hpre st st' hT₁ hpre₁) ρ₀ ρ₀ rfl hr₁.2.2.2
    refine ⟨fun ρ' hstar => ?_, fun lbl ρ' hstar => ?_,
            fun hcf => hr₂.2.2.1 (hr₁.2.2.1 hcf), hr₂.2.2.2⟩
    · -- Terminal
      match (hr₁.1 ρ' hstar) with
      | .inl hcf => exact .inl (hr₂.2.2.1 hcf)
      | .inr hstep₁ =>
        by_cases hf : ρ'.hasFailure = false
        · obtain ⟨ρ'₂, hR₁, hs₂⟩ := hstep₁ hf
          have hf₂ : ρ'₂.hasFailure = false := hR₁fail ρ' ρ'₂ hR₁ hf
          match (hr₂.1 ρ'₂ hs₂) with
          | .inl hcf₃ => exact .inl hcf₃
          | .inr hstep₂ =>
            obtain ⟨ρ'₃, hR₂, hs₃⟩ := hstep₂ hf₂
            exact .inr fun _ => ⟨ρ'₃, ⟨ρ'₂, hR₁, hR₂⟩, hs₃⟩
        · exact .inr fun hf' => absurd hf' hf
    · -- Exiting (mirrors the terminal case)
      match (hr₁.2.1 lbl ρ' hstar) with
      | .inl hcf => exact .inl (hr₂.2.2.1 hcf)
      | .inr hstep₁ =>
        by_cases hf : ρ'.hasFailure = false
        · obtain ⟨ρ'₂, hR₁, hs₂⟩ := hstep₁ hf
          have hf₂ : ρ'₂.hasFailure = false := hR₁fail ρ' ρ'₂ hR₁ hf
          match (hr₂.2.1 lbl ρ'₂ hs₂) with
          | .inl hcf₃ => exact .inl hcf₃
          | .inr hstep₂ =>
            obtain ⟨ρ'₃, hR₂, hs₃⟩ := hstep₂ hf₂
            exact .inr fun _ => ⟨ρ'₃, ⟨ρ'₂, hR₁, hR₂⟩, hs₃⟩
        · exact .inr fun hf' => absurd hf' hf

/-- **Compositionality** (shared-start transitive form).  If the shared output
    relation `R` is *transitive*, composing two shared-start aggressive-up-to
    `R`-transforms yields another.  This is the combinator a pipeline uses to
    chain per-pass instances; transitivity collapses the `RComp`-composed output
    back to `R` (`RComp.collapse`).  Only transitivity is consumed (no
    reflexivity), so an irreflexive-but-transitive `R` — e.g. agreement modulo
    frame — composes here. -/
theorem OverapproximatesAggressivelyUptoWhen.comp_trans_eq (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    {pre₁ : L₁.StmtT → Prop} {pre₂ : L₂.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    {R : Relation (Env P)}
    (htrans : Transitive R)
    (hRfail : ∀ a b, R a b → a.hasFailure = false → b.hasFailure = false)
    (hpre : ∀ st st', T₁ st = some st' → pre₁ st → pre₂ st')
    (h₁ : OverapproximatesAggressivelyUptoWhen (· = ·) R L₁ L₂ T₁ pre₁ params₁ params₂)
    (h₂ : OverapproximatesAggressivelyUptoWhen (· = ·) R L₂ L₃ T₂ pre₂ params₂ params₃) :
    OverapproximatesAggressivelyUptoWhen (· = ·) R L₁ L₃ (fun s => T₁ s >>= T₂) pre₁ params₁ params₃ :=
  OverapproximatesAggressivelyUptoWhen.mono_out L₁ L₃ (fun s => T₁ s >>= T₂) pre₁ params₁ params₃
    (fun _ _ h => RComp.collapse htrans (fun _ _ => id) (fun _ _ => id) h)
    (OverapproximatesAggressivelyUptoWhen.comp_eq L₁ L₂ L₃ T₁ T₂ params₁ params₂ params₃ hRfail hpre h₁ h₂)

/-- Coercion: a faithful up-to transform is also an aggressive up-to transform
    (same `Rin`/`Rout`/precondition).  The exact target execution reaching the
    `Rout`-related `ρ''` witnesses the failure-free disjunct; the `CanFail` and
    target-WF conjuncts carry over unchanged.  This is the up-to generalization
    of `OverapproximatesWhen.toAggressivelyWhen`, and the lemma that lets the
    faithful S2U passes be composed with a genuinely-aggressive first pass. -/
theorem OverapproximatesUptoWhen.toAggressivelyUptoWhen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    {Rin Rout : Relation (Env P)}
    (h : OverapproximatesUptoWhen Rin Rout L₁ L₂ T pre params₁ params₂) :
    OverapproximatesAggressivelyUptoWhen Rin Rout L₁ L₂ T pre params₁ params₂ := by
  intro st st' ht hpre ρ₀ ρ₀' hRin hwf
  have hr := h st st' ht hpre ρ₀ ρ₀' hRin hwf
  refine ⟨fun ρ' hstar => ?_, fun lbl ρ' hstar => ?_, hr.2.1, hr.2.2⟩
  · exact .inr fun _ => (hr.1 ρ').1 hstar
  · exact .inr fun _ => (hr.1 ρ').2 lbl hstar

/-- Equality-specialization bridge: at `Rin = Rout = (· = ·)`,
    `OverapproximatesAggressivelyUptoWhen` coincides with
    `OverapproximatesAggressivelyWhen`.  Since `OverapproximatesAggressivelyWhen`
    is *defined* as exactly that specialization, this is definitional; the lemma
    is kept as a named bridge for callers that reason about the equality form. -/
theorem overapproximatesAggressivelyUptoWhen_eq_iff (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) :
    OverapproximatesAggressivelyUptoWhen (· = ·) (· = ·) L₁ L₂ T pre params₁ params₂ ↔
    OverapproximatesAggressivelyWhen L₁ L₂ T pre params₁ params₂ :=
  Iff.rfl

/-! ## Cross-family boundary joins

A structured-to-unstructured (S2U) pipeline chains passes of *two* different
correctness shapes: passes that only **prune paths** (an inserted `assume` blocks
a target path, so a source terminal may have no counterpart) are aggressive, while
passes that only **generate/rename variables** (the target store agrees with the
source only modulo fresh names) are faithful up-to.  The whole point of
`OverapproximatesAggressivelyUptoWhen` is that it is the common supertype into
which *both* coerce, so a mixed chain composes.

The two lemmas below are the ready-made joins for a mixed adjacency, each a thin
corollary of `comp_eq` after coercing both operands via
`OverapproximatesUptoWhen.toAggressivelyUptoWhen` /
`OverapproximatesAggressivelyWhen.toAggressivelyUptoWhen`.  They share a
`Rin = (· = ·)` (shared start) and conclude at output relation `Rout` — the
`RComp` from `comp_eq` collapses because one side is `(· = ·)`.

Note the **asymmetry** in their hypotheses, which is a real design fact rather than
an accident: `comp_eq`'s `hR₁fail` obligation always lands on the *first* stage's
output relation (the intermediate reachable env is only related to — not equal to —
the source terminal, so its failure-freedom must be recovered from that relation
before the second stage's failure-free reachability branch can fire).  When the
aggressive pass is placed **first** its output is `(· = ·)`, which preserves
failure-freedom for free, so `comp_uptoWhen` needs *no* extra hypothesis.  When the
faithful up-to pass is placed first, its output relation `Rout` carries the
obligation, so `comp_aggressivelyWhen` must take `hRoutFail`.  This is the formal
reason a path-pruning pass composes most freely at the front of the pipeline —
exactly where `InsertLoopInvariantAsserts` sits. -/

/-- Coercion: an equality-output aggressive transform is an aggressive-up-to
    transform at the diagonal `Rin = Rout = (· = ·)`.  The backward direction of
    `overapproximatesAggressivelyUptoWhen_eq_iff`, packaged as the aggressive
    analogue of `OverapproximatesUptoWhen.toAggressivelyUptoWhen` so that a
    faithful and an aggressive pass can be coerced into the same relation before
    composing. -/
theorem OverapproximatesAggressivelyWhen.toAggressivelyUptoWhen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (h : OverapproximatesAggressivelyWhen L₁ L₂ T pre params₁ params₂) :
    OverapproximatesAggressivelyUptoWhen (· = ·) (· = ·) L₁ L₂ T pre params₁ params₂ :=
  (overapproximatesAggressivelyUptoWhen_eq_iff L₁ L₂ T pre params₁ params₂).mpr h

/-- **Boundary join, aggressive-first.**  An equality-output *aggressive* pass
    followed by a faithful *up-to* pass composes to
    `OverapproximatesAggressivelyUptoWhen (· = ·) Rout`.  Because the first stage
    is equality-output, `comp_eq`'s failure-freedom side-condition is discharged by
    `id`, and the `RComp (· = ·) Rout` output collapses to `Rout`.  This is the
    join at the front of an S2U pipeline: the pruning pass (`InsertLoopInvariantAsserts`)
    first, then a variable-generating faithful pass (`nondetElim` / `hoist` /
    `stmtsToCFG`) up to an output relation `Rout` tracking the generated names. -/
theorem OverapproximatesAggressivelyWhen.comp_uptoWhen (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    {pre₁ : L₁.StmtT → Prop} {pre₂ : L₂.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    {Rout : Relation (Env P)}
    (hpre : ∀ st st', T₁ st = some st' → pre₁ st → pre₂ st')
    (h₁ : OverapproximatesAggressivelyWhen L₁ L₂ T₁ pre₁ params₁ params₂)
    (h₂ : OverapproximatesUptoWhen (· = ·) Rout L₂ L₃ T₂ pre₂ params₂ params₃) :
    OverapproximatesAggressivelyUptoWhen (· = ·) Rout L₁ L₃
      (fun s => T₁ s >>= T₂) pre₁ params₁ params₃ :=
  OverapproximatesAggressivelyUptoWhen.mono_out L₁ L₃ (fun s => T₁ s >>= T₂) pre₁ params₁ params₃
    (fun _ _ h => by obtain ⟨m, hEq, hR⟩ := h; subst hEq; exact hR)
    (OverapproximatesAggressivelyUptoWhen.comp_eq L₁ L₂ L₃ T₁ T₂ params₁ params₂ params₃
      (fun _ _ h => by subst h; exact id)
      hpre
      (OverapproximatesAggressivelyWhen.toAggressivelyUptoWhen L₁ L₂ T₁ pre₁ params₁ params₂ h₁)
      (OverapproximatesUptoWhen.toAggressivelyUptoWhen L₂ L₃ T₂ pre₂ params₂ params₃ h₂))

/-- **Boundary join, up-to-first.**  A faithful *up-to* pass followed by an
    equality-output *aggressive* pass, also concluding
    `OverapproximatesAggressivelyUptoWhen (· = ·) Rout`.  Unlike `comp_uptoWhen`,
    this needs `hRoutFail` — the up-to output relation preserves failure-freedom —
    because here `Rout` is the *first* stage's output relation, on which `comp_eq`'s
    `hR₁fail` obligation lands. -/
theorem OverapproximatesUptoWhen.comp_aggressivelyWhen (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    {pre₁ : L₁.StmtT → Prop} {pre₂ : L₂.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    {Rout : Relation (Env P)}
    (hRoutFail : ∀ a b, Rout a b → a.hasFailure = false → b.hasFailure = false)
    (hpre : ∀ st st', T₁ st = some st' → pre₁ st → pre₂ st')
    (h₁ : OverapproximatesUptoWhen (· = ·) Rout L₁ L₂ T₁ pre₁ params₁ params₂)
    (h₂ : OverapproximatesAggressivelyWhen L₂ L₃ T₂ pre₂ params₂ params₃) :
    OverapproximatesAggressivelyUptoWhen (· = ·) Rout L₁ L₃
      (fun s => T₁ s >>= T₂) pre₁ params₁ params₃ :=
  OverapproximatesAggressivelyUptoWhen.mono_out L₁ L₃ (fun s => T₁ s >>= T₂) pre₁ params₁ params₃
    (fun _ _ h => by obtain ⟨m, hR, hEq⟩ := h; subst hEq; exact hR)
    (OverapproximatesAggressivelyUptoWhen.comp_eq L₁ L₂ L₃ T₁ T₂ params₁ params₂ params₃
      hRoutFail
      hpre
      (OverapproximatesUptoWhen.toAggressivelyUptoWhen L₁ L₂ T₁ pre₁ params₁ params₂ h₁)
      (OverapproximatesAggressivelyWhen.toAggressivelyUptoWhen L₂ L₃ T₂ pre₂ params₂ params₃ h₂))

/-- `Underapproximates` identity: the identity transform under-approximates
    itself.  Dual of `overapproximates_id`. -/
theorem underapproximates_id (L₁ : Lang P) (params₁ : L₁.InitEnvWFParamsTy) :
    Underapproximates L₁ L₁ some params₁ params₁ := by
  intro st s' ht ρ₀ hinit
  simp at ht; subst ht
  exact ⟨fun ρ' => ⟨id, fun _ => id⟩, fun h => h, hinit⟩

/-- `SemanticallyEquivalent` identity: the identity transform is semantically
    equivalent to itself.  Follows from `overapproximates_id` and
    `underapproximates_id`. -/
theorem semanticallyEquivalent_id (L₁ : Lang P) (params₁ : L₁.InitEnvWFParamsTy) :
    SemanticallyEquivalent L₁ L₁ some params₁ params₁ :=
  ⟨overapproximates_id L₁ params₁, underapproximates_id L₁ params₁⟩


/-! ## Relating `Overapproximates`, `OverapproximatesWhen`, and their aggressive variants

The lemmas below organize the overapproximation family into a lattice of
implications:
- dropping the exactness requirement (`… → …Aggressively…`);
- strengthening the precondition (`strengthen`) -/

/-- `OverapproximatesWhen` implies `OverapproximatesAggressivelyWhen` (same
    precondition).  An exact transform that handles all preconditioned inputs
    is also an aggressive transform that handles them: the exact target
    execution reaching `ρ'` witnesses the `hasFailure = false` disjunct. -/
theorem OverapproximatesWhen.toAggressivelyWhen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (h : OverapproximatesWhen L₁ L₂ T pre params₁ params₂) :
    OverapproximatesAggressivelyWhen L₁ L₂ T pre params₁ params₂ := by
  intro st s' ht hpre ρ₀ ρ₀' hEq hswf
  subst hEq
  have hr := h st s' ht hpre ρ₀ ρ₀ rfl hswf
  refine ⟨?_, ?_, hr.2.1, hr.2.2⟩
  · intro ρ' hstar
    exact .inr (fun _ => by
      obtain ⟨ρ'', heq, hstar'⟩ := (hr.1 ρ').1 hstar; exact ⟨ρ'', heq, hstar'⟩)
  · intro lbl ρ' hstar
    exact .inr (fun _ => by
      obtain ⟨ρ'', heq, hstar'⟩ := (hr.1 ρ').2 lbl hstar; exact ⟨ρ'', heq, hstar'⟩)

/-- `Overapproximates` implies `OverapproximatesAggressively`. -/
theorem Overapproximates.toAggressive (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (h : Overapproximates L₁ L₂ T params₁ params₂) :
    OverapproximatesAggressively L₁ L₂ T params₁ params₂ :=
  OverapproximatesWhen.toAggressivelyWhen L₁ L₂ T (fun _ => True) params₁ params₂ h

/-- Precondition strengthening for `OverapproximatesWhen`: a relation that holds
    under `pre` also holds under any stronger precondition `pre'`. -/
theorem OverapproximatesWhen.strengthen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) {pre pre' : L₁.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (himp : ∀ st, pre' st → pre st)
    (h : OverapproximatesWhen L₁ L₂ T pre params₁ params₂) :
    OverapproximatesWhen L₁ L₂ T pre' params₁ params₂ := by
  intro st st' ht hpre' ρ₀ ρ₀' hR hswf
  exact h st st' ht (himp st hpre') ρ₀ ρ₀' hR hswf

/-- Precondition strengthening for `OverapproximatesAggressivelyWhen`. -/
theorem OverapproximatesAggressivelyWhen.strengthen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) {pre pre' : L₁.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (himp : ∀ st, pre' st → pre st)
    (h : OverapproximatesAggressivelyWhen L₁ L₂ T pre params₁ params₂) :
    OverapproximatesAggressivelyWhen L₁ L₂ T pre' params₁ params₂ := by
  intro st st' ht hpre' ρ₀ ρ₀' hR hswf
  exact h st st' ht (himp st hpre') ρ₀ ρ₀' hR hswf

/-- Precondition strengthening for `OverapproximatesAggressivelyUptoWhen`: a
    relation that holds under `pre` also holds under any stronger precondition
    `pre'`.  The up-to (input/output relation split) counterpart of
    `OverapproximatesAggressivelyWhen.strengthen`; both relations are held fixed. -/
theorem OverapproximatesAggressivelyUptoWhen.strengthen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) {pre pre' : L₁.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    {Rin Rout : Relation (Env P)}
    (himp : ∀ st, pre' st → pre st)
    (h : OverapproximatesAggressivelyUptoWhen Rin Rout L₁ L₂ T pre params₁ params₂) :
    OverapproximatesAggressivelyUptoWhen Rin Rout L₁ L₂ T pre' params₁ params₂ := by
  intro st st' ht hpre' ρ₀ ρ₀' hR hswf
  exact h st st' ht (himp st hpre') ρ₀ ρ₀' hR hswf

/-- An unconditional `Overapproximates` is the strongest case: it gives
    `OverapproximatesWhen` for ANY precondition. -/
theorem Overapproximates.toWhen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (h : Overapproximates L₁ L₂ T params₁ params₂) :
    OverapproximatesWhen L₁ L₂ T pre params₁ params₂ :=
  OverapproximatesWhen.strengthen L₁ L₂ T params₁ params₂ (fun _ _ => trivial) h

/-- An unconditional `OverapproximatesAggressively` likewise gives
    `OverapproximatesAggressivelyWhen` for any precondition. -/
theorem OverapproximatesAggressively.toWhen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (h : OverapproximatesAggressively L₁ L₂ T params₁ params₂) :
    OverapproximatesAggressivelyWhen L₁ L₂ T pre params₁ params₂ :=
  OverapproximatesAggressivelyWhen.strengthen L₁ L₂ T params₁ params₂ (fun _ _ => trivial) h

end OverapproxProps


/-- `EnvStoreAgree` is transitive: store agreement, failure-flag equality, and
factory equality each compose across a middle environment. -/
theorem EnvStoreAgree_trans {P : PureExpr} {ρ₁ ρ₂ ρ₃ : Env P}
    (h₁ : EnvStoreAgree ρ₁ ρ₂) (h₂ : EnvStoreAgree ρ₂ ρ₃) :
    EnvStoreAgree ρ₁ ρ₃ :=
  ⟨StoreAgreement.trans h₁.1 h₂.1, h₁.2.1.trans h₂.2.1, h₂.2.2.trans h₁.2.2⟩


/-! ## Structured statements-specific results -/

section StructuredStmts

variable {CmdT : Type} (evalCmd : EvalCmdParam P CmdT) (extendFactory : ExtendFactory P)
variable (isAtAssertFn : Config P CmdT → AssertId P → Prop)

omit [HasOps P] in
private theorem overapproximates_stmts_aux
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    {SParams : Type}
    (swf : SParams → Stmt P CmdT → Env P → Prop)
    (sp₁ sp₂ : SParams)
    (Inv : Env P → Prop)
    (hPres : ∀ {s : Stmt P CmdT} {ρ ρ' : Env P}, Inv ρ →
       StepStmtStar P evalCmd extendFactory (.stmt s ρ) (.terminal ρ') → Inv ρ')
    (hGate : ∀ {s : Stmt P CmdT} {ρ : Env P}, Inv ρ → swf sp₁ s ρ)
    (hsem : Overapproximates
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf)
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf) T sp₁ sp₂)
    (ss : List (Stmt P CmdT)) :
    ∀ (ss' : List (Stmt P CmdT)),
      ss.mapM T = some ss' →
      ∀ (ρ₀ ρ' : Env P),
        Inv ρ₀ →
        (StepStmtStar P evalCmd extendFactory (.stmts ss ρ₀) (.terminal ρ') →
         StepStmtStar P evalCmd extendFactory (.stmts ss' ρ₀) (.terminal ρ'))
        ∧
        (∀ lbl, StepStmtStar P evalCmd extendFactory (.stmts ss ρ₀) (.exiting lbl ρ') →
                StepStmtStar P evalCmd extendFactory (.stmts ss' ρ₀) (.exiting lbl ρ')) := by
  induction ss with
  | nil =>
    intro ss' hmap ρ₀ ρ' _
    have : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst this; exact ⟨id, fun _ => id⟩
  | cons s rest ih =>
    intro ss' hmap ρ₀ ρ' hwf
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    have wf_preserved : ∀ ρ₁ : Env P,
        StepStmtStar P evalCmd extendFactory (.stmt s ρ₀) (.terminal ρ₁) →
        Inv ρ₁ := by
      intro ρ₁ hterm_s
      exact hPres hwf hterm_s
    -- `Lang.imperative`'s `initEnvWF` unfolds to `WellFormedSemanticEval ρ.factory`,
    -- so `hwf` directly satisfies the source-side WF gate of `hsem`.
    have hsem_s : ∀ (ρ₁ : Env P),
        (StepStmtStar P evalCmd extendFactory (.stmt s ρ₀) (.terminal ρ₁) →
         StepStmtStar P evalCmd extendFactory (.stmt s' ρ₀) (.terminal ρ₁))
        ∧
        (∀ lbl, StepStmtStar P evalCmd extendFactory (.stmt s ρ₀) (.exiting lbl ρ₁) →
                StepStmtStar P evalCmd extendFactory (.stmt s' ρ₀) (.exiting lbl ρ₁)) := by
      intro ρ₁
      have hr := (hsem s s' hs trivial ρ₀ ρ₀ rfl (hGate hwf)).1 ρ₁
      exact ⟨fun h => by obtain ⟨ρ'', heq, hstar⟩ := hr.1 h; subst heq; exact hstar,
             fun lbl h => by obtain ⟨ρ'', heq, hstar⟩ := hr.2 lbl h; subst heq; exact hstar⟩
    constructor
    · intro hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          have ⟨ρ₁, hterm_s, hterm_rest⟩ := seq_reaches_terminal P evalCmd extendFactory hrest_exec
          have hwf := wf_preserved ρ₁ hterm_s
          exact ReflTrans_Transitive _ _ _ _
            (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀ ρ₁
              ((hsem_s ρ₁).1 hterm_s))
            ((ih rest' hrm ρ₁ ρ' hwf).1 hterm_rest)
    · intro lbl hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          match seq_reaches_exiting P evalCmd extendFactory hrest_exec with
          | .inl hexit_s =>
            exact .step _ _ _ .step_stmts_cons
              (ReflTrans_Transitive _ _ _ _ (seq_inner_star P evalCmd extendFactory _ _ rest'
                ((hsem_s ρ').2 lbl hexit_s))
                (.step _ _ _ .step_seq_exit (.refl _)))
          | .inr ⟨ρ₁, hterm_s, hexit_rest⟩ =>
            have hwf := wf_preserved ρ₁ hterm_s
            exact ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀ ρ₁
                ((hsem_s ρ₁).1 hterm_s))
              ((ih rest' hrm ρ₁ ρ' hwf).2 lbl hexit_rest)

omit [HasOps P] in
private theorem overapproximates_stmts_canfail
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    {SParams : Type}
    (swf : SParams → Stmt P CmdT → Env P → Prop)
    (sp₁ sp₂ : SParams)
    (Inv : Env P → Prop)
    (hPres : ∀ {s : Stmt P CmdT} {ρ ρ' : Env P}, Inv ρ →
       StepStmtStar P evalCmd extendFactory (.stmt s ρ) (.terminal ρ') → Inv ρ')
    (hGate : ∀ {s : Stmt P CmdT} {ρ : Env P}, Inv ρ → swf sp₁ s ρ)
    (hsem : Overapproximates
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf)
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf) T sp₁ sp₂)
    (ss : List (Stmt P CmdT))
    (ss' : List (Stmt P CmdT))
    (hmap : ss.mapM T = some ss')
    (ρ₀ : Env P)
    (hwf : Inv ρ₀)
    (hcf : ∃ cfg : Config P CmdT, cfg.getEnv.hasFailure = true ∧
      StepStmtStar P evalCmd extendFactory (.stmts ss ρ₀) cfg) :
    ∃ cfg' : Config P CmdT, cfg'.getEnv.hasFailure = true ∧
      StepStmtStar P evalCmd extendFactory (.stmts ss' ρ₀) cfg' := by
  induction ss generalizing ss' ρ₀ with
  | nil =>
    have : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst this
    obtain ⟨cfg, hfcfg, hstar⟩ := hcf
    exact ⟨cfg, hfcfg, hstar⟩
  | cons s rest ih =>
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    obtain ⟨cfg, hfcfg, hstar⟩ := hcf
    cases hstar with
    | refl =>
      -- cfg = .stmts (s :: rest) ρ₀, so cfg.getEnv = ρ₀, hasFailure = true
      exact ⟨.stmts (s' :: rest') ρ₀, hfcfg, .refl _⟩
    | step _ _ _ hstep hrest_exec => cases hstep with
      | step_stmts_cons =>
        match seq_canfail_prop hrest_exec hfcfg with
        | .inl ⟨cfg', hf', hstar'⟩ =>
          -- Failure happens in the first statement `s`.
          -- Use hsem's CanFail clause for statement `s`.
          have hsem_canfail := (hsem s s' hs trivial ρ₀ ρ₀ rfl (hGate hwf)).2.1
          have ⟨cfg_t, hf_t, hstar_t⟩ := hsem_canfail ⟨cfg', hf', hstar'⟩
          exact ⟨.seq cfg_t rest', hf_t,
            .step _ _ _ .step_stmts_cons
              (seq_inner_star P evalCmd extendFactory _ cfg_t rest' hstar_t)⟩
        | .inr ⟨ρ₁, hterm_s, cfg', hf', hstar_rest⟩ =>
          -- First statement terminates at ρ₁, failure is in the rest.
          have hwfρ₁ : Inv ρ₁ :=
            hPres hwf hterm_s
          -- Get terminal simulation for s → s'
          have hsem_s := (hsem s s' hs trivial ρ₀ ρ₀ rfl (hGate hwf)).1 ρ₁
          have ⟨ρ₁', heq₁, hterm_s'⟩ := hsem_s.1 hterm_s
          subst heq₁
          -- Recurse on the rest
          have ⟨cfg_rest, hf_rest, hstar_rest'⟩ :=
            ih rest' hrm ρ₁ hwfρ₁ ⟨cfg', hf', hstar_rest⟩
          exact ⟨cfg_rest, hf_rest,
            ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀ ρ₁ hterm_s')
              hstar_rest'⟩

/-! ### Compositionality of `Overapproximates` over statement lists

`overapproximates_stmts` lifts a per-statement overapproximation to whole
statement lists (block bodies).  If `T` overapproximates every individual
statement, then `fun ss => ss.mapM T` overapproximates the block obtained by
mapping `T` over the list.

Note that this lifting depends on finding an environment invariant
`Inv : Env P → Prop` — one that depends only on the `Env` and not on the
statement — that holds at block entry (`hGround`), is preserved across each
statement's execution (`hPres`), and implies the per-statement source
well-formedness for *every* statement (`hGate : Inv ρ → swf sp₁ s ρ`).
When no such statement-independent `Inv` can be found, these lemmas do not
apply and the compositionality has to be proven separately for that
well-formedness.
-/

omit [HasOps P] in
theorem overapproximates_stmts [HasIdent P] [HasVarsImp P CmdT]
    {Params : Type}
    (wf : Params → List (Stmt P CmdT) → Env P → Prop)
    (p₁ p₂ : Params)
    {SParams : Type}
    (swf : SParams → Stmt P CmdT → Env P → Prop)
    (sp₁ sp₂ : SParams)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    -- An abstract operational invariant on environments; the concrete
    -- `WellFormedSemanticEval ρ.factory` is one instance (with `hPres` from
    -- `star_preserves_wfEval`), but any `Inv` will do.
    (Inv : Env P → Prop)
    -- hGround: the block-level well-formedness establishes `Inv` at the initial env.
    (hGround : ∀ ss ρ, wf p₁ ss ρ → Inv ρ)
    -- hPres: `Inv` is preserved when a statement runs to a terminal state.
    (hPres : ∀ {s : Stmt P CmdT} {ρ ρ' : Env P}, Inv ρ →
       StepStmtStar P evalCmd extendFactory (.stmt s ρ) (.terminal ρ') → Inv ρ')
    -- hGate: `Inv` implies the statement-level source well-formedness `hsem` gates on.
    (hGate : ∀ {s : Stmt P CmdT} {ρ : Env P}, Inv ρ → swf sp₁ s ρ)
    -- the block-level well-formedness transfers along the transform.
    (hWF : ∀ ss ss' ρ, ss.mapM T = some ss' → wf p₁ ss ρ → wf p₂ ss' ρ)
    (hsem : Overapproximates
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf)
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf) T sp₁ sp₂) :
    Overapproximates
      (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn (wfPkg := ⟨Params, wf⟩))
      (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn (wfPkg := ⟨Params, wf⟩))
      (fun ss => ss.mapM T) p₁ p₂ := by
  intro ss ss' hmap _ ρ₀ ρ₀' heq hwf
  subst heq
  have hInv0 := hGround ss ρ₀ hwf
  have aux := overapproximates_stmts_aux evalCmd extendFactory isAtAssertFn T
    swf sp₁ sp₂ Inv hPres hGate hsem ss ss' hmap ρ₀
  refine ⟨fun ρ' => ⟨fun h => ⟨ρ', rfl, (aux ρ' hInv0).1 h⟩,
                      fun lbl h => ⟨ρ', rfl, (aux ρ' hInv0).2 lbl h⟩⟩, ?_, hWF ss ss' ρ₀ hmap hwf⟩
  -- CanFail preservation via the dedicated helper.
  intro ⟨cfg, hfcfg, hstar⟩
  exact overapproximates_stmts_canfail evalCmd extendFactory isAtAssertFn T swf sp₁ sp₂ Inv hPres hGate
    hsem ss ss' hmap ρ₀ hInv0 ⟨cfg, hfcfg, hstar⟩


/-! ### Compositionality of `OverapproximatesUpto` over statement lists

`overapproximatesUpto_stmts` is the state-relation (`OverapproximatesUpto R`)
analogue of `overapproximates_stmts`.  If `T` overapproximates every individual
statement *up to* `R` — source and target initial/final envs related by `R`
rather than being equal — then `fun ss => ss.mapM T` overapproximates the whole
block up to `R`.

Because `R` may map the source env to a *different* target env, the empty-list
base case can no longer just reuse the source env: it must produce the target
env's failure flag and well-formedness from `R`.  We therefore require `R` to
preserve those two invariants (`hRfail`, `hRwf`); for the equality relation both
are trivial, recovering `overapproximates_stmts` as the special case. -/

omit [HasOps P] in
private theorem overapproximatesUpto_stmts_aux
    (R : Relation (Env P))
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    {SParams : Type}
    (swf : SParams → Stmt P CmdT → Env P → Prop)
    (sp₁ sp₂ : SParams)
    (Inv : Env P → Prop)
    (hPres : ∀ {s : Stmt P CmdT} {ρ ρ' : Env P}, Inv ρ →
       StepStmtStar P evalCmd extendFactory (.stmt s ρ) (.terminal ρ') → Inv ρ')
    (hGate : ∀ {s : Stmt P CmdT} {ρ : Env P}, Inv ρ → swf sp₁ s ρ)
    (hsem : OverapproximatesUpto R
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf)
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf) T sp₁ sp₂)
    (ss : List (Stmt P CmdT)) :
    ∀ (ss' : List (Stmt P CmdT)),
      ss.mapM T = some ss' →
      ∀ (ρ₀ ρ₀' ρ' : Env P),
        R ρ₀ ρ₀' →
        Inv ρ₀ →
        (StepStmtStar P evalCmd extendFactory (.stmts ss ρ₀) (.terminal ρ') →
         ∃ ρ'', R ρ' ρ'' ∧
           StepStmtStar P evalCmd extendFactory (.stmts ss' ρ₀') (.terminal ρ''))
        ∧
        (∀ lbl, StepStmtStar P evalCmd extendFactory (.stmts ss ρ₀) (.exiting lbl ρ') →
                ∃ ρ'', R ρ' ρ'' ∧
                  StepStmtStar P evalCmd extendFactory (.stmts ss' ρ₀') (.exiting lbl ρ'')) := by
  induction ss with
  | nil =>
    intro ss' hmap ρ₀ ρ₀' ρ' hR _
    have hss' : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst hss'
    constructor
    · intro h
      cases h with
      | step _ _ _ hstep hrest => cases hstep with
        | step_stmts_nil => cases hrest with
          | refl => exact ⟨ρ₀', hR, .step _ _ _ .step_stmts_nil (.refl _)⟩
          | step _ _ _ h _ => exact nomatch h
    · intro lbl h
      cases h with
      | step _ _ _ hstep hrest => cases hstep with
        | step_stmts_nil => cases hrest with
          | step _ _ _ h _ => exact nomatch h
  | cons s rest ih =>
    intro ss' hmap ρ₀ ρ₀' ρ' hR hwf
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    have wf_preserved : ∀ ρ₁ : Env P,
        StepStmtStar P evalCmd extendFactory (.stmt s ρ₀) (.terminal ρ₁) →
        Inv ρ₁ := by
      intro ρ₁ hterm_s
      exact hPres hwf hterm_s
    -- Head simulation up to `R`: source `s` from `ρ₀` and target `s'` from `ρ₀'`.
    have hsem_s := hsem s s' hs trivial ρ₀ ρ₀' hR (hGate hwf)
    constructor
    · intro hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          have ⟨ρ₁, hterm_s, hterm_rest⟩ := seq_reaches_terminal P evalCmd extendFactory hrest_exec
          have hwf := wf_preserved ρ₁ hterm_s
          have ⟨ρ₁', hR₁, hterm_s'⟩ := (hsem_s.1 ρ₁).1 hterm_s
          have ⟨ρ'', hR'', hrest'⟩ := (ih rest' hrm ρ₁ ρ₁' ρ' hR₁ hwf).1 hterm_rest
          exact ⟨ρ'', hR'', ReflTrans_Transitive _ _ _ _
            (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀' ρ₁' hterm_s') hrest'⟩
    · intro lbl hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          match seq_reaches_exiting P evalCmd extendFactory hrest_exec with
          | .inl hexit_s =>
            have ⟨ρ'', hR'', hexit_s'⟩ := (hsem_s.1 ρ').2 lbl hexit_s
            exact ⟨ρ'', hR'', .step _ _ _ .step_stmts_cons
              (ReflTrans_Transitive _ _ _ _
                (seq_inner_star P evalCmd extendFactory _ _ rest' hexit_s')
                (.step _ _ _ .step_seq_exit (.refl _)))⟩
          | .inr ⟨ρ₁, hterm_s, hexit_rest⟩ =>
            have hwf := wf_preserved ρ₁ hterm_s
            have ⟨ρ₁', hR₁, hterm_s'⟩ := (hsem_s.1 ρ₁).1 hterm_s
            have ⟨ρ'', hR'', hexit_rest'⟩ := (ih rest' hrm ρ₁ ρ₁' ρ' hR₁ hwf).2 lbl hexit_rest
            exact ⟨ρ'', hR'', ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀' ρ₁' hterm_s') hexit_rest'⟩

omit [HasOps P] in
private theorem overapproximatesUpto_stmts_canfail
    (R : Relation (Env P))
    (hRfail : ∀ ρ ρ' : Env P, R ρ ρ' → ρ.hasFailure = true → ρ'.hasFailure = true)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    {SParams : Type}
    (swf : SParams → Stmt P CmdT → Env P → Prop)
    (sp₁ sp₂ : SParams)
    (Inv : Env P → Prop)
    (hPres : ∀ {s : Stmt P CmdT} {ρ ρ' : Env P}, Inv ρ →
       StepStmtStar P evalCmd extendFactory (.stmt s ρ) (.terminal ρ') → Inv ρ')
    (hGate : ∀ {s : Stmt P CmdT} {ρ : Env P}, Inv ρ → swf sp₁ s ρ)
    (hsem : OverapproximatesUpto R
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf)
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf) T sp₁ sp₂)
    (ss : List (Stmt P CmdT)) :
    ∀ (ss' : List (Stmt P CmdT)),
      ss.mapM T = some ss' →
      ∀ (ρ₀ ρ₀' : Env P),
        R ρ₀ ρ₀' →
        Inv ρ₀ →
        (∃ cfg : Config P CmdT, cfg.getEnv.hasFailure = true ∧
          StepStmtStar P evalCmd extendFactory (.stmts ss ρ₀) cfg) →
        ∃ cfg' : Config P CmdT, cfg'.getEnv.hasFailure = true ∧
          StepStmtStar P evalCmd extendFactory (.stmts ss' ρ₀') cfg' := by
  induction ss with
  | nil =>
    intro ss' hmap ρ₀ ρ₀' hR _ hcf
    have hss' : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst hss'
    obtain ⟨cfg, hfcfg, hstar⟩ := hcf
    -- All configs reachable from `.stmts [] ρ₀` have env `ρ₀`, so it must be
    -- `ρ₀` that carries the failure; transport it to `ρ₀'` via `hRfail`.
    have hρ₀ : ρ₀.hasFailure = true := by
      cases hstar with
      | refl => simpa [Config.getEnv] using hfcfg
      | step _ _ _ hstep hrest => cases hstep with
        | step_stmts_nil => cases hrest with
          | refl => simpa [Config.getEnv] using hfcfg
          | step _ _ _ h _ => exact nomatch h
    exact ⟨.stmts [] ρ₀', by simpa [Config.getEnv] using hRfail ρ₀ ρ₀' hR hρ₀, .refl _⟩
  | cons s rest ih =>
    intro ss' hmap ρ₀ ρ₀' hR hwf hcf
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    obtain ⟨cfg, hfcfg, hstar⟩ := hcf
    cases hstar with
    | refl =>
      -- `cfg = .stmts (s :: rest) ρ₀` already fails ⇒ head `s` can fail from `ρ₀`.
      have hcanfail_s : CanFail (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) s ρ₀ :=
        ⟨.stmt s ρ₀, by simpa [Config.getEnv] using hfcfg, .refl _⟩
      have ⟨cfg_t, hf_t, hstar_t⟩ := (hsem s s' hs trivial ρ₀ ρ₀' hR (hGate hwf)).2.1 hcanfail_s
      exact ⟨.seq cfg_t rest', by simpa [Config.getEnv] using hf_t,
        .step _ _ _ .step_stmts_cons (seq_inner_star P evalCmd extendFactory _ cfg_t rest' hstar_t)⟩
    | step _ _ _ hstep hrest_exec => cases hstep with
      | step_stmts_cons =>
        match seq_canfail_prop hrest_exec hfcfg with
        | .inl ⟨cfg', hf', hstar'⟩ =>
          -- Failure occurs while executing the head `s`.
          have ⟨cfg_t, hf_t, hstar_t⟩ :=
            (hsem s s' hs trivial ρ₀ ρ₀' hR (hGate hwf)).2.1 ⟨cfg', hf', hstar'⟩
          exact ⟨.seq cfg_t rest', by simpa [Config.getEnv] using hf_t,
            .step _ _ _ .step_stmts_cons (seq_inner_star P evalCmd extendFactory _ cfg_t rest' hstar_t)⟩
        | .inr ⟨ρ₁, hterm_s, cfg', hf', hstar_rest⟩ =>
          -- Head terminates at `ρ₁`; failure is in the rest.  Simulate the head
          -- up to `R` (yielding `ρ₁'`) and recurse from the related env.
          have hwfρ₁ := hPres hwf hterm_s
          have ⟨ρ₁', hR₁, hterm_s'⟩ := ((hsem s s' hs trivial ρ₀ ρ₀' hR (hGate hwf)).1 ρ₁).1 hterm_s
          have ⟨cfg_rest, hf_rest, hstar_rest'⟩ :=
            ih rest' hrm ρ₁ ρ₁' hR₁ hwfρ₁ ⟨cfg', hf', hstar_rest⟩
          exact ⟨cfg_rest, hf_rest,
            ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀' ρ₁' hterm_s')
              hstar_rest'⟩

omit [HasOps P] in
/-- Compositionality of `OverapproximatesUpto` over statement lists.

The state-relation analogue of `overapproximates_stmts`: if `T` overapproximates
every individual statement up to `R`, then `fun ss => ss.mapM T` overapproximates
the whole block up to `R`.  `hRfail` requires `R` to preserve the failure flag,
which is what the empty-block case needs. -/
theorem overapproximatesUpto_stmts [HasIdent P] [HasVarsImp P CmdT]
    {Params : Type}
    (wf : Params → List (Stmt P CmdT) → Env P → Prop)
    (p₁ p₂ : Params)
    {SParams : Type}
    (swf : SParams → Stmt P CmdT → Env P → Prop)
    (sp₁ sp₂ : SParams)
    (R : Relation (Env P))
    -- Precondition on R: it must not make the target program silently succeed.
    (hRfail : ∀ ρ ρ' : Env P,
      R ρ ρ' → ρ.hasFailure = true → ρ'.hasFailure = true)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (Inv : Env P → Prop)
    (hGround : ∀ ss ρ, wf p₁ ss ρ → Inv ρ)
    (hPres : ∀ {s : Stmt P CmdT} {ρ ρ' : Env P}, Inv ρ →
       StepStmtStar P evalCmd extendFactory (.stmt s ρ) (.terminal ρ') → Inv ρ')
    (hGate : ∀ {s : Stmt P CmdT} {ρ : Env P}, Inv ρ → swf sp₁ s ρ)
    -- block-level well-formedness transfers along the transform and `R`.
    (hWF : ∀ ss ss' ρ ρ', ss.mapM T = some ss' → R ρ ρ' → wf p₁ ss ρ → wf p₂ ss' ρ')
    (hsem : OverapproximatesUpto R
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf)
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf) T sp₁ sp₂) :
    OverapproximatesUpto R
      (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn (wfPkg := ⟨Params, wf⟩))
      (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn (wfPkg := ⟨Params, wf⟩))
      (fun ss => ss.mapM T) p₁ p₂ := by
  intro ss ss' hmap _ ρ₀ ρ₀' hR hwf
  have hInv0 := hGround ss ρ₀ hwf
  refine ⟨fun ρ' => ⟨fun h => ?_, fun lbl h => ?_⟩, ?_, hWF ss ss' ρ₀ ρ₀' hmap hR hwf⟩
  · exact (overapproximatesUpto_stmts_aux evalCmd extendFactory isAtAssertFn R T
      swf sp₁ sp₂ Inv hPres hGate hsem ss ss' hmap ρ₀ ρ₀' ρ' hR hInv0).1 h
  · exact (overapproximatesUpto_stmts_aux evalCmd extendFactory isAtAssertFn R T
      swf sp₁ sp₂ Inv hPres hGate hsem ss ss' hmap ρ₀ ρ₀' ρ' hR hInv0).2 lbl h
  · intro ⟨cfg, hfcfg, hstar⟩
    exact overapproximatesUpto_stmts_canfail evalCmd extendFactory isAtAssertFn R hRfail T
      swf sp₁ sp₂ Inv hPres hGate hsem ss ss' hmap ρ₀ ρ₀' hR hInv0 ⟨cfg, hfcfg, hstar⟩


/-! ## Aggressive statement-list overapproximation

The lemmas below are the aggressive analogues of `overapproximates_stmts_*`.
They use `OverapproximatesAggressively`, under which the target program is
allowed to assert-fail spuriously. -/

omit [HasOps P] in
/-- Lifting `CanFail` from a head statement to the enclosing block (cons of a
    statement list): if the head `s` can fail from `ρ₀`, so can `s :: ss`. -/
theorem canFail_head_to_block
    (s : Stmt P CmdT) (ss : List (Stmt P CmdT)) (ρ₀ : Env P)
    (h : CanFail (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) s ρ₀) :
    CanFailBlock evalCmd extendFactory (s :: ss) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := h
  refine ⟨.seq cfg ss, ?_, ?_⟩
  · simp [Config.getEnv]; exact hfail
  · exact ReflTrans_Transitive _ _ _ _
      (.step _ _ _ .step_stmts_cons (.refl _))
      (seq_inner_star P evalCmd extendFactory _ _ ss hreach)

omit [HasOps P] in
private theorem overapproximatesAggressively_stmts_canfail
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    {SParams : Type}
    (swf : SParams → Stmt P CmdT → Env P → Prop)
    (sp₁ sp₂ : SParams)
    (Inv : Env P → Prop)
    (hPres : ∀ {s : Stmt P CmdT} {ρ ρ' : Env P}, Inv ρ →
       StepStmtStar P evalCmd extendFactory (.stmt s ρ) (.terminal ρ') → Inv ρ')
    (hGate : ∀ {s : Stmt P CmdT} {ρ : Env P}, Inv ρ → swf sp₁ s ρ)
    (hsem : OverapproximatesAggressively
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf)
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf) T sp₁ sp₂)
    (ss : List (Stmt P CmdT))
    (ss' : List (Stmt P CmdT))
    (hmap : ss.mapM T = some ss')
    (ρ₀ : Env P)
    (hwf : Inv ρ₀)
    (hcf : ∃ cfg : Config P CmdT, cfg.getEnv.hasFailure = true ∧
      StepStmtStar P evalCmd extendFactory (.stmts ss ρ₀) cfg) :
    ∃ cfg' : Config P CmdT, cfg'.getEnv.hasFailure = true ∧
      StepStmtStar P evalCmd extendFactory (.stmts ss' ρ₀) cfg' := by
  induction ss generalizing ss' ρ₀ with
  | nil =>
    have : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst this
    obtain ⟨cfg, hfcfg, hstar⟩ := hcf
    exact ⟨cfg, hfcfg, hstar⟩
  | cons s rest ih =>
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    obtain ⟨cfg, hfcfg, hstar⟩ := hcf
    cases hstar with
    | refl =>
      exact ⟨.stmts (s' :: rest') ρ₀, hfcfg, .refl _⟩
    | step _ _ _ hstep hrest_exec => cases hstep with
      | step_stmts_cons =>
        match seq_canfail_prop hrest_exec hfcfg with
        | .inl ⟨cfg', hf', hstar'⟩ =>
          -- Failure in the head `s`: use aggressive fail preservation (`.2.2.1`).
          have hsem_canfail := (OverapproximatesAggressivelyWhen.flat_apply hsem s s' hs trivial ρ₀ (hGate hwf)).2.2.1
          have ⟨cfg_t, hf_t, hstar_t⟩ := hsem_canfail ⟨cfg', hf', hstar'⟩
          exact ⟨.seq cfg_t rest', hf_t,
            .step _ _ _ .step_stmts_cons
              (seq_inner_star P evalCmd extendFactory _ cfg_t rest' hstar_t)⟩
        | .inr ⟨ρ₁, hterm_s, cfg', hf', hstar_rest⟩ =>
          have hwfρ₁ : Inv ρ₁ :=
            hPres hwf hterm_s
          -- The head's terminal guarantee is a disjunction under `hsem` (`.1`).
          match (OverapproximatesAggressivelyWhen.flat_apply hsem s s' hs trivial ρ₀ (hGate hwf)).1 ρ₁ hterm_s with
          | .inl canfail_s' =>
            obtain ⟨cfg'', hf'', hreach''⟩ := canfail_s'
            exact ⟨.seq cfg'' rest', by simp [Config.getEnv]; exact hf'',
              .step _ _ _ .step_stmts_cons
                (seq_inner_star P evalCmd extendFactory _ cfg'' rest' hreach'')⟩
          | .inr hterm_s' =>
            by_cases hf₁ : ρ₁.hasFailure = false
            · -- Head terminates without failure at ρ₁; recurse on the tail.
              have ⟨cfg_rest, hf_rest, hstar_rest'⟩ :=
                ih rest' hrm ρ₁ hwfρ₁ ⟨cfg', hf', hstar_rest⟩
              exact ⟨cfg_rest, hf_rest,
                ReflTrans_Transitive _ _ _ _
                  (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                  hstar_rest'⟩
            · -- ρ₁ already has a failure ⇒ the head can fail ⇒ so can `s'`.
              have hf₁' : ρ₁.hasFailure = true := by
                cases h : ρ₁.hasFailure <;> simp_all
              have hcanfail_s :
                  CanFail (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) s ρ₀ :=
                ⟨.terminal ρ₁, by simp [Config.getEnv]; exact hf₁', hterm_s⟩
              have ⟨cfg'', hf'', hreach''⟩ := (OverapproximatesAggressivelyWhen.flat_apply hsem s s' hs trivial ρ₀ (hGate hwf)).2.2.1 hcanfail_s
              exact ⟨.seq cfg'' rest', by simp [Config.getEnv]; exact hf'',
                .step _ _ _ .step_stmts_cons
                  (seq_inner_star P evalCmd extendFactory _ cfg'' rest' hreach'')⟩

private theorem overapproximatesAggressively_stmts_aux
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    {SParams : Type}
    (swf : SParams → Stmt P CmdT → Env P → Prop)
    (sp₁ sp₂ : SParams)
    (Inv : Env P → Prop)
    (hPres : ∀ {s : Stmt P CmdT} {ρ ρ' : Env P}, Inv ρ →
       StepStmtStar P evalCmd extendFactory (.stmt s ρ) (.terminal ρ') → Inv ρ')
    (hGate : ∀ {s : Stmt P CmdT} {ρ : Env P}, Inv ρ → swf sp₁ s ρ)
    (hsem : OverapproximatesAggressively
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf)
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf) T sp₁ sp₂)
    (ss : List (Stmt P CmdT)) :
    ∀ (ss' : List (Stmt P CmdT)),
      ss.mapM T = some ss' →
      ∀ (ρ₀ ρ' : Env P),
        Inv ρ₀ →
        (StepStmtStar P evalCmd extendFactory (.stmts ss ρ₀) (.terminal ρ') →
          CanFailBlock evalCmd extendFactory ss' ρ₀ ∨
          (ρ'.hasFailure = false →
            StepStmtStar P evalCmd extendFactory (.stmts ss' ρ₀) (.terminal ρ')))
        ∧
        (∀ lbl, StepStmtStar P evalCmd extendFactory (.stmts ss ρ₀) (.exiting lbl ρ') →
          CanFailBlock evalCmd extendFactory ss' ρ₀ ∨
          (ρ'.hasFailure = false →
            StepStmtStar P evalCmd extendFactory (.stmts ss' ρ₀) (.exiting lbl ρ'))) := by
  induction ss with
  | nil =>
    intro ss' hmap ρ₀ ρ' _
    have : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst this; exact ⟨fun h => .inr (fun _ => h), fun lbl h => .inr (fun _ => h)⟩
  | cons s rest ih =>
    intro ss' hmap ρ₀ ρ' hwf
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    have wf_preserved : ∀ ρ₁ : Env P,
        StepStmtStar P evalCmd extendFactory (.stmt s ρ₀) (.terminal ρ₁) →
        Inv ρ₁ := by
      intro ρ₁ hterm_s
      exact hPres hwf hterm_s
    have ⟨hsem_term, hsem_exit, hsem_fail, _hsem_swf⟩ :=
      OverapproximatesAggressivelyWhen.flat_apply hsem s s' hs trivial ρ₀ (hGate hwf)
    -- Common pattern: a failing intermediate env makes the head, hence the whole
    -- transformed block, able to fail.
    have canfail_from_failure : ∀ (ρ₁ : Env P),
        StepStmtStar P evalCmd extendFactory (.stmt s ρ₀) (.terminal ρ₁) →
        ρ₁.hasFailure = true →
        CanFailBlock evalCmd extendFactory (s' :: rest') ρ₀ := by
      intro ρ₁ hterm_s hf₁
      have hcanfail_s :
          CanFail (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) s ρ₀ :=
        ⟨.terminal ρ₁, by simp [Config.getEnv]; exact hf₁, hterm_s⟩
      exact canFail_head_to_block evalCmd extendFactory isAtAssertFn s' rest' ρ₀
        (hsem_fail hcanfail_s)
    constructor
    · -- Terminal case
      intro hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          have ⟨ρ₁, hterm_s, hterm_rest⟩ := seq_reaches_terminal P evalCmd extendFactory hrest_exec
          have hwf := wf_preserved ρ₁ hterm_s
          match hsem_term ρ₁ hterm_s with
          | .inl canfail_s' =>
            exact .inl (canFail_head_to_block evalCmd extendFactory isAtAssertFn s' rest' ρ₀ canfail_s')
          | .inr hterm_s' =>
            by_cases hf₁ : ρ₁.hasFailure = false
            · match (ih rest' hrm ρ₁ ρ' hwf).1 hterm_rest with
              | .inl canfail_rest' =>
                obtain ⟨cfg', hf', hreach'⟩ := canfail_rest'
                exact .inl ⟨cfg', hf',
                  ReflTrans_Transitive _ _ _ _
                    (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                    hreach'⟩
              | .inr hterm_rest' =>
                exact .inr fun hf =>
                  ReflTrans_Transitive _ _ _ _
                    (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                    (hterm_rest' hf)
            · have hf₁' : ρ₁.hasFailure = true := by
                cases h : ρ₁.hasFailure <;> simp_all
              exact .inl (canfail_from_failure ρ₁ hterm_s hf₁')
    · -- Exiting case
      intro lbl hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          match seq_reaches_exiting P evalCmd extendFactory hrest_exec with
          | .inl hexit_s =>
            match hsem_exit lbl ρ' hexit_s with
            | .inl canfail_s' =>
              exact .inl (canFail_head_to_block evalCmd extendFactory isAtAssertFn s' rest' ρ₀ canfail_s')
            | .inr hexit_s' =>
              exact .inr fun hf =>
                .step _ _ _ .step_stmts_cons
                  (ReflTrans_Transitive _ _ _ _ (seq_inner_star P evalCmd extendFactory _ _ rest'
                    (hexit_s' hf))
                    (.step _ _ _ .step_seq_exit (.refl _)))
          | .inr ⟨ρ₁, hterm_s, hexit_rest⟩ =>
            have hwf := wf_preserved ρ₁ hterm_s
            match hsem_term ρ₁ hterm_s with
            | .inl canfail_s' =>
              exact .inl (canFail_head_to_block evalCmd extendFactory isAtAssertFn s' rest' ρ₀ canfail_s')
            | .inr hterm_s' =>
              match (ih rest' hrm ρ₁ ρ' hwf).2 lbl hexit_rest with
              | .inl canfail_rest' =>
                by_cases hf₁ : ρ₁.hasFailure = false
                · obtain ⟨cfg', hf', hreach'⟩ := canfail_rest'
                  exact .inl ⟨cfg', hf',
                    ReflTrans_Transitive _ _ _ _
                      (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                      hreach'⟩
                · have hf₁' : ρ₁.hasFailure = true := by
                    cases h : ρ₁.hasFailure <;> simp_all
                  exact .inl (canfail_from_failure ρ₁ hterm_s hf₁')
              | .inr hexit_rest' =>
                exact .inr fun hf => by
                  by_cases hf₁ : ρ₁.hasFailure = false
                  · exact ReflTrans_Transitive _ _ _ _
                      (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                      (hexit_rest' hf)
                  · exfalso
                    have hf₁' : ρ₁.hasFailure = true := by
                      cases h : ρ₁.hasFailure <;> simp_all
                    have hf_ρ' : ρ'.hasFailure = true :=
                      StepStmtStar_hasFailure_monotone hexit_rest hf₁'
                    exact absurd hf (by simp [hf_ρ'])

/-- Compositionality of `OverapproximatesAggressively` over statement lists.

The aggressive analogue of `overapproximates_stmts`: if `T` aggressively
overapproximates every individual statement, then `fun ss => ss.mapM T`
aggressively overapproximates the whole block.
-/
theorem overapproximatesAggressively_stmts [HasIdent P] [HasVarsImp P CmdT]
    {Params : Type}
    (wf : Params → List (Stmt P CmdT) → Env P → Prop)
    (p₁ p₂ : Params)
    {SParams : Type}
    (swf : SParams → Stmt P CmdT → Env P → Prop)
    (sp₁ sp₂ : SParams)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (Inv : Env P → Prop)
    (hGround : ∀ ss ρ, wf p₁ ss ρ → Inv ρ)
    (hPres : ∀ {s : Stmt P CmdT} {ρ ρ' : Env P}, Inv ρ →
       StepStmtStar P evalCmd extendFactory (.stmt s ρ) (.terminal ρ') → Inv ρ')
    (hGate : ∀ {s : Stmt P CmdT} {ρ : Env P}, Inv ρ → swf sp₁ s ρ)
    (hWF : ∀ ss ss' ρ, ss.mapM T = some ss' → wf p₁ ss ρ → wf p₂ ss' ρ)
    (hsem : OverapproximatesAggressively
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf)
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn SParams swf) T sp₁ sp₂) :
    OverapproximatesAggressively
      (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn (wfPkg := ⟨Params, wf⟩))
      (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn (wfPkg := ⟨Params, wf⟩))
      (fun ss => ss.mapM T) p₁ p₂ := by
  intro ss ss' hmap _ ρ₀ ρ₀' hEq hwf
  subst hEq
  have hInv0 := hGround ss ρ₀ hwf
  refine ⟨fun ρ' hstar => ?_, fun lbl ρ' hstar => ?_, ?_, hWF ss ss' ρ₀ hmap hwf⟩
  · rcases (overapproximatesAggressively_stmts_aux evalCmd extendFactory isAtAssertFn T
      swf sp₁ sp₂ Inv hPres hGate hsem ss ss' hmap ρ₀ ρ' hInv0).1 hstar with hcf | hstep
    · exact .inl hcf
    · exact .inr fun hf => ⟨ρ', rfl, hstep hf⟩
  · rcases (overapproximatesAggressively_stmts_aux evalCmd extendFactory isAtAssertFn T
      swf sp₁ sp₂ Inv hPres hGate hsem ss ss' hmap ρ₀ ρ' hInv0).2 lbl hstar with hcf | hstep
    · exact .inl hcf
    · exact .inr fun hf => ⟨ρ', rfl, hstep hf⟩
  · intro ⟨cfg, hfcfg, hstar⟩
    exact overapproximatesAggressively_stmts_canfail evalCmd extendFactory isAtAssertFn T
      swf sp₁ sp₂ Inv hPres hGate hsem ss ss' hmap ρ₀ hInv0
      ⟨cfg, hfcfg, hstar⟩

end StructuredStmts

end Transform
end Specification
end Imperative

end -- public section
