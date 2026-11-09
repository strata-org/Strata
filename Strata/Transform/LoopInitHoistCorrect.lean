/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CmdSemantics
public import Strata.Transform.LoopInitHoistProps
public import Strata.Transform.DetToKleeneCorrect
public import Strata.Transform.NondetElimCorrect
public import Strata.Transform.StructuredToUnstructuredCorrect
public import Strata.Transform.CoreTransformProps

import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.Cmd
import all Strata.Util.ListUtils
import all Strata.Util.ListUtilsProps
import all Strata.Transform.LoopInitHoistProps
import all Strata.Transform.DetToKleeneCorrect
import all Strata.Transform.NondetElimCorrect
import all Strata.Transform.StructuredToUnstructuredCorrect

/-! # Loop-init hoist: infrastructure + correctness

The complete correctness development for the loop-init hoist pass
(`Block.hoistLoopPrefixInits`), the MIDDLE stage of the structured-to-unstructured
pipeline (`nondetElim` → **`hoistLoopPrefixInits`** → `stmtsToCFG`).  It builds on
the pass-output facts from `LoopInitHoistProps`.

Key results:
  * Composition facts used by the pipeline — `Stmt`/`Block.nondetElimM_initVars_nodup`
    (the `nondetElim` output keeps unique initializers) and the
    `*_exitsCoveredByBlocks` lift/hoist pairs.
  * Trace simulation — `LoopInitHoist.overapproximatesTraces`: every finite source
    trace is matched under `Trace.WithWF` matching, and terminal and exiting environments
    are related by `EnvStoreAgree`.

The whole-pipeline soundness capstone chains this stage's simulation with the
other two passes'.  Generic, transformation-agnostic store/run helpers live in
`CoreTransformProps`. -/

public section

namespace Imperative

/-! ## Proof structure

The store relation is `StoreAgreement` (semantics preservation *modulo
hoisted variables*), not exact pointwise equality: the hoisting pass lifts
loop-body inits to a prelude, so the hoisted store legitimately carries entries
the source store does not define.
`StoreAgreement σ_src σ_h` constrains only source-defined variables, leaving
those hoisted slots (and projected loop-locals) unconstrained.

The proof of `LoopInitHoist.overapproximatesTraces` is a mutual structural
induction on the source block (`Stmt.hoistP_trace_sim` /
`Block.hoistP_trace_sim`), dispatching each `.loop` arm via `loopHoistTraceSim`
after running the hoisted prelude.
-/

open StringGenState (GenStep) in
/-- Classification of an `initVars` element of the post-order pass output:
either an ORIGINAL source init (a member of the source `initVars` carrier
`src`), or a FRESH generator name (`HasIdent.ident str` for a string `str`
captured in the output state `σ'` but absent from the input state `σ`).  The
fresh disjunct additionally records that `str` carries the hoist pass's gen
kind `Q` (`Q str`), which the freshly generated carrier names satisfy by the gen
witness `hQgen`.  Instantiating `Q := String.HasUnderscoreDigitSuffix` recovers
the blanket generator-suffix statement. -/
def HoistInitClass {P : PureExpr} [HasIdent P] (Q : String → Prop) (src : List P.Ident) (σ σ' :
    StringGenState) (x : P.Ident) : Prop :=
  (x ∈ src) ∨
  (∃ str : String, x = HasIdent.ident str
    ∧ str ∈ StringGenState.stringGens σ'
    ∧ str ∉ StringGenState.stringGens σ
    ∧ Q str)

open StringGenState (GenStep) in
/-- Two classified `initVars` carriers from consecutive sub-passes are disjoint:
originals are disjoint by `uniqueInits` and suffix-free by `h_src_shapefree`;
fresh names are suffix-shaped and captured in disjoint state windows.  All four
cross-class collisions are impossible. -/
private theorem hoistInitClass_disjoint {P : PureExpr} [HasIdent P] [LawfulHasIdent P] {Q : String → Prop}
    (src₁ src₂ : List P.Ident) (σ σmid σ' : StringGenState)
    (h_src_disjoint : ∀ a ∈ src₁, ∀ b ∈ src₂, a ≠ b)
    (h_sf₁ : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ src₁)
    (h_sf₂ : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ src₂)
    (L₁ L₂ : List P.Ident)
    (hc₁ : ∀ x ∈ L₁, HoistInitClass Q src₁ σ σmid x)
    (hc₂ : ∀ x ∈ L₂, HoistInitClass Q src₂ σmid σ' x) :
    ∀ a ∈ L₁, ∀ b ∈ L₂, a ≠ b := by
  intro a ha b hb hab
  subst hab
  rcases hc₁ a ha with h_o₁ | ⟨str₁, hstr₁_eq, hstr₁_in, hstr₁_not, hstr₁_Q⟩
  · rcases hc₂ a hb with h_o₂ | ⟨str₂, hstr₂_eq, hstr₂_in, _, hstr₂_Q⟩
    · exact h_src_disjoint a h_o₁ a h_o₂ rfl
    · -- a ∈ src₁ (kind-free) but a = ident str₂ with `Q str₂`.
      exact h_sf₁ str₂ hstr₂_Q (hstr₂_eq ▸ h_o₁)
  · -- a = ident str₁ with str₁ ∈ σmid \ σ and `Q str₁`.
    rcases hc₂ a hb with h_o₂ | ⟨str₂, hstr₂_eq, hstr₂_in, hstr₂_not, _⟩
    · exact h_sf₂ str₁ hstr₁_Q (hstr₁_eq ▸ h_o₂)
    · -- ident str₁ = ident str₂ ⇒ str₁ = str₂; but str₁ ∈ σmid, str₂ ∉ σmid.
      have h_id : (HasIdent.ident str₁ : P.Ident) = HasIdent.ident str₂ :=
        hstr₁_eq.symm.trans hstr₂_eq
      have : str₁ = str₂ := LawfulHasIdent.ident_inj h_id
      exact hstr₂_not (this ▸ hstr₁_in)

/-! ## `nondetElim` structural lemmas depending on `exprsShapeFree`

Covers the `Block.nondetElim` shape-free / `namesFreshInRhsExprs` lemmas, the
`initVars`-nodup classification (built on `HoistInitClass`/`hoistInitClass_disjoint`),
and the two hoist exit-coverage mutuals. -/

section NondetElimShapeFree

/-- The freshly generated ndelim guard satisfies the `HoistInitClass` fresh
disjunct at `NondetElim.isGeneratedName` over a one-`gen`-step window. -/
private theorem ndelim_fresh_class {P : PureExpr} [HasIdent P] (pf : String) (σ : StringGenState)
    (h_wf : StringGenState.WF σ)
    (hpf : NondetElim.isGeneratedName (StringGenState.gen pf σ).1) :
    ∃ str : String, HasIdent.ident (P := P) (StringGenState.gen pf σ).1 = HasIdent.ident str
      ∧ str ∈ StringGenState.stringGens (StringGenState.gen pf σ).2
      ∧ str ∉ StringGenState.stringGens σ
      ∧ NondetElim.isGeneratedName str :=
  ⟨(StringGenState.gen pf σ).1, rfl,
    by rw [StringGenState.stringGens_gen]; exact List.mem_cons.mpr (Or.inl rfl),
    StringGenState.stringGens_gen_not_in pf σ h_wf, hpf⟩

mutual
/-- Strengthened nondetElim `initVars` classification: window-tracked
`HoistInitClass` at `NondetElim.isGeneratedName`, plus `Nodup`.  Mirrors the hoist
`_initVars_classified`. -/
theorem Stmt.nondetElimM_initVars_nodup {P : PureExpr} [HasIdent P] [LawfulHasIdent P] [HasFvar P]
    [HasFvars P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) (h_wf : StringGenState.WF σ)
    (h_unique : (Stmt.initVars s).Nodup)
    (h_sf : ∀ str : String, NondetElim.isGeneratedName str →
      HasIdent.ident (P := P) str ∉ Stmt.initVars s) :
    (∀ x ∈ Block.initVars (P := P) (Stmt.nondetElimM s σ).1,
        HoistInitClass NondetElim.isGeneratedName (Stmt.initVars s) σ (Stmt.nondetElimM s σ).2 x)
      ∧ (Block.initVars (P := P) (Stmt.nondetElimM s σ).1).Nodup := by
  match s with
  | .cmd c =>
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars_nil, List.append_nil]
          at hx ⊢
        exact Or.inl hx
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars_nil, List.append_nil]
        exact h_unique
  | .block lbl bss md =>
      rw [Stmt.nondetElimM_block_out, Stmt.nondetElimM_block_state]
      have h_unique' : (Block.initVars bss).Nodup := by
        simpa only [Stmt.initVars_block] using h_unique
      have h_sf' : ∀ str : String, NondetElim.isGeneratedName str →
          HasIdent.ident (P := P) str ∉ Block.initVars bss := by
        intro str hsuf; simpa only [Stmt.initVars_block] using h_sf str hsuf
      have ih := Block.nondetElimM_initVars_nodup bss σ h_wf h_unique' h_sf'
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Block.initVars_cons, Stmt.initVars_block, Block.initVars_nil,
          List.append_nil] at hx ⊢
        simpa only [Stmt.initVars_block] using ih.1 x hx
      · simp only [Block.initVars_cons, Stmt.initVars_block, Block.initVars_nil, List.append_nil]
        exact ih.2
  | .ite (.det e) tss ess md =>
      rw [Stmt.nondetElimM_ite_det_out, Stmt.nondetElimM_ite_det_state]
      have h_uni : (Block.initVars tss ++ Block.initVars ess).Nodup := by
        simpa only [Stmt.initVars_ite] using h_unique
      have h_uni_t : (Block.initVars tss).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_e : (Block.initVars ess).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_disj_te : ∀ a ∈ Block.initVars tss, ∀ b ∈ Block.initVars ess, a ≠ b :=
        (List.nodup_append.mp h_uni).2.2
      have h_sf_t : ∀ str : String, NondetElim.isGeneratedName str →
          HasIdent.ident (P := P) str ∉ Block.initVars tss := by
        intro str hsuf hmem; exact h_sf str hsuf (by
          rw [Stmt.initVars_ite, List.mem_append]; exact Or.inl hmem)
      have h_sf_e : ∀ str : String, NondetElim.isGeneratedName str →
          HasIdent.ident (P := P) str ∉ Block.initVars ess := by
        intro str hsuf hmem; exact h_sf str hsuf (by
          rw [Stmt.initVars_ite, List.mem_append]; exact Or.inr hmem)
      have ih_t := Block.nondetElimM_initVars_nodup tss σ h_wf h_uni_t h_sf_t
      have h_wf_t : StringGenState.WF (Block.nondetElimM tss σ).2 :=
        (Block.nondetElimM_genStep tss σ).wf_mono h_wf
      have ih_e := Block.nondetElimM_initVars_nodup ess (Block.nondetElimM tss σ).2 h_wf_t h_uni_e
          h_sf_e
      have h_step_t : StringGenState.GenStep σ (Block.nondetElimM tss σ).2 :=
          Block.nondetElimM_genStep tss σ
      have h_step_e : StringGenState.GenStep (Block.nondetElimM tss σ).2
          (Block.nondetElimM ess (Block.nondetElimM tss σ).2).2 := Block.nondetElimM_genStep ess _
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Block.initVars_cons, Stmt.initVars_ite, Block.initVars_nil, List.append_nil]
            at hx ⊢
        rw [List.mem_append] at hx
        rcases hx with h | h
        · rcases ih_t.1 x h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [List.mem_append]; exact Or.inl h_o)
          · exact Or.inr ⟨str, he, h_step_e.subset hin, hnot, hQ⟩
        · rcases ih_e.1 x h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [List.mem_append]; exact Or.inr h_o)
          · exact Or.inr ⟨str, he, hin, fun h_in_σ => hnot (h_step_t.subset h_in_σ), hQ⟩
      · simp only [Block.initVars_cons, Stmt.initVars_ite, Block.initVars_nil, List.append_nil]
        rw [List.nodup_append]
        exact ⟨ih_t.2, ih_e.2, hoistInitClass_disjoint (Block.initVars tss) (Block.initVars ess)
          σ (Block.nondetElimM tss σ).2 _
          h_disj_te h_sf_t h_sf_e _ _ ih_t.1 ih_e.1⟩
  | .ite .nondet tss ess md =>
      rw [Stmt.nondetElimM_ite_nondet_out, Stmt.nondetElimM_ite_nondet_state]
      have h_wf₀ : StringGenState.WF (StringGenState.gen NondetElim.prefixIte σ).2 :=
          (StringGenState.GenStep.of_gen NondetElim.prefixIte σ).wf_mono h_wf
      have h_step_g : StringGenState.GenStep σ (StringGenState.gen NondetElim.prefixIte σ).2 :=
          StringGenState.GenStep.of_gen NondetElim.prefixIte σ
      -- the source `.ite .nondet` initVars are the branches'.
      have h_uni : (Block.initVars tss ++ Block.initVars ess).Nodup := by
        simpa only [Stmt.initVars_ite] using h_unique
      have h_uni_t : (Block.initVars tss).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_e : (Block.initVars ess).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_disj_te : ∀ a ∈ Block.initVars tss, ∀ b ∈ Block.initVars ess, a ≠ b :=
        (List.nodup_append.mp h_uni).2.2
      have h_sf_src : ∀ str : String, NondetElim.isGeneratedName str →
          HasIdent.ident (P := P) str ∉ Block.initVars tss ++ Block.initVars ess := by
        intro str hsuf; simpa only [Stmt.initVars_ite] using h_sf str hsuf
      have h_sf_t : ∀ str : String, NondetElim.isGeneratedName str →
          HasIdent.ident (P := P) str ∉ Block.initVars tss :=
        fun str hsuf hmem => h_sf_src str hsuf (List.mem_append.mpr (Or.inl hmem))
      have h_sf_e : ∀ str : String, NondetElim.isGeneratedName str →
          HasIdent.ident (P := P) str ∉ Block.initVars ess :=
        fun str hsuf hmem => h_sf_src str hsuf (List.mem_append.mpr (Or.inr hmem))
      have ih_t := Block.nondetElimM_initVars_nodup tss
        (StringGenState.gen NondetElim.prefixIte σ).2 h_wf₀ h_uni_t h_sf_t
      have h_wf_t : StringGenState.WF
          (Block.nondetElimM tss
            (StringGenState.gen NondetElim.prefixIte σ).2).2 :=
        (Block.nondetElimM_genStep tss
          (StringGenState.gen NondetElim.prefixIte σ).2).wf_mono h_wf₀
      have ih_e := Block.nondetElimM_initVars_nodup ess (Block.nondetElimM tss (StringGenState.gen
          NondetElim.prefixIte σ).2).2 h_wf_t h_uni_e h_sf_e
      have h_step_t : StringGenState.GenStep (StringGenState.gen NondetElim.prefixIte σ).2
          (Block.nondetElimM tss (StringGenState.gen NondetElim.prefixIte σ).2).2 :=
          Block.nondetElimM_genStep tss (StringGenState.gen NondetElim.prefixIte σ).2
      have h_step_e : StringGenState.GenStep (Block.nondetElimM tss (StringGenState.gen
          NondetElim.prefixIte σ).2).2
          (Block.nondetElimM ess (Block.nondetElimM tss (StringGenState.gen NondetElim.prefixIte
              σ).2).2).2 := Block.nondetElimM_genStep ess _
      -- The freshly generated guard is classified over the one-step generator
      -- window beginning at `σ`.
      have h_guard_iv : Stmt.initVars (P := P) (C := Cmd P)
          (Stmt.cmd (HasInit.init
            (HasIdent.ident (P := P)
              (StringGenState.gen NondetElim.prefixIte σ).1)
            HasBool.boolTy ExprOrNondet.nondet md)) =
          [HasIdent.ident (P := P) (StringGenState.gen NondetElim.prefixIte σ).1] := by
        with_unfolding_all rfl
      -- branch inits classified together over the post-gen window `(StringGenState.gen
      -- NondetElim.prefixIte σ).2 → σ₂`.
      have h_branchClass : ∀ y ∈ Block.initVars (Block.nondetElimM tss (StringGenState.gen
          NondetElim.prefixIte σ).2).1 ++
            Block.initVars (Block.nondetElimM ess (Block.nondetElimM tss (StringGenState.gen
                NondetElim.prefixIte σ).2).2).1,
          HoistInitClass NondetElim.isGeneratedName
            (Block.initVars tss ++ Block.initVars ess)
            (StringGenState.gen
              NondetElim.prefixIte σ).2
            (Block.nondetElimM ess (Block.nondetElimM tss (StringGenState.gen NondetElim.prefixIte
                σ).2).2).2 y := by
        intro y hy
        rw [List.mem_append] at hy
        rcases hy with h | h
        · rcases ih_t.1 y h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (List.mem_append.mpr (Or.inl h_o))
          · exact Or.inr ⟨str, he, h_step_e.subset hin, hnot, hQ⟩
        · rcases ih_e.1 y h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (List.mem_append.mpr (Or.inr h_o))
          · exact Or.inr ⟨str, he, hin, fun hσ => hnot (h_step_t.subset hσ), hQ⟩
      have h_branchNodup : (Block.initVars (Block.nondetElimM tss (StringGenState.gen
          NondetElim.prefixIte σ).2).1 ++
            Block.initVars (Block.nondetElimM ess (Block.nondetElimM tss (StringGenState.gen
                NondetElim.prefixIte σ).2).2).1).Nodup := by
        rw [List.nodup_append]
        exact ⟨ih_t.2, ih_e.2, hoistInitClass_disjoint (Block.initVars tss) (Block.initVars ess)
          (StringGenState.gen NondetElim.prefixIte σ).2 (Block.nondetElimM tss (StringGenState.gen
              NondetElim.prefixIte σ).2).2 _
          h_disj_te h_sf_t h_sf_e _ _ ih_t.1 ih_e.1⟩
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Block.initVars_cons, Stmt.initVars_ite, Block.initVars_nil, List.append_nil,
          h_guard_iv, List.singleton_append, List.mem_cons, List.mem_append] at hx
        rcases hx with h_g | h_t | h_e
        · obtain ⟨str, he, hin, hnot, hQ⟩ := ndelim_fresh_class (P := P) NondetElim.prefixIte σ h_wf
            (NondetElim.isGeneratedName_gen.1 σ)
          exact Or.inr ⟨str, h_g.trans he, h_step_e.subset (h_step_t.subset hin), hnot, hQ⟩
        · rcases ih_t.1 x h_t with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [Stmt.initVars_ite, List.mem_append]; exact Or.inl h_o)
          · exact Or.inr ⟨str, he, h_step_e.subset hin,
              fun hσ => hnot (h_step_g.subset hσ), hQ⟩
        · rcases ih_e.1 x h_e with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [Stmt.initVars_ite, List.mem_append]; exact Or.inr h_o)
          · exact Or.inr ⟨str, he, hin,
              fun hσ => hnot (h_step_t.subset (h_step_g.subset hσ)), hQ⟩
      · simp only [Block.initVars_cons, Stmt.initVars_ite, Block.initVars_nil, List.append_nil,
          h_guard_iv, List.singleton_append]
        rw [List.nodup_cons]
        refine ⟨?_, h_branchNodup⟩
        -- The guard is absent from branch initializers. Classify each branch
        -- member and refute each cross-class collision.
        intro hmem
        have h_guard_fresh := ndelim_fresh_class (P := P)
          NondetElim.prefixIte σ h_wf
          (NondetElim.isGeneratedName_gen.1 σ)
        obtain ⟨gstr, geq, gin, gnot, gQ⟩ := h_guard_fresh
        rcases h_branchClass _ hmem with h_o | ⟨str, he, hin, hnot, hQ⟩
        · exact h_sf_src gstr gQ (geq ▸ h_o)
        · have : gstr = str := LawfulHasIdent.ident_inj (geq.symm.trans he)
          exact hnot (this ▸ gin)
  | .loop (.det e) m inv body md =>
      rw [Stmt.nondetElimM_loop_det_out, Stmt.nondetElimM_loop_det_state]
      have h_unique' : (Block.initVars body).Nodup := by
        simpa only [Stmt.initVars_loop] using h_unique
      have h_sf' : ∀ str : String, NondetElim.isGeneratedName str →
          HasIdent.ident (P := P) str ∉ Block.initVars body := by
        intro str hsuf; simpa only [Stmt.initVars_loop] using h_sf str hsuf
      have ih := Block.nondetElimM_initVars_nodup body σ h_wf h_unique' h_sf'
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Block.initVars_cons, Stmt.initVars_loop, Block.initVars_nil,
          List.append_nil] at hx ⊢
        simpa only [Stmt.initVars_loop] using ih.1 x hx
      · simp only [Block.initVars_cons, Stmt.initVars_loop, Block.initVars_nil, List.append_nil]
        exact ih.2
  | .loop .nondet m inv body md =>
      rw [Stmt.nondetElimM_loop_nondet_out, Stmt.nondetElimM_loop_nondet_state]
      have h_wf₀ : StringGenState.WF (StringGenState.gen NondetElim.prefixLoop σ).2 :=
        (StringGenState.GenStep.of_gen NondetElim.prefixLoop σ).wf_mono h_wf
      have h_step_g : StringGenState.GenStep σ (StringGenState.gen NondetElim.prefixLoop σ).2 :=
        StringGenState.GenStep.of_gen NondetElim.prefixLoop σ
      have h_unique' : (Block.initVars body).Nodup := by
        simpa only [Stmt.initVars_loop] using h_unique
      have h_sf' : ∀ str : String, NondetElim.isGeneratedName str →
          HasIdent.ident (P := P) str ∉ Block.initVars body := by
        intro str hsuf; simpa only [Stmt.initVars_loop] using h_sf str hsuf
      have ih := Block.nondetElimM_initVars_nodup body
        (StringGenState.gen NondetElim.prefixLoop σ).2 h_wf₀ h_unique' h_sf'
      have h_step_body : StringGenState.GenStep (StringGenState.gen NondetElim.prefixLoop σ).2
          (Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2).2 :=
        Block.nondetElimM_genStep body _
      -- the new loop body is `body' ++ [havoc guard]`; havoc has no inits.
      have h_havoc_init : Block.initVars (P := P) (C := Cmd P)
          [Stmt.cmd (HasHavoc.havoc
            (HasIdent.ident (P := P)
              (StringGenState.gen NondetElim.prefixLoop σ).1) md)] = [] := by
        with_unfolding_all rfl
      have h_guard_iv : Stmt.initVars (P := P) (C := Cmd P)
          (Stmt.cmd (HasInit.init (HasIdent.ident (P := P) (StringGenState.gen NondetElim.prefixLoop
              σ).1)
            HasBool.boolTy ExprOrNondet.nondet md)) =
          [HasIdent.ident (P := P) (StringGenState.gen NondetElim.prefixLoop σ).1] := by
        with_unfolding_all rfl
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Block.initVars_cons, Stmt.initVars_loop, Block.initVars_nil, List.append_nil,
          h_guard_iv, List.singleton_append, List.mem_cons] at hx
        rw [Block.initVars_append, h_havoc_init, List.append_nil] at hx
        simp only [Stmt.initVars_loop]
        rcases hx with h_g | h_body
        · obtain ⟨str, he, hin, hnot, hQ⟩ :=
            ndelim_fresh_class (P := P) NondetElim.prefixLoop σ h_wf
            (NondetElim.isGeneratedName_gen.2 σ)
          exact Or.inr ⟨str, h_g.trans he, h_step_body.subset hin, hnot, hQ⟩
        · rcases ih.1 x h_body with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl h_o
          · exact Or.inr ⟨str, he, hin, fun hσ => hnot (h_step_g.subset hσ), hQ⟩
      · simp only [Block.initVars_cons, Stmt.initVars_loop, Block.initVars_nil, List.append_nil,
          h_guard_iv, List.singleton_append]
        rw [Block.initVars_append, h_havoc_init, List.append_nil, List.nodup_cons]
        refine ⟨?_, ih.2⟩
        intro hmem
        obtain ⟨gstr, geq, gin, gnot, gQ⟩ :=
          ndelim_fresh_class (P := P) NondetElim.prefixLoop σ h_wf
            (NondetElim.isGeneratedName_gen.2 σ)
        rcases ih.1 _ hmem with h_o | ⟨str, he, hin, hnot, hQ⟩
        · exact h_sf' gstr gQ (geq ▸ h_o)
        · have : gstr = str := LawfulHasIdent.ident_inj (geq.symm.trans he)
          exact hnot (this ▸ gin)
  | .exit lbl md =>
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars_nil, Stmt.initVars,
          Stmt.definedVars,
          List.append_nil] at hx; exact (List.not_mem_nil hx).elim
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars_nil, Stmt.initVars,
          Stmt.definedVars,
          List.append_nil]; exact List.nodup_nil
  | .typeDecl t md =>
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars_nil, Stmt.initVars,
          Stmt.definedVars,
          List.append_nil] at hx; exact (List.not_mem_nil hx).elim
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars_nil, Stmt.initVars,
          Stmt.definedVars,
          List.append_nil]; exact List.nodup_nil
  termination_by sizeOf s

theorem Block.nondetElimM_initVars_nodup {P : PureExpr} [HasIdent P] [LawfulHasIdent P] [HasFvar P]
    [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) (h_wf : StringGenState.WF σ)
    (h_unique : (Block.initVars ss).Nodup)
    (h_sf : ∀ str : String, NondetElim.isGeneratedName str →
      HasIdent.ident (P := P) str ∉ Block.initVars ss) :
    (∀ x ∈ Block.initVars (P := P) (Block.nondetElimM ss σ).1,
        HoistInitClass NondetElim.isGeneratedName (Block.initVars ss) σ
          (Block.nondetElimM ss σ).2 x)
      ∧ (Block.initVars (P := P) (Block.nondetElimM ss σ).1).Nodup := by
  match ss with
  | [] =>
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [Block.nondetElimM, Block.initVars_nil] at hx; exact (List.not_mem_nil hx).elim
      · simp only [Block.nondetElimM, Block.initVars_nil]; exact List.nodup_nil
  | s :: rest =>
      rw [Block.nondetElimM_cons_out, Block.nondetElimM_cons_state]
      have h_uni : (Stmt.initVars s ++ Block.initVars rest).Nodup := by
        simpa only [Block.initVars_cons] using h_unique
      have h_uni_s : (Stmt.initVars s).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_r : (Block.initVars rest).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_disj_sr : ∀ a ∈ Stmt.initVars s, ∀ b ∈ Block.initVars rest, a ≠ b :=
        (List.nodup_append.mp h_uni).2.2
      have h_sf_s : ∀ str : String, NondetElim.isGeneratedName str →
          HasIdent.ident (P := P) str ∉ Stmt.initVars s := by
        intro str hsuf hmem; exact h_sf str hsuf (by
          rw [Block.initVars_cons, List.mem_append]; exact Or.inl hmem)
      have h_sf_r : ∀ str : String, NondetElim.isGeneratedName str →
          HasIdent.ident (P := P) str ∉ Block.initVars rest := by
        intro str hsuf hmem; exact h_sf str hsuf (by
          rw [Block.initVars_cons, List.mem_append]; exact Or.inr hmem)
      have ih_s := Stmt.nondetElimM_initVars_nodup s σ h_wf h_uni_s h_sf_s
      have h_wf_s : StringGenState.WF (Stmt.nondetElimM s σ).2 :=
        (Stmt.nondetElimM_genStep s σ).wf_mono h_wf
      have ih_r := Block.nondetElimM_initVars_nodup rest (Stmt.nondetElimM s σ).2 h_wf_s h_uni_r
          h_sf_r
      have h_step_s : StringGenState.GenStep σ (Stmt.nondetElimM s σ).2 := Stmt.nondetElimM_genStep
          s σ
      have h_step_r : StringGenState.GenStep (Stmt.nondetElimM s σ).2
          (Block.nondetElimM rest (Stmt.nondetElimM s σ).2).2 := Block.nondetElimM_genStep rest _
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Block.initVars_append] at hx
        rw [Block.initVars_cons]
        rw [List.mem_append] at hx
        rcases hx with h | h
        · rcases ih_s.1 x h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [List.mem_append]; exact Or.inl h_o)
          · exact Or.inr ⟨str, he, h_step_r.subset hin, hnot, hQ⟩
        · rcases ih_r.1 x h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [List.mem_append]; exact Or.inr h_o)
          · exact Or.inr ⟨str, he, hin, fun h_in_σ => hnot (h_step_s.subset h_in_σ), hQ⟩
      · rw [Block.initVars_append, List.nodup_append]
        exact ⟨ih_s.2, ih_r.2, hoistInitClass_disjoint (Stmt.initVars s) (Block.initVars rest)
          σ (Stmt.nondetElimM s σ).2 _
          h_disj_sr h_sf_s h_sf_r _ _ ih_s.1 ih_r.1⟩
  termination_by sizeOf ss
end

mutual
/-- `Stmt.liftInitsInLoopBody` preserves exit coverage on its residual (`.2`)
component: lifted inits become sibling `.cmd`s, and `.block`/`.exit`/`.loop` are
structurally preserved. -/
theorem Stmt.liftInitsInLoopBody_exitsCoveredByBlocks {P : PureExpr}
    (labels : List String) (s : Stmt P (Cmd P))
    (h : Stmt.exitsCoveredByBlocks labels s) :
    Block.exitsCoveredByBlocks labels
      (Stmt.liftInitsInLoopBody s).2 := by
  match s with
  | .cmd c =>
    cases c <;>
      (simp only [Stmt.liftInitsInLoopBody]; exact ⟨trivial, trivial⟩)
  | .block lbl bss md =>
    simp only [Stmt.liftInitsInLoopBody]
    exact coveredBlock_singleton labels (.block lbl _ md)
      (Block.liftInitsInLoopBody_exitsCoveredByBlocks (lbl :: labels) bss
        (by simpa [Stmt.exitsCoveredByBlocks] using h))
  | .ite g tss ess md =>
    simp only [Stmt.liftInitsInLoopBody]
    obtain ⟨ht, he⟩ := h
    exact coveredBlock_singleton labels (.ite g _ _ md)
      ⟨Block.liftInitsInLoopBody_exitsCoveredByBlocks labels tss ht,
       Block.liftInitsInLoopBody_exitsCoveredByBlocks labels ess he⟩
  | .loop g m inv body md =>
    simp only [Stmt.liftInitsInLoopBody]
    exact coveredBlock_singleton labels (.loop g m inv body md) h
  | .exit lbl md =>
    simp only [Stmt.liftInitsInLoopBody]
    exact coveredBlock_singleton labels (.exit lbl md) h
  | .typeDecl t md =>
    simp only [Stmt.liftInitsInLoopBody]
    exact coveredBlock_singleton labels (.typeDecl t md) trivial
  termination_by sizeOf s

/-- `Block.liftInitsInLoopBody` preserves exit coverage on its residual. -/
theorem Block.liftInitsInLoopBody_exitsCoveredByBlocks {P : PureExpr}
    (labels : List String) (ss : List (Stmt P (Cmd P)))
    (h : Block.exitsCoveredByBlocks labels ss) :
    Block.exitsCoveredByBlocks labels
      (Block.liftInitsInLoopBody ss).2 := by
  match ss with
  | [] => simp only [Block.liftInitsInLoopBody]; exact trivial
  | s :: rest =>
    rw [Block.liftInitsInLoopBody]
    exact block_exitsCoveredByBlocks_append labels _ _
      (Stmt.liftInitsInLoopBody_exitsCoveredByBlocks labels s h.1)
      (Block.liftInitsInLoopBody_exitsCoveredByBlocks labels rest h.2)
  termination_by sizeOf ss
end

mutual
/-- `Stmt.hoistLoopPrefixInits` preserves exit coverage: the hoisted `init`
prelude is `.cmd`s (trivially covered), and the loop body's exits are covered by
the same labels before and after (the hoist neither relabels `.block`s nor moves
`.exit`s across a `.block` boundary). -/
theorem Stmt.hoistP_exitsCoveredByBlocks {P : PureExpr}
    (labels : List String) (s : Stmt P (Cmd P))
    (h : Stmt.exitsCoveredByBlocks labels s) :
    Block.exitsCoveredByBlocks labels
      (Stmt.hoistLoopPrefixInits s) := by
  match s with
  | .cmd c =>
    simp only [Stmt.hoistLoopPrefixInits]; exact coveredBlock_singleton labels (.cmd c) trivial
  | .block lbl bss md =>
    simp only [Stmt.hoistLoopPrefixInits]
    exact coveredBlock_singleton labels (.block lbl _ md)
      (Block.hoistP_exitsCoveredByBlocks (lbl :: labels) bss
        (by simpa [Stmt.exitsCoveredByBlocks] using h))
  | .ite g tss ess md =>
    simp only [Stmt.hoistLoopPrefixInits]
    obtain ⟨ht, he⟩ := h
    exact coveredBlock_singleton labels (.ite g _ _ md)
      ⟨Block.hoistP_exitsCoveredByBlocks labels tss ht,
       Block.hoistP_exitsCoveredByBlocks labels ess he⟩
  | .loop g m inv body md =>
    simp only [Stmt.hoistLoopPrefixInits]
    refine block_exitsCoveredByBlocks_append labels _ _
      (all_cmd_exitsCoveredByBlocks labels _
        (by intro s hs;
            simp only [List.mem_map] at hs;
            obtain ⟨c, _, hc⟩ := hs;
            exact ⟨c, hc.symm⟩))
      ?_
    exact coveredBlock_singleton labels (.loop g m inv _ md)
      (Block.liftInitsInLoopBody_exitsCoveredByBlocks labels _
        (Block.hoistP_exitsCoveredByBlocks labels body
          (by simpa [Stmt.exitsCoveredByBlocks] using h)))
  | .exit lbl md =>
    simp only [Stmt.hoistLoopPrefixInits]
    exact coveredBlock_singleton labels (.exit lbl md) h
  | .typeDecl t md =>
    simp only [Stmt.hoistLoopPrefixInits]
    exact coveredBlock_singleton labels (.typeDecl t md) trivial
  termination_by sizeOf s

/-- `Block.hoistLoopPrefixInits` preserves exit coverage. -/
theorem Block.hoistP_exitsCoveredByBlocks {P : PureExpr}
    (labels : List String) (ss : List (Stmt P (Cmd P)))
    (h : Block.exitsCoveredByBlocks labels ss) :
    Block.exitsCoveredByBlocks labels
      (Block.hoistLoopPrefixInits ss) := by
  match ss with
  | [] => simp only [Block.hoistLoopPrefixInits]; exact trivial
  | s :: rest =>
    rw [Block.hoistLoopPrefixInits]
    exact block_exitsCoveredByBlocks_append labels _ _
      (Stmt.hoistP_exitsCoveredByBlocks labels s h.1)
      (Block.hoistP_exitsCoveredByBlocks labels rest h.2)
  termination_by sizeOf ss
end

end NondetElimShapeFree

/-! ## Event-level loop-init-hoist foundation -/

/-- Event-producing command evaluation preserves every slot in `DTyped`. -/
theorem DTyped.evalCmdE {P : PureExpr}
    [HasFvar P] [HasBool P] [HasBoolOps P] [DecidableEq P.Ident] [HasFvars P] [LawfulHasVal P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident} {c : Cmd P}
    {ρ : Env P} {σ' : SemanticStore P} {emitted : Trace P}
    (heval : EvalCmdE P ρ.factory ρ.store c σ' emitted)
    (h : DTyped Dτ D ρ) :
    DTyped Dτ D { ρ with store := σ' } := by
  intro y hy
  exact EvalCmdE_preserves_typedAt heval (h y hy)

/-- A source command can be replayed in an agreeing target store while
preserving target typed slots and relating the captured event snapshots. -/
theorem evalCmdE_replay_agreement_typed {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident] [LawfulHasVal P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident}
    {ρs ρt : Env P} {σs' : SemanticStore P} {c : Cmd P} {sourceTrace : Trace P}
    (hfac : ρt.factory = ρs.factory)
    (hagree : StoreAgreement ρs.store ρt.store)
    (htyped : DTyped Dτ D ρt)
    (heval : EvalCmdE P ρs.factory ρs.store c σs' sourceTrace)
    (hmono : WellFormedSemanticEvalMono ρs.factory)
    (hinit : ∀ x ∈ Cmd.definedVars c, ρt.store x = none) :
    ∃ σt' targetTrace,
      EvalCmdE P ρt.factory ρt.store c σt' targetTrace ∧
      StoreAgreement σs' σt' ∧
      DTyped Dτ D { ρt with store := σt' } ∧
      TraceStuttersEnv (fun _ : P.Ident => True) (fun _ : P.Factory => True) sourceTrace targetTrace := by
  have hext : StoreExtendsWith (fun _ : P.Ident => True) ρs.store ρt.store :=
    ⟨hagree, fun _ _ => Or.inr trivial⟩
  obtain ⟨σt', heval', hext', htrace⟩ :=
    evalCmdE_replay_extends (fun _ : P.Ident => True) ρs.factory
      ρs.store ρt.store σs' c sourceTrace hext heval hmono hinit
  have heval_t : EvalCmdE P ρt.factory ρt.store c σt'
      (Cmd.emittedEvents P c ρt.factory ρt.store) := by
    simpa [hfac] using heval'
  refine ⟨σt', Cmd.emittedEvents P c ρt.factory ρt.store,
    heval_t, hext'.1, DTyped.evalCmdE heval_t htyped, ?_⟩
  simpa [hfac] using htrace.toTraceStuttersEnv

/-- A source initializer is replayed by the same-name target assignment.  The
single proof covers deterministic and nondeterministic right-hand sides. -/
theorem initToSetEvalCmdE {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [DecidableEq P.Ident] [LawfulHasVal P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident}
    (y : P.Ident) (ty : P.Ty) (rhs : ExprOrNondet P) (md : MetaData P)
    (ρs ρt : Env P) (σs' : SemanticStore P) (sourceTrace : Trace P)
    (hfac : ρt.factory = ρs.factory)
    (hagree : StoreAgreement ρs.store ρt.store)
    (htyped : DTyped Dτ D ρt)
    (hy : y ∈ D) (hDτ : Dτ y = ty)
    (hmono : WellFormedSemanticEvalMono ρs.factory)
    (heval : EvalCmdE P ρs.factory ρs.store (.init y ty rhs md) σs' sourceTrace) :
    ∃ σt' targetTrace,
      EvalCmdE P ρt.factory ρt.store (.set y rhs md) σt' targetTrace ∧
      StoreAgreement σs' σt' ∧
      DTyped Dτ D { ρt with store := σt' } ∧
      TraceStuttersEnv (fun _ : P.Ident => True) (fun _ : P.Factory => True) sourceTrace targetTrace := by
  obtain ⟨prev, hprev, hprevTy⟩ := htyped y hy
  have hprevTy' : HasVal.valueOfTy ρt.factory prev ty := by
    rw [← hDτ]
    exact hprevTy
  cases rhs with
  | det e =>
      cases heval with
      | eval_init he hstate hvTy hwfVar =>
          rename_i v
          have het : P.eval ρt.factory ρt.store e = some v := by
            rw [hfac]
            exact hmono e v ρs.store ρt.store
              (storeAgreement_supplies_mono_premise _ _ hagree) he
          have hvTy' : HasVal.valueOfTy ρt.factory v ty := by
            rw [hfac]
            exact hvTy
          let σt' := SemanticStore.update ρt.store y v
          have hupd : UpdateState P ρt.store y v σt' :=
            .update hprev (by simp [σt', SemanticStore.update])
              (by intro z hz; simp [σt', SemanticStore.update, Ne.symm hz])
          have heval_t : EvalCmdE P ρt.factory ρt.store (.set y (.det e) md) σt' [] :=
            .eval_set het hupd ⟨prev, ty, hprev, hprevTy', hvTy'⟩
              (by simpa [hfac] using hwfVar)
          cases hstate with
          | init _ hvalue hother =>
              refine ⟨σt', [], heval_t, ?_, DTyped.evalCmdE heval_t htyped, .nil⟩
              intro z hz
              by_cases hzy : z = y
              · subst z
                simpa [σt', SemanticStore.update] using hvalue
              · have hs : σs' z = ρs.store z := hother z (Ne.symm hzy)
                have hsSome : (ρs.store z).isSome = true := by
                  rw [← hs]
                  exact hz z (List.mem_singleton.mpr rfl)
                rw [hs, hagree z (by
                  intro w hw
                  rw [List.mem_singleton.mp hw]
                  exact hsSome)]
                simp [σt', SemanticStore.update, hzy]
  | nondet =>
      cases heval with
      | eval_init_unconstrained hstate hvTy hwfVar =>
          rename_i v
          have hvTy' : HasVal.valueOfTy ρt.factory v ty := by
            rw [hfac]
            exact hvTy
          let σt' := SemanticStore.update ρt.store y v
          have hupd : UpdateState P ρt.store y v σt' :=
            .update hprev (by simp [σt', SemanticStore.update])
              (by intro z hz; simp [σt', SemanticStore.update, Ne.symm hz])
          have heval_t : EvalCmdE P ρt.factory ρt.store (.set y .nondet md) σt' [] :=
            .eval_set_nondet hupd ⟨prev, ty, hprev, hprevTy', hvTy'⟩
              (by simpa [hfac] using hwfVar)
          cases hstate with
          | init _ hvalue hother =>
              refine ⟨σt', [], heval_t, ?_, DTyped.evalCmdE heval_t htyped, .nil⟩
              intro z hz
              by_cases hzy : z = y
              · subst z
                simpa [σt', SemanticStore.update] using hvalue
              · have hs : σs' z = ρs.store z := hother z (Ne.symm hzy)
                have hsSome : (ρs.store z).isSome = true := by
                  rw [← hs]
                  exact hz z (List.mem_singleton.mpr rfl)
                rw [hs, hagree z (by
                  intro w hw
                  rw [List.mem_singleton.mp hw]
                  exact hsSome)]
                simp [σt', SemanticStore.update, hzy]

private theorem evalCmdE_replay_agreement_typed_lockstep {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident] [LawfulHasVal P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident}
    {ρs ρt : Env P} {σs' : SemanticStore P} {c : Cmd P}
    {sourceTrace : Trace P}
    (hfac : ρt.factory = ρs.factory)
    (hagree : StoreAgreement ρs.store ρt.store)
    (htyped : DTyped Dτ D ρt)
    (heval : EvalCmdE P ρs.factory ρs.store c σs' sourceTrace)
    (hmono : WellFormedSemanticEvalMono ρs.factory)
    (hinit : ∀ x ∈ Cmd.definedVars c, ρt.store x = none) :
    ∃ σt' targetTrace,
      EvalCmdE P ρt.factory ρt.store c σt' targetTrace ∧
      StoreAgreement σs' σt' ∧
      DTyped Dτ D { ρt with store := σt' } ∧
      TraceExtendsEnv (fun _ : P.Ident => True) sourceTrace targetTrace := by
  obtain ⟨σt', targetTrace, heval', hagree', htyped', _⟩ :=
    evalCmdE_replay_agreement_typed hfac hagree htyped heval hmono hinit
  refine ⟨σt', targetTrace, heval', hagree', htyped', ?_⟩
  cases heval <;> cases heval' <;>
    first
    | exact .nil
    | exact .cons
        ⟨hfac.symm, ⟨hagree, fun _ _ => Or.inr trivial⟩, rfl, rfl, rfl⟩
        .nil

private theorem initToSetEvalCmdE_lockstep {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [DecidableEq P.Ident] [LawfulHasVal P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident}
    (y : P.Ident) (ty : P.Ty) (rhs : ExprOrNondet P) (md : MetaData P)
    (ρs ρt : Env P) (σs' : SemanticStore P) (sourceTrace : Trace P)
    (hfac : ρt.factory = ρs.factory)
    (hagree : StoreAgreement ρs.store ρt.store)
    (htyped : DTyped Dτ D ρt)
    (hy : y ∈ D) (hDτ : Dτ y = ty)
    (hmono : WellFormedSemanticEvalMono ρs.factory)
    (heval : EvalCmdE P ρs.factory ρs.store (.init y ty rhs md) σs' sourceTrace) :
    ∃ σt' targetTrace,
      EvalCmdE P ρt.factory ρt.store (.set y rhs md) σt' targetTrace ∧
      StoreAgreement σs' σt' ∧
      DTyped Dτ D { ρt with store := σt' } ∧
      TraceExtendsEnv (fun _ : P.Ident => True) sourceTrace targetTrace := by
  obtain ⟨σt', targetTrace, heval', hagree', htyped', _⟩ :=
    initToSetEvalCmdE y ty rhs md ρs ρt σs' sourceTrace hfac hagree htyped
      hy hDτ hmono heval
  refine ⟨σt', targetTrace, heval', hagree', htyped', ?_⟩
  cases heval <;> cases heval' <;> exact .nil

/-- The hoisted havoc prelude executes in the event semantics, establishes all
placeholder types, and preserves agreement and control-state fields. -/
theorem LoopInitHoistProducerProps.prelude_runnerE {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P]
    [DecidableEq P.Ident] [LawfulHasVal P]
    {Dτ : P.Ident → P.Ty}
    (hs : List (P.Ident × P.Ty × MetaData P))
    (acc : List P.Ident)
    (ρs ρt : Env P)
    (hacc : DTyped Dτ acc ρt)
    (hagree : StoreAgreement ρs.store ρt.store)
    (hsrcNone : ∀ y ∈ LoopInitHoistProducerProps.preludeNames hs, ρs.store y = none)
    (htgtNone : ∀ y ∈ LoopInitHoistProducerProps.preludeNames hs, ρt.store y = none)
    (hnodup : (LoopInitHoistProducerProps.preludeNames hs).Nodup)
    (hty : ∀ t ∈ hs, Dτ t.1 = t.2.1)
    (hinhab : ∀ t ∈ hs, ∃ v, HasVal.valueOfTy ρt.factory v t.2.1)
    (hwfVar : WellFormedSemanticEvalVar ρt.factory) :
    ∃ ρt' targetTrace,
      StepStmtStarE P (EvalCmdE P)
        (.stmts (LoopInitHoistProducerProps.preludeHavocs hs) ρt)
        targetTrace (.terminal ρt') ∧
      StoreAgreement ρs.store ρt'.store ∧
      ρt'.factory = ρt.factory ∧
      DTyped Dτ (acc ++ LoopInitHoistProducerProps.preludeNames hs) ρt' ∧
      TraceStuttersEnv (fun _ : P.Ident => True) (fun _ : P.Factory => True) [] targetTrace ∧
      TraceExtendsEnv (fun _ : P.Ident => True) [] targetTrace := by
  induction hs generalizing ρt acc with
  | nil =>
      refine ⟨ρt, [], .step _ [] _ [] _ .step_stmts_nil (.refl _),
        hagree, rfl, ?_, ⟨.nil, .nil⟩⟩
      simpa [LoopInitHoistProducerProps.preludeNames] using hacc
  | cons t rest ih =>
      obtain ⟨y, ty, md⟩ := t
      have hynotin : y ∉ LoopInitHoistProducerProps.preludeNames rest := by
        simpa [LoopInitHoistProducerProps.preludeNames] using (List.nodup_cons.mp hnodup).1
      have hnodupRest : (LoopInitHoistProducerProps.preludeNames rest).Nodup := by
        simpa [LoopInitHoistProducerProps.preludeNames] using (List.nodup_cons.mp hnodup).2
      have hySrc : ρs.store y = none := hsrcNone y (by
        simp [LoopInitHoistProducerProps.preludeNames])
      have hyTgt : ρt.store y = none := htgtNone y (by
        simp [LoopInitHoistProducerProps.preludeNames])
      obtain ⟨v, hvty⟩ := hinhab (y, ty, md) List.mem_cons_self
      let σmid := SemanticStore.update ρt.store y v
      let ρmid : Env P := { ρt with store := σmid }
      have hstate : InitState P ρt.store y v σmid :=
        .init hyTgt (by simp [σmid, SemanticStore.update])
          (by intro z hz; simp [σmid, SemanticStore.update, Ne.symm hz])
      have heval : EvalCmdE P ρt.factory ρt.store (.init y ty .nondet md) σmid [] :=
        .eval_init_unconstrained hstate hvty hwfVar
      have hhead : StepStmtStarE P (EvalCmdE P)
          (.stmts ((.cmd (.init y ty .nondet md)) ::
            LoopInitHoistProducerProps.preludeHavocs rest) ρt) []
          (.stmts (LoopInitHoistProducerProps.preludeHavocs rest) ρmid) :=
        stmts_cons_stepE (EvalCmdE P) (.cmd (.init y ty .nondet md))
          (LoopInitHoistProducerProps.preludeHavocs rest) ρt ρmid
          (Imperative.StepStmtStarE.single (.step_cmd heval))
      have hagreeMid : StoreAgreement ρs.store ρmid.store :=
        storeAgreement_storeWith _ _ _ _ hagree hySrc
      have haccMid : DTyped Dτ acc ρmid := DTyped.evalCmdE heval hacc
      have hyMid : DTyped Dτ [y] ρmid := by
        intro z hz
        rw [List.mem_singleton.mp hz]
        refine ⟨v, by simp [ρmid, σmid, SemanticStore.update], ?_⟩
        rw [hty (y, ty, md) List.mem_cons_self]
        exact hvty
      have htypedMid : DTyped Dτ (acc ++ [y]) ρmid := DTyped.append haccMid hyMid
      have hsrcRest : ∀ z ∈ LoopInitHoistProducerProps.preludeNames rest,
          ρs.store z = none := by
        intro z hz
        apply hsrcNone z
        simpa only [LoopInitHoistProducerProps.preludeNames, List.map_cons, List.mem_cons]
          using Or.inr hz
      have htgtRest : ∀ z ∈ LoopInitHoistProducerProps.preludeNames rest,
          ρmid.store z = none := by
        intro z hz
        have hzy : z ≠ y := fun h => hynotin (h ▸ hz)
        simpa [ρmid, σmid, SemanticStore.update, hzy] using
          htgtNone z (by
            simpa only [LoopInitHoistProducerProps.preludeNames, List.map_cons, List.mem_cons]
              using Or.inr hz)
      have htyRest : ∀ t ∈ rest, Dτ t.1 = t.2.1 := by
        intro t ht
        exact hty t (List.mem_cons_of_mem _ ht)
      have hinRest : ∀ t ∈ rest, ∃ v, HasVal.valueOfTy ρmid.factory v t.2.1 := by
        intro t ht
        exact hinhab t (List.mem_cons_of_mem _ ht)
      obtain ⟨ρt', targetTrace, hrest, hagree', hfac', htyped', htrace⟩ :=
        ih (acc := acc ++ [y]) (ρt := ρmid) htypedMid hagreeMid hsrcRest htgtRest
          hnodupRest htyRest hinRest hwfVar
      refine ⟨ρt', targetTrace, ?_, hagree', ?_, ?_, htrace⟩
      · simpa [LoopInitHoistProducerProps.preludeHavocs] using
          ReflTransTrace.trans _ hhead hrest
      · exact hfac'.trans rfl
      · simpa [LoopInitHoistProducerProps.preludeNames, List.append_assoc] using htyped'

structure LiftEnvRel {P : PureExpr} [HasVal P]
    (Dτ : P.Ident → P.Ty) (D : List P.Ident) (factory : P.Factory)
    (source target : Env P) : Prop where
  agreement : StoreAgreement source.store target.store
  sourceFactory : source.factory = factory
  targetFactory : target.factory = factory
  typed : DTyped Dτ D target

structure LiftStoreRel {P : PureExpr} [HasVal P]
    (Dτ : P.Ident → P.Ty) (D : List P.Ident) (factory : P.Factory)
    (source target : SemanticStore P) : Prop where
  agreement : StoreAgreement source target
  typed : DTyped Dτ D { store := target, factory := factory }

structure LiftStmtRel {P : PureExpr} [HasFvars P]
    (Dτ : P.Ident → P.Ty) (D : List P.Ident)
    (source target : Stmt P (Cmd P)) : Prop where
  residual : (Stmt.liftInitsInLoopBody source).2 = [target]
  loopBodies : Stmt.loopBodyNoInits source = true
  typedInits : ∀ p ∈ LoopInitHoistProducerProps.Stmt.typedInitVars source,
    p.1 ∈ D ∧ Dτ p.1 = p.2

structure LiftBlockRel {P : PureExpr} [HasFvars P]
    (Dτ : P.Ident → P.Ty) (D : List P.Ident)
    (source target : List (Stmt P (Cmd P))) : Prop where
  residual : (Block.liftInitsInLoopBody source).2 = target
  loopBodies : Block.loopBodyNoInits source = true
  typedInits : ∀ p ∈ LoopInitHoistProducerProps.Block.typedInitVars source,
    p.1 ∈ D ∧ Dτ p.1 = p.2

inductive LiftConfigRel {P : PureExpr} [HasFvars P] [HasVal P]
    (Dτ : P.Ident → P.Ty) (D : List P.Ident) (factory : P.Factory) :
    Config P (Cmd P) → Config P (Cmd P) → Prop where
  | stmt : LiftEnvRel Dτ D factory sourceEnv targetEnv →
      LiftStmtRel Dτ D sourceStmt targetStmt →
      LiftConfigRel Dτ D factory (.stmt sourceStmt sourceEnv) (.stmt targetStmt targetEnv)
  | stmts : LiftEnvRel Dτ D factory sourceEnv targetEnv →
      LiftBlockRel Dτ D sourceStmts targetStmts →
      LiftConfigRel Dτ D factory (.stmts sourceStmts sourceEnv) (.stmts targetStmts targetEnv)
  | terminal : LiftEnvRel Dτ D factory sourceEnv targetEnv →
      LiftConfigRel Dτ D factory (.terminal sourceEnv) (.terminal targetEnv)
  | exiting : LiftEnvRel Dτ D factory sourceEnv targetEnv →
      LiftConfigRel Dτ D factory (.exiting label sourceEnv) (.exiting label targetEnv)
  | block : LiftStoreRel Dτ D factory sourceParent targetParent →
      LiftConfigRel Dτ D factory sourceInner targetInner →
      LiftConfigRel Dτ D factory
        (.block label sourceParent sourceInner) (.block label targetParent targetInner)
  | seq : LiftConfigRel Dτ D factory sourceInner targetInner →
      LiftBlockRel Dτ D sourceRest targetRest →
      LiftConfigRel Dτ D factory
        (.seq sourceInner sourceRest) (.seq targetInner targetRest)

private theorem liftStmtResidual_singleton {P : PureExpr}
    (s : Stmt P (Cmd P)) : ∃ s', (Stmt.liftInitsInLoopBody s).2 = [s'] := by
  cases s with
  | cmd c => cases c <;> simp [Stmt.liftInitsInLoopBody]
  | block => simp [Stmt.liftInitsInLoopBody]
  | ite => simp [Stmt.liftInitsInLoopBody]
  | loop => simp [Stmt.liftInitsInLoopBody]
  | exit => simp [Stmt.liftInitsInLoopBody]
  | typeDecl => simp [Stmt.liftInitsInLoopBody]

private theorem LiftBlockRel.cons {P : PureExpr} [HasFvars P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident}
    {s : Stmt P (Cmd P)} {rest target : List (Stmt P (Cmd P))}
    (h : LiftBlockRel Dτ D (s :: rest) target) :
    ∃ s' rest', target = s' :: rest' ∧
      LiftStmtRel Dτ D s s' ∧ LiftBlockRel Dτ D rest rest' := by
  obtain ⟨s', hs'⟩ := liftStmtResidual_singleton s
  let rest' := (Block.liftInitsInLoopBody rest).2
  have htarget : target = s' :: rest' := by
    rw [← h.residual, LoopInitHoistProducerProps.liftP_cons_residual, hs']
    rfl
  have hloops : Stmt.loopBodyNoInits s = true ∧ Block.loopBodyNoInits rest = true := by
    simpa only [Block.loopBodyNoInits, Bool.and_eq_true] using h.loopBodies
  refine ⟨s', rest', htarget,
    ⟨hs', hloops.1, ?_⟩,
    ⟨rfl, hloops.2, ?_⟩⟩
  · intro p hp
    exact h.typedInits p (by
      rw [LoopInitHoistProducerProps.Block.typedInitVars]
      exact List.mem_append.mpr (Or.inl hp))
  · intro p hp
    exact h.typedInits p (by
      rw [LoopInitHoistProducerProps.Block.typedInitVars]
      exact List.mem_append.mpr (Or.inr hp))

private theorem LiftEnvRel.storeRel {P : PureExpr} [HasVal P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident} {factory : P.Factory}
    {source target : Env P}
    (h : LiftEnvRel Dτ D factory source target) :
    LiftStoreRel Dτ D factory source.store target.store := by
  refine ⟨h.agreement, ?_⟩
  intro y hy
  obtain ⟨value, hvalue, hty⟩ := h.typed y hy
  exact ⟨value, hvalue, by simpa [h.targetFactory] using hty⟩

private theorem LiftStmtRel.singleton {P : PureExpr} [HasFvars P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident}
    {source target : Stmt P (Cmd P)}
    (h : LiftStmtRel Dτ D source target) :
    LiftBlockRel Dτ D [source] [target] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [LoopInitHoistProducerProps.liftP_cons_residual, h.residual,
      Block.liftInitsInLoopBody]
    rfl
  · simpa [Block.loopBodyNoInits] using h.loopBodies
  · intro p hp
    exact h.typedInits p (by
      simpa [LoopInitHoistProducerProps.Block.typedInitVars] using hp)

private theorem LiftEnvRel.eval {P : PureExpr} [HasFvars P] [HasVal P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident} {factory : P.Factory}
    {source target : Env P} {e : P.Expr} {value : P.Val}
    (h : LiftEnvRel Dτ D factory source target)
    (hmono : WellFormedSemanticEvalMono factory)
    (heval : P.eval source.factory source.store e = some value) :
    P.eval target.factory target.store e = some value := by
  rw [h.sourceFactory] at heval
  rw [h.targetFactory]
  exact hmono e value source.store target.store
    (storeAgreement_supplies_mono_premise _ _ h.agreement) heval

/-- `LiftEnvRel.eval` at the factory's Boolean values: the value read in the target is
    the target factory's Boolean (the related environments share their factory). -/
private theorem LiftEnvRel.evalBool {P : PureExpr} [HasFvars P] [HasBool P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident} {factory : P.Factory}
    {source target : Env P} {e : P.Expr} (b : P.Factory → P.Val)
    (h : LiftEnvRel Dτ D factory source target)
    (hmono : WellFormedSemanticEvalMono factory)
    (heval : P.eval source.factory source.store e = some (b source.factory)) :
    P.eval target.factory target.store e = some (b target.factory) := by
  have := h.eval hmono heval
  rwa [h.sourceFactory, ← h.targetFactory] at this

private theorem LiftEnvRel.project {P : PureExpr} [HasFvars P] [HasVal P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident} {factory : P.Factory}
    {sourceParent targetParent : SemanticStore P}
    {sourceInner targetInner : Env P}
    (hparent : LiftStoreRel Dτ D factory sourceParent targetParent)
    (hinner : LiftEnvRel Dτ D factory sourceInner targetInner) :
    LiftEnvRel Dτ D factory
      { sourceInner with store := projectStore sourceParent sourceInner.store }
      { targetInner with store := projectStore targetParent targetInner.store } := by
  refine ⟨StoreAgreement.of_projectStore_parents hparent.agreement hinner.agreement,
    hinner.sourceFactory, hinner.targetFactory, ?_⟩
  have hp : DTyped Dτ D { targetInner with store := targetParent } := by
    intro y hy
    obtain ⟨value, hvalue, hty⟩ := hparent.typed y hy
    exact ⟨value, hvalue, by simpa [hinner.targetFactory] using hty⟩
  exact DTyped.projectStore hp hinner.typed

private theorem LiftStmtRel.blockBody {P : PureExpr} [HasFvars P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident}
    {label : String} {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {target : Stmt P (Cmd P)}
    (h : LiftStmtRel Dτ D (.block label body md) target) :
    target = .block label (Block.liftInitsInLoopBody body).2 md ∧
      LiftBlockRel Dτ D body (Block.liftInitsInLoopBody body).2 := by
  have ht : target = .block label (Block.liftInitsInLoopBody body).2 md := by
    simpa [Stmt.liftInitsInLoopBody] using congrArg List.head? h.residual.symm
  refine ⟨ht, ⟨rfl, ?_, ?_⟩⟩
  · simpa [Stmt.loopBodyNoInits] using h.loopBodies
  · intro p hp
    exact h.typedInits p (by simpa [LoopInitHoistProducerProps.Stmt.typedInitVars] using hp)

private theorem LiftStmtRel.iteBranches {P : PureExpr} [HasFvars P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident}
    {g : ExprOrNondet P} {thenSource elseSource : List (Stmt P (Cmd P))} {md : MetaData P}
    {target : Stmt P (Cmd P)}
    (h : LiftStmtRel Dτ D (.ite g thenSource elseSource md) target) :
    target = .ite g
      (Block.liftInitsInLoopBody thenSource).2
      (Block.liftInitsInLoopBody elseSource).2 md ∧
    LiftBlockRel Dτ D thenSource (Block.liftInitsInLoopBody thenSource).2 ∧
    LiftBlockRel Dτ D elseSource (Block.liftInitsInLoopBody elseSource).2 := by
  have ht : target = .ite g
      (Block.liftInitsInLoopBody thenSource).2
      (Block.liftInitsInLoopBody elseSource).2 md := by
    simpa [Stmt.liftInitsInLoopBody] using congrArg List.head? h.residual.symm
  have hloops : Block.loopBodyNoInits thenSource = true ∧
      Block.loopBodyNoInits elseSource = true := by
    simpa only [Stmt.loopBodyNoInits, Bool.and_eq_true] using h.loopBodies
  refine ⟨ht, ⟨rfl, hloops.1, ?_⟩,
    ⟨rfl, hloops.2, ?_⟩⟩
  · intro p hp
    exact h.typedInits p (by
      rw [LoopInitHoistProducerProps.Stmt.typedInitVars]
      exact List.mem_append.mpr (Or.inl hp))
  · intro p hp
    exact h.typedInits p (by
      rw [LoopInitHoistProducerProps.Stmt.typedInitVars]
      exact List.mem_append.mpr (Or.inr hp))

private theorem LiftStmtRel.loopBody {P : PureExpr} [HasFvars P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident}
    {g : ExprOrNondet P} {measure : Option P.Expr} {invariants : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {target : Stmt P (Cmd P)}
    (h : LiftStmtRel Dτ D (.loop g measure invariants body md) target) :
    target = .loop g measure invariants body md ∧
      LiftBlockRel Dτ D body body := by
  have ht : target = .loop g measure invariants body md := by
    simpa [Stmt.liftInitsInLoopBody] using congrArg List.head? h.residual.symm
  have hparts : (Block.initVars body).isEmpty = true ∧
      Block.loopBodyNoInits body = true := by
    simpa only [Stmt.loopBodyNoInits, Bool.and_eq_true] using h.loopBodies
  have hinitNil : Block.initVars body = [] := by
    simpa only [List.isEmpty_iff] using hparts.1
  have hnone : Block.noInitsAnywhere body = true :=
    Block.noInitsAnywhere_of_initVars_nil body hinitNil
  refine ⟨ht, ⟨LoopInitHoistProducerProps.liftP_body_residual_no_inits body hnone,
    hparts.2, ?_⟩⟩
  intro p hp
  rw [LoopInitHoistProducerProps.Block.typedInitVars_eq_nil_of_noInitsAnywhere body hnone] at hp
  exact absurd hp List.not_mem_nil

/-- Every source event step from related lift configurations is matched by a
finite target execution that restores the relation. -/
theorem liftConfigRel_stepE {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident] [LawfulHasVal P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident} {factory : P.Factory}
    (hmono : WellFormedSemanticEvalMono factory)
    {source source' target : Config P (Cmd P)} {sourceTrace : Trace P}
    (hrel : LiftConfigRel Dτ D factory source target)
    (hstep : StepStmtE P (EvalCmdE P) source sourceTrace source') :
    ∃ target' targetTrace,
      StepStmtStarE P (EvalCmdE P) target targetTrace target' ∧
      LiftConfigRel Dτ D factory source' target' ∧
      TraceStuttersEnv (fun _ : P.Ident => True) (fun _ : P.Factory => True) sourceTrace targetTrace ∧
      TraceExtendsEnv (fun _ : P.Ident => True) sourceTrace targetTrace := by
  induction hstep generalizing target with
  | step_cmd heval =>
      cases hrel with
      | stmt henv hstmt =>
          cases heval with
          | eval_init he hstate hty hwf =>
              rename_i e v y ty md
              have ht := hstmt.residual
              simp only [Stmt.liftInitsInLoopBody, List.cons.injEq, and_true] at ht
              subst_vars
              have hp := hstmt.typedInits (y, ty) (by
                simp [LoopInitHoistProducerProps.Stmt.typedInitVars])
              obtain ⟨σt', targetTrace, heval', hagree, htyped, hlock⟩ :=
                initToSetEvalCmdE_lockstep y ty (.det e) md _ _ _ []
                  (henv.targetFactory.trans henv.sourceFactory.symm)
                  henv.agreement henv.typed hp.1 hp.2
                  (by simpa [henv.sourceFactory] using hmono)
                  (.eval_init he hstate hty hwf)
              exact ⟨_, targetTrace, Imperative.StepStmtStarE.single (.step_cmd heval'),
                .terminal ⟨hagree, henv.sourceFactory, henv.targetFactory,
                  htyped⟩, ⟨hlock.toTraceStuttersEnv, hlock⟩⟩
          | eval_init_unconstrained hstate hty hwf =>
              rename_i y v ty md
              have ht := hstmt.residual
              simp only [Stmt.liftInitsInLoopBody, List.cons.injEq, and_true] at ht
              subst_vars
              have hp := hstmt.typedInits (y, ty) (by
                simp [LoopInitHoistProducerProps.Stmt.typedInitVars])
              obtain ⟨σt', targetTrace, heval', hagree, htyped, hlock⟩ :=
                initToSetEvalCmdE_lockstep y ty .nondet md _ _ _ []
                  (henv.targetFactory.trans henv.sourceFactory.symm)
                  henv.agreement henv.typed hp.1 hp.2
                  (by simpa [henv.sourceFactory] using hmono)
                  (.eval_init_unconstrained hstate hty hwf)
              exact ⟨_, targetTrace, Imperative.StepStmtStarE.single (.step_cmd heval'),
                .terminal ⟨hagree, henv.sourceFactory, henv.targetFactory,
                  htyped⟩, ⟨hlock.toTraceStuttersEnv, hlock⟩⟩
          | eval_set he hstate hty hwf =>
              rename_i e v y md
              have ht := hstmt.residual
              simp only [Stmt.liftInitsInLoopBody, List.cons.injEq, and_true] at ht
              subst_vars
              obtain ⟨σt', targetTrace, heval', hagree, htyped, hlock⟩ :=
                evalCmdE_replay_agreement_typed_lockstep
                  (henv.targetFactory.trans henv.sourceFactory.symm)
                  henv.agreement henv.typed (.eval_set he hstate hty hwf)
                  (by simpa [henv.sourceFactory] using hmono) (by simp [Cmd.definedVars])
              exact ⟨_, targetTrace, Imperative.StepStmtStarE.single (.step_cmd heval'),
                .terminal ⟨hagree, henv.sourceFactory, henv.targetFactory,
                  htyped⟩, ⟨hlock.toTraceStuttersEnv, hlock⟩⟩
          | eval_set_nondet hstate hty hwf =>
              rename_i y v md
              have ht := hstmt.residual
              simp only [Stmt.liftInitsInLoopBody, List.cons.injEq, and_true] at ht
              subst_vars
              obtain ⟨σt', targetTrace, heval', hagree, htyped, hlock⟩ :=
                evalCmdE_replay_agreement_typed_lockstep
                  (henv.targetFactory.trans henv.sourceFactory.symm)
                  henv.agreement henv.typed (.eval_set_nondet hstate hty hwf)
                  (by simpa [henv.sourceFactory] using hmono) (by simp [Cmd.definedVars])
              exact ⟨_, targetTrace, Imperative.StepStmtStarE.single (.step_cmd heval'),
                .terminal ⟨hagree, henv.sourceFactory, henv.targetFactory,
                  htyped⟩, ⟨hlock.toTraceStuttersEnv, hlock⟩⟩
          | eval_assert =>
              rename_i label e md
              have ht := hstmt.residual
              simp only [Stmt.liftInitsInLoopBody, List.cons.injEq, and_true] at ht
              subst_vars
              obtain ⟨σt', targetTrace, heval', hagree, htyped, hlock⟩ :=
                evalCmdE_replay_agreement_typed_lockstep
                  (henv.targetFactory.trans henv.sourceFactory.symm)
                  henv.agreement henv.typed (.eval_assert)
                  (by simpa [henv.sourceFactory] using hmono) (by simp [Cmd.definedVars])
              exact ⟨_, targetTrace, Imperative.StepStmtStarE.single (.step_cmd heval'),
                .terminal ⟨hagree, henv.sourceFactory, henv.targetFactory,
                  htyped⟩, ⟨hlock.toTraceStuttersEnv, hlock⟩⟩
          | eval_assume =>
              rename_i label e md
              have ht := hstmt.residual
              simp only [Stmt.liftInitsInLoopBody, List.cons.injEq, and_true] at ht
              subst_vars
              obtain ⟨σt', targetTrace, heval', hagree, htyped, hlock⟩ :=
                evalCmdE_replay_agreement_typed_lockstep
                  (henv.targetFactory.trans henv.sourceFactory.symm)
                  henv.agreement henv.typed (.eval_assume)
                  (by simpa [henv.sourceFactory] using hmono) (by simp [Cmd.definedVars])
              exact ⟨_, targetTrace, Imperative.StepStmtStarE.single (.step_cmd heval'),
                .terminal ⟨hagree, henv.sourceFactory, henv.targetFactory,
                  htyped⟩, ⟨hlock.toTraceStuttersEnv, hlock⟩⟩
          | eval_cover =>
              rename_i label e md
              have ht := hstmt.residual
              simp only [Stmt.liftInitsInLoopBody, List.cons.injEq, and_true] at ht
              subst_vars
              obtain ⟨σt', targetTrace, heval', hagree, htyped, hlock⟩ :=
                evalCmdE_replay_agreement_typed_lockstep
                  (henv.targetFactory.trans henv.sourceFactory.symm)
                  henv.agreement henv.typed (.eval_cover)
                  (by simpa [henv.sourceFactory] using hmono) (by simp [Cmd.definedVars])
              exact ⟨_, targetTrace, Imperative.StepStmtStarE.single (.step_cmd heval'),
                .terminal ⟨hagree, henv.sourceFactory, henv.targetFactory,
                  htyped⟩, ⟨hlock.toTraceStuttersEnv, hlock⟩⟩
  | step_block =>
      cases hrel with
      | stmt henv hstmt =>
          obtain ⟨rfl, hbody⟩ := hstmt.blockBody
          refine ⟨_, [], Imperative.StepStmtStarE.single .step_block,
            .block henv.storeRel (.stmts henv hbody), ⟨.nil, .nil⟩⟩
  | step_ite_true heval =>
      cases hrel with
      | stmt henv hstmt =>
          obtain ⟨rfl, hthen, _⟩ := hstmt.iteBranches
          have heval' := henv.evalBool HasBool.ttVal hmono heval
          refine ⟨_, [], Imperative.StepStmtStarE.single
            (.step_ite_true heval'),
            .block henv.storeRel (.stmts henv hthen), ⟨.nil, .nil⟩⟩
  | step_ite_false heval =>
      cases hrel with
      | stmt henv hstmt =>
          obtain ⟨rfl, _, helse⟩ := hstmt.iteBranches
          have heval' := henv.evalBool HasBool.ffVal hmono heval
          refine ⟨_, [], Imperative.StepStmtStarE.single
            (.step_ite_false heval'),
            .block henv.storeRel (.stmts henv helse), ⟨.nil, .nil⟩⟩
  | step_ite_nondet_true =>
      cases hrel with
      | stmt henv hstmt =>
          obtain ⟨rfl, hthen, _⟩ := hstmt.iteBranches
          refine ⟨_, [], Imperative.StepStmtStarE.single
            .step_ite_nondet_true,
            .block henv.storeRel (.stmts henv hthen), ⟨.nil, .nil⟩⟩
  | step_ite_nondet_false =>
      cases hrel with
      | stmt henv hstmt =>
          obtain ⟨rfl, _, helse⟩ := hstmt.iteBranches
          refine ⟨_, [], Imperative.StepStmtStarE.single
            .step_ite_nondet_false,
            .block henv.storeRel (.stmts henv helse), ⟨.nil, .nil⟩⟩
  | step_loop_enter heval =>
      cases hrel with
      | stmt henv hstmt =>
          obtain ⟨rfl, hbody⟩ := hstmt.loopBody
          have heval' := henv.evalBool HasBool.ttVal hmono heval
          have htail := hstmt.singleton
          refine ⟨_, [], Imperative.StepStmtStarE.single
            (.step_loop_enter heval'),
            .seq (.block henv.storeRel (.stmts henv hbody)) htail, ⟨.nil, .nil⟩⟩
  | step_loop_exit heval =>
      cases hrel with
      | stmt henv hstmt =>
          obtain ⟨rfl, _⟩ := hstmt.loopBody
          have heval' := henv.evalBool HasBool.ffVal hmono heval
          exact ⟨_, [], Imperative.StepStmtStarE.single
            (.step_loop_exit heval'),
            .terminal henv, ⟨.nil, .nil⟩⟩
  | step_loop_nondet_enter =>
      cases hrel with
      | stmt henv hstmt =>
          obtain ⟨rfl, hbody⟩ := hstmt.loopBody
          have htail := hstmt.singleton
          refine ⟨_, [], Imperative.StepStmtStarE.single
            .step_loop_nondet_enter,
            .seq (.block henv.storeRel (.stmts henv hbody)) htail, ⟨.nil, .nil⟩⟩
  | step_loop_nondet_exit =>
      cases hrel with
      | stmt henv hstmt =>
          obtain ⟨rfl, _⟩ := hstmt.loopBody
          exact ⟨_, [], Imperative.StepStmtStarE.single
            .step_loop_nondet_exit,
            .terminal henv, ⟨.nil, .nil⟩⟩
  | step_exit =>
      cases hrel with
      | stmt henv hstmt =>
          have ht := hstmt.residual
          simp only [Stmt.liftInitsInLoopBody, List.cons.injEq, and_true] at ht
          subst_vars
          exact ⟨_, [], Imperative.StepStmtStarE.single .step_exit,
            .exiting henv, ⟨.nil, .nil⟩⟩
  | step_typeDecl =>
      cases hrel with
      | stmt henv hstmt =>
          have ht := hstmt.residual
          simp only [Stmt.liftInitsInLoopBody, List.cons.injEq, and_true] at ht
          subst_vars
          exact ⟨_, [], Imperative.StepStmtStarE.single .step_typeDecl,
            .terminal henv, ⟨.nil, .nil⟩⟩
  | step_stmts_nil =>
      cases hrel with
      | stmts henv hblock =>
          have ht := hblock.residual
          simp only [Block.liftInitsInLoopBody, List.nil_eq] at ht
          subst_vars
          exact ⟨_, [], Imperative.StepStmtStarE.single .step_stmts_nil,
            .terminal henv, ⟨.nil, .nil⟩⟩
  | step_stmts_cons =>
      cases hrel with
      | stmts henv hblock =>
          obtain ⟨s', rest', rfl, hs, hr⟩ := hblock.cons
          exact ⟨_, [], Imperative.StepStmtStarE.single .step_stmts_cons,
            .seq (.stmt henv hs) hr, ⟨.nil, .nil⟩⟩
  | step_seq_done =>
      cases hrel with
      | seq hinner hrest =>
          cases hinner with
          | terminal henv =>
              exact ⟨_, [], Imperative.StepStmtStarE.single .step_seq_done,
                .stmts henv hrest, ⟨.nil, .nil⟩⟩
  | step_seq_exit =>
      cases hrel with
      | seq hinner _ =>
          cases hinner with
          | exiting henv =>
              exact ⟨_, [], Imperative.StepStmtStarE.single .step_seq_exit,
                .exiting henv, ⟨.nil, .nil⟩⟩
  | step_block_done =>
      cases hrel with
      | block hparent hinner =>
          cases hinner with
          | terminal henv =>
              exact ⟨_, [], Imperative.StepStmtStarE.single .step_block_done,
                .terminal (LiftEnvRel.project hparent henv), ⟨.nil, .nil⟩⟩
  | step_block_exit_match heq =>
      cases hrel with
      | block hparent hinner =>
          cases hinner with
          | exiting henv =>
              exact ⟨_, [], Imperative.StepStmtStarE.single
                (.step_block_exit_match heq),
                .terminal (LiftEnvRel.project hparent henv), ⟨.nil, .nil⟩⟩
  | step_block_exit_mismatch hne =>
      cases hrel with
      | block hparent hinner =>
          cases hinner with
          | exiting henv =>
              exact ⟨_, [], Imperative.StepStmtStarE.single
                (.step_block_exit_mismatch hne),
                .exiting (LiftEnvRel.project hparent henv), ⟨.nil, .nil⟩⟩
  | step_seq_inner hinner ih =>
      cases hrel with
      | seq hinnerRel hrest =>
          obtain ⟨targetInner', targetTrace, hrun, hrel', htrace⟩ := ih hinnerRel
          exact ⟨_, targetTrace, seq_inner_starE (EvalCmdE P) hrun,
            .seq hrel' hrest, htrace⟩
  | step_block_body hinner ih =>
      cases hrel with
      | block hparent hinnerRel =>
          obtain ⟨targetInner', targetTrace, hrun, hrel', htrace⟩ := ih hinnerRel
          exact ⟨_, targetTrace, block_inner_starE hrun,
            .block hparent hrel', htrace⟩

/-- Every finite source prefix from related lift configurations has a target
prefix with a related residual configuration and an environment-extending
trace. Terminal and exiting configurations are included as ordinary related
endpoints. -/
theorem liftConfigRel_reflTransTrace {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident] [LawfulHasVal P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident} {factory : P.Factory}
    (hmono : WellFormedSemanticEvalMono factory)
    {source target source' : Config P (Cmd P)} {sourceTrace : Trace P}
    (hrel : LiftConfigRel Dτ D factory source target)
    (hrun : StepStmtStarE P (EvalCmdE P) source sourceTrace source') :
    ∃ target' targetTrace,
      StepStmtStarE P (EvalCmdE P) target targetTrace target' ∧
      LiftConfigRel Dτ D factory source' target' ∧
      TraceStuttersEnv (fun _ : P.Ident => True) (fun _ : P.Factory => True) sourceTrace targetTrace ∧
      TraceExtendsEnv (fun _ : P.Ident => True) sourceTrace targetTrace := by
  induction hrun generalizing target with
  | refl => exact ⟨target, [], .refl _, hrel, ⟨.nil, .nil⟩⟩
  | step source emitted middle rest source' hstep _ ih =>
      obtain ⟨targetMiddle, targetHead, hhead, hmiddle, htraceHead⟩ :=
        liftConfigRel_stepE hmono hrel hstep
      obtain ⟨target', targetTail, htail, hfinal, htraceTail⟩ := ih hmiddle
      exact ⟨target', targetHead ++ targetTail,
        ReflTransTrace.trans _ hhead htail, hfinal,
        ⟨TraceStuttersEnv.append htraceHead.1 htraceTail.1,
          TraceExtendsEnv.append htraceHead.2 htraceTail.2⟩⟩

structure HoistEnvRel {P : PureExpr}
    (factory : P.Factory) (source target : Env P) : Prop where
  agreement : StoreAgreement source.store target.store
  sourceFactory : source.factory = factory
  targetFactory : target.factory = factory

structure HoistStoreRel {P : PureExpr}
    (source target : SemanticStore P) : Prop where
  agreement : StoreAgreement source target

private theorem HoistEnvRel.storeRel {P : PureExpr}
    {factory : P.Factory} {source target : Env P}
    (h : HoistEnvRel factory source target) : HoistStoreRel source.store target.store :=
  ⟨h.agreement⟩

private theorem HoistEnvRel.project {P : PureExpr}
    {factory : P.Factory} {sourceParent targetParent : SemanticStore P}
    {sourceInner targetInner : Env P}
    (hp : HoistStoreRel sourceParent targetParent)
    (hi : HoistEnvRel factory sourceInner targetInner) :
    HoistEnvRel factory
      { sourceInner with store := projectStore sourceParent sourceInner.store }
      { targetInner with store := projectStore targetParent targetInner.store } :=
  ⟨StoreAgreement.of_projectStore_parents hp.agreement hi.agreement,
    hi.sourceFactory, hi.targetFactory⟩

private theorem HoistEnvRel.eval {P : PureExpr} [HasFvars P]
    {factory : P.Factory} {source target : Env P} {e : P.Expr} {v : P.Val}
    (h : HoistEnvRel factory source target)
    (hmono : WellFormedSemanticEvalMono factory)
    (he : P.eval source.factory source.store e = some v) :
    P.eval target.factory target.store e = some v := by
  rw [h.sourceFactory] at he
  rw [h.targetFactory]
  exact hmono e v source.store target.store
    (storeAgreement_supplies_mono_premise _ _ h.agreement) he

/-- `HoistEnvRel.eval` at the factory's Boolean values: the value read in the target is
    the target factory's Boolean (the related environments share their factory). -/
private theorem HoistEnvRel.evalBool {P : PureExpr} [HasFvars P] [HasBool P]
    {factory : P.Factory} {source target : Env P} {e : P.Expr} (b : P.Factory → P.Val)
    (h : HoistEnvRel factory source target)
    (hmono : WellFormedSemanticEvalMono factory)
    (he : P.eval source.factory source.store e = some (b source.factory)) :
    P.eval target.factory target.store e = some (b target.factory) := by
  have := h.eval hmono he
  rwa [h.sourceFactory, ← h.targetFactory] at this

private theorem Config.varsUndefinedThroughout_starE {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [HasInt P]
    [DecidableEq P.Ident]
    {Q : P.Ident → Prop} {source target : Config P (Cmd P)} {trace : Trace P}
    (hrun : StepStmtStarE P (EvalCmdE P) source trace target)
    (hinv : Config.varsUndefined false Q source) :
    Config.varsUndefined false Q target :=
  Config.varsUndefinedThroughout_star_ofE
    (fun heval hnone hndef => evalCmdE_preserves_none_of_not_def heval hnone
      (by simpa [HasVarsImp.definedVars] using hndef))
    hrun hinv

structure ConfigTraceSim {P : PureExpr} [HasFvar P] [HasBoolOps P]
    (Rel : Env P → Env P → Prop)
    (source target : Config P (Cmd P)) : Prop where
  simulate : ∀ {source' : Config P (Cmd P)} {sourceTrace : Trace P},
    StepStmtStarE P (EvalCmdE P) source sourceTrace source' →
    ∃ target' targetTrace,
      StepStmtStarE P (EvalCmdE P) target targetTrace target' ∧
      TraceExtendsEnv (fun _ : P.Ident => True) sourceTrace targetTrace
  terminal : ∀ {sourceEnv : Env P} {sourceTrace : Trace P},
    StepStmtStarE P (EvalCmdE P) source sourceTrace (.terminal sourceEnv) →
    ∃ targetEnv targetTrace,
      StepStmtStarE P (EvalCmdE P) target targetTrace (.terminal targetEnv) ∧
      Rel sourceEnv targetEnv ∧
      TraceExtendsEnv (fun _ : P.Ident => True) sourceTrace targetTrace
  exiting : ∀ {label : String} {sourceEnv : Env P} {sourceTrace : Trace P},
    StepStmtStarE P (EvalCmdE P) source sourceTrace (.exiting label sourceEnv) →
    ∃ targetEnv targetTrace,
      StepStmtStarE P (EvalCmdE P) target targetTrace (.exiting label targetEnv) ∧
      Rel sourceEnv targetEnv ∧
      TraceExtendsEnv (fun _ : P.Ident => True) sourceTrace targetTrace

def StmtHoistTraceSim {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [HasInt P]
    [DecidableEq P.Ident]
    (source : Stmt P (Cmd P)) (target : List (Stmt P (Cmd P))) : Prop :=
  ∀ (sourceEnv targetEnv : Env P),
    HoistEnvRel sourceEnv.factory sourceEnv targetEnv →
    WellFormedSemanticEvalBool sourceEnv.factory →
    WellFormedSemanticEvalVal sourceEnv.factory →
    WellFormedSemanticEvalMono sourceEnv.factory →
    WellFormedSemanticEvalExprCongr sourceEnv.factory →
    WellFormedSemanticEvalVar sourceEnv.factory →
    (∀ y ∈ Stmt.initVars source, sourceEnv.store y = none) →
    (∀ y ∈ Stmt.initVars source, targetEnv.store y = none) →
    Stmt.InitTypesInhabited sourceEnv.factory source →
    ConfigTraceSim (HoistEnvRel sourceEnv.factory)
      (.stmt source sourceEnv) (.stmts target targetEnv)

def BlockHoistTraceSim {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [HasInt P]
    [DecidableEq P.Ident]
    (source target : List (Stmt P (Cmd P))) : Prop :=
  ∀ (sourceEnv targetEnv : Env P),
    HoistEnvRel sourceEnv.factory sourceEnv targetEnv →
    WellFormedSemanticEvalBool sourceEnv.factory →
    WellFormedSemanticEvalVal sourceEnv.factory →
    WellFormedSemanticEvalMono sourceEnv.factory →
    WellFormedSemanticEvalExprCongr sourceEnv.factory →
    WellFormedSemanticEvalVar sourceEnv.factory →
    (∀ y ∈ Block.initVars source, sourceEnv.store y = none) →
    (∀ y ∈ Block.initVars source, targetEnv.store y = none) →
    Block.InitTypesInhabited sourceEnv.factory source →
    ConfigTraceSim (HoistEnvRel sourceEnv.factory)
      (.stmts source sourceEnv) (.stmts target targetEnv)

private theorem HoistEnvRel.trans {P : PureExpr}
    {factory : P.Factory} {first middle last : Env P}
    (h₁ : HoistEnvRel factory first middle)
    (h₂ : HoistEnvRel factory middle last) :
    HoistEnvRel factory first last :=
  ⟨StoreAgreement.trans h₁.agreement h₂.agreement,
    h₁.sourceFactory, h₂.targetFactory⟩

private theorem liftEnvRel_to_hoist {P : PureExpr} [HasVal P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident} {factory : P.Factory}
    {source target : Env P}
    (h : LiftEnvRel Dτ D factory source target) :
    HoistEnvRel factory source target :=
  ⟨h.agreement, h.sourceFactory, h.targetFactory⟩

private theorem ConfigTraceSim.trans {P : PureExpr} [HasFvar P] [HasBoolOps P]
    {R₁ R₂ R₃ : Env P → Env P → Prop}
    (hrel : ∀ a b c, R₁ a b → R₂ b c → R₃ a c)
    {source middle target : Config P (Cmd P)}
    (h₁ : ConfigTraceSim R₁ source middle)
    (h₂ : ConfigTraceSim R₂ middle target) :
    ConfigTraceSim R₃ source target := by
  refine ⟨?_, ?_, ?_⟩
  · intro source' sourceTrace hrun
    obtain ⟨middle', middleTrace, hmiddle, htrace₁⟩ := h₁.simulate hrun
    obtain ⟨target', targetTrace, htarget, htrace₂⟩ := h₂.simulate hmiddle
    exact ⟨target', targetTrace, htarget, TraceExtendsEnv.trans htrace₁ htrace₂⟩
  · intro sourceEnv sourceTrace hrun
    obtain ⟨middleEnv, middleTrace, hmiddle, hrel₁, htrace₁⟩ := h₁.terminal hrun
    obtain ⟨targetEnv, targetTrace, htarget, hrel₂, htrace₂⟩ := h₂.terminal hmiddle
    exact ⟨targetEnv, targetTrace, htarget, hrel _ _ _ hrel₁ hrel₂,
      TraceExtendsEnv.trans htrace₁ htrace₂⟩
  · intro label sourceEnv sourceTrace hrun
    obtain ⟨middleEnv, middleTrace, hmiddle, hrel₁, htrace₁⟩ := h₁.exiting hrun
    obtain ⟨targetEnv, targetTrace, htarget, hrel₂, htrace₂⟩ := h₂.exiting hmiddle
    exact ⟨targetEnv, targetTrace, htarget, hrel _ _ _ hrel₁ hrel₂,
      TraceExtendsEnv.trans htrace₁ htrace₂⟩

private theorem ConfigTraceSim.targetSingleton {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {R : Env P → Env P → Prop} {source : Config P (Cmd P)}
    {targetStmt : Stmt P (Cmd P)} {targetEnv : Env P}
    (h : ConfigTraceSim R source (.stmt targetStmt targetEnv)) :
    ConfigTraceSim R source (.stmts [targetStmt] targetEnv) := by
  refine ⟨?_, ?_, ?_⟩
  · intro source' sourceTrace hrun
    obtain ⟨target', targetTrace, htarget, htrace⟩ := h.simulate hrun
    refine ⟨.seq target' [], targetTrace, ?_, htrace⟩
    exact ReflTransTrace.step _ _ _ _ _ .step_stmts_cons
      (seq_inner_starE (EvalCmdE P) htarget)
  · intro sourceEnv sourceTrace hrun
    obtain ⟨targetEnv', targetTrace, htarget, hrel, htrace⟩ := h.terminal hrun
    exact ⟨targetEnv', targetTrace, stmtRun_to_singletonE (EvalCmdE P) htarget,
      hrel, htrace⟩
  · intro label sourceEnv sourceTrace hrun
    obtain ⟨targetEnv', targetTrace, htarget, hrel, htrace⟩ := h.exiting hrun
    have hfull := ReflTransTrace.trans _
      (ReflTransTrace.step _ _ _ _ _ .step_stmts_cons
        (seq_inner_starE (EvalCmdE P) htarget))
      (Imperative.StepStmtStarE.single
        (c := .seq (.exiting label targetEnv') []) .step_seq_exit)
    exact ⟨targetEnv', targetTrace, by simpa using hfull, hrel, htrace⟩

private theorem liftConfigRel_traceSim {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident] [LawfulHasVal P]
    {Dτ : P.Ident → P.Ty} {D : List P.Ident} {factory : P.Factory}
    (hmono : WellFormedSemanticEvalMono factory)
    {source target : Config P (Cmd P)}
    (hrel : LiftConfigRel Dτ D factory source target) :
    ConfigTraceSim (LiftEnvRel Dτ D factory) source target := by
  refine ⟨?_, ?_, ?_⟩
  · intro source' sourceTrace hrun
    obtain ⟨target', targetTrace, htarget, _, _, hlock⟩ :=
      liftConfigRel_reflTransTrace hmono hrel hrun
    exact ⟨target', targetTrace, htarget, hlock⟩
  · intro sourceEnv sourceTrace hrun
    obtain ⟨target', targetTrace, htarget, hfinal, _, hlock⟩ :=
      liftConfigRel_reflTransTrace hmono hrel hrun
    cases hfinal with
    | terminal henv => exact ⟨_, targetTrace, htarget, henv, hlock⟩
  · intro label sourceEnv sourceTrace hrun
    obtain ⟨target', targetTrace, htarget, hfinal, _, hlock⟩ :=
      liftConfigRel_reflTransTrace hmono hrel hrun
    cases hfinal with
    | exiting henv => exact ⟨_, targetTrace, htarget, henv, hlock⟩

/-- `LoopGuardEnter g ρ` holds when the guard `g` admits *entering* a loop body
(or taking the *then*-branch of an `ite`) from `ρ`.  A deterministic guard admits
entry exactly when it evaluates to `true`; a nondeterministic guard always admits
entry.  The guard expression, a loop's measure, and its invariants are
operationally inert: only this predicate gates the structured control-flow step. -/
def LoopGuardEnter {P : PureExpr} [HasFvar P] [HasBoolOps P]
    (g : ExprOrNondet P) (ρ : Env P) : Prop :=
  match g with
  | .det guard => P.eval ρ.factory ρ.store guard = some (HasBool.ttVal ρ.factory)
  | .nondet => True

/-- `LoopGuardExit g ρ` holds when the guard `g` admits *exiting* a loop (or taking
the *else*-branch of an `ite`) from `ρ`.  Dual to `LoopGuardEnter`. -/
def LoopGuardExit {P : PureExpr} [HasFvar P] [HasBoolOps P]
    (g : ExprOrNondet P) (ρ : Env P) : Prop :=
  match g with
  | .det guard => P.eval ρ.factory ρ.store guard = some (HasBool.ffVal ρ.factory)
  | .nondet => True

/-- Build the single loop *enter* step for an arbitrary guard, measure, and
invariant list. -/
private theorem loopEnterStepE {P : PureExpr} [HasFvar P] [HasBoolOps P]
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P} {ρ : Env P}
    (h : LoopGuardEnter g ρ) :
    StepStmtE P (EvalCmdE P)
      (.stmt (.loop g m inv body md) ρ) []
      (.seq (.block .none ρ.store (.stmts body ρ)) [.loop g m inv body md]) := by
  cases g with
  | det guard => exact (.step_loop_enter h)
  | nondet => exact .step_loop_nondet_enter

/-- Build the single loop *exit* step for an arbitrary guard, measure, and
invariant list. -/
private theorem loopExitStepE {P : PureExpr} [HasFvar P] [HasBoolOps P]
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P} {ρ : Env P}
    (h : LoopGuardExit g ρ) :
    StepStmtE P (EvalCmdE P)
      (.stmt (.loop g m inv body md) ρ) [] (.terminal ρ) := by
  cases g with
  | det guard => exact (.step_loop_exit h)
  | nondet => exact .step_loop_nondet_exit

/-- Invert the first step of a loop: it is either an enter (into the body block
sequenced with the recursive loop) or an exit (to the current terminal store),
each gated by the corresponding guard predicate.  Covers deterministic and
nondeterministic guards uniformly and is independent of the measure/invariant
annotations. -/
private theorem loop_stepE_inv {P : PureExpr} [HasFvar P] [HasBoolOps P]
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P} {ρ : Env P}
    {emitted : Trace P} {next : Config P (Cmd P)}
    (hstep : StepStmtE P (EvalCmdE P) (.stmt (.loop g m inv body md) ρ) emitted next) :
    (emitted = [] ∧
      next = .seq (.block .none ρ.store (.stmts body ρ)) [.loop g m inv body md] ∧
      LoopGuardEnter g ρ) ∨
    (emitted = [] ∧ next = .terminal ρ ∧ LoopGuardExit g ρ) := by
  cases g with
  | det guard =>
      cases hstep with
      | step_loop_enter htrue => exact .inl ⟨rfl, rfl, htrue⟩
      | step_loop_exit hfalse => exact .inr ⟨rfl, rfl, hfalse⟩
  | nondet =>
      cases hstep with
      | step_loop_nondet_enter => exact .inl ⟨rfl, rfl, trivial⟩
      | step_loop_nondet_exit => exact .inr ⟨rfl, rfl, trivial⟩

/-- Build the single `ite` *then* step for an arbitrary guard. -/
private theorem iteThenStepE {P : PureExpr} [HasFvar P] [HasBoolOps P]
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} {ρ : Env P}
    (h : LoopGuardEnter g ρ) :
    StepStmtE P (EvalCmdE P)
      (.stmt (.ite g tss ess md) ρ) []
      (.block .none ρ.store (.stmts tss ρ)) := by
  cases g with
  | det guard => exact (.step_ite_true h)
  | nondet => exact .step_ite_nondet_true

/-- Build the single `ite` *else* step for an arbitrary guard. -/
private theorem iteElseStepE {P : PureExpr} [HasFvar P] [HasBoolOps P]
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} {ρ : Env P}
    (h : LoopGuardExit g ρ) :
    StepStmtE P (EvalCmdE P)
      (.stmt (.ite g tss ess md) ρ) []
      (.block .none ρ.store (.stmts ess ρ)) := by
  cases g with
  | det guard => exact (.step_ite_false h)
  | nondet => exact .step_ite_nondet_false

/-- Invert the first step of an `ite`: it enters the then-branch or the
else-branch, each gated by the corresponding guard predicate. -/
private theorem ite_stepE_inv {P : PureExpr} [HasFvar P] [HasBoolOps P]
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} {ρ : Env P}
    {emitted : Trace P} {next : Config P (Cmd P)}
    (hstep : StepStmtE P (EvalCmdE P) (.stmt (.ite g tss ess md) ρ) emitted next) :
    (emitted = [] ∧ next = .block .none ρ.store (.stmts tss ρ) ∧ LoopGuardEnter g ρ) ∨
    (emitted = [] ∧ next = .block .none ρ.store (.stmts ess ρ) ∧ LoopGuardExit g ρ) := by
  cases g with
  | det guard =>
      cases hstep with
      | step_ite_true htrue => exact .inl ⟨rfl, rfl, htrue⟩
      | step_ite_false hfalse => exact .inr ⟨rfl, rfl, hfalse⟩
  | nondet =>
      cases hstep with
      | step_ite_nondet_true => exact .inl ⟨rfl, rfl, trivial⟩
      | step_ite_nondet_false => exact .inr ⟨rfl, rfl, trivial⟩

private theorem buildLoopIterationPrefixE {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {entry : Env P} {inner : Config P (Cmd P)} {trace : Trace P}
    (hguard : LoopGuardEnter g entry)
    (hbody : StepStmtStarE P (EvalCmdE P) (.stmts body entry) trace inner) :
    StepStmtStarE P (EvalCmdE P)
      (.stmt (.loop g m inv body md) entry) trace
      (.seq (.block .none entry.store inner)
        [.loop g m inv body md]) := by
  exact ReflTransTrace.step _ _ _ _ _ (loopEnterStepE hguard)
    (seq_inner_starE (EvalCmdE P) (block_inner_starE hbody))

private theorem buildLoopIterationTerminalE {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {entry inner : Env P} {trace : Trace P}
    (hguard : LoopGuardEnter g entry)
    (hbody : StepStmtStarE P (EvalCmdE P)
      (.stmts body entry) trace (.terminal inner)) :
    StepStmtStarE P (EvalCmdE P)
      (.stmt (.loop g m inv body md) entry) trace
      (.stmts [.loop g m inv body md]
        { inner with store := projectStore entry.store inner.store }) := by
  have hrun := buildLoopIterationPrefixE (g := g) (m := m) (inv := inv) (md := md) hguard hbody
  have hfull := ReflTransTrace.trans _ hrun
    (ReflTransTrace.step _ _ _ _ _
      (.step_seq_inner .step_block_done)
      (Imperative.StepStmtStarE.single .step_seq_done))
  simpa using hfull

private theorem buildLoopIterationExitE {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {entry inner : Env P} {trace : Trace P} {label : String}
    (hguard : LoopGuardEnter g entry)
    (hbody : StepStmtStarE P (EvalCmdE P)
      (.stmts body entry) trace (.exiting label inner)) :
    StepStmtStarE P (EvalCmdE P)
      (.stmt (.loop g m inv body md) entry) trace
      (.exiting label { inner with store := projectStore entry.store inner.store }) := by
  have hrun := buildLoopIterationPrefixE (g := g) (m := m) (inv := inv) (md := md) hguard hbody
  have hfull := ReflTransTrace.trans _ hrun
    (ReflTransTrace.step _ _ _ _ _
      (.step_seq_inner (.step_block_exit_mismatch (by simp)))
      (Imperative.StepStmtStarE.single .step_seq_exit))
  simpa using hfull

private theorem block_run_decomposeE {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {label : Option String} {parent : SemanticStore P}
    {inner final : Config P (Cmd P)} {trace : Trace P}
    (hrun : StepStmtStarE P (EvalCmdE P)
      (.block label parent inner) trace final) :
    (∃ inner', final = .block label parent inner' ∧
      StepStmtStarE P (EvalCmdE P) inner trace inner') ∨
    (∃ env, StepStmtStarE P (EvalCmdE P) inner trace (.terminal env) ∧
      final = .terminal { env with store := projectStore parent env.store }) ∨
    (∃ exitLabel env, label = some exitLabel ∧
      StepStmtStarE P (EvalCmdE P) inner trace (.exiting exitLabel env) ∧
      final = .terminal { env with store := projectStore parent env.store }) ∨
    (∃ exitLabel env, label ≠ some exitLabel ∧
      StepStmtStarE P (EvalCmdE P) inner trace (.exiting exitLabel env) ∧
      final = .exiting exitLabel { env with store := projectStore parent env.store }) := by
  suffices hgen : ∀ source sourceTrace target,
      StepStmtStarE P (EvalCmdE P) source sourceTrace target →
      ∀ inner, source = .block label parent inner →
      (∃ inner', target = .block label parent inner' ∧
        StepStmtStarE P (EvalCmdE P) inner sourceTrace inner') ∨
      (∃ env, StepStmtStarE P (EvalCmdE P) inner sourceTrace (.terminal env) ∧
        target = .terminal { env with store := projectStore parent env.store }) ∨
      (∃ exitLabel env, label = some exitLabel ∧
        StepStmtStarE P (EvalCmdE P) inner sourceTrace (.exiting exitLabel env) ∧
        target = .terminal { env with store := projectStore parent env.store }) ∨
      (∃ exitLabel env, label ≠ some exitLabel ∧
        StepStmtStarE P (EvalCmdE P) inner sourceTrace (.exiting exitLabel env) ∧
        target = .exiting exitLabel { env with store := projectStore parent env.store }) by
    exact hgen _ _ _ hrun _ rfl
  intro source sourceTrace target hrun'
  induction hrun' with
  | refl =>
      intro inner hsource
      subst hsource
      exact .inl ⟨_, rfl, .refl _⟩
  | step source emitted middle rest target hstep hrest ih =>
      intro inner hsource
      subst hsource
      rcases Imperative.StepStmtE.block_cases hstep with
        ⟨inner', hinner, rfl⟩ | ⟨env, rfl, rfl, rfl⟩ |
        ⟨exitLabel, env, rfl, rfl, heq, rfl⟩ |
        ⟨exitLabel, env, rfl, rfl, hne, rfl⟩
      · rcases ih _ rfl with
          ⟨inner'', hfinal, htail⟩ |
          ⟨env, htail, hfinal⟩ |
          ⟨exitLabel, env, heq, htail, hfinal⟩ |
          ⟨exitLabel, env, hne, htail, hfinal⟩
        · exact .inl ⟨inner'', hfinal, .step _ _ _ _ _ hinner htail⟩
        · exact .inr (.inl ⟨env, .step _ _ _ _ _ hinner htail, hfinal⟩)
        · exact .inr (.inr (.inl
            ⟨exitLabel, env, heq, .step _ _ _ _ _ hinner htail, hfinal⟩))
        · exact .inr (.inr (.inr
            ⟨exitLabel, env, hne, .step _ _ _ _ _ hinner htail, hfinal⟩))
      · obtain ⟨hfinal, htrace⟩ := stepStmtStarE_from_terminal hrest
        subst htrace
        exact .inr (.inl ⟨env, .refl _, hfinal⟩)
      · obtain ⟨hfinal, htrace⟩ := stepStmtStarE_from_terminal hrest
        subst htrace
        exact .inr (.inr (.inl ⟨exitLabel, env, heq, .refl _, hfinal⟩))
      · obtain ⟨hfinal, htrace⟩ := stepStmtStarE_from_exiting hrest
        subst htrace
        exact .inr (.inr (.inr ⟨exitLabel, env, hne, .refl _, hfinal⟩))

private theorem seqT_reaches_exitingE {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {inner : Config P (Cmd P)} {rest : List (Stmt P (Cmd P))}
    {label : String} {finalEnv : Env P} {trace : Trace P}
    (hrun : ReflTransTraceT (StepStmtE P (EvalCmdE P))
      (.seq inner rest) trace (.exiting label finalEnv)) :
    (∃ hinner : ReflTransTraceT (StepStmtE P (EvalCmdE P))
        inner trace (.exiting label finalEnv), hinner.len < hrun.len) ∨
    (∃ middleEnv headTrace tailTrace,
      trace = headTrace ++ tailTrace ∧
      ∃ hhead : ReflTransTraceT (StepStmtE P (EvalCmdE P))
          inner headTrace (.terminal middleEnv),
      ∃ htail : ReflTransTraceT (StepStmtE P (EvalCmdE P))
          (.stmts rest middleEnv) tailTrace (.exiting label finalEnv),
      hhead.len < hrun.len ∧ htail.len < hrun.len) := by
  match hrun with
  | .step _ emitted _ restTrace _ (.step_seq_inner hstep) htail =>
      rcases seqT_reaches_exitingE htail with ⟨hinner, hlen⟩ |
        ⟨middleEnv, headTrace, tailTrace, htrace, hhead, hrest, hlen⟩
      · exact .inl ⟨.step _ _ _ _ _ hstep hinner,
          by simp only [ReflTransTraceT.len]; omega⟩
      · exact .inr ⟨middleEnv, emitted ++ headTrace, tailTrace,
          by rw [htrace]; simp [List.append_assoc],
          .step _ _ _ _ _ hstep hhead, hrest,
          ⟨by simp only [ReflTransTraceT.len]; omega,
           by simp only [ReflTransTraceT.len]; omega⟩⟩
  | .step _ _ _ restTrace _ .step_seq_done htail =>
      exact .inr ⟨_, [], restTrace, by simp, .refl _, htail,
        ⟨by simpa [ReflTransTraceT.len, Nat.add_comm] using Nat.zero_lt_succ htail.len,
         by simp [ReflTransTraceT.len]⟩⟩
  | .step _ _ _ _ _ .step_seq_exit htail =>
      match htail with
      | .refl _ => exact .inl ⟨.refl _, by simp [ReflTransTraceT.len]⟩
      | .step _ _ _ _ _ hstep _ => exact (Imperative.StepStmtE.exiting_false hstep).elim
termination_by hrun.len
decreasing_by all_goals simp only [ReflTransTraceT.len]; omega

private theorem stmtsT_cons_exitingE {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {stmt : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))}
    {entry finalEnv : Env P} {label : String} {trace : Trace P}
    (hrun : ReflTransTraceT (StepStmtE P (EvalCmdE P))
      (.stmts (stmt :: rest) entry) trace (.exiting label finalEnv)) :
    (∃ hhead : ReflTransTraceT (StepStmtE P (EvalCmdE P))
        (.stmt stmt entry) trace (.exiting label finalEnv),
      hhead.len < hrun.len) ∨
    (∃ middleEnv headTrace tailTrace,
      trace = headTrace ++ tailTrace ∧
      ∃ hhead : ReflTransTraceT (StepStmtE P (EvalCmdE P))
          (.stmt stmt entry) headTrace (.terminal middleEnv),
      ∃ htail : ReflTransTraceT (StepStmtE P (EvalCmdE P))
          (.stmts rest middleEnv) tailTrace (.exiting label finalEnv),
      hhead.len < hrun.len ∧ htail.len < hrun.len) := by
  match hrun with
  | .step _ _ _ restTrace _ .step_stmts_cons htail =>
      rcases seqT_reaches_exitingE htail with ⟨hhead, hlen⟩ |
        ⟨middleEnv, headTrace, tailTrace, htrace, hhead, hrest, hlen⟩
      · exact .inl ⟨hhead,
          by simpa [ReflTransTraceT.len, Nat.add_comm] using Nat.lt_succ_of_lt hlen⟩
      · exact .inr ⟨middleEnv, headTrace, tailTrace, htrace, hhead, hrest,
          ⟨by simpa [ReflTransTraceT.len, Nat.add_comm] using Nat.lt_succ_of_lt hlen.1,
           by simpa [ReflTransTraceT.len, Nat.add_comm] using Nat.lt_succ_of_lt hlen.2⟩⟩

private theorem loopTraceSim_terminal_fuel {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {R B : Env P → Env P → Prop}
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {sourceBody targetBody : List (Stmt P (Cmd P))}
    {sourceMd targetMd : MetaData P}
    (henterTarget : ∀ source target, R source target →
      LoopGuardEnter g source → LoopGuardEnter g target)
    (hexitTarget : ∀ source target, R source target →
      LoopGuardExit g source → LoopGuardExit g target)
    (hproject : ∀ sourceParent targetParent sourceInner targetInner,
      R sourceParent targetParent → B sourceInner targetInner →
      R { sourceInner with store := projectStore sourceParent.store sourceInner.store }
        { targetInner with store := projectStore targetParent.store targetInner.store })
    (hbody : ∀ source target, R source target →
      ConfigTraceSim B (.stmts sourceBody source) (.stmts targetBody target)) :
    ∀ n source target finalEnv sourceTrace,
      R source target →
      (hrun : ReflTransTraceT (StepStmtE P (EvalCmdE P))
        (.stmt (.loop g m inv sourceBody sourceMd) source)
        sourceTrace (.terminal finalEnv)) →
      hrun.len ≤ n →
      ∃ targetEnv targetTrace,
        StepStmtStarE P (EvalCmdE P)
          (.stmt (.loop g m inv targetBody targetMd) target)
          targetTrace (.terminal targetEnv) ∧
        R finalEnv targetEnv ∧
        TraceExtendsEnv (fun _ : P.Ident => True) sourceTrace targetTrace := by
  intro n
  induction n with
  | zero =>
      intro source target finalEnv sourceTrace hrel hrun hlen
      cases hrun with
      | step => simp [ReflTransTraceT.len] at hlen
  | succ n ih =>
      intro source target finalEnv sourceTrace hrel hrun hlen
      match hrun with
      | .step _ emittedV nextCfg restTrace _ hfirst hrest =>
          rcases loop_stepE_inv hfirst with ⟨rfl, rfl, henter⟩ | ⟨rfl, rfl, hexit⟩
          · obtain ⟨projectedSource, bodyTrace, loopTrace, htrace, hblock, hloopList,
                hlenSeq⟩ := seqT_reaches_terminalE hrest
            rcases block_run_decomposeE (reflTransTraceT_to_prop hblock) with
              ⟨inner', hbad, _⟩ | ⟨sourceInner, hsourceBody, hprojected⟩ |
              ⟨exitLabel, sourceInner, hnone, _, _⟩ |
              ⟨exitLabel, sourceInner, _, _, hbad⟩
            · simp at hbad
            · injection hprojected with hprojectedEnv
              subst projectedSource
              obtain ⟨targetInner, targetBodyTrace, htargetBody, hrelInner, htraceBody⟩ :=
                (hbody source target hrel).terminal hsourceBody
              let sourceNext : Env P :=
                { sourceInner with store := projectStore source.store sourceInner.store }
              let targetNext : Env P :=
                { targetInner with store := projectStore target.store targetInner.store }
              have hrelNext : R sourceNext targetNext :=
                hproject source target sourceInner targetInner hrel hrelInner
              obtain ⟨loopSourceEnv, sourceLoopTrace, sourceNilTrace, hloopTrace,
                  hsourceLoop, hsourceNil, hlenList⟩ := stmtsT_cons_terminalE hloopList
              obtain ⟨hnilTrace, hnilCfg⟩ := stmts_nil_runE (EvalCmdE P)
                (reflTransTraceT_to_prop hsourceNil)
              subst hnilTrace
              rcases hnilCfg with hbad | hfinal
              · simp at hbad
              · injection hfinal with hfinalEq
                subst loopSourceEnv
                obtain ⟨targetEnv, targetLoopTrace, htargetLoop, hrelFinal, htraceLoop⟩ :=
                  ih sourceNext targetNext finalEnv sourceLoopTrace hrelNext hsourceLoop
                    (by simp only [ReflTransTraceT.len] at hlen; omega)
                have hfirst := buildLoopIterationTerminalE (g := g) (m := m) (inv := inv)
                  (md := targetMd) (entry := target) (inner := targetInner)
                  (henterTarget source target hrel henter) htargetBody
                have hrestTarget := stmtRun_to_singletonE (EvalCmdE P) htargetLoop
                refine ⟨targetEnv, targetBodyTrace ++ targetLoopTrace,
                  ReflTransTrace.trans _ hfirst hrestTarget, hrelFinal, ?_⟩
                simpa [htrace, hloopTrace] using
                  (TraceExtendsEnv.append htraceBody htraceLoop)
            · exact absurd hnone (by simp)
            · simp at hbad
          · obtain ⟨hcfg, htrace⟩ := stepStmtStarE_from_terminal (reflTransTraceT_to_prop hrest)
            subst htrace
            injection hcfg with henv
            subst henv
            refine ⟨target, [], Imperative.StepStmtStarE.single
              (loopExitStepE (hexitTarget _ target hrel hexit)),
              hrel, .nil⟩

private theorem loopTraceSim_terminal {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {R B : Env P → Env P → Prop}
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {sourceBody targetBody : List (Stmt P (Cmd P))}
    {sourceMd targetMd : MetaData P}
    (henterTarget : ∀ source target, R source target →
      LoopGuardEnter g source → LoopGuardEnter g target)
    (hexitTarget : ∀ source target, R source target →
      LoopGuardExit g source → LoopGuardExit g target)
    (hproject : ∀ sourceParent targetParent sourceInner targetInner,
      R sourceParent targetParent → B sourceInner targetInner →
      R { sourceInner with store := projectStore sourceParent.store sourceInner.store }
        { targetInner with store := projectStore targetParent.store targetInner.store })
    (hbody : ∀ source target, R source target →
      ConfigTraceSim B (.stmts sourceBody source) (.stmts targetBody target))
    {source target finalEnv : Env P} {sourceTrace : Trace P}
    (hrel : R source target)
    (hrun : StepStmtStarE P (EvalCmdE P)
      (.stmt (.loop g m inv sourceBody sourceMd) source)
      sourceTrace (.terminal finalEnv)) :
    ∃ targetEnv targetTrace,
      StepStmtStarE P (EvalCmdE P)
        (.stmt (.loop g m inv targetBody targetMd) target)
        targetTrace (.terminal targetEnv) ∧
      R finalEnv targetEnv ∧
      TraceExtendsEnv (fun _ : P.Ident => True) sourceTrace targetTrace :=
  loopTraceSim_terminal_fuel henterTarget hexitTarget hproject hbody
    (reflTransTrace_to_T hrun).len source target finalEnv sourceTrace hrel
    (reflTransTrace_to_T hrun) (Nat.le_refl _)

private theorem loopTraceSim_exiting_fuel {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {R B : Env P → Env P → Prop}
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {sourceBody targetBody : List (Stmt P (Cmd P))}
    {sourceMd targetMd : MetaData P}
    (henterTarget : ∀ source target, R source target →
      LoopGuardEnter g source → LoopGuardEnter g target)
    (hproject : ∀ sourceParent targetParent sourceInner targetInner,
      R sourceParent targetParent → B sourceInner targetInner →
      R { sourceInner with store := projectStore sourceParent.store sourceInner.store }
        { targetInner with store := projectStore targetParent.store targetInner.store })
    (hbody : ∀ source target, R source target →
      ConfigTraceSim B (.stmts sourceBody source) (.stmts targetBody target)) :
    ∀ n source target finalEnv label sourceTrace,
      R source target →
      (hrun : ReflTransTraceT (StepStmtE P (EvalCmdE P))
        (.stmt (.loop g m inv sourceBody sourceMd) source)
        sourceTrace (.exiting label finalEnv)) →
      hrun.len ≤ n →
      ∃ targetEnv targetTrace,
        StepStmtStarE P (EvalCmdE P)
          (.stmt (.loop g m inv targetBody targetMd) target)
          targetTrace (.exiting label targetEnv) ∧
        R finalEnv targetEnv ∧
        TraceExtendsEnv (fun _ : P.Ident => True) sourceTrace targetTrace := by
  intro n
  induction n with
  | zero =>
      intro source target finalEnv label sourceTrace hrel hrun hlen
      cases hrun with
      | step => simp [ReflTransTraceT.len] at hlen
  | succ n ih =>
      intro source target finalEnv label sourceTrace hrel hrun hlen
      match hrun with
      | .step _ emittedV nextCfg restTrace _ hfirst hrest =>
          rcases loop_stepE_inv hfirst with ⟨rfl, rfl, henter⟩ | ⟨rfl, rfl, hexit⟩
          · rcases seqT_reaches_exitingE hrest with ⟨hblock, hlenBlock⟩ |
                    ⟨projectedSource, bodyTrace, loopTrace, htrace, hblock, hloopList,
                      hlenSeq⟩
            · rcases block_run_decomposeE (reflTransTraceT_to_prop hblock) with
                      ⟨inner', hbad, _⟩ | ⟨sourceInner, _, hbad⟩ |
                      ⟨exitLabel, sourceInner, hnone, _, _⟩ |
                      ⟨exitLabel, sourceInner, hne, hsourceBody, hfinal⟩
              · simp at hbad
              · simp at hbad
              · exact absurd hnone (by simp)
              · injection hfinal with hlabel henv
                subst hlabel
                subst henv
                obtain ⟨targetInner, targetBodyTrace, htargetBody, hrelInner, htraceBody⟩ :=
                        (hbody _ _ hrel).exiting hsourceBody
                refine ⟨{ targetInner with store := projectStore target.store targetInner.store },
                        targetBodyTrace,
                        buildLoopIterationExitE (g := g) (m := m) (inv := inv) (md := targetMd)
                          (henterTarget _ target hrel henter) htargetBody,
                        hproject _ _ _ _ hrel hrelInner, ?_⟩
                simpa using htraceBody
            · rcases block_run_decomposeE (reflTransTraceT_to_prop hblock) with
                      ⟨inner', hbad, _⟩ | ⟨sourceInner, hsourceBody, hprojected⟩ |
                      ⟨exitLabel, sourceInner, hnone, _, _⟩ |
                      ⟨exitLabel, sourceInner, _, _, hbad⟩
              · simp at hbad
              · injection hprojected with hprojectedEnv
                subst projectedSource
                obtain ⟨targetInner, targetBodyTrace, htargetBody, hrelInner, htraceBody⟩ :=
                        (hbody _ _ hrel).terminal hsourceBody
                let sourceNext : Env P :=
                        { sourceInner with store := projectStore source.store sourceInner.store }
                let targetNext : Env P :=
                        { targetInner with store := projectStore target.store targetInner.store }
                have hrelNext : R sourceNext targetNext :=
                        hproject _ _ _ _ hrel hrelInner
                rcases stmtsT_cons_exitingE hloopList with ⟨hsourceLoop, hlenLoop⟩ |
                        ⟨middleEnv, headTrace, tailTrace, htailTrace, hsourceLoop, hnil,
                          hlenLoop⟩
                · obtain ⟨targetEnv, targetLoopTrace, htargetLoop, hrelFinal, htraceLoop⟩ :=
                          ih sourceNext targetNext finalEnv label loopTrace hrelNext hsourceLoop
                            (by simp only [ReflTransTraceT.len] at hlen; omega)
                  have hfirst := buildLoopIterationTerminalE (g := g) (m := m) (inv := inv)
                          (md := targetMd) (entry := target) (inner := targetInner)
                          (henterTarget _ target hrel henter) htargetBody
                  have htargetTail : StepStmtStarE P (EvalCmdE P)
                            (.stmts [.loop g m inv targetBody targetMd] targetNext)
                            targetLoopTrace (.exiting label targetEnv) := by
                          have hfull := ReflTransTrace.trans _
                            (ReflTransTrace.step _ _ _ _ _ .step_stmts_cons
                              (seq_inner_starE (EvalCmdE P) htargetLoop))
                            (Imperative.StepStmtStarE.single
                              (c := .seq (.exiting label targetEnv) []) .step_seq_exit)
                          simpa using hfull
                  refine ⟨targetEnv, targetBodyTrace ++ targetLoopTrace,
                          ReflTransTrace.trans _ hfirst htargetTail, hrelFinal, ?_⟩
                  simpa [htrace] using TraceExtendsEnv.append htraceBody htraceLoop
                · obtain ⟨_, hnilCfg⟩ := stmts_nil_runE (EvalCmdE P)
                          (reflTransTraceT_to_prop hnil)
                  rcases hnilCfg with hbad | hbad <;> simp at hbad
              · exact absurd hnone (by simp)
              · simp at hbad
          · have hcontra : False := by
                    obtain ⟨hcfg, _⟩ := stepStmtStarE_from_terminal (reflTransTraceT_to_prop hrest)
                    simp at hcfg
            exact hcontra.elim

private theorem loopTraceSim_exiting {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {R B : Env P → Env P → Prop}
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {sourceBody targetBody : List (Stmt P (Cmd P))}
    {sourceMd targetMd : MetaData P}
    (henterTarget : ∀ source target, R source target →
      LoopGuardEnter g source → LoopGuardEnter g target)
    (hproject : ∀ sourceParent targetParent sourceInner targetInner,
      R sourceParent targetParent → B sourceInner targetInner →
      R { sourceInner with store := projectStore sourceParent.store sourceInner.store }
        { targetInner with store := projectStore targetParent.store targetInner.store })
    (hbody : ∀ source target, R source target →
      ConfigTraceSim B (.stmts sourceBody source) (.stmts targetBody target))
    {source target finalEnv : Env P} {label : String} {sourceTrace : Trace P}
    (hrel : R source target)
    (hrun : StepStmtStarE P (EvalCmdE P)
      (.stmt (.loop g m inv sourceBody sourceMd) source)
      sourceTrace (.exiting label finalEnv)) :
    ∃ targetEnv targetTrace,
      StepStmtStarE P (EvalCmdE P)
        (.stmt (.loop g m inv targetBody targetMd) target)
        targetTrace (.exiting label targetEnv) ∧
      R finalEnv targetEnv ∧
      TraceExtendsEnv (fun _ : P.Ident => True) sourceTrace targetTrace :=
  loopTraceSim_exiting_fuel henterTarget hproject hbody
    (reflTransTrace_to_T hrun).len source target finalEnv label sourceTrace hrel
    (reflTransTrace_to_T hrun) (Nat.le_refl _)

private theorem seqT_run_decomposeE {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {inner : Config P (Cmd P)} {rest : List (Stmt P (Cmd P))}
    {final : Config P (Cmd P)} {trace : Trace P}
    (hrun : ReflTransTraceT (StepStmtE P (EvalCmdE P))
      (.seq inner rest) trace final) :
    (∃ inner', final = .seq inner' rest ∧
      ∃ hinner : ReflTransTraceT (StepStmtE P (EvalCmdE P)) inner trace inner',
        hinner.len ≤ hrun.len) ∨
    (∃ middleEnv headTrace tailTrace,
      trace = headTrace ++ tailTrace ∧
      ∃ hhead : ReflTransTraceT (StepStmtE P (EvalCmdE P))
          inner headTrace (.terminal middleEnv),
      ∃ htail : ReflTransTraceT (StepStmtE P (EvalCmdE P))
          (.stmts rest middleEnv) tailTrace final,
      hhead.len < hrun.len ∧ htail.len < hrun.len) ∨
    (∃ exitLabel exitEnv, final = .exiting exitLabel exitEnv ∧
      ∃ hexit : ReflTransTraceT (StepStmtE P (EvalCmdE P))
          inner trace (.exiting exitLabel exitEnv),
        hexit.len < hrun.len) := by
  match hrun with
  | .refl _ => exact .inl ⟨inner, rfl, .refl _, Nat.le_refl _⟩
  | .step _ emitted _ restTrace _ (.step_seq_inner hstep) htail =>
      rcases seqT_run_decomposeE htail with
        ⟨inner', hfinal, hinner, hlen⟩ |
        ⟨middleEnv, headTrace, tailTrace, htrace, hhead, hrest, hlen⟩ |
        ⟨exitLabel, exitEnv, hfinal, hexit, hlen⟩
      · exact .inl ⟨inner', hfinal, .step _ _ _ _ _ hstep hinner,
          by simp only [ReflTransTraceT.len]; omega⟩
      · exact .inr (.inl ⟨middleEnv, emitted ++ headTrace, tailTrace,
          by rw [htrace]; simp [List.append_assoc],
          .step _ _ _ _ _ hstep hhead, hrest,
          ⟨by simp only [ReflTransTraceT.len]; omega,
           by simp only [ReflTransTraceT.len]; omega⟩⟩)
      · exact .inr (.inr ⟨exitLabel, exitEnv, hfinal,
          .step _ _ _ _ _ hstep hexit,
          by simp only [ReflTransTraceT.len]; omega⟩)
  | .step _ _ _ restTrace _ .step_seq_done htail =>
      exact .inr (.inl ⟨_, [], restTrace, by simp, .refl _, htail,
        ⟨by simpa [ReflTransTraceT.len, Nat.add_comm] using Nat.zero_lt_succ htail.len,
         by simp [ReflTransTraceT.len]⟩⟩)
  | .step _ _ _ _ _ .step_seq_exit htail =>
      match htail with
      | .refl _ => exact .inr (.inr ⟨_, _, rfl, .refl _, by simp [ReflTransTraceT.len]⟩)
      | .step _ _ _ _ _ hstep _ => exact (Imperative.StepStmtE.exiting_false hstep).elim
termination_by hrun.len
decreasing_by all_goals simp only [ReflTransTraceT.len]; omega

private theorem loopTraceSim_prefix_fuel {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {R B : Env P → Env P → Prop}
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {sourceBody targetBody : List (Stmt P (Cmd P))}
    {sourceMd targetMd : MetaData P}
    (henterTarget : ∀ source target, R source target →
      LoopGuardEnter g source → LoopGuardEnter g target)
    (hexitTarget : ∀ source target, R source target →
      LoopGuardExit g source → LoopGuardExit g target)
    (hproject : ∀ sourceParent targetParent sourceInner targetInner,
      R sourceParent targetParent → B sourceInner targetInner →
      R { sourceInner with store := projectStore sourceParent.store sourceInner.store }
        { targetInner with store := projectStore targetParent.store targetInner.store })
    (hbody : ∀ source target, R source target →
      ConfigTraceSim B (.stmts sourceBody source) (.stmts targetBody target)) :
    ∀ n source target final sourceTrace,
      R source target →
      (hrun : ReflTransTraceT (StepStmtE P (EvalCmdE P))
        (.stmt (.loop g m inv sourceBody sourceMd) source)
        sourceTrace final) →
      hrun.len ≤ n →
      ∃ targetFinal targetTrace,
        StepStmtStarE P (EvalCmdE P)
          (.stmt (.loop g m inv targetBody targetMd) target)
          targetTrace targetFinal ∧
        TraceExtendsEnv (fun _ : P.Ident => True) sourceTrace targetTrace := by
  intro n
  induction n with
  | zero =>
      intro source target final sourceTrace hrel hrun hlen
      match hrun with
      | .refl _ => exact ⟨_, [], .refl _, .nil⟩
      | .step _ _ _ _ _ _ _ => simp [ReflTransTraceT.len] at hlen
  | succ n ih =>
      intro source target final sourceTrace hrel hrun hlen
      match hrun with
      | .refl _ => exact ⟨_, [], .refl _, .nil⟩
      | .step _ emittedV nextCfg restTrace _ hfirst hrest =>
          rcases loop_stepE_inv hfirst with ⟨rfl, rfl, henter⟩ | ⟨rfl, rfl, hexit⟩
          · rcases seqT_run_decomposeE hrest with
              ⟨blockFinal, hfinal, hblock, hlenBlock⟩ |
              ⟨projectedSource, bodyTrace, loopTrace, htrace, hblock,
                hloopList, hlenSeq⟩ |
              ⟨exitLabel, exitEnv, hfinal, hblock, hlenBlock⟩
            · subst hfinal
              rcases block_run_decomposeE (reflTransTraceT_to_prop hblock) with
                ⟨sourceInner, rfl, hsourceBody⟩ |
                ⟨sourceInner, hsourceBody, rfl⟩ |
                ⟨exitLabel, sourceInner, hnone, _, _⟩ |
                ⟨exitLabel, sourceInner, hne, hsourceBody, rfl⟩
              · obtain ⟨targetInner, targetBodyTrace, htargetBody, htraceBody⟩ :=
                  (hbody _ _ hrel).simulate hsourceBody
                exact ⟨_, targetBodyTrace,
                  buildLoopIterationPrefixE (g := g) (m := m) (inv := inv) (md := targetMd)
                    (henterTarget _ target hrel henter) htargetBody,
                  by simpa using htraceBody⟩
              · obtain ⟨targetInner, targetBodyTrace, htargetBody, _, htraceBody⟩ :=
                  (hbody _ _ hrel).terminal hsourceBody
                exact ⟨_, targetBodyTrace,
                  buildLoopIterationPrefixE (g := g) (m := m) (inv := inv) (md := targetMd)
                    (henterTarget _ target hrel henter) htargetBody,
                  by simpa using htraceBody⟩
              · exact absurd hnone (by simp)
              · obtain ⟨targetInner, targetBodyTrace, htargetBody, _, htraceBody⟩ :=
                  (hbody _ _ hrel).exiting hsourceBody
                exact ⟨_, targetBodyTrace,
                  buildLoopIterationPrefixE (g := g) (m := m) (inv := inv) (md := targetMd)
                    (henterTarget _ target hrel henter) htargetBody,
                  by simpa using htraceBody⟩
            · rcases block_run_decomposeE (reflTransTraceT_to_prop hblock) with
                ⟨sourceInner, hbad, _⟩ |
                ⟨sourceInner, hsourceBody, hprojected⟩ |
                ⟨exitLabel, sourceInner, hnone, _, _⟩ |
                ⟨exitLabel, sourceInner, _, _, hbad⟩
              · simp at hbad
              · injection hprojected with hprojectedEnv
                subst projectedSource
                obtain ⟨targetInner, targetBodyTrace, htargetBody, hrelInner,
                    htraceBody⟩ := (hbody _ _ hrel).terminal hsourceBody
                let sourceNext : Env P :=
                  { sourceInner with store := projectStore source.store sourceInner.store }
                let targetNext : Env P :=
                  { targetInner with store := projectStore target.store targetInner.store }
                have hrelNext : R sourceNext targetNext :=
                  hproject _ _ _ _ hrel hrelInner
                have hfirstTarget := buildLoopIterationTerminalE (g := g) (m := m) (inv := inv)
                  (md := targetMd) (entry := target) (inner := targetInner)
                  (henterTarget _ target hrel henter) htargetBody
                match hloopList with
                | .refl _ =>
                    refine ⟨_, targetBodyTrace, hfirstTarget, ?_⟩
                    simpa [htrace] using htraceBody
                | .step _ _ _ tailTrace _ hlistFirst hlistRest =>
                    cases hlistFirst with
                    | step_stmts_cons =>
                        rcases seqT_run_decomposeE hlistRest with
                          ⟨loopFinal, rfl, hsourceLoop, hlenLoop⟩ |
                          ⟨middleEnv, headTrace, nilTrace, htailTrace,
                            hsourceLoop, hnil, hlenLoop⟩ |
                          ⟨loopExitLabel, loopExitEnv, rfl, hsourceLoop,
                            hlenLoop⟩
                        · obtain ⟨targetLoopFinal, targetLoopTrace,
                              htargetLoop, htraceLoop⟩ :=
                            ih sourceNext targetNext loopFinal tailTrace hrelNext
                              hsourceLoop
                              (by
                                have hsourceLoopLe : hsourceLoop.len ≤ hlistRest.len := hlenLoop
                                simp only [ReflTransTraceT.len] at hlen hlenSeq
                                omega)
                          have htargetTail : StepStmtStarE P (EvalCmdE P)
                              (.stmts [.loop g m inv targetBody targetMd]
                                targetNext)
                              targetLoopTrace (.seq targetLoopFinal []) :=
                            ReflTransTrace.step _ _ _ _ _
                              .step_stmts_cons
                              (seq_inner_starE (EvalCmdE P) htargetLoop)
                          refine ⟨_, targetBodyTrace ++ targetLoopTrace,
                            ReflTransTrace.trans _ hfirstTarget htargetTail, ?_⟩
                          simpa [htrace] using
                            TraceExtendsEnv.append htraceBody htraceLoop
                        · obtain ⟨nilTraceEq, _⟩ := stmts_nil_runE (EvalCmdE P)
                            (reflTransTraceT_to_prop hnil)
                          subst nilTraceEq
                          obtain ⟨targetLoopEnv, targetLoopTrace, htargetLoop,
                              _, htraceLoop⟩ :=
                            loopTraceSim_terminal henterTarget hexitTarget hproject hbody hrelNext
                              (reflTransTraceT_to_prop hsourceLoop)
                          have htargetTail := stmtRun_to_singletonE (EvalCmdE P)
                            htargetLoop
                          refine ⟨_, targetBodyTrace ++ targetLoopTrace,
                            ReflTransTrace.trans _ hfirstTarget htargetTail, ?_⟩
                          simpa [htrace, htailTrace] using
                            TraceExtendsEnv.append htraceBody htraceLoop
                        · obtain ⟨targetLoopEnv, targetLoopTrace, htargetLoop,
                              _, htraceLoop⟩ :=
                            loopTraceSim_exiting henterTarget hproject hbody hrelNext
                              (reflTransTraceT_to_prop hsourceLoop)
                          have htargetTail : StepStmtStarE P (EvalCmdE P)
                              (.stmts [.loop g m inv targetBody targetMd]
                                targetNext)
                              targetLoopTrace (.exiting loopExitLabel targetLoopEnv) := by
                            have hfull := ReflTransTrace.trans _
                              (ReflTransTrace.step _ _ _ _ _
                                .step_stmts_cons
                                (seq_inner_starE (EvalCmdE P) htargetLoop))
                              (Imperative.StepStmtStarE.single
                                (c := .seq (.exiting loopExitLabel targetLoopEnv) [])
                                .step_seq_exit)
                            simpa using hfull
                          refine ⟨_, targetBodyTrace ++ targetLoopTrace,
                            ReflTransTrace.trans _ hfirstTarget htargetTail, ?_⟩
                          simpa [htrace] using
                            TraceExtendsEnv.append htraceBody htraceLoop
              · exact absurd hnone (by simp)
              · simp at hbad
            · subst hfinal
              rcases block_run_decomposeE (reflTransTraceT_to_prop hblock) with
                ⟨sourceInner, hbad, _⟩ |
                ⟨sourceInner, _, hbad⟩ |
                ⟨innerLabel, sourceInner, hnone, _, _⟩ |
                ⟨innerLabel, sourceInner, hne, hsourceBody, hfinal⟩
              · simp at hbad
              · simp at hbad
              · exact absurd hnone (by simp)
              · injection hfinal with hlabel henv
                subst hlabel
                subst henv
                obtain ⟨targetInner, targetBodyTrace, htargetBody, _, htraceBody⟩ :=
                  (hbody _ _ hrel).exiting hsourceBody
                exact ⟨_, targetBodyTrace,
                  buildLoopIterationExitE (g := g) (m := m) (inv := inv) (md := targetMd)
                    (henterTarget _ target hrel henter) htargetBody,
                  by simpa using htraceBody⟩
          · obtain ⟨hcfg, htrace⟩ := stepStmtStarE_from_terminal
              (reflTransTraceT_to_prop hrest)
            subst htrace
            subst hcfg
            exact ⟨_, [], Imperative.StepStmtStarE.single
              (loopExitStepE (hexitTarget _ target hrel hexit)), .nil⟩

private theorem loopTraceSim_prefix {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {R B : Env P → Env P → Prop}
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {sourceBody targetBody : List (Stmt P (Cmd P))}
    {sourceMd targetMd : MetaData P}
    (henterTarget : ∀ source target, R source target →
      LoopGuardEnter g source → LoopGuardEnter g target)
    (hexitTarget : ∀ source target, R source target →
      LoopGuardExit g source → LoopGuardExit g target)
    (hproject : ∀ sourceParent targetParent sourceInner targetInner,
      R sourceParent targetParent → B sourceInner targetInner →
      R { sourceInner with store := projectStore sourceParent.store sourceInner.store }
        { targetInner with store := projectStore targetParent.store targetInner.store })
    (hbody : ∀ source target, R source target →
      ConfigTraceSim B (.stmts sourceBody source) (.stmts targetBody target))
    {source target : Env P} {final : Config P (Cmd P)} {sourceTrace : Trace P}
    (hrel : R source target)
    (hrun : StepStmtStarE P (EvalCmdE P)
      (.stmt (.loop g m inv sourceBody sourceMd) source)
      sourceTrace final) :
    ∃ targetFinal targetTrace,
      StepStmtStarE P (EvalCmdE P)
        (.stmt (.loop g m inv targetBody targetMd) target)
        targetTrace targetFinal ∧
      TraceExtendsEnv (fun _ : P.Ident => True) sourceTrace targetTrace :=
  loopTraceSim_prefix_fuel henterTarget hexitTarget hproject hbody
    (reflTransTrace_to_T hrun).len source target final sourceTrace hrel
    (reflTransTrace_to_T hrun) (Nat.le_refl _)

private theorem loopTraceSim {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {R B : Env P → Env P → Prop}
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {sourceBody targetBody : List (Stmt P (Cmd P))}
    {sourceMd targetMd : MetaData P}
    (henterTarget : ∀ source target, R source target →
      LoopGuardEnter g source → LoopGuardEnter g target)
    (hexitTarget : ∀ source target, R source target →
      LoopGuardExit g source → LoopGuardExit g target)
    (hproject : ∀ sourceParent targetParent sourceInner targetInner,
      R sourceParent targetParent → B sourceInner targetInner →
      R { sourceInner with store := projectStore sourceParent.store sourceInner.store }
        { targetInner with store := projectStore targetParent.store targetInner.store })
    (hbody : ∀ source target, R source target →
      ConfigTraceSim B (.stmts sourceBody source) (.stmts targetBody target))
    {source target : Env P} (hrel : R source target) :
    ConfigTraceSim R
      (.stmt (.loop g m inv sourceBody sourceMd) source)
      (.stmt (.loop g m inv targetBody targetMd) target) :=
  ⟨loopTraceSim_prefix henterTarget hexitTarget hproject hbody hrel,
   loopTraceSim_terminal henterTarget hexitTarget hproject hbody hrel,
   loopTraceSim_exiting henterTarget hproject hbody hrel⟩

private theorem preludeThenTraceSim {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {R : Env P → Env P → Prop}
    {source : Config P (Cmd P)} {targetEntry targetPre : Env P}
    {prelude : List (Stmt P (Cmd P))} {targetStmt : Stmt P (Cmd P)}
    {preludeTrace : Trace P}
    (hprelude : StepStmtStarE P (EvalCmdE P)
      (.stmts prelude targetEntry) preludeTrace (.terminal targetPre))
    (hpreludeTrace : TraceExtendsEnv (fun _ : P.Ident => True) [] preludeTrace)
    (hloop : ConfigTraceSim R source (.stmt targetStmt targetPre)) :
    ConfigTraceSim R source (.stmts (prelude ++ [targetStmt]) targetEntry) := by
  have hstart : StepStmtStarE P (EvalCmdE P)
      (.stmts (prelude ++ [targetStmt]) targetEntry) preludeTrace
      (.stmts [targetStmt] targetPre) :=
    stmts_prefix_terminal_appendE prelude [targetStmt] targetEntry targetPre hprelude
  have hsingle := hloop.targetSingleton
  refine ⟨?_, ?_, ?_⟩
  · intro source' sourceTrace hrun
    obtain ⟨target', targetTrace, htarget, htrace⟩ := hsingle.simulate hrun
    exact ⟨target', preludeTrace ++ targetTrace,
      ReflTransTrace.trans _ hstart htarget,
      by simpa using TraceExtendsEnv.append hpreludeTrace htrace⟩
  · intro sourceEnv sourceTrace hrun
    obtain ⟨targetEnv, targetTrace, htarget, hrel, htrace⟩ := hsingle.terminal hrun
    exact ⟨targetEnv, preludeTrace ++ targetTrace,
      ReflTransTrace.trans _ hstart htarget, hrel,
      by simpa using TraceExtendsEnv.append hpreludeTrace htrace⟩
  · intro label sourceEnv sourceTrace hrun
    obtain ⟨targetEnv, targetTrace, htarget, hrel, htrace⟩ := hsingle.exiting hrun
    exact ⟨targetEnv, preludeTrace ++ targetTrace,
      ReflTransTrace.trans _ hstart htarget, hrel,
      by simpa using TraceExtendsEnv.append hpreludeTrace htrace⟩

private theorem cmdHoistTraceSim {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [HasInt P]
    [DecidableEq P.Ident] [LawfulHasVal P]
    (command : Cmd P) :
    StmtHoistTraceSim (.cmd command) [.cmd command] := by
  intro sourceEnv targetEnv henv hwfb hwfv hmono hwfc hwfvar hsourceUndef
    htargetUndef hinhab
  have replay : ∀ {sourceStore : SemanticStore P} {sourceTrace : Trace P},
      EvalCmdE P sourceEnv.factory sourceEnv.store command sourceStore sourceTrace →
      ∃ targetStore targetTrace,
        EvalCmdE P targetEnv.factory targetEnv.store command targetStore targetTrace ∧
        HoistEnvRel sourceEnv.factory
          { sourceEnv with store := sourceStore }
          { targetEnv with store := targetStore } ∧
        TraceExtendsEnv (fun _ : P.Ident => True) sourceTrace targetTrace := by
    intro sourceStore sourceTrace heval
    obtain ⟨targetStore, targetTrace, htarget, hagree, _, htrace⟩ :=
      evalCmdE_replay_agreement_typed_lockstep
        (Dτ := fun _ => HasBool.boolTy) (D := [])
        (henv.targetFactory.trans henv.sourceFactory.symm) henv.agreement
        (by intro y hy; exact absurd hy List.not_mem_nil) heval
        (by simpa [henv.sourceFactory] using hmono) (by
          intro y hy
          exact htargetUndef y (by
            cases command <;> simp_all [Stmt.initVars, Cmd.definedVars,
              HasVarsImp.definedVars]))
    exact ⟨targetStore, targetTrace, htarget,
      ⟨hagree, henv.sourceFactory, henv.targetFactory⟩, htrace⟩
  refine ⟨?_, ?_, ?_⟩
  · intro source' sourceTrace hrun
    match hrun with
    | .refl _ => exact ⟨_, [], .refl _, .nil⟩
    | .step _ emitted _ restTrace _ hstep hrest =>
        obtain ⟨sourceStore, heval, rfl⟩ := Imperative.StepStmtE.cmd_cases hstep
        obtain ⟨hcfg, htailTrace⟩ := stepStmtStarE_from_terminal hrest
        subst htailTrace
        subst hcfg
        obtain ⟨targetStore, targetTrace, htarget, _, htrace⟩ := replay heval
        exact ⟨_, targetTrace, stmtRun_to_singletonE (EvalCmdE P)
          (Imperative.StepStmtStarE.single (.step_cmd htarget)), by simpa using htrace⟩
  · intro sourceOut sourceTrace hrun
    match hrun with
    | .step _ emitted _ restTrace _ hstep hrest =>
        obtain ⟨sourceStore, heval, hcfg⟩ := Imperative.StepStmtE.cmd_cases hstep
        subst hcfg
        obtain ⟨hfinal, htailTrace⟩ := stepStmtStarE_from_terminal hrest
        subst htailTrace
        injection hfinal with henvOut
        subst henvOut
        obtain ⟨targetStore, targetTrace, htarget, hrel, htrace⟩ := replay heval
        exact ⟨_, targetTrace, stmtRun_to_singletonE (EvalCmdE P)
          (Imperative.StepStmtStarE.single (.step_cmd htarget)), hrel, by simpa using htrace⟩
  · intro label sourceOut sourceTrace hrun
    match hrun with
    | .step _ _ _ _ _ hstep hrest =>
        obtain ⟨_, _, hcfg⟩ := Imperative.StepStmtE.cmd_cases hstep
        subst hcfg
        have hcontra : False := by
          obtain ⟨hcfg', _⟩ := stepStmtStarE_from_terminal hrest
          simp at hcfg'
        exact hcontra.elim

private theorem exitHoistTraceSim {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [HasInt P]
    [DecidableEq P.Ident]
    (stmtLabel : String) (md : MetaData P) :
    StmtHoistTraceSim (.exit stmtLabel md) [.exit stmtLabel md] := by
  intro sourceEnv targetEnv henv hwfb hwfv hmono hwfc hwfvar hsourceUndef
    htargetUndef hinhab
  refine ⟨?_, ?_, ?_⟩
  · intro source' sourceTrace hrun
    match hrun with
    | .refl _ => exact ⟨_, [], .refl _, .nil⟩
    | .step _ _ _ restTrace _ hstep hrest =>
        cases hstep with
        | step_exit =>
            obtain ⟨hcfg, htrace⟩ := stepStmtStarE_from_exiting hrest
            subst htrace
            subst hcfg
            exact ⟨_, [], ReflTransTrace.step _ _ _ _ _
              .step_stmts_cons
              (ReflTransTrace.step _ _ _ _ _
                (.step_seq_inner .step_exit)
                (Imperative.StepStmtStarE.single .step_seq_exit)), .nil⟩
  · intro sourceOut sourceTrace hrun
    match hrun with
    | .step _ _ _ _ _ hstep hrest =>
        cases hstep with
        | step_exit =>
            have hcontra : False := by
              obtain ⟨hcfg, _⟩ := stepStmtStarE_from_exiting hrest
              simp at hcfg
            exact hcontra.elim
  · intro exitLabel sourceOut sourceTrace hrun
    match hrun with
    | .step _ _ _ restTrace _ hstep hrest =>
        cases hstep with
        | step_exit =>
            obtain ⟨hcfg, htrace⟩ := stepStmtStarE_from_exiting hrest
            subst htrace
            injection hcfg with hlabel henvOut
            subst hlabel
            subst henvOut
            have hstmt : StepStmtStarE P (EvalCmdE P)
                (.stmt (.exit exitLabel md) targetEnv) []
                (.exiting exitLabel targetEnv) :=
              Imperative.StepStmtStarE.single
                (c := .stmt (.exit exitLabel md) targetEnv) .step_exit
            have hseq : StepStmtStarE P (EvalCmdE P)
                (.stmts [.exit exitLabel md] targetEnv) []
                (.seq (.exiting exitLabel targetEnv) []) :=
              ReflTransTrace.step _ _ _ _ _ .step_stmts_cons
                (seq_inner_starE (EvalCmdE P) hstmt)
            have htarget : StepStmtStarE P (EvalCmdE P)
                (.stmts [.exit exitLabel md] targetEnv) [] (.exiting exitLabel targetEnv) := by
              have hfull := ReflTransTrace.trans _ hseq
                (Imperative.StepStmtStarE.single
                  (c := .seq (.exiting exitLabel targetEnv) []) .step_seq_exit)
              simpa using hfull
            exact ⟨targetEnv, [], htarget, henv, .nil⟩

private theorem typeDeclHoistTraceSim {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [HasInt P]
    [DecidableEq P.Ident]
    (typeCtor : TypeConstructor) (md : MetaData P) :
    StmtHoistTraceSim (.typeDecl typeCtor md) [.typeDecl typeCtor md] := by
  intro sourceEnv targetEnv henv hwfb hwfv hmono hwfc hwfvar hsourceUndef
    htargetUndef hinhab
  have htarget : StepStmtStarE P (EvalCmdE P)
      (.stmts [.typeDecl typeCtor md] targetEnv) [] (.terminal targetEnv) :=
    stmtRun_to_singletonE (EvalCmdE P)
      (Imperative.StepStmtStarE.single
        (c := .stmt (.typeDecl typeCtor md) targetEnv)
        .step_typeDecl)
  refine ⟨?_, ?_, ?_⟩
  · intro source' sourceTrace hrun
    match hrun with
    | .refl _ => exact ⟨_, [], .refl _, .nil⟩
    | .step _ _ _ restTrace _ hstep hrest =>
        cases hstep with
        | step_typeDecl =>
            obtain ⟨hcfg, htrace⟩ := stepStmtStarE_from_terminal hrest
            subst htrace
            subst hcfg
            exact ⟨_, [], htarget, .nil⟩
  · intro sourceOut sourceTrace hrun
    match hrun with
    | .step _ _ _ restTrace _ hstep hrest =>
        cases hstep with
        | step_typeDecl =>
            obtain ⟨hcfg, htrace⟩ := stepStmtStarE_from_terminal hrest
            subst htrace
            injection hcfg with henvOut
            subst henvOut
            exact ⟨targetEnv, [], htarget, henv, .nil⟩
  · intro label sourceOut sourceTrace hrun
    match hrun with
    | .step _ _ _ _ _ hstep hrest =>
        cases hstep with
        | step_typeDecl =>
            have hcontra : False := by
              obtain ⟨hcfg, _⟩ := stepStmtStarE_from_terminal hrest
              simp at hcfg
            exact hcontra.elim

private theorem blockHoistTraceSim {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [HasInt P]
    [DecidableEq P.Ident]
    {label : String} {sourceBody targetBody : List (Stmt P (Cmd P))} {md : MetaData P}
    (hbody : BlockHoistTraceSim sourceBody targetBody) :
    StmtHoistTraceSim (.block label sourceBody md) [.block label targetBody md] := by
  intro sourceEnv targetEnv henv hwfb hwfv hmono hwfc hwfvar hsourceUndef
    htargetUndef hinhab
  have hbodySim := hbody sourceEnv targetEnv henv hwfb hwfv hmono hwfc hwfvar
    hsourceUndef htargetUndef hinhab
  have hstmt : ConfigTraceSim (HoistEnvRel sourceEnv.factory)
      (.stmt (.block label sourceBody md) sourceEnv)
      (.stmt (.block label targetBody md) targetEnv) := by
    refine ⟨?_, ?_, ?_⟩
    · intro source' sourceTrace hrun
      match hrun with
      | .refl _ => exact ⟨_, [], .refl _, .nil⟩
      | .step _ _ _ restTrace _ hfirst hrest =>
          cases hfirst with
          | step_block =>
              rcases block_run_decomposeE hrest with
                ⟨sourceInner, rfl, hsourceBody⟩ |
                ⟨sourceInner, hsourceBody, rfl⟩ |
                ⟨exitLabel, sourceInner, heq, hsourceBody, rfl⟩ |
                ⟨exitLabel, sourceInner, hne, hsourceBody, rfl⟩
              · obtain ⟨targetInner, targetTrace, htargetBody, htrace⟩ :=
                  hbodySim.simulate hsourceBody
                exact ⟨_, targetTrace,
                  ReflTransTrace.step (.stmt (.block label targetBody md) targetEnv) _ _ _ _ .step_block
                    (block_inner_starE (label := some label) (σ_parent := targetEnv.store) htargetBody), by simpa using htrace⟩
              · obtain ⟨targetInner, targetTrace, htargetBody, _, htrace⟩ :=
                  hbodySim.terminal hsourceBody
                have htarget := ReflTransTrace.step (.stmt (.block label targetBody md) targetEnv) _ _ _ _ .step_block
                  (ReflTransTrace.trans _ (block_inner_starE (label := some label) (σ_parent := targetEnv.store) htargetBody)
                    (Imperative.StepStmtStarE.single .step_block_done))
                exact ⟨_, targetTrace, by simpa using htarget, by simpa using htrace⟩
              · obtain ⟨targetInner, targetTrace, htargetBody, _, htrace⟩ :=
                  hbodySim.exiting hsourceBody
                have htarget := ReflTransTrace.step (.stmt (.block label targetBody md) targetEnv) _ _ _ _ .step_block
                  (ReflTransTrace.trans _ (block_inner_starE (label := some label) (σ_parent := targetEnv.store) htargetBody)
                    (Imperative.StepStmtStarE.single
                      (.step_block_exit_match heq)))
                exact ⟨_, targetTrace, by simpa using htarget, by simpa using htrace⟩
              · obtain ⟨targetInner, targetTrace, htargetBody, _, htrace⟩ :=
                  hbodySim.exiting hsourceBody
                have htarget := ReflTransTrace.step (.stmt (.block label targetBody md) targetEnv) _ _ _ _ .step_block
                  (ReflTransTrace.trans _ (block_inner_starE (label := some label) (σ_parent := targetEnv.store) htargetBody)
                    (Imperative.StepStmtStarE.single
                      (.step_block_exit_mismatch hne)))
                exact ⟨_, targetTrace, by simpa using htarget, by simpa using htrace⟩
    · intro sourceOut sourceTrace hrun
      match hrun with
      | .step _ _ _ restTrace _ hfirst hrest =>
          cases hfirst with
          | step_block =>
              rcases block_run_decomposeE hrest with
                ⟨sourceInner, hbad, _⟩ |
                ⟨sourceInner, hsourceBody, hfinal⟩ |
                ⟨exitLabel, sourceInner, heq, hsourceBody, hfinal⟩ |
                ⟨exitLabel, sourceInner, hne, _, hbad⟩
              · simp at hbad
              · injection hfinal with hsourceOut
                subst hsourceOut
                obtain ⟨targetInner, targetTrace, htargetBody, hrel, htrace⟩ :=
                  hbodySim.terminal hsourceBody
                have htarget := ReflTransTrace.step (.stmt (.block label targetBody md) targetEnv) _ _ _ _ .step_block
                  (ReflTransTrace.trans _ (block_inner_starE (label := some label) (σ_parent := targetEnv.store) htargetBody)
                    (Imperative.StepStmtStarE.single .step_block_done))
                exact ⟨_, targetTrace, by simpa using htarget,
                  HoistEnvRel.project henv.storeRel hrel, by simpa using htrace⟩
              · injection hfinal with hsourceOut
                subst hsourceOut
                obtain ⟨targetInner, targetTrace, htargetBody, hrel, htrace⟩ :=
                  hbodySim.exiting hsourceBody
                have htarget := ReflTransTrace.step (.stmt (.block label targetBody md) targetEnv) _ _ _ _ .step_block
                  (ReflTransTrace.trans _ (block_inner_starE (label := some label) (σ_parent := targetEnv.store) htargetBody)
                    (Imperative.StepStmtStarE.single
                      (.step_block_exit_match heq)))
                exact ⟨_, targetTrace, by simpa using htarget,
                  HoistEnvRel.project henv.storeRel hrel, by simpa using htrace⟩
              · simp at hbad
    · intro exitLabel sourceOut sourceTrace hrun
      match hrun with
      | .step _ _ _ restTrace _ hfirst hrest =>
          cases hfirst with
          | step_block =>
              rcases block_run_decomposeE hrest with
                ⟨sourceInner, hbad, _⟩ |
                ⟨sourceInner, _, hbad⟩ |
                ⟨innerLabel, sourceInner, heq, _, hbad⟩ |
                ⟨innerLabel, sourceInner, hne, hsourceBody, hfinal⟩
              · simp at hbad
              · simp at hbad
              · simp at hbad
              · injection hfinal with hlabel hsourceOut
                subst hlabel
                subst hsourceOut
                obtain ⟨targetInner, targetTrace, htargetBody, hrel, htrace⟩ :=
                  hbodySim.exiting hsourceBody
                have htarget := ReflTransTrace.step (.stmt (.block label targetBody md) targetEnv) _ _ _ _ .step_block
                  (ReflTransTrace.trans _ (block_inner_starE (label := some label) (σ_parent := targetEnv.store) htargetBody)
                    (Imperative.StepStmtStarE.single
                      (.step_block_exit_mismatch hne)))
                exact ⟨_, targetTrace, by simpa using htarget,
                  HoistEnvRel.project henv.storeRel hrel, by simpa using htrace⟩
  exact hstmt.targetSingleton

private theorem blockFrameTraceSim {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {factory : P.Factory} {label : Option String}
    {sourceParent targetParent : SemanticStore P}
    {sourceInner targetInner : Config P (Cmd P)}
    (hparent : HoistStoreRel sourceParent targetParent)
    (hinner : ConfigTraceSim (HoistEnvRel factory) sourceInner targetInner) :
    ConfigTraceSim (HoistEnvRel factory)
      (.block label sourceParent sourceInner)
      (.block label targetParent targetInner) := by
  refine ⟨?_, ?_, ?_⟩
  · intro source' sourceTrace hrun
    rcases block_run_decomposeE hrun with
      ⟨inner', rfl, hsourceInner⟩ |
      ⟨sourceEnv, hsourceInner, rfl⟩ |
      ⟨exitLabel, sourceEnv, heq, hsourceInner, rfl⟩ |
      ⟨exitLabel, sourceEnv, hne, hsourceInner, rfl⟩
    · obtain ⟨targetInner', targetTrace, htargetInner, htrace⟩ :=
        hinner.simulate hsourceInner
      exact ⟨_, targetTrace, block_inner_starE (label := label) (σ_parent := targetParent) htargetInner, htrace⟩
    · obtain ⟨targetEnv, targetTrace, htargetInner, _, htrace⟩ :=
        hinner.terminal hsourceInner
      exact ⟨_, targetTrace, by simpa using (ReflTransTrace.trans _ (block_inner_starE (label := label) (σ_parent := targetParent) htargetInner)
        (Imperative.StepStmtStarE.single .step_block_done)), by simpa using htrace⟩
    · obtain ⟨targetEnv, targetTrace, htargetInner, _, htrace⟩ :=
        hinner.exiting hsourceInner
      exact ⟨_, targetTrace, by simpa using (ReflTransTrace.trans _ (block_inner_starE (label := label) (σ_parent := targetParent) htargetInner)
        (Imperative.StepStmtStarE.single (.step_block_exit_match heq))),
        by simpa using htrace⟩
    · obtain ⟨targetEnv, targetTrace, htargetInner, _, htrace⟩ :=
        hinner.exiting hsourceInner
      exact ⟨_, targetTrace, by simpa using (ReflTransTrace.trans _ (block_inner_starE (label := label) (σ_parent := targetParent) htargetInner)
        (Imperative.StepStmtStarE.single (.step_block_exit_mismatch hne))),
        by simpa using htrace⟩
  · intro sourceEnv sourceTrace hrun
    rcases block_run_decomposeE hrun with
      ⟨inner', hbad, _⟩ |
      ⟨sourceInnerEnv, hsourceInner, hfinal⟩ |
      ⟨exitLabel, sourceInnerEnv, heq, hsourceInner, hfinal⟩ |
      ⟨exitLabel, sourceInnerEnv, hne, _, hbad⟩
    · simp at hbad
    · injection hfinal with hsourceEnv
      subst hsourceEnv
      obtain ⟨targetEnv, targetTrace, htargetInner, hrel, htrace⟩ :=
        hinner.terminal hsourceInner
      exact ⟨_, targetTrace, by simpa using (ReflTransTrace.trans _ (block_inner_starE (label := label) (σ_parent := targetParent) htargetInner)
        (Imperative.StepStmtStarE.single .step_block_done)),
        HoistEnvRel.project hparent hrel, htrace⟩
    · injection hfinal with hsourceEnv
      subst hsourceEnv
      obtain ⟨targetEnv, targetTrace, htargetInner, hrel, htrace⟩ :=
        hinner.exiting hsourceInner
      exact ⟨_, targetTrace, by simpa using (ReflTransTrace.trans _ (block_inner_starE (label := label) (σ_parent := targetParent) htargetInner)
        (Imperative.StepStmtStarE.single (.step_block_exit_match heq))),
        HoistEnvRel.project hparent hrel, htrace⟩
    · simp at hbad
  · intro exitLabel sourceEnv sourceTrace hrun
    rcases block_run_decomposeE hrun with
      ⟨inner', hbad, _⟩ |
      ⟨sourceInnerEnv, _, hbad⟩ |
      ⟨innerLabel, sourceInnerEnv, heq, _, hbad⟩ |
      ⟨innerLabel, sourceInnerEnv, hne, hsourceInner, hfinal⟩
    · simp at hbad
    · simp at hbad
    · simp at hbad
    · injection hfinal with hlabel hsourceEnv
      subst hlabel
      subst hsourceEnv
      obtain ⟨targetEnv, targetTrace, htargetInner, hrel, htrace⟩ :=
        hinner.exiting hsourceInner
      exact ⟨_, targetTrace, by simpa using (ReflTransTrace.trans _ (block_inner_starE (label := label) (σ_parent := targetParent) htargetInner)
        (Imperative.StepStmtStarE.single (.step_block_exit_mismatch hne))),
        HoistEnvRel.project hparent hrel, htrace⟩

private theorem iteHoistTraceSim {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [HasInt P]
    [DecidableEq P.Ident]
    {g : ExprOrNondet P} {sourceThen targetThen sourceElse targetElse : List (Stmt P (Cmd P))}
    {md : MetaData P}
    (hthen : BlockHoistTraceSim sourceThen targetThen)
    (helse : BlockHoistTraceSim sourceElse targetElse) :
    StmtHoistTraceSim (.ite g sourceThen sourceElse md)
      [.ite g targetThen targetElse md] := by
  intro sourceEnv targetEnv henv hwfb hwfv hmono hwfc hwfvar hsourceUndef
    htargetUndef hinhab
  have hsourceThen : ∀ y ∈ Block.initVars sourceThen, sourceEnv.store y = none := by
    intro y hy
    exact hsourceUndef y (by simpa [Stmt.initVars] using List.mem_append_left _ hy)
  have hsourceElse : ∀ y ∈ Block.initVars sourceElse, sourceEnv.store y = none := by
    intro y hy
    exact hsourceUndef y (by simpa [Stmt.initVars] using List.mem_append_right _ hy)
  have htargetThen : ∀ y ∈ Block.initVars sourceThen, targetEnv.store y = none := by
    intro y hy
    exact htargetUndef y (by simpa [Stmt.initVars] using List.mem_append_left _ hy)
  have htargetElse : ∀ y ∈ Block.initVars sourceElse, targetEnv.store y = none := by
    intro y hy
    exact htargetUndef y (by simpa [Stmt.initVars] using List.mem_append_right _ hy)
  have hinhabThen : Block.InitTypesInhabited sourceEnv.factory sourceThen := by
    intro ty hty
    exact hinhab ty (by simpa [Stmt.initTypes] using List.mem_append_left _ hty)
  have hinhabElse : Block.InitTypesInhabited sourceEnv.factory sourceElse := by
    intro ty hty
    exact hinhab ty (by simpa [Stmt.initTypes] using List.mem_append_right _ hty)
  have hEnterT : LoopGuardEnter g sourceEnv → LoopGuardEnter g targetEnv := by
    cases g with
    | det guard => intro h; exact henv.evalBool HasBool.ttVal hmono h
    | nondet => intro _; exact trivial
  have hExitT : LoopGuardExit g sourceEnv → LoopGuardExit g targetEnv := by
    cases g with
    | det guard => intro h; exact henv.evalBool HasBool.ffVal hmono h
    | nondet => intro _; exact trivial
  have hthenSim := blockFrameTraceSim (label := none) henv.storeRel
    (hthen sourceEnv targetEnv henv hwfb hwfv hmono hwfc hwfvar
      hsourceThen htargetThen hinhabThen)
  have helseSim := blockFrameTraceSim (label := none) henv.storeRel
    (helse sourceEnv targetEnv henv hwfb hwfv hmono hwfc hwfvar
      hsourceElse htargetElse hinhabElse)
  have hstmt : ConfigTraceSim (HoistEnvRel sourceEnv.factory)
      (.stmt (.ite g sourceThen sourceElse md) sourceEnv)
      (.stmt (.ite g targetThen targetElse md) targetEnv) := by
    refine ⟨?_, ?_, ?_⟩
    · intro source' sourceTrace hrun
      match hrun with
      | .refl _ => exact ⟨_, [], .refl _, .nil⟩
      | .step _ emittedV nextCfg restTrace _ hfirst hrest =>
          rcases ite_stepE_inv hfirst with ⟨rfl, rfl, henter⟩ | ⟨rfl, rfl, hexit⟩
          · obtain ⟨target', targetTrace, htarget, htrace⟩ := hthenSim.simulate hrest
            exact ⟨target', targetTrace,
              ReflTransTrace.step _ _ _ _ _ (iteThenStepE (hEnterT henter)) htarget,
              by simpa using htrace⟩
          · obtain ⟨target', targetTrace, htarget, htrace⟩ := helseSim.simulate hrest
            exact ⟨target', targetTrace,
              ReflTransTrace.step _ _ _ _ _ (iteElseStepE (hExitT hexit)) htarget,
              by simpa using htrace⟩
    · intro sourceOut sourceTrace hrun
      match hrun with
      | .step _ emittedV nextCfg restTrace _ hfirst hrest =>
          rcases ite_stepE_inv hfirst with ⟨rfl, rfl, henter⟩ | ⟨rfl, rfl, hexit⟩
          · obtain ⟨targetOut, targetTrace, htarget, hrel, htrace⟩ :=
              hthenSim.terminal hrest
            exact ⟨targetOut, targetTrace,
              ReflTransTrace.step _ _ _ _ _ (iteThenStepE (hEnterT henter)) htarget,
              hrel, by simpa using htrace⟩
          · obtain ⟨targetOut, targetTrace, htarget, hrel, htrace⟩ :=
              helseSim.terminal hrest
            exact ⟨targetOut, targetTrace,
              ReflTransTrace.step _ _ _ _ _ (iteElseStepE (hExitT hexit)) htarget,
              hrel, by simpa using htrace⟩
    · intro exitLabel sourceOut sourceTrace hrun
      match hrun with
      | .step _ emittedV nextCfg restTrace _ hfirst hrest =>
          rcases ite_stepE_inv hfirst with ⟨rfl, rfl, henter⟩ | ⟨rfl, rfl, hexit⟩
          · obtain ⟨targetOut, targetTrace, htarget, hrel, htrace⟩ :=
              hthenSim.exiting hrest
            exact ⟨targetOut, targetTrace,
              ReflTransTrace.step _ _ _ _ _ (iteThenStepE (hEnterT henter)) htarget,
              hrel, by simpa using htrace⟩
          · obtain ⟨targetOut, targetTrace, htarget, hrel, htrace⟩ :=
              helseSim.exiting hrest
            exact ⟨targetOut, targetTrace,
              ReflTransTrace.step _ _ _ _ _ (iteElseStepE (hExitT hexit)) htarget,
              hrel, by simpa using htrace⟩
  exact hstmt.targetSingleton

private theorem nilBlockHoistTraceSim {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [HasInt P]
    [DecidableEq P.Ident] :
    BlockHoistTraceSim ([] : List (Stmt P (Cmd P))) [] := by
  intro sourceEnv targetEnv henv hwfb hwfv hmono hwfc hwfvar hsourceUndef
    htargetUndef hinhab
  refine ⟨?_, ?_, ?_⟩
  · intro source' sourceTrace hrun
    obtain ⟨htrace, _⟩ := stmts_nil_runE (EvalCmdE P) hrun
    subst htrace
    exact ⟨_, [], .refl _, .nil⟩
  · intro sourceOut sourceTrace hrun
    obtain ⟨htrace, hcfg⟩ := stmts_nil_runE (EvalCmdE P) hrun
    subst htrace
    rcases hcfg with hbad | hfinal
    · simp at hbad
    · injection hfinal with hsourceOut
      subst hsourceOut
      exact ⟨targetEnv, [], Imperative.StepStmtStarE.single
        (c := .stmts [] targetEnv) .step_stmts_nil, henv, .nil⟩
  · intro label sourceOut sourceTrace hrun
    obtain ⟨_, hcfg⟩ := stmts_nil_runE (EvalCmdE P) hrun
    rcases hcfg with hbad | hbad <;> simp at hbad

private theorem consBlockHoistTraceSim {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [HasInt P]
    [DecidableEq P.Ident]
    {sourceHead : Stmt P (Cmd P)} {sourceRest : List (Stmt P (Cmd P))}
    {targetHead targetRest : List (Stmt P (Cmd P))}
    (hhead : StmtHoistTraceSim sourceHead targetHead)
    (htail : BlockHoistTraceSim sourceRest targetRest)
    (hdef : ∀ y ∈ Block.definedVars (P := P) (C := Cmd P) targetHead false,
      y ∈ Stmt.initVars sourceHead)
    (hdisj : ∀ y ∈ Stmt.initVars sourceHead, y ∉ Block.initVars sourceRest) :
    BlockHoistTraceSim (sourceHead :: sourceRest) (targetHead ++ targetRest) := by
  intro sourceEnv targetEnv henv hwfb hwfv hmono hwfc hwfvar hsourceUndef
    htargetUndef hinhab
  have hsourceHead : ∀ y ∈ Stmt.initVars sourceHead, sourceEnv.store y = none := by
    intro y hy
    exact hsourceUndef y (by simpa [Block.initVars] using List.mem_append_left _ hy)
  have hsourceRest : ∀ y ∈ Block.initVars sourceRest, sourceEnv.store y = none := by
    intro y hy
    exact hsourceUndef y (by simpa [Block.initVars] using List.mem_append_right _ hy)
  have htargetHead : ∀ y ∈ Stmt.initVars sourceHead, targetEnv.store y = none := by
    intro y hy
    exact htargetUndef y (by simpa [Block.initVars] using List.mem_append_left _ hy)
  have htargetRest : ∀ y ∈ Block.initVars sourceRest, targetEnv.store y = none := by
    intro y hy
    exact htargetUndef y (by simpa [Block.initVars] using List.mem_append_right _ hy)
  have hinhabHead : Stmt.InitTypesInhabited sourceEnv.factory sourceHead := by
    intro ty hty
    exact hinhab ty (by simpa [Block.initTypes] using List.mem_append_left _ hty)
  have hinhabRest : Block.InitTypesInhabited sourceEnv.factory sourceRest := by
    intro ty hty
    exact hinhab ty (by simpa [Block.initTypes] using List.mem_append_right _ hty)
  have hheadSim := hhead sourceEnv targetEnv henv hwfb hwfv hmono hwfc hwfvar
    hsourceHead htargetHead hinhabHead
  have sourceRestInv : Config.varsUndefined false
      (fun y => y ∈ Block.initVars sourceRest) (.stmt sourceHead sourceEnv) := by
    intro y hy
    refine ⟨hsourceRest y hy, ?_⟩
    rw [show Stmt.definedVars (P := P) (C := Cmd P) sourceHead false =
      Stmt.initVars sourceHead from rfl]
    exact fun hmem => hdisj y hmem hy
  have targetDefinedMem : ∀ {stmt : Stmt P (Cmd P)}, stmt ∈ targetHead →
      ∀ {y}, y ∈ Stmt.definedVars stmt false →
        y ∈ Block.definedVars (P := P) (C := Cmd P) targetHead false := by
    intro stmt hstmt y hdefined
    clear hhead htail hdef hdisj hheadSim
    induction targetHead with
    | nil => simp at hstmt
    | cons first rest ihrest =>
        rw [Block.definedVars]
        rcases List.mem_cons.mp hstmt with rfl | hstmt
        · exact List.mem_append_left _ hdefined
        · exact List.mem_append_right _ (ihrest hstmt)
  have targetRestInv : Config.varsUndefined false
      (fun y => y ∈ Block.initVars sourceRest) (.stmts targetHead targetEnv) := by
    intro y hy
    refine ⟨htargetRest y hy, ?_⟩
    intro stmt hstmt hdefined
    apply hdisj y (hdef y ?_) hy
    exact targetDefinedMem hstmt hdefined
  have tailData : ∀ sourceMid targetMid sourceTrace targetTrace,
      StepStmtStarE P (EvalCmdE P) (.stmt sourceHead sourceEnv)
        sourceTrace (.terminal sourceMid) →
      StepStmtStarE P (EvalCmdE P) (.stmts targetHead targetEnv)
        targetTrace (.terminal targetMid) →
      HoistEnvRel sourceEnv.factory sourceMid targetMid →
      BlockHoistTraceSim sourceRest targetRest →
      ConfigTraceSim (HoistEnvRel sourceEnv.factory)
        (.stmts sourceRest sourceMid) (.stmts targetRest targetMid) := by
    intro sourceMid targetMid sourceTrace targetTrace hsourceRun htargetRun hrelMid htail'
    have hsourceRestMid : ∀ y ∈ Block.initVars sourceRest, sourceMid.store y = none := by
      intro y hy
      exact (Config.varsUndefinedThroughout_starE hsourceRun sourceRestInv y hy)
    have htargetRestMid : ∀ y ∈ Block.initVars sourceRest, targetMid.store y = none := by
      intro y hy
      exact (Config.varsUndefinedThroughout_starE htargetRun targetRestInv y hy)
    have hsourceFactory : sourceMid.factory = sourceEnv.factory := by
      have hf := starE_preserves_factory hsourceRun
      simpa [Config.getEnv] using hf.symm
    have hrelMid' : HoistEnvRel sourceMid.factory sourceMid targetMid := by
      rw [hsourceFactory]
      exact hrelMid
    have htailSim := htail' sourceMid targetMid hrelMid'
      (by rw [hsourceFactory]; exact hwfb)
      (by rw [hsourceFactory]; exact hwfv)
      (by rw [hsourceFactory]; exact hmono)
      (by rw [hsourceFactory]; exact hwfc)
      (by rw [hsourceFactory]; exact hwfvar)
      hsourceRestMid htargetRestMid (by rw [hsourceFactory]; exact hinhabRest)
    simpa [hsourceFactory] using htailSim
  refine ⟨?_, ?_, ?_⟩
  · intro source' sourceTrace hrun
    rcases stmts_cons_headE (EvalCmdE P) hrun with ⟨hcfg, htrace⟩ | hseq
    · subst hcfg
      subst htrace
      exact ⟨_, [], .refl _, .nil⟩
    · rcases seq_run_decomposeE (EvalCmdE P) hseq with
        ⟨headFinal, hfinal, hsourceHeadRun⟩ |
        ⟨sourceMid, headTrace, tailTrace, htrace, hsourceHeadRun, hsourceTailRun⟩ |
        ⟨exitLabel, exitEnv, hfinal, hsourceHeadRun⟩
      · subst hfinal
        obtain ⟨targetHeadFinal, targetTrace, htargetHeadRun, htraceHead⟩ :=
          hheadSim.simulate hsourceHeadRun
        obtain ⟨targetFinal, htargetRun⟩ :=
          stmts_prefix_appendE targetHead targetRest targetEnv htargetHeadRun
        exact ⟨targetFinal, targetTrace, htargetRun, htraceHead⟩
      · obtain ⟨targetMid, targetHeadTrace, htargetHeadRun, hrelMid, htraceHead⟩ :=
          hheadSim.terminal hsourceHeadRun
        have htargetPrefix := stmts_prefix_terminal_appendE targetHead targetRest
          targetEnv targetMid htargetHeadRun
        have htailSim := tailData sourceMid targetMid headTrace targetHeadTrace
          hsourceHeadRun htargetHeadRun hrelMid htail
        obtain ⟨targetFinal, targetTailTrace, htargetTailRun, htraceTail⟩ :=
          htailSim.simulate hsourceTailRun
        refine ⟨targetFinal, targetHeadTrace ++ targetTailTrace,
          ReflTransTrace.trans _ htargetPrefix htargetTailRun, ?_⟩
        rw [htrace]
        exact TraceExtendsEnv.append htraceHead htraceTail
      · subst hfinal
        obtain ⟨targetExitEnv, targetTrace, htargetHeadRun, _, htraceHead⟩ :=
          hheadSim.exiting hsourceHeadRun
        exact ⟨_, targetTrace, stmts_prefix_exiting_appendE targetHead targetRest
          targetEnv targetExitEnv exitLabel htargetHeadRun, htraceHead⟩
  · intro sourceOut sourceTrace hrun
    rcases stmts_cons_headE (EvalCmdE P) hrun with hbad | hseq
    · simp at hbad
    · obtain ⟨sourceMid, headTrace, tailTrace, htrace, hsourceHeadRun,
        hsourceTailRun⟩ := seq_reaches_terminalE (EvalCmdE P) hseq
      obtain ⟨targetMid, targetHeadTrace, htargetHeadRun, hrelMid, htraceHead⟩ :=
        hheadSim.terminal hsourceHeadRun
      have htargetPrefix := stmts_prefix_terminal_appendE targetHead targetRest
        targetEnv targetMid htargetHeadRun
      have htailSim := tailData sourceMid targetMid headTrace targetHeadTrace
        hsourceHeadRun htargetHeadRun hrelMid htail
      obtain ⟨targetOut, targetTailTrace, htargetTailRun, hrelOut, htraceTail⟩ :=
        htailSim.terminal hsourceTailRun
      refine ⟨targetOut, targetHeadTrace ++ targetTailTrace,
        ReflTransTrace.trans _ htargetPrefix htargetTailRun, hrelOut, ?_⟩
      rw [htrace]
      exact TraceExtendsEnv.append htraceHead htraceTail
  · intro exitLabel sourceOut sourceTrace hrun
    rcases stmts_cons_headE (EvalCmdE P) hrun with hbad | hseq
    · simp at hbad
    · rcases seq_reaches_exitingE (EvalCmdE P) hseq with hsourceHeadRun |
        ⟨sourceMid, headTrace, tailTrace, htrace, hsourceHeadRun, hsourceTailRun⟩
      · obtain ⟨targetOut, targetTrace, htargetHeadRun, hrelOut, htraceHead⟩ :=
          hheadSim.exiting hsourceHeadRun
        exact ⟨targetOut, targetTrace,
          stmts_prefix_exiting_appendE targetHead targetRest targetEnv targetOut exitLabel
            htargetHeadRun,
          hrelOut, htraceHead⟩
      · obtain ⟨targetMid, targetHeadTrace, htargetHeadRun, hrelMid, htraceHead⟩ :=
          hheadSim.terminal hsourceHeadRun
        have htargetPrefix := stmts_prefix_terminal_appendE targetHead targetRest
          targetEnv targetMid htargetHeadRun
        have htailSim := tailData sourceMid targetMid headTrace targetHeadTrace
          hsourceHeadRun htargetHeadRun hrelMid htail
        obtain ⟨targetOut, targetTailTrace, htargetTailRun, hrelOut, htraceTail⟩ :=
          htailSim.exiting hsourceTailRun
        refine ⟨targetOut, targetHeadTrace ++ targetTailTrace,
          ReflTransTrace.trans _ htargetPrefix htargetTailRun, hrelOut, ?_⟩
        rw [htrace]
        exact TraceExtendsEnv.append htraceHead htraceTail

private theorem ConfigTraceSim.mapRel {P : PureExpr}
    [HasFvar P] [HasBoolOps P]
    {R S : Env P → Env P → Prop}
    (hmap : ∀ source target, R source target → S source target)
    {source target : Config P (Cmd P)}
    (h : ConfigTraceSim R source target) :
    ConfigTraceSim S source target := by
  refine ⟨h.simulate, ?_, ?_⟩
  · intro sourceEnv sourceTrace hrun
    obtain ⟨targetEnv, targetTrace, htarget, hrel, htrace⟩ := h.terminal hrun
    exact ⟨targetEnv, targetTrace, htarget, hmap _ _ hrel, htrace⟩
  · intro label sourceEnv sourceTrace hrun
    obtain ⟨targetEnv, targetTrace, htarget, hrel, htrace⟩ := h.exiting hrun
    exact ⟨targetEnv, targetTrace, htarget, hmap _ _ hrel, htrace⟩

def RecursiveLoopRel {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [HasInt P]
    [DecidableEq P.Ident]
    (factory : P.Factory) (body : List (Stmt P (Cmd P)))
    (source target : Env P) : Prop :=
  HoistEnvRel factory source target ∧
  WellFormedSemanticEvalBool factory ∧
  WellFormedSemanticEvalVal factory ∧
  WellFormedSemanticEvalMono factory ∧
  WellFormedSemanticEvalExprCongr factory ∧
  WellFormedSemanticEvalVar factory ∧
  (∀ y ∈ Block.initVars body, source.store y = none) ∧
  (∀ y ∈ Block.initVars body, target.store y = none) ∧
  Block.InitTypesInhabited factory body

private theorem RecursiveLoopRel.projectBody {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [HasInt P]
    [DecidableEq P.Ident]
    {factory : P.Factory} {body : List (Stmt P (Cmd P))}
    {sourceParent targetParent sourceInner targetInner : Env P}
    (hp : RecursiveLoopRel factory body sourceParent targetParent)
    (hi : HoistEnvRel factory sourceInner targetInner) :
    RecursiveLoopRel factory body
      { sourceInner with store := projectStore sourceParent.store sourceInner.store }
      { targetInner with store := projectStore targetParent.store targetInner.store } := by
  refine ⟨HoistEnvRel.project hp.1.storeRel hi,
    hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, ?_, ?_,
    hp.2.2.2.2.2.2.2.2⟩
  · intro y hy
    exact projectStore_undef_at (hp.2.2.2.2.2.2.1 y hy)
  · intro y hy
    exact projectStore_undef_at (hp.2.2.2.2.2.2.2.1 y hy)

private theorem loopHoistTraceSim {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [HasInt P]
    [DecidableEq P.Ident] [LawfulHasVal P]
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P}
    (hbody : BlockHoistTraceSim body (Block.hoistLoopPrefixInits body))
    (hunique : (Block.initVars body).Nodup) :
    StmtHoistTraceSim (.loop g m inv body md)
      (Stmt.hoistLoopPrefixInits (.loop g m inv body md)) := by
  let body₁ := Block.hoistLoopPrefixInits body
  let havocs := (Block.liftInitsInLoopBody body₁).1
  let body₂ := (Block.liftInitsInLoopBody body₁).2
  have hloops₁ : Block.loopBodyNoInits body₁ = true :=
    LoopInitHoistProducerProps.Block.hoistP_allLoop_uncond body
  have hnoinit₂ : Block.noInitsAnywhere body₂ = true := by
    exact LoopInitHoistProducerProps.Block.liftP_res_noInits body₁ hloops₁
  obtain ⟨hs, hmap, hnames, htypedHavocs⟩ :=
    LoopInitHoistProducerProps.nondet_cmds_to_prelude havocs
      (LoopInitHoistProducerProps.Block.liftP_havocs_nondet body₁)
  have hperm : List.Perm (LoopInitHoistProducerProps.preludeNames hs)
      (Block.initVars body) := by
    rw [hnames]
    have hp := LoopInitHoistProducerProps.Block.liftP_initVars_perm body₁
    rw [Block.initVars_eq_nil_of_noInitsAnywhere body₂ hnoinit₂, List.append_nil] at hp
    exact hp.trans (LoopInitHoistProducerProps.Block.hoistP_initVars_perm body)
  have hnodupNames : (LoopInitHoistProducerProps.preludeNames hs).Nodup :=
    hperm.nodup_iff.mpr hunique
  have hbridge : hs.map (fun t => (t.1, t.2.1)) =
      LoopInitHoistProducerProps.Block.typedInitVars body₁ := by
    rw [htypedHavocs,
      LoopInitHoistProducerProps.Block.liftP_typedInitVars_res body₁]
  let Dτ : P.Ident → P.Ty :=
    LoopInitHoistProducerProps.typedInitVarsLookup
      (LoopInitHoistProducerProps.Block.typedInitVars body₁)
  have htypedNames :
      ((LoopInitHoistProducerProps.Block.typedInitVars body₁).map Prod.fst).Nodup := by
    have heq : (LoopInitHoistProducerProps.Block.typedInitVars body₁).map Prod.fst =
        LoopInitHoistProducerProps.preludeNames hs := by
      rw [← hbridge]
      simp [LoopInitHoistProducerProps.preludeNames, List.map_map, Function.comp]
    rw [heq]
    exact hnodupNames
  have hDτ : ∀ p ∈ LoopInitHoistProducerProps.Block.typedInitVars body₁,
      Dτ p.1 = p.2 :=
    fun p hp => LoopInitHoistProducerProps.typedInitVarsLookup_agrees _ htypedNames p hp
  have hty : ∀ t ∈ hs, Dτ t.1 = t.2.1 := by
    intro t ht
    apply hDτ (t.1, t.2.1)
    rw [← hbridge]
    exact List.mem_map.mpr ⟨t, ht, rfl⟩
  have htypedMem : ∀ p ∈ LoopInitHoistProducerProps.Block.typedInitVars body₁,
      p.1 ∈ LoopInitHoistProducerProps.preludeNames hs ∧ Dτ p.1 = p.2 := by
    intro p hp
    refine ⟨?_, hDτ p hp⟩
    have hm : p.1 ∈ (LoopInitHoistProducerProps.Block.typedInitVars body₁).map Prod.fst :=
      List.mem_map.mpr ⟨p, hp, rfl⟩
    simpa [← hbridge, LoopInitHoistProducerProps.preludeNames,
      List.map_map, Function.comp] using hm
  have hliftBlock : LiftBlockRel Dτ (LoopInitHoistProducerProps.preludeNames hs)
      body₁ body₂ :=
    ⟨rfl, hloops₁, htypedMem⟩
  have htypeSub : ∀ t ∈ hs, t.2.1 ∈ Block.initTypes body₁ := by
    intro t ht
    exact LoopInitHoistProducerProps.Block.typedInitVars_snd_sub_initTypes _
      (t.1, t.2.1) (by rw [← hbridge]; exact List.mem_map.mpr ⟨t, ht, rfl⟩)
  have hout : Stmt.hoistLoopPrefixInits (.loop g m inv body md) =
      LoopInitHoistProducerProps.preludeHavocs hs ++
        [.loop g m inv body₂ md] := by
    rw [show Stmt.hoistLoopPrefixInits (.loop g m inv body md) =
      havocs.map Stmt.cmd ++ [.loop g m inv body₂ md] by
        simp [body₁, havocs, body₂, Stmt.hoistLoopPrefixInits]]
    rw [hmap]
  rw [hout]
  intro sourceEnv targetEnv henv hwfb hwfv hmono hwfc hwfvar hsourceUndef
    htargetUndef hinhab
  have hrecursive : RecursiveLoopRel sourceEnv.factory body sourceEnv targetEnv :=
    ⟨henv, hwfb, hwfv, hmono, hwfc, hwfvar, hsourceUndef, htargetUndef, hinhab⟩
  have henterTargetA : ∀ source target,
      RecursiveLoopRel sourceEnv.factory body source target →
      LoopGuardEnter g source → LoopGuardEnter g target := by
    intro source target hrel h
    cases g with
    | det guard => exact hrel.1.evalBool HasBool.ttVal hrel.2.2.2.1 h
    | nondet => exact trivial
  have hexitTargetA : ∀ source target,
      RecursiveLoopRel sourceEnv.factory body source target →
      LoopGuardExit g source → LoopGuardExit g target := by
    intro source target hrel h
    cases g with
    | det guard => exact hrel.1.evalBool HasBool.ffVal hrel.2.2.2.1 h
    | nondet => exact trivial
  have hlegA : ConfigTraceSim (RecursiveLoopRel sourceEnv.factory body)
      (.stmt (.loop g m inv body md) sourceEnv)
      (.stmt (.loop g m inv body₁ md) targetEnv) :=
    loopTraceSim (R := RecursiveLoopRel sourceEnv.factory body)
      (B := HoistEnvRel sourceEnv.factory)
      henterTargetA hexitTargetA
      (fun _ _ _ _ hp hi => RecursiveLoopRel.projectBody hp hi)
      (fun source target hrel => by
        have hsourceFactory := hrel.1.sourceFactory
        have hsim := hbody source target
          (by rw [hsourceFactory]; exact hrel.1)
          (by rw [hsourceFactory]; exact hrel.2.1)
          (by rw [hsourceFactory]; exact hrel.2.2.1)
          (by rw [hsourceFactory]; exact hrel.2.2.2.1)
          (by rw [hsourceFactory]; exact hrel.2.2.2.2.1)
          (by rw [hsourceFactory]; exact hrel.2.2.2.2.2.1)
          hrel.2.2.2.2.2.2.1 hrel.2.2.2.2.2.2.2.1
          (by rw [hsourceFactory]; exact hrel.2.2.2.2.2.2.2.2)
        simpa [hsourceFactory] using hsim)
      hrecursive
  have hnamesSub : ∀ y ∈ LoopInitHoistProducerProps.preludeNames hs,
      y ∈ Block.initVars body := fun y hy => hperm.mem_iff.mp hy
  have hnoneNames : ∀ y ∈ LoopInitHoistProducerProps.preludeNames hs,
      targetEnv.store y = none := fun y hy => htargetUndef y (hnamesSub y hy)
  have hinhab₁ : Block.InitTypesInhabited targetEnv.factory body₁ := by
    rw [henv.targetFactory, ← henv.sourceFactory]
    exact LoopInitHoistProducerProps.Block.hoistP_initTypesInhabited hinhab
  have hpreInhab : ∀ t ∈ hs, ∃ value,
      HasVal.valueOfTy targetEnv.factory value t.2.1 := by
    intro t ht
    exact hinhab₁ t.2.1 (htypeSub t ht)
  obtain ⟨preEnv, preludeTrace, hprelude, hagreePre, hfactoryPre,
      htypedPre, hpreludeRelations⟩ :=
    LoopInitHoistProducerProps.prelude_runnerE hs [] targetEnv targetEnv
      (by intro y hy; exact absurd hy List.not_mem_nil)
      (StoreAgreement.refl _) hnoneNames hnoneNames hnodupNames hty hpreInhab
      (by rw [henv.targetFactory, ← henv.sourceFactory]; exact hwfvar)
  have hliftEnv : LiftEnvRel Dτ (LoopInitHoistProducerProps.preludeNames hs)
      targetEnv.factory targetEnv preEnv :=
    ⟨hagreePre, rfl, hfactoryPre, by simpa using htypedPre⟩
  have hmonoTarget : WellFormedSemanticEvalMono targetEnv.factory := by
    rw [henv.targetFactory, ← henv.sourceFactory]
    exact hmono
  have henterTargetB : ∀ source target,
      LiftEnvRel Dτ (LoopInitHoistProducerProps.preludeNames hs) targetEnv.factory source target →
      LoopGuardEnter g source → LoopGuardEnter g target := by
    intro source target hrel h
    cases g with
    | det guard => exact hrel.evalBool HasBool.ttVal hmonoTarget h
    | nondet => exact trivial
  have hexitTargetB : ∀ source target,
      LiftEnvRel Dτ (LoopInitHoistProducerProps.preludeNames hs) targetEnv.factory source target →
      LoopGuardExit g source → LoopGuardExit g target := by
    intro source target hrel h
    cases g with
    | det guard => exact hrel.evalBool HasBool.ffVal hmonoTarget h
    | nondet => exact trivial
  have hlegBLoop : ConfigTraceSim
      (LiftEnvRel Dτ (LoopInitHoistProducerProps.preludeNames hs) targetEnv.factory)
      (.stmt (.loop g m inv body₁ md) targetEnv)
      (.stmt (.loop g m inv body₂ md) preEnv) :=
    loopTraceSim
      henterTargetB hexitTargetB
      (fun _ _ _ _ hp hi => LiftEnvRel.project hp.storeRel hi)
      (fun source target hrel =>
        liftConfigRel_traceSim hmonoTarget (.stmts hrel hliftBlock))
      hliftEnv
  have hlegB := preludeThenTraceSim hprelude hpreludeRelations.2 hlegBLoop
  have hlegA' : ConfigTraceSim (HoistEnvRel sourceEnv.factory)
      (.stmt (.loop g m inv body md) sourceEnv)
      (.stmt (.loop g m inv body₁ md) targetEnv) :=
    hlegA.mapRel (fun _ _ hrel => hrel.1)
  have hlegB' : ConfigTraceSim (HoistEnvRel sourceEnv.factory)
      (.stmt (.loop g m inv body₁ md) targetEnv)
      (.stmts (LoopInitHoistProducerProps.preludeHavocs hs ++
        [.loop g m inv body₂ md]) targetEnv) :=
    hlegB.mapRel (fun _ _ hrel => by
      have h := liftEnvRel_to_hoist hrel
      simpa [henv.targetFactory] using h)
  exact ConfigTraceSim.trans
    (R₁ := HoistEnvRel sourceEnv.factory)
    (R₂ := HoistEnvRel sourceEnv.factory)
    (R₃ := HoistEnvRel sourceEnv.factory)
    (fun _ _ _ hA hB => HoistEnvRel.trans hA hB) hlegA' hlegB'

mutual
private theorem Stmt.hoistP_trace_sim {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [HasInt P]
    [DecidableEq P.Ident] [LawfulHasVal P]
    (stmt : Stmt P (Cmd P))
    (hunique : (Stmt.initVars stmt).Nodup) :
    StmtHoistTraceSim stmt (Stmt.hoistLoopPrefixInits stmt) := by
  match stmt, hunique with
  | .cmd command, _ =>
      rw [show Stmt.hoistLoopPrefixInits (.cmd command) = [.cmd command] by
        rw [Stmt.hoistLoopPrefixInits]]
      exact cmdHoistTraceSim command
  | .block label body md, hunique =>
      rw [show Stmt.hoistLoopPrefixInits (.block label body md) =
        [.block label (Block.hoistLoopPrefixInits body) md] by
          rw [Stmt.hoistLoopPrefixInits]]
      exact blockHoistTraceSim
        (Block.hoistP_trace_sim body
          (by simpa [Stmt.initVars] using hunique))
  | .ite g thenBody elseBody md, hunique =>
      rw [show Stmt.hoistLoopPrefixInits (.ite g thenBody elseBody md) =
        [.ite g (Block.hoistLoopPrefixInits thenBody)
          (Block.hoistLoopPrefixInits elseBody) md] by
            rw [Stmt.hoistLoopPrefixInits]]
      have hunique' : (Block.initVars thenBody ++ Block.initVars elseBody).Nodup := by
        simpa [Stmt.initVars] using hunique
      exact iteHoistTraceSim
        (Block.hoistP_trace_sim thenBody
          (List.nodup_append.mp hunique').1)
        (Block.hoistP_trace_sim elseBody
          (List.nodup_append.mp hunique').2.1)
  | .loop g measure invariants body md, hunique =>
      have huniqueBody : (Block.initVars body).Nodup := by
        simpa [Stmt.initVars] using hunique
      exact loopHoistTraceSim
        (Block.hoistP_trace_sim body huniqueBody)
        huniqueBody
  | .exit label md, _ =>
      rw [show Stmt.hoistLoopPrefixInits (.exit label md) = [.exit label md] by
        rw [Stmt.hoistLoopPrefixInits]]
      exact exitHoistTraceSim label md
  | .typeDecl typeCtor md, _ =>
      rw [show Stmt.hoistLoopPrefixInits (.typeDecl typeCtor md) =
        [.typeDecl typeCtor md] by rw [Stmt.hoistLoopPrefixInits]]
      exact typeDeclHoistTraceSim typeCtor md
  termination_by sizeOf stmt

private theorem Block.hoistP_trace_sim {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [HasInt P]
    [DecidableEq P.Ident] [LawfulHasVal P]
    (stmts : List (Stmt P (Cmd P)))
    (hunique : (Block.initVars stmts).Nodup) :
    BlockHoistTraceSim stmts (Block.hoistLoopPrefixInits stmts) := by
  match stmts, hunique with
  | [], _ =>
      rw [show Block.hoistLoopPrefixInits ([] : List (Stmt P (Cmd P))) = [] by
        rw [Block.hoistLoopPrefixInits]]
      exact nilBlockHoistTraceSim
  | head :: rest, hunique =>
      rw [show Block.hoistLoopPrefixInits (head :: rest) =
        Stmt.hoistLoopPrefixInits head ++ Block.hoistLoopPrefixInits rest by
          rw [Block.hoistLoopPrefixInits]]
      have hunique' : (Stmt.initVars head ++ Block.initVars rest).Nodup := by
        simpa [Block.initVars] using hunique
      have hdisj : ∀ y ∈ Stmt.initVars head, y ∉ Block.initVars rest := by
        have hd := (List.nodup_append.mp hunique').2.2
        intro y hyHead hyRest
        exact hd y hyHead y hyRest rfl
      exact consBlockHoistTraceSim
        (Stmt.hoistP_trace_sim head
          (List.nodup_append.mp hunique').1)
        (Block.hoistP_trace_sim rest
          (List.nodup_append.mp hunique').2.1)
        (fun y hy => LoopInitHoistProducerProps.Stmt.hoistP_initVars_sub head y hy)
        hdisj
  termination_by sizeOf stmts
end

section HoistTraceOverapprox

open Imperative.Specification Imperative.Specification.Transform Imperative.Logic
open StructuredToUnstructured

/-- Loop-initializer hoisting simulates every finite event trace under
`Trace.WithWF` matching and preserves terminal and exiting stores up to
`EnvStoreAgree`.  The hoisted `init` prelude commands are event-silent and the
remaining commands replay one-for-one, so no event is inserted or dropped on
either side; the simulation already produces the lockstep witness, which this
theorem exposes directly.

The guards of `ite`/`loop` statements (deterministic or nondeterministic) and a
loop's measure and invariant annotations are operationally inert, so the only
precondition the transform requires is that inits declared across the block are
unique. -/
theorem LoopInitHoist.overapproximatesTraces {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [HasInt P] [HasIntOps P] [DecidableEq P.Ident]
    [LawfulHasIdent P] [LawfulHasVal P] [HasSubstFvar P] [HasOps P]
    (params : Imperative.Logic.InitEnvWFParams P) :
    Specification.Transform.OverapproximatesTracesUptoWhen
      (Trace.WithWF (P := P) (EventArg.ExtendsEnv (fun _ => True)))
      (· = ·)
      (EnvStoreAgree (P := P))
      (EventLang.imperativeBlockE P (Cmd P) (EvalCmdE P)
        ⟨Imperative.Logic.InitEnvWFParams P, BlockInitEnvWF⟩)
      (EventLang.imperativeBlockE P (Cmd P) (EvalCmdE P)
        ⟨Imperative.Logic.InitEnvWFParams P, BlockInitEnvWF⟩)
      (fun stmts => some (Block.hoistLoopPrefixInits stmts))
      (fun stmts => Block.uniqueInits stmts)
      params params := by
  intro stmts targetStmts htransform hunique sourceEnv targetEnv hinput hwf
  subst hinput
  simp only [Option.some.injEq] at htransform
  subst htransform
  change BlockInitEnvWF params stmts sourceEnv at hwf
  have hsim := Block.hoistP_trace_sim stmts hunique
    sourceEnv sourceEnv
    (show HoistEnvRel sourceEnv.factory sourceEnv sourceEnv from
      ⟨StoreAgreement.refl _, rfl, rfl⟩)
    hwf.bool hwf.val hwf.mono hwf.exprCongr hwf.var
    (fun ident hident =>
      Option.isNone_iff_eq_none.mp (hwf.defsUndefined ident hident))
    (fun ident hident =>
      Option.isNone_iff_eq_none.mp (hwf.defsUndefined ident hident))
    hwf.initTypesInhabited
  have hstrong : ∀ {sourceFinal targetFinal : Config P (Cmd P)}
      {sourceTrace targetTrace : Trace P},
      StepStmtStarE P (EvalCmdE P) (.stmts stmts sourceEnv) sourceTrace sourceFinal →
      StepStmtStarE P (EvalCmdE P)
        (.stmts (Block.hoistLoopPrefixInits stmts) sourceEnv) targetTrace targetFinal →
      TraceExtendsEnv (fun _ : P.Ident => True) sourceTrace targetTrace →
      Trace.WithWF (P := P) (EventArg.ExtendsEnv (fun _ => True)) sourceTrace targetTrace := by
    intro _ _ _ _ hrun htarget htrace
    exact Trace.WithWF.of_extends htrace
      (Block.run_readsDefined hwf.defUseOk hrun)
      (Trace.semanticWF_of_starE hrun hwf.val hwf.exprCongr hwf.storeWellDefined)
      (Trace.semanticWF_of_starE htarget hwf.val hwf.exprCongr hwf.storeWellDefined)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro sourceFinal sourceTrace hrun
    obtain ⟨targetFinal, targetTrace, htarget, htrace⟩ := hsim.simulate hrun
    exact ⟨targetFinal, targetTrace, htarget, hstrong hrun htarget htrace⟩
  · intro sourceFinal sourceTrace hrun
    obtain ⟨targetFinal, targetTrace, htarget, hrel, htrace⟩ := hsim.terminal hrun
    exact ⟨targetFinal, targetTrace, htarget, hrel.agreement,
      hstrong hrun htarget htrace⟩
  · intro label sourceFinal sourceTrace hrun
    obtain ⟨targetFinal, targetTrace, htarget, hrel, htrace⟩ := hsim.exiting hrun
    exact ⟨targetFinal, targetTrace, htarget, hrel.agreement,
      hstrong hrun htarget htrace⟩
  · change BlockInitEnvWF params
      (Block.hoistLoopPrefixInits stmts) sourceEnv
    have hdu :=
      LoopInitHoistWF.Block.hoistLoopPrefixInits_defUseWellFormed
        stmts (fun ident => (sourceEnv.store ident).isSome)
        params.declaredFuncs hwf.defUseOk hunique
    exact
      { toWellFormedSemanticEval := hwf.toWellFormedSemanticEval
        storeWellDefined := hwf.storeWellDefined
        readWritesDefined := fun _ htouched hnotDefined =>
          Block.defined_of_mem_touchedVars (fun _ _ h => h) hdu
            htouched hnotDefined
        defsUndefined := fun ident hident =>
          hwf.defsUndefined ident
            (LoopInitHoistProducerProps.Block.hoistP_initVars_sub
              stmts ident hident)
        definedVarsNotReserved := fun ident hident =>
          hwf.definedVarsNotReserved ident
            (LoopInitHoistProducerProps.Block.hoistP_initVars_sub
              stmts ident hident)
        reservedFresh := hwf.reservedFresh
        defUseOk := hdu
        initTypesInhabited :=
          LoopInitHoistProducerProps.Block.hoistP_initTypesInhabited
            hwf.initTypesInhabited
        fvarTypesOk := by
          obtain ⟨Γ, hσ, hw⟩ := hwf.fvarTypesOk
          refine ⟨Γ, hσ, LoopInitHoistWF.Block.hoistLoopPrefixInits_fvarTypesWellAnnotated
            stmts Γ (fun y hy => hσ.eq_none_of_store_none (hwf.defsUndefined y hy))
            hunique hw⟩ }

end HoistTraceOverapprox

end Imperative

end -- public section
