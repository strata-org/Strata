/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF.FoldAndDecompose
import all Strata.DL.Imperative.ToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline

/-! # WellFormedTranslation - Block body closures

This file is part 5 of the CoreCFGToGotoTransformWF split. It
provides the closure helpers for the hypothesis-parameter fields of
`coreCFGToGotoTransform_wellFormed_nonempty`:

* `entry_in_map_of_translator`
* `labelMap_inj_of_translator` and helpers
* `layout_block_body_of_translator` and helpers
* the patcher's "preserves full instruction except target" lemmas
-/

namespace CProverGOTO

open Imperative

public section

/-! ## Closures for hypothesis-parameter fields of `_wellFormed_nonempty`

Each closure theorem (`entry_in_map_of_translator`,
`labelMap_inj_of_translator`, `layout_block_body_of_translator`) takes
the same inputs as `coreCFGToGotoTransform_wellFormed_nonempty` and
produces the matching hypothesis shape. The
`layout_cond_goto`/`layout_cond_goto_guards` closures are below
(`layout_cond_goto_of_translator`, `layout_cond_goto_guards_of_translator`). -/

/-- Closure for `entry_in_map`. Trivial corollary of
`blocksFoldlM_layout_location` — given `cfg.blocks.head?.map Prod.fst =
some cfg.entry` (the entry-first invariant the translator checks), the
first block's label IS `cfg.entry`, so `(cfg.entry, _) ∈ cfg.blocks`,
and `blocksFoldlM_layout_location` gives the labelMap entry.

The translator's entry-check ensures `cfg.blocks ≠ []` whenever the
entry is to be used. We require `h_entry_first` to be supplied; in the
`coreCFGToGotoTransform_decompose` empty-blocks branch, the labelMap
remains empty and `entry_in_map` is unprovable — but the entry-check
in `coreCFGToGotoTransform` would have to either accept `cfg.blocks = []`
(and then nothing references `cfg.entry`) or reject. The translator's
implementation does both: it accepts `cfg.blocks = []` as a no-op, but
then `h_entry_first` (which the caller supplies) constrains the case. -/
theorem entry_in_map_of_translator
    (cfg : Core.DetCFG)
    (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_distinct : BlockLabelsDistinct cfg.blocks)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_entry_first : cfg.blocks.head?.map Prod.fst = some cfg.entry) :
    ∀ (st_final : Strata.CoreCFGTransLoopState),
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀) = Except.ok st_final →
    ∃ pc, hashMapToLabelMap st_final.labelMap cfg.entry = some pc := by
  intro st_final h_blocks_run
  -- The `head?` witness gives us a (l, blk) ∈ cfg.blocks with l = cfg.entry.
  cases h_blocks : cfg.blocks with
  | nil =>
    -- head?.map _ = none ≠ some cfg.entry; contradiction.
    rw [h_blocks] at h_entry_first
    simp at h_entry_first
  | cons hd rest =>
    obtain ⟨l, blk⟩ := hd
    rw [h_blocks] at h_entry_first
    simp at h_entry_first
    -- h_entry_first : l = cfg.entry. Substitute.
    subst h_entry_first
    -- Apply blocksFoldlM_layout_location.
    have h_in : (cfg.entry, blk) ∈ cfg.blocks := by
      rw [h_blocks]; simp
    have h_init_size_st :
        (coreCFGToGotoInitState trans₀).trans.instructions.size =
          (coreCFGToGotoInitState trans₀).trans.nextLoc := by
      simp [coreCFGToGotoInitState]; exact h_init_size
    have h_admitted_st :
        ∀ lblBlk ∈ cfg.blocks, ∀ c ∈ lblBlk.2.cmds,
          Core.CmdExt.isAdmittedCmd c = true :=
      fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb
    obtain ⟨pc, _, h_lookup, _, _, _⟩ :=
      blocksFoldlM_layout_location functionName cfg.blocks _ st_final
        h_admitted_st h_blocks_run h_init_size_st h_distinct cfg.entry blk h_in
    refine ⟨pc, ?_⟩
    show st_final.labelMap[cfg.entry]? = some pc
    exact h_lookup

/-! ### Helpers for `labelMap_inj_of_translator`

The strategy is a stronger combined invariant `(I)`:
1. Every pc in the labelMap is `< trans.nextLoc`.
2. The labelMap is injective.

Each block step preserves `(I)` because:
- The newly inserted pc equals the pre-step `nextLoc`, which is
  strictly less than the post-step `nextLoc` (by
  `coreCFGToGotoBlockStep_nextLoc_advance_*`). So all post-step pcs
  remain `< new nextLoc`.
- For injectivity: pre-existing pcs were `< pre-step nextLoc`; the new
  pc equals the pre-step `nextLoc`. So no old entry can collide with
  the new entry. Within the old entries, injectivity follows from
  the IH. Within the new entry alone, trivially distinct.

`(I)` holds at the initial state (empty labelMap). Applying via
`blocksFoldlM` yields `(I)` at `st_final`, from which `labelMap_inj`
follows. -/

/-- Combined invariant: labelMap codomain is bounded by `nextLoc`
and the labelMap is injective. -/
@[expose] def labelMapBoundedAndInj
    (m : Std.HashMap String Nat) (nextLoc : Nat) : Prop :=
  (∀ (l : String) (pc : Nat), m[l]? = some pc → pc < nextLoc) ∧
  (∀ (l₁ l₂ : String) (pc : Nat),
    m[l₁]? = some pc → m[l₂]? = some pc → l₁ = l₂)

/-- The empty labelMap satisfies the invariant trivially. -/
theorem labelMapBoundedAndInj_empty (n : Nat) :
    labelMapBoundedAndInj (∅ : Std.HashMap String Nat) n := by
  refine ⟨?_, ?_⟩
  · intro l pc h
    simp [Std.HashMap.getElem?_empty] at h
  · intro l₁ l₂ pc h₁ h₂
    simp [Std.HashMap.getElem?_empty] at h₁

/-- Per-block step preserves `labelMapBoundedAndInj`, because the new
pc equals the old `nextLoc` and the new `nextLoc` strictly advances. -/
theorem coreCFGToGotoBlockStep_preserves_labelMapBoundedAndInj
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_inv : labelMapBoundedAndInj st.labelMap st.trans.nextLoc) :
    labelMapBoundedAndInj st'.labelMap st'.trans.nextLoc := by
  obtain ⟨h_bound, h_inj⟩ := h_inv
  -- The labelMap effect: insert lblBlk.1 ↦ st.trans.nextLoc.
  have h_lbl : st'.labelMap = st.labelMap.insert lblBlk.1 st.trans.nextLoc :=
    coreCFGToGotoBlockStep_labelMap fname lblBlk st st' h_run
  -- The nextLoc advance: depending on transfer.
  have h_advance : st.trans.nextLoc < st'.trans.nextLoc := by
    cases h_t : lblBlk.2.transfer with
    | condGoto cond lt lf md =>
      have := coreCFGToGotoBlockStep_nextLoc_advance_condGoto fname lblBlk st st'
        cond lt lf md h_t h_admitted h_run
      rw [this]; omega
    | finish md =>
      have := coreCFGToGotoBlockStep_nextLoc_advance_finish fname lblBlk st st'
        md h_t h_admitted h_run
      rw [this]; omega
  refine ⟨?_, ?_⟩
  · -- bound preservation.
    intro l pc h_at
    rw [h_lbl] at h_at
    rw [Std.HashMap.getElem?_insert] at h_at
    by_cases h_eq : lblBlk.1 = l
    · simp [h_eq] at h_at
      omega
    · have : ¬ lblBlk.1 = l := h_eq
      simp [this] at h_at
      have h_pc_lt_old := h_bound l pc h_at
      omega
  · -- injectivity preservation.
    intro l₁ l₂ pc h₁ h₂
    rw [h_lbl] at h₁ h₂
    rw [Std.HashMap.getElem?_insert] at h₁ h₂
    by_cases h_eq₁ : lblBlk.1 = l₁
    · by_cases h_eq₂ : lblBlk.1 = l₂
      · rw [← h_eq₁, ← h_eq₂]
      · -- l₁ = lblBlk.1, l₂ ≠ lblBlk.1.
        simp [h_eq₁] at h₁
        have h_neq₂ : ¬ lblBlk.1 = l₂ := h_eq₂
        simp [h_neq₂] at h₂
        -- h₁: pc = st.trans.nextLoc. h₂: st.labelMap[l₂]? = some pc, with pc < st.trans.nextLoc.
        have h_pc_lt := h_bound l₂ pc h₂
        subst h₁
        omega
    · by_cases h_eq₂ : lblBlk.1 = l₂
      · -- Symmetric.
        have h_neq₁ : ¬ lblBlk.1 = l₁ := h_eq₁
        simp [h_neq₁] at h₁
        simp [h_eq₂] at h₂
        have h_pc_lt := h_bound l₁ pc h₁
        subst h₂
        omega
      · -- Neither = lblBlk.1; both come from old map.
        have h_neq₁ : ¬ lblBlk.1 = l₁ := h_eq₁
        have h_neq₂ : ¬ lblBlk.1 = l₂ := h_eq₂
        simp [h_neq₁] at h₁
        simp [h_neq₂] at h₂
        exact h_inj l₁ l₂ pc h₁ h₂

/-- The blocks-fold preserves `labelMapBoundedAndInj`. -/
theorem blocksFoldlM_preserves_labelMapBoundedAndInj
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_inv : labelMapBoundedAndInj st.labelMap st.trans.nextLoc) :
    labelMapBoundedAndInj st'.labelMap st'.trans.nextLoc := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_inv
  | cons hd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st hd with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ hd.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted hd (by simp)
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have h_inv₁ : labelMapBoundedAndInj st₁.labelMap st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_labelMapBoundedAndInj fname hd st st₁
          h_admitted_head h_step h_inv
      exact ih st₁ h_admitted_rest h_run h_inv₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- Closure for `labelMap_inj`. Distinct CFG block labels map to
distinct pcs in the post-blocks-fold state, by way of the invariant
`labelMapBoundedAndInj`. -/
theorem labelMap_inj_of_translator
    (cfg : Core.DetCFG)
    (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true) :
    ∀ (st_final : Strata.CoreCFGTransLoopState),
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀) = Except.ok st_final →
    ∀ l₁ l₂ pc,
      hashMapToLabelMap st_final.labelMap l₁ = some pc →
      hashMapToLabelMap st_final.labelMap l₂ = some pc →
      l₁ = l₂ := by
  intro st_final h_blocks_run l₁ l₂ pc h₁ h₂
  -- Apply the foldlM lift with the empty initial labelMap invariant.
  have h_admitted_st :
      ∀ lblBlk ∈ cfg.blocks, ∀ c ∈ lblBlk.2.cmds,
        Core.CmdExt.isAdmittedCmd c = true :=
    fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb
  have h_inv₀ :
      labelMapBoundedAndInj (coreCFGToGotoInitState trans₀).labelMap
        (coreCFGToGotoInitState trans₀).trans.nextLoc := by
    simp [coreCFGToGotoInitState]
    exact labelMapBoundedAndInj_empty trans₀.nextLoc
  obtain ⟨_, h_inj⟩ :=
    blocksFoldlM_preserves_labelMapBoundedAndInj functionName cfg.blocks
      _ st_final h_admitted_st h_blocks_run h_inv₀
  -- Convert hashMapToLabelMap form to st_final.labelMap[?]? form.
  exact h_inj l₁ l₂ pc h₁ h₂

/-! ### Helpers for `layout_block_body_of_translator`

The closure proceeds in three layers:

1. **Equivalence**: `cmdsFoldlM_eq_innerCmdLoop_on_admitted` — on
   admitted commands, `cmdsFoldlM coreCFGToGotoCmdStep trans = ok ans`
   iff `innerCmdLoop trans.T fname cmds trans = ok ans`. This lets us
   reuse `innerCmdLoop_layout_block_body` directly.

2. **Per-block extraction**: `coreCFGToGotoBlockStep_layout_block_body`
   — for a successful per-block step, the body cmds emit at
   `pre_step_nextLoc + 1 + cmdsPrefixInstrCount blk.cmds k` in the
   post-step `st'.trans`.

3. **Outer-fold lift**: `blocksFoldlM_layout_block_body` — for each
   `(l, blk) ∈ cfg.blocks`, the layout extends to `st_final.trans`.

4. **Patcher bridge**: combine with `patchGotoTargets_preserves_*` to
   move from `st_final.trans.instructions` to `ans.instructions`. -/

/-- `cmdsFoldlM` and `innerCmdLoop` produce the same `ans` on the
admitted-commands fragment. The first iteration's `T` argument to
`innerCmdLoop` is `trans.T`; subsequent iterations thread `trans'.T`
matching `coreCFGToGotoCmdStep`'s `trans.T` lookup. -/
theorem cmdsFoldlM_eq_innerCmdLoop_on_admitted
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans) :
    innerCmdLoop trans.T fname cmds trans = Except.ok ans := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run
    rw [innerCmdLoop_nil]
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_cmd := h_admitted cmd (by simp)
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      cases cmd with
      | cmd c =>
        rw [coreCFGToGotoCmdStep_cmd] at h_step
        unfold innerCmdLoop
        simp only [h_step, Except.mapError, Bind.bind, Except.bind]
        exact ih trans' h_admitted_rest h_run
      | call _ _ _ =>
        simp [Core.CmdExt.isAdmittedCmd] at h_admitted_cmd
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- Per-block step layout-extraction. For a block step that succeeds,
each admitted command in `blk.cmds` is emitted at the right offset in
`st'.trans.instructions`. -/
theorem coreCFGToGotoBlockStep_layout_block_body
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_tx_eq :
      ∀ e : Core.Expression.Expr,
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
          = Except.ok (h_expr_corr.tx e))
    (h_prefix :
      ∀ (k : Nat) (h : k < st'.trans.instructions.size),
        pgm.instructions[k]? = some st'.trans.instructions[k]) :
    ∀ (k : Nat) (inner : Imperative.Cmd Core.Expression)
      (h : k < lblBlk.2.cmds.length),
      lblBlk.2.cmds[k]'h = .cmd inner →
      CmdEmittedAt δ δ_goto δ_goto_bool pgm
        (st.trans.nextLoc + 1 + cmdsPrefixInstrCount lblBlk.2.cmds k) inner := by
  obtain ⟨label, blk⟩ := lblBlk
  -- Unfold the block step.
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    -- Step 1: extract size-eq for trans₂ via cmdsFoldlM_preserves_size_eq.
    have h_size_after_label :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname } st.trans).instructions.size =
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname } st.trans).nextLoc :=
      emitLabel_preserves_size_eq label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans h_size
    -- Step 2: convert cmdsFoldlM to innerCmdLoop on the admitted fragment.
    have h_inner_cmd :
        innerCmdLoop
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname } st.trans).T
          fname blk.cmds
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname } st.trans)
        = Except.ok trans₂ :=
      cmdsFoldlM_eq_innerCmdLoop_on_admitted fname blk.cmds _ trans₂ h_admitted h_inner
    -- Step 3: extract h_prefix' for trans₂. We need
    -- ∀ k h, pgm.instructions[k]? = some trans₂.instructions[k].
    -- This requires a chain: trans₂.size ≤ st'.size, then the trans₂-prefix
    -- extends through transfer-emit + outer.
    have h_size_le_st' : trans₂.instructions.size ≤ st'.trans.instructions.size := by
      cases h_t : blk.transfer with
      | condGoto cond lt lf md =>
        rw [h_t] at h_run
        simp only at h_run
        generalize h_cond_eval :
            Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond
              = cond_eval at h_run
        match cond_eval, h_cond_eval with
        | .ok cond_expr, _ =>
          simp only at h_run
          injection h_run with h_run
          rw [← h_run]
          simp [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto, Array.size_push]
          omega
        | .error _, _ => simp at h_run
      | finish md =>
        rw [h_t] at h_run
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        simp [Array.size_push]
    have h_trans₂_prefix :
        ∀ (k : Nat) (h : k < trans₂.instructions.size),
          st'.trans.instructions[k]? = some trans₂.instructions[k] := by
      intro k h_k
      -- Use the existing cmdsFoldlM_instructions_prefix? + the
      -- already-proven block-step prefix lemma. The block step's
      -- post-state has instructions extending trans₂'s instructions.
      have h_size_le_eq : trans₂.instructions.size ≤ st'.trans.instructions.size :=
        h_size_le_st'
      have h_k' : k < st'.trans.instructions.size := Nat.lt_of_lt_of_le h_k h_size_le_eq
      -- We need the prefix-? on st'.trans. Since the block step only pushes
      -- 1 or 2 transfer instructions on top of trans₂, the prefix relation
      -- holds at all k < trans₂.instructions.size.
      have h_eq : st'.trans.instructions[k]? = trans₂.instructions[k]? := by
        cases h_t : blk.transfer with
        | condGoto cond lt lf md =>
          rw [h_t] at h_run
          simp only at h_run
          generalize h_cond_eval :
              Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond
                = cond_eval at h_run
          match cond_eval, h_cond_eval with
          | .ok cond_expr, _ =>
            simp only at h_run
            injection h_run with h_run
            rw [← h_run]
            simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
            -- Goal: ((trans₂.instructions.push i₁).push i₂)[k]? = trans₂.instructions[k]?.
            -- Apply outer push (size grows by 1; k still in range).
            have h_k_post_first :
                k < (trans₂.instructions.push
                  ({ type := .GOTO, guard := cond_expr.not,
                     sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                     locationNum := trans₂.nextLoc } : CProverGOTO.Instruction)).size := by
              rw [Array.size_push]; exact Nat.lt_succ_of_lt h_k
            rw [Array.getElem?_push_lt h_k_post_first]
            -- Goal: some (trans₂.instructions.push inst1)[k] = trans₂.instructions[k]?
            rw [Array.getElem_push_lt h_k]
            rw [Array.getElem?_eq_getElem h_k]
          | .error _, _ => simp at h_run
        | finish md =>
          rw [h_t] at h_run
          simp only at h_run
          injection h_run with h_run
          rw [← h_run]
          rw [Array.getElem?_push_lt h_k]
          rw [Array.getElem?_eq_getElem h_k]
      rw [h_eq]
      exact Array.getElem?_eq_getElem h_k
    have h_prefix_trans₂ :
        ∀ (k : Nat) (h : k < trans₂.instructions.size),
          pgm.instructions[k]? = some trans₂.instructions[k] := by
      intro k h_k
      have h_k' : k < st'.trans.instructions.size := Nat.lt_of_lt_of_le h_k h_size_le_st'
      rw [h_prefix k h_k']
      have h_eq := h_trans₂_prefix k h_k
      rw [Array.getElem?_eq_getElem h_k'] at h_eq
      injection h_eq with h_eq
      rw [h_eq]
    -- Step 4: now apply innerCmdLoop_layout_block_body.
    intro k inner h_lt h_at
    have h_admitted_indexed :
        ∀ (k : Nat) (h : k < blk.cmds.length),
          Core.CmdExt.isAdmittedCmd (blk.cmds[k]'h) = true := by
      intro k h_k
      exact h_admitted blk.cmds[k] (List.getElem_mem _)
    have h_layout :=
      innerCmdLoop_layout_block_body
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname } st.trans).T
        fname blk.cmds
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname } st.trans)
        trans₂ h_inner_cmd h_size_after_label
        pgm δ δ_goto δ_goto_bool h_expr_corr h_tx_eq h_admitted_indexed
        h_prefix_trans₂ k inner h_lt h_at
    -- The offset in h_layout is
    -- (emitLabel ...).nextLoc + cmdsPrefixInstrCount blk.cmds k
    -- = (st.trans.nextLoc + 1) + cmdsPrefixInstrCount blk.cmds k
    -- = st.trans.nextLoc + 1 + cmdsPrefixInstrCount blk.cmds k.
    have h_after_label_nextLoc :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname } st.trans).nextLoc =
        st.trans.nextLoc + 1 := rfl
    rw [h_after_label_nextLoc] at h_layout
    exact h_layout
  | .error _, _ => simp at h_run

/-- The blocks-fold extends `coreCFGToGotoBlockStep_layout_block_body`
to the outer fold. For each `(l, blk) ∈ blocks` such that the foldlM
produces `st_final`, the body of `blk` is emitted at the right
offsets relative to `st_final.labelMap[l]?`. -/
theorem blocksFoldlM_layout_block_body
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_distinct : BlockLabelsDistinct blocks)
    (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_tx_eq :
      ∀ e : Core.Expression.Expr,
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
          = Except.ok (h_expr_corr.tx e))
    (h_prefix :
      ∀ (k : Nat) (h : k < st'.trans.instructions.size),
        pgm.instructions[k]? = some st'.trans.instructions[k]) :
    ∀ l blk pc, (l, blk) ∈ blocks →
      st'.labelMap[l]? = some pc →
    ∀ k inner,
      (h : k < blk.cmds.length) →
      blk.cmds[k]'h = .cmd inner →
      CmdEmittedAt δ δ_goto δ_goto_bool pgm
        (pc + 1 + cmdsPrefixInstrCount blk.cmds k) inner := by
  induction blocks generalizing st with
  | nil =>
    intro l blk pc h_in
    simp at h_in
  | cons hd rest ih =>
    intro l blk pc h_in h_lookup k inner h_lt h_at
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st hd with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ hd.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted hd (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname hd st st₁ h_admitted_head h_step h_size
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have h_distinct_rest : BlockLabelsDistinct rest :=
        BlockLabelsDistinct_tail hd rest h_distinct
      have h_le_st' : st₁.trans.instructions.size ≤ st'.trans.instructions.size :=
        blocksFoldlM_size_le fname rest st₁ st' h_admitted_rest h_run
      -- h_prefix on st'.trans, transferred to st₁.trans:
      have h_prefix₁ :
          ∀ (k : Nat) (h : k < st₁.trans.instructions.size),
            pgm.instructions[k]? = some st₁.trans.instructions[k] := by
        intro k h_k
        have h_k' : k < st'.trans.instructions.size := Nat.lt_of_lt_of_le h_k h_le_st'
        rw [h_prefix k h_k']
        have h_eq :=
          blocksFoldlM_instructions_prefix? fname rest st₁ st' h_admitted_rest h_run k h_k
        rw [Array.getElem?_eq_getElem h_k'] at h_eq
        rw [Array.getElem?_eq_getElem h_k] at h_eq
        injection h_eq with h_eq
        rw [h_eq]
      -- Either (l, blk) = hd, or (l, blk) ∈ rest.
      rw [List.mem_cons] at h_in
      rcases h_in with h_eq | h_in_rest
      · -- (l, blk) = hd. Extract the layout from the head step.
        subst h_eq
        -- The labelMap entry for hd.1 = l in st₁ is st.trans.nextLoc.
        have h_lbl₁ : st₁.labelMap = st.labelMap.insert l st.trans.nextLoc :=
          coreCFGToGotoBlockStep_labelMap fname (l, blk) st st₁ h_step
        have h_head_not_in_rest : ∀ p ∈ rest, p.1 ≠ l := by
          intro p hp h_p_eq
          have : l ≠ p.1 := BlockLabelsDistinct_head_neq_tail (l, blk) rest h_distinct p hp
          exact this h_p_eq.symm
        have h_lbl_st' :
            st'.labelMap[l]? = st₁.labelMap[l]? :=
          blocksFoldlM_labelMap_preserves_external fname rest st₁ st' h_admitted_rest
            h_run l h_head_not_in_rest
        rw [h_lbl_st'] at h_lookup
        rw [h_lbl₁] at h_lookup
        rw [Std.HashMap.getElem?_insert] at h_lookup
        simp at h_lookup
        -- h_lookup : pc = st.trans.nextLoc.
        subst h_lookup
        -- Apply per-block layout extraction with prefix h_prefix₁.
        exact coreCFGToGotoBlockStep_layout_block_body fname (l, blk) st st₁
          h_admitted_head h_step h_size pgm δ δ_goto δ_goto_bool h_expr_corr h_tx_eq
          h_prefix₁ k inner h_lt h_at
      · -- (l, blk) ∈ rest. Apply IH.
        exact ih st₁ h_admitted_rest h_run h_size₁ h_distinct_rest
          l blk pc h_in_rest h_lookup k inner h_lt h_at
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Patcher preserves full instruction except target

The patcher only writes the `target` field. Hence every other field
(`type`, `guard`, `code`, `locationNum`, `sourceLoc`, `labels`) is
preserved at any index.

For `layout_block_body_of_translator`, we need to lift `CmdEmittedAt`
over the body cmds from `st_final.trans` to `ans` (the patched
output). Since `CmdEmittedAt` constructors check only `type`, `guard`,
`code` (not `target`), the lift via this lemma works straight
through. -/

/-- A single patch step preserves the non-target fields. -/
private theorem patch_one_preserves_full_except_target
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (i : Nat) (instr : CProverGOTO.Instruction)
    (h : (a.set! idx { a[idx]! with target := some tgt })[i]? = some instr) :
    ∃ instr_pre,
      a[i]? = some instr_pre ∧
      instr.type = instr_pre.type ∧
      instr.guard = instr_pre.guard ∧
      instr.code = instr_pre.code ∧
      instr.locationNum = instr_pre.locationNum := by
  rw [Array.set!_eq_setIfInBounds] at h
  by_cases h_idx : idx < a.size
  · by_cases h_eq : i = idx
    · subst h_eq
      have h_lt_set :
          i < (a.setIfInBounds i { a[i]! with target := some tgt }).size := by
        simp [h_idx]
      rw [Array.getElem?_eq_getElem h_lt_set] at h
      rw [Array.getElem_setIfInBounds_self] at h
      injection h with h
      have h_at : a[i]? = some a[i] := Array.getElem?_eq_getElem h_idx
      refine ⟨a[i], h_at, ?_, ?_, ?_, ?_⟩ <;>
        (have h_getD : a[i]! = a[i] := getElem!_pos a i h_idx
         rw [← h]
         simp [h_getD])
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm h_eq)] at h
      exact ⟨instr, h, rfl, rfl, rfl, rfl⟩
  · rw [Array.setIfInBounds_eq_of_size_le (Nat.le_of_not_lt h_idx)] at h
    exact ⟨instr, h, rfl, rfl, rfl, rfl⟩

/-- `patchGotoTargets` preserves the non-target fields at any
in-bounds index — the patcher only writes the `target` field. -/
theorem patchGotoTargets_preserves_full_except_target
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (patches : List (Nat × Nat))
    (i : Nat) (instr : CProverGOTO.Instruction)
    (h : (Imperative.patchGotoTargets trans patches).instructions[i]? = some instr) :
    ∃ instr_pre,
      trans.instructions[i]? = some instr_pre ∧
      instr.type = instr_pre.type ∧
      instr.guard = instr_pre.guard ∧
      instr.code = instr_pre.code ∧
      instr.locationNum = instr_pre.locationNum := by
  unfold Imperative.patchGotoTargets at h
  simp only at h
  have hgen :
      ∀ (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat))
        (i : Nat) (instr : CProverGOTO.Instruction),
        (List.foldl
          (fun acc (p : Nat × Nat) =>
            acc.set! p.fst { acc[p.fst]! with target := some p.snd })
          a ps)[i]? = some instr →
        ∃ instr_pre, a[i]? = some instr_pre ∧
          instr.type = instr_pre.type ∧
          instr.guard = instr_pre.guard ∧
          instr.code = instr_pre.code ∧
          instr.locationNum = instr_pre.locationNum := by
    intro a ps i instr h
    induction ps generalizing a with
    | nil =>
      simp at h
      exact ⟨instr, h, rfl, rfl, rfl, rfl⟩
    | cons p ps ih =>
      simp only [List.foldl] at h
      obtain ⟨instr_after_first, h_after_first, h_ty_after, h_g_after, h_c_after, h_l_after⟩ := ih _ h
      obtain ⟨instr_pre, h_pre, h_ty_pre, h_g_pre, h_c_pre, h_l_pre⟩ :=
        patch_one_preserves_full_except_target a p.1 p.2 i instr_after_first h_after_first
      refine ⟨instr_pre, h_pre, ?_, ?_, ?_, ?_⟩
      · exact h_ty_after.trans h_ty_pre
      · exact h_g_after.trans h_g_pre
      · exact h_c_after.trans h_c_pre
      · exact h_l_after.trans h_l_pre
  exact hgen _ _ _ _ h

/-- Closure for `layout_block_body`. Given the per-block-body layout
on `st_final.trans.instructions` (from `blocksFoldlM_layout_block_body`),
lift to `ans.instructions` via `patchGotoTargets_preserves_full_except_target`.
Only `type`, `guard`, `code` fields matter for `CmdEmittedAt`, all of
which are preserved by the patcher. -/
theorem layout_block_body_of_translator
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_distinct : BlockLabelsDistinct cfg.blocks)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_tx_eq :
      ∀ e : Core.Expression.Expr,
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
          = Except.ok (h_expr_corr.tx e)) :
    ∀ (st_final : Strata.CoreCFGTransLoopState),
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀) = Except.ok st_final →
    ∀ l blk pc, (l, blk) ∈ cfg.blocks →
      hashMapToLabelMap st_final.labelMap l = some pc →
    ∀ k inner,
      (h : k < blk.cmds.length) →
      blk.cmds[k]'h = .cmd inner →
      CmdEmittedAt δ δ_goto δ_goto_bool
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        (pc + 1 + cmdsPrefixInstrCount blk.cmds k)
        inner := by
  intro st_final h_blocks_run l blk pc h_in h_lookup k inner h_lt h_at
  -- Decompose the translator output to bridge st_final.trans to ans.
  obtain ⟨st_final', resolved, trans_post, h_blocks_run', h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  -- The decomposition gives a (potentially different) st_final'. Show they agree.
  have h_st_eq : st_final = st_final' := by
    rw [h_blocks_run] at h_blocks_run'
    exact Except.ok.inj h_blocks_run'
  subst h_st_eq
  -- patches preserve trans (loopContracts empty).
  have h_lc_empty := h_loopContracts_empty_post st_final h_blocks_run
  rw [h_lc_empty] at h_patches_run
  have h_trans_post_eq : trans_post = st_final.trans :=
    patchesFoldlM_no_contracts_trans_eq st_final.labelMap st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
  have h_ans_eq' : ans = Imperative.patchGotoTargets st_final.trans resolved := by
    rw [h_ans_eq, h_trans_post_eq]
  -- Apply the per-block-body extraction on st_final.trans first.
  -- We need a pgm with instructions = st_final.trans.instructions and the trivial prefix.
  let pgm_st : Program :=
    { name := "", parameterIdentifiers := #[],
      instructions := st_final.trans.instructions }
  have h_admitted_st :
      ∀ lblBlk ∈ cfg.blocks, ∀ c ∈ lblBlk.2.cmds,
        Core.CmdExt.isAdmittedCmd c = true :=
    fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb
  have h_init_size_st :
      (coreCFGToGotoInitState trans₀).trans.instructions.size =
        (coreCFGToGotoInitState trans₀).trans.nextLoc := by
    simp [coreCFGToGotoInitState]; exact h_init_size
  have h_lookup_st : st_final.labelMap[l]? = some pc := h_lookup
  have h_prefix_trivial :
      ∀ (k : Nat) (h : k < st_final.trans.instructions.size),
        pgm_st.instructions[k]? = some st_final.trans.instructions[k] := by
    intro k h_k
    show st_final.trans.instructions[k]? = some st_final.trans.instructions[k]
    exact Array.getElem?_eq_getElem h_k
  have h_emit_st :=
    blocksFoldlM_layout_block_body functionName cfg.blocks _ st_final
      h_admitted_st h_blocks_run h_init_size_st h_distinct
      pgm_st δ δ_goto δ_goto_bool h_expr_corr h_tx_eq h_prefix_trivial
      l blk pc h_in h_lookup_st k inner h_lt h_at
  -- Now bridge from pgm_st (over st_final.trans) to the goal (over ans).
  -- The trick: CmdEmittedAt only checks type/guard/code, all preserved by patchGotoTargets.
  -- We do a case analysis on h_emit_st's constructor and rebuild over ans.
  -- The patcher preservation:
  have h_preserves :
      ∀ (idx : Nat) (instr_ans : CProverGOTO.Instruction),
        ans.instructions[idx]? = some instr_ans →
        ∃ instr_st, st_final.trans.instructions[idx]? = some instr_st ∧
          instr_ans.type = instr_st.type ∧
          instr_ans.guard = instr_st.guard ∧
          instr_ans.code = instr_st.code ∧
          instr_ans.locationNum = instr_st.locationNum := by
    intro idx instr_ans h_at_ans
    rw [h_ans_eq'] at h_at_ans
    exact patchGotoTargets_preserves_full_except_target st_final.trans resolved idx instr_ans h_at_ans
  -- Reverse direction: at any in-bounds idx of st_final.trans, ans has SOME instruction
  -- with the same type/code/guard/locationNum.
  have h_size_eq : ans.instructions.size = st_final.trans.instructions.size := by
    rw [h_ans_eq']
    exact patchGotoTargets_preserves_size st_final.trans resolved
  have h_st_to_ans :
      ∀ (idx : Nat) (instr_st : CProverGOTO.Instruction),
        st_final.trans.instructions[idx]? = some instr_st →
        ∃ instr_ans, ans.instructions[idx]? = some instr_ans ∧
          instr_ans.type = instr_st.type ∧
          instr_ans.guard = instr_st.guard ∧
          instr_ans.code = instr_st.code := by
    intro idx instr_st h_at_st
    have h_idx_lt : idx < st_final.trans.instructions.size :=
      (Array.getElem?_eq_some_iff.mp h_at_st).1
    have h_idx_lt_ans : idx < ans.instructions.size := by rw [h_size_eq]; exact h_idx_lt
    have h_at_ans : ans.instructions[idx]? = some ans.instructions[idx] :=
      Array.getElem?_eq_getElem h_idx_lt_ans
    obtain ⟨instr_st', h_at_st', h_ty, h_g, h_c, _⟩ :=
      h_preserves idx ans.instructions[idx] h_at_ans
    rw [h_at_st'] at h_at_st
    injection h_at_st with h_st_eq
    refine ⟨ans.instructions[idx], h_at_ans, ?_, ?_, ?_⟩ <;>
      simp [h_ty, h_g, h_c, h_st_eq]
  -- Now case-split on h_emit_st and rebuild each constructor over ans.
  -- This is mechanical: each constructor's hypotheses need to be rebuilt by replacing
  -- pgm_st-instructions with ans-instructions while preserving type/code/guard.
  -- The constructor's pc arg is unified with the relation's pc, so cases
  -- doesn't bind a fresh name for it.
  cases h_emit_st with
  | init_det v ty e_core md i_decl i_assn h_decl_at h_decl_ty h_assn_at h_assn_ty
              e_goto gty h_decl_code h_assn_code h_translated =>
    obtain ⟨i_decl', h_at_decl', h_ty_decl', _, h_c_decl'⟩ :=
      h_st_to_ans _ i_decl h_decl_at
    obtain ⟨i_assn', h_at_assn', h_ty_assn', _, h_c_assn'⟩ :=
      h_st_to_ans _ i_assn h_assn_at
    refine CmdEmittedAt.init_det _ v ty e_core md i_decl' i_assn'
      h_at_decl' (h_ty_decl'.trans h_decl_ty)
      h_at_assn' (h_ty_assn'.trans h_assn_ty)
      e_goto gty ?_ ?_ h_translated
    · rw [h_c_decl']; exact h_decl_code
    · rw [h_c_assn']; exact h_assn_code
  | init_nondet v ty md i_decl h_decl_at h_decl_ty gty h_decl_code =>
    obtain ⟨i_decl', h_at_decl', h_ty_decl', _, h_c_decl'⟩ :=
      h_st_to_ans _ i_decl h_decl_at
    refine CmdEmittedAt.init_nondet _ v ty md i_decl' h_at_decl'
      (h_ty_decl'.trans h_decl_ty) gty ?_
    rw [h_c_decl']; exact h_decl_code
  | set_det v e_core md i_assn h_assn_at h_assn_ty e_goto gty h_assn_code h_translated =>
    obtain ⟨i_assn', h_at_assn', h_ty_assn', _, h_c_assn'⟩ :=
      h_st_to_ans _ i_assn h_assn_at
    refine CmdEmittedAt.set_det _ v e_core md i_assn'
      h_at_assn' (h_ty_assn'.trans h_assn_ty)
      e_goto gty ?_ h_translated
    rw [h_c_assn']; exact h_assn_code
  | set_nondet v md i_assn h_assn_at h_assn_ty gty h_assn_code =>
    obtain ⟨i_assn', h_at_assn', h_ty_assn', _, h_c_assn'⟩ :=
      h_st_to_ans _ i_assn h_assn_at
    obtain ⟨e_nondet, h_assn_code_eq, h_id, h_ty_e⟩ := h_assn_code
    refine CmdEmittedAt.set_nondet _ v md i_assn'
      h_at_assn' (h_ty_assn'.trans h_assn_ty) gty
      ⟨e_nondet, ?_, h_id, h_ty_e⟩
    rw [h_c_assn']; exact h_assn_code_eq
  | assert_emit label e_core md i h_at_st h_ty e_goto h_guard h_translated =>
    obtain ⟨i', h_at', h_ty', h_g', _⟩ := h_st_to_ans _ i h_at_st
    refine CmdEmittedAt.assert_emit _ label e_core md i' h_at' (h_ty'.trans h_ty)
      e_goto ?_ h_translated
    rw [h_g']; exact h_guard
  | assume_emit label e_core md i h_at_st h_ty e_goto h_guard h_translated =>
    obtain ⟨i', h_at', h_ty', h_g', _⟩ := h_st_to_ans _ i h_at_st
    refine CmdEmittedAt.assume_emit _ label e_core md i' h_at' (h_ty'.trans h_ty)
      e_goto ?_ h_translated
    rw [h_g']; exact h_guard
  | cover_emit label e_core md i h_at_st h_ty e_goto h_guard h_translated =>
    obtain ⟨i', h_at', h_ty', h_g', _⟩ := h_st_to_ans _ i h_at_st
    refine CmdEmittedAt.cover_emit _ label e_core md i' h_at' (h_ty'.trans h_ty)
      e_goto ?_ h_translated
    rw [h_g']; exact h_guard


end -- public section

end CProverGOTO
