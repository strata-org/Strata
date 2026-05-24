/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOInvariants
public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline
public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOCorrect
public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF.Shape
public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF.Preservation
public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF.StepPreservation
public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF.FoldAndDecompose
import all Strata.DL.Imperative.ToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline

/-! # Discharging `WellFormedTranslation` against `coreCFGToGotoTransform`

This module proves that the program output by
`Strata.coreCFGToGotoTransform` (composed with
`procedureToGotoCtxViaCFG`) satisfies the `WellFormedTranslation`
predicate consumed by `CProverGOTO.coreCFGToGoto_forward_simulation`.

The file is organised in three layers:

1. **Per-`Cmd` shape lemmas** (`Cmd_toGotoInstructions_*_ok`): for each
   constructor of `Imperative.Cmd Core.Expression` (in the admitted
   fragment), the resulting `GotoTransform` has a precisely-described
   `instructions` suffix appended and `nextLoc` advanced by exactly
   `Imperative.Cmd.gotoInstrCount`.

2. **Emit-helper shape lemmas** (`emitLabel_shape`, `emitCondGoto_shape`,
   `emitUncondGoto_shape`): one-liners characterising each helper's
   suffix.

3. **`patchGotoTargets` invariants**: the second pass mutates only the
   `target` field, so all type/guard/code/locationNum invariants
   transfer through patching unchanged.

These layers compose into `coreCFGToGotoTransform_wellFormed_nonempty`
and the strengthened `coreCFGToGotoTransform_wellFormed_strengthened`
at the bottom of the module.
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

/-! ## `layout_cond_goto` + guards closures

This section discharges:
* `layout_cond_goto` — every `.condGoto` block produces two GOTO
  instructions at the right pcs with the right targets *after patching*.
* `layout_cond_goto_guards` — those two GOTO instructions carry the
  expected guards (`e_goto.not` and `Expr.true`).

The crux is a **patcher post-condition** lemma
(`patchGotoTargets_target_at_patched_idx`): under unique-indices
patches, if `(idx, tgt) ∈ patches` and `idx < array.size`, then the
patched array at `idx` has `target = some tgt`.

Combined with a `pendingPatches`-tracking invariant and the fact that
every `.condGoto` per-block step pushes exactly two patches
(`(falseIdx, lf)` and `(trueIdx, lt)`) at strictly increasing indices,
we obtain `layout_cond_goto`. The guards lemma is mostly a
restatement of `coreCFGToGotoBlockStep_condGoto_at_pc` lifted across
the foldlM and through the patcher.
-/

/-! ### Patcher post-condition: `target` at patched indices

For an in-bounds index appearing in the patches list with a unique
first projection, `patchGotoTargets` stores `some tgt` at that index.

We work with two flavours:
* **`patchOne`** lemma: for a single patch `(idx, tgt)`, the result has
  `target = some tgt` at `idx` when `idx < array.size`.
* **Inductive lift** to `patchGotoTargets`, leveraging that any later
  patches don't touch `idx` (under uniqueness).
-/

/-- Single-patch post-condition: setting `target` via `set!` at an in-
bounds index produces `target = some tgt` at that index. -/
private theorem patch_one_target_eq
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (h_idx : idx < a.size) :
    (a.set! idx { a[idx]! with target := some tgt })[idx]?
      = some { a[idx]! with target := some tgt } := by
  rw [Array.set!_eq_setIfInBounds]
  have h_lt : idx < (a.setIfInBounds idx { a[idx]! with target := some tgt }).size := by
    simp [h_idx]
  rw [Array.getElem?_eq_getElem h_lt]
  rw [Array.getElem_setIfInBounds_self]

/-- The target of the result of a single-patch `set!` is `some tgt`. -/
private theorem patch_one_target
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (h_idx : idx < a.size) :
    ∃ instr,
      (a.set! idx { a[idx]! with target := some tgt })[idx]? = some instr ∧
      instr.target = some tgt := by
  refine ⟨{ a[idx]! with target := some tgt }, patch_one_target_eq a idx tgt h_idx, rfl⟩

/-- Single-patch preserves array size. -/
private theorem patch_one_preserves_size
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat) :
    (a.set! idx { a[idx]! with target := some tgt }).size = a.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

/-- The single-patch fold preserves array size. -/
private theorem patch_foldl_preserves_size
    (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat)) :
    (List.foldl
      (fun acc (p : Nat × Nat) =>
        acc.set! p.fst { acc[p.fst]! with target := some p.snd })
      a ps).size = a.size := by
  induction ps generalizing a with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl]
    rw [ih, patch_one_preserves_size]

/-- Single-patch preserves the value at any index different from the
patched one. -/
private theorem patch_one_other_index
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (i : Nat) (h_neq : i ≠ idx) :
    (a.set! idx { a[idx]! with target := some tgt })[i]? = a[i]? := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases h_idx : idx < a.size
  · -- in-bounds: setIfInBounds does the actual write at idx; getElem? at i ≠ idx is the same.
    exact Array.getElem?_setIfInBounds_ne h_neq.symm
  · -- out-of-bounds: setIfInBounds is a no-op.
    rw [Array.setIfInBounds_eq_of_size_le (Nat.le_of_not_lt h_idx)]

/-- The patcher's foldl preserves `target = some tgt` at `idx`,
provided no later patch in the list has first projection `idx`. -/
private theorem patch_foldl_target_preserved_when_idx_unique_in_tail
    (a : Array CProverGOTO.Instruction) (idx : Nat) (tgt : Nat)
    (ps : List (Nat × Nat))
    (h_target : ∃ instr, a[idx]? = some instr ∧ instr.target = some tgt)
    (h_tail_no_idx : ∀ p ∈ ps, p.1 ≠ idx) :
    ∃ instr,
      (List.foldl
        (fun acc (p : Nat × Nat) =>
          acc.set! p.fst { acc[p.fst]! with target := some p.snd })
        a ps)[idx]? = some instr ∧
      instr.target = some tgt := by
  induction ps generalizing a with
  | nil => exact h_target
  | cons p rest ih =>
    simp only [List.foldl]
    have h_p_neq : p.1 ≠ idx := h_tail_no_idx p (by simp)
    have h_rest_neq : ∀ q ∈ rest, q.1 ≠ idx := fun q hq => h_tail_no_idx q (by simp [hq])
    apply ih
    · obtain ⟨instr, h_at, h_tgt⟩ := h_target
      have h_neq : idx ≠ p.1 := Ne.symm h_p_neq
      rw [patch_one_other_index a p.1 p.2 idx h_neq]
      exact ⟨instr, h_at, h_tgt⟩
    · exact h_rest_neq

/-- Patches with the form `(idx, tgt) :: rest`, where `rest` doesn't
contain `idx` as a first projection: after the foldl, the result at
`idx` has `target = some tgt`, provided `idx < array.size`. -/
private theorem patch_foldl_target_head
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (rest : List (Nat × Nat))
    (h_idx : idx < a.size)
    (h_rest_no_idx : ∀ p ∈ rest, p.1 ≠ idx) :
    ∃ instr,
      (List.foldl
        (fun acc (p : Nat × Nat) =>
          acc.set! p.fst { acc[p.fst]! with target := some p.snd })
        a ((idx, tgt) :: rest))[idx]? = some instr ∧
      instr.target = some tgt := by
  simp only [List.foldl]
  obtain ⟨instr, h_at, h_tgt⟩ := patch_one_target a idx tgt h_idx
  exact patch_foldl_target_preserved_when_idx_unique_in_tail
    (a.set! idx { a[idx]! with target := some tgt }) idx tgt rest
    ⟨instr, h_at, h_tgt⟩ h_rest_no_idx

/-- General patcher post-condition: if `(idx, tgt)` is in the patches
list with no later element sharing the same first projection, and
`idx < array.size`, then the patched array at `idx` has
`target = some tgt`. -/
private theorem patch_foldl_target_at_idx_when_last
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (ps : List (Nat × Nat))
    (h_in : ∃ pre suf, ps = pre ++ (idx, tgt) :: suf ∧
        (∀ p ∈ suf, p.1 ≠ idx))
    (h_idx : idx < a.size) :
    ∃ instr,
      (List.foldl
        (fun acc (p : Nat × Nat) =>
          acc.set! p.fst { acc[p.fst]! with target := some p.snd })
        a ps)[idx]? = some instr ∧
      instr.target = some tgt := by
  obtain ⟨pre, suf, h_eq, h_suf_no_idx⟩ := h_in
  rw [h_eq]
  rw [List.foldl_append]
  -- After processing pre, we get some array b with b.size = a.size.
  have h_b_size :
      (List.foldl
        (fun acc (p : Nat × Nat) =>
          acc.set! p.fst { acc[p.fst]! with target := some p.snd }) a pre).size = a.size :=
    patch_foldl_preserves_size a pre
  have h_idx_b :
      idx <
      (List.foldl
        (fun acc (p : Nat × Nat) =>
          acc.set! p.fst { acc[p.fst]! with target := some p.snd }) a pre).size := h_b_size ▸ h_idx
  -- Now apply patch_foldl_target_head with (idx, tgt) :: suf.
  exact patch_foldl_target_head _ idx tgt suf h_idx_b h_suf_no_idx

/-- The main patcher post-condition: under unique first-projections in
`patches`, every `(idx, tgt) ∈ patches` with `idx < trans.instructions.size`
gives `(patchGotoTargets trans patches).instructions[idx].target = some tgt`. -/
theorem patchGotoTargets_target_at_patched_idx
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (patches : List (Nat × Nat))
    (h_unique : List.Pairwise (fun a b => a.1 ≠ b.1) patches)
    (idx tgt : Nat)
    (h_in : (idx, tgt) ∈ patches)
    (h_idx : idx < trans.instructions.size) :
    ∃ instr,
      (Imperative.patchGotoTargets trans patches).instructions[idx]? = some instr ∧
      instr.target = some tgt := by
  unfold Imperative.patchGotoTargets
  simp only
  -- Split patches at (idx, tgt) and apply patch_foldl_target_at_idx_when_last.
  obtain ⟨pre, suf, h_eq⟩ := List.append_of_mem h_in
  have h_suf_no_idx : ∀ p ∈ suf, p.1 ≠ idx := by
    intro p hp
    -- (idx, tgt) appears in `pre ++ (idx, tgt) :: suf` BEFORE p ∈ suf.
    -- By Pairwise, (idx, tgt).1 ≠ p.1, i.e., idx ≠ p.1, so p.1 ≠ idx.
    rw [h_eq] at h_unique
    rw [List.pairwise_append] at h_unique
    obtain ⟨_, h_tail, _⟩ := h_unique
    rw [List.pairwise_cons] at h_tail
    obtain ⟨h_head, _⟩ := h_tail
    exact (h_head p hp).symm
  exact patch_foldl_target_at_idx_when_last trans.instructions idx tgt patches
    ⟨pre, suf, h_eq, h_suf_no_idx⟩ h_idx

/-! ### Tracking pendingPatches across the block fold

We track three properties of `pendingPatches` through `coreCFGToGotoBlockStep`:
* `IndicesDistinct`: all indices in `pendingPatches` are distinct.
* `IndicesBounded` (relative to `st`): all indices are
  < `st.trans.instructions.size`.
* For each `.condGoto` block at `pc`, the corresponding patches
  `(pc + 1 + bodyCount, lf)` and `(pc + 1 + bodyCount + 1, lt)` are
  members of `pendingPatches` after processing.
-/

/-- After the per-block step, the `pendingPatches` from input `st` are
preserved (via push for `.condGoto`, identity for `.finish`). -/
theorem coreCFGToGotoBlockStep_pendingPatches_preserves
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (p : Nat × String) (h_in : p ∈ st.pendingPatches) :
    p ∈ st'.pendingPatches := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, _ =>
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, _ =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        -- Goal: p ∈ ((st.pendingPatches.push (..., lf)).push (..., lt)).
        -- Reduce via Array.mem_push.
        simp only [Array.mem_push]
        left; left; exact h_in
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      exact h_in
  | .error _, _ => simp at h_run

/-- After the foldlM, `pendingPatches` from input state are preserved. -/
theorem blocksFoldlM_pendingPatches_preserves
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (p : Nat × String) (h_in : p ∈ st.pendingPatches) :
    p ∈ st'.pendingPatches := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_in
  | cons hd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st hd with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_in₁ : p ∈ st₁.pendingPatches :=
        coreCFGToGotoBlockStep_pendingPatches_preserves fname hd st st₁ h_step p h_in
      exact ih st₁ h_run h_in₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Patches-fold-correctness lemma

For each `(idx, label) ∈ pendingPatches`, after the patches foldlM
under empty `loopContracts`, the resolved patches list contains
`(idx, targetLoc)` where `targetLoc = labelMap[label]?`. -/

/-- Per-step under empty contracts: `(idx, targetLoc) :: oldResolved`. -/
theorem coreCFGToGotoPatchStep_no_contracts_resolvedPatches
    (labelMap : Std.HashMap String Nat)
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (targetLoc : Nat)
    (h_lookup : labelMap[idxLabel.2]? = some targetLoc)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap ∅ acc idxLabel = Except.ok acc') :
    acc'.1 = (idxLabel.1, targetLoc) :: acc.1 := by
  obtain ⟨resolvedPatches, trans⟩ := acc
  obtain ⟨idx, label⟩ := idxLabel
  unfold Strata.coreCFGToGotoPatchStep at h_run
  simp only [Bind.bind, Except.bind] at h_run
  rw [h_lookup] at h_run
  simp only [Std.HashMap.getElem?_empty] at h_run
  injection h_run with h_run
  rw [← h_run]

/-- Per-step under empty contracts: `acc.1 ⊆ acc'.1`. -/
theorem patchesFoldlM_no_contracts_step_subset
    (labelMap : Std.HashMap String Nat)
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap ∅ acc idxLabel = Except.ok acc') :
    ∀ p ∈ acc.1, p ∈ acc'.1 := by
  obtain ⟨resolvedPatches, trans⟩ := acc
  obtain ⟨idx, label⟩ := idxLabel
  unfold Strata.coreCFGToGotoPatchStep at h_run
  simp only [Bind.bind, Except.bind] at h_run
  cases h_lookup : labelMap[label]? with
  | none =>
    rw [h_lookup] at h_run
    simp at h_run
  | some targetLoc =>
    rw [h_lookup] at h_run
    simp only [Std.HashMap.getElem?_empty] at h_run
    injection h_run with h_run
    rw [← h_run]
    intro p h_p
    -- acc'.1 = (idx, targetLoc) :: resolvedPatches; old elements remain.
    simp only [List.mem_cons]
    right; exact h_p

/-- The patches foldlM only prepends to `resolvedPatches`. So input
elements are preserved in the output. -/
theorem patchesFoldlM_no_contracts_resolvedPatches_subset
    (labelMap : Std.HashMap String Nat)
    (patches : List (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc') :
    ∀ p ∈ acc.1, p ∈ acc'.1 := by
  induction patches generalizing acc with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact fun p h => h
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap ∅ acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      intro p h_p
      have h_acc₁ : ∀ p ∈ acc.1, p ∈ acc₁.1 :=
        patchesFoldlM_no_contracts_step_subset labelMap acc acc₁ head h_step
      have h_p_acc₁ : p ∈ acc₁.1 := h_acc₁ p h_p
      exact ih acc₁ h_run p h_p_acc₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- After the patches foldlM under empty contracts, every input
patch `(idx, label) ∈ pendingPatches` with a labelMap entry produces
a resolved patch in the output, AND the input resolvedPatches are
preserved. -/
theorem patchesFoldlM_no_contracts_resolvedPatches_mem
    (labelMap : Std.HashMap String Nat)
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc')
    (idx : Nat) (label : String) (targetLoc : Nat)
    (h_in : (idx, label) ∈ patches)
    (h_lookup : labelMap[label]? = some targetLoc) :
    (idx, targetLoc) ∈ acc'.1 := by
  rw [← Array.foldlM_toList] at h_run
  generalize h_eq : patches.toList = patchesL at h_run
  have h_in_list : (idx, label) ∈ patchesL := by
    rw [← h_eq]; exact (Array.mem_toList_iff).mpr h_in
  clear h_eq
  induction patchesL generalizing acc with
  | nil => simp at h_in_list
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap ∅ acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      rw [List.mem_cons] at h_in_list
      rcases h_in_list with h_eq | h_in_rest
      · -- (idx, label) is the head; this step puts (idx, targetLoc) :: acc.1 in acc₁.1.
        subst h_eq
        have h_acc₁ := coreCFGToGotoPatchStep_no_contracts_resolvedPatches
          labelMap acc acc₁ (idx, label) targetLoc h_lookup h_step
        -- Then (idx, targetLoc) ∈ acc'.1, since fold preserves all initial elements.
        have h_preserve : ∀ p ∈ acc₁.1, p ∈ acc'.1 :=
          patchesFoldlM_no_contracts_resolvedPatches_subset labelMap rest acc₁ acc' h_run
        apply h_preserve
        rw [h_acc₁]
        exact List.mem_cons_self
      · -- (idx, label) ∈ rest. Apply IH.
        exact ih acc₁ h_run h_in_rest
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### pendingPatches index distinctness

The `pendingPatches` indices grow strictly across blocks (each block
push at indices ≥ block's start). We track this to instantiate the
patcher's "pairwise-distinct first projections" hypothesis. -/

/-- pendingPatches index bound after block step (condGoto): two new
patches at indices `pc + 1 + bodyCount` and `+1`, both <
`st'.trans.instructions.size`. -/
theorem coreCFGToGotoBlockStep_pendingPatches_indices_bound
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_old_bound : ∀ p ∈ st.pendingPatches, p.1 < st.trans.instructions.size) :
    ∀ p ∈ st'.pendingPatches, p.1 < st'.trans.instructions.size := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      simp [Imperative.emitLabel, Array.size_push]
    have h_inner_size :
        trans₂.instructions.size = st.trans.instructions.size + 1 + DetBlockBodyInstrCount blk := by
      have h_size_after_label :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).instructions.size =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc :=
        emitLabel_preserves_size_eq label _ st.trans h_size
      have h_size_eq₂ : trans₂.instructions.size = trans₂.nextLoc :=
        cmdsFoldlM_preserves_size_eq fname blk.cmds _ trans₂ h_admitted h_inner h_size_after_label
      have h_advance₂ :
          trans₂.nextLoc =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc +
            blk.cmds.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 :=
        cmdsFoldlM_nextLoc_advance fname blk.cmds _ trans₂ h_admitted h_inner
      have h_after_label_nextLoc :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc = st.trans.nextLoc + 1 := rfl
      rw [h_size_eq₂, h_advance₂, h_after_label_nextLoc]
      simp [DetBlockBodyInstrCount, h_size]
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, _ =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        intro p h_p
        -- p in pushed array of two elements past st.pendingPatches.
        simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto] at h_p
        simp only [Array.mem_push] at h_p
        -- st'.trans.instructions.size = trans₂.instructions.size + 2 (after two pushes).
        -- Note: push order: first the cond-goto, then the uncond-goto.
        show p.1 < (((Imperative.emitUncondGoto _ ((Imperative.emitCondGoto _ _ trans₂).fst)).fst).instructions).size
        simp only [Imperative.emitUncondGoto, Imperative.emitCondGoto, Imperative.emitGoto, Array.size_push]
        -- After two pushes: size = trans₂.instructions.size + 2.
        rcases h_p with (h_p | h_p) | h_p
        · -- p ∈ st.pendingPatches; old bound + everything.
          have := h_old_bound p h_p
          have h_le : st.trans.instructions.size ≤ trans₂.instructions.size := by
            rw [h_inner_size]; omega
          omega
        · -- p = (trans₂.instructions.size, lf).
          subst h_p; simp; omega
        · -- p = (trans₂.instructions.push.size, lt) = (trans₂.instructions.size + 1, lt).
          subst h_p; simp [Array.size_push]
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      -- pendingPatches preserved; state's instructions.size grew by bodyCount + 1 (END).
      intro p h_p
      have := h_old_bound p h_p
      have h_le : st.trans.instructions.size ≤ st.trans.instructions.size + 1 + DetBlockBodyInstrCount blk + 1 := by
        omega
      -- Need st'.trans.instructions.size ≥ st.trans.instructions.size.
      show p.1 < ({ trans₂ with
        instructions := trans₂.instructions.push _,
        nextLoc := trans₂.nextLoc + 1 } : Imperative.GotoTransform Core.Expression.TyEnv).instructions.size
      simp [Array.size_push, h_inner_size]
      omega
  | .error _, _ => simp at h_run

/-- After the foldlM, all pendingPatches indices are bounded by
`st'.trans.instructions.size`. -/
theorem blocksFoldlM_pendingPatches_indices_bound
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_old_bound : ∀ p ∈ st.pendingPatches, p.1 < st.trans.instructions.size) :
    ∀ p ∈ st'.pendingPatches, p.1 < st'.trans.instructions.size := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_old_bound
  | cons hd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st hd with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ hd.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted hd (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname hd st st₁ h_admitted_head h_step h_size
      have h_bound₁ := coreCFGToGotoBlockStep_pendingPatches_indices_bound fname hd st st₁
        h_admitted_head h_step h_size h_old_bound
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      exact ih st₁ h_admitted_rest h_run h_size₁ h_bound₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The pendingPatches indices are pairwise distinct: any two distinct
elements have distinct first projections. We thread this through the
fold, given the input is distinct AND all input patches' indices are
strictly less than `st.trans.instructions.size`. -/
theorem coreCFGToGotoBlockStep_pendingPatches_indices_distinct
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_old_bound : ∀ p ∈ st.pendingPatches, p.1 < st.trans.instructions.size)
    (h_old_distinct :
      List.Pairwise (fun a b => a.1 ≠ b.1) st.pendingPatches.toList) :
    List.Pairwise (fun a b => a.1 ≠ b.1) st'.pendingPatches.toList := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      simp [Imperative.emitLabel, Array.size_push]
    have h_inner_size :
        trans₂.instructions.size = st.trans.instructions.size + 1 + DetBlockBodyInstrCount blk := by
      have h_size_after_label :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).instructions.size =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc :=
        emitLabel_preserves_size_eq label _ st.trans h_size
      have h_size_eq₂ : trans₂.instructions.size = trans₂.nextLoc :=
        cmdsFoldlM_preserves_size_eq fname blk.cmds _ trans₂ h_admitted h_inner h_size_after_label
      have h_advance₂ :
          trans₂.nextLoc =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc +
            blk.cmds.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 :=
        cmdsFoldlM_nextLoc_advance fname blk.cmds _ trans₂ h_admitted h_inner
      have h_after_label_nextLoc :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc = st.trans.nextLoc + 1 := rfl
      rw [h_size_eq₂, h_advance₂, h_after_label_nextLoc]
      simp [DetBlockBodyInstrCount, h_size]
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, _ =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        -- Goal: pairwise distinct in (st.pendingPatches.push (X, lf)).push (Y, lt).toList
        -- where X = trans₂.instructions.size, Y = trans₂.instructions.size + 1.
        simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
        simp only [Array.toList_push]
        -- toList is st.pendingPatches.toList ++ [(X, lf)] ++ [(Y, lt)]
        -- = st.pendingPatches.toList ++ [(X, lf), (Y, lt)]
        rw [List.append_assoc]
        rw [List.pairwise_append]
        refine ⟨h_old_distinct, ?_, ?_⟩
        · -- Pairwise on [X] ++ [Y]: distinct first projections.
          rw [List.pairwise_append]
          refine ⟨List.pairwise_singleton _ _, List.pairwise_singleton _ _, ?_⟩
          intro a ha b hb
          simp only [List.mem_singleton] at ha hb
          subst ha; subst hb
          simp [Array.size_push]
        · -- Old elements vs new: old indices < trans₂.instructions.size.
          intro p h_p_old q h_q_new
          have h_p_lt : p.1 < st.trans.instructions.size := by
            have h_p_arr : p ∈ st.pendingPatches :=
              Array.mem_toList_iff.mp h_p_old
            exact h_old_bound p h_p_arr
          have h_le : st.trans.instructions.size ≤ trans₂.instructions.size := by
            rw [h_inner_size]; omega
          have h_p_lt_trans₂ : p.1 < trans₂.instructions.size := Nat.lt_of_lt_of_le h_p_lt h_le
          -- q is one of the two new entries; its index is ≥ trans₂.instructions.size.
          rw [List.mem_append] at h_q_new
          rcases h_q_new with h_q | h_q
          · simp only [List.mem_singleton] at h_q
            subst h_q; omega
          · simp only [List.mem_singleton] at h_q
            subst h_q; simp [Array.size_push]; omega
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      exact h_old_distinct
  | .error _, _ => simp at h_run

/-- After the foldlM, `pendingPatches` toList is pairwise index-distinct. -/
theorem blocksFoldlM_pendingPatches_indices_distinct
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_old_bound : ∀ p ∈ st.pendingPatches, p.1 < st.trans.instructions.size)
    (h_old_distinct :
      List.Pairwise (fun a b => a.1 ≠ b.1) st.pendingPatches.toList) :
    List.Pairwise (fun a b => a.1 ≠ b.1) st'.pendingPatches.toList := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_old_distinct
  | cons hd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st hd with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ hd.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted hd (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname hd st st₁ h_admitted_head h_step h_size
      have h_bound₁ := coreCFGToGotoBlockStep_pendingPatches_indices_bound fname hd st st₁
        h_admitted_head h_step h_size h_old_bound
      have h_distinct₁ := coreCFGToGotoBlockStep_pendingPatches_indices_distinct fname hd st st₁
        h_admitted_head h_step h_size h_old_bound h_old_distinct
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      exact ih st₁ h_admitted_rest h_run h_size₁ h_bound₁ h_distinct₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Patch step success implies labelMap lookup succeeds

If `coreCFGToGotoPatchStep` succeeds, then `labelMap[label]?` is `some _`. -/

/-- Per-step success implies labelMap lookup succeeds. -/
theorem coreCFGToGotoPatchStep_success_lookup
    (labelMap : Std.HashMap String Nat)
    (loopContracts : Std.HashMap String (Imperative.MetaData Core.Expression))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap loopContracts acc idxLabel = Except.ok acc') :
    ∃ targetLoc, labelMap[idxLabel.2]? = some targetLoc := by
  obtain ⟨resolvedPatches, trans⟩ := acc
  obtain ⟨idx, label⟩ := idxLabel
  unfold Strata.coreCFGToGotoPatchStep at h_run
  simp only [Bind.bind, Except.bind] at h_run
  -- Use Option.isSome destructuring.
  by_cases h_some : (labelMap[label]?).isSome
  · obtain ⟨targetLoc, h_lookup⟩ := Option.isSome_iff_exists.mp h_some
    exact ⟨targetLoc, h_lookup⟩
  · -- If not some, the step would have errored.
    have h_none : labelMap[label]? = none := Option.not_isSome_iff_eq_none.mp h_some
    rw [h_none] at h_run
    simp at h_run

/-- The full patches fold success implies every `(idx, label)` in
the input patches has a labelMap lookup. -/
theorem patchesFoldlM_success_all_lookups
    (labelMap : Std.HashMap String Nat)
    (loopContracts : Std.HashMap String (Imperative.MetaData Core.Expression))
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap loopContracts) acc
              = Except.ok acc') :
    ∀ p ∈ patches, ∃ targetLoc, labelMap[p.2]? = some targetLoc := by
  rw [← Array.foldlM_toList] at h_run
  generalize h_eq : patches.toList = patchesL at h_run
  intro p h_p
  have h_p_list : p ∈ patchesL := by
    rw [← h_eq]; exact (Array.mem_toList_iff).mpr h_p
  clear h_eq h_p
  induction patchesL generalizing acc with
  | nil => simp at h_p_list
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap loopContracts acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      rw [List.mem_cons] at h_p_list
      rcases h_p_list with h_eq | h_in_rest
      · subst h_eq
        exact coreCFGToGotoPatchStep_success_lookup labelMap loopContracts acc acc₁ p h_step
      · exact ih acc₁ h_run h_in_rest
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- For a `.condGoto` block, the per-block step pushes the patches
`(st.trans.nextLoc + 1 + bodyCount, lf)` and `(st.trans.nextLoc + 1 + bodyCount + 1, lt)`
onto `pendingPatches`. -/
theorem coreCFGToGotoBlockStep_condGoto_pendingPatches
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (cond : Core.Expression.Expr) (lt lf : String)
    (md : Imperative.MetaData Core.Expression)
    (h_transfer : lblBlk.2.transfer = .condGoto cond lt lf md)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    (st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2, lf) ∈ st'.pendingPatches ∧
    (st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2 + 1, lt) ∈ st'.pendingPatches := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      simp [Imperative.emitLabel, Array.size_push]
    have h_inner_size :
        trans₂.instructions.size = st.trans.instructions.size + 1 + DetBlockBodyInstrCount blk := by
      have h_size_after_label :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).instructions.size =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc :=
        emitLabel_preserves_size_eq label _ st.trans h_size
      have h_size_eq₂ : trans₂.instructions.size = trans₂.nextLoc :=
        cmdsFoldlM_preserves_size_eq fname blk.cmds _ trans₂ h_admitted h_inner h_size_after_label
      have h_advance₂ :
          trans₂.nextLoc =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc +
            blk.cmds.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 :=
        cmdsFoldlM_nextLoc_advance fname blk.cmds _ trans₂ h_admitted h_inner
      have h_after_label_nextLoc :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc = st.trans.nextLoc + 1 := rfl
      rw [h_size_eq₂, h_advance₂, h_after_label_nextLoc]
      simp [DetBlockBodyInstrCount, h_size]
    rw [h_transfer] at h_run
    simp only at h_run
    generalize h_cond_eval :
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
    match cond_eval, h_cond_eval with
    | .ok cond_expr, _ =>
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      -- Now show the two patches are in the resulting pendingPatches array.
      -- pendingPatches = (st.pendingPatches.push (falseIdx, lf)).push (trueIdx, lt)
      -- where falseIdx = trans₂.instructions.size, trueIdx = trans₂.instructions.size + 1.
      -- We need: (st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk, lf) and
      --         (st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk + 1, lt) are in.
      have h_pc_neg_eq :
          st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk = trans₂.instructions.size := by
        rw [h_inner_size]; omega
      have h_pc_uncond_eq :
          st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk + 1 = trans₂.instructions.size + 1 := by
        rw [h_inner_size]; omega
      simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
      refine ⟨?_, ?_⟩
      · -- (st.trans.nextLoc + 1 + bodyCount, lf) ∈ pushed array
        rw [h_pc_neg_eq]
        simp only [Array.mem_push]
        left; right
        trivial
      · -- (st.trans.nextLoc + 1 + bodyCount + 1, lt) ∈ pushed array
        rw [h_pc_uncond_eq]
        simp only [Array.mem_push, Array.size_push]
        right
        trivial
    | .error _, _ => simp at h_run
  | .error _, _ => simp at h_run

/-! ### Lifted condGoto layout across blocksFoldlM

Lifts `coreCFGToGotoBlockStep_condGoto_at_pc` across the foldlM,
producing `pc` from the labelMap and the prefix-preservation of the
fold. -/

/-- For each `(l, blk) ∈ blocks` with `blk.transfer = .condGoto cond lt lf md`,
the foldlM produces an `st_final` where:
* `st_final.labelMap[l]? = some pc`
* `st_final.trans.instructions[pc + 1 + bodyCount]? = some instr_neg` with
  `.GOTO`, `target = none`, and guard `e_goto.not`.
* `st_final.trans.instructions[pc + 1 + bodyCount + 1]? = some instr_uncond`
  with `.GOTO`, `target = none`, and guard `Expr.true`.
* `(pc + 1 + bodyCount, lf) ∈ st_final.pendingPatches`
* `(pc + 1 + bodyCount + 1, lt) ∈ st_final.pendingPatches`

The `pc` here is the `nextLoc` BEFORE the block step processes the
block. -/
theorem blocksFoldlM_layout_cond_goto_pre_patch
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_distinct : BlockLabelsDistinct blocks) :
    ∀ l blk cond lt lf md, (l, blk) ∈ blocks → blk.transfer = .condGoto cond lt lf md →
      ∃ pc instr_neg instr_uncond e_goto,
        st'.labelMap[l]? = some pc ∧
        st'.trans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_neg ∧
        instr_neg.type = .GOTO ∧
        instr_neg.target = none ∧
        instr_neg.guard = e_goto.not ∧
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = .ok e_goto ∧
        st'.trans.instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]? = some instr_uncond ∧
        instr_uncond.type = .GOTO ∧
        instr_uncond.target = none ∧
        instr_uncond.guard = CProverGOTO.Expr.true ∧
        (pc + 1 + DetBlockBodyInstrCount blk, lf) ∈ st'.pendingPatches ∧
        (pc + 1 + DetBlockBodyInstrCount blk + 1, lt) ∈ st'.pendingPatches := by
  induction blocks generalizing st with
  | nil =>
    intro l blk cond lt lf md h_in
    simp at h_in
  | cons hd rest ih =>
    intro l blk cond lt lf md h_in h_transfer
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
      have h_distinct_rest : BlockLabelsDistinct rest := BlockLabelsDistinct_tail hd rest h_distinct
      have h_le_st' : st₁.trans.instructions.size ≤ st'.trans.instructions.size :=
        blocksFoldlM_size_le fname rest st₁ st' h_admitted_rest h_run
      rw [List.mem_cons] at h_in
      rcases h_in with h_eq | h_in_rest
      · subst h_eq
        -- (l, blk) is the head; transfer is .condGoto cond lt lf md.
        obtain ⟨instr_neg, instr_uncond, e_goto, h_at_neg_st₁, h_ty_neg, h_tgt_neg, h_guard_neg,
                h_e_goto, h_at_uncond_st₁, h_ty_uncond, h_tgt_uncond, h_guard_uncond⟩ :=
          coreCFGToGotoBlockStep_condGoto_at_pc fname (l, blk) st st₁ cond lt lf md
            h_transfer h_admitted_head h_step h_size
        have ⟨h_pp_lf_st₁, h_pp_lt_st₁⟩ := coreCFGToGotoBlockStep_condGoto_pendingPatches
          fname (l, blk) st st₁ cond lt lf md h_transfer h_admitted_head h_step h_size
        have h_pc_neg_lt :
            st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk < st₁.trans.instructions.size := by
          rw [Array.getElem?_eq_some_iff] at h_at_neg_st₁
          exact h_at_neg_st₁.1
        have h_pc_uncond_lt :
            st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk + 1 < st₁.trans.instructions.size := by
          rw [Array.getElem?_eq_some_iff] at h_at_uncond_st₁
          exact h_at_uncond_st₁.1
        have h_at_neg_st' :
            st'.trans.instructions[st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk]?
              = some instr_neg := by
          rw [blocksFoldlM_instructions_prefix? fname rest st₁ st' h_admitted_rest h_run _ h_pc_neg_lt]
          exact h_at_neg_st₁
        have h_at_uncond_st' :
            st'.trans.instructions[st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk + 1]?
              = some instr_uncond := by
          rw [blocksFoldlM_instructions_prefix? fname rest st₁ st' h_admitted_rest h_run _ h_pc_uncond_lt]
          exact h_at_uncond_st₁
        have h_lbl₁ : st₁.labelMap = st.labelMap.insert l st.trans.nextLoc :=
          coreCFGToGotoBlockStep_labelMap fname (l, blk) st st₁ h_step
        have h_head_not_in_rest : ∀ p ∈ rest, p.1 ≠ l := by
          intro p hp h_eq
          have : l ≠ p.1 := BlockLabelsDistinct_head_neq_tail (l, blk) rest h_distinct p hp
          exact this h_eq.symm
        have h_lbl_st' :
            st'.labelMap[l]? = st₁.labelMap[l]? :=
          blocksFoldlM_labelMap_preserves_external fname rest st₁ st' h_admitted_rest
            h_run l h_head_not_in_rest
        rw [h_lbl₁] at h_lbl_st'
        rw [Std.HashMap.getElem?_insert] at h_lbl_st'
        simp at h_lbl_st'
        -- Pending patches preserve through the rest of the fold.
        have h_pp_lf_st' :
            (st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk, lf) ∈ st'.pendingPatches :=
          blocksFoldlM_pendingPatches_preserves fname rest st₁ st' h_run _ h_pp_lf_st₁
        have h_pp_lt_st' :
            (st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk + 1, lt) ∈ st'.pendingPatches :=
          blocksFoldlM_pendingPatches_preserves fname rest st₁ st' h_run _ h_pp_lt_st₁
        refine ⟨st.trans.nextLoc, instr_neg, instr_uncond, e_goto, h_lbl_st', h_at_neg_st',
                h_ty_neg, h_tgt_neg, h_guard_neg, h_e_goto, h_at_uncond_st', h_ty_uncond,
                h_tgt_uncond, h_guard_uncond, h_pp_lf_st', h_pp_lt_st'⟩
      · -- Apply IH on rest.
        exact ih st₁ h_admitted_rest h_run h_size₁ h_distinct_rest l blk cond lt lf md
          h_in_rest h_transfer
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Resolved-patches index distinctness

Under empty contracts, resolvedPatches inherits index-distinctness
from pendingPatches. Specifically: each step prepends `(idx, targetLoc)`
where `idx` is the head's first projection, and pendingPatches' first
projections are pairwise distinct, so resolvedPatches is too. -/

/-- Per-step under empty contracts: if the input pendingPatches list's
first projections are distinct from `acc.1`'s, then so is the output's. -/
theorem patchesFoldlM_no_contracts_resolvedPatches_pairwise_distinct
    (labelMap : Std.HashMap String Nat)
    (patches : List (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc')
    (h_acc_distinct : List.Pairwise (fun a b => a.1 ≠ b.1) acc.1)
    (h_patches_distinct : List.Pairwise (fun a b => a.1 ≠ b.1) patches)
    (h_disjoint : ∀ p ∈ acc.1, ∀ q ∈ patches, p.1 ≠ q.1) :
    List.Pairwise (fun a b => a.1 ≠ b.1) acc'.1 := by
  induction patches generalizing acc with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_acc_distinct
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap ∅ acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      -- acc₁.1 = (head.1, targetLoc) :: acc.1
      obtain ⟨targetLoc, h_lookup⟩ :=
        coreCFGToGotoPatchStep_success_lookup labelMap ∅ acc acc₁ head h_step
      have h_acc₁_eq : acc₁.1 = (head.1, targetLoc) :: acc.1 :=
        coreCFGToGotoPatchStep_no_contracts_resolvedPatches labelMap acc acc₁ head targetLoc
          h_lookup h_step
      -- Build the IH preconditions.
      have h_distinct_rest : List.Pairwise (fun a b => a.1 ≠ b.1) rest := by
        rw [List.pairwise_cons] at h_patches_distinct
        exact h_patches_distinct.2
      have h_head_neq_rest : ∀ q ∈ rest, head.1 ≠ q.1 := by
        rw [List.pairwise_cons] at h_patches_distinct
        exact h_patches_distinct.1
      have h_acc₁_distinct : List.Pairwise (fun a b => a.1 ≠ b.1) acc₁.1 := by
        rw [h_acc₁_eq]
        rw [List.pairwise_cons]
        refine ⟨?_, h_acc_distinct⟩
        intro p hp
        -- p ∈ acc.1; head.1 ≠ p.1 by h_disjoint.
        exact (h_disjoint p hp head (by simp)).symm
      have h_disjoint_acc₁ : ∀ p ∈ acc₁.1, ∀ q ∈ rest, p.1 ≠ q.1 := by
        intro p hp q hq
        rw [h_acc₁_eq] at hp
        rw [List.mem_cons] at hp
        rcases hp with hp | hp
        · subst hp
          exact h_head_neq_rest q hq
        · exact h_disjoint p hp q (by simp [hq])
      exact ih acc₁ h_run h_acc₁_distinct h_distinct_rest h_disjoint_acc₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Top-level closures

Two closure theorems:
* `layout_cond_goto_of_translator`
* `layout_cond_goto_guards_of_translator`
-/

/-- The pendingPatches of the initial state (empty) are pairwise
distinct (trivially). -/
theorem coreCFGToGotoInitState_pendingPatches_distinct
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv) :
    List.Pairwise (fun a b => a.1 ≠ b.1)
      (coreCFGToGotoInitState trans₀).pendingPatches.toList := by
  simp [coreCFGToGotoInitState]

/-- The pendingPatches of the initial state are bounded (vacuously). -/
theorem coreCFGToGotoInitState_pendingPatches_bounded
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv) :
    ∀ p ∈ (coreCFGToGotoInitState trans₀).pendingPatches,
      p.1 < (coreCFGToGotoInitState trans₀).trans.instructions.size := by
  intro p hp
  simp [coreCFGToGotoInitState] at hp

/-- Closure for `layout_cond_goto`: under structural hypotheses on the
CFG and translator, every `.condGoto` block at offset `pc` produces two
GOTO instructions (after patching) with the right targets. -/
theorem layout_cond_goto_of_translator
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
              = Except.ok ans) :
    ∀ (st_final : Strata.CoreCFGTransLoopState),
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀) = Except.ok st_final →
    ∀ l blk pc cond lt lf md, (l, blk) ∈ cfg.blocks →
      hashMapToLabelMap st_final.labelMap l = some pc →
      blk.transfer = .condGoto cond lt lf md →
      ∃ pc_neg pc_uncond pc_lf pc_lt instr_neg instr_uncond,
        pc_neg = pc + 1 + DetBlockBodyInstrCount blk ∧
        pc_uncond = pc_neg + 1 ∧
        ans.instructions[pc_neg]? = some instr_neg ∧
        instr_neg.type = .GOTO ∧
        instr_neg.target = some pc_lf ∧
        hashMapToLabelMap st_final.labelMap lf = some pc_lf ∧
        ans.instructions[pc_uncond]? = some instr_uncond ∧
        instr_uncond.type = .GOTO ∧
        instr_uncond.target = some pc_lt ∧
        hashMapToLabelMap st_final.labelMap lt = some pc_lt := by
  intro st_final h_blocks_run l blk pc cond lt lf md h_in_blk h_lookup_l h_transfer
  -- Decompose ans = patchGotoTargets trans_post resolved.
  obtain ⟨st_final', resolved, trans_post, h_blocks_run', h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  -- The two block-folds give the same st_final (functions are deterministic).
  have h_st_eq : st_final = st_final' := by
    rw [h_blocks_run] at h_blocks_run'
    injection h_blocks_run'
  subst h_st_eq
  -- Apply lifted condGoto layout to extract instr_neg, instr_uncond at pre-patch positions.
  obtain ⟨pc', instr_neg_pre, instr_uncond_pre, e_goto,
          h_lookup_pre, h_at_neg_pre, h_ty_neg_pre, h_tgt_neg_pre, h_guard_neg_pre,
          h_e_goto, h_at_uncond_pre, h_ty_uncond_pre, h_tgt_uncond_pre, h_guard_uncond_pre,
          h_pp_lf, h_pp_lt⟩ :=
    blocksFoldlM_layout_cond_goto_pre_patch functionName cfg.blocks
      (coreCFGToGotoInitState trans₀) st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb)
      h_blocks_run (by simp [coreCFGToGotoInitState]; exact h_init_size) h_distinct
      l blk cond lt lf md h_in_blk h_transfer
  -- pc' = pc.
  have h_pc_eq : pc = pc' := by
    unfold hashMapToLabelMap at h_lookup_l
    rw [h_lookup_pre] at h_lookup_l
    exact (Option.some.inj h_lookup_l).symm
  subst h_pc_eq
  -- Use empty contracts to get trans_post = st_final.trans.
  have h_lc_empty := h_loopContracts_empty_post st_final h_blocks_run
  rw [h_lc_empty] at h_patches_run
  have h_trans_post_eq : trans_post = st_final.trans :=
    patchesFoldlM_no_contracts_trans_eq st_final.labelMap st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
  -- ans.instructions = patchGotoTargets st_final.trans resolved.instructions.
  have h_ans_instr :
      ans.instructions = (Imperative.patchGotoTargets st_final.trans resolved).instructions := by
    rw [h_ans_eq, h_trans_post_eq]
  -- Look up labelMap entries for lf and lt: by patchesFoldlM_success_all_lookups.
  obtain ⟨pc_lf, h_lf_lookup⟩ :=
    patchesFoldlM_success_all_lookups st_final.labelMap _ st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
      (pc + 1 + DetBlockBodyInstrCount blk, lf) h_pp_lf
  obtain ⟨pc_lt, h_lt_lookup⟩ :=
    patchesFoldlM_success_all_lookups st_final.labelMap _ st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
      (pc + 1 + DetBlockBodyInstrCount blk + 1, lt) h_pp_lt
  -- Get (pc + ..., pc_lf) ∈ resolved and (pc + ... + 1, pc_lt) ∈ resolved.
  have h_resolved_lf :
      (pc + 1 + DetBlockBodyInstrCount blk, pc_lf) ∈ resolved := by
    have := patchesFoldlM_no_contracts_resolvedPatches_mem st_final.labelMap
      st_final.pendingPatches ([], st_final.trans) (resolved, trans_post)
      h_patches_run (pc + 1 + DetBlockBodyInstrCount blk) lf pc_lf h_pp_lf h_lf_lookup
    exact this
  have h_resolved_lt :
      (pc + 1 + DetBlockBodyInstrCount blk + 1, pc_lt) ∈ resolved := by
    have := patchesFoldlM_no_contracts_resolvedPatches_mem st_final.labelMap
      st_final.pendingPatches ([], st_final.trans) (resolved, trans_post)
      h_patches_run (pc + 1 + DetBlockBodyInstrCount blk + 1) lt pc_lt h_pp_lt h_lt_lookup
    exact this
  -- Resolved's first projections are pairwise distinct.
  have h_pp_distinct :
      List.Pairwise (fun a b => a.1 ≠ b.1) st_final.pendingPatches.toList :=
    blocksFoldlM_pendingPatches_indices_distinct functionName cfg.blocks
      (coreCFGToGotoInitState trans₀) st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb)
      h_blocks_run (by simp [coreCFGToGotoInitState]; exact h_init_size)
      (coreCFGToGotoInitState_pendingPatches_bounded trans₀)
      (coreCFGToGotoInitState_pendingPatches_distinct trans₀)
  -- Index-bound for pendingPatches.
  have h_pp_bound :
      ∀ p ∈ st_final.pendingPatches, p.1 < st_final.trans.instructions.size :=
    blocksFoldlM_pendingPatches_indices_bound functionName cfg.blocks
      (coreCFGToGotoInitState trans₀) st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb)
      h_blocks_run (by simp [coreCFGToGotoInitState]; exact h_init_size)
      (coreCFGToGotoInitState_pendingPatches_bounded trans₀)
  -- Resolved indices are subset of pendingPatches indices, so resolved indices are
  -- bounded and pairwise distinct.
  -- We need: pc + 1 + bodyCount < st_final.trans.instructions.size and
  --         pc + 1 + bodyCount + 1 < st_final.trans.instructions.size.
  have h_neg_lt : pc + 1 + DetBlockBodyInstrCount blk < st_final.trans.instructions.size := by
    rw [Array.getElem?_eq_some_iff] at h_at_neg_pre
    exact h_at_neg_pre.1
  have h_uncond_lt : pc + 1 + DetBlockBodyInstrCount blk + 1 < st_final.trans.instructions.size := by
    rw [Array.getElem?_eq_some_iff] at h_at_uncond_pre
    exact h_at_uncond_pre.1
  -- Resolved indices distinct: a sufficient condition is "every (idx, _) ∈ resolved corresponds
  -- to a unique (idx, _) ∈ pendingPatches" — but we only need distinctness here.
  -- Lemma: under empty contracts, resolved.toList.map fst ⊂ pendingPatches.toList.map fst,
  -- AND each resolved element corresponds to a unique pendingPatches element.
  -- We need more: the map preserves distinctness.
  -- Let's use a workaround: prove distinctness directly via the structural argument.
  have h_resolved_distinct_aux :
      List.Pairwise (fun a b => a.1 ≠ b.1) resolved := by
    have h_patches_run_list :
        st_final.pendingPatches.toList.foldlM
          (Strata.coreCFGToGotoPatchStep st_final.labelMap ∅)
          ([], st_final.trans) = Except.ok (resolved, trans_post) := by
      rw [← Array.foldlM_toList] at h_patches_run
      exact h_patches_run
    apply patchesFoldlM_no_contracts_resolvedPatches_pairwise_distinct
      st_final.labelMap st_final.pendingPatches.toList
      ([], st_final.trans) (resolved, trans_post) h_patches_run_list
    · simp -- acc.1 = [] is trivially Pairwise.
    · exact h_pp_distinct
    · simp -- acc.1 = [] disjoint from anything.
  -- Apply patcher post-condition.
  have h_at_neg_ans :
      ∃ instr, ans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr ∧
        instr.target = some pc_lf := by
    rw [h_ans_instr]
    exact patchGotoTargets_target_at_patched_idx st_final.trans resolved
      h_resolved_distinct_aux _ pc_lf h_resolved_lf h_neg_lt
  have h_at_uncond_ans :
      ∃ instr, ans.instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]? = some instr ∧
        instr.target = some pc_lt := by
    rw [h_ans_instr]
    exact patchGotoTargets_target_at_patched_idx st_final.trans resolved
      h_resolved_distinct_aux _ pc_lt h_resolved_lt h_uncond_lt
  obtain ⟨instr_neg, h_at_neg, h_tgt_neg⟩ := h_at_neg_ans
  obtain ⟨instr_uncond, h_at_uncond, h_tgt_uncond⟩ := h_at_uncond_ans
  -- The .GOTO type is preserved by the patcher.
  have h_ty_neg : instr_neg.type = .GOTO := by
    have h_at_post : (Imperative.patchGotoTargets st_final.trans resolved).instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_neg := by
      rw [← h_ans_instr]; exact h_at_neg
    obtain ⟨instr_pre, h_at_pre, h_ty_eq⟩ :=
      patchGotoTargets_preserves_type st_final.trans resolved _ _ h_at_post
    rw [h_at_pre] at h_at_neg_pre
    injection h_at_neg_pre with h_eq
    rw [h_ty_eq, h_eq]; exact h_ty_neg_pre
  have h_ty_uncond : instr_uncond.type = .GOTO := by
    have h_at_post : (Imperative.patchGotoTargets st_final.trans resolved).instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]? = some instr_uncond := by
      rw [← h_ans_instr]; exact h_at_uncond
    obtain ⟨instr_pre, h_at_pre, h_ty_eq⟩ :=
      patchGotoTargets_preserves_type st_final.trans resolved _ _ h_at_post
    rw [h_at_pre] at h_at_uncond_pre
    injection h_at_uncond_pre with h_eq
    rw [h_ty_eq, h_eq]; exact h_ty_uncond_pre
  -- Convert HashMap lookups to hashMapToLabelMap.
  have h_lf_lookup' : hashMapToLabelMap st_final.labelMap lf = some pc_lf := h_lf_lookup
  have h_lt_lookup' : hashMapToLabelMap st_final.labelMap lt = some pc_lt := h_lt_lookup
  -- Combine.
  exact ⟨pc + 1 + DetBlockBodyInstrCount blk, pc + 1 + DetBlockBodyInstrCount blk + 1,
         pc_lf, pc_lt, instr_neg, instr_uncond, rfl, rfl, h_at_neg, h_ty_neg, h_tgt_neg,
         h_lf_lookup', h_at_uncond, h_ty_uncond, h_tgt_uncond, h_lt_lookup'⟩

/-! ### Patcher preserves the guard field

The patcher only edits the `target` field, so `guard` is preserved.
This is the analogue of `patchGotoTargets_preserves_type`. -/

/-- Single-patch preserves the `guard` field at any index. -/
private theorem patch_one_preserves_guard
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (i : Nat) (instr : CProverGOTO.Instruction)
    (h : (a.set! idx { a[idx]! with target := some tgt })[i]? = some instr) :
    ∃ instr_pre,
      a[i]? = some instr_pre ∧
      instr.guard = instr_pre.guard := by
  rw [Array.set!_eq_setIfInBounds] at h
  by_cases h_idx : idx < a.size
  · by_cases h_eq : i = idx
    · subst h_eq
      have h_lt_set : i < (a.setIfInBounds i { a[i]! with target := some tgt }).size := by
        simp [h_idx]
      rw [Array.getElem?_eq_getElem h_lt_set] at h
      rw [Array.getElem_setIfInBounds_self] at h
      injection h with h
      have h_at : a[i]? = some a[i] := Array.getElem?_eq_getElem h_idx
      refine ⟨a[i], h_at, ?_⟩
      have h_getD : a[i]! = a[i] := getElem!_pos a i h_idx
      rw [← h]
      simp [h_getD]
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm h_eq)] at h
      exact ⟨instr, h, rfl⟩
  · rw [Array.setIfInBounds_eq_of_size_le (Nat.le_of_not_lt h_idx)] at h
    exact ⟨instr, h, rfl⟩

/-- `patchGotoTargets` preserves the guard field at any index — the
patcher only writes the `target` field. -/
theorem patchGotoTargets_preserves_guard
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (patches : List (Nat × Nat))
    (i : Nat) (instr : CProverGOTO.Instruction)
    (h : (Imperative.patchGotoTargets trans patches).instructions[i]? = some instr) :
    ∃ instr_pre,
      trans.instructions[i]? = some instr_pre ∧
      instr.guard = instr_pre.guard := by
  unfold Imperative.patchGotoTargets at h
  simp only at h
  -- Generalize over the array.
  have hgen :
      ∀ (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat))
        (i : Nat) (instr : CProverGOTO.Instruction),
        (List.foldl
          (fun acc (p : Nat × Nat) =>
            acc.set! p.fst { acc[p.fst]! with target := some p.snd })
          a ps)[i]? = some instr →
        ∃ instr_pre, a[i]? = some instr_pre ∧ instr.guard = instr_pre.guard := by
    intro a ps i instr h
    induction ps generalizing a with
    | nil =>
      simp at h
      exact ⟨instr, h, rfl⟩
    | cons p ps ih =>
      simp only [List.foldl] at h
      obtain ⟨instr_after_first, h_after_first, h_g_after_first⟩ := ih _ h
      obtain ⟨instr_pre, h_pre, h_g_pre⟩ :=
        patch_one_preserves_guard a p.1 p.2 i instr_after_first h_after_first
      exact ⟨instr_pre, h_pre, h_g_after_first.trans h_g_pre⟩
  exact hgen _ _ _ _ h

/-! ### Top-level closure for `layout_cond_goto_guards`

Uses the per-block-step's guard shape (`e_goto.not` and `Expr.true`)
plus the patcher's preservation of guards. -/

/-- Closure for `layout_cond_goto_guards`: every `.condGoto` block
produces two GOTO instructions with the expected guards `e_goto.not`
and `Expr.true` (after patching, which preserves guards). -/
theorem layout_cond_goto_guards_of_translator
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
    (h_expr_translated_witness :
      ∀ (cond : Core.Expression.Expr) (e_goto : CProverGOTO.Expr),
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond
          = .ok e_goto →
        ExprTranslated δ δ_goto δ_goto_bool cond e_goto) :
    ∀ (st_final : Strata.CoreCFGTransLoopState),
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀) = Except.ok st_final →
    ∀ l blk pc cond lt lf md instr_neg instr_uncond,
      (l, blk) ∈ cfg.blocks →
      hashMapToLabelMap st_final.labelMap l = some pc →
      blk.transfer = .condGoto cond lt lf md →
      ans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_neg →
      ans.instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]? = some instr_uncond →
      ∃ e_goto,
        instr_neg.guard = e_goto.not ∧
        ExprTranslated δ δ_goto δ_goto_bool cond e_goto ∧
        instr_uncond.guard = CProverGOTO.Expr.true := by
  intro st_final h_blocks_run l blk pc cond lt lf md instr_neg instr_uncond
        h_in_blk h_lookup_l h_transfer h_at_neg h_at_uncond
  -- Decompose ans.
  obtain ⟨st_final', resolved, trans_post, h_blocks_run', h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  have h_st_eq : st_final = st_final' := by
    rw [h_blocks_run] at h_blocks_run'
    injection h_blocks_run'
  subst h_st_eq
  -- Extract pre-patch guards from the lifted condGoto layout.
  obtain ⟨pc', instr_neg_pre, instr_uncond_pre, e_goto,
          h_lookup_pre, h_at_neg_pre, h_ty_neg_pre, h_tgt_neg_pre, h_guard_neg_pre,
          h_e_goto, h_at_uncond_pre, h_ty_uncond_pre, h_tgt_uncond_pre, h_guard_uncond_pre,
          _, _⟩ :=
    blocksFoldlM_layout_cond_goto_pre_patch functionName cfg.blocks
      (coreCFGToGotoInitState trans₀) st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb)
      h_blocks_run (by simp [coreCFGToGotoInitState]; exact h_init_size) h_distinct
      l blk cond lt lf md h_in_blk h_transfer
  have h_pc_eq : pc = pc' := by
    unfold hashMapToLabelMap at h_lookup_l
    rw [h_lookup_pre] at h_lookup_l
    exact (Option.some.inj h_lookup_l).symm
  subst h_pc_eq
  -- Use empty contracts.
  have h_lc_empty := h_loopContracts_empty_post st_final h_blocks_run
  rw [h_lc_empty] at h_patches_run
  have h_trans_post_eq : trans_post = st_final.trans :=
    patchesFoldlM_no_contracts_trans_eq st_final.labelMap st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
  -- ans.instructions = patchGotoTargets st_final.trans resolved.instructions.
  have h_ans_instr :
      ans.instructions = (Imperative.patchGotoTargets st_final.trans resolved).instructions := by
    rw [h_ans_eq, h_trans_post_eq]
  -- Apply patchGotoTargets_preserves_guard.
  have h_at_neg_post :
      (Imperative.patchGotoTargets st_final.trans resolved).instructions[pc + 1 + DetBlockBodyInstrCount blk]?
        = some instr_neg := by
    rw [← h_ans_instr]; exact h_at_neg
  have h_at_uncond_post :
      (Imperative.patchGotoTargets st_final.trans resolved).instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]?
        = some instr_uncond := by
    rw [← h_ans_instr]; exact h_at_uncond
  obtain ⟨instr_neg_pre', h_at_neg_pre', h_g_neg_eq⟩ :=
    patchGotoTargets_preserves_guard st_final.trans resolved _ _ h_at_neg_post
  obtain ⟨instr_uncond_pre', h_at_uncond_pre', h_g_uncond_eq⟩ :=
    patchGotoTargets_preserves_guard st_final.trans resolved _ _ h_at_uncond_post
  -- Match instr_neg_pre' with instr_neg_pre and similar.
  rw [h_at_neg_pre] at h_at_neg_pre'
  rw [h_at_uncond_pre] at h_at_uncond_pre'
  injection h_at_neg_pre' with h_neg_eq
  injection h_at_uncond_pre' with h_uncond_eq
  -- The guards match. h_neg_eq : instr_neg_pre = instr_neg_pre'.
  -- h_g_neg_eq : instr_neg.guard = instr_neg_pre'.guard.
  -- h_guard_neg_pre : instr_neg_pre.guard = e_goto.not.
  refine ⟨e_goto, ?_, h_expr_translated_witness cond e_goto h_e_goto, ?_⟩
  · rw [h_g_neg_eq, ← h_neg_eq]; exact h_guard_neg_pre
  · rw [h_g_uncond_eq, ← h_uncond_eq]; exact h_guard_uncond_pre

/-! ## Strengthened top-level theorem

`coreCFGToGotoTransform_wellFormed_strengthened` composes the
`layout_*_of_translator` and `{labelMap_inj,entry_in_map}_of_translator`
closures with `coreCFGToGotoTransform_wellFormed_nonempty`, internalising
its five hypothesis parameters covering layout and labelMap fields.

External hypotheses still required from callers:

* `h_entry_first` — `cfg.blocks.head?.map Prod.fst = some cfg.entry`.
  The translator already checks this and rejects on violation.
* `h_expr_corr` — `ExprTranslationPreservesEval` (caller-supplied).
* `h_tx_eq` — technical equality between
  `Imperative.ToGoto.toGotoExpr` and `h_expr_corr.tx`.
* `h_expr_translated_witness` — finer-grained version of
  `h_expr_corr` for the cond-goto layout proof. -/

theorem coreCFGToGotoTransform_wellFormed_strengthened
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans₀.instructions[i]? = some instr → instr.locationNum = i)
    (h_distinct : BlockLabelsDistinct cfg.blocks)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (h_entry_first : cfg.blocks.head?.map Prod.fst = some cfg.entry)
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
          = Except.ok (h_expr_corr.tx e))
    (h_expr_translated_witness :
      ∀ (cond : Core.Expression.Expr) (e_goto : CProverGOTO.Expr),
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond
          = .ok e_goto →
        ExprTranslated δ δ_goto δ_goto_bool cond e_goto) :
    Nonempty (WellFormedTranslation cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      δ δ_goto δ_goto_bool) := by
  -- Discharge each of `_wellFormed_nonempty`'s five hypothesis
  -- parameters via the closure theorems, then plug into it.
  have h_layout_cond_goto :=
    layout_cond_goto_of_translator cfg Env functionName trans₀
      h_init_size h_distinct h_admitted_blocks
      h_loopContracts_empty_post ans h_run
  have h_layout_cond_goto_guards :=
    layout_cond_goto_guards_of_translator cfg Env functionName trans₀
      h_init_size h_distinct h_admitted_blocks
      h_loopContracts_empty_post ans h_run
      δ δ_goto δ_goto_bool h_expr_translated_witness
  have h_layout_block_body :=
    layout_block_body_of_translator cfg Env functionName trans₀
      h_init_size h_distinct h_admitted_blocks
      h_loopContracts_empty_post ans h_run
      δ δ_goto δ_goto_bool h_expr_corr h_tx_eq
  have h_labelMap_inj :=
    labelMap_inj_of_translator cfg functionName trans₀
      h_admitted_blocks
  have h_entry_in_map :=
    entry_in_map_of_translator cfg functionName trans₀
      h_init_size h_distinct h_admitted_blocks h_entry_first
  exact coreCFGToGotoTransform_wellFormed_nonempty
    cfg Env functionName trans₀
    h_init_size h_init_loc h_distinct h_admitted_blocks
    h_loopContracts_empty_post ans h_run
    δ δ_goto δ_goto_bool
    h_layout_cond_goto h_layout_cond_goto_guards h_layout_block_body
    h_labelMap_inj h_entry_in_map

end -- public section

end CProverGOTO
