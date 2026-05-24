/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF.StepPreservation
import all Strata.DL.Imperative.ToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline

/-! # WellFormedTranslation - Outer fold + decompose

This file is part 4 of the CoreCFGToGotoTransformWF split. It
provides the outer-loop fold layout-fact preservation, the
layout-fact propagation, the patch-step preservation lemmas, the
structural soundness theorems, the translator decomposition, the
shadow structure + recovery, and the top-level
`coreCFGToGotoTransform_wellFormed_nonempty` theorem.
-/

namespace CProverGOTO

open Imperative

public section


/-! ### Outer-loop foldlM layout-fact preservation

The per-block layout facts (LOCATION at pc, END_FUNCTION/condGoto-pair
at the end of the block) need to be propagated through subsequent
block iterations using `coreCFGToGotoBlockStep_instructions_prefix?`.

The labelMap accumulates entries for each processed block; we need
that distinct block labels stay distinct in the final HashMap. -/

/-- The outer foldlM only grows the instruction array. -/
theorem blocksFoldlM_size_le
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st') :
    st.trans.instructions.size ≤ st'.trans.instructions.size := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact Nat.le_refl _
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ head.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted head (by simp)
      have h_le := coreCFGToGotoBlockStep_size_le fname head st st₁ h_admitted_head h_step
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have := ih st₁ h_admitted_rest h_run
      omega
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The outer foldlM preserves the instruction-array prefix. -/
theorem blocksFoldlM_instructions_prefix?
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (k : Nat) (h : k < st.trans.instructions.size) :
    st'.trans.instructions[k]? = st.trans.instructions[k]? := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; rfl
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ head.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted head (by simp)
      have h_le := coreCFGToGotoBlockStep_size_le fname head st st₁ h_admitted_head h_step
      have h_k₁ : k < st₁.trans.instructions.size := Nat.lt_of_lt_of_le h h_le
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have h_ih := ih st₁ h_admitted_rest h_run h_k₁
      rw [h_ih]
      exact coreCFGToGotoBlockStep_instructions_prefix? fname head st st₁ h_admitted_head h_step k h
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Layout-fact propagation through foldlM

For each `(l, blk)` in the processed prefix, we want the LOCATION,
END_FUNCTION, or condGoto-pair of that block to remain in the final
`st_final.trans.instructions` array at the same offset. The position
of the block (the snapshot of `nextLoc` at the start of the block's
iteration) is captured by walking the foldlM with an accumulator.

The labelMap accumulates entries — block `i` inserts `(label_i ↦
pc_i)`. Subsequent iterations may overwrite if `label_j = label_i` for
`j > i`. To ensure the labelMap-correspondence works, we require
distinct labels (`BlockLabelsDistinct`).

These lemmas thread a `BlockLabelsDistinct` hypothesis: the labels of
all blocks in `blocks` are pairwise distinct. -/

/-- A list of blocks has pairwise distinct labels. -/
@[expose] def BlockLabelsDistinct
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression)) :
    Prop :=
  List.Pairwise (fun a b => a.1 ≠ b.1) blocks

/-- A `Pairwise` distinctness on labels implies any element's label is
distinct from all subsequent labels. -/
theorem BlockLabelsDistinct_head_neq_tail
    (head : String × Imperative.DetBlock String Core.Command Core.Expression)
    (rest : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (h : BlockLabelsDistinct (head :: rest)) :
    ∀ p ∈ rest, head.1 ≠ p.1 := by
  unfold BlockLabelsDistinct at h
  cases h with
  | cons h_head h_rest =>
    intro p h_in
    exact h_head p h_in

/-- A `Pairwise` distinctness on the tail. -/
theorem BlockLabelsDistinct_tail
    (head : String × Imperative.DetBlock String Core.Command Core.Expression)
    (rest : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (h : BlockLabelsDistinct (head :: rest)) :
    BlockLabelsDistinct rest := by
  unfold BlockLabelsDistinct at h ⊢
  cases h with
  | cons _ h_rest => exact h_rest

/-- After the foldlM, if a label is in the labelMap of the input
state, it remains the same in the output state — provided the label is
not the head of any block in the processed list (because each block's
step only inserts its own label). -/
theorem blocksFoldlM_labelMap_preserves_external
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (l : String) (h_not_in : ∀ p ∈ blocks, p.1 ≠ l) :
    st'.labelMap[l]? = st.labelMap[l]? := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; rfl
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ head.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted head (by simp)
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have h_lbl₁ : st₁.labelMap = st.labelMap.insert head.1 st.trans.nextLoc :=
        coreCFGToGotoBlockStep_labelMap fname head st st₁ h_step
      have h_not_l_head : head.1 ≠ l := h_not_in head (by simp)
      have h_not_l_rest : ∀ p ∈ rest, p.1 ≠ l := fun p hp => h_not_in p (by simp [hp])
      have h_ih := ih st₁ h_admitted_rest h_run h_not_l_rest
      rw [h_ih, h_lbl₁]
      rw [Std.HashMap.getElem?_insert]
      have h_l_neq : ¬ head.1 = l := h_not_l_head
      simp [h_l_neq]
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- For each `(l, blk) ∈ blocks` such that the foldlM produces
`st_final`, there exists a `pc` with:
* `st_final.labelMap[l]? = some pc`
* `st_final.trans.instructions[pc]? = some instr` and `instr.type = .LOCATION`
* `pc < st_final.trans.instructions.size`

The proof works by induction on `blocks`. -/
theorem blocksFoldlM_layout_location
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_distinct : BlockLabelsDistinct blocks) :
    ∀ l blk, (l, blk) ∈ blocks →
      ∃ pc instr,
        st'.labelMap[l]? = some pc ∧
        st'.trans.instructions[pc]? = some instr ∧
        instr.type = .LOCATION ∧
        pc < st'.trans.instructions.size := by
  induction blocks generalizing st with
  | nil =>
    intro l blk h_in
    simp at h_in
  | cons hd rest ih =>
    intro l blk h_in
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
      have h_le_st₁ : st.trans.instructions.size ≤ st₁.trans.instructions.size :=
        coreCFGToGotoBlockStep_size_le fname hd st st₁ h_admitted_head h_step
      have h_le_st' : st₁.trans.instructions.size ≤ st'.trans.instructions.size :=
        blocksFoldlM_size_le fname rest st₁ st' h_admitted_rest h_run
      -- Either (l, blk) = hd, or (l, blk) ∈ rest.
      rw [List.mem_cons] at h_in
      rcases h_in with h_eq | h_in_rest
      · -- (l, blk) = hd.
        subst h_eq
        obtain ⟨instr, h_at_st₁, h_ty, _⟩ :=
          coreCFGToGotoBlockStep_location_at_pc_with_labels fname (l, blk) st st₁
            h_admitted_head h_step h_size
        have h_pc_lt_st₁ : st.trans.nextLoc < st₁.trans.instructions.size := by
          rw [Array.getElem?_eq_some_iff] at h_at_st₁
          exact h_at_st₁.1
        have h_pc_lt_st' : st.trans.nextLoc < st'.trans.instructions.size :=
          Nat.lt_of_lt_of_le h_pc_lt_st₁ h_le_st'
        have h_at_st' : st'.trans.instructions[st.trans.nextLoc]? = some instr := by
          rw [blocksFoldlM_instructions_prefix? fname rest st₁ st' h_admitted_rest h_run _ h_pc_lt_st₁]
          exact h_at_st₁
        have h_lbl₁ : st₁.labelMap = st.labelMap.insert l st.trans.nextLoc :=
          coreCFGToGotoBlockStep_labelMap fname (l, blk) st st₁ h_step
        have h_head_not_in_rest : ∀ p ∈ rest, p.1 ≠ l := by
          intro p hp h_eq
          have : l ≠ p.1 := BlockLabelsDistinct_head_neq_tail (l, blk) rest h_distinct p hp
          exact this h_eq.symm
        have h_lbl_st' :
            st'.labelMap[l]? = st₁.labelMap[l]? := by
          exact blocksFoldlM_labelMap_preserves_external fname rest st₁ st' h_admitted_rest
            h_run l h_head_not_in_rest
        rw [h_lbl₁] at h_lbl_st'
        rw [Std.HashMap.getElem?_insert] at h_lbl_st'
        simp at h_lbl_st'
        refine ⟨st.trans.nextLoc, instr, h_lbl_st', h_at_st', h_ty, h_pc_lt_st'⟩
      · -- (l, blk) ∈ rest. Apply IH.
        exact ih st₁ h_admitted_rest h_run h_size₁ h_distinct_rest l blk h_in_rest
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- Strengthened `blocksFoldlM_layout_location`: also exposes that the
LOCATION instruction's `labels` field equals `[l]`. Used to prove that
any `WellFormedTranslation`'s `labelMap l` agrees with the translator's
hashmap-keyed labelMap on `cfg.blocks` labels. -/
theorem blocksFoldlM_layout_location_with_labels
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_distinct : BlockLabelsDistinct blocks) :
    ∀ l blk, (l, blk) ∈ blocks →
      ∃ pc instr,
        st'.labelMap[l]? = some pc ∧
        st'.trans.instructions[pc]? = some instr ∧
        instr.type = .LOCATION ∧
        instr.labels = [l] ∧
        pc < st'.trans.instructions.size := by
  induction blocks generalizing st with
  | nil =>
    intro l blk h_in
    simp at h_in
  | cons hd rest ih =>
    intro l blk h_in
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
      have h_le_st₁ : st.trans.instructions.size ≤ st₁.trans.instructions.size :=
        coreCFGToGotoBlockStep_size_le fname hd st st₁ h_admitted_head h_step
      have h_le_st' : st₁.trans.instructions.size ≤ st'.trans.instructions.size :=
        blocksFoldlM_size_le fname rest st₁ st' h_admitted_rest h_run
      rw [List.mem_cons] at h_in
      rcases h_in with h_eq | h_in_rest
      · -- (l, blk) = hd.
        subst h_eq
        obtain ⟨instr, h_at_st₁, h_ty, h_labels⟩ :=
          coreCFGToGotoBlockStep_location_at_pc_with_labels fname (l, blk) st st₁
            h_admitted_head h_step h_size
        have h_pc_lt_st₁ : st.trans.nextLoc < st₁.trans.instructions.size := by
          rw [Array.getElem?_eq_some_iff] at h_at_st₁
          exact h_at_st₁.1
        have h_pc_lt_st' : st.trans.nextLoc < st'.trans.instructions.size :=
          Nat.lt_of_lt_of_le h_pc_lt_st₁ h_le_st'
        have h_at_st' : st'.trans.instructions[st.trans.nextLoc]? = some instr := by
          rw [blocksFoldlM_instructions_prefix? fname rest st₁ st' h_admitted_rest h_run _ h_pc_lt_st₁]
          exact h_at_st₁
        have h_lbl₁ : st₁.labelMap = st.labelMap.insert l st.trans.nextLoc :=
          coreCFGToGotoBlockStep_labelMap fname (l, blk) st st₁ h_step
        have h_head_not_in_rest : ∀ p ∈ rest, p.1 ≠ l := by
          intro p hp h_eq
          have : l ≠ p.1 := BlockLabelsDistinct_head_neq_tail (l, blk) rest h_distinct p hp
          exact this h_eq.symm
        have h_lbl_st' :
            st'.labelMap[l]? = st₁.labelMap[l]? := by
          exact blocksFoldlM_labelMap_preserves_external fname rest st₁ st' h_admitted_rest
            h_run l h_head_not_in_rest
        rw [h_lbl₁] at h_lbl_st'
        rw [Std.HashMap.getElem?_insert] at h_lbl_st'
        simp at h_lbl_st'
        refine ⟨st.trans.nextLoc, instr, h_lbl_st', h_at_st', h_ty, h_labels, h_pc_lt_st'⟩
      · -- (l, blk) ∈ rest. Apply IH.
        exact ih st₁ h_admitted_rest h_run h_size₁ h_distinct_rest l blk h_in_rest
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- For each `(l, blk) ∈ blocks` such that `blk.transfer = .finish md`,
the foldlM puts an END_FUNCTION at `pc + 1 + bodyCount` for the
appropriate pc. -/
theorem blocksFoldlM_layout_finish
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_distinct : BlockLabelsDistinct blocks) :
    ∀ l blk md, (l, blk) ∈ blocks → blk.transfer = .finish md →
      ∃ pc instr_end,
        st'.labelMap[l]? = some pc ∧
        st'.trans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_end ∧
        instr_end.type = .END_FUNCTION := by
  induction blocks generalizing st with
  | nil =>
    intro l blk md h_in
    simp at h_in
  | cons hd rest ih =>
    intro l blk md h_in h_transfer
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
        -- (l, blk) is the head; transfer is .finish md.
        obtain ⟨instr_end, h_at_st₁, h_ty⟩ :=
          coreCFGToGotoBlockStep_finish_at_pc fname (l, blk) st st₁ md h_transfer h_admitted_head h_step h_size
        -- Propagate through the rest of the foldlM.
        have h_pc_lt_st₁ : st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk < st₁.trans.instructions.size := by
          rw [Array.getElem?_eq_some_iff] at h_at_st₁
          exact h_at_st₁.1
        have h_at_st' :
            st'.trans.instructions[st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk]? =
              some instr_end := by
          rw [blocksFoldlM_instructions_prefix? fname rest st₁ st' h_admitted_rest h_run _ h_pc_lt_st₁]
          exact h_at_st₁
        -- Now show st'.labelMap[l]? = some st.trans.nextLoc.
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
        refine ⟨st.trans.nextLoc, instr_end, h_lbl_st', h_at_st', h_ty⟩
      · -- Apply IH on rest.
        exact ih st₁ h_admitted_rest h_run h_size₁ h_distinct_rest l blk md h_in_rest h_transfer
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Patch-step preservation (under empty loopContracts)

The patch step (`coreCFGToGotoPatchStep`) either fails (label
unresolved), prepends `(idx, targetLoc)` to `resolvedPatches`, or also
mutates `trans.instructions[idx].guard` for loop contracts. We
discharge the patch step under the hypothesis `loopContracts = ∅`,
which is the case for any CFG without loop-invariant or loop-decreases
metadata; concrete callers verifying the WF property pass this
hypothesis. -/

/-- When `loopContracts` is empty, the patch step returns the input
`trans` unchanged (only modifies `resolvedPatches`). -/
theorem coreCFGToGotoPatchStep_no_contracts_trans_eq
    (labelMap : Std.HashMap String Nat)
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap ∅ acc idxLabel = Except.ok acc') :
    acc'.2 = acc.2 := by
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
    -- With empty loopContracts, there are no entries.
    have h_lc : (∅ : Std.HashMap String (Imperative.MetaData Core.Expression))[label]? = none := by
      simp
    rw [h_lc] at h_run
    simp [pure, Except.pure] at h_run
    rw [← h_run]

/-- The patch step preserves `size_eq` when `loopContracts` is empty. -/
theorem coreCFGToGotoPatchStep_preserves_size_eq_no_contracts
    (labelMap : Std.HashMap String Nat)
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap ∅ acc idxLabel = Except.ok acc')
    (h_size : acc.2.instructions.size = acc.2.nextLoc) :
    acc'.2.instructions.size = acc'.2.nextLoc := by
  rw [coreCFGToGotoPatchStep_no_contracts_trans_eq labelMap acc acc' idxLabel h_run]
  exact h_size

/-- The patch step preserves `locationNum_eq_index` when `loopContracts` is empty. -/
theorem coreCFGToGotoPatchStep_preserves_locationNum_no_contracts
    (labelMap : Std.HashMap String Nat)
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap ∅ acc idxLabel = Except.ok acc')
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        acc.2.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      acc'.2.instructions[i]? = some instr → instr.locationNum = i := by
  rw [coreCFGToGotoPatchStep_no_contracts_trans_eq labelMap acc acc' idxLabel h_run]
  exact h_loc

/-- The patches-fold preserves the transform under empty loop contracts. -/
theorem patchesFoldlM_no_contracts_trans_eq
    (labelMap : Std.HashMap String Nat)
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc') :
    acc'.2 = acc.2 := by
  rw [← Array.foldlM_toList] at h_run
  generalize h_eq : patches.toList = patchesL at h_run
  clear h_eq
  induction patchesL generalizing acc with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; rfl
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap ∅ acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp at h_run
      have h_eq₁ : acc₁.2 = acc.2 :=
        coreCFGToGotoPatchStep_no_contracts_trans_eq labelMap acc acc₁ head h_step
      rw [ih acc₁ h_run, h_eq₁]
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The patches-fold preserves `size_eq` (no loop contracts). -/
theorem patchesFoldlM_preserves_size_eq_no_contracts
    (labelMap : Std.HashMap String Nat)
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc')
    (h_size : acc.2.instructions.size = acc.2.nextLoc) :
    acc'.2.instructions.size = acc'.2.nextLoc := by
  -- Convert to list-foldlM for inductive reasoning.
  rw [← Array.foldlM_toList] at h_run
  -- Now `patches.toList.foldlM ... acc = .ok acc'`.
  generalize h_eq : patches.toList = patchesL at h_run
  clear h_eq
  induction patchesL generalizing acc with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_size
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap ∅ acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_size₁ : acc₁.2.instructions.size = acc₁.2.nextLoc :=
        coreCFGToGotoPatchStep_preserves_size_eq_no_contracts labelMap acc acc₁ head h_step h_size
      exact ih acc₁ h_size₁ h_run
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The patches-fold preserves `locationNum_eq_index` (no loop contracts). -/
theorem patchesFoldlM_preserves_locationNum_no_contracts
    (labelMap : Std.HashMap String Nat)
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc')
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        acc.2.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      acc'.2.instructions[i]? = some instr → instr.locationNum = i := by
  rw [← Array.foldlM_toList] at h_run
  generalize h_eq : patches.toList = patchesL at h_run
  clear h_eq
  induction patchesL generalizing acc with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_loc
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap ∅ acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_loc₁ :
          ∀ (i : Nat) (instr : CProverGOTO.Instruction),
            acc₁.2.instructions[i]? = some instr → instr.locationNum = i :=
        coreCFGToGotoPatchStep_preserves_locationNum_no_contracts
          labelMap acc acc₁ head h_step h_loc
      exact ih acc₁ h_loc₁ h_run
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ## Structural soundness of the translator output

`coreCFGToGotoTransform_size_eq_and_loc` is the structural half of the
top-level theorem: under the right hypotheses, the translator's output
satisfies `instructions.size = nextLoc` and every instruction's
`locationNum` equals its array index. -/

/-- After the translator runs (under no-loop-contracts and admitted-cmds
hypotheses), the output `ans : GotoTransform` satisfies:
* `ans.instructions.size = ans.nextLoc`,
* every instruction's `locationNum` equals its array index. -/
theorem coreCFGToGotoTransform_size_eq_and_loc
    (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans₀.instructions[i]? = some instr → instr.locationNum = i)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (st_final : Strata.CoreCFGTransLoopState)
    (h_blocks_run :
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        ({ trans := trans₀, pendingPatches := #[], labelMap := {},
           loopContracts := {} } : Strata.CoreCFGTransLoopState)
      = Except.ok st_final)
    (h_loopContracts_empty : st_final.loopContracts = ∅)
    (resolved : List (Nat × Nat))
    (trans_post : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_patches_run :
      st_final.pendingPatches.foldlM
        (Strata.coreCFGToGotoPatchStep st_final.labelMap st_final.loopContracts)
        ([], st_final.trans)
      = Except.ok (resolved, trans_post))
    (h_ans_eq : ans = Imperative.patchGotoTargets trans_post resolved) :
    ans.instructions.size = ans.nextLoc ∧
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i := by
  -- Step 1: the blocks-fold preserves size_eq + locationNum_eq_index.
  have h_size_st : st_final.trans.instructions.size = st_final.trans.nextLoc :=
    blocksFoldlM_preserves_size_eq functionName cfg.blocks _ st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb) h_blocks_run h_init_size
  have h_loc_st :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        st_final.trans.instructions[i]? = some instr → instr.locationNum = i :=
    blocksFoldlM_preserves_locationNum_eq_index functionName cfg.blocks _ st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb) h_blocks_run h_init_size h_init_loc
  -- Step 2: the patches-fold preserves them under the empty-loopContracts hypothesis.
  rw [h_loopContracts_empty] at h_patches_run
  have h_size_post : trans_post.instructions.size = trans_post.nextLoc :=
    patchesFoldlM_preserves_size_eq_no_contracts st_final.labelMap _
      ([], st_final.trans) (resolved, trans_post) h_patches_run h_size_st
  have h_loc_post :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans_post.instructions[i]? = some instr → instr.locationNum = i :=
    patchesFoldlM_preserves_locationNum_no_contracts st_final.labelMap _
      ([], st_final.trans) (resolved, trans_post) h_patches_run h_loc_st
  -- Step 3: patchGotoTargets preserves them.
  have h_size_ans : ans.instructions.size = ans.nextLoc := by
    rw [h_ans_eq]
    rw [patchGotoTargets_preserves_size, patchGotoTargets_preserves_nextLoc]
    exact h_size_post
  have h_loc_ans :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        ans.instructions[i]? = some instr → instr.locationNum = i := by
    intro i instr h
    rw [h_ans_eq] at h
    exact patchGotoTargets_preserves_locationNum_eq_index trans_post resolved h_loc_post i instr h
  exact ⟨h_size_ans, h_loc_ans⟩

/-! ### Translator decomposition

Initial state for the translator's forward pass and an explicit
unfolding of the translator into `do let st ← ...; let (r, t) ← ...;
return ...` form. -/

/-- Initial loop-state for `coreCFGToGotoTransform`'s forward pass. -/
@[expose] def coreCFGToGotoInitState
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    : Strata.CoreCFGTransLoopState :=
  { trans := trans₀, pendingPatches := #[], labelMap := {}, loopContracts := {} }

/-- The translator's output factors through the post-blocks-fold,
post-patches-fold, and a final `patchGotoTargets`. The proof works by
case-analysis on `cfg.blocks` to dispense with the entry-check, then
walking the two foldlM chains with `match`. -/
theorem coreCFGToGotoTransform_decompose
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans) :
    ∃ (st_final : Strata.CoreCFGTransLoopState)
      (resolved : List (Nat × Nat))
      (trans_post : Imperative.GotoTransform Core.Expression.TyEnv),
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀)
      = Except.ok st_final ∧
      st_final.pendingPatches.foldlM
        (Strata.coreCFGToGotoPatchStep st_final.labelMap st_final.loopContracts)
        ([], st_final.trans)
      = Except.ok (resolved, trans_post) ∧
      ans = Imperative.patchGotoTargets trans_post resolved := by
  unfold Strata.coreCFGToGotoTransform at h_run
  -- Two cases on cfg.blocks for the entry-check; both dispatch to the same body.
  -- We use a unified strategy: rewrite the entry-check to `pure ()` first when the
  -- entry condition holds; in the empty-blocks case, the entry-check is `pure ()`
  -- directly. Use `match` on cfg.blocks via h_blocks.
  match h_blocks : cfg.blocks with
  | [] =>
    -- With empty blocks, both folds are trivial and the entry-check is `pure ()`.
    -- After the `match h_blocks : cfg.blocks with | [] =>`, in this branch
    -- `cfg.blocks` may already be substituted, so we don't `rw [h_blocks]`.
    refine ⟨coreCFGToGotoInitState trans₀, [], trans₀, ?_, ?_, ?_⟩
    · -- Goal: [].foldlM ... = ok (initState trans₀). Holds by rfl.
      rfl
    · rfl
    · -- ans = patchGotoTargets trans₀ [].
      rw [h_blocks] at h_run
      simp only [Bind.bind, Except.bind, pure, Except.pure, List.foldlM] at h_run
      injection h_run with h_run
      rw [← h_run]
  | (firstLabel, firstBlk) :: tail =>
    rw [h_blocks] at h_run
    simp only at h_run
    by_cases h_eq : firstLabel = cfg.entry
    · -- Entry match; if-bypassed.
      have h_neq : (firstLabel != cfg.entry) = false := by simp [h_eq]
      simp only [h_neq, Bool.false_eq_true, if_false] at h_run
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
      -- Match on the blocks-fold result. Use the literal initSt record so it unifies with h_run.
      generalize h_blocks_fold :
        ((firstLabel, firstBlk) :: tail).foldlM
          (Strata.coreCFGToGotoBlockStep functionName)
          ({ trans := trans₀, pendingPatches := #[], labelMap := {},
             loopContracts := {} } : Strata.CoreCFGTransLoopState)
          = blocks_fold at h_run
      match blocks_fold, h_blocks_fold with
      | .ok st_final, h_blocks_fold =>
        simp only at h_run -- reduce `match Except.ok st_final` step
        generalize h_patches_fold :
          st_final.pendingPatches.foldlM
            (Strata.coreCFGToGotoPatchStep st_final.labelMap st_final.loopContracts)
            ([], st_final.trans) = patches_fold at h_run
        match patches_fold, h_patches_fold with
        | .ok (resolved, trans_post), h_patches_fold =>
          refine ⟨st_final, resolved, trans_post, ?_, h_patches_fold, ?_⟩
          · -- Goal: ((firstLabel, firstBlk) :: tail).foldlM ... (initState trans₀) = ok st_final.
            -- (cfg.blocks already substituted by Lean's match-rewrite.)
            -- coreCFGToGotoInitState unfolds to the literal record in h_blocks_fold.
            simp only [coreCFGToGotoInitState]
            exact h_blocks_fold
          · simp only at h_run
            injection h_run with h_run; rw [← h_run]
        | .error _, _ => simp at h_run
      | .error _, _ => simp at h_run
    · -- Entry mismatch; throws.
      have h_neq : (firstLabel != cfg.entry) = true := by simp [h_eq]
      simp only [h_neq, if_true, throw, throwThe, MonadExcept.throw,
                 Bind.bind, Except.bind] at h_run
      cases h_run

/-! ### Direct structural soundness

Composes `coreCFGToGotoTransform_decompose` with
`coreCFGToGotoTransform_size_eq_and_loc` to deliver the structural
guarantees of `coreCFGToGotoTransform`'s output directly from input
hypotheses + a "post-blocks-fold loopContracts is empty" hypothesis. -/

/-- The translator's output satisfies `size_eq` and
`locationNum_eq_index`, given input hypotheses + the post-blocks-fold
hypothesis that `loopContracts` is empty (true for any CFG without
loop-invariant or decreases metadata). -/
theorem coreCFGToGotoTransform_size_eq_and_loc_direct
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans₀.instructions[i]? = some instr → instr.locationNum = i)
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
    ans.instructions.size = ans.nextLoc ∧
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i := by
  obtain ⟨st_final, resolved, trans_post, h_blocks_run, h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  exact coreCFGToGotoTransform_size_eq_and_loc functionName cfg trans₀
    h_init_size h_init_loc h_admitted_blocks ans
    st_final h_blocks_run (h_loopContracts_empty_post st_final h_blocks_run)
    resolved trans_post h_patches_run h_ans_eq



/-- The hypothesis bundle for `coreCFGToGotoTransform_wellFormed_via_shadow`:
captures all the facts that an outer-loop equivalence proof must
supply about the `coreCFGToGotoTransform`'s output. -/
structure CoreCFGToGotoTransformShadow
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression) where
  /-- The final labelMap, total over `cfg.blocks`. -/
  finalLabelMap : LabelMap
  /-- Every CFG block label has a `pc` in `finalLabelMap`. -/
  labelMap_total :
    ∀ l, l ∈ cfg.blocks.map Prod.fst → (finalLabelMap l).isSome
  /-- Distinct labels map to distinct `pc`s. -/
  labelMap_inj :
    ∀ l₁ l₂ pc, finalLabelMap l₁ = some pc → finalLabelMap l₂ = some pc → l₁ = l₂
  /-- The `instructions.size = nextLoc` invariant on the final state. -/
  size_eq : ans.instructions.size = ans.nextLoc
  /-- Every instruction's `locationNum = index`. -/
  locationNum_eq_index :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i
  /-- For each CFG block label, `instrAt` of its `pc` returns a LOCATION
  instruction. -/
  layout_location :
    ∀ l blk pc,
      (l, blk) ∈ cfg.blocks → finalLabelMap l = some pc →
      ∃ instr, ans.instructions[pc]? = some instr ∧ instr.type = .LOCATION
  /-- The LOCATION instruction at `finalLabelMap l`'s `pc` carries `[l]` in
  its `labels` field. -/
  layout_location_labels :
    ∀ l blk pc,
      (l, blk) ∈ cfg.blocks → finalLabelMap l = some pc →
      ∃ instr, ans.instructions[pc]? = some instr ∧
        instr.type = .LOCATION ∧ instr.labels = [l]
  /-- For each `condGoto` block, two GOTO instructions appear at the
  end with proper targets. -/
  layout_cond_goto :
    ∀ l blk pc cond lt lf md, (l, blk) ∈ cfg.blocks →
      finalLabelMap l = some pc →
      blk.transfer = .condGoto cond lt lf md →
      ∃ pc_neg pc_uncond pc_lf pc_lt instr_neg instr_uncond,
        pc_neg = pc + 1 + DetBlockBodyInstrCount blk ∧
        pc_uncond = pc_neg + 1 ∧
        ans.instructions[pc_neg]? = some instr_neg ∧
        instr_neg.type = .GOTO ∧
        instr_neg.target = some pc_lf ∧
        finalLabelMap lf = some pc_lf ∧
        ans.instructions[pc_uncond]? = some instr_uncond ∧
        instr_uncond.type = .GOTO ∧
        instr_uncond.target = some pc_lt ∧
        finalLabelMap lt = some pc_lt
  /-- The condGoto guards have the right shape. -/
  layout_cond_goto_guards :
    ∀ l blk pc cond lt lf md instr_neg instr_uncond,
      (l, blk) ∈ cfg.blocks →
      finalLabelMap l = some pc →
      blk.transfer = .condGoto cond lt lf md →
      ans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_neg →
      ans.instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]? = some instr_uncond →
      ∃ e_goto,
        instr_neg.guard = e_goto.not ∧
        ExprTranslated δ δ_goto δ_goto_bool cond e_goto ∧
        instr_uncond.guard = CProverGOTO.Expr.true
  /-- For each `finish` block, an END_FUNCTION appears after the body. -/
  layout_finish :
    ∀ l blk pc md, (l, blk) ∈ cfg.blocks →
      finalLabelMap l = some pc →
      blk.transfer = .finish md →
      ∃ pc_end instr_end,
        pc_end = pc + 1 + DetBlockBodyInstrCount blk ∧
        ans.instructions[pc_end]? = some instr_end ∧
        instr_end.type = .END_FUNCTION
  /-- For each block body, the per-Cmd layout holds. -/
  layout_block_body :
    ∀ l blk pc, (l, blk) ∈ cfg.blocks → finalLabelMap l = some pc →
    ∀ k inner,
      (h : k < blk.cmds.length) →
      blk.cmds[k]'h = .cmd inner →
      CmdEmittedAt δ δ_goto δ_goto_bool
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions } -- temporary program
        (pc + 1 + cmdsPrefixInstrCount blk.cmds k)
        inner
  /-- The CFG's entry label is in the map. -/
  entry_in_map : ∃ pc, finalLabelMap cfg.entry = some pc

/-- Bridge from `CoreCFGToGotoTransformShadow` to
`WellFormedTranslation`: build the witness over the program whose
instructions equal `ans.instructions`. The bridge is essentially a
field-by-field copy — each field of `WellFormedTranslation` is
provided directly by the corresponding field of
`CoreCFGToGotoTransformShadow`, modulo the
`instrAt`-vs-`instructions[?]` rephrasing. -/
def wellFormedTranslation_of_shadow
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (shadow : CoreCFGToGotoTransformShadow cfg Env functionName
                trans₀ ans δ δ_goto δ_goto_bool) :
    WellFormedTranslation cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      δ δ_goto δ_goto_bool where
  labelMap := shadow.finalLabelMap
  labelMap_total := shadow.labelMap_total
  labelMap_inj := shadow.labelMap_inj
  layout_location := by
    intro l blk pc h_in h_lookup
    obtain ⟨instr, h_at, h_ty⟩ := shadow.layout_location l blk pc h_in h_lookup
    refine ⟨instr, ?_, h_ty⟩
    -- Goal: pgm.instrAt pc = some instr, where pgm.instructions = ans.instructions.
    show ans.instructions[pc]? = some instr
    exact h_at
  layout_location_labels := by
    intro l blk pc h_in h_lookup
    obtain ⟨instr, h_at, h_ty, h_labels⟩ :=
      shadow.layout_location_labels l blk pc h_in h_lookup
    refine ⟨instr, ?_, h_ty, h_labels⟩
    show ans.instructions[pc]? = some instr
    exact h_at
  layout_cond_goto := by
    intro l blk pc cond lt lf md h_in h_lookup h_transfer
    obtain ⟨pc_neg, pc_uncond, pc_lf, pc_lt, instr_neg, instr_uncond,
            h_pc_neg, h_pc_uncond, h_at_neg, h_ty_neg, h_target_neg, h_lf_lookup,
            h_at_uncond, h_ty_uncond, h_target_uncond, h_lt_lookup⟩ :=
      shadow.layout_cond_goto l blk pc cond lt lf md h_in h_lookup h_transfer
    refine ⟨pc_neg, pc_uncond, pc_lf, pc_lt, instr_neg, instr_uncond,
            h_pc_neg, h_pc_uncond, ?_, h_ty_neg, h_target_neg, h_lf_lookup,
            ?_, h_ty_uncond, h_target_uncond, h_lt_lookup⟩
    · show ans.instructions[pc_neg]? = some instr_neg
      exact h_at_neg
    · show ans.instructions[pc_uncond]? = some instr_uncond
      exact h_at_uncond
  layout_cond_goto_guards := by
    intro l blk pc cond lt lf md instr_neg instr_uncond h_in h_lookup h_transfer h_neg h_uncond
    -- The hypotheses use Program.instrAt; convert to ans.instructions[?].
    have h_neg' : ans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_neg := h_neg
    have h_uncond' : ans.instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]? = some instr_uncond := h_uncond
    exact shadow.layout_cond_goto_guards l blk pc cond lt lf md instr_neg instr_uncond
      h_in h_lookup h_transfer h_neg' h_uncond'
  layout_finish := by
    intro l blk pc md h_in h_lookup h_transfer
    obtain ⟨pc_end, instr_end, h_pc_end, h_at_end, h_ty_end⟩ :=
      shadow.layout_finish l blk pc md h_in h_lookup h_transfer
    refine ⟨pc_end, instr_end, h_pc_end, ?_, h_ty_end⟩
    show ans.instructions[pc_end]? = some instr_end
    exact h_at_end
  layout_block_body := shadow.layout_block_body
  entry_in_map := shadow.entry_in_map
  locationNum_eq_index := by
    intro i instr h
    -- Goal: instr.locationNum = i, where h : pgm.instrAt i = some instr.
    -- pgm.instrAt i = ans.instructions[i]? by the program's instructions field.
    have h' : ans.instructions[i]? = some instr := h
    exact shadow.locationNum_eq_index i instr h'

/-! ## Top-level theorem

`coreCFGToGotoTransform_wellFormed_nonempty` proves
`Nonempty (WellFormedTranslation ...)` — there exists a witness for
the well-formedness predicate over the translator's output. The proof
composes:

1. `coreCFGToGotoTransform_size_eq_and_loc_direct` (size_eq + locationNum).
2. `blocksFoldlM_layout_location` and `blocksFoldlM_layout_finish` for
   the LOCATION and END_FUNCTION layouts.
3. `patchGotoTargets_preserves_type` to bridge from
   `st_final.trans.instructions` to `ans.instructions`.
4. External hypotheses for the unproven layout fields
   (`layout_cond_goto`, `layout_cond_goto_guards`, `layout_block_body`,
   `labelMap_inj`, `entry_in_map`).

`Nonempty` form sidesteps the motive-typing issues with
`Classical.choose` on `coreCFGToGotoTransform_decompose`'s ∃-witness:
the goal is now a `Prop` (`Nonempty _`) so `obtain` on the `∃` works
directly. -/

/-- Top-level theorem in `Nonempty` form: `coreCFGToGotoTransform`
produces a `WellFormedTranslation`-witnessed program (under the
hypotheses). -/
theorem coreCFGToGotoTransform_wellFormed_nonempty
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
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_layout_cond_goto :
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
          hashMapToLabelMap st_final.labelMap lt = some pc_lt)
    (h_layout_cond_goto_guards :
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
          instr_uncond.guard = CProverGOTO.Expr.true)
    (h_layout_block_body :
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
          inner)
    (h_labelMap_inj :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀) = Except.ok st_final →
      ∀ l₁ l₂ pc,
        hashMapToLabelMap st_final.labelMap l₁ = some pc →
        hashMapToLabelMap st_final.labelMap l₂ = some pc →
        l₁ = l₂)
    (h_entry_in_map :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀) = Except.ok st_final →
      ∃ pc, hashMapToLabelMap st_final.labelMap cfg.entry = some pc) :
    Nonempty (WellFormedTranslation cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      δ δ_goto δ_goto_bool) := by
  -- Decompose the translator's output (in Prop, so obtain works).
  obtain ⟨st_final, resolved, trans_post, h_blocks_run, h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  -- size_eq + locationNum_eq_index from structural soundness.
  obtain ⟨h_size_ans, h_loc_ans⟩ :=
    coreCFGToGotoTransform_size_eq_and_loc_direct Env functionName cfg trans₀
      h_init_size h_init_loc
      (fun l blk h_in c h_c => h_admitted_blocks l blk h_in c h_c)
      h_loopContracts_empty_post ans h_run
  -- Layout lemmas at the post-blocks-fold state.
  have h_layout_loc_st :=
    blocksFoldlM_layout_location functionName cfg.blocks _ st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb)
      h_blocks_run h_init_size h_distinct
  have h_layout_loc_labels_st :=
    blocksFoldlM_layout_location_with_labels functionName cfg.blocks _ st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb)
      h_blocks_run h_init_size h_distinct
  have h_layout_fin_st :=
    blocksFoldlM_layout_finish functionName cfg.blocks _ st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb)
      h_blocks_run h_init_size h_distinct
  -- Patches + patchGotoTargets preserve the array under loop-contracts-empty.
  have h_lc_empty := h_loopContracts_empty_post st_final h_blocks_run
  rw [h_lc_empty] at h_patches_run
  have h_trans_post_eq : trans_post = st_final.trans :=
    patchesFoldlM_no_contracts_trans_eq st_final.labelMap st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
  -- Helper: at any pc, ans.instructions[pc]? gives some instr with type
  -- preserved from st_final.trans.instructions[pc]?.
  have h_ans_eq' : ans = Imperative.patchGotoTargets st_final.trans resolved := by
    rw [h_ans_eq, h_trans_post_eq]
  have h_ans_type_at :
      ∀ (pc : Nat) (instr_st : CProverGOTO.Instruction),
        st_final.trans.instructions[pc]? = some instr_st →
        ∃ instr_ans,
          ans.instructions[pc]? = some instr_ans ∧
          instr_ans.type = instr_st.type := by
    intro pc instr_st h_at_st
    have h_size_ans' : ans.instructions.size = st_final.trans.instructions.size := by
      rw [h_ans_eq']
      exact patchGotoTargets_preserves_size st_final.trans resolved
    have h_pc_lt : pc < ans.instructions.size := by
      have h_st_lt : pc < st_final.trans.instructions.size :=
        Array.getElem?_eq_some_iff.mp h_at_st |>.1
      omega
    have h_at_ans_eq : ans.instructions = (Imperative.patchGotoTargets st_final.trans resolved).instructions := by
      rw [h_ans_eq']
    have h_at_ans : ans.instructions[pc]? = some ans.instructions[pc] :=
      Array.getElem?_eq_getElem h_pc_lt
    refine ⟨ans.instructions[pc], h_at_ans, ?_⟩
    -- Use patchGotoTargets_preserves_type. The hypothesis h_at_ans is over
    -- ans.instructions; we rewrite to get over patchGotoTargets.
    have h_at_patched :
        (Imperative.patchGotoTargets st_final.trans resolved).instructions[pc]? = some ans.instructions[pc] := by
      rw [← h_at_ans_eq]; exact h_at_ans
    obtain ⟨instr_pre, h_at_pre, h_ty_eq⟩ :=
      patchGotoTargets_preserves_type st_final.trans resolved pc _ h_at_patched
    rw [h_at_pre] at h_at_st
    injection h_at_st with h_at_st
    rw [h_ty_eq]; rw [← h_at_st]
  -- labelMap_total: every block label is in st_final.labelMap.
  have h_labelMap_total :
      ∀ l, l ∈ cfg.blocks.map Prod.fst →
        (hashMapToLabelMap st_final.labelMap l).isSome := by
    intro l h_in
    rw [List.mem_map] at h_in
    obtain ⟨p, h_in', h_eq⟩ := h_in
    obtain ⟨l', blk⟩ := p
    simp at h_eq
    subst h_eq
    obtain ⟨pc, _, h_lookup, _, _, _⟩ := h_layout_loc_st l' blk h_in'
    show (st_final.labelMap[l']?).isSome
    rw [h_lookup]; rfl
  -- Build the shadow.
  refine ⟨wellFormedTranslation_of_shadow cfg Env functionName trans₀ ans
            δ δ_goto δ_goto_bool ?_⟩
  exact {
    finalLabelMap := hashMapToLabelMap st_final.labelMap
    labelMap_total := h_labelMap_total
    labelMap_inj := h_labelMap_inj st_final h_blocks_run
    size_eq := h_size_ans
    locationNum_eq_index := h_loc_ans
    layout_location := by
      intro l blk pc h_in h_lookup
      obtain ⟨pc', instr, h_lookup', h_at_st, h_ty_st, _⟩ := h_layout_loc_st l blk h_in
      have h_pc_eq : pc = pc' := by
        unfold hashMapToLabelMap at h_lookup
        rw [h_lookup'] at h_lookup
        exact (Option.some.inj h_lookup).symm
      obtain ⟨instr_ans, h_at_ans, h_ty_eq⟩ := h_ans_type_at pc' instr h_at_st
      refine ⟨instr_ans, h_pc_eq ▸ h_at_ans, ?_⟩
      rw [h_ty_eq]; exact h_ty_st
    layout_location_labels := by
      intro l blk pc h_in h_lookup
      obtain ⟨pc', instr_st, h_lookup', h_at_st, h_ty_st, h_labels_st, _⟩ :=
        h_layout_loc_labels_st l blk h_in
      have h_pc_eq : pc = pc' := by
        unfold hashMapToLabelMap at h_lookup
        rw [h_lookup'] at h_lookup
        exact (Option.some.inj h_lookup).symm
      -- Lift the LOCATION fact + labels through the patcher.
      obtain ⟨instr_ans, h_at_ans, h_ty_eq⟩ := h_ans_type_at pc' instr_st h_at_st
      -- Use the labels-preserving lemma.
      have h_at_patched :
          (Imperative.patchGotoTargets st_final.trans resolved).instructions[pc']?
            = some instr_ans := by
        have h_at_ans_eq : ans.instructions =
            (Imperative.patchGotoTargets st_final.trans resolved).instructions := by
          rw [h_ans_eq']
        rw [← h_at_ans_eq]; exact h_at_ans
      obtain ⟨instr_pre_lab, h_pre_lab, h_lab_eq⟩ :=
        patchGotoTargets_preserves_labels st_final.trans resolved pc' _ h_at_patched
      have h_inst_eq : instr_pre_lab = instr_st := by
        rw [h_pre_lab] at h_at_st
        injection h_at_st
      refine ⟨instr_ans, h_pc_eq ▸ h_at_ans, ?_, ?_⟩
      · rw [h_ty_eq]; exact h_ty_st
      · rw [h_lab_eq, h_inst_eq]; exact h_labels_st
    layout_cond_goto := h_layout_cond_goto st_final h_blocks_run
    layout_cond_goto_guards := h_layout_cond_goto_guards st_final h_blocks_run
    layout_finish := by
      intro l blk pc md h_in h_lookup h_transfer
      obtain ⟨pc', instr_end, h_lookup', h_at_st, h_ty_st⟩ :=
        h_layout_fin_st l blk md h_in h_transfer
      have h_pc_eq : pc = pc' := by
        unfold hashMapToLabelMap at h_lookup
        rw [h_lookup'] at h_lookup
        exact (Option.some.inj h_lookup).symm
      obtain ⟨instr_ans, h_at_ans, h_ty_eq⟩ := h_ans_type_at _ instr_end h_at_st
      refine ⟨pc' + 1 + DetBlockBodyInstrCount blk, instr_ans, h_pc_eq ▸ rfl, h_pc_eq ▸ h_at_ans, ?_⟩
      rw [h_ty_eq]; exact h_ty_st
    layout_block_body := h_layout_block_body st_final h_blocks_run
    entry_in_map := h_entry_in_map st_final h_blocks_run
  }


end -- public section

end CProverGOTO
