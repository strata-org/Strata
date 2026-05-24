/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF
public import Strata.Backends.CBMC.GOTO.GotoTargetInRange
public import Strata.Backends.CBMC.GOTO.BlocksFoldClosed
import all Strata.DL.Imperative.ToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline

public section

/-! # Discharging `EveryGotoTargetIsLabelMapEntry` by translator induction

Closes the `EveryGotoTargetIsLabelMapEntry cfg pgm wf.labelMap`
hypothesis by structural induction over `coreCFGToGotoTransform`'s
pieces.

Strategy: the blocks-fold emits GOTOs only with `target = none`
(invariant `NoGotoHasTarget'`, preserved via `BlocksFoldClosed`); the
patcher (under empty `loopContracts`) writes `target = some t` only at
indices `pc` for which `(pc, t) ∈ resolved`, which trace back to a
pending patch label and a labelMap lookup, hence to a block label. -/

namespace CProverGOTO.GotoTargetProvenance

open Imperative
open CProverGOTO

/-! ## "No GOTO has target set" predicate + push/append primitives -/

/-- Array-level: every `GOTO` in `a` has `target = none`. -/
abbrev NoGotoHasTarget' (a : Array CProverGOTO.Instruction) : Prop :=
  ∀ {pc : Nat} {instr : Instruction},
    a[pc]? = some instr → instr.type = .GOTO → instr.target = none

/-- Transform-level (legacy public name). -/
abbrev NoGotoHasTarget (trans : Imperative.GotoTransform Core.Expression.TyEnv) : Prop :=
  NoGotoHasTarget' trans.instructions

private theorem noGotoHasTarget'_push
    (a : Array CProverGOTO.Instruction) (new_instr : Instruction)
    (h : NoGotoHasTarget' a)
    (h_safe : new_instr.type = .GOTO → new_instr.target = none) :
    NoGotoHasTarget' (a.push new_instr) := by
  intro pc instr h_at h_ty
  by_cases h_lt : pc < a.size
  · rw [Array.getElem?_push_lt h_lt] at h_at
    exact h (by rw [Array.getElem?_eq_getElem h_lt]; exact h_at) h_ty
  · by_cases h_eq : pc = a.size
    · subst h_eq
      rw [Array.getElem?_push_size] at h_at
      injection h_at with h_at
      subst h_at
      exact h_safe h_ty
    · have h_oor : (a.push new_instr).size ≤ pc := by
        rw [Array.size_push]; omega
      rw [Array.getElem?_eq_none h_oor] at h_at
      exact absurd h_at (by simp)

private theorem noGotoHasTarget'_append_two
    (a : Array CProverGOTO.Instruction) (i₀ i₁ : Instruction)
    (h : NoGotoHasTarget' a)
    (h_safe0 : i₀.type = .GOTO → i₀.target = none)
    (h_safe1 : i₁.type = .GOTO → i₁.target = none) :
    NoGotoHasTarget' (a ++ #[i₀, i₁]) := by
  intro pc instr h_at h_ty
  by_cases h_lt : pc < a.size
  · rw [Array.getElem?_append_left h_lt] at h_at
    exact h h_at h_ty
  · by_cases h_eq0 : pc = a.size
    · subst h_eq0
      rw [Array.getElem?_append_right (Nat.le_refl _)] at h_at
      simp at h_at
      subst h_at
      exact h_safe0 h_ty
    · by_cases h_eq1 : pc = a.size + 1
      · subst h_eq1
        rw [Array.getElem?_append_right (Nat.le_add_right _ _)] at h_at
        simp at h_at
        subst h_at
        exact h_safe1 h_ty
      · have h_oor : (a ++ #[i₀, i₁]).size ≤ pc := by
          rw [Array.size_append]
          simp; omega
        rw [Array.getElem?_eq_none h_oor] at h_at
        exact absurd h_at (by simp)

/-! ## `BlocksFoldClosed` instance for `NoGotoHasTarget'`

Every leaf emit pushes either a non-GOTO instruction (vacuously safe)
or a GOTO with `target = none` (`emitCondGoto`/`emitUncondGoto`). We
provide the instance manually because `ofPushSafe` only sees the type,
not the GOTO target. The cmds-fold portion (toGotoInstructions /
cmdStep_call) reuses the standalone helpers in `BlocksFoldClosed`. -/

-- Discharge "non-GOTO type ⇒ safe" by `cases` on the type-equality.
private theorem nonGoto_isSafe {instr : Instruction} {T : InstructionType}
    (h_ty : instr.type = T) (h_neq : T ≠ .GOTO) :
    instr.type = .GOTO → instr.target = none := by
  intro h_g; rw [h_ty] at h_g; cases h_neq h_g

instance instBlocksFoldClosed_NoGotoHasTarget' :
    BlocksFoldClosed NoGotoHasTarget' where
  toGotoInstructions T fname c trans ans h_run h :=
    BlocksFoldClosed.toGotoInstructions_preserves_of_pushSafe
      (fun x => x.type = .GOTO → x.target = none)
      noGotoHasTarget'_push noGotoHasTarget'_append_two
      (fun _ h_ty => nonGoto_isSafe h_ty (by decide))
      (fun _ h_ty => nonGoto_isSafe h_ty (by decide))
      (fun _ h_ty => nonGoto_isSafe h_ty (by decide))
      (fun _ h_ty => nonGoto_isSafe h_ty (by decide))
      T fname c trans ans h_run h
  cmdStep_call fname cmd trans ans h_call h_run h :=
    BlocksFoldClosed.cmdStep_call_preserves_of_pushSafe
      (fun x => x.type = .GOTO → x.target = none)
      noGotoHasTarget'_push
      (fun _ h_ty => nonGoto_isSafe h_ty (by decide))
      fname cmd trans ans h_call h_run h
  emitLabel label srcLoc trans h := by
    show NoGotoHasTarget' (trans.instructions.push _)
    intro pc instr h_at h_ty
    exact noGotoHasTarget'_push trans.instructions _ h
      (nonGoto_isSafe (T := .LOCATION) rfl (by decide)) h_at h_ty
  emitCondGoto guard srcLoc trans h := by
    show NoGotoHasTarget' (trans.instructions.push _)
    intro pc instr h_at h_ty
    exact noGotoHasTarget'_push trans.instructions _ h (fun _ => rfl) h_at h_ty
  emitUncondGoto srcLoc trans h := by
    show NoGotoHasTarget' (trans.instructions.push _)
    intro pc instr h_at h_ty
    exact noGotoHasTarget'_push trans.instructions _ h (fun _ => rfl) h_at h_ty
  endFunctionEmit md fname trans h := by
    intro pc instr h_at h_ty
    exact noGotoHasTarget'_push _ _ h
      (nonGoto_isSafe (T := .END_FUNCTION) (by unfold endFunctionInstr; rfl) (by decide))
      h_at h_ty

/-! ## Patcher reverse-target lemma: post-target = some t implies (pc, t) ∈ patches -/

private theorem patch_one_other_index
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (i : Nat) (h_neq : i ≠ idx) :
    (a.set! idx { a[idx]! with target := some tgt })[i]? = a[i]? := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases h_idx : idx < a.size
  · exact Array.getElem?_setIfInBounds_ne h_neq.symm
  · rw [Array.setIfInBounds_eq_of_size_le (Nat.le_of_not_lt h_idx)]

private theorem patch_one_target_local
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (h_idx : idx < a.size) :
    ∃ instr,
      (a.set! idx { a[idx]! with target := some tgt })[idx]? = some instr ∧
      instr.target = some tgt := by
  rw [Array.set!_eq_setIfInBounds]
  have h_lt : idx < (a.setIfInBounds idx { a[idx]! with target := some tgt }).size := by
    simp [h_idx]
  refine ⟨{ a[idx]! with target := some tgt }, ?_, rfl⟩
  rw [Array.getElem?_eq_getElem h_lt, Array.getElem_setIfInBounds_self]

private theorem patch_foldl_preserves_size_local
    (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat)) :
    (List.foldl
      (fun acc (p : Nat × Nat) =>
        acc.set! p.fst { acc[p.fst]! with target := some p.snd })
      a ps).size = a.size := by
  induction ps generalizing a with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl]
    rw [ih, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

private theorem patch_foldl_unchanged_when_idx_not_in
    (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat))
    (pc : Nat) (h_no_idx : ∀ p ∈ ps, p.1 ≠ pc) :
    (List.foldl
      (fun acc (p : Nat × Nat) =>
        acc.set! p.fst { acc[p.fst]! with target := some p.snd })
      a ps)[pc]? = a[pc]? := by
  induction ps generalizing a with
  | nil => simp
  | cons p rest ih =>
    simp only [List.foldl]
    have h_p_neq : p.1 ≠ pc := h_no_idx p (by simp)
    rw [ih _ (fun q hq => h_no_idx q (by simp [hq]))]
    exact patch_one_other_index a p.1 p.2 pc (Ne.symm h_p_neq)

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
    apply ih
    · obtain ⟨instr, h_at, h_tgt⟩ := h_target
      rw [patch_one_other_index a p.1 p.2 idx (Ne.symm h_p_neq)]
      exact ⟨instr, h_at, h_tgt⟩
    · exact fun q hq => h_tail_no_idx q (by simp [hq])

private theorem last_occurrence_split
    (ps : List (Nat × Nat)) (pc : Nat)
    (h : ∃ p ∈ ps, p.1 = pc) :
    ∃ pre t suf, ps = pre ++ (pc, t) :: suf ∧
                 ∀ p ∈ suf, p.1 ≠ pc := by
  induction ps with
  | nil => obtain ⟨p, hp, _⟩ := h; cases hp
  | cons head rest ih =>
    by_cases h_rest : ∃ p ∈ rest, p.1 = pc
    · obtain ⟨pre', t', suf', h_eq', h_no_idx'⟩ := ih h_rest
      exact ⟨head :: pre', t', suf', by rw [List.cons_append, h_eq'], h_no_idx'⟩
    · -- ¬∃ p ∈ rest, p.1 = pc means ∀ p ∈ rest, p.1 ≠ pc.
      have h_rest' : ∀ p ∈ rest, p.1 ≠ pc :=
        fun p hp h_eq => h_rest ⟨p, hp, h_eq⟩
      by_cases h_head : head.1 = pc
      · exact ⟨[], head.2, rest, by simp; rw [← h_head], h_rest'⟩
      · obtain ⟨p, hp, h_eq⟩ := h
        rw [List.mem_cons] at hp
        rcases hp with h_phead | h_prest
        · exact absurd (h_phead ▸ h_eq) h_head
        · exact absurd h_eq (h_rest' p h_prest)

private theorem patch_foldl_target_at_last
    (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat))
    (pc t : Nat)
    (h_last_eq : ∃ pre suf, ps = pre ++ (pc, t) :: suf ∧
                            ∀ p ∈ suf, p.1 ≠ pc)
    (h_idx : pc < a.size) :
    ∃ instr,
      (List.foldl
        (fun acc (p : Nat × Nat) =>
          acc.set! p.fst { acc[p.fst]! with target := some p.snd })
        a ps)[pc]? = some instr ∧
      instr.target = some t := by
  obtain ⟨pre, suf, h_eq, h_suf_no_idx⟩ := h_last_eq
  rw [h_eq, List.foldl_append, List.foldl_cons]
  let a_pre := List.foldl
    (fun acc (p : Nat × Nat) =>
      acc.set! p.fst { acc[p.fst]! with target := some p.snd })
    a pre
  have h_idx_apre : pc < a_pre.size :=
    (patch_foldl_preserves_size_local a pre).symm ▸ h_idx
  obtain ⟨_, h_at_apre_set, h_target_apre_set⟩ := patch_one_target_local a_pre pc t h_idx_apre
  exact patch_foldl_target_preserved_when_idx_unique_in_tail
    (a_pre.set! pc { a_pre[pc]! with target := some t }) pc t suf
    ⟨_, h_at_apre_set, h_target_apre_set⟩ h_suf_no_idx

private theorem patch_foldl_target_some_in_list
    (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat))
    (pc t : Nat) (instr_pre instr_post : CProverGOTO.Instruction)
    (h_pre_at : a[pc]? = some instr_pre)
    (h_pre_target : instr_pre.target = none)
    (h_post_at :
      (List.foldl
        (fun acc (p : Nat × Nat) =>
          acc.set! p.fst { acc[p.fst]! with target := some p.snd })
        a ps)[pc]? = some instr_post)
    (h_post_target : instr_post.target = some t) :
    (pc, t) ∈ ps := by
  by_cases h_some : ∃ p ∈ ps, p.1 = pc
  · have h_idx_lt : pc < a.size :=
      (Array.getElem?_eq_some_iff.mp h_pre_at).1
    obtain ⟨pre, t', suf, h_eq, h_suf_no_idx⟩ := last_occurrence_split ps pc h_some
    obtain ⟨_, h_at_post', h_target_post'⟩ :=
      patch_foldl_target_at_last a ps pc t' ⟨pre, suf, h_eq, h_suf_no_idx⟩ h_idx_lt
    rw [h_at_post'] at h_post_at
    injection h_post_at with h_eq2
    rw [← h_eq2, h_target_post'] at h_post_target
    injection h_post_target with h_t_eq
    rw [h_eq, ← h_t_eq]
    exact List.mem_append_right pre (by simp)
  · -- ¬∃ p ∈ ps, p.1 = pc means ∀ p ∈ ps, p.1 ≠ pc.
    have h_no_idx : ∀ p ∈ ps, p.1 ≠ pc :=
      fun p hp h_eq => h_some ⟨p, hp, h_eq⟩
    rw [patch_foldl_unchanged_when_idx_not_in a ps pc h_no_idx, h_pre_at] at h_post_at
    injection h_post_at with h_eq
    rw [← h_eq, h_pre_target] at h_post_target
    cases h_post_target

/-- Reverse-direction patcher post-condition (top-level form). -/
theorem patchGotoTargets_target_some_in_patches
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (patches : List (Nat × Nat))
    (pc t : Nat) (instr_pre instr_post : Instruction)
    (h_pre_at : trans.instructions[pc]? = some instr_pre)
    (h_pre_target : instr_pre.target = none)
    (h_post_at : (Imperative.patchGotoTargets trans patches).instructions[pc]? = some instr_post)
    (h_post_target : instr_post.target = some t) :
    (pc, t) ∈ patches := by
  unfold Imperative.patchGotoTargets at h_post_at
  simp only at h_post_at
  exact patch_foldl_target_some_in_list trans.instructions patches pc t
    instr_pre instr_post h_pre_at h_pre_target h_post_at h_post_target

/-! ## Patches-fold reverse direction -/

theorem coreCFGToGotoPatchStep_no_contracts_resolved_reverse
    (labelMap : Std.HashMap String Nat)
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap ∅ acc idxLabel = Except.ok acc')
    (pc target : Nat) (h_in : (pc, target) ∈ acc'.1) :
    (pc, target) ∈ acc.1 ∨
    (pc = idxLabel.1 ∧ labelMap[idxLabel.2]? = some target) := by
  obtain ⟨resolvedPatches, trans⟩ := acc
  obtain ⟨idx, label⟩ := idxLabel
  obtain ⟨targetLoc, h_lookup⟩ :=
    coreCFGToGotoPatchStep_success_lookup labelMap ∅
      (resolvedPatches, trans) acc' (idx, label) h_run
  have h_acc'_eq : acc'.1 = (idx, targetLoc) :: resolvedPatches :=
    coreCFGToGotoPatchStep_no_contracts_resolvedPatches labelMap
      (resolvedPatches, trans) acc' (idx, label) targetLoc h_lookup h_run
  rw [h_acc'_eq] at h_in
  simp only [List.mem_cons] at h_in
  rcases h_in with h_eq | h_old
  · injection h_eq with h_pc h_target
    right
    refine ⟨h_pc, ?_⟩
    rw [h_target]; exact h_lookup
  · left; exact h_old

theorem patchesFoldlM_no_contracts_resolved_reverse
    (labelMap : Std.HashMap String Nat)
    (patches : List (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc')
    (pc target : Nat) (h_in : (pc, target) ∈ acc'.1) :
    (pc, target) ∈ acc.1 ∨
    ∃ label, (pc, label) ∈ patches ∧ labelMap[label]? = some target := by
  induction patches generalizing acc with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; left; exact h_in
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap ∅ acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      rcases ih acc₁ h_run with h_in_acc₁ | ⟨lbl, h_in_rest, h_lookup⟩
      · rcases coreCFGToGotoPatchStep_no_contracts_resolved_reverse
                labelMap acc acc₁ head h_step pc target h_in_acc₁
        with h_acc | ⟨h_pc, h_lookup⟩
        · left; exact h_acc
        · right
          refine ⟨head.2, ?_, h_lookup⟩
          obtain ⟨h₁, h₂⟩ := head
          subst h_pc
          exact List.mem_cons_self
      · right; exact ⟨lbl, by simp [h_in_rest], h_lookup⟩
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

theorem patchesFoldlM_no_contracts_resolved_reverse_array
    (labelMap : Std.HashMap String Nat)
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc')
    (pc target : Nat) (h_in : (pc, target) ∈ acc'.1) :
    (pc, target) ∈ acc.1 ∨
    ∃ label, (pc, label) ∈ patches ∧ labelMap[label]? = some target := by
  rw [← Array.foldlM_toList] at h_run
  rcases patchesFoldlM_no_contracts_resolved_reverse
    labelMap patches.toList acc acc' h_run pc target h_in
    with h | ⟨lbl, h_in', h_lookup⟩
  · left; exact h
  · right; exact ⟨lbl, Array.mem_toList_iff.mp h_in', h_lookup⟩

/-! ## labelMap keys are block labels -/

theorem coreCFGToGotoBlockStep_labelMap_key
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (label : String) (pc : Nat)
    (h_lookup : st'.labelMap[label]? = some pc) :
    label = lblBlk.1 ∨ st.labelMap[label]? = some pc := by
  rw [coreCFGToGotoBlockStep_labelMap fname lblBlk st st' h_run] at h_lookup
  rw [Std.HashMap.getElem?_insert] at h_lookup
  by_cases h : lblBlk.1 = label
  · left; exact h.symm
  · simp [h] at h_lookup
    right; exact h_lookup

theorem blocksFoldlM_labelMap_keys_subset
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (label : String) (pc : Nat)
    (h_lookup : st'.labelMap[label]? = some pc) :
    (∃ pc', st.labelMap[label]? = some pc') ∨
    label ∈ blocks.map Prod.fst := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; left; exact ⟨pc, h_lookup⟩
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      rcases ih st₁ h_run with ⟨pc₁, h_in_st₁⟩ | h_in_rest
      · rcases coreCFGToGotoBlockStep_labelMap_key fname head st st₁ h_step
                label pc₁ h_in_st₁ with h_eq | h_in_st
        · right; rw [h_eq]; exact List.mem_cons_self
        · left; exact ⟨pc₁, h_in_st⟩
      · right; exact List.mem_cons_of_mem _ h_in_rest
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

theorem blocksFoldlM_labelMap_keys_in_blocks
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (st_final : Strata.CoreCFGTransLoopState)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname)
              ({ trans := trans₀, pendingPatches := #[], labelMap := {},
                 loopContracts := {} } : Strata.CoreCFGTransLoopState)
            = Except.ok st_final)
    (label : String) (pc : Nat)
    (h_lookup : st_final.labelMap[label]? = some pc) :
    label ∈ blocks.map Prod.fst := by
  rcases blocksFoldlM_labelMap_keys_subset fname blocks _ st_final h_run label pc h_lookup
    with ⟨pc', h_init⟩ | h_block
  · -- Initial labelMap is empty, contradiction.
    have : (∅ : Std.HashMap String Nat)[label]? = some pc' := h_init
    rw [Std.HashMap.getElem?_empty] at this
    cases this
  · exact h_block

/-! ## Top-level theorems -/

/-- **Top-level theorem.** Given a successful run of
`coreCFGToGotoTransform`, every emitted GOTO instruction's target
value is a `labelMap` entry for some block in `cfg.blocks` (where
`labelMap` is the translator's hashmap-keyed labelMap). -/
theorem everyGotoTargetIsLabelMapEntry_of_translator_translatorMap
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_no_goto_target : NoGotoHasTarget trans₀)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    (st_final : Strata.CoreCFGTransLoopState)
    (h_blocks_run :
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀)
      = Except.ok st_final) :
    GotoTargetInRange.EveryGotoTargetIsLabelMapEntry cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      (hashMapToLabelMap st_final.labelMap) := by
  -- Decompose ans = patchGotoTargets trans_post resolved with trans_post = st_final.trans.
  obtain ⟨st_final', resolved, trans_post, h_blocks_run', h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  have h_st_final_eq : st_final = st_final' := by
    rw [h_blocks_run] at h_blocks_run'; injection h_blocks_run'
  subst h_st_final_eq
  have h_no_goto_target_st_final : NoGotoHasTarget' st_final.trans.instructions :=
    BlocksFoldClosed.of_blocks_run (P := NoGotoHasTarget') functionName cfg trans₀
      h_init_no_goto_target st_final h_blocks_run
  rw [h_loopContracts_empty_post st_final h_blocks_run] at h_patches_run
  have h_trans_post_eq : trans_post = st_final.trans :=
    patchesFoldlM_no_contracts_trans_eq st_final.labelMap st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
  intros pc target instr h_at h_ty h_target
  have h_at' : ans.instructions[pc]? = some instr := h_at
  rw [h_ans_eq] at h_at'
  -- Pre-patcher GOTO at pc had target = none (by NoGotoHasTarget'). Apply reverse-target.
  obtain ⟨instr_pre, h_pre_at, _, _, _, _⟩ :=
    patchGotoTargets_preserves_full_except_target trans_post resolved pc instr h_at'
  rw [h_trans_post_eq] at h_pre_at
  have h_pre_ty : instr_pre.type = .GOTO := by
    obtain ⟨_, h_at_pre', h_ty_eq⟩ :=
      patchGotoTargets_preserves_type trans_post resolved pc instr h_at'
    rw [h_trans_post_eq] at h_at_pre'; rw [h_at_pre'] at h_pre_at
    injection h_pre_at with h_inj; rw [← h_inj, ← h_ty_eq]; exact h_ty
  have h_in_resolved : (pc, target) ∈ resolved :=
    patchGotoTargets_target_some_in_patches trans_post resolved pc target
      instr_pre instr (by rw [h_trans_post_eq]; exact h_pre_at)
      (h_no_goto_target_st_final h_pre_at h_pre_ty)
      (by rw [← h_ans_eq]; exact h_at) h_target
  -- Reverse-trace (pc, target) ∈ resolved to a pendingPatch + labelMap lookup.
  rcases patchesFoldlM_no_contracts_resolved_reverse_array st_final.labelMap
    st_final.pendingPatches ([], st_final.trans) (resolved, trans_post)
    h_patches_run pc target h_in_resolved with h_in_acc | ⟨lbl, _, h_lookup⟩
  · simp at h_in_acc
  · -- lbl is a block label by blocksFoldlM_labelMap_keys_in_blocks.
    have h_lbl_in : lbl ∈ cfg.blocks.map Prod.fst :=
      blocksFoldlM_labelMap_keys_in_blocks functionName cfg.blocks trans₀ st_final
        (by simp [coreCFGToGotoInitState] at h_blocks_run; exact h_blocks_run) lbl _ h_lookup
    rw [List.mem_map] at h_lbl_in
    obtain ⟨⟨l', blk⟩, h_pair_in, h_pair_eq⟩ := h_lbl_in
    simp at h_pair_eq
    subst h_pair_eq
    exact ⟨l', blk, h_pair_in, h_lookup⟩

/-- **Top-level theorem (`wf.labelMap` form).** Given a bridge
`h_labelMap_agree` connecting `wf.labelMap` with the translator's
hashmap-keyed labelMap on `cfg.blocks` labels, every emitted GOTO
instruction's target value is a `wf.labelMap` entry for some block in
`cfg.blocks`. -/
theorem everyGotoTargetIsLabelMapEntry_of_translator
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_no_goto_target : NoGotoHasTarget trans₀)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    (st_final : Strata.CoreCFGTransLoopState)
    (h_blocks_run :
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀)
      = Except.ok st_final)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (wf : WellFormedTranslation cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      δ δ_goto δ_goto_bool)
    (h_labelMap_agree :
      ∀ l blk target, (l, blk) ∈ cfg.blocks →
        st_final.labelMap[l]? = some target →
        wf.labelMap l = some target) :
    GotoTargetInRange.EveryGotoTargetIsLabelMapEntry cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      wf.labelMap := by
  intros pc target instr h_at h_ty h_target
  obtain ⟨l, blk, h_in, h_lookup⟩ :=
    everyGotoTargetIsLabelMapEntry_of_translator_translatorMap
      Env functionName cfg trans₀ h_init_no_goto_target
      h_loopContracts_empty_post ans h_run st_final h_blocks_run
      h_at h_ty h_target
  exact ⟨l, blk, h_in, h_labelMap_agree l blk target h_in h_lookup⟩

end CProverGOTO.GotoTargetProvenance
