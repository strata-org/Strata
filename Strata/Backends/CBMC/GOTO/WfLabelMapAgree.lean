/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF
public import Strata.Backends.CBMC.GOTO.BlocksFoldClosed
public import Strata.Languages.Core.Procedure
import all Strata.DL.Imperative.ToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline

public section

/-! # R10a: discharge `h_labelMap_agree` from `WellFormedTranslation`

Proves that for any `WellFormedTranslation` over the translator's
output, `wf.labelMap` agrees with the translator's hashmap-keyed
labelMap on `cfg.blocks` labels.

The argument threads the invariant `LocationsTrackLabelMap` (every
LOCATION-with-`labels = [l]` in `trans.instructions` has its pc tracked
by `labelMap[l]?`) through the blocks-fold (only `emitLabel` emits
LOCATIONs; everything else pushes non-LOCATIONs) and the patcher
(which only writes targets). Combined with `wf.layout_location_labels`
(which gives a LOCATION at `wf.labelMap l` carrying `labels = [l]`),
the agreement falls out. -/

namespace CProverGOTO.WfLabelMapAgree

open Strata
open Imperative

/-! ## "LOCATIONs track labelMap" predicate -/

/-- Array-level: every LOCATION instruction in `a` with `labels = [l]`
has its pc tracked by `labelMap[l]?`. -/
def LocationsTrackLabelMap'
    (labelMap : Std.HashMap String Nat) (a : Array Instruction) : Prop :=
  ∀ {pc : Nat} {instr : Instruction} {l : String},
    a[pc]? = some instr →
    instr.type = .LOCATION → instr.labels = [l] →
    labelMap[l]? = some pc

/-- Transform-level (legacy public name). -/
@[expose] abbrev LocationsTrackLabelMap
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (labelMap : Std.HashMap String Nat) : Prop :=
  LocationsTrackLabelMap' labelMap trans.instructions

/-! ## Push/append preservation primitives -/

private theorem push_non_location_preserves
    (a : Array Instruction)
    (labelMap : Std.HashMap String Nat)
    (new_instr : Instruction)
    (h_inv : LocationsTrackLabelMap' labelMap a)
    (h_new : new_instr.type ≠ .LOCATION) :
    LocationsTrackLabelMap' labelMap (a.push new_instr) := by
  intro pc instr l h_at h_ty h_labels
  by_cases h_lt : pc < a.size
  · rw [Array.getElem?_push_lt h_lt] at h_at
    have h' : a[pc]? = some instr := by
      rw [Array.getElem?_eq_getElem h_lt]; exact h_at
    exact h_inv h' h_ty h_labels
  · by_cases h_eq : pc = a.size
    · subst h_eq
      rw [Array.getElem?_push_size] at h_at
      injection h_at with h_at
      subst h_at
      exact absurd h_ty h_new
    · have h_oor : (a.push new_instr).size ≤ pc := by
        rw [Array.size_push]; omega
      rw [Array.getElem?_eq_none h_oor] at h_at
      exact absurd h_at (by simp)

private theorem append_two_non_location_preserves
    (a : Array Instruction)
    (labelMap : Std.HashMap String Nat)
    (i₀ i₁ : Instruction)
    (h_inv : LocationsTrackLabelMap' labelMap a)
    (h0 : i₀.type ≠ .LOCATION) (h1 : i₁.type ≠ .LOCATION) :
    LocationsTrackLabelMap' labelMap (a ++ #[i₀, i₁]) := by
  intro pc instr l h_at h_ty h_labels
  by_cases h_lt : pc < a.size
  · rw [Array.getElem?_append_left h_lt] at h_at
    exact h_inv h_at h_ty h_labels
  · by_cases h_eq0 : pc = a.size
    · subst h_eq0
      rw [Array.getElem?_append_right (Nat.le_refl _)] at h_at
      simp at h_at
      subst h_at
      exact absurd h_ty h0
    · by_cases h_eq1 : pc = a.size + 1
      · subst h_eq1
        rw [Array.getElem?_append_right (Nat.le_add_right _ _)] at h_at
        simp at h_at
        subst h_at
        exact absurd h_ty h1
      · have h_oor : (a ++ #[i₀, i₁]).size ≤ pc := by
          rw [Array.size_append]
          simp; omega
        rw [Array.getElem?_eq_none h_oor] at h_at
        exact absurd h_at (by simp)

/-! ## Cmds-fold preservation (no LOCATION emitted)

The cmds-fold pushes only DECL / ASSIGN / ASSERT / ASSUME / FUNCTION_CALL
instructions — never LOCATION — so the shared
`BlocksFoldClosed.cmdsFoldlM_preserves_of_pushSafe` helper applies
(with `IsSafe := (· ≠ .LOCATION)`). The labelMap is fixed throughout. -/
theorem cmdsFoldlM_preserves
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (labelMap : Std.HashMap String Nat)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans)
    (h_inv : LocationsTrackLabelMap trans labelMap) :
    LocationsTrackLabelMap ans labelMap :=
  BlocksFoldClosed.cmdsFoldlM_preserves_of_pushSafe
    (P := LocationsTrackLabelMap' labelMap)
    (IsSafe := fun x => x.type ≠ InstructionType.LOCATION)
    (fun a x => push_non_location_preserves a labelMap x)
    (fun a x y => append_two_non_location_preserves a labelMap x y)
    (fun _ h_ty h_loc => by rw [h_loc] at h_ty; cases h_ty)
    (fun _ h_ty h_loc => by rw [h_loc] at h_ty; cases h_ty)
    (fun _ h_ty h_loc => by rw [h_loc] at h_ty; cases h_ty)
    (fun _ h_ty h_loc => by rw [h_loc] at h_ty; cases h_ty)
    (fun _ h_ty h_loc => by rw [h_loc] at h_ty; cases h_ty)
    fname cmds trans ans h_run h_inv

/-! ## Per-block step preservation -/

/-- `emitLabel` extends `trans` (with a new LOCATION at `trans.nextLoc`
carrying `labels = [label]`) and `labelMap` (insert
`(label, trans.nextLoc)`). The invariant is preserved. -/
theorem emitLabel_preserves
    (label : String) (srcLoc : CProverGOTO.SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (labelMap : Std.HashMap String Nat)
    (h_inv : LocationsTrackLabelMap trans labelMap)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_label_fresh : labelMap[label]? = none) :
    LocationsTrackLabelMap (Imperative.emitLabel label srcLoc trans)
      (labelMap.insert label trans.nextLoc) := by
  intro pc instr l h_at h_ty h_labels
  -- emitLabel definitionally pushes the LOCATION instruction below.
  change (trans.instructions.push
    { type := .LOCATION, locationNum := trans.nextLoc, sourceLoc := srcLoc,
      labels := [label], code := CProverGOTO.Code.skip })[pc]? = some instr at h_at
  by_cases h_lt : pc < trans.instructions.size
  · rw [Array.getElem?_push_lt h_lt] at h_at
    have h_at' : trans.instructions[pc]? = some instr := by
      rw [Array.getElem?_eq_getElem h_lt]; exact h_at
    have h_old : labelMap[l]? = some pc := h_inv h_at' h_ty h_labels
    by_cases h_l_eq : l = label
    · subst h_l_eq; rw [h_label_fresh] at h_old; cases h_old
    · rw [Std.HashMap.getElem?_insert]
      have h_neq : ¬ label = l := fun h => h_l_eq h.symm
      simp [h_neq]; exact h_old
  · by_cases h_eq : pc = trans.instructions.size
    · subst h_eq
      rw [Array.getElem?_push_size] at h_at
      injection h_at with h_at
      subst h_at
      simp at h_labels
      subst h_labels
      rw [Std.HashMap.getElem?_insert]
      simp; exact h_size.symm
    · have h_oor : (trans.instructions.push
        ({ type := .LOCATION, locationNum := trans.nextLoc, sourceLoc := srcLoc,
           labels := [label], code := CProverGOTO.Code.skip } : Instruction)).size ≤ pc := by
        rw [Array.size_push]; omega
      rw [Array.getElem?_eq_none h_oor] at h_at
      exact absurd h_at (by simp)

/-! ## Block-step + blocks-fold preservation

The block-step composes `emitLabel`, `cmdsFoldlM_preserves`, and a
non-LOCATION transfer push (GOTO×2 or END_FUNCTION). -/

theorem coreCFGToGotoBlockStep_preserves
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_inv : LocationsTrackLabelMap st.trans st.labelMap)
    (h_label_fresh : st.labelMap[lblBlk.1]? = none) :
    LocationsTrackLabelMap st'.trans st'.labelMap := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  have h_inv_after_label :
      LocationsTrackLabelMap
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname } st.trans)
        (st.labelMap.insert label st.trans.nextLoc) :=
    emitLabel_preserves label _ st.trans st.labelMap h_inv h_size h_label_fresh
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_inv_after_cmds : LocationsTrackLabelMap trans₂
        (st.labelMap.insert label st.trans.nextLoc) :=
      cmdsFoldlM_preserves fname blk.cmds _ trans₂ _ h_inner h_inv_after_label
    have h_GOTO : InstructionType.GOTO ≠ InstructionType.LOCATION := by decide
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
        intro pc instr l h_at h_ty h_labels
        let srcLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText
        let trans₃ := (Imperative.emitCondGoto cond_expr.not srcLoc trans₂).fst
        have h_invc : LocationsTrackLabelMap trans₃
            (st.labelMap.insert label st.trans.nextLoc) :=
          push_non_location_preserves trans₂.instructions _ _ h_inv_after_cmds h_GOTO
        change (trans₃.instructions.push _)[pc]? = some instr at h_at
        exact push_non_location_preserves trans₃.instructions _ _ h_invc h_GOTO h_at h_ty h_labels
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      intro pc instr l h_at h_ty h_labels
      have h_EF : InstructionType.END_FUNCTION ≠ InstructionType.LOCATION := by decide
      change (trans₂.instructions.push _)[pc]? = some instr at h_at
      exact push_non_location_preserves trans₂.instructions _ _ h_inv_after_cmds
        h_EF h_at h_ty h_labels
  | .error _, _ => simp at h_run

theorem blocksFoldlM_preserves
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_inv : LocationsTrackLabelMap st.trans st.labelMap)
    (h_distinct : BlockLabelsDistinct blocks)
    (h_no_blocks_in_init : ∀ p ∈ blocks, st.labelMap[p.1]? = none) :
    LocationsTrackLabelMap st'.trans st'.labelMap := by
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
      have h_inv₁ : LocationsTrackLabelMap st₁.trans st₁.labelMap :=
        coreCFGToGotoBlockStep_preserves fname hd st st₁
          (h_admitted hd (by simp)) h_step h_size h_inv
          (h_no_blocks_in_init hd (by simp))
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname hd st st₁
          (h_admitted hd (by simp)) h_step h_size
      -- For rest's head labels: each was distinct from hd.1 (by h_distinct),
      -- so their lookups in st₁.labelMap = (st.labelMap.insert hd.1 _) are
      -- the same as in st.labelMap.
      have h_lbl₁ : st₁.labelMap = st.labelMap.insert hd.1 st.trans.nextLoc :=
        coreCFGToGotoBlockStep_labelMap fname hd st st₁ h_step
      have h_no_blocks_in_st₁ : ∀ p ∈ rest, st₁.labelMap[p.1]? = none := by
        intro p h_p_in
        have h_neq : hd.1 ≠ p.1 :=
          BlockLabelsDistinct_head_neq_tail hd rest h_distinct p h_p_in
        rw [h_lbl₁, Std.HashMap.getElem?_insert]
        rw [if_neg (by simp; exact h_neq)]
        exact h_no_blocks_in_init p (List.mem_cons_of_mem hd h_p_in)
      intro pc instr l h_at h_ty h_labels
      exact ih st₁ (fun lblBlk h_lb => h_admitted lblBlk (by simp [h_lb])) h_run
        h_size₁ h_inv₁ (BlockLabelsDistinct_tail hd rest h_distinct) h_no_blocks_in_st₁
        h_at h_ty h_labels
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ## Patcher preservation -/

theorem patchGotoTargets_preserves
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (resolved : List (Nat × Nat))
    (labelMap : Std.HashMap String Nat)
    (h_inv : LocationsTrackLabelMap trans labelMap) :
    LocationsTrackLabelMap (Imperative.patchGotoTargets trans resolved) labelMap := by
  intro pc instr l h_at h_ty h_labels
  obtain ⟨instr_pre, h_at_pre, h_ty_eq⟩ :=
    patchGotoTargets_preserves_type trans resolved pc instr h_at
  obtain ⟨instr_pre', h_at_pre', h_lab_eq⟩ :=
    patchGotoTargets_preserves_labels trans resolved pc instr h_at
  have h_pre_eq : instr_pre = instr_pre' := by
    rw [h_at_pre] at h_at_pre'; injection h_at_pre'
  exact h_inv h_at_pre (by rw [← h_ty_eq]; exact h_ty)
    (by rw [h_pre_eq, ← h_lab_eq]; exact h_labels)

/-! ## Top-level theorem: labelMap-agreement for arbitrary WF -/

/-- **R10a's main theorem.** For any `WellFormedTranslation` over the
translator's output `ans`, its `labelMap` agrees with the translator's
hashmap-keyed `labelMap` on `cfg.blocks` labels.

The argument: any wf has, at `wf.labelMap l = some pc1`, a LOCATION
with `labels = [l]` (by `wf.layout_location_labels`). The translator's
output's LOCATIONs all track the hashmap-keyed labelMap (by
`blocksFoldlM_preserves` + `patchGotoTargets_preserves`). So
`hashMap[l]? = some pc1`, equating with the given `hashMap[l]? = some
target` to give `pc1 = target`. -/
theorem labelMap_agree_of_translator
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_no_location :
      ∀ {pc : Nat} {instr : Instruction},
        trans₀.instructions[pc]? = some instr → instr.type ≠ .LOCATION)
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
      δ δ_goto δ_goto_bool) :
    ∀ l blk target, (l, blk) ∈ cfg.blocks →
      st_final.labelMap[l]? = some target →
      wf.labelMap l = some target := by
  intro l blk target h_in h_lookup
  -- Step 1: get wf.labelMap l = some pc1 + the LOCATION at pc1 with labels [l].
  rcases h_pc1 : wf.labelMap l with _ | pc1
  · have := wf.labelMap_total l (List.mem_map.mpr ⟨(l, blk), h_in, rfl⟩)
    rw [h_pc1] at this; cases this
  obtain ⟨instr1, h_at1, h_ty1, h_lab1⟩ :=
    wf.layout_location_labels l blk pc1 h_in h_pc1
  -- Step 2: build LocationsTrackLabelMap for st_final.trans via blocksFoldlM_preserves.
  have h_inv_init : LocationsTrackLabelMap (coreCFGToGotoInitState trans₀).trans
                      (coreCFGToGotoInitState trans₀).labelMap := by
    intro pc instr l' h h_ty _
    show (∅ : Std.HashMap String Nat)[l']? = some pc
    exact absurd h_ty (h_init_no_location h)
  have h_inv_st_final : LocationsTrackLabelMap st_final.trans st_final.labelMap :=
    blocksFoldlM_preserves functionName cfg.blocks _ st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb) h_blocks_run
      (by simp [coreCFGToGotoInitState]; exact h_init_size)
      h_inv_init h_distinct (fun _ _ => Std.HashMap.getElem?_empty)
  -- Step 3: extend through the patcher to ans (= patchGotoTargets st_final.trans resolved).
  obtain ⟨st_final', resolved, trans_post, h_blocks_run', h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  have h_st_final_eq : st_final = st_final' := by
    rw [h_blocks_run] at h_blocks_run'; injection h_blocks_run'
  subst h_st_final_eq
  rw [h_loopContracts_empty_post st_final h_blocks_run] at h_patches_run
  have h_trans_post_eq : trans_post = st_final.trans :=
    patchesFoldlM_no_contracts_trans_eq st_final.labelMap st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
  have h_inv_ans : LocationsTrackLabelMap (Imperative.patchGotoTargets st_final.trans resolved)
      st_final.labelMap :=
    patchGotoTargets_preserves st_final.trans resolved _ h_inv_st_final
  -- Step 4: apply h_inv_ans to instr1 at pc1 to get st_final.labelMap[l]? = some pc1.
  have h_at1_post : (Imperative.patchGotoTargets st_final.trans resolved).instructions[pc1]?
                     = some instr1 := by
    have : ans.instructions[pc1]? = some instr1 := h_at1
    rw [h_ans_eq, h_trans_post_eq] at this; exact this
  have h_eq : pc1 = target := by
    have := (h_inv_ans h_at1_post h_ty1 h_lab1).symm.trans h_lookup
    injection this
  rw [h_eq]

end CProverGOTO.WfLabelMapAgree
