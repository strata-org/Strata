/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF
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

/-- For every LOCATION instruction in `trans.instructions`, if its
`labels` field is `[l]` then `labelMap[l]?` resolves to its pc. -/
@[expose] def LocationsTrackLabelMap
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (labelMap : Std.HashMap String Nat) : Prop :=
  ∀ {pc : Nat} {instr : Instruction} {l : String},
    trans.instructions[pc]? = some instr →
    instr.type = .LOCATION → instr.labels = [l] →
    labelMap[l]? = some pc

/-! ## Push/append preservation primitives -/

/-- Pushing one non-LOCATION instruction preserves
`LocationsTrackLabelMap`. -/
private theorem push_non_location_preserves
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (labelMap : Std.HashMap String Nat)
    (new_instr : Instruction)
    (h_inv : LocationsTrackLabelMap trans labelMap)
    (h_new : new_instr.type ≠ .LOCATION) :
    ∀ {pc : Nat} {instr : Instruction} {l : String},
      (trans.instructions.push new_instr)[pc]? = some instr →
      instr.type = .LOCATION → instr.labels = [l] →
      labelMap[l]? = some pc := by
  intro pc instr l h_at h_ty h_labels
  by_cases h_lt : pc < trans.instructions.size
  · rw [Array.getElem?_push_lt h_lt] at h_at
    have h' : trans.instructions[pc]? = some instr := by
      rw [Array.getElem?_eq_getElem h_lt]; exact h_at
    exact h_inv h' h_ty h_labels
  · by_cases h_eq : pc = trans.instructions.size
    · subst h_eq
      rw [Array.getElem?_push_size] at h_at
      injection h_at with h_at
      subst h_at
      exact absurd h_ty h_new
    · have h_oor : (trans.instructions.push new_instr).size ≤ pc := by
        rw [Array.size_push]; omega
      rw [Array.getElem?_eq_none h_oor] at h_at
      exact absurd h_at (by simp)

/-- Appending two non-LOCATION instructions preserves
`LocationsTrackLabelMap`. -/
private theorem append_two_non_location_preserves
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (labelMap : Std.HashMap String Nat)
    (i₀ i₁ : Instruction)
    (h_inv : LocationsTrackLabelMap trans labelMap)
    (h0 : i₀.type ≠ .LOCATION) (h1 : i₁.type ≠ .LOCATION) :
    ∀ {pc : Nat} {instr : Instruction} {l : String},
      (trans.instructions.append #[i₀, i₁])[pc]? = some instr →
      instr.type = .LOCATION → instr.labels = [l] →
      labelMap[l]? = some pc := by
  intro pc instr l h_at h_ty h_labels
  have h_eq : trans.instructions.append #[i₀, i₁]
      = trans.instructions ++ #[i₀, i₁] := rfl
  rw [h_eq] at h_at
  by_cases h_lt : pc < trans.instructions.size
  · rw [Array.getElem?_append_left h_lt] at h_at
    exact h_inv h_at h_ty h_labels
  · by_cases h_eq0 : pc = trans.instructions.size
    · subst h_eq0
      rw [Array.getElem?_append_right (Nat.le_refl _)] at h_at
      simp at h_at
      subst h_at
      exact absurd h_ty h0
    · by_cases h_eq1 : pc = trans.instructions.size + 1
      · subst h_eq1
        rw [Array.getElem?_append_right (Nat.le_add_right _ _)] at h_at
        simp at h_at
        subst h_at
        exact absurd h_ty h1
      · have h_oor : (trans.instructions ++ #[i₀, i₁]).size ≤ pc := by
          rw [Array.size_append]
          simp; omega
        rw [Array.getElem?_eq_none h_oor] at h_at
        exact absurd h_at (by simp)

/-! ## Per-cmd step preservation: cmds emit no LOCATION -/

/-- `Cmd.toGotoInstructions` for an admitted cmd preserves
`LocationsTrackLabelMap`: it pushes only DECL / ASSIGN / ASSERT /
ASSUME instructions, never LOCATION. -/
theorem toGotoInstructions_preserves
    (T : Core.Expression.TyEnv) (fname : String)
    (c : Imperative.Cmd Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (labelMap : Std.HashMap String Nat)
    (h_run : Imperative.Cmd.toGotoInstructions T fname c trans = Except.ok ans)
    (h_inv : LocationsTrackLabelMap trans labelMap) :
    LocationsTrackLabelMap ans labelMap := by
  -- Helper: for the single-push cases, given `h_inst : ans.instructions = trans.instructions.push i`
  -- and `h_ty : i.type = T` for some non-LOCATION T, the result follows from
  -- `push_non_location_preserves`.
  intro pc instr l h h_ty h_labels
  cases c with
  | init v ty initVal md =>
    cases initVal with
    | det e =>
      obtain ⟨_, _, i_decl, i_assn, _, _, h_decl_ty, _, _, h_assn_ty, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
      rw [h_inst] at h
      exact append_two_non_location_preserves trans labelMap i_decl i_assn h_inv
        (by rw [h_decl_ty]; decide) (by rw [h_assn_ty]; decide) h h_ty h_labels
    | nondet =>
      obtain ⟨_, i_decl, _, h_decl_ty, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
      rw [h_inst] at h
      exact push_non_location_preserves trans labelMap i_decl h_inv
        (by rw [h_decl_ty]; decide) h h_ty h_labels
  | set v src md =>
    cases src with
    | det e =>
      obtain ⟨_, _, i_assn, _, _, h_assn_ty, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
      rw [h_inst] at h
      exact push_non_location_preserves trans labelMap i_assn h_inv
        (by rw [h_assn_ty]; decide) h h_ty h_labels
    | nondet =>
      obtain ⟨_, i_assn, _, h_assn_ty, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
      rw [h_inst] at h
      exact push_non_location_preserves trans labelMap i_assn h_inv
        (by rw [h_assn_ty]; decide) h h_ty h_labels
  | assert label e md =>
    obtain ⟨_, i, _, h_assert_ty, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
    rw [h_inst] at h
    exact push_non_location_preserves trans labelMap i h_inv
      (by rw [h_assert_ty]; decide) h h_ty h_labels
  | assume label e md =>
    obtain ⟨_, i, _, h_assume_ty, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
    rw [h_inst] at h
    exact push_non_location_preserves trans labelMap i h_inv
      (by rw [h_assume_ty]; decide) h h_ty h_labels
  | cover label e md =>
    -- `cover` emits an ASSERT — never LOCATION.
    unfold Imperative.Cmd.toGotoInstructions at h_run
    simp only at h_run
    match h_expr : Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      subst h_run
      let assert_inst : Instruction :=
        { type := .ASSERT, locationNum := trans.nextLoc,
          sourceLoc := metadataToSourceLoc md fname trans.sourceText
            (comment := md.getPropertySummary.getD s!"cover {label}"),
          guard := e_goto }
      have h' : (trans.instructions.push assert_inst)[pc]? = some instr := h
      exact push_non_location_preserves trans labelMap assert_inst h_inv
        (show InstructionType.ASSERT ≠ InstructionType.LOCATION by decide) h' h_ty h_labels
    | .error _ =>
      simp [h_expr, Bind.bind, Except.bind] at h_run

/-! ## Preservation through `coreCFGToGotoCmdStep` (admitted-fragment) -/

theorem coreCFGToGotoCmdStep_preserves
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (labelMap : Std.HashMap String Nat)
    (h_admitted : Core.CmdExt.isAdmittedCmd cmd = true)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans)
    (h_inv : LocationsTrackLabelMap trans labelMap) :
    LocationsTrackLabelMap ans labelMap := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact toGotoInstructions_preserves trans.T fname c trans ans labelMap h_run h_inv
  | call procName callArgs md =>
    -- `.call` is not admitted.
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-- The cmds-fold (admitted-fragment) preserves the invariant. -/
theorem cmdsFoldlM_preserves
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (labelMap : Std.HashMap String Nat)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans)
    (h_inv : LocationsTrackLabelMap trans labelMap) :
    LocationsTrackLabelMap ans labelMap := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_inv
  | cons hd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans hd with
    | .ok trans₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_inv₁ : LocationsTrackLabelMap trans₁ labelMap :=
        coreCFGToGotoCmdStep_preserves fname hd trans trans₁ labelMap
          (h_admitted hd (by simp)) h_step h_inv
      intro pc instr l h_at h_ty h_labels
      exact ih trans₁ (fun c hc => h_admitted c (by simp [hc])) h_run h_inv₁
        h_at h_ty h_labels
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

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

/-! ## Outer block / blocks step preservation

The block-step composes `emitLabel`, `cmdsFoldlM_preserves`, and a
non-LOCATION transfer push (either two GOTOs from `condGoto` or one
END_FUNCTION from `finish`). All three preserve the invariant. -/

/-- `coreCFGToGotoBlockStep` preserves the invariant. -/
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
  -- After emitLabel, the labelMap is `st.labelMap.insert label st.trans.nextLoc`.
  -- This is what `st'` will eventually carry.
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
    have h_inv_after_cmds :
        LocationsTrackLabelMap trans₂
          (st.labelMap.insert label st.trans.nextLoc) :=
      cmdsFoldlM_preserves fname blk.cmds _ trans₂
        (st.labelMap.insert label st.trans.nextLoc)
        h_admitted h_inner h_inv_after_label
    -- Transfer push (GOTO×2 or END_FUNCTION). Both are non-LOCATION.
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
        -- The transfer pushes two GOTO instructions (cond + uncond). Both
        -- are non-LOCATION; reduce to push_non_location_preserves twice.
        let srcLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText
        let cond_inst : Instruction :=
          { type := .GOTO, locationNum := trans₂.nextLoc,
            sourceLoc := srcLoc, guard := cond_expr.not, target := none }
        let trans₃ := (Imperative.emitCondGoto cond_expr.not srcLoc trans₂).fst
        let uncond_inst : Instruction :=
          { type := .GOTO, locationNum := trans₃.nextLoc,
            sourceLoc := srcLoc, guard := CProverGOTO.Expr.true, target := none }
        have h_invc : LocationsTrackLabelMap trans₃
            (st.labelMap.insert label st.trans.nextLoc) := by
          intro pc' instr' l' h_at' h_ty' h_labels'
          change (trans₂.instructions.push cond_inst)[pc']? = some instr' at h_at'
          exact push_non_location_preserves trans₂ _ cond_inst h_inv_after_cmds
            (show InstructionType.GOTO ≠ InstructionType.LOCATION by decide)
            h_at' h_ty' h_labels'
        change ((Imperative.emitUncondGoto _ _).fst).instructions[pc]? = some instr at h_at
        change (st.labelMap.insert label st.trans.nextLoc)[l]? = some pc
        change (trans₃.instructions.push uncond_inst)[pc]? = some instr at h_at
        exact push_non_location_preserves trans₃ _ uncond_inst h_invc
          (show InstructionType.GOTO ≠ InstructionType.LOCATION by decide)
          h_at h_ty h_labels
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      intro pc instr l h_at h_ty h_labels
      change (trans₂.instructions.push (endFunctionInstr md fname trans₂))[pc]? = some instr at h_at
      change (st.labelMap.insert label st.trans.nextLoc)[l]? = some pc
      exact push_non_location_preserves trans₂ _ (endFunctionInstr md fname trans₂)
        h_inv_after_cmds
        (show InstructionType.END_FUNCTION ≠ InstructionType.LOCATION by decide)
        h_at h_ty h_labels
  | .error _, _ => simp at h_run

/-- `blocksFoldlM` preserves the invariant, given the freshness
hypothesis for each head label. -/
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

/-- The patcher preserves the invariant: it writes only `target`, and
the type/labels are preserved. The labelMap is unchanged by patching. -/
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
  -- Step 1: get wf.labelMap l = some pc1 by total + layout_location_labels.
  have h_l_in : l ∈ cfg.blocks.map Prod.fst := by
    rw [List.mem_map]; exact ⟨(l, blk), h_in, rfl⟩
  rcases h_pc1 : wf.labelMap l with _ | pc1
  · have := wf.labelMap_total l h_l_in
    rw [h_pc1] at this; cases this
  obtain ⟨instr1, h_at1, h_ty1, h_lab1⟩ :=
    wf.layout_location_labels l blk pc1 h_in h_pc1
  -- Step 2: build the LocationsTrackLabelMap invariant for ans.instructions.
  have h_inv_init : LocationsTrackLabelMap (coreCFGToGotoInitState trans₀).trans
                      (coreCFGToGotoInitState trans₀).labelMap := by
    intro pc instr l' h h_ty _
    show (∅ : Std.HashMap String Nat)[l']? = some pc
    exact absurd h_ty (h_init_no_location h)
  have h_inv_st_final : LocationsTrackLabelMap st_final.trans st_final.labelMap :=
    blocksFoldlM_preserves functionName cfg.blocks _ st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb)
      h_blocks_run
      (by simp [coreCFGToGotoInitState]; exact h_init_size)
      h_inv_init h_distinct
      (fun p _ => Std.HashMap.getElem?_empty)
  -- Step 3: extend through the patcher to ans.
  -- ans = patchGotoTargets trans_post resolved where trans_post = st_final.trans
  -- under the empty-loopContracts hypothesis.
  obtain ⟨st_final', resolved, trans_post, h_blocks_run', h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  have h_st_final_eq : st_final = st_final' := by
    rw [h_blocks_run] at h_blocks_run'; injection h_blocks_run'
  subst h_st_final_eq
  rw [h_loopContracts_empty_post st_final h_blocks_run] at h_patches_run
  have h_trans_post_eq : trans_post = st_final.trans :=
    patchesFoldlM_no_contracts_trans_eq st_final.labelMap st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
  have h_inv_ans :
      LocationsTrackLabelMap (Imperative.patchGotoTargets st_final.trans resolved)
        st_final.labelMap :=
    patchGotoTargets_preserves st_final.trans resolved _ h_inv_st_final
  -- Step 4: instr1 at pc1 in ans.instructions has labels [l]. Apply h_inv_ans.
  have h_at1_post : (Imperative.patchGotoTargets st_final.trans resolved).instructions[pc1]?
                     = some instr1 := by
    have : ans.instructions[pc1]? = some instr1 := h_at1
    rw [h_ans_eq, h_trans_post_eq] at this; exact this
  have h_lookup_pc1 : st_final.labelMap[l]? = some pc1 :=
    h_inv_ans h_at1_post h_ty1 h_lab1
  -- Step 5: combine with h_lookup : st_final.labelMap[l]? = some target.
  have h_eq : pc1 = target := by
    have := h_lookup_pc1.symm.trans h_lookup; injection this
  rw [h_eq]

end CProverGOTO.WfLabelMapAgree
