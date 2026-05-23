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

Round-10a deliverable: prove the universal-form labelMap-agreement
hypothesis that R8a left as a parameter on
`coreCFGToGotoTransform_forward_simulation_concrete_v6`:

```
∀ (wf : WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool),
∀ l blk target, (l, blk) ∈ cfg.blocks →
  st_final.labelMap[l]? = some target →
  wf.labelMap l = some target
```

i.e., for **any** WF on the translator output, the labelMap agrees with
the translator's hashmap-keyed labelMap on `cfg.blocks` labels.

## Strategy

Closing this for arbitrary `wf` requires the new
`wf.layout_location_labels` field (R10a step 1, in
`CoreCFGToGOTOInvariants.lean`):

* `wf.layout_location_labels l blk pc1` gives an instruction at `pc1`
  with `type = .LOCATION` and `labels = [l]`.
* From the translator's structure (`blocksFoldlM_layout_location_with_labels`
  + `patchGotoTargets_preserves_labels`), the LOCATION at
  `hashMapToLabelMap st_final.labelMap l` carries `labels = [l]`.

To force `pc1 = pc2`, we need: **at most one LOCATION instruction in
`ans.instructions` carries `labels = [l]`** for each `l`.

This uniqueness follows from a structural induction over the
translator's outer loop, threading the invariant
`LocationsTrackLabelMap`: every LOCATION-with-labels-`[l]` in
`st.trans.instructions` has its pc tracked by `st.labelMap[l]?`. The
inner cmds-fold and the transfer push emit no LOCATIONs (only
DECL/ASSIGN/ASSERT/ASSUME/GOTO/END_FUNCTION); the only LOCATION
emission is `emitLabel`, which inserts the new label/pc pair into the
labelMap atomically.

Composing with `patchGotoTargets_preserves_labels` (which trivially
preserves the invariant since the patcher writes only `target`),
we conclude that for `(l, blk) ∈ cfg.blocks`, the unique
LOCATION-with-labels-`[l]` in `ans.instructions` has
`pc = hashMapToLabelMap st_final.labelMap l`. -/

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
  · have h_ge : trans.instructions.size ≤ pc := Nat.le_of_not_lt h_lt
    by_cases h_eq : pc = trans.instructions.size
    · subst h_eq
      rw [Array.getElem?_push_size] at h_at
      injection h_at with h_at
      subst h_at
      exact absurd h_ty h_new
    · have h_lt' : trans.instructions.size < pc := by omega
      have h_oor : (trans.instructions.push new_instr).size ≤ pc := by
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
  cases c with
  | init v ty initVal md =>
    cases initVal with
    | det e =>
      obtain ⟨_gty, _e_goto, i_decl, i_assn,
              _, _, h_decl_ty, _, _, h_assn_ty, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
      intro pc instr l h h_ty h_labels
      rw [h_inst] at h
      have h_decl_nl : i_decl.type ≠ .LOCATION := by rw [h_decl_ty]; decide
      have h_assn_nl : i_assn.type ≠ .LOCATION := by rw [h_assn_ty]; decide
      exact append_two_non_location_preserves trans labelMap i_decl i_assn h_inv
        h_decl_nl h_assn_nl h h_ty h_labels
    | nondet =>
      obtain ⟨_gty, i_decl, _, h_decl_ty, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
      intro pc instr l h h_ty h_labels
      rw [h_inst] at h
      have h_decl_nl : i_decl.type ≠ .LOCATION := by rw [h_decl_ty]; decide
      exact push_non_location_preserves trans labelMap i_decl h_inv h_decl_nl h h_ty h_labels
  | set v src md =>
    cases src with
    | det e =>
      obtain ⟨_gty, _e_goto, i_assn, _, _, h_assn_ty, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
      intro pc instr l h h_ty h_labels
      rw [h_inst] at h
      have h_assn_nl : i_assn.type ≠ .LOCATION := by rw [h_assn_ty]; decide
      exact push_non_location_preserves trans labelMap i_assn h_inv h_assn_nl h h_ty h_labels
    | nondet =>
      obtain ⟨_gty, i_assn, _, h_assn_ty, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
      intro pc instr l h h_ty h_labels
      rw [h_inst] at h
      have h_assn_nl : i_assn.type ≠ .LOCATION := by rw [h_assn_ty]; decide
      exact push_non_location_preserves trans labelMap i_assn h_inv h_assn_nl h h_ty h_labels
  | assert label e md =>
    obtain ⟨_e_goto, i, _, h_assert_ty, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
    intro pc instr l h h_ty h_labels
    rw [h_inst] at h
    have h_assert_nl : i.type ≠ .LOCATION := by rw [h_assert_ty]; decide
    exact push_non_location_preserves trans labelMap i h_inv h_assert_nl h h_ty h_labels
  | assume label e md =>
    obtain ⟨_e_goto, i, _, h_assume_ty, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
    intro pc instr l h h_ty h_labels
    rw [h_inst] at h
    have h_assume_nl : i.type ≠ .LOCATION := by rw [h_assume_ty]; decide
    exact push_non_location_preserves trans labelMap i h_inv h_assume_nl h h_ty h_labels
  | cover label e md =>
    -- `cover` emits an ASSERT — never LOCATION.
    unfold Imperative.Cmd.toGotoInstructions at h_run
    simp only at h_run
    match h_expr :
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      intro pc instr l h h_ty h_labels
      subst h_run
      let assert_inst : Instruction :=
        { type := .ASSERT, locationNum := trans.nextLoc,
          sourceLoc := metadataToSourceLoc md fname trans.sourceText
            (comment := md.getPropertySummary.getD s!"cover {label}"),
          guard := e_goto }
      have h' : (trans.instructions.push assert_inst)[pc]? = some instr := h
      have h_assert_nl : assert_inst.type ≠ .LOCATION := by
        show InstructionType.ASSERT ≠ InstructionType.LOCATION
        decide
      exact push_non_location_preserves trans labelMap assert_inst h_inv h_assert_nl h' h_ty h_labels
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
      have h_admitted_hd : Core.CmdExt.isAdmittedCmd hd = true := h_admitted hd (by simp)
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      have h_inv₁ : LocationsTrackLabelMap trans₁ labelMap :=
        coreCFGToGotoCmdStep_preserves fname hd trans trans₁ labelMap
          h_admitted_hd h_step h_inv
      intro pc instr l h_at h_ty h_labels
      exact ih trans₁ h_admitted_rest h_run h_inv₁ h_at h_ty h_labels
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ## Per-block step preservation -/

/-- `emitLabel` extends both `trans` (with a new LOCATION at
`trans.nextLoc` carrying `labels = [label]`) and `labelMap` (insert
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
  -- emitLabel pushes a single LOCATION instruction.
  have h_emit_unfold :
      (Imperative.emitLabel label srcLoc trans).instructions =
      trans.instructions.push
        { type := .LOCATION, locationNum := trans.nextLoc,
          sourceLoc := srcLoc, labels := [label],
          code := CProverGOTO.Code.skip } := rfl
  rw [h_emit_unfold] at h_at
  by_cases h_lt : pc < trans.instructions.size
  · -- pc is in the old prefix. The instruction is unchanged.
    rw [Array.getElem?_push_lt h_lt] at h_at
    have h_at' : trans.instructions[pc]? = some instr := by
      rw [Array.getElem?_eq_getElem h_lt]; exact h_at
    have h_old : labelMap[l]? = some pc := h_inv h_at' h_ty h_labels
    -- After insert: if l ≠ label, lookup is unchanged.
    by_cases h_l_eq : l = label
    · -- l = label: but labelMap[label]? = none, contradiction with h_old.
      subst h_l_eq
      rw [h_label_fresh] at h_old
      cases h_old
    · rw [Std.HashMap.getElem?_insert]
      have h_neq : ¬ label = l := fun h => h_l_eq h.symm
      simp [h_neq]; exact h_old
  · -- pc is at the new push position.
    have h_ge : trans.instructions.size ≤ pc := Nat.le_of_not_lt h_lt
    by_cases h_eq : pc = trans.instructions.size
    · subst h_eq
      rw [Array.getElem?_push_size] at h_at
      injection h_at with h_at
      -- instr is the new LOCATION with labels [label].
      subst h_at
      simp at h_labels
      subst h_labels
      -- l = label, pc = trans.instructions.size = trans.nextLoc.
      rw [Std.HashMap.getElem?_insert]
      simp; exact h_size.symm
    · have h_lt' : trans.instructions.size < pc := by omega
      have h_oor : (trans.instructions.push
        ({ type := .LOCATION, locationNum := trans.nextLoc,
           sourceLoc := srcLoc, labels := [label],
           code := CProverGOTO.Code.skip } : Instruction)).size ≤ pc := by
        rw [Array.size_push]; omega
      rw [Array.getElem?_eq_none h_oor] at h_at
      exact absurd h_at (by simp)

/-- `emitCondGoto`'s push is a GOTO, not LOCATION; the invariant is
preserved. The labelMap is unchanged. -/
theorem emitCondGoto_preserves
    (guard : CProverGOTO.Expr) (srcLoc : CProverGOTO.SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (labelMap : Std.HashMap String Nat)
    (h_inv : LocationsTrackLabelMap trans labelMap) :
    LocationsTrackLabelMap (Imperative.emitCondGoto guard srcLoc trans).fst
      labelMap := by
  intro pc instr l h_at h_ty h_labels
  let new_instr : Instruction :=
    { type := .GOTO, locationNum := trans.nextLoc,
      sourceLoc := srcLoc, guard := guard, target := none }
  have h_unfold :
      (Imperative.emitCondGoto guard srcLoc trans).fst.instructions =
      trans.instructions.push new_instr := rfl
  rw [h_unfold] at h_at
  have h_new_ne : new_instr.type ≠ .LOCATION := by
    show InstructionType.GOTO ≠ InstructionType.LOCATION; decide
  exact push_non_location_preserves trans labelMap new_instr h_inv h_new_ne h_at h_ty h_labels

/-- `emitUncondGoto`'s push is a GOTO, not LOCATION. -/
theorem emitUncondGoto_preserves
    (srcLoc : CProverGOTO.SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (labelMap : Std.HashMap String Nat)
    (h_inv : LocationsTrackLabelMap trans labelMap) :
    LocationsTrackLabelMap (Imperative.emitUncondGoto srcLoc trans).fst
      labelMap := by
  intro pc instr l h_at h_ty h_labels
  let new_instr : Instruction :=
    { type := .GOTO, locationNum := trans.nextLoc,
      sourceLoc := srcLoc, guard := CProverGOTO.Expr.true,
      target := none }
  have h_unfold :
      (Imperative.emitUncondGoto srcLoc trans).fst.instructions =
      trans.instructions.push new_instr := rfl
  rw [h_unfold] at h_at
  have h_new_ne : new_instr.type ≠ .LOCATION := by
    show InstructionType.GOTO ≠ InstructionType.LOCATION; decide
  exact push_non_location_preserves trans labelMap new_instr h_inv h_new_ne h_at h_ty h_labels

/-- The END_FUNCTION push is not LOCATION. -/
theorem endFunction_emit_preserves
    (md : Imperative.MetaData Core.Expression) (fname : String)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (labelMap : Std.HashMap String Nat)
    (h_inv : LocationsTrackLabelMap trans labelMap) :
    ∀ {pc : Nat} {instr : Instruction} {l : String},
      (trans.instructions.push (endFunctionInstr md fname trans))[pc]? = some instr →
      instr.type = .LOCATION → instr.labels = [l] →
      labelMap[l]? = some pc := by
  intro pc instr l h_at h_ty h_labels
  have h_new : (endFunctionInstr md fname trans).type ≠ .LOCATION := by
    show InstructionType.END_FUNCTION ≠ InstructionType.LOCATION; decide
  exact push_non_location_preserves trans labelMap (endFunctionInstr md fname trans) h_inv h_new
    h_at h_ty h_labels

/-- `coreCFGToGotoBlockStep` preserves the invariant. The block step:
1. emitLabel for `head_label` (push LOCATION + labelMap.insert).
2. cmds-fold over admitted cmds (no LOCATIONs emitted).
3. transfer push (GOTO or END_FUNCTION; no LOCATION).

The invariant `LocationsTrackLabelMap` threads through all three.

The `h_label_fresh` hypothesis says `labelMap[head_label]? = none`,
required by `emitLabel_preserves`. For the outer `blocksFoldlM`, this
is supplied by `BlockLabelsDistinct` + the inductive hypothesis. -/
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
  -- Step 1: emitLabel.
  have h_inv_after_label :
      LocationsTrackLabelMap
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname } st.trans)
        (st.labelMap.insert label st.trans.nextLoc) :=
    emitLabel_preserves label _ st.trans st.labelMap h_inv h_size h_label_fresh
  -- The post-emitLabel labelMap is what st' will eventually carry.
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    -- Step 2: cmds-fold preserves invariant.
    have h_inv_after_cmds :
        LocationsTrackLabelMap trans₂
          (st.labelMap.insert label st.trans.nextLoc) :=
      cmdsFoldlM_preserves fname blk.cmds _ trans₂
        (st.labelMap.insert label st.trans.nextLoc)
        h_admitted h_inner h_inv_after_label
    -- Step 3: transfer push (GOTO or END_FUNCTION).
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
        -- st'.trans.instructions = (emit two GOTOs after trans₂).
        -- pendingPatches and labelMap unchanged from post-cmds-fold.
        have h_invc :
            LocationsTrackLabelMap
              (Imperative.emitCondGoto cond_expr.not
                (Imperative.metadataToSourceLoc md fname trans₂.sourceText) trans₂).fst
              (st.labelMap.insert label st.trans.nextLoc) :=
          emitCondGoto_preserves _ _ trans₂ _ h_inv_after_cmds
        have h_invu :
            LocationsTrackLabelMap
              (Imperative.emitUncondGoto
                (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
                (Imperative.emitCondGoto cond_expr.not
                  (Imperative.metadataToSourceLoc md fname trans₂.sourceText) trans₂).fst).fst
              (st.labelMap.insert label st.trans.nextLoc) :=
          emitUncondGoto_preserves _ _ _ h_invc
        -- Goal is the same shape, just with the literal record. Reduce.
        intro pc instr l h_at h_ty h_labels
        -- Unfold the literal record's instructions field.
        change ((Imperative.emitUncondGoto _ (Imperative.emitCondGoto _ _ _).fst).fst).instructions[pc]?
          = some instr at h_at
        change (st.labelMap.insert label st.trans.nextLoc)[l]? = some pc
        exact h_invu h_at h_ty h_labels
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      -- st'.trans.instructions = trans₂.instructions.push (endFunctionInstr md fname trans₂).
      intro pc instr l h_at h_ty h_labels
      change (trans₂.instructions.push (endFunctionInstr md fname trans₂))[pc]? = some instr at h_at
      change (st.labelMap.insert label st.trans.nextLoc)[l]? = some pc
      exact endFunction_emit_preserves md fname trans₂ _ h_inv_after_cmds h_at h_ty h_labels
  | .error _, _ => simp at h_run

/-! ## Outer-fold preservation -/

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
      have h_admitted_hd : ∀ c ∈ hd.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted hd (by simp)
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk h_lb => h_admitted lblBlk (by simp [h_lb])
      have h_label_fresh : st.labelMap[hd.1]? = none :=
        h_no_blocks_in_init hd (by simp)
      have h_inv₁ : LocationsTrackLabelMap st₁.trans st₁.labelMap :=
        coreCFGToGotoBlockStep_preserves fname hd st st₁ h_admitted_hd h_step h_size
          h_inv h_label_fresh
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname hd st st₁ h_admitted_hd h_step h_size
      have h_distinct_rest : BlockLabelsDistinct rest :=
        BlockLabelsDistinct_tail hd rest h_distinct
      -- For rest's head labels: each was distinct from hd.1 (by h_distinct),
      -- so their lookups in st₁.labelMap = (st.labelMap.insert hd.1 _) are
      -- the same as in st.labelMap.
      have h_lbl₁ : st₁.labelMap = st.labelMap.insert hd.1 st.trans.nextLoc :=
        coreCFGToGotoBlockStep_labelMap fname hd st st₁ h_step
      have h_no_blocks_in_st₁ : ∀ p ∈ rest, st₁.labelMap[p.1]? = none := by
        intro p h_p_in
        have h_neq : hd.1 ≠ p.1 :=
          BlockLabelsDistinct_head_neq_tail hd rest h_distinct p h_p_in
        have h_p_in_cfg : p ∈ hd :: rest := List.mem_cons_of_mem hd h_p_in
        have h_old : st.labelMap[p.1]? = none := h_no_blocks_in_init p h_p_in_cfg
        rw [h_lbl₁]
        rw [Std.HashMap.getElem?_insert]
        have h_neq' : ¬ hd.1 == p.1 := by
          simp; exact h_neq
        rw [if_neg h_neq']
        exact h_old
      intro pc instr l h_at h_ty h_labels
      exact ih st₁ h_admitted_rest h_run h_size₁ h_inv₁ h_distinct_rest h_no_blocks_in_st₁
        h_at h_ty h_labels
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ## Patcher preservation -/

/-- The patcher preserves the invariant: the patcher writes only
`target`, and labels-preservation is already established. The labelMap
is unchanged by patching. -/
theorem patchGotoTargets_preserves
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (resolved : List (Nat × Nat))
    (labelMap : Std.HashMap String Nat)
    (h_inv : LocationsTrackLabelMap trans labelMap) :
    LocationsTrackLabelMap (Imperative.patchGotoTargets trans resolved) labelMap := by
  intro pc instr l h_at h_ty h_labels
  -- Use patchGotoTargets_preserves_type and patchGotoTargets_preserves_labels.
  obtain ⟨instr_pre_ty, h_at_pre_ty, h_ty_eq⟩ :=
    patchGotoTargets_preserves_type trans resolved pc instr h_at
  obtain ⟨instr_pre_lab, h_at_pre_lab, h_lab_eq⟩ :=
    patchGotoTargets_preserves_labels trans resolved pc instr h_at
  -- Both pre-instructions are the same (same pc, same trans).
  have h_pre_eq : instr_pre_ty = instr_pre_lab := by
    rw [h_at_pre_ty] at h_at_pre_lab
    injection h_at_pre_lab
  -- Apply h_inv.
  have h_ty_pre : instr_pre_ty.type = .LOCATION := by rw [← h_ty_eq]; exact h_ty
  have h_lab_pre : instr_pre_ty.labels = [l] := by
    rw [h_pre_eq, ← h_lab_eq]; exact h_labels
  exact h_inv h_at_pre_ty h_ty_pre h_lab_pre

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
  -- Step 1: get wf.labelMap l = some pc1 by total.
  have h_l_in : l ∈ cfg.blocks.map Prod.fst := by
    rw [List.mem_map]
    exact ⟨(l, blk), h_in, rfl⟩
  have h_total : (wf.labelMap l).isSome := wf.labelMap_total l h_l_in
  rcases h_pc1 : wf.labelMap l with _ | pc1
  · rw [h_pc1] at h_total; cases h_total
  -- Step 2: by layout_location_labels, instr at pc1 with labels [l].
  obtain ⟨instr1, h_at1, h_ty1, h_lab1⟩ :=
    wf.layout_location_labels l blk pc1 h_in h_pc1
  -- Step 3: build the LocationsTrackLabelMap invariant for ans.instructions.
  have h_inv_init : LocationsTrackLabelMap (coreCFGToGotoInitState trans₀).trans
                      (coreCFGToGotoInitState trans₀).labelMap := by
    intro pc instr l' h h_ty _
    show (∅ : Std.HashMap String Nat)[l']? = some pc
    -- pc has a LOCATION in trans₀ — contradicts h_init_no_location.
    exact absurd h_ty (h_init_no_location h)
  have h_size_init : (coreCFGToGotoInitState trans₀).trans.instructions.size =
                       (coreCFGToGotoInitState trans₀).trans.nextLoc := by
    simp [coreCFGToGotoInitState]; exact h_init_size
  have h_admitted_st :
      ∀ lblBlk ∈ cfg.blocks, ∀ c ∈ lblBlk.2.cmds,
        Core.CmdExt.isAdmittedCmd c = true :=
    fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb
  have h_no_blocks_in_init :
      ∀ p ∈ cfg.blocks, (coreCFGToGotoInitState trans₀).labelMap[p.1]? = none := by
    intro p _
    show (∅ : Std.HashMap String Nat)[p.1]? = none
    exact Std.HashMap.getElem?_empty
  have h_inv_st_final :
      LocationsTrackLabelMap st_final.trans st_final.labelMap :=
    blocksFoldlM_preserves functionName cfg.blocks _ st_final h_admitted_st h_blocks_run
      h_size_init h_inv_init h_distinct h_no_blocks_in_init
  -- Step 4: extend through the patcher to ans.
  -- ans = patchGotoTargets trans_post resolved where trans_post = st_final.trans
  -- under the empty-loopContracts hypothesis.
  obtain ⟨st_final', resolved, trans_post, h_blocks_run', h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  have h_st_final_eq : st_final = st_final' := by
    rw [h_blocks_run] at h_blocks_run'; injection h_blocks_run'
  subst h_st_final_eq
  have h_lc_empty := h_loopContracts_empty_post st_final h_blocks_run
  rw [h_lc_empty] at h_patches_run
  have h_trans_post_eq : trans_post = st_final.trans :=
    patchesFoldlM_no_contracts_trans_eq st_final.labelMap st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
  have h_ans_eq' : ans = Imperative.patchGotoTargets st_final.trans resolved := by
    rw [h_ans_eq, h_trans_post_eq]
  have h_inv_ans :
      LocationsTrackLabelMap (Imperative.patchGotoTargets st_final.trans resolved)
        st_final.labelMap :=
    patchGotoTargets_preserves st_final.trans resolved _ h_inv_st_final
  -- Step 5: instr1 at pc1 in ans.instructions has labels [l]. Apply h_inv_ans.
  have h_at1_post : (Imperative.patchGotoTargets st_final.trans resolved).instructions[pc1]?
                     = some instr1 := by
    have h_at1_ans : ans.instructions[pc1]? = some instr1 := h_at1
    rw [h_ans_eq'] at h_at1_ans; exact h_at1_ans
  have h_lookup_pc1 : st_final.labelMap[l]? = some pc1 :=
    h_inv_ans h_at1_post h_ty1 h_lab1
  -- Step 6: combine with h_lookup : st_final.labelMap[l]? = some target.
  have h_lookup' : (some pc1 : Option Nat) = some target := by
    rw [← h_lookup_pc1]; exact h_lookup
  have h_eq : pc1 = target := by injection h_lookup'
  rw [h_eq]

end CProverGOTO.WfLabelMapAgree
