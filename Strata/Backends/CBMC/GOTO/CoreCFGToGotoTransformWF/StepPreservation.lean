/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF.Preservation
import all Strata.DL.Imperative.ToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline

/-! # WellFormedTranslation - Per-step preservation

This file is part 3 of the CoreCFGToGotoTransformWF split. It
provides the LabelMap operations and the per-cmd / per-block step
preservation lemmas: size_eq, locationNum_eq_index, instr-array
prefix, and per-block layout effects + post-conditions.
-/

namespace CProverGOTO

open Imperative

public section

/-- An empty `LabelMap`: returns `none` for every label. -/
@[expose] def emptyLabelMap : LabelMap := fun _ => none

/-! ## LabelMap operations and invariants

The translator threads a `Std.HashMap String Nat` for `labelMap`,
inserting `label ↦ trans.nextLoc` at the start of each outer-loop
iteration. We model the labelMap as a `LabelMap = String → Option Nat`
function, which is the form `WellFormedTranslation` consumes.

The key operation: extending an existing `labelMap` with `label ↦ pc`.
This only preserves injectivity when `label` is fresh (not already in
the map's domain), which corresponds to the implicit
`BlockLabelsDistinct cfg` requirement on the input CFG. -/

/-- Extend a `LabelMap` with one new `label ↦ pc` mapping. -/
@[expose] def labelMapInsert
    (m : LabelMap) (label : String) (pc : Nat) : LabelMap :=
  fun l => if l = label then some pc else m l

/-- After `labelMapInsert`, the inserted label resolves to its `pc`. -/
@[simp] theorem labelMapInsert_self
    (m : LabelMap) (label : String) (pc : Nat) :
    (labelMapInsert m label pc) label = some pc := by
  unfold labelMapInsert
  simp

/-- After `labelMapInsert`, an unrelated label resolves the same as in
the original map. -/
@[simp] theorem labelMapInsert_other
    (m : LabelMap) (label l : String) (pc : Nat) (h : l ≠ label) :
    (labelMapInsert m label pc) l = m l := by
  unfold labelMapInsert
  simp [h]

/-- Convert a `Std.HashMap String Nat` to a `LabelMap = String →
Option Nat` via `m.get?`. The translator's `CoreCFGTransLoopState`
threads a `HashMap`; the `WellFormedTranslation` consumer expects a
function form. -/
@[expose] def hashMapToLabelMap (m : Std.HashMap String Nat) : LabelMap :=
  fun l => m[l]?

/-- The empty hashmap converts to `emptyLabelMap`. -/
@[simp] theorem hashMapToLabelMap_empty :
    hashMapToLabelMap (∅ : Std.HashMap String Nat) = emptyLabelMap := by
  funext l
  unfold hashMapToLabelMap emptyLabelMap
  simp

/-! ## Per-cmd / per-block step preservation

`coreCFGToGotoTransform` is structured as

```
cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) initSt
  >>= λ st => st.pendingPatches.foldlM (Strata.coreCFGToGotoPatchStep ..) ([], st.trans)
  >>= λ (resolved, trans) => Imperative.patchGotoTargets trans resolved
```

with named per-cmd / per-block / per-patch step functions. The
preservation lemmas below characterise each step's effect on the
partial `WellFormedTranslation` invariant. -/

/-- The per-cmd step `Strata.coreCFGToGotoCmdStep` agrees with
`Cmd.toGotoInstructions` on the `.cmd c` case, and produces a single
appended FUNCTION_CALL instruction on the `.call` case. -/
theorem coreCFGToGotoCmdStep_cmd
    (fname : String) (c : Imperative.Cmd Core.Expression)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv) :
    Strata.coreCFGToGotoCmdStep fname trans (.cmd c) =
      Imperative.Cmd.toGotoInstructions trans.T fname c trans := by
  unfold Strata.coreCFGToGotoCmdStep
  rfl

/-- The per-cmd step preserves `instructions.size = nextLoc` on
admitted commands (i.e., `.cmd c`; `.call` is rejected by
`isAdmittedCmd`). -/
theorem coreCFGToGotoCmdStep_preserves_size_eq
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : Core.CmdExt.isAdmittedCmd cmd = true)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc) :
    ans.instructions.size = ans.nextLoc := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact toGotoInstructions_preserves_size_eq trans.T fname c trans ans h_run h_size
  | call _ _ _ =>
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-- The per-cmd step preserves `locationNum = index` on admitted
commands. -/
theorem coreCFGToGotoCmdStep_preserves_locationNum_eq_index
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : Core.CmdExt.isAdmittedCmd cmd = true)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact toGotoInstructions_preserves_locationNum_eq_index
      trans.T fname c trans ans h_run h_size h_loc
  | call _ _ _ =>
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-- The cmds-fold via `foldlM` preserves `size_eq`, when each cmd is
admitted by `isAdmittedCmd`. -/
theorem cmdsFoldlM_preserves_size_eq
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc) :
    ans.instructions.size = ans.nextLoc := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_size
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_admitted_cmd := h_admitted cmd (by simp)
      have h_size' : trans'.instructions.size = trans'.nextLoc :=
        coreCFGToGotoCmdStep_preserves_size_eq fname cmd trans trans'
          h_admitted_cmd h_step h_size
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      exact ih trans' h_admitted_rest h_run h_size'
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The cmds-fold via `foldlM` preserves `locationNum_eq_index`. -/
theorem cmdsFoldlM_preserves_locationNum_eq_index
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_loc
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_admitted_cmd := h_admitted cmd (by simp)
      have h_size' : trans'.instructions.size = trans'.nextLoc :=
        coreCFGToGotoCmdStep_preserves_size_eq fname cmd trans trans'
          h_admitted_cmd h_step h_size
      have h_loc' :
          ∀ (i : Nat) (instr : CProverGOTO.Instruction),
            trans'.instructions[i]? = some instr → instr.locationNum = i :=
        coreCFGToGotoCmdStep_preserves_locationNum_eq_index
          fname cmd trans trans' h_admitted_cmd h_step h_size h_loc
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      exact ih trans' h_admitted_rest h_run h_size' h_loc'
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The per-cmd step's `nextLoc` advance equals `Core.CmdExt.gotoInstrCount cmd`. -/
theorem coreCFGToGotoCmdStep_nextLoc_advance
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : Core.CmdExt.isAdmittedCmd cmd = true)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans) :
    ans.nextLoc = trans.nextLoc + Core.CmdExt.gotoInstrCount cmd := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    have := toGotoInstructions_nextLoc_advance trans.T fname c trans ans h_run
    rw [this]
    rfl
  | call _ _ _ =>
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-- The cmds-fold's `nextLoc` advance equals `DetBlockBodyInstrCount`
applied to a synthetic block. -/
theorem cmdsFoldlM_nextLoc_advance
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans) :
    ans.nextLoc =
      trans.nextLoc + cmds.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; simp
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_admitted_cmd := h_admitted cmd (by simp)
      have h_advance' : trans'.nextLoc = trans.nextLoc + Core.CmdExt.gotoInstrCount cmd :=
        coreCFGToGotoCmdStep_nextLoc_advance fname cmd trans trans' h_admitted_cmd h_step
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      have h_ih := ih trans' h_admitted_rest h_run
      rw [h_ih, h_advance']
      -- Goal: trans.nextLoc + gotoInstrCount cmd + foldl (+) 0 rest =
      --        trans.nextLoc + foldl (+) 0 (cmd :: rest)
      simp only [List.foldl]
      rw [foldl_gotoInstrCount_extract_acc rest (0 + Core.CmdExt.gotoInstrCount cmd)]
      omega
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Per-block step preservation

The per-block step's body is a sequence of three pieces: `emitLabel`,
`block.cmds.foldlM coreCFGToGotoCmdStep`, and the transfer-emit branch
(condGoto or finish). The lemmas below establish that this composition
preserves `size_eq` and `locationNum_eq_index`. -/

/-- The per-block step preserves `size_eq` (admitted cmds only). -/
theorem coreCFGToGotoBlockStep_preserves_size_eq
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    st'.trans.instructions.size = st'.trans.nextLoc := by
  obtain ⟨label, blk⟩ := lblBlk
  -- Step 1: emitLabel produces a state with size_eq.
  have h_size₁ :
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname }
        st.trans).instructions.size =
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname }
        st.trans).nextLoc :=
    emitLabel_preserves_size_eq label
      { CProverGOTO.SourceLocation.nil with function := fname } st.trans h_size
  -- Unfold the step function and the inner do-block.
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  -- Now `h_run` has shape `match (foldlM ...) with .ok x => match transfer with ... | .error => Except.error _`.
  -- Case on the inner-fold result.
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_size₂ : trans₂.instructions.size = trans₂.nextLoc :=
      cmdsFoldlM_preserves_size_eq fname blk.cmds _ trans₂
        h_admitted h_inner h_size₁
    -- h_run now is `(match transfer ...) = Except.ok st'`. Case on transfer.
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, h_cond_eval =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        simp [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto, Array.size_push, h_size₂]
      | .error e, h_cond_eval =>
        simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      simp [Array.size_push, h_size₂]
  | .error e, h_inner =>
    simp at h_run

/-- The per-block step preserves `locationNum_eq_index`. -/
theorem coreCFGToGotoBlockStep_preserves_locationNum_eq_index
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        st.trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      st'.trans.instructions[i]? = some instr → instr.locationNum = i := by
  obtain ⟨label, blk⟩ := lblBlk
  -- Step 1: emitLabel preserves size_eq + locationNum_eq_index.
  have h_size₁ :
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname }
        st.trans).instructions.size =
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname }
        st.trans).nextLoc :=
    emitLabel_preserves_size_eq label
      { CProverGOTO.SourceLocation.nil with function := fname } st.trans h_size
  have h_loc₁ :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions[i]? = some instr → instr.locationNum = i :=
    emitLabel_preserves_locationNum_eq_index label
      { CProverGOTO.SourceLocation.nil with function := fname } st.trans h_size h_loc
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_size₂ : trans₂.instructions.size = trans₂.nextLoc :=
      cmdsFoldlM_preserves_size_eq fname blk.cmds _ trans₂
        h_admitted h_inner h_size₁
    have h_loc₂ :
        ∀ (i : Nat) (instr : CProverGOTO.Instruction),
          trans₂.instructions[i]? = some instr → instr.locationNum = i :=
      cmdsFoldlM_preserves_locationNum_eq_index fname blk.cmds _ trans₂
        h_admitted h_inner h_size₁ h_loc₁
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, h_cond_eval =>
        simp only at h_run
        injection h_run with h_run
        intro i instr h
        rw [← h_run] at h
        -- After two emitGoto pushes, the array has 2 more instructions.
        -- Use emitCondGoto / emitUncondGoto preservation lemmas.
        have h_after_neg :
          ∀ (i : Nat) (instr : CProverGOTO.Instruction),
            (Imperative.emitCondGoto (CProverGOTO.Expr.not cond_expr)
              (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
              trans₂).fst.instructions[i]? = some instr → instr.locationNum = i :=
          emitCondGoto_preserves_locationNum_eq_index
            (CProverGOTO.Expr.not cond_expr)
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText) trans₂ h_size₂ h_loc₂
        have h_after_neg_size :
          (Imperative.emitCondGoto (CProverGOTO.Expr.not cond_expr)
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
            trans₂).fst.instructions.size =
          (Imperative.emitCondGoto (CProverGOTO.Expr.not cond_expr)
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
            trans₂).fst.nextLoc :=
          emitCondGoto_preserves_size_eq
            (CProverGOTO.Expr.not cond_expr)
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText) trans₂ h_size₂
        have h_after_uncond :
          ∀ (i : Nat) (instr : CProverGOTO.Instruction),
            (Imperative.emitUncondGoto
              (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
              (Imperative.emitCondGoto (CProverGOTO.Expr.not cond_expr)
                (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
                trans₂).fst).fst.instructions[i]? = some instr →
            instr.locationNum = i :=
          emitUncondGoto_preserves_locationNum_eq_index
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
            _ h_after_neg_size h_after_neg
        exact h_after_uncond i instr h
      | .error e, h_cond_eval =>
        simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      intro i instr h
      rw [← h_run] at h
      -- After pushing 1 END_FUNCTION, locationNum_eq_index transfers via
      -- a generic push lemma.
      exact endFunction_emit_preserves_locationNum_eq_index md fname trans₂ h_size₂ h_loc₂ i instr h
  | .error e, h_inner =>
    simp at h_run

/-! ### Per-block step layout effects

The per-block step's effect on `st`'s fields:
* `st'.labelMap = st.labelMap.insert lblBlk.1 st.trans.nextLoc`
* `st'.trans.nextLoc = st.trans.nextLoc + 1 + bodyCount + transferCount`
* The block's pc (= `st.trans.nextLoc`) addresses a LOCATION instruction
  in `st'.trans.instructions` (the leading `emitLabel` push).
* For `.finish md`: position `pc + 1 + bodyCount` holds an END_FUNCTION.
* For `.condGoto cond lt lf md`: positions `pc + 1 + bodyCount` and
  `pc + 1 + bodyCount + 1` hold two GOTOs (target = none, guard =
  `e_goto.not` and `Expr.true` respectively).
* The pendingPatches array is extended by two patches for `.condGoto`
  blocks; preserved for `.finish` blocks. -/

/-- The per-block step's effect on `st.labelMap` is to insert
`lblBlk.1 ↦ st.trans.nextLoc`. -/
theorem coreCFGToGotoBlockStep_labelMap
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st') :
    st'.labelMap = st.labelMap.insert lblBlk.1 st.trans.nextLoc := by
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
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
  | .error _, _ => simp at h_run

/-- The per-block step's effect on `st.trans.nextLoc` for `.finish md`
blocks: it advances by `1 + bodyCount + 1` (the trailing `+1` is the
END_FUNCTION push). -/
theorem coreCFGToGotoBlockStep_nextLoc_advance_finish
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (md : Imperative.MetaData Core.Expression)
    (h_transfer : lblBlk.2.transfer = .finish md)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st') :
    st'.trans.nextLoc = st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2 + 1 := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_advance₂ :
        trans₂.nextLoc = st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk := by
      have := cmdsFoldlM_nextLoc_advance fname blk.cmds _ trans₂ h_admitted h_inner
      have h_after_label :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname } st.trans).nextLoc =
          st.trans.nextLoc + 1 := rfl
      rw [h_after_label] at this
      rw [this]
      simp [DetBlockBodyInstrCount]
    rw [h_transfer] at h_run
    simp only at h_run
    injection h_run with h_run
    rw [← h_run]
    show trans₂.nextLoc + 1 = st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk + 1
    omega
  | .error _, _ => simp at h_run

/-- The per-block step's effect on `st.trans.nextLoc` for `.condGoto`
blocks: it advances by `1 + bodyCount + 2`. -/
theorem coreCFGToGotoBlockStep_nextLoc_advance_condGoto
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (cond : Core.Expression.Expr) (lt lf : String)
    (md : Imperative.MetaData Core.Expression)
    (h_transfer : lblBlk.2.transfer = .condGoto cond lt lf md)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st') :
    st'.trans.nextLoc = st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2 + 2 := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_advance₂ :
        trans₂.nextLoc = st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk := by
      have := cmdsFoldlM_nextLoc_advance fname blk.cmds _ trans₂ h_admitted h_inner
      have h_after_label :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname } st.trans).nextLoc =
          st.trans.nextLoc + 1 := rfl
      rw [h_after_label] at this
      rw [this]
      simp [DetBlockBodyInstrCount]
    rw [h_transfer] at h_run
    simp only at h_run
    generalize h_cond_eval :
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
    match cond_eval, h_cond_eval with
    | .ok cond_expr, _ =>
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
      omega
    | .error _, _ => simp at h_run
  | .error _, _ => simp at h_run

/-! ### Per-block step instruction-array prefix preservation

The per-block step only appends to `trans.instructions`. This means
positions `[0, st.trans.instructions.size)` keep the same instruction
through the block step. Composed with foldlM, this gives positions
`[0, st_initial.trans.instructions.size)` retaining their original
contents through all blocks. -/

/-- Each step in `cmdsFoldlM` only grows the instruction array. -/
theorem coreCFGToGotoCmdStep_size_le
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : Core.CmdExt.isAdmittedCmd cmd = true)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans) :
    trans.instructions.size ≤ ans.instructions.size := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact toGotoInstructions_size_le trans.T fname c trans ans h_run
  | call _ _ _ =>
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-- Each step in `cmdsFoldlM` preserves the instruction-array prefix
on `?`-lookups. -/
theorem coreCFGToGotoCmdStep_instructions_prefix?
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : Core.CmdExt.isAdmittedCmd cmd = true)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans)
    (k : Nat) (h : k < trans.instructions.size) :
    ans.instructions[k]? = trans.instructions[k]? := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact toGotoInstructions_instructions_prefix? trans.T fname c trans ans h_run k h
  | call _ _ _ =>
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-- The cmds-fold preserves the instruction-array prefix on
`?`-lookups: any index `k` below the input size returns the same
instruction in `ans` as in `trans`. -/
theorem cmdsFoldlM_instructions_prefix?
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans)
    (k : Nat) (h : k < trans.instructions.size) :
    ans.instructions[k]? = trans.instructions[k]? := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; rfl
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_admitted_cmd := h_admitted cmd (by simp)
      have h_size_le : trans.instructions.size ≤ trans'.instructions.size :=
        coreCFGToGotoCmdStep_size_le fname cmd trans trans' h_admitted_cmd h_step
      have h_k' : k < trans'.instructions.size := Nat.lt_of_lt_of_le h h_size_le
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      have h_ih := ih trans' h_admitted_rest h_run h_k'
      rw [h_ih]
      exact coreCFGToGotoCmdStep_instructions_prefix? fname cmd trans trans' h_admitted_cmd h_step k h
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- `cmdsFoldlM_size_le` — the cmds-fold only grows the instruction
array. -/
theorem cmdsFoldlM_size_le
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans) :
    trans.instructions.size ≤ ans.instructions.size := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact Nat.le_refl _
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_admitted_cmd := h_admitted cmd (by simp)
      have h_le := coreCFGToGotoCmdStep_size_le fname cmd trans trans' h_admitted_cmd h_step
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      have := ih trans' h_admitted_rest h_run
      omega
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The per-block step only grows the instruction array. -/
theorem coreCFGToGotoBlockStep_size_le
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st') :
    st.trans.instructions.size ≤ st'.trans.instructions.size := by
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
    have h_inner_le :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size ≤ trans₂.instructions.size :=
      cmdsFoldlM_size_le fname blk.cmds _ trans₂ h_admitted h_inner
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
        simp [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto, Array.size_push]
        omega
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      simp [Array.size_push]
      omega
  | .error _, _ => simp at h_run

/-- The per-block step preserves the instruction-array prefix on
`?`-lookups: any index `k` below the input size returns the same
instruction in `st'.trans` as in `st.trans`. -/
theorem coreCFGToGotoBlockStep_instructions_prefix?
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (k : Nat) (h : k < st.trans.instructions.size) :
    st'.trans.instructions[k]? = st.trans.instructions[k]? := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    -- emitLabel(...).instructions = st.trans.instructions.push <new>
    have h_label_unfold :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions =
        st.trans.instructions.push
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := rfl
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      rw [h_label_unfold, Array.size_push]
    have h_k_after_label :
        k < (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size := by
      rw [h_label_size]; omega
    have h_label_lookup :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions[k]? = st.trans.instructions[k]? := by
      rw [h_label_unfold]
      rw [Array.getElem?_push_lt h, Array.getElem?_eq_getElem h]
    have h_inner_prefix :
        trans₂.instructions[k]? =
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions[k]? :=
      cmdsFoldlM_instructions_prefix? fname blk.cmds _ trans₂ h_admitted h_inner k h_k_after_label
    have h_inner_size_le :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size ≤ trans₂.instructions.size :=
      cmdsFoldlM_size_le fname blk.cmds _ trans₂ h_admitted h_inner
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
        have h_k_in_trans₂ : k < trans₂.instructions.size := by omega
        simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
        have h_k_in_post_first :
            k < (trans₂.instructions.push
              { type := .GOTO, guard := cond_expr.not,
                sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                locationNum := trans₂.nextLoc, target := .none }).size := by
          simp [Array.size_push]; omega
        rw [Array.getElem?_push_lt h_k_in_post_first,
            Array.getElem_push_lt h_k_in_trans₂,
            ← Array.getElem?_eq_getElem h_k_in_trans₂]
        rw [h_inner_prefix, h_label_lookup]
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      have h_k_in_trans₂ : k < trans₂.instructions.size := by omega
      rw [Array.getElem?_push_lt h_k_in_trans₂,
          ← Array.getElem?_eq_getElem h_k_in_trans₂]
      rw [h_inner_prefix, h_label_lookup]
  | .error _, _ => simp at h_run

/-! ### Per-block step layout post-conditions

After one block step, certain instructions are at specific positions in
`st'.trans.instructions`:

* The LOCATION instruction is at `st.trans.nextLoc`.
* For `.finish md` blocks: the END_FUNCTION is at `st.trans.nextLoc + 1
  + bodyCount`.
* For `.condGoto cond lt lf md` blocks: two GOTOs at `st.trans.nextLoc
  + 1 + bodyCount` (guard `e_goto.not`, target `none`) and at `+1`
  (guard `Expr.true`, target `none`).

These results are stable through subsequent block steps because of
`coreCFGToGotoBlockStep_instructions_prefix?`. -/

/-- After one block step, the LOCATION instruction is at
`st.trans.nextLoc` in `st'.trans.instructions`. -/
theorem coreCFGToGotoBlockStep_location_at_pc
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    ∃ instr,
      st'.trans.instructions[st.trans.nextLoc]? = some instr ∧
      instr.type = .LOCATION := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    -- The LOCATION instruction is the LAST one pushed by emitLabel.
    have h_label_unfold :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions =
        st.trans.instructions.push
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := rfl
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      rw [h_label_unfold, Array.size_push]
    have h_label_at :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions[st.trans.instructions.size]? = some
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := by
      rw [h_label_unfold, Array.getElem?_push_eq]
    -- Show that the inner cmds-fold preserves this LOCATION.
    have h_pc_lt : st.trans.instructions.size <
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size := by
      rw [h_label_size]; omega
    have h_pc_in_trans₂ :
        trans₂.instructions[st.trans.instructions.size]? = some
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := by
      rw [cmdsFoldlM_instructions_prefix? fname blk.cmds _ trans₂ h_admitted h_inner _ h_pc_lt]
      exact h_label_at
    -- pc = st.trans.nextLoc = st.trans.instructions.size by h_size.
    have h_pc_eq : st.trans.nextLoc = st.trans.instructions.size := h_size.symm
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
        simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
        rw [h_pc_eq]
        have h_pc_in_trans₂_size : st.trans.instructions.size < trans₂.instructions.size := by
          have := cmdsFoldlM_size_le fname blk.cmds _ trans₂ h_admitted h_inner
          rw [h_label_size] at this; omega
        have h_pc_in_first :
            st.trans.instructions.size < (trans₂.instructions.push
              { type := .GOTO, guard := cond_expr.not,
                sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                locationNum := trans₂.nextLoc, target := .none }).size := by
          simp [Array.size_push]; omega
        rw [Array.getElem?_push_lt h_pc_in_first,
            Array.getElem_push_lt h_pc_in_trans₂_size,
            ← Array.getElem?_eq_getElem h_pc_in_trans₂_size]
        rw [h_pc_in_trans₂]
        exact ⟨_, rfl, rfl⟩
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      rw [h_pc_eq]
      have h_pc_in_trans₂_size : st.trans.instructions.size < trans₂.instructions.size := by
        have := cmdsFoldlM_size_le fname blk.cmds _ trans₂ h_admitted h_inner
        rw [h_label_size] at this; omega
      rw [Array.getElem?_push_lt h_pc_in_trans₂_size,
          ← Array.getElem?_eq_getElem h_pc_in_trans₂_size]
      rw [h_pc_in_trans₂]
      exact ⟨_, rfl, rfl⟩
  | .error _, _ => simp at h_run

/-- Strengthened version of `coreCFGToGotoBlockStep_location_at_pc`:
the LOCATION instruction at `st.trans.nextLoc` carries the block's
label in its `labels` field — exactly `[label]`. Used to pin
`wf.labelMap l` to the translator's hashmap-keyed labelMap by
exhibiting at most one LOCATION per label. -/
theorem coreCFGToGotoBlockStep_location_at_pc_with_labels
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    ∃ instr,
      st'.trans.instructions[st.trans.nextLoc]? = some instr ∧
      instr.type = .LOCATION ∧
      instr.labels = [lblBlk.1] := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_label_unfold :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions =
        st.trans.instructions.push
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := rfl
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      rw [h_label_unfold, Array.size_push]
    have h_label_at :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions[st.trans.instructions.size]? = some
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := by
      rw [h_label_unfold, Array.getElem?_push_eq]
    have h_pc_lt : st.trans.instructions.size <
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size := by
      rw [h_label_size]; omega
    have h_pc_in_trans₂ :
        trans₂.instructions[st.trans.instructions.size]? = some
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := by
      rw [cmdsFoldlM_instructions_prefix? fname blk.cmds _ trans₂ h_admitted h_inner _ h_pc_lt]
      exact h_label_at
    have h_pc_eq : st.trans.nextLoc = st.trans.instructions.size := h_size.symm
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
        simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
        rw [h_pc_eq]
        have h_pc_in_trans₂_size : st.trans.instructions.size < trans₂.instructions.size := by
          have := cmdsFoldlM_size_le fname blk.cmds _ trans₂ h_admitted h_inner
          rw [h_label_size] at this; omega
        have h_pc_in_first :
            st.trans.instructions.size < (trans₂.instructions.push
              { type := .GOTO, guard := cond_expr.not,
                sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                locationNum := trans₂.nextLoc, target := .none }).size := by
          simp [Array.size_push]; omega
        rw [Array.getElem?_push_lt h_pc_in_first,
            Array.getElem_push_lt h_pc_in_trans₂_size,
            ← Array.getElem?_eq_getElem h_pc_in_trans₂_size]
        rw [h_pc_in_trans₂]
        exact ⟨_, rfl, rfl, rfl⟩
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      rw [h_pc_eq]
      have h_pc_in_trans₂_size : st.trans.instructions.size < trans₂.instructions.size := by
        have := cmdsFoldlM_size_le fname blk.cmds _ trans₂ h_admitted h_inner
        rw [h_label_size] at this; omega
      rw [Array.getElem?_push_lt h_pc_in_trans₂_size,
          ← Array.getElem?_eq_getElem h_pc_in_trans₂_size]
      rw [h_pc_in_trans₂]
      exact ⟨_, rfl, rfl, rfl⟩
  | .error _, _ => simp at h_run

/-- After one block step on a `.finish md` block, the END_FUNCTION
instruction is at `st.trans.nextLoc + 1 + bodyCount` in
`st'.trans.instructions`. -/
theorem coreCFGToGotoBlockStep_finish_at_pc
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (md : Imperative.MetaData Core.Expression)
    (h_transfer : lblBlk.2.transfer = .finish md)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    ∃ instr,
      st'.trans.instructions[st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2]? = some instr ∧
      instr.type = .END_FUNCTION := by
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
    injection h_run with h_run
    rw [← h_run]
    -- After the END_FUNCTION push, position trans₂.instructions.size = pc + 1 + bodyCount
    -- holds the new END_FUNCTION instruction.
    have h_target_eq :
        st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk = trans₂.instructions.size := by
      rw [h_inner_size]; omega
    rw [h_target_eq]
    refine ⟨{ type := .END_FUNCTION, locationNum := trans₂.nextLoc,
              sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText }, ?_, rfl⟩
    show (trans₂.instructions.push _)[trans₂.instructions.size]? = some _
    exact Array.getElem?_push_size
  | .error _, _ => simp at h_run

/-- After one block step on a `.condGoto cond lt lf md` block, two GOTO
instructions appear at `st.trans.nextLoc + 1 + bodyCount` (guard
`e_goto.not`, target `none`) and at `+1` (guard `Expr.true`, target
`none`). -/
theorem coreCFGToGotoBlockStep_condGoto_at_pc
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (cond : Core.Expression.Expr) (lt lf : String)
    (md : Imperative.MetaData Core.Expression)
    (h_transfer : lblBlk.2.transfer = .condGoto cond lt lf md)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    ∃ instr_neg instr_uncond e_goto,
      st'.trans.instructions[st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2]? = some instr_neg ∧
      instr_neg.type = .GOTO ∧
      instr_neg.target = none ∧
      instr_neg.guard = e_goto.not ∧
      Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = .ok e_goto ∧
      st'.trans.instructions[st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2 + 1]? = some instr_uncond ∧
      instr_uncond.type = .GOTO ∧
      instr_uncond.target = none ∧
      instr_uncond.guard = CProverGOTO.Expr.true := by
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
    -- Use generalize-with-equation style to keep h_eq usable.
    -- We must `revert h_run` to expose the type containing the LHS of the cond_eval.
    revert h_run
    generalize h_eq :
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = res
    intro h_run
    -- Capture h_eq into the existential pre-emptively.
    -- Re-state h_eq before the cases analysis (so it's not over a substituted res).
    cases res with
    | error _ => simp at h_run
    | ok cond_expr =>
      -- Now h_eq : ... = Except.ok cond_expr.
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      have h_pc_neg_eq :
          st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk = trans₂.instructions.size := by
        rw [h_inner_size]; omega
      have h_pc_uncond_eq :
          st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk + 1 = trans₂.instructions.size + 1 := by
        rw [h_inner_size]; omega
      simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
      have h_neg :
          ((trans₂.instructions.push
              { type := .GOTO, guard := cond_expr.not,
                sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                locationNum := trans₂.nextLoc }).push
            { type := .GOTO, guard := CProverGOTO.Expr.true,
              sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
              locationNum := trans₂.nextLoc + 1 })[trans₂.instructions.size]?
          = some
              { type := .GOTO, guard := cond_expr.not,
                sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                locationNum := trans₂.nextLoc } := by
        rw [Array.getElem?_push_lt (by simp [Array.size_push])]
        congr 1
        exact Array.getElem_push_eq
      -- For h_uncond, use the fact that pushing onto an array of size n+1 makes
      -- the new last element accessible via getElem? at index n+1.
      -- We use `Array.getElem?_push_size` after rewriting.
      have h_uncond :
          ((trans₂.instructions.push
              ({ type := .GOTO, guard := cond_expr.not,
                 sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                 locationNum := trans₂.nextLoc } : CProverGOTO.Instruction)).push
            { type := .GOTO, guard := CProverGOTO.Expr.true,
              sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
              locationNum := trans₂.nextLoc + 1 })[trans₂.instructions.size + 1]?
          = some
              { type := .GOTO, guard := CProverGOTO.Expr.true,
                sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                locationNum := trans₂.nextLoc + 1 } := by
        let arr1 := trans₂.instructions.push
            ({ type := .GOTO, guard := cond_expr.not,
               sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
               locationNum := trans₂.nextLoc } : CProverGOTO.Instruction)
        have h_size_inner : arr1.size = trans₂.instructions.size + 1 := by
          simp [arr1, Array.size_push]
        show (arr1.push _)[trans₂.instructions.size + 1]? = _
        rw [← h_size_inner]
        exact Array.getElem?_push_size
      refine ⟨_, _, cond_expr, by rw [h_pc_neg_eq]; exact h_neg, rfl, rfl, rfl, ?_,
        by rw [h_pc_uncond_eq]; exact h_uncond, rfl, rfl, rfl⟩
      -- h_eq has the form `Lambda.LExpr.toGotoExprCtx [] cond = Except.ok cond_expr`,
      -- but simp may have already substituted in the goal; either way, rfl or h_eq
      -- works.
      first | rfl | exact h_eq
  | .error _, _ => simp at h_run

/-- The outer-loop fold preserves `size_eq` if every block's body is
admitted. -/
theorem blocksFoldlM_preserves_size_eq
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    st'.trans.instructions.size = st'.trans.nextLoc := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_size
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ head.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted head (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname head st st₁ h_admitted_head h_step h_size
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      exact ih st₁ h_admitted_rest h_run h_size₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The outer-loop fold preserves `locationNum_eq_index`. -/
theorem blocksFoldlM_preserves_locationNum_eq_index
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        st.trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      st'.trans.instructions[i]? = some instr → instr.locationNum = i := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_loc
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ head.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted head (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname head st st₁ h_admitted_head h_step h_size
      have h_loc₁ :
          ∀ (i : Nat) (instr : CProverGOTO.Instruction),
            st₁.trans.instructions[i]? = some instr → instr.locationNum = i :=
        coreCFGToGotoBlockStep_preserves_locationNum_eq_index fname head st st₁
          h_admitted_head h_step h_size h_loc
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      exact ih st₁ h_admitted_rest h_run h_size₁ h_loc₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run


end -- public section

end CProverGOTO
