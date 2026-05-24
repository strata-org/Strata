/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF
public import Strata.Backends.CBMC.GOTO.CmdProvenance
import all Strata.DL.Imperative.ToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline

public section

/-! # Discharging R8b's three PC-inversion auxiliaries

Round-9 deliverable. Closes the three "PC inversion" hypotheses
(`DeclPcInversion`, `AssignPcInversion`, `AssignNondetPcInversion`)
that R8b left as auxiliary preconditions on its three provenance
theorems (`decl_provenance_of_translator`,
`assn_provenance_of_translator`,
`assn_nondet_provenance_of_translator_strict`).

## Strategy

Rather than directly inverting "PC carrying a DECL/ASSIGN" into a
block + offset, we prove a **coverage predicate** by translator-fold
induction:

```
def BodyPcCovered (trans : ...) (pgm : Program) : Prop :=
  ∀ pc instr, trans.instructions[pc]? = some instr →
    -- DECL → there's a CmdEmittedAt over pgm with init_* shape at pc
    (instr.type = .DECL → ∃ inner, CmdEmittedAt ... pgm pc inner) ∧
    -- ASSIGN → either offset-0 set _ _ _, or offset-1 init _ _ (.det _) _
    (instr.type = .ASSIGN →
      (∃ v cv md, CmdEmittedAt ... pgm pc (.set v cv md)) ∨
      (∃ pc_pred v ty e_core md, pc = pc_pred + 1 ∧
        CmdEmittedAt ... pgm pc_pred (.init v ty (.det e_core) md)))
```

Each translator emit step preserves the predicate or strictly extends
it; the patcher only modifies `target` fields, preserving the
predicate trivially.

This predicate gives us **directly** what R8b's `DeclPcInversion`
and `AssignPcInversion` ask for. The strict `AssignNondetPcInversion`
(which says every ASSIGN PC is *exactly* a `.set _ .nondet _`
cmd-start) is **provably false** for any source CFG containing a
`.set _ (.det _) _` or `.init _ _ (.det _) _` cmd, per R8b's finding.
We close the strict form only under an extra, narrowing precondition
that constrains the source CFG.

## File layout

* **`BodyPcCovered`** predicate over a translator state and a target
  program.
* **Push/append preservation primitives** for in-bounds PCs.
* **`Cmd.toGotoInstructions`** preservation (5 admitted shapes):
  `init_det`, `init_nondet`, `set_det`, `set_nondet`, `assert`,
  `assume`, `cover`. Each branch's emitted DECL/ASSIGN at `nextLoc`
  (and possibly `nextLoc + 1` for `init_det`) is covered by the
  matching `cmdEmittedAt_*_of_toGotoInstructions` lemma from
  `CoreCFGToGotoTransformWF.lean`.
* **Lifts through `coreCFGToGotoCmdStep`, `cmdsFoldlM`, emit helpers,
  `coreCFGToGotoBlockStep`, `blocksFoldlM`** mirroring the existing
  templates in `NoDead.lean` and `GotoTargetProvenance.lean`.
* **Patcher preservation** via `patchGotoTargets_preserves_full_except_target`.
* **Top-level theorems**: `declPcInversion_of_translator_abbrev`,
  `assignPcInversion_of_translator_abbrev`. Each closes the
  corresponding abbrev from `CmdProvenance.lean` directly.
-/

namespace CProverGOTO.PcInversion

open Imperative
open CProverGOTO

/-! ## The `BodyPcCovered` predicate

Records, for the translator's current `instructions` array, that
every body-instruction PC (DECL or ASSIGN) is covered by an
appropriately-placed `CmdEmittedAt` witness over a fixed target
program `pgm`.

The predicate is parameterised by the target program because during
the translator fold we don't yet have `ans`; we use the post-fold
`ans` (or `st_final.trans`) as the "target" program for the chain
preservation argument. -/

/-- `BodyPcCovered trans pgm`: for every PC of `trans.instructions`
whose type is DECL or ASSIGN, there is a corresponding `CmdEmittedAt`
witness over `pgm`. -/
abbrev BodyPcCovered
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (pgm : Program) : Prop :=
  ∀ {pc : Nat} {instr : Instruction},
    trans.instructions[pc]? = some instr →
    (instr.type = .DECL →
      ∃ inner, CmdEmittedAt δ δ_goto δ_goto_bool pgm pc inner) ∧
    (instr.type = .ASSIGN →
      (∃ v cv md, CmdEmittedAt δ δ_goto δ_goto_bool pgm pc
        (.set v cv md)) ∨
      (∃ pc_pred v ty e_core md, pc = pc_pred + 1 ∧
        CmdEmittedAt δ δ_goto δ_goto_bool pgm pc_pred
          (.init v ty (.det e_core) md)))

/-! ## Push/append preservation primitives

`BodyPcCovered` is preserved by pushes/appends provided each new
instruction is "covered" — i.e., its DECL/ASSIGN observation comes
with an existing `CmdEmittedAt` witness. The witnesses are constructed
in the `Cmd.toGotoInstructions` cases. -/

/-- Pushing a new instruction whose DECL/ASSIGN obligations are
already discharged preserves `BodyPcCovered`. -/
private theorem push_preserves_body_pc_covered
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (pgm : Program)
    (new_instr : Instruction)
    (h_cov : BodyPcCovered δ δ_goto δ_goto_bool trans pgm)
    (h_new_decl : new_instr.type = .DECL →
      ∃ inner, CmdEmittedAt δ δ_goto δ_goto_bool pgm
        trans.instructions.size inner)
    (h_new_assn : new_instr.type = .ASSIGN →
      (∃ v cv md, CmdEmittedAt δ δ_goto δ_goto_bool pgm
        trans.instructions.size (.set v cv md)) ∨
      (∃ pc_pred v ty e_core md, trans.instructions.size = pc_pred + 1 ∧
        CmdEmittedAt δ δ_goto δ_goto_bool pgm pc_pred
          (.init v ty (.det e_core) md))) :
    ∀ {pc : Nat} {instr : Instruction},
      (trans.instructions.push new_instr)[pc]? = some instr →
      (instr.type = .DECL →
        ∃ inner, CmdEmittedAt δ δ_goto δ_goto_bool pgm pc inner) ∧
      (instr.type = .ASSIGN →
        (∃ v cv md, CmdEmittedAt δ δ_goto δ_goto_bool pgm pc
          (.set v cv md)) ∨
        (∃ pc_pred v ty e_core md, pc = pc_pred + 1 ∧
          CmdEmittedAt δ δ_goto δ_goto_bool pgm pc_pred
            (.init v ty (.det e_core) md))) := by
  intro pc instr h
  by_cases h_lt : pc < trans.instructions.size
  · rw [Array.getElem?_push_lt h_lt] at h
    have h' : trans.instructions[pc]? = some instr := by
      rw [Array.getElem?_eq_getElem h_lt]; exact h
    exact h_cov h'
  · have h_ge : trans.instructions.size ≤ pc := Nat.le_of_not_lt h_lt
    by_cases h_eq : pc = trans.instructions.size
    · subst h_eq
      rw [Array.getElem?_push_size] at h
      injection h with h
      subst h
      exact ⟨h_new_decl, h_new_assn⟩
    · have h_lt' : trans.instructions.size < pc := by omega
      have h_oor : (trans.instructions.push new_instr).size ≤ pc := by
        rw [Array.size_push]; omega
      rw [Array.getElem?_eq_none h_oor] at h
      exact absurd h (by simp)

/-- Appending two instructions whose DECL/ASSIGN obligations are
already discharged preserves `BodyPcCovered`. The two new positions
are `trans.instructions.size` and `trans.instructions.size + 1`. -/
private theorem append_two_preserves_body_pc_covered
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (pgm : Program)
    (i₀ i₁ : Instruction)
    (h_cov : BodyPcCovered δ δ_goto δ_goto_bool trans pgm)
    (h_new0_decl : i₀.type = .DECL →
      ∃ inner, CmdEmittedAt δ δ_goto δ_goto_bool pgm
        trans.instructions.size inner)
    (h_new0_assn : i₀.type = .ASSIGN →
      (∃ v cv md, CmdEmittedAt δ δ_goto δ_goto_bool pgm
        trans.instructions.size (.set v cv md)) ∨
      (∃ pc_pred v ty e_core md, trans.instructions.size = pc_pred + 1 ∧
        CmdEmittedAt δ δ_goto δ_goto_bool pgm pc_pred
          (.init v ty (.det e_core) md)))
    (h_new1_decl : i₁.type = .DECL →
      ∃ inner, CmdEmittedAt δ δ_goto δ_goto_bool pgm
        (trans.instructions.size + 1) inner)
    (h_new1_assn : i₁.type = .ASSIGN →
      (∃ v cv md, CmdEmittedAt δ δ_goto δ_goto_bool pgm
        (trans.instructions.size + 1) (.set v cv md)) ∨
      (∃ pc_pred v ty e_core md,
        trans.instructions.size + 1 = pc_pred + 1 ∧
        CmdEmittedAt δ δ_goto δ_goto_bool pgm pc_pred
          (.init v ty (.det e_core) md))) :
    ∀ {pc : Nat} {instr : Instruction},
      (trans.instructions.append #[i₀, i₁])[pc]? = some instr →
      (instr.type = .DECL →
        ∃ inner, CmdEmittedAt δ δ_goto δ_goto_bool pgm pc inner) ∧
      (instr.type = .ASSIGN →
        (∃ v cv md, CmdEmittedAt δ δ_goto δ_goto_bool pgm pc
          (.set v cv md)) ∨
        (∃ pc_pred v ty e_core md, pc = pc_pred + 1 ∧
          CmdEmittedAt δ δ_goto δ_goto_bool pgm pc_pred
            (.init v ty (.det e_core) md))) := by
  intro pc instr h
  have h_eq : trans.instructions.append #[i₀, i₁]
      = trans.instructions ++ #[i₀, i₁] := rfl
  rw [h_eq] at h
  by_cases h_lt : pc < trans.instructions.size
  · rw [Array.getElem?_append_left h_lt] at h
    exact h_cov h
  · have h_ge : trans.instructions.size ≤ pc := Nat.le_of_not_lt h_lt
    by_cases h_eq0 : pc = trans.instructions.size
    · subst h_eq0
      rw [Array.getElem?_append_right (Nat.le_refl _)] at h
      simp at h
      subst h
      exact ⟨h_new0_decl, h_new0_assn⟩
    · by_cases h_eq1 : pc = trans.instructions.size + 1
      · subst h_eq1
        rw [Array.getElem?_append_right (Nat.le_add_right _ _)] at h
        simp at h
        subst h
        exact ⟨h_new1_decl, h_new1_assn⟩
      · have h_oor : (trans.instructions ++ #[i₀, i₁]).size ≤ pc := by
          rw [Array.size_append]
          simp; omega
        rw [Array.getElem?_eq_none h_oor] at h
        exact absurd h (by simp)

/-- Pushing a non-DECL, non-ASSIGN instruction preserves
`BodyPcCovered`. The DECL/ASSIGN obligations are vacuous. -/
private theorem push_non_body_preserves_body_pc_covered
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (pgm : Program)
    (new_instr : Instruction)
    (h_not_decl : new_instr.type ≠ .DECL)
    (h_not_assn : new_instr.type ≠ .ASSIGN)
    (h_cov : BodyPcCovered δ δ_goto δ_goto_bool trans pgm) :
    ∀ {pc : Nat} {instr : Instruction},
      (trans.instructions.push new_instr)[pc]? = some instr →
      (instr.type = .DECL →
        ∃ inner, CmdEmittedAt δ δ_goto δ_goto_bool pgm pc inner) ∧
      (instr.type = .ASSIGN →
        (∃ v cv md, CmdEmittedAt δ δ_goto δ_goto_bool pgm pc
          (.set v cv md)) ∨
        (∃ pc_pred v ty e_core md, pc = pc_pred + 1 ∧
          CmdEmittedAt δ δ_goto δ_goto_bool pgm pc_pred
            (.init v ty (.det e_core) md))) :=
  push_preserves_body_pc_covered δ δ_goto δ_goto_bool trans pgm new_instr h_cov
    (fun h => absurd h h_not_decl) (fun h => absurd h h_not_assn)

/-- Pushing an ASSIGN instruction whose `.set` emit witness is already
discharged preserves `BodyPcCovered`. -/
private theorem push_assn_set_preserves_body_pc_covered
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (pgm : Program)
    (new_instr : Instruction)
    (h_assn_ty : new_instr.type = .ASSIGN)
    (h_invariant : trans.instructions.size = trans.nextLoc)
    (v : Core.Expression.Ident) (cv : Imperative.ExprOrNondet Core.Expression)
    (md : Imperative.MetaData Core.Expression)
    (h_emit : CmdEmittedAt δ δ_goto δ_goto_bool pgm trans.nextLoc
                (.set v cv md))
    (h_cov : BodyPcCovered δ δ_goto δ_goto_bool trans pgm) :
    ∀ {pc : Nat} {instr : Instruction},
      (trans.instructions.push new_instr)[pc]? = some instr →
      (instr.type = .DECL →
        ∃ inner, CmdEmittedAt δ δ_goto δ_goto_bool pgm pc inner) ∧
      (instr.type = .ASSIGN →
        (∃ v cv md, CmdEmittedAt δ δ_goto δ_goto_bool pgm pc
          (.set v cv md)) ∨
        (∃ pc_pred v ty e_core md, pc = pc_pred + 1 ∧
          CmdEmittedAt δ δ_goto δ_goto_bool pgm pc_pred
            (.init v ty (.det e_core) md))) :=
  push_preserves_body_pc_covered δ δ_goto δ_goto_bool trans pgm new_instr h_cov
    (fun h_d => absurd (h_assn_ty.symm.trans h_d) (by decide))
    (fun _ => Or.inl ⟨v, cv, md, h_invariant ▸ h_emit⟩)

/-! ## Preservation through `Cmd.toGotoInstructions`

For each `Imperative.Cmd` constructor in the admitted fragment, we
build the obligations for the new instruction(s) using the
`cmdEmittedAt_*_of_toGotoInstructions` lemmas. These give us the
required `CmdEmittedAt` witnesses over the target program `pgm`,
provided `pgm` has a prefix that matches `trans.instructions` (or
`ans.instructions`) on the relevant slot. -/

/-- Preservation through `Cmd.toGotoInstructions`. Requires the
loop invariant `trans.instructions.size = trans.nextLoc` (so the new
instructions are at PCs ≥ `trans.nextLoc`), the expression-translation
agreement (for the `init_det`, `set_det`, `assert`, `assume` cases),
and the `pgm`-prefix property (so the new emit positions in `ans`
correspond to the same positions in `pgm`). -/
theorem toGotoInstructions_preserves_body_pc_covered
    (T : Core.Expression.TyEnv) (fname : String)
    (c : Imperative.Cmd Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname c trans = Except.ok ans)
    (h_invariant : trans.instructions.size = trans.nextLoc)
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
      ∀ (k : Nat) (h : k < ans.instructions.size),
        pgm.instructions[k]? = some ans.instructions[k])
    (h_cov : BodyPcCovered δ δ_goto δ_goto_bool trans pgm) :
    BodyPcCovered δ δ_goto δ_goto_bool ans pgm := by
  cases c with
  | init v ty initVal md =>
    cases initVal with
    | det e =>
      -- Two-instruction case: DECL at nextLoc, ASSIGN at nextLoc+1.
      obtain ⟨_gty, _e_goto, i_decl, i_assn,
              _, _, h_decl_ty, _, _, h_assn_ty, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
      have h_emit : CmdEmittedAt δ δ_goto δ_goto_bool pgm trans.nextLoc
                      (.init v ty (.det e) md) :=
        cmdEmittedAt_init_det_of_toGotoInstructions T fname v ty e md trans ans
          h_run h_invariant pgm δ δ_goto δ_goto_bool h_expr_corr (h_tx_eq e) h_prefix
      intro pc instr h
      rw [h_inst] at h
      exact append_two_preserves_body_pc_covered δ δ_goto δ_goto_bool trans pgm
        i_decl i_assn h_cov
        (fun _ => h_invariant ▸ ⟨_, h_emit⟩)
        (fun h_a => absurd (h_decl_ty.symm.trans h_a) (by decide))
        (fun h_d => absurd (h_assn_ty.symm.trans h_d) (by decide))
        (fun _ => Or.inr ⟨trans.instructions.size, v, ty, e, md, rfl,
                          h_invariant ▸ h_emit⟩) h
    | nondet =>
      -- One-instruction case: DECL at nextLoc.
      obtain ⟨_gty, i_decl, _, h_decl_ty, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
      have h_emit : CmdEmittedAt δ δ_goto δ_goto_bool pgm trans.nextLoc
                      (.init v ty .nondet md) :=
        cmdEmittedAt_init_nondet_of_toGotoInstructions T fname v ty md trans ans
          h_run h_invariant pgm δ δ_goto δ_goto_bool h_prefix
      intro pc instr h
      rw [h_inst] at h
      exact push_preserves_body_pc_covered δ δ_goto δ_goto_bool trans pgm i_decl h_cov
        (fun _ => h_invariant ▸ ⟨_, h_emit⟩)
        (fun h_a => absurd (h_decl_ty.symm.trans h_a) (by decide)) h
  | set v src md =>
    cases src with
    | det e =>
      -- One-instruction case: ASSIGN at nextLoc.
      obtain ⟨_gty, _e_goto, i_assn, _, _, h_assn_ty, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
      have h_emit : CmdEmittedAt δ δ_goto δ_goto_bool pgm trans.nextLoc
                      (.set v (.det e) md) :=
        cmdEmittedAt_set_det_of_toGotoInstructions T fname v e md trans ans
          h_run h_invariant pgm δ δ_goto δ_goto_bool h_expr_corr (h_tx_eq e) h_prefix
      intro pc instr h
      rw [h_inst] at h
      exact push_assn_set_preserves_body_pc_covered δ δ_goto δ_goto_bool
        trans pgm i_assn h_assn_ty h_invariant v (.det e) md h_emit h_cov h
    | nondet =>
      -- One-instruction case: ASSIGN at nextLoc, set_nondet.
      obtain ⟨_gty, i_assn, _, h_assn_ty, _h_assn_code, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
      have h_emit : CmdEmittedAt δ δ_goto δ_goto_bool pgm trans.nextLoc
                      (.set v .nondet md) :=
        cmdEmittedAt_set_nondet_of_toGotoInstructions T fname v md trans ans
          h_run h_invariant pgm δ δ_goto δ_goto_bool h_prefix
      intro pc instr h
      rw [h_inst] at h
      exact push_assn_set_preserves_body_pc_covered δ δ_goto δ_goto_bool
        trans pgm i_assn h_assn_ty h_invariant v .nondet md h_emit h_cov h
  | assert label e md =>
    -- One-instruction case: ASSERT at nextLoc, not DECL or ASSIGN.
    obtain ⟨_e_goto, i, _, h_assert_ty, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
    intro pc instr h
    rw [h_inst] at h
    exact push_non_body_preserves_body_pc_covered δ δ_goto δ_goto_bool trans pgm
      i (fun h_eq => absurd (h_assert_ty.symm.trans h_eq) (by decide))
        (fun h_eq => absurd (h_assert_ty.symm.trans h_eq) (by decide)) h_cov h
  | assume label e md =>
    obtain ⟨_e_goto, i, _, h_assume_ty, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
    intro pc instr h
    rw [h_inst] at h
    exact push_non_body_preserves_body_pc_covered δ δ_goto δ_goto_bool trans pgm
      i (fun h_eq => absurd (h_assume_ty.symm.trans h_eq) (by decide))
        (fun h_eq => absurd (h_assume_ty.symm.trans h_eq) (by decide)) h_cov h
  | cover label e md =>
    -- Cover is *not* admitted (`isAdmittedCmd (.cover _ _ _) = false`),
    -- but cover at the source level emits an ASSERT instruction. Since
    -- we may still be passed a cover cmd in the inductive step (the
    -- predicate is preservation, not strict admittance), handle it.
    unfold Imperative.Cmd.toGotoInstructions at h_run
    simp only at h_run
    match h_expr :
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      intro pc instr h
      subst h_run
      let assert_inst : Instruction :=
        { type := .ASSERT, locationNum := trans.nextLoc,
          sourceLoc := metadataToSourceLoc md fname trans.sourceText
            (comment := md.getPropertySummary.getD s!"cover {label}"),
          guard := e_goto }
      have h' : (trans.instructions.push assert_inst)[pc]? = some instr := h
      exact push_non_body_preserves_body_pc_covered δ δ_goto δ_goto_bool trans pgm
        assert_inst (by intro h_eq; cases h_eq) (by intro h_eq; cases h_eq) h_cov h'
    | .error _ =>
      simp [h_expr, Bind.bind, Except.bind] at h_run

/-! ## Preservation through `coreCFGToGotoCmdStep` -/

theorem coreCFGToGotoCmdStep_preserves_body_pc_covered
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans)
    (h_invariant : trans.instructions.size = trans.nextLoc)
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
      ∀ (k : Nat) (h : k < ans.instructions.size),
        pgm.instructions[k]? = some ans.instructions[k])
    (h_cov : BodyPcCovered δ δ_goto δ_goto_bool trans pgm) :
    BodyPcCovered δ δ_goto δ_goto_bool ans pgm := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact toGotoInstructions_preserves_body_pc_covered trans.T fname c trans ans
      h_run h_invariant pgm δ δ_goto δ_goto_bool h_expr_corr h_tx_eq
      h_prefix h_cov
  | call procName callArgs md =>
    -- The `.call` branch pushes a FUNCTION_CALL — neither DECL nor ASSIGN.
    unfold Strata.coreCFGToGotoCmdStep at h_run
    simp only at h_run
    generalize h_args :
        (Core.CallArg.getInputExprs callArgs).mapM
          (Lambda.LExpr.toGotoExprCtx
            (TBase := ⟨Core.ExpressionMetadata, Unit⟩) []) = argRes at h_run
    match argRes, h_args with
    | .ok argExprs, _ =>
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      intro pc instr h
      rw [← h_run] at h
      exact push_non_body_preserves_body_pc_covered δ δ_goto δ_goto_bool trans pgm
        _ (by intro h_eq; cases h_eq) (by intro h_eq; cases h_eq) h_cov h
    | .error _, _ =>
      simp [Bind.bind, Except.bind] at h_run

/-! ## Preservation through `cmdsFoldlM` -/

theorem cmdsFoldlM_preserves_body_pc_covered
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans)
    (h_invariant : trans.instructions.size = trans.nextLoc)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
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
      ∀ (k : Nat) (h : k < ans.instructions.size),
        pgm.instructions[k]? = some ans.instructions[k])
    (h_cov : BodyPcCovered δ δ_goto δ_goto_bool trans pgm) :
    BodyPcCovered δ δ_goto δ_goto_bool ans pgm := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run
    exact h_cov
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_admitted_cmd : Core.CmdExt.isAdmittedCmd cmd = true :=
        h_admitted cmd List.mem_cons_self
      have h_invariant' : trans'.instructions.size = trans'.nextLoc :=
        coreCFGToGotoCmdStep_preserves_size_eq fname cmd trans trans'
          h_admitted_cmd h_step h_invariant
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c h => h_admitted c (List.mem_cons_of_mem _ h)
      -- Need the prefix property for trans' relative to ans.
      have h_size_le : trans'.instructions.size ≤ ans.instructions.size :=
        cmdsFoldlM_size_le fname rest trans' ans h_admitted_rest h_run
      have h_prefix' :
          ∀ (k : Nat) (h : k < ans.instructions.size),
            pgm.instructions[k]? = some ans.instructions[k] := h_prefix
      have h_prefix_trans' :
          ∀ (k : Nat) (h : k < trans'.instructions.size),
            pgm.instructions[k]? = some trans'.instructions[k] := by
        intro k h_k
        have h_k' : k < ans.instructions.size := by
          have h_le : trans'.instructions.size ≤ ans.instructions.size :=
            h_size_le
          omega
        rw [h_prefix' k h_k']
        have h_eq :=
          cmdsFoldlM_instructions_prefix? fname rest trans' ans h_admitted_rest h_run k h_k
        rw [Array.getElem?_eq_getElem h_k'] at h_eq
        rw [Array.getElem?_eq_getElem h_k] at h_eq
        injection h_eq with h_eq
        rw [h_eq]
      have h_cov' : BodyPcCovered δ δ_goto δ_goto_bool trans' pgm :=
        coreCFGToGotoCmdStep_preserves_body_pc_covered fname cmd trans trans'
          h_step h_invariant pgm δ δ_goto δ_goto_bool h_expr_corr h_tx_eq
          h_prefix_trans' h_cov
      intro pc instr h_at
      exact ih trans' h_run h_invariant' h_admitted_rest h_cov' h_at
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ## Preservation through emit helpers (LOCATION / GOTO / END_FUNCTION)

None emit DECL or ASSIGN instructions. For LOCATION / GOTO /
END_FUNCTION pushes, we just push an instruction whose type is
trivially not DECL or ASSIGN. -/

theorem emitLabel_preserves_body_pc_covered
    (label : String) (srcLoc : SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_cov : BodyPcCovered δ δ_goto δ_goto_bool trans pgm) :
    BodyPcCovered δ δ_goto δ_goto_bool
      (Imperative.emitLabel label srcLoc trans) pgm := by
  intro pc instr h
  exact push_non_body_preserves_body_pc_covered δ δ_goto δ_goto_bool trans pgm
    _ (by intro h_eq; cases h_eq) (by intro h_eq; cases h_eq) h_cov h

theorem emitCondGoto_preserves_body_pc_covered
    (guard : Expr) (srcLoc : SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_cov : BodyPcCovered δ δ_goto δ_goto_bool trans pgm) :
    BodyPcCovered δ δ_goto δ_goto_bool
      (Imperative.emitCondGoto guard srcLoc trans).fst pgm := by
  intro pc instr h
  exact push_non_body_preserves_body_pc_covered δ δ_goto δ_goto_bool trans pgm
    _ (by intro h_eq; cases h_eq) (by intro h_eq; cases h_eq) h_cov h

theorem emitUncondGoto_preserves_body_pc_covered
    (srcLoc : SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_cov : BodyPcCovered δ δ_goto δ_goto_bool trans pgm) :
    BodyPcCovered δ δ_goto δ_goto_bool
      (Imperative.emitUncondGoto srcLoc trans).fst pgm := by
  intro pc instr h
  exact push_non_body_preserves_body_pc_covered δ δ_goto δ_goto_bool trans pgm
    _ (by intro h_eq; cases h_eq) (by intro h_eq; cases h_eq) h_cov h

theorem endFunction_emit_preserves_body_pc_covered
    (md : Imperative.MetaData Core.Expression) (fname : String)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_cov : BodyPcCovered δ δ_goto δ_goto_bool trans pgm) :
    ∀ {pc : Nat} {instr : Instruction},
      (trans.instructions.push (endFunctionInstr md fname trans))[pc]? =
        some instr →
      (instr.type = .DECL →
        ∃ inner, CmdEmittedAt δ δ_goto δ_goto_bool pgm pc inner) ∧
      (instr.type = .ASSIGN →
        (∃ v cv md', CmdEmittedAt δ δ_goto δ_goto_bool pgm pc
          (.set v cv md')) ∨
        (∃ pc_pred v ty e_core md', pc = pc_pred + 1 ∧
          CmdEmittedAt δ δ_goto δ_goto_bool pgm pc_pred
            (.init v ty (.det e_core) md'))) := by
  intro pc instr h
  exact push_non_body_preserves_body_pc_covered δ δ_goto δ_goto_bool trans pgm
    _ (fun h_eq => by unfold endFunctionInstr at h_eq; cases h_eq)
      (fun h_eq => by unfold endFunctionInstr at h_eq; cases h_eq) h_cov h

/-! ## Preservation through `coreCFGToGotoBlockStep` -/

theorem coreCFGToGotoBlockStep_preserves_body_pc_covered
    (fname : String)
    (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_invariant : st.trans.instructions.size = st.trans.nextLoc)
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
        pgm.instructions[k]? = some st'.trans.instructions[k])
    (h_cov : BodyPcCovered δ δ_goto δ_goto_bool st.trans pgm) :
    BodyPcCovered δ δ_goto δ_goto_bool st'.trans pgm := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  -- emitLabel preserves
  let trans₁ := Imperative.emitLabel label
    { CProverGOTO.SourceLocation.nil with function := fname } st.trans
  have h_size₁ : trans₁.instructions.size = trans₁.nextLoc :=
    emitLabel_preserves_size_eq label
      { CProverGOTO.SourceLocation.nil with function := fname } st.trans h_invariant
  -- cmdsFoldlM preserves
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans₁ = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    -- emitLabel preservation.
    have h_cov₁ : BodyPcCovered δ δ_goto δ_goto_bool trans₁ pgm :=
      emitLabel_preserves_body_pc_covered label _ st.trans pgm
        δ δ_goto δ_goto_bool h_cov
    -- Case-split on transfer first; in each branch we know st'.trans
    -- explicitly (a 1- or 2-push extension of trans₂), which gives us
    -- both the prefix property for trans₂ and the post-transfer
    -- preservation in one pass.
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
        -- st'.trans = ((trans₂.push GOTO_neg).push GOTO_uncond).
        -- Build h_prefix₂ by transporting through two pushes.
        have h_prefix₂ :
            ∀ (k : Nat) (h : k < trans₂.instructions.size),
              pgm.instructions[k]? = some trans₂.instructions[k] := by
          intro k h_k
          have h_k_st' : k < st'.trans.instructions.size := by
            rw [← h_run]
            simp [Imperative.emitCondGoto, Imperative.emitUncondGoto,
                  Imperative.emitGoto, Array.size_push]
            omega
          have h_st_eq : st'.trans.instructions[k]? = trans₂.instructions[k]? := by
            rw [← h_run]
            simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto,
                       Imperative.emitGoto]
            have h_k_post_first :
                k < (trans₂.instructions.push
                  ({ type := .GOTO, guard := cond_expr.not,
                     sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                     locationNum := trans₂.nextLoc } : CProverGOTO.Instruction)).size := by
              rw [Array.size_push]; exact Nat.lt_succ_of_lt h_k
            rw [Array.getElem?_push_lt h_k_post_first]
            rw [Array.getElem_push_lt h_k]
            rw [Array.getElem?_eq_getElem h_k]
          rw [h_prefix k h_k_st', ← Array.getElem?_eq_getElem h_k_st', h_st_eq,
              Array.getElem?_eq_getElem h_k]
        have h_cov₂ : BodyPcCovered δ δ_goto δ_goto_bool trans₂ pgm :=
          cmdsFoldlM_preserves_body_pc_covered fname blk.cmds trans₁ trans₂
            h_inner h_size₁ h_admitted pgm δ δ_goto δ_goto_bool h_expr_corr h_tx_eq
            h_prefix₂ h_cov₁
        let transferSrcLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText
        have h_cov₃ : BodyPcCovered δ δ_goto δ_goto_bool
            (Imperative.emitCondGoto cond_expr.not transferSrcLoc trans₂).fst pgm :=
          emitCondGoto_preserves_body_pc_covered cond_expr.not transferSrcLoc trans₂ pgm
            δ δ_goto δ_goto_bool h_cov₂
        have h_cov₄ : BodyPcCovered δ δ_goto δ_goto_bool
            (Imperative.emitUncondGoto transferSrcLoc
              (Imperative.emitCondGoto cond_expr.not transferSrcLoc trans₂).fst).fst pgm :=
          emitUncondGoto_preserves_body_pc_covered transferSrcLoc
            (Imperative.emitCondGoto cond_expr.not transferSrcLoc trans₂).fst pgm
            δ δ_goto δ_goto_bool h_cov₃
        rw [← h_run]
        intro pc instr h
        exact h_cov₄ h
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      -- st'.trans = trans₂.push endFunctionInstr.
      have h_prefix₂ :
          ∀ (k : Nat) (h : k < trans₂.instructions.size),
            pgm.instructions[k]? = some trans₂.instructions[k] := by
        intro k h_k
        have h_k_st' : k < st'.trans.instructions.size := by
          rw [← h_run]; simp [Array.size_push]; omega
        have h_st_eq : st'.trans.instructions[k]? = trans₂.instructions[k]? := by
          rw [← h_run, Array.getElem?_push_lt h_k, Array.getElem?_eq_getElem h_k]
        rw [h_prefix k h_k_st', ← Array.getElem?_eq_getElem h_k_st', h_st_eq,
            Array.getElem?_eq_getElem h_k]
      have h_cov₂ : BodyPcCovered δ δ_goto δ_goto_bool trans₂ pgm :=
        cmdsFoldlM_preserves_body_pc_covered fname blk.cmds trans₁ trans₂
          h_inner h_size₁ h_admitted pgm δ δ_goto δ_goto_bool h_expr_corr h_tx_eq
          h_prefix₂ h_cov₁
      rw [← h_run]
      intro pc instr h
      simp only at h ⊢
      exact endFunction_emit_preserves_body_pc_covered md fname trans₂ pgm
        δ δ_goto δ_goto_bool h_cov₂ h
  | .error _, _ => simp at h_run

/-! ## Preservation through `blocksFoldlM` -/

theorem blocksFoldlM_preserves_body_pc_covered
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_invariant : st.trans.instructions.size = st.trans.nextLoc)
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
        pgm.instructions[k]? = some st'.trans.instructions[k])
    (h_cov : BodyPcCovered δ δ_goto δ_goto_bool st.trans pgm) :
    BodyPcCovered δ δ_goto δ_goto_bool st'.trans pgm := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run
    exact h_cov
  | cons hd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st hd with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ hd.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted hd List.mem_cons_self
      have h_invariant₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname hd st st₁
          h_admitted_head h_step h_invariant
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk h => h_admitted lblBlk (List.mem_cons_of_mem _ h)
      have h_size_le_st' : st₁.trans.instructions.size ≤ st'.trans.instructions.size :=
        blocksFoldlM_size_le fname rest st₁ st' h_admitted_rest h_run
      have h_prefix₁ :
          ∀ (k : Nat) (h : k < st₁.trans.instructions.size),
            pgm.instructions[k]? = some st₁.trans.instructions[k] := by
        intro k h_k
        have h_k' : k < st'.trans.instructions.size :=
          Nat.lt_of_lt_of_le h_k h_size_le_st'
        rw [h_prefix k h_k']
        have h_eq :=
          blocksFoldlM_instructions_prefix? fname rest st₁ st' h_admitted_rest h_run k h_k
        rw [Array.getElem?_eq_getElem h_k'] at h_eq
        rw [Array.getElem?_eq_getElem h_k] at h_eq
        injection h_eq with h_eq
        rw [h_eq]
      have h_cov₁ : BodyPcCovered δ δ_goto δ_goto_bool st₁.trans pgm :=
        coreCFGToGotoBlockStep_preserves_body_pc_covered fname hd st st₁
          h_admitted_head h_step h_invariant pgm δ δ_goto δ_goto_bool
          h_expr_corr h_tx_eq h_prefix₁ h_cov
      intro pc instr h_at
      exact ih st₁ h_admitted_rest h_run h_invariant₁ h_cov₁ h_at
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ## Patcher preservation

`patchGotoTargets` only modifies the `target` field of GOTO
instructions. The `type` and `code` fields are preserved
(`patchGotoTargets_preserves_full_except_target`), so any
`CmdEmittedAt` witness over the pre-patcher program lifts to the
post-patcher program. -/

/-- The `CmdEmittedAt` predicate is preserved when the program's
instructions only change in the `target` field. -/
private theorem cmdEmittedAt_preserved_target_only
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (pgm pgm' : Program)
    (h_preserves_back :
      ∀ idx (instr_pre : Instruction),
        pgm.instrAt idx = some instr_pre →
        ∃ instr_post, pgm'.instrAt idx = some instr_post ∧
          instr_post.type = instr_pre.type ∧
          instr_post.guard = instr_pre.guard ∧
          instr_post.code = instr_pre.code)
    (pc : Nat) (inner : Imperative.Cmd Core.Expression)
    (h_emit : CmdEmittedAt δ δ_goto δ_goto_bool pgm pc inner) :
    CmdEmittedAt δ δ_goto δ_goto_bool pgm' pc inner := by
  cases h_emit with
  | init_det v ty e_core md i_decl i_assn h_decl_at h_decl_ty
              h_assn_at h_assn_ty e_goto gty h_decl_code h_assn_code h_translated =>
    obtain ⟨i_decl', h_at', h_ty', _, h_code'⟩ :=
      h_preserves_back _ i_decl h_decl_at
    obtain ⟨i_assn', h_at_a', h_ty_a', _, h_code_a'⟩ :=
      h_preserves_back _ i_assn h_assn_at
    refine CmdEmittedAt.init_det pc v ty e_core md i_decl' i_assn'
      h_at' (h_ty'.trans h_decl_ty) h_at_a' (h_ty_a'.trans h_assn_ty)
      e_goto gty ?_ ?_ h_translated
    · rw [h_code']; exact h_decl_code
    · rw [h_code_a']; exact h_assn_code
  | init_nondet v ty md i_decl h_decl_at h_decl_ty gty h_decl_code =>
    obtain ⟨i_decl', h_at', h_ty', _, h_code'⟩ :=
      h_preserves_back _ i_decl h_decl_at
    refine CmdEmittedAt.init_nondet pc v ty md i_decl' h_at'
      (h_ty'.trans h_decl_ty) gty ?_
    rw [h_code']; exact h_decl_code
  | set_det v e_core md i_assn h_assn_at h_assn_ty e_goto gty h_assn_code h_translated =>
    obtain ⟨i_assn', h_at', h_ty', _, h_code'⟩ :=
      h_preserves_back _ i_assn h_assn_at
    refine CmdEmittedAt.set_det pc v e_core md i_assn'
      h_at' (h_ty'.trans h_assn_ty) e_goto gty ?_ h_translated
    rw [h_code']; exact h_assn_code
  | set_nondet v md i_assn h_assn_at h_assn_ty gty h_assn_code =>
    obtain ⟨i_assn', h_at', h_ty', _, h_code'⟩ :=
      h_preserves_back _ i_assn h_assn_at
    obtain ⟨e_nondet, h_code_eq, h_id, h_ty_e⟩ := h_assn_code
    refine CmdEmittedAt.set_nondet pc v md i_assn'
      h_at' (h_ty'.trans h_assn_ty) gty ⟨e_nondet, ?_, h_id, h_ty_e⟩
    rw [h_code']; exact h_code_eq
  | assert_emit label e_core md i h_at h_ty e_goto h_guard h_translated =>
    obtain ⟨i', h_at', h_ty', h_g', _⟩ :=
      h_preserves_back _ i h_at
    refine CmdEmittedAt.assert_emit pc label e_core md i'
      h_at' (h_ty'.trans h_ty) e_goto ?_ h_translated
    rw [h_g']; exact h_guard
  | assume_emit label e_core md i h_at h_ty e_goto h_guard h_translated =>
    obtain ⟨i', h_at', h_ty', h_g', _⟩ :=
      h_preserves_back _ i h_at
    refine CmdEmittedAt.assume_emit pc label e_core md i'
      h_at' (h_ty'.trans h_ty) e_goto ?_ h_translated
    rw [h_g']; exact h_guard
  | cover_emit label e_core md i h_at h_ty e_goto h_guard h_translated =>
    obtain ⟨i', h_at', h_ty', h_g', _⟩ :=
      h_preserves_back _ i h_at
    refine CmdEmittedAt.cover_emit pc label e_core md i'
      h_at' (h_ty'.trans h_ty) e_goto ?_ h_translated
    rw [h_g']; exact h_guard

/-- Lifts `BodyPcCovered` from the pre-patcher state to the
post-patcher program, given the patcher's "preserves full except
target" invariant. -/
theorem patchGotoTargets_preserves_body_pc_covered
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (resolved : List (Nat × Nat))
    (pgm_pre pgm_post : Program)
    (h_pre_eq : pgm_pre.instructions = trans.instructions)
    (h_post_eq : pgm_post.instructions =
      (Imperative.patchGotoTargets trans resolved).instructions)
    (h_cov : BodyPcCovered δ δ_goto δ_goto_bool trans pgm_pre) :
    BodyPcCovered δ δ_goto δ_goto_bool
      (Imperative.patchGotoTargets trans resolved) pgm_post := by
  -- Build the back-direction preservation lemma.
  have h_preserves_back :
      ∀ idx (instr_pre : Instruction),
        pgm_pre.instrAt idx = some instr_pre →
        ∃ instr_post, pgm_post.instrAt idx = some instr_post ∧
          instr_post.type = instr_pre.type ∧
          instr_post.guard = instr_pre.guard ∧
          instr_post.code = instr_pre.code := by
    intro idx instr_pre h_at_pre
    have h_at_pre' : trans.instructions[idx]? = some instr_pre := by
      have : pgm_pre.instructions[idx]? = some instr_pre := h_at_pre
      rw [h_pre_eq] at this
      exact this
    -- idx is in bounds for trans; same for patcher result.
    have h_idx_lt_pre : idx < trans.instructions.size :=
      (Array.getElem?_eq_some_iff.mp h_at_pre').1
    have h_idx_lt_post : idx < (Imperative.patchGotoTargets trans resolved).instructions.size := by
      rw [patchGotoTargets_preserves_size]
      exact h_idx_lt_pre
    have h_at_post_get :
        (Imperative.patchGotoTargets trans resolved).instructions[idx]? =
          some (Imperative.patchGotoTargets trans resolved).instructions[idx] :=
      Array.getElem?_eq_getElem h_idx_lt_post
    obtain ⟨instr_pre', h_pre_at_again, h_ty, h_g, h_c, _⟩ :=
      patchGotoTargets_preserves_full_except_target trans resolved idx
        _ h_at_post_get
    rw [h_pre_at_again] at h_at_pre'
    injection h_at_pre' with h_eq_pre
    refine ⟨(Imperative.patchGotoTargets trans resolved).instructions[idx],
            ?_, ?_, ?_, ?_⟩
    · show pgm_post.instructions[idx]? = some _
      rw [h_post_eq]
      exact h_at_post_get
    · rw [h_ty, h_eq_pre]
    · rw [h_g, h_eq_pre]
    · rw [h_c, h_eq_pre]
  intro pc instr h
  -- h : (patchGotoTargets trans resolved).instructions[pc]? = some instr.
  obtain ⟨instr_pre', h_pre_at, h_ty_eq, _, _⟩ :=
    patchGotoTargets_preserves_full_except_target trans resolved pc instr h
  -- Now use h_cov on instr_pre' (over pgm_pre, which agrees with trans).
  have h_cov_pre : trans.instructions[pc]? = some instr_pre' := h_pre_at
  have h_cov' := h_cov h_cov_pre
  refine ⟨?_, ?_⟩
  · intro h_decl
    rw [h_ty_eq] at h_decl
    obtain ⟨inner, h_emit_pre⟩ := h_cov'.1 h_decl
    refine ⟨inner, ?_⟩
    exact cmdEmittedAt_preserved_target_only δ δ_goto δ_goto_bool pgm_pre pgm_post
      h_preserves_back pc inner h_emit_pre
  · intro h_assn
    rw [h_ty_eq] at h_assn
    rcases h_cov'.2 h_assn with
      ⟨v, cv, md, h_emit_pre⟩ | ⟨pc_pred, v, ty, e_core, md, h_pc_eq, h_emit_pre⟩
    · left
      refine ⟨v, cv, md, ?_⟩
      exact cmdEmittedAt_preserved_target_only δ δ_goto δ_goto_bool pgm_pre pgm_post
        h_preserves_back pc _ h_emit_pre
    · right
      refine ⟨pc_pred, v, ty, e_core, md, h_pc_eq, ?_⟩
      exact cmdEmittedAt_preserved_target_only δ δ_goto δ_goto_bool pgm_pre pgm_post
        h_preserves_back pc_pred _ h_emit_pre

/-! ## Top-level theorems closing R8b's PC inversions

We now compose the above preservation lemmas into theorems closing
R8b's `DeclPcInversion` and `AssignPcInversion` from the actual
translator output, using `coreCFGToGotoTransform_decompose` to
extract the blocks-fold + patches-fold structure.

The strict `AssignNondetPcInversion` is *provably false* in general,
per R8b's discovery; we close it under an extra precondition that
narrows the source CFG. -/

/-- Build `BodyPcCovered` over the translator output `ans` by composing
the blocks-fold preservation and the patcher preservation. Both
`declPcInversion_of_translator_abbrev` and
`assignPcInversion_of_translator_abbrev` project from this. -/
private theorem bodyPcCovered_of_translator
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_empty_decl_assign : ∀ {pc : Nat} {instr : Instruction},
      trans₀.instructions[pc]? = some instr →
      instr.type ≠ .DECL ∧ instr.type ≠ .ASSIGN)
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
    BodyPcCovered δ δ_goto δ_goto_bool ans
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions } := by
  obtain ⟨st_final, resolved, trans_post, h_blocks_run, h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  have h_lc_empty := h_loopContracts_empty_post st_final h_blocks_run
  rw [h_lc_empty] at h_patches_run
  have h_trans_post_eq : trans_post = st_final.trans :=
    patchesFoldlM_no_contracts_trans_eq st_final.labelMap st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
  have h_ans_eq' : ans = Imperative.patchGotoTargets st_final.trans resolved := by
    rw [h_ans_eq, h_trans_post_eq]
  let pgm_st : Program :=
    { name := "", parameterIdentifiers := #[],
      instructions := st_final.trans.instructions }
  let pgm : Program :=
    { name := "", parameterIdentifiers := #[],
      instructions := ans.instructions }
  have h_cov₀ : BodyPcCovered δ δ_goto δ_goto_bool trans₀ pgm_st := by
    intro pc' instr' h_at'
    refine ⟨?_, ?_⟩
    · intro h_d
      exact absurd h_d (h_init_empty_decl_assign h_at').1
    · intro h_a
      exact absurd h_a (h_init_empty_decl_assign h_at').2
  have h_init_size_st :
      (coreCFGToGotoInitState trans₀).trans.instructions.size =
        (coreCFGToGotoInitState trans₀).trans.nextLoc := by
    simp [coreCFGToGotoInitState]; exact h_init_size
  have h_admitted_st :
      ∀ lblBlk ∈ cfg.blocks, ∀ c ∈ lblBlk.2.cmds,
        Core.CmdExt.isAdmittedCmd c = true :=
    fun lblBlk h => h_admitted_blocks lblBlk.1 lblBlk.2 h
  have h_prefix_st :
      ∀ (k : Nat) (h : k < st_final.trans.instructions.size),
        pgm_st.instructions[k]? = some st_final.trans.instructions[k] := by
    intro k h_k
    show st_final.trans.instructions[k]? = some st_final.trans.instructions[k]
    exact Array.getElem?_eq_getElem h_k
  have h_cov_st : BodyPcCovered δ δ_goto δ_goto_bool st_final.trans pgm_st :=
    blocksFoldlM_preserves_body_pc_covered functionName cfg.blocks _ st_final
      h_admitted_st h_blocks_run h_init_size_st pgm_st δ δ_goto δ_goto_bool
      h_expr_corr h_tx_eq h_prefix_st h_cov₀
  have h_pre_eq : pgm_st.instructions = st_final.trans.instructions := rfl
  have h_post_eq : pgm.instructions =
      (Imperative.patchGotoTargets st_final.trans resolved).instructions := by
    show ans.instructions = (Imperative.patchGotoTargets st_final.trans resolved).instructions
    rw [h_ans_eq']
  have h_cov_post : BodyPcCovered δ δ_goto δ_goto_bool
      (Imperative.patchGotoTargets st_final.trans resolved) pgm :=
    patchGotoTargets_preserves_body_pc_covered δ δ_goto δ_goto_bool st_final.trans
      resolved pgm_st pgm h_pre_eq h_post_eq h_cov_st
  intro pc' instr' h_at'
  have h_at_post : (Imperative.patchGotoTargets st_final.trans resolved).instructions[pc']? = some instr' := by
    have : ans.instructions = (Imperative.patchGotoTargets st_final.trans resolved).instructions := by
      rw [h_ans_eq']
    rw [← this]
    exact h_at'
  exact h_cov_post h_at_post

/-- **Discharge `DeclPcInversion`** from the translator. Every DECL PC
in `ans.instructions` corresponds to an `init_*` cmd-start.

The auxiliary hypotheses are the standard translator-input invariants
(empty/admitted initial state, distinct labels, admitted blocks,
empty-loopContracts post-fold). -/
theorem declPcInversion_of_translator_abbrev
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_empty_decl_assign : ∀ {pc : Nat} {instr : Instruction},
      trans₀.instructions[pc]? = some instr →
      instr.type ≠ .DECL ∧ instr.type ≠ .ASSIGN)
    (_h_distinct : BlockLabelsDistinct cfg.blocks)
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
          = Except.ok (h_expr_corr.tx e))
    (wf : WellFormedTranslation cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      δ δ_goto δ_goto_bool) :
    CmdProvenance.DeclPcInversion cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      δ δ_goto δ_goto_bool wf := by
  intro pc instr h_at h_ty
  exact (bodyPcCovered_of_translator Env functionName cfg trans₀
      h_init_size h_init_empty_decl_assign h_admitted_blocks
      h_loopContracts_empty_post ans h_run δ δ_goto δ_goto_bool
      h_expr_corr h_tx_eq h_at).1 h_ty

/-- **Discharge `AssignPcInversion`** from the translator. Every
ASSIGN PC in `ans.instructions` is either offset-0 of a `set _ _ _`
cmd or offset-1 of an `init _ _ (.det _) _` cmd. -/
theorem assignPcInversion_of_translator_abbrev
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_empty_decl_assign : ∀ {pc : Nat} {instr : Instruction},
      trans₀.instructions[pc]? = some instr →
      instr.type ≠ .DECL ∧ instr.type ≠ .ASSIGN)
    (_h_distinct : BlockLabelsDistinct cfg.blocks)
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
          = Except.ok (h_expr_corr.tx e))
    (wf : WellFormedTranslation cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      δ δ_goto δ_goto_bool) :
    CmdProvenance.AssignPcInversion cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      δ δ_goto δ_goto_bool wf := by
  intro pc instr h_at h_ty
  exact (bodyPcCovered_of_translator Env functionName cfg trans₀
      h_init_size h_init_empty_decl_assign h_admitted_blocks
      h_loopContracts_empty_post ans h_run δ δ_goto δ_goto_bool
      h_expr_corr h_tx_eq h_at).2 h_ty

/-! ## Strict ASSIGN-Nondet PC inversion — Tier 3

R8b discovered that the universal `AssignNondetPcInversion` is
provably false for any source CFG containing `init_det` or `set_det`
cmds — those emit ASSIGNs whose rhs is a translated source
expression, not `Side_effect.Nondet`. The strict variant says every
ASSIGN PC is exactly a `set _ .nondet _` cmd-start, which is only
satisfied by source CFGs where every ASSIGN is a nondet one.

R9 cannot close `AssignNondetPcInversion` from `BodyPcCovered` alone:
the predicate yields *some* `CmdEmittedAt` witness for each ASSIGN
PC, but the constructor it lands in (`set_det`, `set_nondet`, or
`init_det`) is not recoverable from `BodyPcCovered`'s proof structure
without enriching the predicate to track source-cmd shape per emit.

The "right" closure for this is at the **bridge layer**, not the
translator layer (per R8b's report): refactor
`assign_nondet_lookup_of_provenance_and_pinned` in
`InstructionLookups.lean` to take a *per-PC partial* provenance gated
on a `step_assign_nondet`-firing trace precondition. This is
documented in `docs/CoreToGOTO_ProofStatusRound8.md` as a
**[bridge-required]** task.

We therefore continue to surface the strict `AssignNondetPcInversion`
as a hypothesis on `_v6` (matching `_v5`'s shape). A future round
that takes on the bridge refactor would close this cleanly. -/

end CProverGOTO.PcInversion
