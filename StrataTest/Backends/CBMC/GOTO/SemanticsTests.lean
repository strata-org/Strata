/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.Semantics
import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOInvariants
import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOCorrect

/-! # Sanity tests for the GOTO operational semantics and simulation skeleton

Concrete instantiations of the `Sim` relation, `WellFormedTranslation`
predicate, and `block_simulation_empty_finish` lemma. These exercise the
machinery on the simplest possible program — a single empty block with a
`finish` transfer — and confirm the types compose end-to-end.

The full forward-simulation theorem
(`coreCFGToGoto_forward_simulation`) is currently `sorry`-blocked; tests
that depend on it would also need to be `sorry`-blocked, providing little
verification value. -/

namespace CProverGOTOTests

open CProverGOTO Imperative

/-! ## Trivial CFG: a single block, empty body, `finish` transfer -/

/-- The block of the trivial CFG. -/
def trivialBlock : Imperative.DetBlock String Core.Command Core.Expression :=
  { cmds := []
    transfer := .finish .empty }

/-- The simplest possible `DetCFG`: one block named `"entry"` with no
commands, terminating with `.finish`. -/
def trivialCfg : Core.DetCFG :=
  { entry := "entry"
    blocks := [("entry", trivialBlock)] }

/-- The corresponding GOTO program: a `LOCATION` followed by an
`END_FUNCTION`. The labels `["entry"]` on the LOCATION are cosmetic. -/
def trivialPgm : Program :=
  { name := "main"
    parameterIdentifiers := #[]
    instructions := #[
      { type := .LOCATION, locationNum := 0, labels := ["entry"] },
      { type := .END_FUNCTION, locationNum := 1 }
    ] }

private def trivialLabelMap : LabelMap :=
  fun l => if l = "entry" then some 0 else none

private theorem trivial_labelMap_total :
    ∀ l, l ∈ trivialCfg.blocks.map Prod.fst → (trivialLabelMap l).isSome := by
  intro l hl
  simp [trivialCfg] at hl
  subst hl
  simp [trivialLabelMap]

private theorem trivial_labelMap_inj :
    ∀ l₁ l₂ pc, trivialLabelMap l₁ = some pc →
      trivialLabelMap l₂ = some pc → l₁ = l₂ := by
  intro l₁ l₂ pc h₁ h₂
  by_cases h1 : l₁ = "entry"
  · by_cases h2 : l₂ = "entry"
    · subst h1; subst h2; rfl
    · simp [trivialLabelMap, h2] at h₂
  · simp [trivialLabelMap, h1] at h₁

private theorem trivial_layout_location :
    ∀ l blk pc,
      (l, blk) ∈ trivialCfg.blocks → trivialLabelMap l = some pc →
      ∃ instr, trivialPgm.instrAt pc = some instr ∧ instr.type = .LOCATION := by
  intro l blk pc h_blk h_pc
  simp [trivialCfg] at h_blk
  obtain ⟨h_l, _⟩ := h_blk
  subst h_l
  simp [trivialLabelMap] at h_pc
  subst h_pc
  exact ⟨_, rfl, rfl⟩

private theorem trivial_layout_cond_goto :
    ∀ l blk pc cond lt lf md, (l, blk) ∈ trivialCfg.blocks →
      trivialLabelMap l = some pc →
      blk.transfer = .condGoto cond lt lf md →
      ∃ pc_neg pc_uncond pc_lf pc_lt instr_neg instr_uncond,
        pc_neg = pc + 1 + DetBlockBodyInstrCount blk ∧
        pc_uncond = pc_neg + 1 ∧
        trivialPgm.instrAt pc_neg = some instr_neg ∧
        instr_neg.type = .GOTO ∧
        instr_neg.target = some pc_lf ∧
        trivialLabelMap lf = some pc_lf ∧
        trivialPgm.instrAt pc_uncond = some instr_uncond ∧
        instr_uncond.type = .GOTO ∧
        instr_uncond.target = some pc_lt ∧
        trivialLabelMap lt = some pc_lt := by
  intro l blk pc cond lt lf md h_blk h_pc h_xfer
  simp [trivialCfg] at h_blk
  obtain ⟨_, h_blk_eq⟩ := h_blk
  -- The trivial block's transfer is `.finish`, not `.condGoto` — contradiction.
  subst h_blk_eq
  simp [trivialBlock] at h_xfer

private theorem trivial_layout_finish :
    ∀ l blk pc md, (l, blk) ∈ trivialCfg.blocks →
      trivialLabelMap l = some pc →
      blk.transfer = .finish md →
      ∃ pc_end instr_end,
        pc_end = pc + 1 + DetBlockBodyInstrCount blk ∧
        trivialPgm.instrAt pc_end = some instr_end ∧
        instr_end.type = .END_FUNCTION := by
  intro l blk pc md h_blk h_pc h_xfer
  simp [trivialCfg] at h_blk
  obtain ⟨h_l, h_blk_eq⟩ := h_blk
  subst h_l
  subst h_blk_eq
  simp [trivialLabelMap] at h_pc
  subst h_pc
  refine ⟨1, _, ?_, rfl, rfl⟩
  simp [DetBlockBodyInstrCount, trivialBlock]

private theorem trivial_entry_in_map :
    ∃ pc, trivialLabelMap trivialCfg.entry = some pc :=
  ⟨0, by simp [trivialLabelMap, trivialCfg]⟩

/-! ## Dummy evaluators

Two arbitrary evaluators (we don't need their concrete shape — the
lemma's conclusion does not depend on expression evaluation when the
block is empty). -/

def dummyEval : Imperative.SemanticEval Core.Expression :=
  fun _ _ => none

def dummyEvalGoto : SemanticEvalGoto Core.Expression :=
  fun _ _ => none

def dummyEvalGotoBool : SemanticEvalGotoBool Core.Expression :=
  fun _ _ => none

/-- A hand-built `WellFormedTranslation` witness for the trivial pair. -/
def trivialWF :
    WellFormedTranslation trivialCfg trivialPgm
      dummyEval dummyEvalGoto dummyEvalGotoBool where
  labelMap := trivialLabelMap
  labelMap_total := trivial_labelMap_total
  labelMap_inj := trivial_labelMap_inj
  layout_location := trivial_layout_location
  layout_cond_goto := trivial_layout_cond_goto
  layout_cond_goto_guards := by
    intro l blk pc cond lt lf md instr_neg instr_uncond h_blk h_pc h_xfer
      h_neg_at h_uncond_at
    -- The trivial block uses `.finish`, not `.condGoto` — contradiction.
    simp [trivialCfg] at h_blk
    obtain ⟨_, h_blk_eq⟩ := h_blk
    subst h_blk_eq
    simp [trivialBlock] at h_xfer
  layout_finish := trivial_layout_finish
  layout_block_body := by
    intro l blk pc h_blk h_pc k inner h_k h_cmd
    -- The trivial block has no commands; `k < 0` is impossible.
    simp [trivialCfg] at h_blk
    obtain ⟨_, h_blk_eq⟩ := h_blk
    subst h_blk_eq
    simp [trivialBlock] at h_k
  entry_in_map := trivial_entry_in_map

/-! ## Test: `block_simulation_empty_finish` instantiates correctly

Use the proven lemma to obtain a concrete `StepGotoStar` for the trivial
program. This confirms the lemma actually fires on a real input and that
the `Sim` relation composes correctly with `WellFormedTranslation`. -/

/-- The lemma instantiates: from `(running 0 σ failed)`, two GOTO steps
reach `(terminal σ failed)` for any store `σ` and failure flag. -/
example (σ : Imperative.SemanticStore Core.Expression) (failed : Bool) :
    StepGotoStar Core.Expression dummyEvalGoto dummyEvalGotoBool trivialPgm
      (.running 0 σ failed) (.terminal σ failed) :=
  block_simulation_empty_finish
    (δ := dummyEval)
    (δ_goto := dummyEvalGoto)
    (δ_goto_bool := dummyEvalGotoBool)
    (cfg := trivialCfg) (pgm := trivialPgm) (wf := trivialWF)
    (l := "entry") (md := Imperative.MetaData.empty)
    (blk := trivialBlock)
    (h_blk_cmds := rfl)
    (h_blk_xfer := rfl)
    (h_block := by simp [trivialCfg])
    (σ := σ) (failed := failed)
    (pc := 0) (h_pc := rfl)

end CProverGOTOTests
