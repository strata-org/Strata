/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.SteppingBridgesDischarge
public import Strata.Backends.CBMC.GOTO.WellFormedTranslationProps
public import Strata.Backends.CBMC.GOTO.InstructionLookups
public import Strata.Languages.Core.Procedure

public section

/-! # Bridging `WellFormedTranslation` to `TranslatorBridgeHyps`

From a `WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool` witness
(`CoreCFGToGOTOInvariants.lean`) plus a small bundle of caller-supplied
bridge hypotheses, build the `TranslatorBridgeHyps pgm nameMap δ_goto
eval` value consumed by `steppingBridges_of_translator`
(`SteppingBridgesDischarge.lean`).

## What this bridge actually closes

The `TranslatorBridgeHyps` structure has eight fields. Most of them
are universally quantified over PCs *and* over arbitrary `x : P.Ident`
values (for DECL/ASSIGN/DEAD), demanding a per-PC fact tying the
GOTO instruction's symbol/lhs operand to `nameMap x`.

Of the eight fields:

* `goto_target_resolves` is discharged from
  `WellFormedTranslation.locationNum_eq_index` via
  `WellFormedTranslationProps.findLocIdx_resolves`, modulo a side
  condition that the GOTO target's PC is in range
  (`h_goto_target_in_range`).
* `dead_lookup` is vacuous from `h_no_dead` — the translator never
  emits DEAD instructions, so no `step_dead` ever fires.
* `nameMap_inj` is preserved as a passthrough from the caller's
  `h_inj` hypothesis.

The remaining five fields:

* The lookup fields (`decl_lookup`, `assign_lookup`,
  `assign_nondet_lookup`) require the GOTO instruction's `code`
  field to expose a specific symbol name `nameMap x`. They are
  decomposed via the `InstructionLookups` lemmas into per-PC
  structural witnesses (`provenance`) plus per-firing trace
  witnesses (`pinned`).
* The value fields (`decl_empty_value`, `assign_value_corr`,
  `assign_nondet_value_corr`) are caller-side obligations on the
  source-side `δ` ↔ target-side `eval` correspondence. -/

namespace CProverGOTO.TranslatorBridgeHypsDischarge

open Imperative
open CProverGOTO
open CProverGOTO.SemanticsTautschnig (ValueCorr StoreCorr ExprEval Store)
open CProverGOTO.SteppingBridgesDischarge (TranslatorBridgeHyps)

/-! ## The bridge -/

/-- Bridge from `WellFormedTranslation` to `TranslatorBridgeHyps`.

Of the eight `TranslatorBridgeHyps` fields, three are discharged
from `wf` (plus minor side hypotheses), three are decomposed via
the `InstructionLookups` lemmas into per-PC `provenance` + per-firing
`pinned` hypotheses, and the remaining three (the value fields) are
caller passthroughs.

The two side hypotheses (`h_goto_target_in_range`, `h_no_dead`) are
metaproperties of `coreCFGToGotoTransform`'s output that are
discharged by `GotoTargetInRange.lean` and `NoDead.lean`
respectively. -/
theorem wellFormedTranslation_to_translatorBridgeHyps_v2
    (cfg : Core.DetCFG) (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (wf : WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool)
    (nameMap : Core.Expression.Ident → String)
    (h_inj : Function.Injective nameMap)
    (eval : SemanticsTautschnig.ExprEval)
    (h_goto_target_in_range :
      ∀ {pc target : Nat} {instr : Instruction},
        pgm.instrAt pc = some instr → instr.type = .GOTO →
        instr.target = some target →
        ∃ instr_target, pgm.instrAt target = some instr_target)
    (h_no_dead :
      ∀ {pc : Nat} {instr : Instruction},
        pgm.instrAt pc = some instr → instr.type ≠ .DEAD)
    -- Provenance hypotheses (discharged from `wf` + `CmdEmittedAt`
    -- by `CmdProvenance.lean` plus a CFG-PC inversion).
    (h_decl_provenance :
      ∀ {pc : Nat} {instr : Instruction},
        pgm.instrAt pc = some instr → instr.type = .DECL →
        ∃ v_src gty, instr.code = Code.decl (Expr.symbol (nameMap v_src) gty))
    (h_assn_provenance :
      ∀ {pc : Nat} {instr : Instruction},
        pgm.instrAt pc = some instr → instr.type = .ASSIGN →
        ∃ v_src gty rhs_emitted,
          instr.code = Code.assign
            (Expr.symbol (nameMap v_src) gty) rhs_emitted)
    -- The strict nondet-rhs variant is not required: the rhs-shape
    -- witness arrives via the `step_assign_nondet` constructor itself.
    -- Trace-level pinning (caller-side; irreducible at this layer).
    (h_decl_x_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v : Core.Expression.Expr},
        pgm.instrAt pc = some instr → instr.type = .DECL →
        Imperative.InitState Core.Expression σ x v σ' →
        ∀ v_src gty, instr.code = Code.decl (Expr.symbol (nameMap v_src) gty) →
        x = v_src)
    (h_assn_x_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v_imp : Core.Expression.Expr},
        pgm.instrAt pc = some instr → instr.type = .ASSIGN →
        Imperative.UpdateState Core.Expression σ x v_imp σ' →
        ∀ v_src gty rhs_emitted,
          instr.code = Code.assign
            (Expr.symbol (nameMap v_src) gty) rhs_emitted →
          x = v_src)
    (h_assn_rhs_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {σ : Imperative.SemanticStore Core.Expression}
        {rhs_g : Expr} {v_imp : Core.Expression.Expr},
        pgm.instrAt pc = some instr → instr.type = .ASSIGN →
        δ_goto σ rhs_g = some v_imp →
        ∀ v_src gty rhs_emitted,
          instr.code = Code.assign
            (Expr.symbol (nameMap v_src) gty) rhs_emitted →
          rhs_g = rhs_emitted)
    -- Value-side passthroughs (caller-side; out of scope for this bridge).
    (h_decl_empty_value :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {v : Core.Expression.Expr}
        {σ σ' : Imperative.SemanticStore Core.Expression},
        pgm.instrAt pc = some instr → instr.type = .DECL →
        Imperative.InitState Core.Expression σ x v σ' →
        (SemanticsTautschnig.ValueCorr.toValue v
          : Option SemanticsTautschnig.Value)
          = some .vEmpty)
    (h_assign_value_corr :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {σ_imp σ_imp' : Imperative.SemanticStore Core.Expression}
        {σ_goto : SemanticsTautschnig.Store}
        {rhs_g : Expr} {v_imp : Core.Expression.Expr},
        pgm.instrAt pc = some instr → instr.type = .ASSIGN →
        δ_goto σ_imp rhs_g = some v_imp →
        Imperative.UpdateState Core.Expression σ_imp x v_imp σ_imp' →
        SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto →
        ∃ v_goto,
          (SemanticsTautschnig.ValueCorr.toValue v_imp
            : Option SemanticsTautschnig.Value) = some v_goto ∧
          eval σ_goto rhs_g = some v_goto)
    (h_assign_nondet_value_corr :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v_imp : Core.Expression.Expr},
        pgm.instrAt pc = some instr → instr.type = .ASSIGN →
        Imperative.UpdateState Core.Expression σ x v_imp σ' →
        ∃ v_goto,
          (SemanticsTautschnig.ValueCorr.toValue v_imp
            : Option SemanticsTautschnig.Value)
            = some v_goto) :
    TranslatorBridgeHyps pgm nameMap δ_goto eval where
  nameMap_inj := h_inj
  decl_lookup :=
    -- decl_lookup: decomposed via InstructionLookups.
    CProverGOTO.InstructionLookups.decl_lookup_of_provenance_and_pinned
      pgm nameMap h_decl_provenance h_decl_x_pinned
  dead_lookup := by
    -- Vacuous from `h_no_dead`: no DEAD instructions ever fire.
    intro pc instr x σ σ' h_at h_ty _h_remove
    exact absurd h_ty (h_no_dead h_at)
  assign_lookup :=
    -- assign_lookup: decomposed via InstructionLookups.
    CProverGOTO.InstructionLookups.assign_lookup_of_provenance_and_pinned
      pgm δ_goto nameMap h_assn_provenance h_assn_x_pinned h_assn_rhs_pinned
  assign_nondet_lookup :=
    -- assign_nondet_lookup: decomposed via InstructionLookups; the
    -- rhs-shape witness comes from the `step_assign_nondet` constructor
    -- itself, not from a separate hypothesis.
    CProverGOTO.InstructionLookups.assign_nondet_lookup_of_provenance_and_pinned
      pgm nameMap h_assn_provenance h_assn_x_pinned
  goto_target_resolves := by
    -- Discharge: instr.type = .GOTO + instr.target = some target
    -- gives instrTarget pgm pc = some (some target). Then
    -- locationNum_eq_index + findLocIdx_resolves give findLocIdx pgm.instructions
    -- target = some target.
    intro pc target instr h_at h_ty h_target
    refine ⟨target, ?_, ?_⟩
    · -- instrTarget pgm pc = some (some target)
      simp only [SemanticsTautschnig.instrTarget, Program.instrAt] at *
      rw [h_at]
      simp [h_target]
    · -- findLocIdx pgm.instructions target = some target
      obtain ⟨instr_target, h_at_target⟩ :=
        h_goto_target_in_range h_at h_ty h_target
      exact findLocIdx_resolves target instr_target wf.locationNum_eq_index h_at_target
  decl_empty_value := h_decl_empty_value
  assign_value_corr := h_assign_value_corr
  assign_nondet_value_corr := h_assign_nondet_value_corr

end CProverGOTO.TranslatorBridgeHypsDischarge
