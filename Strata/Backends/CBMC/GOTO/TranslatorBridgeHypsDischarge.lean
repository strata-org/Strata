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

Round-6a deliverable: from a `WellFormedTranslation cfg pgm δ δ_goto
δ_goto_bool` witness (`CoreCFGToGOTOInvariants.lean`) plus a small
bundle of caller-supplied bridge hypotheses, build the
`TranslatorBridgeHyps pgm nameMap δ_goto eval` value consumed by
Worker C's `steppingBridges_of_translator`
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
  (`h_goto_target_in_range`). The translator only ever emits GOTOs
  with in-range targets (`layout_cond_goto` + `layout_location`);
  closing this side condition from `wf` alone is mechanical and
  deferred.
* `dead_lookup` is vacuous from `h_no_dead` — the translator never
  emits DEAD instructions, so no `step_dead` ever fires.
* `nameMap_inj` is preserved as a passthrough from the caller's
  `h_inj` hypothesis.

The remaining five fields are passthroughs:

* The lookup fields (`decl_lookup`, `assign_lookup`,
  `assign_nondet_lookup`) require the GOTO instruction's `code`
  field to expose a specific symbol name `nameMap x`. Today's
  `CmdEmittedAt` constructors carry `i.code = Code.assign lhs e_goto`
  with `lhs` *existential*, so even with full `WellFormedTranslation`
  + an inversion lemma we cannot extract `lhs = Expr.symbol (nameMap
  x) gty`. Strengthening `CmdEmittedAt` is an A-side change deferred
  to a future round.
* The value fields (`decl_empty_value`, `assign_value_corr`,
  `assign_nondet_value_corr`) are caller-side obligations on the
  source-side `δ` ↔ target-side `eval` correspondence.

Net hypothesis-surface reduction: callers no longer need to
separately prove `findLocIdx`-resolution or "no DEAD instructions";
those two facts are now closed from `wf` plus a small side bundle
(`h_goto_target_in_range`, `h_no_dead`) that's mechanically
discharable from the translator's structure.

## Boundary with later rounds

Round 7 candidates that close the lookup fields:

1. Strengthen `CmdEmittedAt` to also expose
   `Code.decl (Expr.symbol (nameMap v) gty)` /
   `Code.assign (Expr.symbol (nameMap v) gty) e_goto` (instead of
   existential `lhs`). Then write a CFG-PC inversion lemma
   walking `cfg.blocks` to find the unique block/offset for each
   admitted PC.

2. Reshape the `TranslatorBridgeHyps` lookup fields to be
   conditional on a "`x` is the source-CFG variable for this PC"
   premise; that premise gets discharged at the StepGoto-step level,
   not here.

Either path lets a future bridge close more of the eight fields. -/

namespace CProverGOTO.TranslatorBridgeHypsDischarge

open Imperative
open CProverGOTO
open CProverGOTO.SemanticsTautschnig (ValueCorr StoreCorr ExprEval Store)
open CProverGOTO.SteppingBridgesDischarge (TranslatorBridgeHyps)

/-! ## The bridge -/

/-- Bridge from `WellFormedTranslation` (round-5) to
`TranslatorBridgeHyps` (Worker C, `SteppingBridgesDischarge.lean`).

Of the eight `TranslatorBridgeHyps` fields, three are discharged
from `wf` (plus minor side hypotheses) and five remain caller
passthroughs:

* `goto_target_resolves` (closed from `wf.locationNum_eq_index` +
  `findLocIdx_resolves`, modulo `h_goto_target_in_range`),
* `dead_lookup` (vacuous from `h_no_dead`),
* `nameMap_inj` (caller passthrough),
* the five lookup/value passthroughs (out of reach without
  strengthening `CmdEmittedAt` or providing source-side ↔
  target-side evaluator agreement).

The two side hypotheses (`h_goto_target_in_range`, `h_no_dead`) are
metaproperties of `coreCFGToGotoTransform`'s output that are
mechanically discharable by induction on the translator. They're
intentionally surfaced as hypotheses here so that closing them is
disjoint from the `WellFormedTranslation` story. -/
theorem wellFormedTranslation_to_translatorBridgeHyps
    (cfg : Core.DetCFG) (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (wf : WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool)
    (nameMap : Core.Expression.Ident → String)
    (h_inj : Function.Injective nameMap)
    (eval : SemanticsTautschnig.ExprEval)
    -- For every GOTO instruction with a target, the target PC is in range.
    -- Holds for every GOTO emitted by `coreCFGToGotoTransform` (per
    -- `WellFormedTranslation.layout_cond_goto`'s `labelMap lf = some pc_lf`
    -- + `layout_location`); a future round can close it from `wf`.
    (h_goto_target_in_range :
      ∀ {pc target : Nat} {instr : Instruction},
        pgm.instrAt pc = some instr → instr.type = .GOTO →
        instr.target = some target →
        ∃ instr_target, pgm.instrAt target = some instr_target)
    -- The translator never emits DEAD instructions. A separate
    -- "no-DEAD" property of `coreCFGToGotoTransform`'s output, stable
    -- under all rounds; provable by induction on the translator
    -- (every emit-helper pushes DECL/ASSIGN/ASSERT/ASSUME/GOTO/LOCATION,
    -- never DEAD). With it `dead_lookup` is vacuous.
    (h_no_dead :
      ∀ {pc : Nat} {instr : Instruction},
        pgm.instrAt pc = some instr → instr.type ≠ .DEAD)
    -- Lookup fields: the source-side `x` matches the GOTO's
    -- symbol/lhs operand. Cannot be discharged from current `wf`
    -- because `CmdEmittedAt` carries existential `lhs` rather than
    -- `Expr.symbol (nameMap x) gty`. Round-7 candidate.
    (h_decl_lookup :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v : Core.Expression.Expr},
        pgm.instrAt pc = some instr → instr.type = .DECL →
        Imperative.InitState Core.Expression σ x v σ' →
        (SemanticsTautschnig.instrCode pgm pc).bind
          SemanticsTautschnig.getSymbolName = some (nameMap x))
    (h_assign_lookup :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {rhs_g : Expr} {v_imp : Core.Expression.Expr},
        pgm.instrAt pc = some instr → instr.type = .ASSIGN →
        δ_goto σ rhs_g = some v_imp →
        Imperative.UpdateState Core.Expression σ x v_imp σ' →
        (SemanticsTautschnig.instrCode pgm pc).bind
            SemanticsTautschnig.getAssignLhs = some (nameMap x) ∧
        (SemanticsTautschnig.instrCode pgm pc).bind
            SemanticsTautschnig.getAssignRhs = some rhs_g)
    (h_assign_nondet_lookup :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v_imp : Core.Expression.Expr},
        pgm.instrAt pc = some instr → instr.type = .ASSIGN →
        Imperative.UpdateState Core.Expression σ x v_imp σ' →
        ∃ rhs_g,
          (SemanticsTautschnig.instrCode pgm pc).bind
              SemanticsTautschnig.getAssignLhs = some (nameMap x) ∧
          (SemanticsTautschnig.instrCode pgm pc).bind
              SemanticsTautschnig.getAssignRhs = some rhs_g ∧
          rhs_g.id = .side_effect .Nondet)
    -- Value fields: caller-side source ↔ target evaluator agreement.
    -- Out of scope for this bridge.
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
  decl_lookup := h_decl_lookup
  dead_lookup := by
    -- Vacuous from `h_no_dead`: no DEAD instructions ever fire.
    intro pc instr x σ σ' h_at h_ty _h_remove
    exact absurd h_ty (h_no_dead h_at)
  assign_lookup := h_assign_lookup
  assign_nondet_lookup := h_assign_nondet_lookup
  goto_target_resolves := by
    -- Discharge: instr.type = .GOTO + instr.target = some target
    -- gives instrTarget pgm pc = some (some target). Then
    -- locationNum_eq_index + findLocIdx_resolves give findLocIdx pgm.instructions target
    -- = some target.
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

/-! ## v2: lookup-field decomposition via `InstructionLookups`

Round-7c introduces an alternative bridge that consumes the
`InstructionLookups` lemmas to refactor the three lookup-field
caller passthroughs into:

* per-PC structural witnesses (`provenance`, mechanically discharable
  from `wf` + strengthened `CmdEmittedAt` + a future CFG-PC inversion),
* per-firing trace-level witnesses (`pinned`, irreducibly caller-side
  bisimulation invariants).

The total hypothesis count goes up (5 instead of 3), but each new
hypothesis is *strictly smaller* than the original lookup field it
replaces: each new hypothesis quantifies over a single PC (no `x`
universal in the conclusion) plus a single firing's data, and produces
either a pure structural fact about the GOTO code or an equality
linking the firing's `x` to the source-cmd's `v_src`.

Future rounds can close `*_provenance` from `wf` via a CFG-PC
inversion lemma (~100-200 LoC). The `*_pinned` hypotheses are
trace-level and are typically discharged at the simulation
consumer's level (e.g., the `coreCFGToGotoTransform_forward_simulation`
chain in `CoreCFGToGOTOConcrete.lean`). -/

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
    -- Provenance hypotheses (mechanically from wf + strengthened CmdEmittedAt
    -- via a CFG-PC inversion; deferred to a follow-up round).
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
    (h_assn_nondet_provenance :
      ∀ {pc : Nat} {instr : Instruction},
        pgm.instrAt pc = some instr → instr.type = .ASSIGN →
        ∃ v_src gty rhs_emitted,
          instr.code = Code.assign
            (Expr.symbol (nameMap v_src) gty) rhs_emitted ∧
          rhs_emitted.id = .side_effect .Nondet)
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
    TranslatorBridgeHyps pgm nameMap δ_goto eval :=
  wellFormedTranslation_to_translatorBridgeHyps cfg pgm δ δ_goto δ_goto_bool wf
    nameMap h_inj eval h_goto_target_in_range h_no_dead
    -- decl_lookup: discharged via InstructionLookups.
    (CProverGOTO.InstructionLookups.decl_lookup_of_provenance_and_pinned
      pgm nameMap h_inj h_decl_provenance h_decl_x_pinned)
    -- assign_lookup: discharged via InstructionLookups.
    (CProverGOTO.InstructionLookups.assign_lookup_of_provenance_and_pinned
      pgm δ_goto nameMap h_inj h_assn_provenance h_assn_x_pinned h_assn_rhs_pinned)
    -- assign_nondet_lookup: discharged via InstructionLookups.
    (CProverGOTO.InstructionLookups.assign_nondet_lookup_of_provenance_and_pinned
      pgm nameMap h_inj h_assn_nondet_provenance h_assn_x_pinned)
    h_decl_empty_value h_assign_value_corr h_assign_nondet_value_corr

end CProverGOTO.TranslatorBridgeHypsDischarge
