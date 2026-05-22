/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOInvariants
public import Strata.Languages.Core.Procedure

public section

/-! # Discharging `h_goto_target_in_range` from `WellFormedTranslation`

Round-7a deliverable: bridge from `WellFormedTranslation cfg pgm δ
δ_goto δ_goto_bool` (`CoreCFGToGOTOInvariants.lean`) plus a small
auxiliary hypothesis to the
`h_goto_target_in_range` predicate consumed by R6a's
`wellFormedTranslation_to_translatorBridgeHyps`
(`TranslatorBridgeHypsDischarge.lean`).

## What we prove

```
∀ {pc target : Nat} {instr : Instruction},
  pgm.instrAt pc = some instr → instr.type = .GOTO →
  instr.target = some target →
  ∃ instr_target, pgm.instrAt target = some instr_target
```

— i.e., the target of every emitted GOTO is in the program's
instruction array.

## Tier outcome

**Tier 2 (Good).** Closed under one stable auxiliary hypothesis,
`EveryGotoTargetIsLabelMapEntry`: every GOTO target is a `labelMap`
entry for a label in `cfg.blocks`.

The auxiliary is mechanically discharable from
`coreCFGToGotoTransform`'s structure (every GOTO instruction is
emitted by either `emitCondGoto` or `emitUncondGoto`, both of which
resolve targets via `labelMap`), but proving that requires
structural induction over the translator's outer loop — separable
from the structural-soundness story `WellFormedTranslation` tells
and deferred to a future round.

Given the auxiliary, the proof is mechanical:

1. The auxiliary gives us `(l, blk) ∈ cfg.blocks` and
   `labelMap l = some target`.
2. `WellFormedTranslation.layout_location` consumes those and
   returns an `instr_target` with `pgm.instrAt target = some
   instr_target`.

## Why we can't close it from `wf` alone

`WellFormedTranslation` is written from the *forward* direction
(CFG → program): for each `(l, blk) ∈ cfg.blocks`, what GOTOs are
emitted. It doesn't expose the *backward* direction (program →
CFG): for an arbitrary GOTO instruction, which CFG block emitted
it.

Closing the backward direction requires either:

1. Adding a `WellFormedTranslation.every_goto_originates_from_block`
   field, discharged in `CoreCFGToGotoTransformWF.lean` via
   structural induction over the outer loop.
2. Or a separate "reverse-mapping" lemma walking
   `coreCFGToGotoTransform`'s output.

Option 1 is the natural follow-up: it parallels how
`layout_cond_goto`/`layout_finish` are constructed today. Out of
scope for this round.
-/

namespace CProverGOTO.GotoTargetInRange

open Imperative
open CProverGOTO

/-! ## Auxiliary: every GOTO target is a labelMap entry -/

/-- Predicate: every GOTO instruction's target value is the
`labelMap` lookup for some label that appears as a block label in
`cfg.blocks`.

This is a *backward-mapping* property of `pgm` relative to `cfg` and
`labelMap`: for each emitted GOTO with `instr.target = some target`,
there exists an `(l, blk) ∈ cfg.blocks` with `labelMap l = some
target`.

Discharable from `coreCFGToGotoTransform`'s structure (every GOTO
is emitted by `emitCondGoto` or `emitUncondGoto`, both resolving
targets via the same `labelMap`); held here as a hypothesis. -/
@[expose] def EveryGotoTargetIsLabelMapEntry
    (cfg : Core.DetCFG) (pgm : Program) (labelMap : LabelMap) : Prop :=
  ∀ {pc target : Nat} {instr : Instruction},
    pgm.instrAt pc = some instr → instr.type = .GOTO →
    instr.target = some target →
    ∃ l blk, (l, blk) ∈ cfg.blocks ∧ labelMap l = some target

/-! ## The discharge -/

/-- **Discharge `h_goto_target_in_range` under one auxiliary.**

Given a `WellFormedTranslation` plus the
`EveryGotoTargetIsLabelMapEntry` auxiliary, every GOTO instruction's
target is a valid index into `pgm.instrAt`.

Proof: The auxiliary gives a `(l, blk) ∈ cfg.blocks` with `labelMap
l = some target`; `wf.layout_location` hands back an instruction at
that pc. -/
theorem goto_target_in_range_of_wf
    (cfg : Core.DetCFG) (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (wf : WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool)
    (h_aux : EveryGotoTargetIsLabelMapEntry cfg pgm wf.labelMap) :
    ∀ {pc target : Nat} {instr : Instruction},
      pgm.instrAt pc = some instr → instr.type = .GOTO →
      instr.target = some target →
      ∃ instr_target, pgm.instrAt target = some instr_target := by
  intro pc target instr h_at h_ty h_target
  obtain ⟨l, blk, h_in, h_lookup⟩ := h_aux h_at h_ty h_target
  obtain ⟨instr_target, h_at_target, _h_loc_ty⟩ :=
    wf.layout_location l blk target h_in h_lookup
  exact ⟨instr_target, h_at_target⟩

end CProverGOTO.GotoTargetInRange
