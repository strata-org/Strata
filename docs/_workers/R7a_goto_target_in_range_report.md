# Worker R7a — Discharge `h_goto_target_in_range`

**Goal.** Discharge R6a's `h_goto_target_in_range` from a
`WellFormedTranslation` value, possibly under a small auxiliary
hypothesis. New file:
`Strata/Backends/CBMC/GOTO/GotoTargetInRange.lean`.

## Outcome

**Tier 2 (Good).** Theorem closed under one stable auxiliary
hypothesis (`EveryGotoTargetIsLabelMapEntry`) that's mechanically
discharable from the translator's structure.

* Build green:
  `lake build Strata.Backends.CBMC.GOTO.GotoTargetInRange` and
  full `lake build` both pass (585/585 jobs).
* Axiom set: `[propext, Quot.sound]` — even tighter than the
  project's standard `[propext, Classical.choice, Quot.sound]`,
  because the proof is purely structural unfolding via
  `wf.layout_location`.
* Net code: 105 LoC (proof) + 14 LoC (axiom test) + 75 LoC (this
  report) = 194 LoC total.

## What we proved

In `Strata/Backends/CBMC/GOTO/GotoTargetInRange.lean`:

```lean
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
      ∃ instr_target, pgm.instrAt target = some instr_target
```

with the auxiliary defined as:

```lean
def EveryGotoTargetIsLabelMapEntry
    (cfg : Core.DetCFG) (pgm : Program) (labelMap : LabelMap) : Prop :=
  ∀ {pc target : Nat} {instr : Instruction},
    pgm.instrAt pc = some instr → instr.type = .GOTO →
    instr.target = some target →
    ∃ l blk, (l, blk) ∈ cfg.blocks ∧ labelMap l = some target
```

## Proof strategy

The proof is two lines of `obtain`:

1. The auxiliary `h_aux` gives `(l, blk) ∈ cfg.blocks` and
   `wf.labelMap l = some target`.
2. `wf.layout_location l blk target h_in h_lookup` returns an
   `instr_target` with `pgm.instrAt target = some instr_target`.

That's it. The structural work is entirely in `layout_location`'s
existence; this file's only job is gluing it to the bridge
predicate's exact shape.

## Why we can't close it from `wf` alone (Tier 1 obstacle)

`WellFormedTranslation` is written in the *forward* direction
(CFG → program): for each `(l, blk) ∈ cfg.blocks`, what GOTOs are
emitted (`layout_cond_goto`, `layout_finish`, `layout_block_body`).

It doesn't expose the *backward* direction (program → CFG): for an
arbitrary GOTO instruction in `pgm`, which CFG block emitted it.
That's the gap the auxiliary fills.

## Why the auxiliary is the right shape

Consider the alternatives:

| Auxiliary | Tradeoff |
|---|---|
| "Every GOTO came from a condGoto block" (full block witness) | Carries `cond/lt/lf/md` baggage that `goto_target_in_range`'s conclusion doesn't need — bloats the bridge interface unnecessarily. |
| **"Every GOTO target is a labelMap entry"** (current) | Minimal: just maps `target` to the labelMap. Plays directly with `layout_location`. |
| "Every GOTO target is `< pgm.instructions.size`" | Equivalent to the conclusion modulo `instrAt`'s definition — circular for our purposes. |

The current auxiliary is the smallest premise that exposes
*structurally* what we need (a labelMap key) without circularity.

## Next-round path to Tier 1

To eliminate the auxiliary entirely, the natural approach is to
extend `WellFormedTranslation` (in
`CoreCFGToGOTOInvariants.lean`) with a backward-mapping field:

```lean
goto_originates_from_block :
  ∀ {pc target : Nat} {instr : Instruction},
    pgm.instrAt pc = some instr → instr.type = .GOTO →
    instr.target = some target →
    ∃ l blk, (l, blk) ∈ cfg.blocks ∧ labelMap l = some target
```

Then close that field in `CoreCFGToGotoTransformWF.lean` by
induction on the outer loop (every `coreCFGToGotoBlockStep`
preserves "all GOTOs in `trans.instructions` came from
`emitCondGoto`/`emitUncondGoto`", and both helpers resolve targets
via `labelMap` lookups). Estimated ~150-200 LoC.

That extension is parallel to the existing `layout_cond_goto`
field's discharge (which is ~600 LoC across three theorems
covering `emitLabel`, `emitCondGoto`, `emitUncondGoto`,
`patchGotoTargets`, and the cmds-fold), so it's mechanical but not
trivial. Out of scope here.

## Files added

* `Strata/Backends/CBMC/GOTO/GotoTargetInRange.lean` (105 LoC,
  build green).
* `StrataTest/Backends/CBMC/GOTO/GotoTargetInRangeAxioms.lean`
  (14 LoC) — axiom-set smoke test.
* `docs/_workers/R7a_goto_target_in_range_report.md` (this file).

## Commit log (in order)

1. `docs(R7a): report stub for h_goto_target_in_range discharge` —
   `52f1957ba`.
2. `feat(goto-correct): R7a - discharge h_goto_target_in_range
   under EveryGotoTargetIsLabelMapEntry` — `3de19127d`.
3. (this commit) — final report.

## Build verification

```
$ lake build Strata.Backends.CBMC.GOTO.GotoTargetInRange
✔ [88/88] Built Strata.Backends.CBMC.GOTO.GotoTargetInRange (1.9s)
Build completed successfully (88 jobs).

$ lake build
Build completed successfully (585 jobs).

$ lake env lean StrataTest/Backends/CBMC/GOTO/GotoTargetInRangeAxioms.lean
'CProverGOTO.GotoTargetInRange.goto_target_in_range_of_wf' depends
on axioms: [propext, Quot.sound]
```

## Status checklist

- [x] Stub created.
- [x] Decide auxiliary-hypothesis shape (Tier 2 deliverable).
- [x] Write proof.
- [x] `lake build` green.
- [x] `#print axioms` standard (in fact tighter:
  `[propext, Quot.sound]`).
- [x] Final report.
