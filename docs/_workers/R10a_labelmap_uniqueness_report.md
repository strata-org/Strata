# R10a — labelMap-agreement closure (final report)

**Tier outcome:** **Tier 1 (full closure).** The universal-form
labelMap-agreement hypothesis is now internalised in
`coreCFGToGotoTransform_forward_simulation_concrete_v6` with no
auxiliary obligations beyond the trivial-for-standard-caller
`h_init_no_location`.

**Status:** Closed. Build green at every commit. Axiom set verified
clean (`[propext, Classical.choice, Quot.sound]`).

## What was closed

The universally-quantified `h_labelMap_agree` hypothesis on
`coreCFGToGotoTransform_forward_simulation_concrete_v6`:

```lean
∀ (wf : WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool),
∀ l blk target, (l, blk) ∈ cfg.blocks →
  st_final.labelMap[l]? = some target →
  wf.labelMap l = some target
```

is no longer a hypothesis. It is discharged internally by
`WfLabelMapAgree.labelMap_agree_of_translator`.

## Why the supervisor's original LOCATION-uniqueness sketch wasn't
sufficient

The supervisor's hint suggested that "any WF satisfies labelMap_total
+ labelMap_inj + layout_location" plus locationNum-unique-indices
forces `wf.labelMap l = hashMapToLabelMap st_final.labelMap l`.

Concretely the difficulty: with only `wf.layout_location l blk pc1`
giving an instruction at `pc1` of *type* `.LOCATION` (no constraint on
its `labels` field), and *multiple* LOCATION pcs in the program (one
per block), the existing WF fields can't pin `wf.labelMap` to be the
identity permutation — for two structurally-identical blocks (same
body, same finish transfer, same metadata), a "permuted" labelMap
satisfies every existing field.

The fix: add a new field `layout_location_labels` to
`WellFormedTranslation` that pins the LOCATION at `wf.labelMap l` to
have its `labels` field equal to `[l]`.

## Architecture

Three commits (atomic, each green):

1. **`f84e2f3c7` — R10a step 1: add `layout_location_labels`
   field.** New WF field + matching shadow field; the strengthened
   theorem discharges it via two new helper lemmas:
   - `coreCFGToGotoBlockStep_location_at_pc_with_labels` — the
     per-block step's LOCATION carries `labels = [head_label]`.
   - `blocksFoldlM_layout_location_with_labels` — outer-fold lift.
   - `patchGotoTargets_preserves_labels` (new) — patcher preserves
     the `labels` field unchanged.
2. **`83a6301b0` — R10a step 2:
   `Strata/Backends/CBMC/GOTO/WfLabelMapAgree.lean` (698 LoC).**
   Threads a new `LocationsTrackLabelMap` invariant through every
   stage of the translator's outer loop (per-cmd-step, cmds-fold,
   emitLabel/emitCondGoto/emitUncondGoto/endFunction, blocksFoldlM,
   patcher), culminating in
   `labelMap_agree_of_translator`.
3. **`8eafe5e3c` — R10a step 3: drop `h_labelMap_agree` from `_v6`.**
   Adds one trivial hypothesis `h_init_no_location` (trans₀ has no
   LOCATION at any PC), discharges `h_labelMap_agree` internally via
   the R10a theorem.

## Proof outline of `labelMap_agree_of_translator`

```
∀ wf l blk target, (l, blk) ∈ cfg.blocks →
  st_final.labelMap[l]? = some target →
  wf.labelMap l = some target
```

1. By `wf.labelMap_total`, `wf.labelMap l = some pc1` for some `pc1`.
2. By `wf.layout_location_labels l blk pc1`, an instruction at
   `pc1` in `ans.instructions` has `type = .LOCATION` and
   `labels = [l]`.
3. By `LocationsTrackLabelMap` (threaded via `blocksFoldlM_preserves`
   + `patchGotoTargets_preserves`), every LOCATION-with-labels-[l]
   pc in `ans.instructions` has its pc tracked by
   `st_final.labelMap[l]?`. Hence `st_final.labelMap[l]? = some pc1`.
4. From the given `st_final.labelMap[l]? = some target`, conclude
   `pc1 = target`.

## The `LocationsTrackLabelMap` invariant

```lean
def LocationsTrackLabelMap
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (labelMap : Std.HashMap String Nat) : Prop :=
  ∀ {pc : Nat} {instr : Instruction} {l : String},
    trans.instructions[pc]? = some instr →
    instr.type = .LOCATION → instr.labels = [l] →
    labelMap[l]? = some pc
```

Threading this invariant requires an explicit base-case hypothesis
that `trans₀` carries no LOCATION (the trivial-for-standard-caller
`h_init_no_location`) plus `BlockLabelsDistinct` for the outer-fold's
inductive step (each new block's head label is *fresh* in the
labelMap, so `emitLabel`'s simultaneous push + insert keeps the
invariant).

## Files changed

* **Modified**: `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOInvariants.lean`
  (+15 LoC) — new `layout_location_labels` field on
  `WellFormedTranslation`.
* **Modified**: `Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean`
  (+288 LoC) — new shadow field, two new structural helpers, two new
  patcher lemmas, and the construction-site update in
  `coreCFGToGotoTransform_wellFormed_nonempty`.
* **Added**: `Strata/Backends/CBMC/GOTO/WfLabelMapAgree.lean`
  (698 LoC) — the R10a closure.
* **Modified**: `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean`
  (+27/-17 LoC) — drops `h_labelMap_agree` from `_v6`, adds
  `h_init_no_location`, internalises the discharge.
* **Added**: `StrataTest/Backends/CBMC/GOTO/WfLabelMapAgreeAxioms.lean`
  (16 LoC) — axiom-set smoke test.
* **Added**: `docs/_workers/R10a_labelmap_uniqueness_report.md`
  (this file).

**Total LoC**: ~1050 (proof + tests + docs).

## Build verification

```
$ lake build
Build completed successfully (585 jobs).
```

## Axiom verification

```
$ lake env lean StrataTest/Backends/CBMC/GOTO/WfLabelMapAgreeAxioms.lean
'CProverGOTO.WfLabelMapAgree.labelMap_agree_of_translator' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v6' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Both at the project's standard axiom set. No `sorry` in live code.

## Status checklist

- [x] Stub created.
- [x] Decide closure approach (Tier 1 with new WF field).
- [x] Add `layout_location_labels` field + supporting infrastructure
      in WF + strengthened theorem.
- [x] Write `WfLabelMapAgree.lean` with the universal closure.
- [x] Update `_v6` to drop `h_labelMap_agree`, add
      `h_init_no_location`.
- [x] `lake build` green.
- [x] `#print axioms` standard
      (`[propext, Classical.choice, Quot.sound]`).
- [x] Final report.

## Hand-off to supervisor

The branch `worktree-agent-af1f339ce3d479c3e` carries three atomic
commits ready to cherry-pick onto `htd/unstructured-to-goto`:

1. `f84e2f3c7 — feat(goto-correct): R10a step 1 - add
   layout_location_labels field to WellFormedTranslation`
2. `83a6301b0 — feat(goto-correct): R10a step 2 - WfLabelMapAgree
   proves universal labelMap-agreement`
3. `8eafe5e3c — feat(goto-correct): R10a step 3 - drop
   h_labelMap_agree from _v6`

Plus the report stub commit `96422c8d8` (which can be squashed into
the final report commit).

R10b's `coreCFGToGotoTransform_decompose` extraction work is
disjoint and unaffected. R10c's `InstructionLookups.lean` /
`TranslatorBridgeHypsDischarge.lean` bridge layer is also disjoint.
