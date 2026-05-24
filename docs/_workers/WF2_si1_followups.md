# WF2 — SI1 follow-up small actionable items

Worker WF2 applying the 5 small still-actionable items from
`docs/_workers/SI1_shrink_audit_followup.md` §2.

Branch base: `htd/unstructured-to-goto` HEAD `87670ec22`.

## Plan

Five items, each evaluated independently. Final disposition below.

## Per-item disposition

### Item 1 — §1.2: Inline bridge_v1 into bridge_v2 — **APPLIED**

- **File:** `Strata/Backends/CBMC/GOTO/TranslatorBridgeHypsDischarge.lean`
- **Change:** Inlined v1 (`wellFormedTranslation_to_translatorBridgeHyps`)
  into v2 (`wellFormedTranslation_to_translatorBridgeHyps_v2`). v2 was
  the only caller. The structure-literal body that v1 carried for the
  three discharged fields (`nameMap_inj`, `dead_lookup`, `goto_target_resolves`)
  plus the value passthroughs is now directly inside v2. The three lookup
  fields go through `InstructionLookups` helpers as before.
- **Public API:** `wellFormedTranslation_to_translatorBridgeHyps_v2` signature
  unchanged (`CoreCFGToGOTOConcrete.lean` consumer at `_v6` continues to
  work).
- **Doc references** in `SteppingBridgesDischarge.lean` and
  `GotoTargetInRange.lean` updated to point at v2 directly.
- **LoC:** file goes from 335 → 209 lines. Stat: 50 ins / 175 del = **-125 LoC**.
- **Commit:** `f57354fe4`.

### Item 2 — §2.2: Promote private patcher lemmas — **SKIPPED (WF1 territory)**

- **Files:** `GotoTargetProvenance.lean` (private `patch_one_other_index`,
  `patch_foldl_target_preserved_when_idx_unique_in_tail`) and the WF tree
  copies in `CoreCFGToGotoTransformWF/CondGotoClosures.lean`.
- **Reason for skip:** WF1 owns the WF tree. The non-WF copies (in
  GotoTargetProvenance.lean) have no callers outside that file. To
  deduplicate, a public re-exported version would have to live somewhere
  — and the natural home is a shared module imported by both WF and
  non-WF, which would touch the WF tree.
- **Disposition:** defer to WF1 if/when WF1 chooses to expose the patcher
  lemmas as a public utility. No action from WF2.

### Item 3 — §6.4: omega in 3 surviving Nat.le_of_not_lt sites — **APPLIED**

- **Files:** `Strata/Backends/CBMC/GOTO/NoDead.lean` (lines ~81, ~103) and
  `Strata/Backends/CBMC/GOTO/GotoTargetProvenance.lean` (line ~151).
- **NoDead sites:** the explicit `have h_ge : a.size ≤ pc := Nat.le_of_not_lt h_lt`
  bindings were never used directly — `omega` later in the proof picks
  up `h_lt` itself and derives the same fact. Removing the binding
  shortens both proofs.
- **GotoTargetProvenance site:** `Nat.le_of_not_lt h_idx` was an inline
  argument to `Array.setIfInBounds_eq_of_size_le`; replaced with `by omega`.
- **LoC:** Stat: 4 ins / 7 del = **-3 LoC**.
- **Commit:** `dde930ca4`.

### Item 4 — §6.2: case_contra_on_type macro — **SKIPPED (net-negative)**

- **Surveyed sites:** the only consumer of the pattern outside the WF
  tree is `CmdProvenance.lean`, which has 5 occurrences of:
  ```
  inj_subst h_at h_X_at
  rw [h_X_ty] at h_ty
  cases h_ty
  ```
  Each is a 3-line block.
- **Cost-benefit:** A macro absorbing the pattern would save ~10 lines
  across the 5 sites but add ~6-8 lines of macro definition + docstring
  in `Tactics.lean`. Net is approximately zero, possibly net-negative.
- **Per SI1's guidance:** "inj_subst already absorbed the pain, the macro
  may be net-negative LoC." Confirmed by site count + collapse arithmetic.
- **Disposition:** declined. WF1 may revisit if the WF tree's Shape.lean /
  StepPreservation.lean exhibit the pattern at higher density.

### Item 5 — §1.3: drop wf-form everyGotoTargetIsLabelMapEntry_of_translator — **SKIPPED (per SI1)**

- **File:** `Strata/Backends/CBMC/GOTO/GotoTargetProvenance.lean` (~line 526),
  ~40 LoC theorem.
- **Per SI1:** "Probably leave. Axiom test gives a smoke check on a
  slightly different shape; the cost is 40 LoC of theorem + 4 LoC of test."
- **Disposition:** skipped per SI1's recommendation.

## Build/axioms verification

After all WF2 commits + cherry-pick of WF1 commit `b0ccbbf22` on top:

```
$ lake build StrataTest.Backends.CBMC.GOTO.CoreCFGToGOTOConcreteAxioms
...
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v6'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v7'
  depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (234 jobs).
```

Full `lake build` green (585 jobs).

## Final tally

| Item | Disposition | LoC change |
|---|---|---|
| §1.2 Inline bridge_v1 | applied | **-125** |
| §2.2 Promote patcher lemmas | skipped (WF tree) | 0 |
| §6.4 omega replacements | applied | **-3** |
| §6.2 case_contra_on_type macro | skipped (net-negative) | 0 |
| §1.3 wf-form everyGotoTargetIsLabelMapEntry | skipped (per SI1) | 0 |

**Total: -128 LoC** across 5 files (TranslatorBridgeHypsDischarge -126,
SteppingBridgesDischarge ~0, GotoTargetInRange ~0, NoDead -5,
GotoTargetProvenance -1; the inline bridges absorbed the bulk).

**Tier 2** (50-150 LoC saved). Bridge inlining was the headline win;
omega cleanup was trivial; remaining 3 items declined for documented
reasons.

## Notes on the parallel WF1 worker

WF1 cherry-picked their own commit `b0ccbbf22 cleanup(WF1): drop redundant
location_at_pc — keep _with_labels (-100 LoC)` onto the same branch
during this session. That commit touches WF tree files
(`FoldAndDecompose.lean`, `StepPreservation.lean`) and is unrelated to
WF2 work. No conflict.
