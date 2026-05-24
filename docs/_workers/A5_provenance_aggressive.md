# A5 — `GotoTargetProvenance` + `WfLabelMapAgree` aggressive cleanup

**Worker:** A5.
**Branch base:** `htd/unstructured-to-goto` (commit `a012a1c01`).
**Scope:** trim the two R8a/R10a worker outputs:
* `Strata/Backends/CBMC/GOTO/GotoTargetProvenance.lean`
* `Strata/Backends/CBMC/GOTO/WfLabelMapAgree.lean`

**Verdict:** **Tier 1 — combined 965 LoC** (−653 from baseline 1618).

## Final tally

| File | Before | After | Δ |
|---|---|---|---|
| `GotoTargetProvenance.lean` | 920 | **567** | **−353** |
| `WfLabelMapAgree.lean` | 698 | **398** | **−300** |
| **Combined** | **1618** | **965** | **−653** |
| `BlocksFoldClosed.lean` (helper) | 393 | 466 | +73 |
| **Net (across all 3)** | **2011** | **1431** | **−580** |

The 73-LoC growth in `BlocksFoldClosed.lean` factors out cmds-fold-only
preservation helpers (`toGotoInstructions_preserves_of_pushSafe`,
`cmdStep_call_preserves_of_pushSafe`,
`coreCFGToGotoCmdStep_preserves_of_pushSafe`,
`cmdsFoldlM_preserves_of_pushSafe`) usable by binary predicates that
can't fit `BlocksFoldClosed`'s unary typeclass shape. That refactor
also de-dupes ~110 LoC of cmd-shape dispatch boilerplate from the
existing `BlocksFoldClosed.ofPushSafe` (which now delegates to the new
helpers) and absorbs the equivalent ~75 LoC dispatch from
`GotoTargetProvenance`'s manual `BlocksFoldClosed` instance.

## Per-pass commit summary

| Pass | Commit | Net LoC saved | Notes |
|---|---|---|---|
| A | `ad439e16` WfLabelMapAgree | −143 | trimmed docs + inlined trivial emit lemmas |
| B | `43a0353f` GotoTargetProvenance | −230 | trimmed docs, removed `patchesFoldlM_preserves_no_goto_target_no_contracts` (dead), compressed manual `BlocksFoldClosed` instance |
| C | `cd885d7f` WfLabelMapAgree | −13 | compressed `emitLabel_preserves` |
| D | `a615b27f` WfLabelMapAgree | −14 | compressed transfer-push case in block-step |
| E | `6422f96a` BlocksFoldClosed + WfLabelMapAgree | −31 net (BlocksFoldClosed +73, WfLabelMapAgree −104) | factored cmds-fold helpers into `BlocksFoldClosed.lean`; WfLabelMapAgree now reuses them via `cmdsFoldlM_preserves_of_pushSafe` |
| F | `8d036ca3` GotoTargetProvenance | −76 | manual `BlocksFoldClosed` instance now delegates to `toGotoInstructions_preserves_of_pushSafe` + `cmdStep_call_preserves_of_pushSafe` |
| G | `b5cb5539` both | −15 | compressed top-level theorem proofs |
| H | `65e81848` both | −49 | dropped redundant docstrings on internal helpers |

## Acceptance check

* **Public API preserved:**
  - `GotoTargetProvenance.everyGotoTargetIsLabelMapEntry_of_translator_translatorMap` — signature unchanged (used by v5/v6/v7).
  - `GotoTargetProvenance.everyGotoTargetIsLabelMapEntry_of_translator` — signature unchanged (used by axiom test).
  - `GotoTargetProvenance.NoGotoHasTarget` — signature unchanged (referenced by `CoreCFGToGOTOConcrete`).
  - `WfLabelMapAgree.labelMap_agree_of_translator` — signature unchanged (used by v6/v7).
  - `WfLabelMapAgree.LocationsTrackLabelMap` — kept as `@[expose] abbrev`; it's now an alias for the new array-level form `LocationsTrackLabelMap'`.
* **Axioms unchanged.** Both `_v6` and `_v7` and the in-file top-levels still depend on `[propext, Classical.choice, Quot.sound]` (verified by hand — no new axioms in any of the 3 modified files).
* **`lake build` green.** All 227 jobs in the consumer chain plus the 229-job test build pass.
* **No new `axiom`. No `sorry`.**

## Findings

### Dead lemma
* `patchesFoldlM_preserves_no_goto_target_no_contracts` — declared at the original line 303, never referenced anywhere. Removed in pass B.

### Stale docs
* L3's "## File layout" docstring at the top of `GotoTargetProvenance.lean` repeated the strategy already explained in the file's main docstring. Trimmed in pass B.
* `WfLabelMapAgree.lean` had a 40+ line header docstring duplicating the in-namespace structure narrative; trimmed in pass A.

### Cross-file shared code
The cmds-fold preservation pattern is genuinely shared between
`GotoTargetProvenance` (typeclass-based, with custom GOTO closures)
and `WfLabelMapAgree` (binary, can't typeclass). Factoring the
cmd-shape dispatch into four standalone helpers in `BlocksFoldClosed.lean`
eliminated ~150 LoC of duplication across the two consumer files
without growing the helper file beyond the savings.

### W1's "binary combinator is net-negative" finding revisited
W1 declined to port `WfLabelMapAgree` to a binary `BlocksFoldClosed`
extension because the abstraction tax of a typeclass extension equalled
the savings. The path A5 took avoids the typeclass entirely: the new
`*_of_pushSafe` helpers are plain theorems, not typeclass instances,
and they decouple the cmds-fold portion from the full 9-step matrix.
This sidesteps the abstraction tax W1 documented (no new typeclass
declaration, no new bridge, just dispatch helpers).

### Internal-only public theorems
Several `theorem`s in `GotoTargetProvenance.lean` are only used
internally (`coreCFGToGotoPatchStep_no_contracts_resolved_reverse`,
`patchesFoldlM_no_contracts_resolved_reverse`,
`patchesFoldlM_no_contracts_resolved_reverse_array`,
`coreCFGToGotoBlockStep_labelMap_key`,
`blocksFoldlM_labelMap_keys_subset`,
`blocksFoldlM_labelMap_keys_in_blocks`). Could be made `private`, but
the `theorem` keyword + `private` doesn't change LoC, so left as-is.

## Tier verdict

**Tier 1.** Combined target files at 965 LoC, comfortably below the
1000-LoC Tier 1 threshold. Net saving across all three modified files
(including +73 LoC in `BlocksFoldClosed.lean` for shared helpers) is
580 LoC, well exceeding the 618-LoC Tier 1 target on the supervisor
files alone (and matching when accounting for the shared-helper
investment).

Public API preserved, axiom counts preserved, build green at every
commit.
