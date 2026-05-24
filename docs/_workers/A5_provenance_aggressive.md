# A5 — `GotoTargetProvenance` + `WfLabelMapAgree` aggressive cleanup

**Worker:** A5.
**Branch base:** `htd/unstructured-to-goto` (commit `a012a1c01`).
**Scope:** trim the two R8a/R10a worker outputs:
* `Strata/Backends/CBMC/GOTO/GotoTargetProvenance.lean` (920 LoC)
* `Strata/Backends/CBMC/GOTO/WfLabelMapAgree.lean` (698 LoC)

Total combined: 1618 LoC. Targets:
* **Tier 1**: combined ≤1,000 LoC (-618).
* **Tier 2**: combined 1,000-1,400 LoC (-218 to -618).
* **Tier 3**: combined stays >1,400 LoC.

## Plan (stub)

### Audit phase (per file)

For each file:
1. **Dead lemma scan**: for every `theorem`/`def` declared, run
   `grep -rn '<name>' Strata/ StrataTest/`; flag declarations whose only
   reference is the declaration itself.
2. **Stale comment scan**: any docstrings/sections referring to L3/W1/R8a/R10a
   work that's no longer accurate.
3. **Internal redundancy**: per-block emit step lemmas
   (emitLabel/CondGoto/UncondGoto/EndFunction) — common pattern?

### Cross-file phase

Both files thread similar structural reasoning through the blocks-fold +
patcher decomposition. Look for:
* Shared decompose-and-bridge boilerplate around
  `coreCFGToGotoTransform_decompose` / `patchesFoldlM_no_contracts_trans_eq`
  / `h_loopContracts_empty_post`.
* Anything that could move into `BlocksFoldClosed.lean` as a generic
  "lift `P` from blocks-fold to `ans` under empty loop contracts" helper.

### Public API to preserve

* `everyGotoTargetIsLabelMapEntry_of_translator_translatorMap` (called by `_v5`/`_v6`/`_v7`)
* `everyGotoTargetIsLabelMapEntry_of_translator` (the `wf.labelMap` form)
* `labelMap_agree_of_translator` (called by `_v6`/`_v7`)
* Plus any other public theorem still grepped from the public set.

### Process

1. Stub report (this file). Commit.
2. Audit each file independently.
3. Apply per-file cleanups, commit between each.
4. If cross-file shared code emerges, factor out (carefully — `BlocksFoldClosed.lean` may be the natural home).
5. **Lake build green at every commit.**
6. **Verify axioms** at end.

## Constraints (from supervisor)

* Don't touch any file other than these two and possibly `BlocksFoldClosed.lean`.
* No new `axiom`. No `sorry`.
* No `git push`. No commits under `docs/superpowers/specs/`.

## Status

Stub. Will be filled in after audits + cleanup passes.
