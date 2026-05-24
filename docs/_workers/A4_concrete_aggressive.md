# A4 — Aggressive cleanup of `CoreCFGToGOTOConcrete.lean`

## Result: Tier 1 (-658 LoC)

| | LoC |
| --- | --- |
| Baseline | 1,376 |
| Final | **718** |
| Saved | **658 (47.8%)** |

Tier target was ≤900 LoC (Tier 1). Achieved 718.

## Public API and axioms

- `_v6` and `_v7` external signatures: unchanged (same parameters, same conclusion).
- `#print axioms` on both: still `[propext, Classical.choice, Quot.sound]`.
- Verified by `StrataTest/Backends/CBMC/GOTO/CoreCFGToGOTOConcreteAxioms.lean`.

## Commits (on branch `A4-concrete-aggressive`)

1. `2e627227e` — stub report.
2. `63c7f16ef` — **Pass A: trim docstrings** (-172 LoC). Module preamble + four `_vN` docstrings rewritten from round-archaeology narratives down to short summaries. Per-round detail still lives in `docs/_workers/round*_supervisor_report.md`.
3. `fbc303226` — **Pass B: inline `_v4` into `_v5`, delete `_v4`** (-234 LoC). `_v4` was private with a single caller (`_v5`); its proof body now lives in `_v5`'s tactic block.
4. `f67ae9222` — **Pass C: inline `_v5` into `_v6`, delete `_v5`** (-252 LoC). Same idea: `_v5` was private with a single caller (`_v6`).
5. `5d85e74e9` — **Pass D: doc cleanup** (-0 LoC net). Refresh the live-versions header and `_v6` docstring after the waypoint deletions; clear two stale "matches vN" inline comments.

## Final structure

The file now contains:

- Module preamble (50 LoC).
- `ConcreteExprCorr` namespace (107 LoC, used internally by `_v6`).
- `_v6` (public, ~324 LoC including signature + body).
- `_v7` (public, ~196 LoC; identical surface to `_v6` minus two structural witnesses, derived via `coreCFGToGotoTransform_decompose`).

## Inlining mechanics (Passes B & C)

Both inlinings followed the same pattern:

1. Inside the caller (`_v5` for Pass B, `_v6` for Pass C), the `exact <waypoint> ...` delegation was replaced with the waypoint's actual proof body (build `wf`, discharge bridges, build `SteppingBridges`, call the storeCorr theorem).
2. Hypotheses already-in-scope at the caller layer were reused (h_red, h_op, …); the waypoint's tactic-local witnesses (h_aux_for_r7a, h_no_dead, h_brHyps, h_call_free, br) were rebuilt in the caller's scope.
3. Notably for Pass C: `_v5` built `h_aux_goto_target` per-`wf'` via `h_labelMap_agree wf'`. After inlining, `wf` is in scope and `h_labelMap_agree` is `wf`-specific, so the per-`wf'` lambda re-applies `WfLabelMapAgree.labelMap_agree_of_translator` to whatever `wf'` is supplied. This preserves universal quantification.
4. The waypoint declaration is then deleted in full.

## Verification

```
$ lake build Strata.Backends.CBMC.GOTO.CoreCFGToGOTOConcrete
✔ Built (227 jobs)

$ lake build StrataTest.Backends.CBMC.GOTO.CoreCFGToGOTOConcreteAxioms
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v6'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v7'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Notes

- The branch was cut from `htd/unstructured-to-goto` (`a012a1c01`) — but checked out as `A4-concrete-aggressive` because the worktree at `/Users/htd/Documents/Strata-goto` already holds `htd/unstructured-to-goto`. The diff is intended to be cherry-picked back / merged into the canonical branch by the supervisor.
- No new axioms, no `sorry`. No files outside `CoreCFGToGOTOConcrete.lean` and this report were modified.
