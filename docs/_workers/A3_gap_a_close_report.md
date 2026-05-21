# Worker A3 — Gap A close report (round 3)

## Goal

Close `coreCFGToGotoTransform_wellFormed` in
`Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean`. Round-2
A2 left a `wellFormedTranslation_of_shadow` bridge; the remaining
piece is producing a `CoreCFGToGotoTransformShadow` from the
translator's output.

## Strategic decision

TBD — to be filled in as exploration proceeds. Three options
listed in A2's report (order is preference order set by
supervisor):

a. **Refactor `coreCFGToGotoTransform`** to be a `foldlM` over a
   per-block step function. The supervisor has explicitly
   permitted this; preferred if a clean refactor is feasible.
b. **Define an `outerBlockLoop` shadow** in the WF file and prove
   it equivalent to the imperative loop (largest piece per A2).
c. **Reason about the `forIn`/`mut` desugar directly** (brittle).

## Status

In progress. See git log for incremental commits.

## Working notes

- Started 2026-05-21.
- Worktree: `/Users/htd/Documents/Strata-goto`, branch
  `htd/unstructured-to-goto`.
- Initial baseline: commit `d34adcbb7` (round-2 A2 + supervisor docs).
- A2 reports:
  - File: 2457 LoC.
  - Existing infrastructure: `PartialWellFormedTranslation`,
    `innerCmdLoop`, `CoreCFGToGotoTransformShadow`,
    `wellFormedTranslation_of_shadow`,
    `innerCmdLoop_layout_block_body`, `labelMapInsert`
    invariants, per-Cmd preservation lemmas.
  - `lake build`: green.
  - No live `sorry`.

## Plan

1. Read the actual translator body. Decide between options (a/b/c).
2. If (a): refactor to `foldlM` per-block step function. Run
   `FinishPlacementProbe.lean` and full `lake build` to verify
   behavior preserved.
3. Define the per-block step function as a pure recursive shadow.
4. Prove the equivalence (translator-output = step's output).
5. Prove the per-block step preserves the partial-WF invariant
   and produces the right shadow facts.
6. Build the `CoreCFGToGotoTransformShadow` value at the end of
   the loop, threading patching-correctness.
7. Discharge the top-level theorem via
   `wellFormedTranslation_of_shadow`.
