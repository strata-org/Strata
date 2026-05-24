# W4: CoreCFGToGotoTransformWF.lean stale-hypothesis audit

## Plan (stub)

`Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean` is the largest file
in the GOTO proof at 7,105 LoC. Audit it for stale hypotheses on theorems
and definitions across three categories:

1. **Underscore-prefixed unused params** — `_h_X` parameters that no tactic
   in the body references. Almost always safe to drop.
2. **Trivially-discharable hypotheses** — once load-bearing, now `rfl` for
   every concrete caller. **Risk:** removing forces all callers to commit
   to the trivial value. Skip unless on a private/internal helper.
3. **Vestigial hypotheses superseded by later infrastructure** — threaded
   through unused after a refactor. Same caution.

Constraints:
- Do **not** modify the public signature of
  `coreCFGToGotoTransform_wellFormed_strengthened` or any theorem
  referenced from `CoreCFGToGOTOConcrete.lean`.
- One candidate at a time, `lake build` green at every commit.
- No new `sorry` / `axiom`. Verify `_v6`/`_v7` axiom set unchanged at end.

Threshold: keep going while ≥30 LoC reachable; declare Tier 3 if every
candidate is load-bearing or only nibbling.

## Progress

(filled in as the audit runs)
