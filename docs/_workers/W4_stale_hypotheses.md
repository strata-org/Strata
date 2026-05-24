# W4: CoreCFGToGotoTransformWF.lean stale-hypothesis audit

## Plan (carried over from stub)

`Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean` is the largest file
in the GOTO proof at 7,105 LoC. Audit it for stale hypotheses on theorems
and definitions across three categories:

1. **Underscore-prefixed unused params** — `_h_X` parameters that no tactic
   in the body references. Almost always safe to drop.
2. **Trivially-discharable hypotheses** — once load-bearing, now `rfl` for
   every concrete caller. Skip unless on a private/internal helper.
3. **Vestigial hypotheses superseded by later infrastructure** — threaded
   through unused after a refactor. Same caution.

## Verdict: Tier 3 (3 LoC saved)

**7,105 → 7,102 LoC = 3 LoC saved.**

The file is largely clean for what it does. Lean's `unusedVariables` linter
flagged exactly two real candidates, both internal/non-exported helpers,
and removing them produced one cascade (a parameter that became unused
once another was removed). After applying these, the linter reports zero
remaining unused-variable warnings on the file.

The file's many large theorems thread upwards of fifteen hypotheses each,
but every one I sampled used every parameter. The Tier-3 outcome is the
honest report: the file is lean for its size.

## Inventory of candidates

### Lint-flagged (confirmed stale)

| # | Theorem (line) | Stale param | Category | Action |
|---|---|---|---|---|
| 1 | `coreCFGToGotoTransform_size_eq_and_loc` (4142) | `h_run` | 3 (vestigial) | **Removed** — saved 2 LoC |
| 2 | `labelMapInsert_preserves_inj` (2283) | `h_fresh_dom` | 1 (lint-flagged) | **Removed** — saved 1 LoC |
| 3 | `coreCFGToGotoTransform_size_eq_and_loc` (4141) | `Env` | cascaded from #1 | **Removed** — 0 net (already counted in #1) |

### Surveyed and load-bearing (no action)

| Theorem / region | Why it stayed | Notes |
|---|---|---|
| `coreCFGToGotoTransform_wellFormed_strengthened` (7032) | Public-API per task brief | Cannot change |
| `coreCFGToGotoTransform_decompose` (4219) | Used in `_v7` | Public-API |
| `coreCFGToGotoInitState` (4213) | Used in `_v6`/`_v7` parameter types | Public-API |
| `coreCFGToGotoTransform_size_eq_and_loc_direct` (4307) | `h_run`/`Env` used via `coreCFGToGotoTransform_decompose` | Internal but truly used |
| `wellFormedTranslation_of_shadow` (4434) | `Env`/`functionName`/`trans₀` only thread the `shadow` arg's type | Removing them breaks unification of `CoreCFGToGotoTransformShadow` indices |
| `CoreCFGToGotoTransformShadow` (4341) | Same — structure indices, not used in fields | Removing them is a real API change |
| `cmdEmittedAt_*_of_toGotoInstructions` (586–924) | Each Cmd-shape uses every parameter | All hypotheses used |
| `coreCFGToGotoBlockStep_layout_block_body` (5043) | All 12 params used in body | |
| `blocksFoldlM_layout_block_body` (5212) | All 12 params used in body | |
| `coreCFGToGotoBlockStep_pendingPatches_indices_distinct` (6120) | All 7 params used | |
| `blocksFoldlM_layout_cond_goto_pre_patch` (6477) | All 6 params used | |
| `layout_cond_goto_of_translator` (6666), `layout_cond_goto_guards_of_translator` (6918), `layout_block_body_of_translator` (5400) | Public closure helpers used by `_strengthened`; every parameter routes into either `coreCFGToGotoTransform_decompose` or the chosen layout fold | |
| 17 `private theorem patch_*` helpers | Each used in adjacent caller (sampled all) | |

### Skipped (out of scope)

* **Dead theorem `labelMapInsert_preserves_inj`** has zero callers
  anywhere. Deleting it would save ~36 LoC. The task brief is "remove
  stale hypotheses on theorems" — not "remove dead theorems" — so I
  scoped to dropping its lint-flagged unused parameter only.
* **`@[simp]` lemmas `labelMapInsert_self`/`labelMapInsert_other`** —
  no explicit callers but `@[simp]` tag means `simp` may use them
  implicitly. Untouched.

## Per-candidate detail

### Candidate 1 — `coreCFGToGotoTransform_size_eq_and_loc`'s `h_run`

Internal helper at line 4142. Caller is `coreCFGToGotoTransform_size_eq_and_loc_direct`
(line 4307), which derives `h_blocks_run`/`h_patches_run`/`h_ans_eq` via
`coreCFGToGotoTransform_decompose ... h_run`. Inner helper's body uses
`h_blocks_run`/`h_patches_run`/`h_ans_eq` directly; `h_run` itself is
threaded but never referenced.

* **Linter:** `unused variable h_run` at 4154.
* **Action:** dropped from inner helper's signature and from the call
  site at 4334.
* **Verification:** `lake build Strata.Backends.CBMC.GOTO.CoreCFGToGOTOConcrete` green.

### Candidate 2 — `labelMapInsert_preserves_inj`'s `h_fresh_dom`

Public-but-uncalled theorem at line 2283 stating that
`labelMapInsert m label pc` preserves `m`'s injectivity provided the
new `pc` is fresh in the codomain (`h_fresh_cod`) **and** the new
`label` is fresh in the domain (`h_fresh_dom`). The proof case-splits
on `l₁ = label` / `l₂ = label`; the contradiction in mixed cases
goes through `h_fresh_cod` — `h_fresh_dom` is genuinely never used.

* **Linter:** `unused variable h_fresh_dom` at 2287.
* **Action:** dropped the parameter.
* **Verification:** `lake build` green.
* **Caller impact:** none — theorem has no callers in the workspace.

### Candidate 3 — `coreCFGToGotoTransform_size_eq_and_loc`'s `Env` (cascade)

After removing `h_run` (Candidate 1), `Env` only appeared in the now-removed
`h_run` type. The linter then flagged `unused variable Env` at 4142.

* **Linter:** `unused variable Env` (post-Candidate-1).
* **Action:** dropped from inner helper's signature and from the call site.
* **Verification:** `lake build` green; linter clean.

## Verification

* `lake build Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF` green
  at every commit.
* `lake build Strata.Backends.CBMC.GOTO.CoreCFGToGOTOConcrete` (downstream
  consumer of the public theorems) green at the final commit.
* `lake env lean Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean`
  reports **zero** remaining `unused variable` warnings on this file
  (only pre-existing `unusedSimpArgs` and a `getElem?_push_eq`
  deprecation, neither in scope here).
* No new `axiom`, `sorry`, or `admit` introduced.
* Public API of `coreCFGToGotoTransform_wellFormed_strengthened`,
  `coreCFGToGotoTransform_decompose`, `coreCFGToGotoTransform_size_eq_and_loc_direct`,
  `wellFormedTranslation_of_shadow`, and `CoreCFGToGotoTransformShadow`
  unchanged.
* **Axiom verification (`_v6`/`_v7`):**
  ```
  'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v6'
   depends on axioms: [propext, Classical.choice, Quot.sound]
  'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v7'
   depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
  Unchanged from baseline.

## Commits

```
565f714d6 docs(W4): stub plan
5b20dcc23 refactor(W4): drop unused h_run parameter from coreCFGToGotoTransform_size_eq_and_loc                  -2 LoC
a49d8f731 refactor(W4): drop unused h_fresh_dom parameter from labelMapInsert_preserves_inj                      -1 LoC
dc91f4d5c refactor(W4): drop now-unused Env parameter from coreCFGToGotoTransform_size_eq_and_loc                 0 LoC (parameter only)
                                                                                                       total = -3 LoC (7,105 → 7,102)
```

## Honest assessment

This file got most of its cruft removed in earlier rounds (the file's
own commit history shows a "round-9 cleanup" comment about removing
`_v1`/`_v2`/`_v3` waypoint versions). What remains is dense but
load-bearing. The lint output is the most reliable signal here — Lean
flags every truly unreferenced parameter, and after Candidates 1/2/3
the file is lint-clean. Manual scanning of the 23 `private` helpers
plus the 10 `*_of_translator` closures plus the structure-soundness
chain found zero further removable hypotheses.

A more aggressive sweep could delete `labelMapInsert_preserves_inj`
(zero callers, ~36 LoC), but that exceeds the brief's "stale hypotheses"
scope into "dead-theorem deletion." Filed as a known opportunity for
a future audit if dead code becomes a focus.
