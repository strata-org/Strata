# W5: Unused-Lemma Audit of `CoreCFGToGotoTransformWF.lean`

**Status:** final
**Worker:** W5
**Base commit:** `506d524a8` (W4-base)
**Target file:** `Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean` (7,105 LoC)
**Mode:** READ-ONLY. Only this audit doc was written; no `.lean` file touched.

## TL;DR

- **17 declarations** in the file appear nowhere outside their own declaration line
  (count == 1 across `Strata/` and `StrataTest/` `.lean` files).
- After filtering out 3 `@[simp]`-tagged lemmas (which are consumed by simp
  without name reference), **14 candidates remain** with a combined budget of
  **~408 LoC**.
- Verdict: **Tier 1** (≥300 LoC of unused lemmas).
- Recommended next step: a follow-up worker can delete the candidates listed
  under `safe-to-delete` below in any order; they have no internal cross-deps.

## Audit methodology

### Step 1: enumerate declarations

I extracted every `theorem`/`lemma`/`def`/`abbrev`/`instance` in the file
(allowing `?` and `'` in names — Lean permits both) using a Python regex
equivalent to:

```
^\s*(?:@\[[^\]]+\]\s*)?(?:private |protected |public |noncomputable )*(theorem|lemma|def|abbrev|instance)\s+([A-Za-z_][A-Za-z0-9_'?]*(?:\.[...])*)
```

Total: **162 named declarations** (no `instance`s; the file has zero typeclass
instances, so the typeclass-resolution caveat in the brief does not bite).

### Step 2: count cross-project occurrences

I tokenised every `.lean` file under `Strata/` and `StrataTest/` with the same
identifier alphabet, dropped the namespace prefix when present (so a usage like
`CProverGOTO.foo` matches a decl `foo`), and tallied per-name occurrences.

This is the moral equivalent of running, for each name `N`:

```
grep -rn '\bN\b' Strata/ StrataTest/ --include='*.lean' | wc -l
```

but in a single pass over ~780k tokens (much faster than 162 separate greps).

I cross-checked 17 candidate names with a direct `grep -rEn` and the counts
matched exactly — every count==1 candidate appears at exactly one line, the
declaration site itself.

### Step 3: filtering rules

Per the task brief, I excluded from "safe-to-delete":
- `@[simp]`-tagged lemmas (consumed implicitly by `simp` calls)
- `instance` declarations (consumed by typeclass resolution) — N/A here
- Anything reachable from the load-bearing public theorems — guaranteed
  excluded since count == 1 means **no other reference anywhere**, including
  inside `coreCFGToGotoTransform_wellFormed_strengthened`,
  `coreCFGToGotoTransform_forward_simulation_concrete_v{4,5,6,7}`,
  `coreCFGToGoto_forward_simulation`, etc.

## Inventory snapshot

```
Total declarations:                        162
  Count == 1 (only declaration site):       17
  Count == 2 (one external use):            60
  Count >= 3:                               85
```

The "count == 2" tier looks roughly healthy — most are paired up
(`emitLabel_preserves_size_eq` is consumed inside the file once,
`*_preserves_locationNum_eq_index` once, etc.). Spot-checks did not reveal
transitive-dead patterns; the dead set is shallow.

## Candidates (count == 1)

For each, the columns are: file:line, kind, LoC (decl line through proof end),
sole-occurrence verification, and verdict.

### `safe-to-delete` (14 entries, ~408 LoC)

| # | Name | File:line | LoC | Notes |
|---|------|-----------|----:|-------|
| 1 | `patchGotoTargets_preserves_T` | `CoreCFGToGotoTransformWF.lean:365` | 18 | Trivial `rfl` on `.T` field. Sibling `patchGotoTargets_preserves_size`/`_nextLoc` are both used; this one was written but never called. |
| 2 | `instrAt_of_push_lt` | `CoreCFGToGotoTransformWF.lean:395` | 15 | Bounded-pc variant of `instrAt_of_push`. The unbounded `_push` and `_append_two` siblings are used; the `_lt` form is orphaned. |
| 3 | `partialWellFormedTranslation_initial` | `CoreCFGToGotoTransformWF.lean:1045` | 34 | Constructor for `PartialWellFormedTranslation` at `n = 0`. The `PartialWellFormedTranslation` structure itself is also unused outside its declaration block (verified — it appears only at L980/L996/L1003/L1029/L1040/L1055 — all in its own definition block plus this constructor). After deleting this constructor, the struct + section preamble (~100 LoC at L996–L1078) becomes dead too, but I leave that for a follow-up since the struct is a `structure`, not in the audit scope. |
| 4 | `emitUncondGoto_preserves_size_eq` | `CoreCFGToGotoTransformWF.lean:1379` | 9 | One-line `simp`-only proof. Sibling `emitCondGoto_preserves_size_eq` (count=2) is used at L2698; this `Uncond` variant has no caller. Likely an early scaffolding lemma — `emitUncondGoto` is now consumed inline elsewhere. |
| 5 | `endFunction_emit_preserves_size_eq` | `CoreCFGToGotoTransformWF.lean:1430` | 12 | One-line `simp`-only proof. Companion `_locationNum_eq_index` (count=2) IS used; this size-eq one is not. |
| 6 | `innerCmdLoop_preserves_size_eq` | `CoreCFGToGotoTransformWF.lean:1698` | 31 | Inductive proof. Superseded by `innerCmdLoop_size_le` (L1993, count=2 — used at L2194) which subsumes the equality with a `≤` bound. |
| 7 | `innerCmdLoop_preserves_locationNum_eq_index` | `CoreCFGToGotoTransformWF.lean:1729` | 44 | Inductive proof. Likely subsumed by `cmdsFoldlM_preserves_locationNum_eq_index` (L2471) plus `cmdsFoldlM_eq_innerCmdLoop_on_admitted` (L5011) in the post-shadow construction. |
| 8 | `innerCmdLoop_nextLoc_advance` | `CoreCFGToGotoTransformWF.lean:1773` | 107 | Largest single dead lemma. Inductive `nextLoc` accounting for `innerCmdLoop`. Almost certainly superseded by `cmdsFoldlM_nextLoc_advance` (L2526) once the loop was hoisted to a fold. |
| 9 | `labelMapInsert_preserves_inj` | `CoreCFGToGotoTransformWF.lean:2283` | 36 | Was used by an earlier hand-rolled WF construction. `labelMap_inj_of_translator` (L4956) — the surviving injection lemma — derives the conclusion via the translator induction directly, not via this combinator. |
| 10 | `labelMapInsert_preserves_lt` | `CoreCFGToGotoTransformWF.lean:2319` | 14 | Same story as `_preserves_inj`. |
| 11 | `hashMapToLabelMap_insert` | `CoreCFGToGotoTransformWF.lean:2364` | 30 | Conversion lemma between `HashMap.insert` and `labelMapInsert`. The shadow-based construction routes around it; `hashMapToLabelMap` itself is still used (L4555, L4563) but only at lookup positions. Neither `_empty` nor `_insert` is named in any proof — the `_empty` is `@[simp]` (kept), but `_insert` has no tag and no caller. |
| 12 | `PendingPatchesIndicesDistinct` | `CoreCFGToGotoTransformWF.lean:5785` | 4 | Predicate definition. Never referenced. The actual distinctness lemmas (`coreCFGToGotoBlockStep_pendingPatches_indices_distinct`, etc.) state the property pointwise (`Pairwise (...)`) without going through this name. |
| 13 | `PendingPatchesIndicesBounded` | `CoreCFGToGotoTransformWF.lean:5789` | 5 | Same pattern as `_Distinct`. The actual `_bound` lemmas write `∀ p ∈ patches, p.1 < bound` directly. |
| 14 | `patchesFoldlM_no_contracts_resolvedPatches_indices_subset` | `CoreCFGToGotoTransformWF.lean:6272` | 49 | A subset characterisation lemma. Looking at neighbours: `_subset` (L5909) and `_mem` (L5938) and `_pairwise_distinct` (L6591) are used; this `_indices_subset` was likely written speculatively and superseded by `_mem`. |

**LoC tally for `safe-to-delete`:** 18+15+34+9+12+31+44+107+36+14+30+4+5+49 = **408 LoC**.

### `keep` (3 entries — `@[simp]`-tagged)

These appear only at their declaration sites in source, but are tagged
`@[simp]` and consumed by `simp` invocations without a name mention. Per the
task brief, do not flag.

| # | Name | File:line | LoC |
|---|------|-----------|----:|
| K1 | `labelMapInsert_self` | `CoreCFGToGotoTransformWF.lean:2333` | 8 |
| K2 | `labelMapInsert_other` | `CoreCFGToGotoTransformWF.lean:2341` | 10 |
| K3 | `hashMapToLabelMap_empty` | `CoreCFGToGotoTransformWF.lean:2355` | 9 |

That said, a future cleanup could try `Lake build` after disabling each one
in turn — if simp's progress doesn't change, they really are dead. Out of
scope for this read-only audit.

### `needs-review` — none

Every count==1 candidate falls cleanly into either `safe-to-delete` or
the `@[simp]` skip-list. There are no borderline cases requiring deeper
analysis.

## Total estimated saving

If a follow-up worker deletes all `safe-to-delete` entries:

- **Direct saving:** ~408 LoC out of 7,105 (~5.7% of the file).
- **Indirect saving:** the `PartialWellFormedTranslation` structure
  (`structure ... extends ...` at L1003) and its preamble (~80 LoC) become
  immediately dead once `partialWellFormedTranslation_initial` is removed,
  for an additional ~80 LoC saving — **so the realistic ceiling is ~488 LoC**.

## Tier verdict

**Tier 1.** The file accumulated ~5.7% of dead code over 9 rounds of evolving
constructions. Every dead lemma can be traced to a superseded approach
(direct `innerCmdLoop` accounting → `cmdsFoldlM`-based; hand-rolled
`PartialWellFormedTranslation` → shadow-based `wellFormedTranslation_of_shadow`;
`HashMap` rewriting predicate → translator induction).

## Recommended next step

A single follow-up worker can apply the deletions in any order — none of the
14 candidates calls any of the others (verified by my count==1 check), so
there is no dependency ordering required. Suggested batching:

1. **Pass A — emit-shape orphans (~24 LoC):** `emitUncondGoto_preserves_size_eq`,
   `endFunction_emit_preserves_size_eq`, `instrAt_of_push_lt`,
   `patchGotoTargets_preserves_T`. Tiny, low risk.
2. **Pass B — `innerCmdLoop` survivors of the fold migration (~182 LoC):**
   `innerCmdLoop_preserves_size_eq`, `innerCmdLoop_preserves_locationNum_eq_index`,
   `innerCmdLoop_nextLoc_advance`. The single biggest win.
3. **Pass C — `labelMapInsert`/`hashMapToLabelMap` non-simp helpers (~80 LoC):**
   `labelMapInsert_preserves_inj`, `labelMapInsert_preserves_lt`,
   `hashMapToLabelMap_insert`. Verify the `@[simp]` siblings still rebuild.
4. **Pass D — `PartialWellFormedTranslation` constructor + struct (~115 LoC):**
   `partialWellFormedTranslation_initial` (34 LoC) **plus** the
   `structure PartialWellFormedTranslation` block at L1003 (the structure has
   no callers either — confirmed). A small amount of cross-file checking is
   warranted: ensure the structure isn't referenced via type signature in any
   downstream module.
5. **Pass E — patch/pending-patches predicates and orphan subset
   lemma (~58 LoC):** `PendingPatchesIndicesDistinct`,
   `PendingPatchesIndicesBounded`,
   `patchesFoldlM_no_contracts_resolvedPatches_indices_subset`.

After each pass, run `lake build Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF`
and `lake build Strata.Backends.CBMC.GOTO.CoreCFGToGOTOConcrete` to confirm
no breakage. Since each pass touches a contiguous block, a clean revert is
trivial if a build fails.

## Note on W4 collision

W4 is concurrently editing this file. None of the 14 deletion candidates
overlaps with the parameter-level cleanup pattern that W3/W4 have been
applying (W3's R7-style fix to `cmdEmittedAt_preserved_target_only` was a
parameter drop, not a lemma deletion). The supervisor can land both patches
independently — at worst, some line numbers shift, and `git` will rebase the
unused-lemma deletions cleanly on top of W4's parameter cleanups.
