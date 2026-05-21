# Round-3 supervisor report — A3/B3 parallel run

**Run date:** 2026-05-21
**Supervisor:** main session on `htd/unstructured-to-goto`
**Workers:** two parallel agents (A3, B3); no supervisor-direct items
this round.

## TL;DR

| Item | Status | Outcome |
|---|---|---|
| **Item 1** (Worker A finish) | **partially closed** | A3 hit Tier 3 (Acceptable+): structural fields proven end-to-end through the refactored translator; 7 layout/labelMap fields and loop-contract handling remain (~600-1000 LoC) |
| **Item 2** (Worker B finish) | **fully closed** | B3 hit Tier 1 (Best): all 13 per-operator helpers + ite + top-level theorem closed for bool+int fragment |
| **Item 3** (A → C wiring) | **partial** | Compose-able for structural fields; blocked on Item 1's layout fields |
| **Top-level concrete theorem** | **blocked** | Awaits remaining Item 1 work + Item 3 closure |

Net contribution to `htd/unstructured-to-goto` since round 2:
**~1900 LoC** of new Lean (B3: +1198, A3: +714, plus translator
refactor of +88), `lake build` green (585 jobs), no `sorry`, axioms
unchanged on `coreCFGToGoto_forward_simulation` and confirmed
`[propext, Classical.choice, Quot.sound]` on B3's top-level
`toGotoExprCtx_preservesEval_boolInt`.

## Per-worker outcomes

### Worker B3 — Tier 1 (Best)

**Closed** — see `docs/_workers/B3_gap_b_close_report.md`. Seven
atomic commits, file grew 1048 → 2246 lines (+1198), no `sorry`
anywhere (including docstrings).

Delivered:

- 13 per-operator bridge helpers (intAdd/Sub/Mul/DivT/ModT,
  intLt/Le/Gt/Ge, boolNot/And/Or/Implies). Each takes
  `FnToGotoIDReductions` + a side `h_op_gty` hypothesis on the
  GOTO output type, then unfolds the translator and recurses.
- `ite` extension to `isBoolIntFragment`, `BoolIntGtyAgrees`,
  `IsBoolIntTranslated`, `BoolIntOpHypotheses`, plus the per-op
  lemma `ite_translated` and the bridge helper.
- Recursive `BoolIntGtyAgrees` predicate threading GOTO-type
  agreement at every operator subterm.
- **Top-level `toGotoExprCtx_preservesEval_boolInt`**: dispatches
  on LExpr shape via `termination_by sizeOf e_core` (manual
  recursion since structural induction on `.app` doesn't directly
  produce IHs for sub-expressions). **Closed**. Axiom set:
  `[propext, Classical.choice, Quot.sound]`.

### Worker A3 — Tier 3 (Acceptable+)

**Partial** — see `docs/_workers/A3_gap_a_close_report.md`. 12
commits, WF file grew 2457 → 3171 lines (+714), translator file
grew ~88 lines for the refactor.

**Strategic choice (Option a):** Refactored the translator to
expose per-cmd / per-block / per-patch step functions over a
`CoreCFGTransLoopState` struct, making the imperative `for` loops
into `foldlM` chains. The `FinishPlacementProbe.lean` regression
test confirms behavior is bit-for-bit preserved.

Delivered:

- Per-cmd / cmds-fold / per-block / outer-blocks-fold preservation
  of `size_eq` + `locationNum_eq_index`.
- Patch-step + patches-fold preservation under
  `loopContracts = ∅` hypothesis.
- `coreCFGToGotoTransform_decompose`: extracts
  `(st_final, resolved, trans_post)` from the translator's output.
- `coreCFGToGotoTransform_size_eq_and_loc` and its `_direct`
  variant: end-to-end structural soundness.

Not delivered (out of scope for the round; sized at ~600-1000 LoC
remaining):

- `layout_location` / `layout_finish` / `layout_cond_goto` /
  `layout_cond_goto_guards` / `layout_block_body` — the layout
  fields of `WellFormedTranslation`.
- LabelMap correspondence (HashMap → LabelMap function with
  `labelMap_total`/`_inj`/`_lt`).
- `entry_in_map`.
- Loop-contract handling (the patch step's guard-tweak branch
  requires reasoning about a custom `BEq` instance).

A3's report has effort estimates per remaining field. The
structural foundation now in place means the layout fields are
mechanical extraction rather than open-ended proof work.

## What this means for the integration

The original integration plan (in
`docs/_workers/integration_notes.md`) called for:

1. Item 1 finish ✅ structural part / ⏳ layout part
2. Item 2 finish ✅ done
3. Item 3 (A → C wiring): partial — see below
4. Top-level theorem composing 1 + 2 + 3 + externally-supplied
   `EvalBoolCorr` and `EvalValueCorr`: still blocked.

### Item 3 — what's compose-able now

Worker C's `TranslatorBridgeHyps` has 8 fields:
`nameMap_inj`, `decl_lookup`, `dead_lookup`, `assign_lookup`,
`assign_nondet_lookup`, `goto_target_resolves`, `decl_empty_value`,
`assign_value_corr`, `assign_nondet_value_corr`.

Of these:

- `goto_target_resolves` already discharges from `findLocIdx_resolves`
  + `WellFormedTranslation.locationNum_eq_index` (Items 5 + 6 from
  round 2). A3's structural soundness gives `locationNum_eq_index`
  end-to-end. **Discharge-able now** modulo the
  `i < pgm.instructions.size` predicate which A3's
  `coreCFGToGotoTransform_size_eq_and_loc_direct` provides.
- `decl_lookup`, `dead_lookup`, `assign_lookup`,
  `assign_nondet_lookup`: each follows from the corresponding
  `CmdEmittedAt` constructor extracted from
  `WellFormedTranslation.layout_block_body`. **Blocked**: A3 did
  not close `layout_block_body`.
- `decl_empty_value`: closed via the `coreVEmptySentinel` recipe
  from round 2 (Item 6) — *if* the source CFG uses the sentinel.
- `assign_value_corr` / `assign_nondet_value_corr`: provided
  externally (Worker B3's `ExprTranslated` + a target-side
  evaluator agreement hypothesis).
- `nameMap_inj`: external hypothesis (the realistic-name-collision
  question is Risk #1 in the original analysis).

So Item 3 is **partially compose-able**: the
`goto_target_resolves` discharge can land now; the four
instruction-shape lookups must wait for A3's layout fields.

### The complete picture

The chain to a concrete `coreCFGToGoto_forward_simulation_storeCorr_concrete`
theorem:

```
Item 1 (A3 structural) ✅
  + Item 1 layout (~600-1000 LoC) ⏳
  ▼
Item 3 (A → C bundle) ⏳ blocked partially on Item 1 layout
  ▼
Item 4 (EvalBoolCorr + EvalValueCorr as external hypotheses) — supplied by caller
  +
Item 2 (B3 toGotoExprCtx_preservesEval_boolInt) ✅
  ▼
Top-level concrete theorem ⏳
```

About 700-1100 LoC total to close, all mechanical now.

## Process observations

**The "report stub first + commit-as-you-go" pattern continued to
deliver.** Both A3 and B3 ran cleanly to completion. No watchdog
stalls in round 3.

**Permission to refactor the translator was the right call.** A3's
report explicitly credits this — Option (a) made the proof
tractable by replacing imperative `for` loops with `foldlM`. None
of the previous rounds had this permission and accordingly hit
loop-equivalence walls.

**B3 hit Best tier without a single architectural surprise.** The
`FnToGotoIDReductions` bundle from round-2 B2 was exactly the right
infrastructure; B3 just had to use it. This is a successful example
of staged work where round N's salvage feeds round N+1.

**A3's worker apparently committed to `htd/unstructured-to-goto`
directly rather than to its worktree branch.** The brief specified
`isolation: "worktree"` but A3's commits show up on the main branch
log. The supervisor confirmed:

- A3's report says *"Worktree: `/Users/htd/Documents/Strata-goto`,
  branch `htd/unstructured-to-goto`"* — A3 was told its worktree
  was the main checkout.
- B3's commits are isolated in
  `/Users/htd/Documents/Strata/.claude/worktrees/agent-a7b855f6f1fe92f60`
  as expected.

The A3 oddity didn't cause a problem (no merge conflicts; both
workers wrote to disjoint files), but is worth noting for future
runs. If a non-isolated agent ever conflicts with a true
worktree-isolated one, the supervisor will need to do conflict
resolution.

## Verification

- `lake build` succeeds (585 jobs).
- `grep -rn 'sorry\b' Strata/Backends/CBMC/GOTO/` returns only
  documentation references (no live `sorry`).
- `#print axioms CProverGOTO.coreCFGToGoto_forward_simulation` →
  `[propext, Classical.choice, Quot.sound]` (unchanged).
- `#print axioms CProverGOTO.ExprTranslationBoolInt.toGotoExprCtx_preservesEval_boolInt` →
  `[propext, Classical.choice, Quot.sound]`.
- `FinishPlacementProbe.lean` passes after A3's translator refactor.

## Next steps (suggested for round 4)

1. **Worker A4: layout fields + labelMap correspondence** — pick
   up where A3 left off. Each layout field is mechanical extraction
   from per-block / per-cmd step preservation. ~600-800 LoC.
   Skip loop-contract handling (sidestep with hypothesis as A3
   did).
2. **Supervisor: Item 3 — `wellFormedTranslation_to_translatorBridgeHyps`**
   — once A4 lands, the four instruction-shape lookups +
   `goto_target_resolves` discharge mechanically from
   `CmdEmittedAt` + `findLocIdx_resolves`. ~100 LoC.
3. **Supervisor: top-level concrete theorem** — compose all the
   pieces. ~50 LoC.

After that the chain is complete: a concrete
`coreCFGToGoto_forward_simulation_storeCorr_concrete` theorem on
the call-free, bool+int-fragment, single-`.finish` CFG slice, with
axioms `[propext, Classical.choice, Quot.sound]`.

## Files changed in round 3

| File | Change | Worker |
|---|---|---|
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOPipeline.lean` | refactor: extract per-block / per-cmd / per-patch step (+88) | A3 |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean` | 2457 → 3171 (+714) | A3 |
| `Strata/Backends/CBMC/GOTO/ExprTranslationPreservesEvalBoolInt.lean` | 1048 → 2246 (+1198) | B3 |
| `docs/_workers/A3_gap_a_close_report.md` | new (199 LoC) | A3 |
| `docs/_workers/B3_gap_b_close_report.md` | new (130 LoC) | B3 |
| `docs/_workers/round3_supervisor_report.md` | new (this file) | supervisor |

Total: ~2330 lines added. 19 commits since round 2 baseline.

## Worktree archival

Round-3 worktrees:

- A3 was committed directly to `htd/unstructured-to-goto`; no
  separate worktree to archive.
- B3 worktree:
  `/Users/htd/Documents/Strata/.claude/worktrees/agent-a7b855f6f1fe92f60`
  remains locked.
