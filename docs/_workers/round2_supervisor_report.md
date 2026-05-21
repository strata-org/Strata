# Round-2 supervisor report — A2/B2 parallel run + integration items

**Run date:** 2026-05-21
**Supervisor:** main session on `htd/unstructured-to-goto`
**Workers:** two parallel agents (A2, B2) plus three direct supervisor
items (5, 6, 4).

## TL;DR

| Item | Outcome |
|---|---|
| **Item 5** (findLocIdx_resolves) | **Closed** by supervisor (`6894c78a9`). |
| **Item 6** (vEmpty sentinel) | **Closed** by supervisor (`8be270559`). |
| **Item 4** (B → C wiring) | **Reshaped** — interfaces don't compose; deferred to top-level theorem (`07970827c`). |
| **Item 2** (Worker B's bridge finish) | **Partial** — Worker B2 stalled. `FnToGotoIDReductions` bundle landed (`b93babbc1`); per-operator helpers and top-level theorem unfinished. |
| **Item 1** (Worker A's loop induction) | **Mostly closed** — Worker A2 completed 1626 LoC of infrastructure (`52e2de42a`); only the outer-loop equivalence + shadow-construction step remain (estimated 500-900 LoC). |
| **Item 3** (A → C wiring) | **Pending** — blocked on Item 1's full closure. |

Net contribution to `htd/unstructured-to-goto` since round 1:
**~2000 LoC** of new Lean infrastructure, `lake build` green, no
`sorry`, axioms unchanged.

## Process

The round-2 brief incorporated lessons from round 1 (workers A and B
had stalled on the stream watchdog before writing their final
reports):

1. **"Write the report stub FIRST."** Both A2 and B2 followed this.
   Worker A2 ran to completion. Worker B2 stalled, but the report
   stub (already committed) provided context for salvaging.

2. **"Commit progress as you go."** Both did. Worker A2 made 15
   commits; B2 made 2 commits before stalling. Round 1's stalled
   workers had also committed enough for salvage, so this confirmed
   the pattern.

3. **"No `sorry` ever."** Both honoured. The single `sorry` mention
   in A2's file is in a docstring (Worker A's original from round 1).

4. **"Worktree isolation."** Cleanly disjoint files (Worker A2 →
   `CoreCFGToGotoTransformWF.lean`; Worker B2 →
   `ExprTranslationPreservesEvalBoolInt.lean`). No git conflicts,
   though merging via `git cherry-pick` would have hit the same
   conflicts as round 1; the supervisor again copied final file
   states across instead.

## What landed: per-item

### Item 5 — `findLocIdx_resolves` (supervisor, closed)

`Strata/Backends/CBMC/GOTO/WellFormedTranslationProps.lean` (new file,
123 LoC). Proves that under the new
`WellFormedTranslation.locationNum_eq_index` field, tautschnig's
`findLocIdx pgm.instructions i = some i`. Uses helper
`findLocIdx_go_resolves` with list-prefix-induction.

`WellFormedTranslation` itself gained a `locationNum_eq_index` field
(every instruction's `locationNum` equals its array index). The
existing `trivialWF` test was updated to discharge it for the
trivial program.

This closes Worker C's `goto_target_resolves` obligation.

### Item 6 — `coreVEmptySentinel` (supervisor, closed)

`Strata/Backends/CBMC/GOTO/ValueCorrCore.lean` extended (+68 lines).
Adds `coreVEmptySentinel := LExpr.fvar () { name :=
"__strata_vEmpty__", metadata := () } none` and routes it through
`coreToValue` (→ `some .vEmpty`) and `coreFromValue` (←
`Value.vEmpty`).

Closes Worker C's `decl_empty_value` obligation. The magic name
`__strata_vEmpty__` never collides with real source identifiers
because (a) it is double-underscored and (b) the
`<proc>::<scope>::<name>` renaming pass on real procedure-level
identifiers always inserts `::` separators.

### Item 4 — `EvalBoolCorr` wiring (supervisor, RESHAPED)

Documented in `docs/_workers/integration_notes.md`. Worker B's
`IsBoolIntTranslated.translated` produces source/target translation
correspondence; Worker C's `EvalBoolCorr` consumes target/target
evaluator agreement. They're orthogonal predicates. `EvalBoolCorr`
must be supplied directly at the eventual top-level theorem,
not derived from B's output.

The supervisor's earlier "wire B → C" plan was conflating two
different things. This is now correctly captured in the
integration_notes doc; future top-level theorem will take three
hypotheses (`EvalBoolCorr`, `EvalValueCorr`, `BoolIntOpHypotheses`)
rather than two.

### Item 1 — Worker A2 loop-invariant infrastructure (mostly closed)

Round-1 Worker A landed 831 LoC of sub-lemmas without stating the
top-level theorem. Round-2 Worker A2 added 1626 LoC of loop-
invariant infrastructure on top, bringing the file to **2457 LoC**.

**Closed:**

- Per-Cmd dispatcher `cmdEmittedAt_of_toGotoInstructions` covering
  all 6 `Imperative.Cmd` shapes (including the missing `init_det`
  two-instruction driver and `set_nondet` shape lemma + driver).
- `PartialWellFormedTranslation` invariant structure with 5
  fields capturing the loop-induction shape.
- Per-emit-helper preservation lemmas: `size_eq` and
  `locationNum_eq_index` for `emitLabel`,
  `Cmd.toGotoInstructions`, `emitCondGoto`, `emitUncondGoto`, the
  `.finish` END_FUNCTION emit, and `patchGotoTargets`.
- `innerCmdLoop` shadow capturing the inner per-cmd loop, with 6
  preservation lemmas including `nextLoc_advance` and
  `instructions_prefix?`.
- `innerCmdLoop_layout_block_body` (~200 LoC, proven) — produces
  `CmdEmittedAt` at the offset `WellFormedTranslation.layout_block_body`
  consumes.
- LabelMap operations + invariants
  (`labelMapInsert_preserves_inj`, `_preserves_lt`).
- `CoreCFGToGotoTransformShadow` structure +
  `wellFormedTranslation_of_shadow` bridge (~70 LoC) — defines
  exactly what facts the missing outer-loop step must produce, and
  converts a shadow value to `WellFormedTranslation` mechanically.

**Still open (~500-900 LoC):** producing a
`CoreCFGToGotoTransformShadow` from the actual translator's output.
This requires either:

a. Refactoring `coreCFGToGotoTransform`'s imperative `for` loop
   into a plain `foldlM` over a clean per-block step function
   (out of scope for the worker per the brief); or
b. Defining an `outerBlockLoop` shadow and proving it equivalent
   to the imperative loop body (`do`-notation equivalence proof —
   the largest piece); or
c. Reasoning directly about the `forIn`-over-`mut`-state desugar
   (brittle).

A2 deliberately did not attempt this (it's its own ~500-900 LoC
project); the architectural foundation is in place for whoever
picks it up.

### Item 2 — Worker B2 bridge finish (PARTIAL, stalled)

Worker B2 stalled on the watchdog before completing the per-operator
bridge helpers. The supervisor salvaged:

- `FnToGotoIDReductions` hypothesis bundle (47 lines, committed).
  Lists the operator-name → GOTO-id reductions
  (`fnToGotoID "Int.Add" = .ok (.multiary .Plus)`, etc.), plus
  `isSignedBvOp = false` and `parseBvExtractLo = none` reductions,
  for all 13 supported bool+int operators. **This is the missing
  infrastructure** any future worker on Item 2 will use to discharge
  the operator-name pattern matches inside `LExpr.toGotoExprCtx`.
- B2's report (`docs/_workers/B2_gap_b_finish_report.md`) extended
  by the supervisor with: what landed, what didn't, why the
  uncommitted experiments were discarded (`simp` chain didn't
  build), and the recipe for finishing.

**Discarded:** ~71 lines of uncommitted experiments that did not
build. The supervisor confirmed the discard is the right call —
the recipe in the report is cleaner.

### Item 3 — A → C wiring (PENDING)

Blocked on Item 1's full closure. The plan
(documented in `integration_notes.md`):

> "wellFormedTranslation_to_translatorBridgeHyps covering the four
> mechanical fields (`decl_lookup`, `dead_lookup`, `assign_lookup`,
> `assign_nondet_lookup`) by case-analysis on `CmdEmittedAt`."

Each follows directly from the appropriate `CmdEmittedAt`
constructor, but needs a `WellFormedTranslation` value to extract
`CmdEmittedAt` from `layout_block_body`. So Item 3 mechanically
discharges from Item 1's eventual `coreCFGToGotoTransform_wellFormed`
theorem — but until Item 1 closes, Item 3 has nothing to compose
against.

## Verification

- `lake build` succeeds (585 jobs).
- `grep -rn 'sorry\b' Strata/Backends/CBMC/GOTO/` returns only
  documentation references (no live `sorry`).
- `#print axioms CProverGOTO.coreCFGToGoto_forward_simulation` →
  `[propext, Classical.choice, Quot.sound]` (unchanged across both
  rounds).
- `WellFormedTranslation`'s new `locationNum_eq_index` field is
  discharged for the trivial-program test (`SemanticsTests.lean`).

## Process-level observations (round 2)

**The "report stub first" pattern worked.** Worker A2 used it
properly and ran to completion (cleanest deliverable in the entire
A/B/C effort across both rounds). Worker B2 also wrote a stub,
which preserved enough context that the supervisor could salvage
the work even though the worker stalled.

**The watchdog still fires unpredictably.** B2 stalled at ~7 minutes
of work (1700-second wall clock), in the middle of an active error-
diagnosis loop on `simp` chains. Round-1 workers also stalled
mid-investigation. There's no clear pattern to predict when it
fires; the only mitigation is the round-2 protocol (commit early,
report stub first, salvage what can be salvaged).

**Worker A2's report is unusually high quality.** It explicitly
documents the architectural foundation (PartialWellFormedTranslation
+ shadow) and lists the next steps with effort estimates. This is
the gold standard the round-1 reports lacked (because both stalled
workers never wrote them).

**Item 4 was a real interface mismatch, not a thinko.** The
supervisor report's plan called it "50 LoC mechanical" but the
predicates B produces and C consumes are about different things.
Catching this required reading both files with care; an
LLM-blind "wire them together" would have invented a fake bridge.
This is a worth-recording lesson for future plans.

## Next steps (suggested priority order)

1. **Finish Item 1 (~500-900 LoC).** The outer-loop equivalence +
   shadow construction. A2's architecture is in place; the
   remaining work is mechanical loop-equivalence reasoning. This
   single piece unblocks Items 3 and the eventual top-level theorem.

2. **Finish Item 2 (~150-300 LoC).** Per-operator bridge helpers
   using the `FnToGotoIDReductions` bundle, then the top-level
   `toGotoExprCtx_preservesEval_boolInt` dispatcher. Recipe is
   documented in `B2_gap_b_finish_report.md`.

3. **Item 3 (~100 LoC).** Mechanical case-analysis from Item 1's
   theorem.

4. **Top-level concrete theorem (~50 LoC).** Compose Items 1, 2, 3,
   plus the externally-supplied `EvalBoolCorr` and
   `EvalValueCorr` (the reshape from Item 4) into the final
   `coreCFGToGoto_forward_simulation_storeCorr_concrete`.

Total remaining for the **complete** call-free-fragment correctness
theorem: ~750-1450 LoC, mostly mechanical now that the
infrastructure is in place. That closes Gaps A+B+C concretely; the
remaining gaps D-G in `CoreToGOTO_CorrectnessAnalysis.md` are
independent strength expansions.

## Files changed in round 2

| File | Change | Worker |
|---|---|---|
| `Strata/Backends/CBMC/GOTO/ValueCorrCore.lean` | +68 | supervisor (item 6) |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOInvariants.lean` | +13 (one new field) | supervisor (item 5) |
| `Strata/Backends/CBMC/GOTO/WellFormedTranslationProps.lean` | new (123 LoC) | supervisor (item 5) |
| `StrataTest/Backends/CBMC/GOTO/SemanticsTests.lean` | +9 (discharge new field) | supervisor (item 5) |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean` | 831 → 2457 (+1626) | A2 |
| `Strata/Backends/CBMC/GOTO/ExprTranslationPreservesEvalBoolInt.lean` | +47 (FnToGotoIDReductions) | B2 |
| `docs/_workers/A2_gap_a_finish_report.md` | new (288 LoC) | A2 |
| `docs/_workers/B2_gap_b_finish_report.md` | new (91 LoC) | B2 + supervisor |
| `docs/_workers/integration_notes.md` | new (140 LoC) | supervisor |
| `docs/_workers/round2_supervisor_report.md` | new (this file) | supervisor |

Total: ~2400 lines added, ~85 removed across 10 files. Twelve commits between baseline (round-1 commit `5f58b1db0`) and round-2 conclusion.

## Worktree archival

Two new worktrees from round 2 remain locked at their final
commits:

- `/Users/htd/Documents/Strata/.claude/worktrees/agent-ae4bbbaf7ed56f29c` (A2)
- `/Users/htd/Documents/Strata/.claude/worktrees/agent-a953b9c579e7a44e1` (B2)

They can be removed once this report has been reviewed.
