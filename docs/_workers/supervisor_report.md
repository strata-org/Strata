# Supervisor report — parallel Gaps A/B/C run

**Run date:** 2026-05-21
**Supervisor:** main session on `htd/unstructured-to-goto`
**Workers:** three parallel agents in isolated `git worktree`s, each on
its own branch off `htd/unstructured-to-goto`.

## TL;DR

| Worker | Gap | Outcome | Status when stopped |
|---|---|---|---|
| A | Gap A — discharge `WellFormedTranslation` against `coreCFGToGotoTransform` | **Salvaged** (831 LoC of sub-lemmas; loop-invariant induction not started) | Watchdog stall (no progress for 600s) |
| B | Gap B — discharge `ExprTranslationPreservesEval` for bool+int fragment | **Salvaged** (1001 LoC, full per-operator + structural-induction theorem closed; concrete-translator bridge ~30% done) | Watchdog stall (no progress for 600s) |
| C | Gap C — discharge `SteppingBridges` from translator output | **Complete** (393 LoC, all 12 constructors closed, full report written) | Returned cleanly |

All three workers' output **builds** on `htd/unstructured-to-goto`,
contains **no `sorry`**, and adds **no new project-internal axioms**
(verified via `#print axioms`). Net contribution from the parallel
run: 2235 LoC of new Lean across four files, plus three supervisor
commits and this report.

## Process

The supervisor dispatched three sub-agents simultaneously in worktree
isolation mode. Each was briefed with:

- The relevant section of `docs/CoreToGOTO_CorrectnessAnalysis.md`.
- Pointers to the relevant existing files.
- Hard rules: no `sorry`, `lake build` must stay green at every
  commit, no destructive git operations, write a report at the end.
- Strategic latitude for choosing between options (b) abstract +
  hypotheses vs. (c) concrete restricted fragment for Gap B; whether
  to surface obligations as hypotheses vs. discharge them in-file
  for Gap C.
- Explicit instruction to commit progress as they go so partial work
  survives a watchdog stall.

Workers A and B both stalled on the stream watchdog before they
could write their final report or finish their last sub-step. Worker
C completed its full deliverable and report. Both stalled workers'
last commits build clean and have no `sorry`, so their work is
salvageable.

The supervisor:

1. Captured Worker B's last uncommitted changes (which built clean)
   onto a "WIP" commit on B's branch.
2. Cherry-pick attempts on the intermediate commits hit conflicts
   because each worker's own commit history overlapped, so the
   supervisor instead copied each worker's final file state across
   from the worktree.
3. Ran `lake build` on the merged tree — green.
4. Ran the `#print axioms` smoke tests on
   `coreCFGToGoto_forward_simulation` and
   `steppingBridges_of_translator` — both `[propext,
   Classical.choice, Quot.sound]`.
5. Made one consolidating commit per worker on
   `htd/unstructured-to-goto` (`9c0d90fab`, `ef0165db1`,
   `65818663e`).

The worktrees are not deleted; they remain locked at their final
state for archival if needed.

## What landed

### Gap A — `Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean`

831 lines of mechanical sub-lemmas:

- Per-`Cmd` shape lemmas (`Cmd_toGotoInstructions_*_ok`) for
  init_det, init_nondet, set_det, assert, assume — characterising
  what each emits.
- Emit-helper shape lemmas (`emitLabel_shape`, `emitCondGoto_shape`,
  `emitUncondGoto_shape`).
- `patchGotoTargets` invariants (size / nextLoc / T preservation).
- `instrAt` lookup helpers (`instrAt_of_push`,
  `instrAt_of_push_lt`, `instrAt_of_append_two`).
- `CmdEmittedAt` builders bridging shape lemmas to the predicate
  consumed by `WellFormedTranslation`.
- Per-`Cmd` "drivers" combining shape + builder under loop
  invariants for the four single-instruction cases.

**What's missing.** The top-level theorem
`coreCFGToGotoTransform_wellFormed` is **not** stated. The
loop-invariant induction over the imperative `for` loop is the next
step; Worker A correctly chose not to introduce a `sorry`-bodied
declaration. The two-instruction `init_det` driver is also a
follow-up.

**Effort to finish.** Roughly 300-700 LoC: state the loop
invariant, prove it preserved by each loop iteration (most cases
are direct applications of the existing drivers), then derive each
field of `WellFormedTranslation` from the final invariant.

### Gap B — `Strata/Backends/CBMC/GOTO/ExprTranslationPreservesEvalBoolInt.lean`

1001 lines, three layers:

1. **`BoolIntOpHypotheses` bundle** — per-operator agreement
   hypotheses (intAdd, intSub, intMul, intDivT, intModT, intLt,
   intLe, intGt, intGe, intEq, boolNot, boolAnd, boolOr,
   boolImplies, eq, plus value/bool agreement glue).

2. **Per-operator lemmas** — `intConst_translated`,
   `boolConst_translated`, `fvar_translated`, and one per
   operator above. Each takes the bundle and produces an
   `ExprTranslated` witness.

3. **Structural-induction theorem** —
   `IsBoolIntTranslated.translated` composes the per-operator
   lemmas over an `IsBoolIntTranslated` predicate that mirrors
   `LExpr.toGotoExprCtx`'s shape. **Closed, no `sorry`.**

Plus: WIP bridge from `LExpr.toGotoExprCtx` to
`IsBoolIntTranslated` (private helpers for `const`, `fvar`, `eq`
cases). Full bridge is the remaining work.

**Strategic choice.** Worker B picked Option (b) from the analysis
doc (abstract evaluators + per-operator hypotheses). This produced
an interface-shaped theorem — a downstream caller plugs in their
own evaluators and per-operator agreement proofs to get
`ExprTranslated`.

**Side effect.** Worker B marked seven helpers in
`LambdaToCProverGOTO.lean` as `@[expose]`
(`fnToGotoID`, `parseBvExtractLo`, `isSignedBvOp`,
`mkSDivOverflow`, `mkEuclideanDiv`, `mkEuclideanMod`,
`LExpr.toGotoExprCtx`) and changed `Core.CoreOp`'s import to
`public`. These are benign — the helpers are pure, already in the
public section, and the exposures are needed for the bridge proofs
to unfold them. The full project still builds.

**What's missing.** The bridge from the concrete `toGotoExprCtx`
back to `IsBoolIntTranslated` only handles `const`, `fvar`, `eq`.
Other LExpr cases (`app`, `op`, `ite`) need analogous bridge
helpers. Once that's done, the top-level
`toGotoExprCtx_preservesEval_boolInt` theorem (statement: "for
every bool+int fragment LExpr, its `toGotoExprCtx` translation is
`ExprTranslated`-correct under `BoolIntOpHypotheses`") is direct.

**Effort to finish.** Roughly 150-300 LoC: complete the bridge
helpers for the remaining LExpr constructors, then state and
prove the top-level theorem by structural induction using them.

### Gap C — `Strata/Backends/CBMC/GOTO/SteppingBridgesDischarge.lean`

393 lines, complete deliverable:

- **`TranslatorBridgeHyps` bundle** — 8 per-PC hypothesis fields.
- **`steppingBridges_of_translator`** — the main theorem; closes
  all 12 `StepGoto` constructors in `step_running` + `step_terminal`.

Plus: `StrataTest/.../SteppingBridgesDischargeAxioms.lean` (axiom
smoke test) and `docs/_workers/C_gap_c_report.md` (per-constructor
status, interface notes, two genuine remaining obligations).

**Already in the right shape.** Worker C's interface (`TranslatorBridgeHyps`
+ `Bisim.EvalBoolCorr`) is exactly what an integrator needs to
combine A's `WellFormedTranslation`-style facts with B's
per-operator agreement proofs. No restructuring needed.

## What's still open after this run

The original A+B+C plan estimated 2-3 weeks for each gap to land
fully. The parallel run delivered partial coverage in <1 hour of
wall-clock time. Concrete remaining work, in priority order:

1. **Worker A finish** — state and prove
   `coreCFGToGotoTransform_wellFormed` by loop-invariant induction
   using the sub-lemmas already landed. ~300-700 LoC.

2. **Worker B finish** — complete the
   `LExpr.toGotoExprCtx → IsBoolIntTranslated` bridge for the
   remaining LExpr constructors (`app`, `op`, `ite`). ~150-300 LoC.

3. **Wire A → C** — write
   `wellFormedTranslation_to_translatorBridgeHyps` covering the
   four mechanical fields (`decl_lookup`, `dead_lookup`,
   `assign_lookup`, `assign_nondet_lookup`) by case-analysis on
   `CmdEmittedAt`. ~100 LoC.

4. **Wire B → C** — feed B's
   `BoolIntOpHypotheses` + `IsBoolIntTranslated.translated` into
   C's `Bisim.EvalBoolCorr` parameter. ~50 LoC.

5. **Patcher post-condition** — add a
   `findLocIdx_resolves` lemma proven against `patchGotoTargets`,
   then extend `WellFormedTranslation` with a
   `layout_findLocIdx_resolves` field that
   C's `goto_target_resolves` consumes. ~50-100 LoC.

6. **`vEmpty` strategy choice** — Worker C documented three
   options for the `decl_empty_value` obligation. Recommend
   enriching `valueCorrCore` (Option 1) for minimum disruption.
   ~50 LoC.

After all six items, the chain becomes:

```
coreCFGToGotoTransform_wellFormed (Worker A's finish, item 1)
    ▼
wellFormedTranslation_to_translatorBridgeHyps (item 3)
    +
LExpr.toGotoExprCtx_preservesEval_boolInt (Worker B's finish, item 2)
    +
findLocIdx_resolves (item 5)
    +
valueCorrCore_extended (item 6)
    ▼
TranslatorBridgeHyps (concrete instance for the actual translator)
    +
EvalBoolCorr (concrete instance for the actual evaluators)
    ▼
steppingBridges_of_translator (Worker C's deliverable, already complete)
    ▼
StepGotoStar_to_ExecProg (Phase 3, already complete)
    ▼
coreCFGToGoto_forward_simulation_storeCorr_concrete
   (the unconditional, per-real-translator, per-bool+int-fragment,
    StoreCorr-shaped forward simulation theorem)
```

That's the natural next milestone. The remaining items D-G in
`CoreToGOTO_CorrectnessAnalysis.md` (function calls, source-side
fidelity, backward simulation, etc.) are independent strength
expansions.

## Verification

- `lake build` succeeds (585 jobs).
- `grep -rn 'sorry\b' Strata/Backends/CBMC/GOTO/` returns only
  documentation references (no live `sorry`).
- `#print axioms CProverGOTO.coreCFGToGoto_forward_simulation` →
  `[propext, Classical.choice, Quot.sound]` (unchanged).
- `#print axioms CProverGOTO.SteppingBridgesDischarge.steppingBridges_of_translator`
  → `[propext, Classical.choice, Quot.sound]`.

## Process-level observations

**What worked.** Worktree isolation. The three workers ran in
parallel against disjoint files (different `.lean` files in
`Strata/Backends/CBMC/GOTO/`) and never conflicted on git state.
Cherry-picking individual commits hit conflicts due to per-worker
file-history interleaving, but **copying final file states across
worked perfectly** — because the workers respected the disjoint-file
discipline.

**What didn't work.** The 600-second stream watchdog killed two of
three workers before they could write their reports or finish their
last sub-step. Both had committed substantial intermediate progress,
so the loss was *the report itself + ~30% of the deliverable*, not
the whole effort. For future runs: brief workers to write their
report *first* (as a stub) and update it incrementally, so a stall
near the end doesn't lose the analysis.

**The interface design held up.** All three workers chose
parameterised theorems with explicit hypothesis bundles
(`TranslatorBridgeHyps`, `BoolIntOpHypotheses`,
`coreCFGToGotoTransform_wellFormed` taking `ExprTranslationPreservesEval`
as input). This means each can be integrated independently, and the
final wiring (items 3-4 above) is mechanical case-analysis rather
than redesign.

**No worker had to be terminated for divergence.** The risk in
spec-supplied "stop early if it goes wrong" instructions is that a
worker might independently misjudge the situation and commit something
unsound. None of the three did. Worker A correctly avoided stating
the top-level theorem rather than `sorry`-stubbing it. Worker B
correctly chose Option (b) and documented the trade-off. Worker C
correctly surfaced the two genuinely-extra obligations as bundle
fields rather than smuggling in unsatisfiable hypotheses.

## Files changed

| File | Worker | Status |
|---|---|---|
| `Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean` | A | new (831 lines) |
| `Strata/Backends/CBMC/GOTO/ExprTranslationPreservesEvalBoolInt.lean` | B | new (1001 lines) |
| `Strata/Backends/CBMC/GOTO/LambdaToCProverGOTO.lean` | B | modified (`@[expose]` 7 helpers; `import Core.CoreOp` → `public import`) |
| `Strata/Backends/CBMC/GOTO/SteppingBridgesDischarge.lean` | C | new (393 lines) |
| `StrataTest/Backends/CBMC/GOTO/SteppingBridgesDischargeAxioms.lean` | C | new (14 lines) |
| `docs/_workers/C_gap_c_report.md` | C | new (269 lines) |
| `docs/_workers/supervisor_report.md` | (this) | new |

Total: ~2500 LoC across 7 files.

## Worktree archival

The three worktrees remain locked at their final commits for
forensic value. They live at:

- `/Users/htd/Documents/Strata/.claude/worktrees/agent-aeca122e7954a7ac7` (A)
- `/Users/htd/Documents/Strata/.claude/worktrees/agent-a0486c6cea1dfe7a2` (B)
- `/Users/htd/Documents/Strata/.claude/worktrees/agent-aaa4be56897351707` (C)

They can be removed once this report has been reviewed.
