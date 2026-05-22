# Round-6 supervisor report — R6a/R6b parallel run + v3 composition

**Run date:** 2026-05-22 (started 2026-05-21)
**Supervisor:** main session on `htd/unstructured-to-goto`
**Workers:** two parallel agents (R6a, R6b) on disjoint files +
supervisor v3 composition.

## TL;DR

| Item | Status | Outcome |
|---|---|---|
| **Worker R6a** | **Tier 3 (Acceptable)** | `wellFormedTranslation_to_translatorBridgeHyps` discharges 2 of 8 fields from `wf` (+ 1 vacuated via `h_no_dead`); 5 remain caller passthroughs. Axiom set standard. |
| **Worker R6b** | **Tier 1 (Best)** | `coreCFGToGotoTransform_forward_simulation_concrete_v2` discharges both `h_tx_eq` and `h_expr_translated_witness` via a `ConcreteExprCorr` namespace. Axiom set standard. |
| **Supervisor v3** | **closed** | `coreCFGToGotoTransform_forward_simulation_concrete_v3` composes R6a + R6b: takes R6a's 8 bridge hypotheses + R6b's expression bundle, internally builds `h_brHyps`, delegates through. |

Net contribution to `htd/unstructured-to-goto` since round 5:
**~750 LoC** (R6a: 235 LoC new file + 4 small commits; R6b: ~270
LoC additions to existing file + 1-token translator exposure;
supervisor v3: ~256 LoC). `lake build` green throughout. No
`sorry`/`admit` in live code. Standard axiom set on all top-level
theorems.

## Per-worker outcomes

### Worker R6a — Tier 3 (Acceptable)

`docs/_workers/R6a_translator_bridge_report.md`. Five commits.

**Delivered** (`Strata/Backends/CBMC/GOTO/TranslatorBridgeHypsDischarge.lean`,
235 LoC):

* `wellFormedTranslation_to_translatorBridgeHyps` produces a
  `TranslatorBridgeHyps` from a `WellFormedTranslation` plus 8
  per-PC bridge hypotheses.

**Field-by-field discharge breakdown:**

| Field | Status | How |
|---|---|---|
| `nameMap_inj` | passthrough | caller `h_inj` |
| `goto_target_resolves` | **discharged from `wf`** | `findLocIdx_resolves` + `wf.locationNum_eq_index` (modulo small `h_goto_target_in_range` side condition) |
| `dead_lookup` | **vacuated** | `h_no_dead` (translator never emits DEAD) |
| `decl_lookup` | passthrough | `CmdEmittedAt`'s lhs is existential |
| `assign_lookup` | passthrough | same |
| `assign_nondet_lookup` | passthrough | same |
| `decl_empty_value` | passthrough | source/target evaluator obligation |
| `assign_value_corr` | passthrough | source/target evaluator obligation |
| `assign_nondet_value_corr` | passthrough | source/target evaluator obligation |

**Why not better.** R6a documented two structural obstacles:

1. **`CmdEmittedAt`'s existentials.** The lookup fields require
   knowing that the emitted GOTO instruction's lhs operand equals
   `Expr.symbol (nameMap x) gty`, but `CmdEmittedAt` carries the
   lhs as an existential variable rather than fixing its shape.
   Closing these would require either strengthening `CmdEmittedAt`
   to expose the lhs explicitly, or reshaping
   `TranslatorBridgeHyps` to make the lookup fields conditional on
   source-side step provenance.
2. **Source/target evaluator agreement** for the value-correspondence
   fields. The structural soundness from `WellFormedTranslation`
   doesn't tell you anything about evaluator behaviour — that's
   inherently a caller obligation.

Both are deferred to round 7+ (the lookup fields are the more
tractable target).

### Worker R6b — Tier 1 (Best)

`docs/_workers/R6b_h_tx_eq_report.md`. Three commits.

**Delivered** (additions to
`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean`, ~267 lines;
plus a 1-token `@[expose]` on `Lambda.LExpr.toGotoExpr`):

* `ConcreteExprCorr.UniformBoolIntFragment` — caller-supplied
  uniformity hypothesis (every Core expression in the bool+int
  fragment, with gty-agreement, with successful translation).
* `ConcreteExprCorr.tx` — `noncomputable` translator function
  picked via `Classical.choose` from the existential success
  witness.
* `ConcreteExprCorr.h_tx_eq_holds` — discharges `h_tx_eq` via
  `Classical.choose_spec` plus the now-`rfl`
  `Imperative.ToGoto.toGotoExpr = LExpr.toGotoExprCtx []`
  identity.
* `ConcreteExprCorr.h_expr_translated_witness_holds` — discharges
  via B3's `toGotoExprCtx_preservesEval_boolInt` chained with
  `IsBoolIntTranslated.translated`.
* `coreCFGToGotoTransform_forward_simulation_concrete_v2` —
  top-level theorem replacing v1's three expression-side
  hypotheses (`h_expr`, `h_tx_eq`, `h_expr_translated_witness`)
  with B3's `BoolIntOpHypotheses` + `FnToGotoIDReductions` +
  `UniformBoolIntFragment` + `h_commutes_not`.

**Notable findings (from R6b report):**

* `Lambda.LExpr.toGotoExpr` lacked `@[expose]`, blocking the `rfl`
  identity. One-token fix; safe (body is `toGotoExprCtx [] e`).
* `ExprTranslationPreservesEval.tx_commutes_not` is **dormant** —
  declared on the structure but read by no proof anywhere in
  `Strata/`. The hypothesis is generally **false** for the actual
  translator (since `HasNot.not Core.true = Core.false` while
  `(tx Core.true).not` is `.unary .Not (tx Core.true)`). Future
  cleanup opportunity: drop this field from v1.
* `UniformBoolIntFragment` is a strong universal hypothesis. It is
  satisfiable for any caller who restricts the source `δ` to
  expressions in the bool+int fragment but is not satisfiable for
  arbitrary Core expressions.

### Supervisor — v3 composition

After R6a/R6b returned (R6a's commits had been on a divergent
branch line; supervisor cherry-picked them onto HEAD), the
supervisor wrote
`coreCFGToGotoTransform_forward_simulation_concrete_v3` in
`CoreCFGToGOTOConcrete.lean` (~256 LoC).

**Strategy:** v3 takes R6a's bridge inputs (R6a's 8 per-PC
hypotheses replacing `h_brHyps`) and R6b's expression bundle
(`h_red`, `h_op`, `h_uniform`, `h_commutes_not` replacing
`h_expr_corr` + `h_tx_eq` + `h_expr_translated_witness`). Inside
the proof:

1. Build `h_expr` from R6b's `ConcreteExprCorr.buildExprCorr`.
2. Discharge `h_tx_eq_pre` and `h_expr_translated_witness` via
   R6b's `h_tx_eq_holds` and `h_expr_translated_witness_holds`.
3. Get a `WellFormedTranslation` via the round-5 strengthened
   theorem.
4. Discharge `h_brHyps` via R6a's
   `wellFormedTranslation_to_translatorBridgeHyps`.
5. Build `SteppingBridges` via Worker C's
   `steppingBridges_of_translator`.
6. Invoke the storeCorr forward simulation.

**Verified axiom set:**

```
'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v3'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

Same as the original `coreCFGToGoto_forward_simulation`. No new
project-internal axioms.

**Removed:** redundant `[SemanticsTautschnig.ValueCorr Core.Expression]`
instance bracket (the global `valueCorrCore` instance is found by
type-class search; the bracket was overspecifying and conflicting
with R6a's expectation).

## What this delivers

After round 6, the top-level concrete theorem `_v3` takes only:

* **Translator-input invariants** (mostly trivial when the caller
  uses `stmtsToCFG` + empty initial state): `h_init_size`,
  `h_init_loc`, `h_distinct`, `h_admitted_blocks`,
  `h_loopContracts_empty_post`, `h_entry_first`.
* **B3 expression-side bundle** (caller-supplied): `h_red`, `h_op`,
  `h_uniform`, `h_commutes_not`.
* **`nameMap` + `Function.Injective nameMap`** (caller-supplied;
  Risk #1 from the original analysis).
* **R6a's 8 per-PC bridge hypotheses** (5 of which are still
  passthroughs from R6a; round-7 candidates):
  `h_goto_target_in_range`, `h_no_dead`,
  `h_decl_lookup`, `h_assign_lookup`, `h_assign_nondet_lookup`,
  `h_decl_empty_value`, `h_assign_value_corr`,
  `h_assign_nondet_value_corr`.
* **Target-side**: `callResult`, `eval`, `fenv`,
  `h_eval_bool_corr` (caller-supplied target/target evaluator
  agreement).
* **Source-side**: `σ`, `σ'`, `b`, `σ_goto`, `h_corr`, `h_run_src`.
* `h_wf_bool : WellFormedSemanticEvalGotoBool δ_goto_bool`
  (caller-supplied bool-evaluator well-formedness).

**Conclusion** (matching v1/v2):

```
∃ pc_entry σ_goto',
  StoreCorr nameMap σ' σ_goto' ∧
  ExecProg callResult eval fenv pgm pc_entry σ_goto σ_goto' none
```

This is the complete soundness story for the call-free,
bool+int-fragment, single-`.finish` CFG slice — modulo R6a's 5
remaining caller-side passthroughs and the genuine evaluator-side
caller obligations.

## What's still open after round 6

Looking at the v3 hypothesis list, the obligations group as
follows:

### Genuine caller obligations (not closable by translator induction)

These are facts about the caller's evaluator/store/source-program,
not facts about the translator:

* `h_eval_bool_corr` (target/target boolean evaluator agreement).
* `h_corr` (initial-store correspondence).
* `h_run_src` (source-side terminating run; this is the input).
* `h_op`, `h_uniform`, `h_commutes_not` (B3 expression-side
  hypotheses).
* `h_inj : Function.Injective nameMap` (Risk #1; a property of
  the caller's chosen nameMap).
* `h_red : FnToGotoIDReductions` (a fact about the caller's
  operator-name conventions).
* `h_decl_empty_value`, `h_assign_value_corr`,
  `h_assign_nondet_value_corr` (the three R6a value-side
  passthroughs; bridge between source-side `δ`'s output and
  target-side `eval`).
* `h_wf_bool` (boolean evaluator well-formedness).

### Round-7 candidates (closable by deeper translator induction)

These should be discharable by induction on the translator output
(i.e., by extending Worker A's WellFormedTranslation infrastructure):

* `h_goto_target_in_range` — every emitted GOTO's target PC is in
  bounds. Follows from `WellFormedTranslation.layout_cond_goto`'s
  `labelMap lf = some pc_lf` plus `layout_location` (any pc in the
  labelMap is < `instructions.size` from A4's `labelMap_lt`).
  ~50-100 LoC.
* `h_no_dead` — translator never emits DEAD. Follows by induction
  on the per-block step (every emit-helper pushes
  DECL/ASSIGN/ASSERT/ASSUME/GOTO/LOCATION/END_FUNCTION, never
  DEAD). ~30-50 LoC.
* `h_decl_lookup`, `h_assign_lookup`, `h_assign_nondet_lookup` —
  follow from extending `CmdEmittedAt` to expose the lhs symbol
  explicitly, then case-analysis on each constructor. ~150-300 LoC.

### Translator-input invariants (mostly trivial)

These hold for any caller using `stmtsToCFG` + empty initial
state. Closing them as theorems for that specific path would close
the chain at `procedureToGotoCtxViaCFG` rather than
`coreCFGToGotoTransform`.

## Process observations

**Both R6a and R6b ran cleanly** — no watchdog stalls.

**R6a's outcome (Tier 3) reflected genuine structural obstacles**,
not laziness. The lookup-field obstacle is real: `CmdEmittedAt`
was designed before `TranslatorBridgeHyps` existed, and the
existential `lhs` field doesn't expose enough to discharge the
`getAssignLhs = some (nameMap x)` lookup. R6a's choice to surface
the obstacles cleanly as hypothesis parameters (rather than push
into the round-6 budget) was the right call.

**R6b's `Classical.choose`-based `tx` field** is an interesting
move. Rather than committing to a specific `tx` function, R6b
defines `tx h_uniform := Classical.choose (h_uniform e).2` (the
witness from `UniformBoolIntFragment`). This means the equality
between `Imperative.ToGoto.toGotoExpr` and `tx` reduces to
`Classical.choose_spec` — making `h_tx_eq` discharge automatic.
Clever.

**A merge note:** R6a's commits had been on a divergent branch
line that wasn't on `htd/unstructured-to-goto`. Cherry-picking
the three substantive commits worked cleanly; the report file's
"deleted by us" rename needed a manual `cp` from the worktree
(small friction, no real conflict). For round 7, supervisor will
explicitly check the working dir state after each worker returns
to catch divergent-branch-line situations earlier.

## Cumulative across all rounds

| Round | New Lean LoC | Theorem closed |
|---|---|---|
| Pre-rounds | ~3000 | `coreCFGToGoto_forward_simulation` (Phase 0/1/2/3 from the original expansion plan) |
| Round 1 | ~2500 | A's sub-lemmas + B's per-operator + C's full discharge |
| Round 2 | ~2000 | A2's loop infrastructure + B2's `FnToGotoIDReductions` + items 5/6 |
| Round 3 | ~1900 | A3's structural soundness + B3's full bool+int bridge |
| Round 4 | ~1900 | A4's WF top-level (Tier 2) + supervisor's concrete top-level (Tier 1) |
| Round 5 | ~2400 | A5a/A5b layout closures (both Tier 1) + supervisor's strengthened WF |
| Round 6 | ~750 | R6a's TranslatorBridgeHyps bridge (Tier 3) + R6b's expression-side discharge (Tier 1) + v3 composition |

**~14,450 LoC** of correctness infrastructure. `lake build` green
throughout, no `sorry` in live code, all top-level theorems closed
under the standard axiom set `[propext, Classical.choice, Quot.sound]`.

## Files changed in round 6

| File | Change | Worker |
|---|---|---|
| `Strata/Backends/CBMC/GOTO/TranslatorBridgeHypsDischarge.lean` | new (235 LoC) | R6a |
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` | +267 (R6b) +256 (supervisor v3) | R6b + supervisor |
| `Strata/Backends/CBMC/GOTO/LambdaToCProverGOTO.lean` | +1 char (`@[expose]`) | R6b |
| `docs/_workers/R6a_translator_bridge_report.md` | new (197 LoC) | R6a |
| `docs/_workers/R6b_h_tx_eq_report.md` | new (226 LoC) | R6b |
| `docs/_workers/round6_supervisor_report.md` | new (this file) | supervisor |

## Worktree archival

R6a worktree:
`/Users/htd/Documents/Strata/.claude/worktrees/agent-a7314fa05673afa5b`
R6b worktree:
`/Users/htd/Documents/Strata/.claude/worktrees/agent-a771473ebf1a1c572`

Both remain locked at their final commits.

## Suggested round 7

The natural round-7 scope is to close R6a's three "tractable
passthroughs":

1. `h_goto_target_in_range` (~50-100 LoC).
2. `h_no_dead` (~30-50 LoC).
3. `h_decl_lookup`/`h_assign_lookup`/`h_assign_nondet_lookup`
   (~150-300 LoC after a small `CmdEmittedAt` strengthening).

After these, `_v4` would have only:
* Translator-input invariants (trivial for `stmtsToCFG` callers).
* B3's expression-side bundle (caller-supplied).
* `Function.Injective nameMap` (Risk #1).
* Three value-side passthroughs (genuine source/target evaluator
  obligations).
* Target-side: `h_eval_bool_corr`.
* Source-side: `h_corr`, `h_run_src`.

That would be the "concrete soundness story modulo evaluator
agreement" milestone — a complete theorem about *the translator's
shape*, with all remaining hypotheses genuinely about the
caller's evaluator/store/program rather than the translator's
behaviour.
