# Worker L4 — OpDesc full refactor (aggressive path)

**Branch base:** `htd/unstructured-to-goto`
**Target file:** `Strata/Backends/CBMC/GOTO/ExprTranslationPreservesEvalBoolInt.lean`
**Reference:** `docs/_workers/L1_opdesc_smoke_test.md` (smoke-test feasibility study).

## TL;DR

**Tier 1: aggressive path completed end-to-end.** All 12 binary
operators ported to `BoolIntBinOpDesc` + 2 generics; both
`<op>_translated` lemmas and `isBoolIntTranslated_of_toGotoExprCtx_<op>`
bridge helpers deleted; dispatch sites in `IsBoolIntTranslated.translated`
and `toGotoExprCtx_preservesEval_boolInt` rewritten to call the generics
directly.

* Baseline: **2246 LoC**.
* After refactor: **1527 LoC**.
* **Net saving: 719 LoC** (-31.6 %), within L1's projected ~600-800 LoC
  range and matching the audit's headline claim.
* Diff: `+210 / -929`.
* `lake build` green at every commit (201/201 in the per-target build,
  585/585 in the full build).
* Axioms unchanged: `_v6` and `_v7` still depend only on
  `[propext, Classical.choice, Quot.sound]`.

## Per-step LoC progression

| Step | LoC | Δ | Notes |
|---|---|---|---|
| Baseline (3c23ec624) | 2246 | — | original |
| +Descriptor + 2 generics + intAdd PoC | 2375 | +129 | overhead added before any deletion |
| Delete 12 `<op>_translated` lemmas | 2229 | −146 | dispatch via `binOp_translated_of_corr` |
| Delete 12 binary bridge helpers | 1533 | −696 | dispatch via `isBoolIntTranslated_of_toGotoExprCtx_binOp` |
| Drop dead `op_id_ne_funApp_unary` | 1527 | −6 | pre-existing dead lemma, surfaced after cleanup |

The bridge-helper deletion is by far the biggest single win, matching
L1's prediction (~640 LoC). The `<op>_translated` deletion saves
~150 LoC after netting out the descriptor + first generic, also in
line with L1.

## Final structure

What's added:

* `BoolIntBinOpDesc` — 3-field structure (`opName : String`,
  `opId : Expr.Identifier`, `outTy : Ty`).
* 12 descriptor literals (`BoolIntBinOpDesc.intAdd` through
  `.boolImplies`), one line each.
* `binOp_translated_of_corr` — generic per-op `_translated` lemma
  (~17 LoC including signature).
* `isBoolIntTranslated_of_toGotoExprCtx_binOp` — generic bridge helper
  (~60 LoC including signature).

What's removed:

* 12 `<op>_translated` theorems (intAdd, intSub, intMul, intDivT,
  intModT, intLt, intLe, intGt, intGe, boolAnd, boolOr, boolImplies),
  each ~12 LoC including signatures.
* 12 `isBoolIntTranslated_of_toGotoExprCtx_<op>` helpers, each
  ~60-66 LoC.
* Stale section header `Per-operator binary integer ops` (replaced).
* Dead `op_id_ne_funApp_unary` (pre-existing, never referenced).

## What stayed put

* `intConst_translated`, `boolConst_translated`, `fvar_translated`
  — non-operator shapes, hand-rolled proofs.
* `boolNot_translated` and `isBoolIntTranslated_of_toGotoExprCtx_boolNot`
  — unary, would need a separate `BoolIntUnaryOpDesc`. Out of scope per
  L1's verdict.
* `ite_translated` and `isBoolIntTranslated_of_toGotoExprCtx_ite` —
  ternary, completely different shape.
* `eq_translated` and `isBoolIntTranslated_of_toGotoExprCtx_eq` —
  uses `LExpr.eq` constructor, not `LExpr.app … (LExpr.op …)`.
* `BoolIntOpHypotheses` (the 23-field bundle) — untouched. The
  per-op `<op>_corr` fields are still consumed individually.

## Notes on the dispatch refactor

The per-op invocation in `toGotoExprCtx_preservesEval_boolInt` is
slightly more verbose than L1 sketched: each case threads the
descriptor, the four side-conditions, the constructor lambda, and the
operator-specific `h_op_gty` proof. That's ~7-9 LoC per case (vs.
L1's "one line"). The verbosity is real, but per-op savings still
amount to ~57 LoC each (66-line bridge helper deleted vs. 8-line
dispatch addition).

The `mk` parameter is exactly the load-bearing complexity L1 flagged:
each invocation supplies a 1-line `(fun _ _ _ _ _ _ _ ih1 ih2 =>
.<op> _ _ _ _ _ _ _ ih1 ih2)`. Can't be deduplicated because
`IsBoolIntTranslated`'s 12 binary constructors hardcode the operator
name in their conclusion's `LExpr` pattern.

The `(by decide)` for `(od.opName == "old") = false` works because
each descriptor literal has a closed `String` for `opName`; Lean
decides this automatically. (L1 used `from rfl` for the same shape
when the string was literal-baked-in; either works.)

## Deviations from L1's design

Minor:

* L1 sketched `h_corr` as a 9-arg `∀ σ m₁ m₂ ty e1c e2c e1g e2g v` in
  `binOp_translated_of_corr`. We took the `m₁ m₂ ty e1c e2c e1g e2g`
  arguments out of the universal quantifier and into theorem
  arguments, leaving only `∀ σ v` quantified inside `h_corr`. This
  matches the way callers consume `h.<op>_corr σ m₁ m₂ ty …` — the
  per-op fields of `BoolIntOpHypotheses` are likewise universally
  quantified over `σ` and `v` only. Cleaner threading, identical
  power.

* L1's bridge generic took `h_frag` (the parent fragment hypothesis)
  and derived `h_frag1`/`h_frag2` inside. We push that derivation up
  to the dispatch site (where it was already happening pre-refactor,
  via `h_frag_split`). The generic now takes `h_frag1 h_frag2`
  directly, which simplifies its signature.

Otherwise: the descriptor, the four side-conditions, and the `mk`
constructor parameter are exactly as L1 designed.

## Process record

Three substantive commits on `worktree-agent-aa21c1e3d028f0a0a`:

1. `feat(goto-correct): L4 step 1 — add BoolIntBinOpDesc + 2 generics + intAdd PoC` (+157/-30).
2. `feat(goto-correct): L4 step 2 — delete 12 binary _translated lemmas, dispatch via generic` (+24/-168).
3. `feat(goto-correct): L4 step 3 — delete 12 binary bridge helpers, dispatch via generic` (+81/-777).

Plus the stub-report commit at the start.

* `lake build` green at each commit (201/201, 585/585 on full build).
* Axiom test (`#print axioms` on `_v6`/`_v7`) still prints
  `[propext, Classical.choice, Quot.sound]`. (Run via a temporary
  `StrataTest/Backends/CBMC/GOTO/L4OpDescAxioms.lean` file, deleted
  before the final commit per scope-discipline.)
* No `sorry`. No new `axiom`. No `git push`. No changes outside
  `ExprTranslationPreservesEvalBoolInt.lean` and this report.

## Tier verdict — Tier 1

Matched L1's projection (claimed ~600-800 LoC, delivered 719 LoC).
The aggressive path proved fully feasible: every binary operator's
per-op wrapper and bridge helper was deletable since all consumers are
in-file. The two generics absorb ~80 LoC of fixed overhead, easily
amortised across 12 operators.

The `mk` parameter was exactly as awkward as L1 warned, but it
remains a 1-line lambda at each call site and didn't force any
inductive restructuring. No operator failed to fit the descriptor.

## Future work suggestions (not done here)

* **Unary OpDesc for `boolNot`**: would save ~30 LoC if landed.
  Marginal return (one operator) and a separate generic (different
  fragment-extraction, different translator path with `parseBvExtractLo`).
* **`ite` and `eq`**: not abstraction-shaped. Leave as hand-written.
* **`BoolIntOpHypotheses` 23-field collapse**: the audit (§3.3)
  flagged this as a Tier-2 follow-up. Would save ~140 LoC but changes
  the user-facing interface for hypothesis-bundle discharge. Not
  obviously a win.
* **`FnToGotoIDReductions` 26-field collapse**: same story; could be
  parameterised over `BoolIntBinOpDesc` (`fnToGotoID od.opName = .ok
  od.opId`) but changes the user-facing fields. Modest savings, real
  API churn.
