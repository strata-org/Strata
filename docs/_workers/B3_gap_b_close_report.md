# Worker B3 — Gap B Close Report

Round: 3
Status: in progress
Started: 2026-05-21

## Goal

Bridge `LExpr.toGotoExprCtx` to `IsBoolIntTranslated` for app/op/ite
cases, then prove the top-level theorem
`toGotoExprCtx_preservesEval_boolInt`.

## Plan

1. Read `B2_gap_b_finish_report.md` and the live file
   `ExprTranslationPreservesEvalBoolInt.lean` to understand:
   - Existing helpers `_const`, `_fvar`, `_eq`.
   - The `FnToGotoIDReductions` bundle B2 left.
   - `IsBoolIntTranslated` constructor parameter shapes.
   - Translator `LExpr.toGotoExprCtx` for `app`/`op`/`ite`.
2. Write per-operator helpers, building up complexity:
   - Binary integer ops (intAdd, intSub, intMul, intLt, intLe, intGt,
     intGe, intDivT, intModT) — same skeleton modulo
     `h_op_gty : ... = .ok .Integer` and the `IsBoolIntTranslated`
     constructor.
   - Boolean ops (boolNot, boolAnd, boolOr, boolImplies).
   - `ite`.
3. Top-level dispatcher: pattern match on the LExpr shape, recurse,
   feed each operator helper.
4. Commit progress per operator/group.

## Status — DELIVERY: BEST TIER

- [x] Read context (B2 report, live file, translator).
- [x] Stub helper for intAdd. **Build green.**
- [x] Other binary integer ops (intSub, intMul, intDivT, intModT,
      intLt, intLe, intGt, intGe). **Build green.**
- [x] Boolean ops (boolNot, boolAnd, boolOr, boolImplies).
      **Build green.**
- [x] Top-level theorem `toGotoExprCtx_preservesEval_boolInt`.
      **Build green.** Uses well-founded recursion via
      `termination_by sizeOf e_core`.
- [x] **ite** — extended `isBoolIntFragment`, `BoolIntGtyAgrees`,
      `IsBoolIntTranslated`, `BoolIntOpHypotheses` (new
      `ite_corr` field), `ite_translated` per-op lemma, bridge
      helper, and top-level dispatch. **Build green.**

All deliverables in the brief's "Best" tier are closed. `lake build`
green for all 585 jobs. No `sorry` introduced.

## Findings

- Worktree was on `worktree-agent-a7b855f6f1fe92f60` at `e9d0f83d8`
  (older code lacking `ExprTranslationPreservesEvalBoolInt.lean`).
  Reset locally to `htd/unstructured-to-goto` tip
  (`d34adcbb7 docs(workers): round-2 supervisor report`).

## Architectural decisions

### `op_id_ne_funApp_*` helpers

The translator binary path has three `if op == .functionApplication
"<sentinel>"` checks (Euclidean div, Euclidean mod, SDivOverflow).
For our supported ops, `op` is `.multiary _` / `.binary _` / `.unary
_`, so these comparisons are always `false`. We factor this into
three helper lemmas (one per outer constructor) — they discharge the
inequality via `simp only [BEq.beq, decide_eq_false_iff_not]; intro
h; cases h`. This pattern works because `Identifier`'s `BEq` is
derived from `DecidableEq` via the global `instBEqOfDecidableEq`.

### `BoolIntGtyAgrees` recursive predicate

The `IsBoolIntTranslated` constructors hardcode `.Integer` /
`.Boolean` in their GOTO output. The translator computes
`gty := mty.destructArrow.getLast!.toGotoType` from the operator's
type annotation. To bridge between the two, we take a recursive
`Prop`-valued predicate `BoolIntGtyAgrees` that asserts the gty
agreement at each operator subterm. This parallels
`isBoolIntFragment` (the syntactic fragment check) and is supplied
by the user alongside the fragment hypothesis.

For binary integer arithmetic (Add/Sub/Mul/DivT/ModT) the predicate
asserts `mty.destructArrow.getLast!.toGotoType = .ok .Integer`; for
binary integer comparison (Lt/Le/Gt/Ge) and for boolean binary/unary
ops the assertion is `.ok .Boolean`. For LExpr.eq / LExpr.ite there
is no per-op gty constraint (the eq constructor hardcodes `.Boolean`
unconditionally; ite uses `tg.type` directly).

### Top-level uses well-founded recursion (`sizeOf`)

`induction e_core` on LExpr produces IHs for `app m fn arg` of type
"about `fn`" and "about `arg`" — but our binary case requires IHs on
`e1c` and `e2c`, which live *inside* `fn = .app m_inner (.op _ _ _)
e1c`. To reach those, we structure the proof via
`match e_core, h_gty, h_frag, h_tx` with explicit recursive calls to
`toGotoExprCtx_preservesEval_boolInt` on subexpressions. Lean checks
termination via `termination_by sizeOf e_core`; the
`decreasing_by simp_wf; omega` discharges all the recursive calls.

### `ite` constructor uses `Expr.ite cg tg eg`

Initially we tried `⟨.ternary .ite, tg.type, [cg, tg, eg], .nil, []⟩`
in the constructor. The translator returns `Expr.ite cg tg eg`, and
since `Expr.ite` is *not* `@[expose]` the elaborator cannot reduce
between the two forms. Switching the constructor (and `ite_corr` /
`ite_translated`) to use `Expr.ite cg tg eg` directly aligns the
shape with the translator output.

## Files changed

| File | Change |
|---|---|
| `Strata/Backends/CBMC/GOTO/ExprTranslationPreservesEvalBoolInt.lean` | +850 lines (1048 → 1898). |
| `docs/_workers/B3_gap_b_close_report.md` | new (this file). |

## Verification

- `lake build` succeeds (585 jobs, no warnings on this file).
- `grep -n 'sorry\b'` in the file returns nothing.
- All commits build green individually.

## Commits (in order)

1. `f391aa9f3` docs(B3): report stub for Gap B close round 3
2. `9841bd8eb` feat(goto-correct): B3 - bridge helper for Int.Add op
3. `72b81b569` feat(goto-correct): B3 - bridge helpers for all binary integer ops
4. `d3b3d71f8` feat(goto-correct): B3 - bridge helpers for boolean ops
5. `4a405e415` feat(goto-correct): B3 - top-level toGotoExprCtx_preservesEval_boolInt
6. `c4c986ed5` docs(B3): top-level theorem closed; ite remains as stretch goal
7. `a19bce8c8` feat(goto-correct): B3 - ite bridge helper + extend fragment/predicate
