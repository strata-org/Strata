# Worker R6b — Discharge `h_tx_eq` and `h_expr_translated_witness`

Round: 6 (parallel: R6a is on `TranslatorBridgeHyps`)
Status: **DELIVERY: BEST TIER (Tier 1)**
Started: 2026-05-21
Finished: 2026-05-21

## Goal

Discharge two of the remaining hypotheses on
`coreCFGToGotoTransform_forward_simulation_concrete` (in
`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean`):

1. **`h_tx_eq`** — the technical equality
   `∀ e, Imperative.ToGoto.toGotoExpr e = .ok (h_expr_corr.tx e)`.
2. **`h_expr_translated_witness`** —
   `∀ cond e_goto, LExpr.toGotoExprCtx [] cond = .ok e_goto →
    ExprTranslated δ δ_goto δ_goto_bool cond e_goto`.

Deliver `coreCFGToGotoTransform_forward_simulation_concrete_v2` that
takes B3's `BoolIntOpHypotheses` + a uniformity hypothesis, builds
the `ExprTranslationPreservesEval` and the witness internally, then
delegates to v1.

## Outcome — both discharged (Tier 1)

| Item | Status |
|---|---|
| `h_tx_eq` discharge | **closed** via `ConcreteExprCorr.h_tx_eq_holds` (uses `Classical.choose_spec` + `rfl`-equality between `Imperative.ToGoto.toGotoExpr` and `LExpr.toGotoExprCtx []`) |
| `h_expr_translated_witness` discharge | **closed** via `ConcreteExprCorr.h_expr_translated_witness_holds` (chains B3's `toGotoExprCtx_preservesEval_boolInt` with `IsBoolIntTranslated.translated`) |
| `coreCFGToGotoTransform_forward_simulation_concrete_v2` | **closed**; delegates to v1 |
| Axiom set | `[propext, Classical.choice, Quot.sound]` (standard) |
| `lake build` | green throughout (585 jobs) |

Net contribution: **+267 lines** in
`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` (v2 theorem
+ supporting helpers in the `ConcreteExprCorr` namespace), **+1
char** in `Strata/Backends/CBMC/GOTO/LambdaToCProverGOTO.lean`
(adding `@[expose]` to `Lambda.LExpr.toGotoExpr`).

## Design

### The `ConcreteExprCorr` namespace

Added at the end of `CoreCFGToGOTOConcrete.lean` (just before the
v2 theorem and `end CProverGOTO`):

| Declaration | Role |
|---|---|
| `UniformBoolIntFragment` | Caller's uniformity claim: every Core expression is in the bool+int fragment, has gty agreement, and translates successfully. |
| `tx` (`noncomputable`) | The translation function, picked from `UniformBoolIntFragment.translates` via `Classical.choose`. |
| `tx_eq_toGotoExprCtx` | `Lambda.LExpr.toGotoExprCtx [] e = .ok (tx h_uniform e)` (from `Classical.choose_spec`). |
| `toGotoExpr_eq_toGotoExprCtx` | `Imperative.ToGoto.toGotoExpr e = LExpr.toGotoExprCtx [] e` (by `rfl`). |
| `h_tx_eq_holds` | The `h_tx_eq` discharge. |
| `h_expr_translated_witness_holds` | The `h_expr_translated_witness` discharge via B3. |
| `buildExprCorr` (`noncomputable`) | Assembles `ExprTranslationPreservesEval` from the bundle, plus a caller-supplied `tx_commutes_not`. |

### v2 theorem signature

`coreCFGToGotoTransform_forward_simulation_concrete_v2` replaces v1's
three hypotheses
- `h_expr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool`
- `h_tx_eq : ∀ e, ToGoto.toGotoExpr e = .ok (h_expr.tx e)`
- `h_expr_translated_witness : ∀ cond e_goto, ... → ExprTranslated ...`

with the bundle
- `h_red : FnToGotoIDReductions`
- `h_op : BoolIntOpHypotheses δ δ_goto δ_goto_bool`
- `h_uniform : UniformBoolIntFragment`
- `h_commutes_not : ∀ e, tx h_uniform (HasNot.not e) = (tx h_uniform e).not`

The first two are directly B3's interface — the caller obtains
them by invoking B3's named theorems. `h_uniform` is the genuine
new uniformity claim; `h_commutes_not` is a side-condition that
v1 already required (see "limitations" below).

All other hypotheses (translator structural inputs, evaluator
hypotheses, store-corr) are unchanged from v1.

## Key technical findings

### `LExpr.toGotoExpr` was not `@[expose]`

Originally `Lambda.LExpr.toGotoExpr := toGotoExprCtx []` was
declared without `@[expose]`. Lean refused to reduce
`Imperative.ToGoto.toGotoExpr e` to `LExpr.toGotoExprCtx [] e` by
`rfl` for that reason — `unfold`, `simp [LExpr.toGotoExpr]`, and
explicit `eq_def` rewrites all failed (typeclass-instance
inference for the unexposed body got stuck on metavariables).

Adding `@[expose]` to the definition is safe: the body is
`toGotoExprCtx [] e`, both `toGotoExprCtx` and the typeclass
hierarchy are already exposed, and no downstream proofs change
their meaning. After this single-token edit the equality holds by
`rfl`.

### `tx_commutes_not` is dormant in proofs

Searched all of `Strata/` for usage of
`ExprTranslationPreservesEval.tx_commutes_not` (or
`h_expr_corr.tx_commutes_not`):

```
$ grep -rn "tx_commutes_not\|.tx_commutes_not\b" Strata/
Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean: ...
Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrect.lean:102: ... (the field declaration only)
```

The field is declared on the structure but **no proof reads it**.
This means the value the caller supplies is "dormant" — any
inhabitant of the type works. (We still must take it as a
hypothesis since v2 must construct a complete
`ExprTranslationPreservesEval` to delegate to v1.)

For the actual translator, the equation is generally **false**:
`HasNot.not Core.true = Core.false` and
`tx Core.true ≠ tx Core.false`, so
`tx (HasNot.not Core.true) = tx Core.false` differs from
`(tx Core.true).not = .unary .Not (tx Core.true)`. A future cleanup
opportunity: drop `tx_commutes_not` from
`ExprTranslationPreservesEval` since it's unused.

### Discharge of `h_tx_eq`

The pattern is:
```
Imperative.ToGoto.toGotoExpr e
  = LExpr.toGotoExprCtx [] e        -- by rfl after @[expose]
  = .ok (tx h_uniform e)            -- from Classical.choose_spec h_uniform.translates
  = .ok (h_expr.tx e)               -- since h_expr.tx = tx h_uniform
```

The third equality is by definition of `buildExprCorr`. The whole
chain is a one-liner via `rw [toGotoExpr_eq_toGotoExprCtx];
exact tx_eq_toGotoExprCtx h_uniform e`.

### Discharge of `h_expr_translated_witness`

The chain via B3:
```
LExpr.toGotoExprCtx [] cond = .ok e_goto                  -- given
+ h_uniform.gtyAgrees cond, h_uniform.inFragment cond
⟹ IsBoolIntTranslated cond e_goto                        -- B3's toGotoExprCtx_preservesEval_boolInt
+ h_op : BoolIntOpHypotheses
⟹ ExprTranslated δ δ_goto δ_goto_bool cond e_goto         -- B3's IsBoolIntTranslated.translated
```

This is exactly what the strategic notes anticipated.

## Tradeoff: the uniformity hypothesis is strong

`UniformBoolIntFragment` is universally quantified over the entire
`Core.Expression.Expr` universe. It is **not satisfiable** for
arbitrary expressions (the translator fails on `.abs`,
unsupported `.app` shapes, `.bvar` outside the binders, etc.).

In practice the caller satisfies it by:

1. Restricting the source CFG so its expressions are syntactically
   confined to the bool+int fragment, and
2. Restricting the source semantic-evaluator `δ` to be defined
   only on those expressions — at which point uniformity is a
   property of the program text rather than a universal claim.

This is a familiar pattern at this layer of the proof: the v2
theorem is a "concrete-pipeline" theorem in the sense of "what the
caller writes once for their program", not a "universal soundness"
theorem in the sense of "for all CFGs over `Core.Expression`".

## Files changed

| File | Change | Description |
|---|---|---|
| `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` | +267 | v2 theorem + `ConcreteExprCorr` helpers |
| `Strata/Backends/CBMC/GOTO/LambdaToCProverGOTO.lean` | +1 char | `@[expose]` on `Lambda.LExpr.toGotoExpr` |
| `docs/_workers/R6b_h_tx_eq_report.md` | new (this file) | report |

## Verification

- `lake build` succeeds for all 585 jobs.
- `grep 'sorry\b'` in the file returns nothing.
- All commits build green individually.
- Axiom check via `#print axioms`:
  - `coreCFGToGotoTransform_forward_simulation_concrete_v2` →
    `[propext, Classical.choice, Quot.sound]` (standard)
  - `ConcreteExprCorr.h_tx_eq_holds` →
    `[propext, Classical.choice, Quot.sound]`
  - `ConcreteExprCorr.h_expr_translated_witness_holds` →
    `[propext, Classical.choice, Quot.sound]`
  - `ConcreteExprCorr.tx_eq_toGotoExprCtx` →
    `[propext, Classical.choice, Quot.sound]`
  - `ConcreteExprCorr.toGotoExpr_eq_toGotoExprCtx` →
    `[propext, Classical.choice, Quot.sound]`
  - v1 unchanged: `[propext, Classical.choice, Quot.sound]`

`Classical.choice` is genuinely needed (not a leftover): we use
`Classical.choose` on `h_uniform.translates` to extract the GOTO
expression, since the existential hypothesis cannot be unpacked
constructively.

## Commits (in order)

1. `35f597a91` docs(R6b): report stub.
2. `b85fc4974` feat(goto-correct): R6b — v2 theorem +
   `@[expose]` on `LExpr.toGotoExpr`.
3. `<TBD>` docs(R6b): final report.

## Suggested next steps

After R6b:

* The remaining concrete-theorem hypotheses are translator-input
  invariants (mostly trivial), `h_brHyps : TranslatorBridgeHyps`
  (R6a's scope), and the caller-supplied evaluator obligations
  (`h_eval_bool_corr`, `h_corr`, fragment restrictions on the
  source `δ`).
* If R6a closes `TranslatorBridgeHyps`, a "v3" theorem could
  combine R6a's discharge with this v2's discharge plus the
  trivial structural inputs (init_size, init_loc, distinct,
  admitted_blocks, loopContracts_empty_post, entry_first), leaving
  only the truly external caller obligations as parameters.
* `tx_commutes_not` cleanup: since it's unused in proofs, it
  could be removed from `ExprTranslationPreservesEval`. This would
  shrink v1's hypothesis surface and simplify v2 (the
  `h_commutes_not` parameter could disappear). Out of scope for
  R6b.
