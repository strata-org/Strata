# Worker R6b — Discharge `h_tx_eq` and `h_expr_translated_witness`

Round: 6 (parallel: R6a is on `TranslatorBridgeHyps`)
Status: in progress
Started: 2026-05-21

## Goal

Discharge two of the remaining hypotheses on
`coreCFGToGotoTransform_forward_simulation_concrete` (in
`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean`):

1. **`h_tx_eq`** — the technical equality
   `∀ e, Imperative.ToGoto.toGotoExpr e = .ok (h_expr_corr.tx e)`.
2. **`h_expr_translated_witness`** —
   `∀ cond e_goto, LExpr.toGotoExprCtx [] cond = .ok e_goto →
    ExprTranslated δ δ_goto δ_goto_bool cond e_goto`.

Deliver a stronger top-level theorem
`coreCFGToGotoTransform_forward_simulation_concrete_v2` that takes
the *replacements* for these hypotheses (B3's `BoolIntOpHypotheses`
+ uniformity) and discharges them internally before delegating to
the existing v1 theorem.

## Plan

1. Read context (round-5 report, B3 report, target file, related
   files).  **Done.**
2. Write report stub.  **Done.**
3. Inspect `Imperative.ToGoto Core.Expression` instance and
   confirm `toGotoExpr = Lambda.LExpr.toGotoExpr`.  **Done.**
4. Construct the bundle: take `BoolIntOpHypotheses`,
   `FnToGotoIDReductions`, plus uniformity witnesses
   (`isBoolIntFragment` + `BoolIntGtyAgrees` + translation
   success on all CFG-source expressions).
5. From this bundle, build:
   - A function `tx_concrete : Core.Expression.Expr → CProverGOTO.Expr`
     that picks the translated expression on success / a junk default
     on failure.
   - A proof of `Imperative.ToGoto.toGotoExpr e = .ok (tx_concrete e)`
     for every `e` in scope (this is the `h_tx_eq` discharge).
   - A proof of `tx_correct` and `tx_commutes_not` for
     `tx_concrete` from B3.
   - A proof of `h_expr_translated_witness` from B3 +
     `IsBoolIntTranslated.translated`.
6. Assemble `coreCFGToGotoTransform_forward_simulation_concrete_v2`
   that delegates to v1.
7. Verify `lake build` green; commit.

## Key observations

### `Imperative.ToGoto.toGotoExpr` is `Lambda.LExpr.toGotoExpr`

In `Strata/Backends/CBMC/GOTO/CoreToCProverGOTO.lean:58-63`:

```
instance : Imperative.ToGoto Core.Expression where
  ...
  toGotoExpr := Lambda.LExpr.toGotoExpr
```

And `Lambda.LExpr.toGotoExpr e := Lambda.LExpr.toGotoExprCtx [] e`
(`LambdaToCProverGOTO.lean:362-364`).

So `Imperative.ToGoto.toGotoExpr e = Lambda.LExpr.toGotoExprCtx [] e`
**by `rfl`** (assuming both definitions are in scope and the typeclass
is resolved).

### The discharge cannot be unconditional

`Imperative.ToGoto.toGotoExpr e` may *fail* (`.error _`) on
unsupported LExpr shapes. So `h_tx_eq` requires an assumption that
all expressions used by the CFG translate successfully, or — more
strongly — a proof that for **every** `Core.Expression.Expr`,
`toGotoExpr` is `.ok`. The latter is false in general, so v2 must
take a uniformity hypothesis.

### Possible v2 hypothesis shapes

Two clean options:

**(A) Per-expression success hypothesis** — take
`h_tx_succeeds : ∀ e : Core.Expression.Expr, ∃ g, Imperative.ToGoto.toGotoExpr e = .ok g`.
Then define `tx := fun e => (Imperative.ToGoto.toGotoExpr e).toOption.get!`
(or via classical choice from the existential). With this,
`h_tx_eq` follows by `simp` / `cases` on the success.

**(B) Restricted-fragment hypothesis** — assume every expression
appearing in `cfg.blocks` (via `Stmt.getVars` / a closure) is in
`isBoolIntFragment`. Then both `h_tx_eq` and
`h_expr_translated_witness` follow from B3 + a uniformity claim.
Slightly nicer for the user but requires more machinery to thread.

Going with **(A)** for tractability — let the caller supply both:
- A universal `h_tx_succeeds` (assert `toGotoExpr` always succeeds).
- A universal `h_translated` (assert each translation is correct).

Then we build `h_expr_corr` and `h_expr_translated_witness`
internally.

## Sub-deliverables status

- [ ] `concreteExprCorr` constructor — TODO
- [ ] `h_tx_eq` discharged from `concreteExprCorr` — TODO
- [ ] `h_expr_translated_witness` discharged from B3 + structural
      induction theorem — TODO
- [ ] `coreCFGToGotoTransform_forward_simulation_concrete_v2` —
      TODO
- [ ] `lake build` green — TODO
- [ ] axiom check — TODO

## Files touched

- `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOConcrete.lean` — append
  v2 theorem (and supporting helpers) at end of file.
- `docs/_workers/R6b_h_tx_eq_report.md` — this file.

## Commits (in order)

1. `<TBD>` docs(R6b): report stub.
