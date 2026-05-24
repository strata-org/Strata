# Worker L4 — OpDesc full refactor (aggressive path)

**Branch base:** `htd/unstructured-to-goto`
**Target file:** `Strata/Backends/CBMC/GOTO/ExprTranslationPreservesEvalBoolInt.lean` (baseline 2246 LoC).
**Reference:** `docs/_workers/L1_opdesc_smoke_test.md` (smoke-test feasibility study).

## Plan (stub)

Apply L1's Tier-2 aggressive path. Convert all 12 binary
arithmetic-ish operators (`Int.{Add,Sub,Mul,DivT,ModT,Lt,Le,Gt,Ge}` +
`Bool.{And,Or,Implies}`) to use a `BoolIntBinOpDesc` descriptor +
two generic theorems:

* `binOp_translated_of_corr` (replaces 12 `<op>_translated` theorems)
* `isBoolIntTranslated_of_toGotoExprCtx_binOp` (replaces 12 bridge
  helpers).

The 3 non-binary cases (`boolNot`, `ite`, `eq`/`const`/`fvar`) stay as
they are.

Expected savings: **~600-800 LoC** (file → ~1500 LoC).

## Process

1. Stub report (this file).
2. Add `BoolIntBinOpDesc` + 2 generic theorems + 12 descriptor
   literals.
3. Port operators to use generics; keep wrappers for now (pin build).
4. Inline generics into dispatch sites; delete wrappers.
5. Final report with actual LoC saved.

`lake build` green at every commit.
