# Worker B2 — Gap B finish report (round 2)

Status: **stalled** before completion; partial deliverable salvaged.

## Goal

Bridge `LExpr.toGotoExprCtx` → `IsBoolIntTranslated` for the
remaining LExpr cases (`app`, `op`, `ite`) and prove the top-level
theorem `toGotoExprCtx_preservesEval_boolInt`.

## What landed (committed and salvaged)

- `e540f130c` — report stub.
- `3f5eaf6c9` — `FnToGotoIDReductions` hypothesis bundle in
  `ExprTranslationPreservesEvalBoolInt.lean`. A 47-line `Prop`-valued
  structure listing the operator-name → GOTO-id reductions
  (`fnToGotoID "Int.Add" = .ok (.multiary .Plus)`, etc.) plus
  `isSignedBvOp = false` and `parseBvExtractLo = none` reductions
  for each supported operator. This is exactly the *missing
  hypothesis bundle* required to discharge the operator-name
  pattern matches inside `LExpr.toGotoExprCtx` for the bool+int
  fragment. **Builds clean.**

## What did not land (uncommitted experiments, discarded)

The worker was attempting to write the per-operator bridge helpers
(`isBoolIntTranslated_of_toGotoExprCtx_intAdd` etc.) when the
watchdog stalled. The uncommitted ~71-line attempt did *not* build
— the `simp only` invocations for unfolding
`fnToGotoID`/`isSignedBvOp` chains hit type-mismatch errors that
the worker was actively diagnosing when the stall happened.

The discarded approach was inlining `simp [fnToGotoID,
parseBvExtractLo, isSignedBvOp]` directly. The cleaner approach
(left to a future worker) is:

1. Take a `FnToGotoIDReductions` parameter and use *its* stated
   equalities as named rewrites instead of `simp` unfolding.
2. State each helper around the named bundle field
   (e.g. `h_red.intAdd`) rather than relying on `simp` to derive
   it.

That recipe is now possible because `FnToGotoIDReductions` exists
as a committed building block.

## Architectural notes preserved from the worker

Worker B's `IsBoolIntTranslated.intAdd` (and similar binary integer
ops) hard-code `.Integer` as the GOTO output type. The translator
computes `gty := ty.destructArrow.getLast!.toGotoType` from the
operator's type annotation, which in well-typed programs equals
`.ok .Integer` for `Int.Add` etc. but isn't guaranteed by
`isBoolIntFragment` alone.

Resolution proposed: each bridge helper takes a side hypothesis
`h_op_gty : ty.destructArrow.getLast!.toGotoType = .ok .Integer`
(or `.Boolean`) as an explicit argument. The top-level dispatcher
either strengthens the fragment to imply this, or accepts the
hypotheses as theorem inputs.

## Concrete next steps

To finish Item 2 (the original goal):

1. **Per-operator bridge helpers.** For each of intAdd / intSub /
   intMul / intDivT / intModT / intLt / intLe / intGt / intGe /
   boolNot / boolAnd / boolOr / boolImplies, write a private
   theorem `isBoolIntTranslated_of_toGotoExprCtx_<op>` that:
   - Takes a `FnToGotoIDReductions` parameter (now available).
   - Takes an `h_tx : LExpr.toGotoExprCtx [] <pattern> = .ok e_goto`.
   - Takes inductive hypotheses on the recursive sub-translations.
   - Takes a side hypothesis on the GOTO output type.
   - Concludes `IsBoolIntTranslated <pattern> e_goto`.

2. **`ite` bridge helper.** Similar shape; recursive on c, t, e.

3. **Top-level dispatcher** `toGotoExprCtx_preservesEval_boolInt`
   that case-splits on the LExpr shape and applies the appropriate
   helper.

Estimated remaining effort: ~150-300 LoC, *if* the
`FnToGotoIDReductions`-based recipe pans out cleanly.

## What the supervisor decided

The committed `FnToGotoIDReductions` bundle is genuinely useful
infrastructure regardless of whether the bridge gets finished —
any future worker on Item 2 will use it. So the partial output is
*kept* (merged into `htd/unstructured-to-goto`) and Item 2 is
re-classified as "scaffolded but unfinished" rather than rolled
back.
