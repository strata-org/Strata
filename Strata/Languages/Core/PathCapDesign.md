# Path Cap: Between-Statement Merging (Option B)

## Problem

The current path cap implementation merges paths at two sites:
1. `processIteBranches` — merges same-exit-label groups
2. Block boundary — merges cross-exit-label paths after exit consumption

This relies on frontends (Boogie-to-Core, Laurel-to-Core) wrapping ITEs
with exits inside labeled blocks. Without blocks, sequential ITEs
accumulate paths exponentially. The block-boundary convention is an
implicit contract, not a structural guarantee.

## Proposal

Replace the two-site design with a single merge site: **between
statements**, in `evalAuxGo`'s continuation fold. After any statement
produces `EAndNexts` and before the fold feeds them to the remaining
statements (StatementEval.lean, after line 643), enforce the cap.

### Algorithm

```
EAndNexts := result of evaluating the current statement

if pathCap is active:
  let (noExit, hasExit) := EAndNexts.partition (exitLabel == .none)
  if noExit.length > cap:
    noExit := mergeCondPairs noExit.length noExit
  EAndNexts := noExit ++ hasExit

fold EAndNexts through remaining statements (existing logic)
```

### Why only merge `.none` paths

- Paths with `exitLabel = .some l` skip all remaining statements via
  `processExit` (line 397). They pass through the fold untouched and
  propagate up to the enclosing block. They don't contribute to
  exponential explosion because they don't enter nested ITEs.

- Paths with `exitLabel = .none` all continue to the same next
  statement. Merging them is safe: they share the same control flow
  continuation, and `Env.merge` wraps their state in `ite(cond, ...)`
  with `splitConds` providing the precise condition.

- Exiting paths accumulate at most linearly (one per ITE that has an
  exit branch), not exponentially. They're collected at the block
  boundary by the existing exit-label consumption logic (lines 550-558)
  and merged at procedure end by `mergeResults` (ProcedureEval.lean:49).

### Why this subsumes block-boundary merging

The block-boundary merge exists because paths that exit a block and
paths that fall through have different exit labels during evaluation.
They only reconverge after the block consumes the exit labels. With
between-statement merging, the `.none` paths are merged *before* each
subsequent ITE, so they never multiply. The exiting paths pass through
untouched and are consumed by the block as before. The net effect is the
same: the block produces a bounded number of paths.

### Changes

1. **StatementEval.lean** (line 643): Add cap enforcement on `EAndNexts`
   before the continuation fold, partitioning by exit label and merging
   only `.none` paths. Add `betweenStmt_capMerged` stat increment.

2. **StatementEval.lean** (block case, lines ~566-574): Remove the
   `match Ewn.env.pathCap` block-boundary merge logic. Blocks go back
   to pure scope/exit-label management.

3. **StatementEval.lean** (`processIteBranches`): Keep the existing
   same-exit-label merge for the common case (both branches produce one
   result with same exit label). Remove the `capMerged` path — the
   between-statement merge handles it. `processIteBranches` still tags
   `splitConds` when `pathCap` is active and paths diverge.

4. **Statistics.lean**: Remove `blockBoundary_capMerged`. Add
   `betweenStmt_capMerged`. Keep `processIteBranches_capMerged` or
   remove it if the same-exit-label merge in `processIteBranches` is
   also removed in favor of between-statement handling.

5. **Options.lean**: Update `pathCap` docstring to document the single
   merge site.

6. **Tests**: Update stats expectations. Add a test with sequential
   ITEs *without* blocks (the case the old design couldn't handle).

### What stays the same

- `pathCap : Option Nat` on `VerifyOptions` and `Env`
- `splitConds` on `EnvWithNext` — still needed for `mergeCondPairs`
- `condEq` with `eraseMetadata.eraseTypes`
- `mergeCondPairs`, `findCondPairs`, `extractMatchingTrue` helpers
- `groupByExitLabel` — may still be useful but no longer needed at the
  block boundary
- The continuation fold itself (lines 644-648) — unchanged
- Termination: `mergeCondPairs` is outside the `mutual` block, so
  calling it before the fold has no impact

### Tradeoffs

- **Simpler**: one merge site vs. two, no frontend convention dependency
- **Same VC quality**: `.none` paths are merged with the same
  `ite(cond, ...)` wrapping as before
- **Open question**: if a program has many ITEs where one branch exits
  and the other continues, the exiting paths accumulate linearly (not
  exponentially). With N such ITEs, there are N+1 paths at the block
  boundary. If this is a concern, the cap could also be enforced on
  exiting paths at the block boundary as a follow-up. But linear
  accumulation is acceptable for practical programs.

### TODO

Add a test demonstrating the linear accumulation of exiting paths:
a single block with N ITEs where each true branch exits. This produces
N+1 paths at the block boundary (1 fallthrough + N exiting). Verify
that between-statement merging keeps the fallthrough to 1 path but the
exiting paths accumulate. If N+1 becomes a practical problem, revisit
adding a block-boundary merge for exiting paths.
