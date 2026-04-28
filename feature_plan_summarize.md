# Feature Plan: Summary-Based Demand Analysis

## Motivation

The current `backwardCompound` in `Blockify.lean` computes per-block demands
in a single backward pass. This works well for acyclic constructs (if, try,
with), but loops (For, While) have a cyclic dependency: the header/test block's
demand depends on the body's liveness, but the body's sub-block demands depend
on the header's liveness as their `liveAfter`. The current workaround is to
traverse the body twice — once for liveness, once for demands.

For non-nested loops this is fine. But nested loops multiply the cost: each
outer loop's body traversal re-traverses inner loops, leading to O(depth *
body_size) work in the worst case.

## Proposed Design

Replace the current approach with two stages:

1. **Summarize** — Single forward-or-backward AST walk. For each block, record
   a compact summary (defs, reads, edges). No `liveAfter` parameter needed.

2. **Solve** — Iterative fixpoint over the block summaries to compute actual
   demands. Standard backward liveness analysis handles cycles naturally.

The existing `backward*` functions remain as-is for now. The new `summarize*`
functions are added alongside, producing `Array BlockSummary` that gets resolved
by `solveDemands`. Once validated, the old functions can be removed.

## Data Structures

```lean
/-- Per-block summary collected during AST traversal. -/
structure BlockSummary where
  /-- Variables definitely assigned (killed) in this block. -/
  defs : Std.HashSet String
  /-- Variables read (generated) in this block — upward-exposed uses. -/
  reads : Std.HashSet String
  /-- Block indices this block can branch to. -/
  successors : Array Nat
```

The summary array is indexed the same way as the current `DemandArr`: entry `i`
corresponds to block `i` (in allocation order). Block 0 is always the entry
block.

## Fixpoint Solver

Standard backward liveness with worklist:

```
liveIn(B)  = reads(B) ∪ (liveOut(B) \ defs(B))
liveOut(B) = ∪ { liveIn(S) | S ∈ successors(B) }
```

Initialize `liveIn(B) = reads(B)` for all B. Add all blocks to worklist.
Process in reverse postorder for fast convergence. Iterate until no `liveIn`
changes.

For acyclic subgraphs, one reverse-postorder pass suffices. Loops typically
converge in 2–3 iterations over just the loop blocks.

Output: `Array DemandVars` where `result[i]` = sorted variable names needed
by block `i` — same format as the current `demandAnalysis` return type.

## Summarize Functions

Mirror the structure of the current `backward*` functions but without
`liveAfter` threading:

```lean
/-- Collect block summaries for a statement array.
    Returns (reads, updatedSummaries) where reads = variables read by the
    statement sequence (needed for the parent block's reads set). -/
partial def summarizeStmts (stmts : Array (stmt SourceRange))
    (summaries : Array BlockSummary)
    : Std.HashSet String × Array BlockSummary

/-- Collect block summaries for a compound statement. -/
partial def summarizeCompound (s : stmt SourceRange)
    (summaries : Array BlockSummary)
    : Std.HashSet String × Array BlockSummary

/-- Collect block summaries for expression sub-blocks (BoolOp, IfExp,
    chained Compare). Also returns free variables of the expression. -/
partial def summarizeExprBlocks (e : expr SourceRange)
    (fv : Std.HashSet String) (summaries : Array BlockSummary)
    : Std.HashSet String × Array BlockSummary
```

### Key simplifications vs current backward* functions

- **No `liveAfter` parameter.** Each function only needs to record what the
  block itself reads and defines, plus its edges. The solver handles propagation.

- **Loops are single-pass.** For/While just summarize the body once, record
  the back-edge in `successors`, and move on. No double traversal.

- **Expression blocks are trivial.** BoolOp/IfExp/Compare sub-blocks have
  `defs = {}` and `reads = {free vars of their sub-expression}`. The cumulative
  demand logic (the merged reverse loops) goes away — the solver handles it.

- **No special FV accumulator.** The current `backwardExprBlocks` threads both
  `fv` and `da` because it computes demands inline. `summarizeExprBlocks` still
  collects FV (needed for the parent block's `reads`), but the block summaries
  replace DA — simpler return type.

## Successor Edges by Construct

| Construct | Blocks allocated | Successor edges |
|-----------|-----------------|-----------------|
| If | then, else, join | current→then, current→else, then→join, else→join |
| For | iterInit, header, end | current→iterInit, iterInit→header, header→body[0], header→end, body[last]→header (back-edge), orelse[last]→end |
| While | test, body, end | current→test, test→body[0], test→end, body[last]→test (back-edge), orelse[last]→end |
| Try | handlers[], join, finally?, reraise? | body→handler (exception edge), body→orelse, orelse→join/finally, handler→join/finally, finally→join |
| With | enter, excExit, normalExit, reraise | current→enter, enter→body[0], body→normalExit (normal), body→excExit (exception), excExit→reraise or normalExit |
| BoolOp | eval[1..n-1], join | current→eval[1] or join, eval[i]→eval[i+1] or join |
| IfExp | then, else, join | current→then or else, then→join, else→join |
| Compare | eval[1..n-1], join | current→eval[1] or join, eval[i]→eval[i+1] or join |

Note: "current" means the block that contains the statement/expression. Its
successors are set by the caller, not by the summarize function itself. The
summarize function pushes summaries for the *new* blocks only.

## Block Summary Ordering

Summaries are pushed in the same order as the current `DemandArr` — reverse
allocation order. The solver doesn't care about push order since it uses
explicit successor indices, but maintaining the same order means the existing
block-ID arithmetic in PythonToSSA.lean doesn't change.

Actually, since the solver uses explicit edges, the summaries could be pushed
in *any* order as long as the indices are consistent. Forward (allocation)
order is more natural for a single-pass collection. Worth considering whether
to switch from reverse to forward order.

## Integration

```lean
/-- Demand analysis using block summaries + fixpoint solver.
    Drop-in replacement for the current demandAnalysis. -/
public def demandAnalysis2 (stmts : Array (stmt SourceRange))
    (globals : Std.HashSet String := {})
    : Array DemandVars :=
  let summaries := (summarizeStmts stmts #[]).2
  let demands := solveDemands summaries
  -- demands[0] = entry block (always empty)
  if globals.isEmpty then demands
  else demands.map fun dv => dv.filter (!globals.contains ·)
```

PythonToSSA.lean calls `demandAnalysis2` instead of `demandAnalysis` — same
return type, same semantics. Can be swapped with a one-line change.

## Verification Plan

1. Implement `summarizeStmts` / `summarizeCompound` / `summarizeExprBlocks`
2. Implement `solveDemands` (fixpoint solver)
3. Wire up as `demandAnalysis2`
4. Compare output of `demandAnalysis` vs `demandAnalysis2` on all 33 tests
5. Once outputs match, run full SSA test suite with `demandAnalysis2`
6. Remove old `backward*` functions and rename

## Resolved Questions

- **Defs for expression blocks**: `defs = {}` — defs/reads are about
  Python-level variable names, not SSA values. The `fwd` mechanism in
  PythonToSSA handles expression-stack threading independently of variables.

- **Break/Continue edges**: Pass loop targets (break → endBlock, continue →
  headerBlock/testBlock) as parameters to the summarize functions. Matches
  the current backward function structure.

- **Exception edges**: Every block inside a try body has the handler block as
  a successor. The summarize function receives the handler block index as
  context.

## Block ID Ordering

The summarize pass uses **internal indices** for edges — pre-allocated per
construct before recursing into bodies. Each construct's fixed blocks are
allocated upfront (e.g., while allocates test, body, end before processing
the body). These indices may be out of program-text order (endBlock gets
a lower index than the body's internal blocks).

This is fine because:

1. The **fixpoint solver** doesn't care about index order — it uses explicit
   successor edges.

2. **Phase 2 (PythonToSSA)** assigns actual `BlockId` values sequentially
   during DFS emission. Since it processes blocks in program order (body
   before endBlock), endBlock naturally gets an ID after all body blocks.

3. The demand array lines up because both the summarize pass and Phase 2
   traverse the same AST with the same construct-level block pattern.
   `demands[i]` corresponds to the i-th block Phase 2 encounters. Phase 2
   consumes entries via a counter (`demandIdx`) as it starts each block.

In short: internal summary indices are an implementation detail of the solver.
Program-order block IDs are Phase 2's responsibility — they fall out naturally
from DFS emission order.
