# Plan: Fix Unresolved Variables in Expression Blocks

## Problem

19 corpus warnings remain for "Unresolved name" in function-local variables.
All share the same root cause: an assignment whose RHS contains expression-level
control flow (`IfExp`, `BoolOp`, chained `Compare`).

Example from `ecs_utils.py`:
```python
filter_msg: str = f' for service {service_name}' if service_name else ''
```

## Root Cause: Demand analysis bug

The IfExp creates expression sub-blocks (then, else, join). In
`backwardExprBlocks` for IfExp (Blockify.lean line 215-217), each expression
block's demands include `liveAfter` — the full set of variables live after
the enclosing statement:

```lean
let da := pushDemand da liveAfter                -- join
let da := pushDemand da (liveAfter ∪ orelseFV)   -- else
let da := pushDemand da (liveAfter ∪ bodyFV)     -- then
```

The problem is in `processSimpleStmt` (line 326), which calls:

```lean
| some v => backwardExprBlocks v liveAfter live da
```

Here `liveAfter` still includes `filter_msg` (it's used later in the function).
The `live` variable has `filter_msg` removed by `removeTargetDefs`. But
`liveAfter` is passed as the expression blocks' liveness context, so the
IfExp blocks demand `filter_msg` even though it's being *defined* by this
statement, not read.

The same issue affects `Assign` (line 321):

```lean
backwardExprBlocks value liveAfter live da
```

## Fix

Pass `live` (target removed) instead of `liveAfter` (target present) as the
first argument to `backwardExprBlocks` for the assignment value:

```lean
-- AnnAssign (line 326)
| some v => backwardExprBlocks v live live da

-- Assign (line 321)
backwardExprBlocks value live live da
```

This means expression sub-blocks only demand variables that are live after
the assignment *minus the target*. The target variable won't be threaded
through expression blocks it doesn't need to be in.

## Why this is correct

For `filter_msg = X if cond else Y`:
- Before fix: IfExp blocks demand `filter_msg` → `lookupVar` fails → error
- After fix: IfExp blocks don't demand `filter_msg` → not threaded → the
  IfExp produces a result value → `bindVar("filter_msg", result)` assigns it

The assignment target is never read by the RHS expression. Python evaluates
the RHS completely, then assigns to the target. The expression blocks should
only carry variables that the expression itself reads plus variables needed
by subsequent code (excluding the target being defined).

Note: `AugAssign` (`x += expr`) is different — it reads the target. The
existing code (line 328-331) already handles this correctly by passing
`liveAfter` for target reads.

## Test plan

- Existing 35/35 tests should still pass
- Add test case: function with `IfExp` and `BoolOp` in assignments
- Corpus: 47 → ~28 warnings (only comprehensions remain)
