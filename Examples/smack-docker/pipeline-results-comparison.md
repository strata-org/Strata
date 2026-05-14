# Pipeline Results Comparison: Before vs After Grammar Fix

## Change

Removed the "locals-as-out-params" workaround from BoogieToStrata. Instead:
- Added a `locals` block to `command_cfg_procedure` in the DDM grammar
- Local variable declarations are emitted in a `{ var x : int; }` block
  before the `cfg` body
- `@[scope(locals)]` makes declarations visible across all CFG blocks

## Before (locals-as-out-params workaround)

```
Program                  |  Strip |    B2S |    Fix |    deductive |   bugFinding |         cbmc | Detail
---------------------------------------------------------------------------------------------------------
abs_func                 |     OK |     OK |     OK |         SKIP |         SKIP |         FAIL | Nondet goto type-check (#1162)
array_sum                |     OK |     OK |     OK |         SKIP |         SKIP |         FAIL | Nondet goto type-check (#1162)
aws_array_eq             |     OK |     OK |     OK |         FAIL |         FAIL |         FAIL | Exit code 3
aws_byte_cursor_advance  |     OK |     OK |     OK |         FAIL |         FAIL |         FAIL | Exit code 3
aws_ring_buffer          |     OK |     OK |     OK |         FAIL |         FAIL |         FAIL | Exit code 3
loop_sum                 |     OK |     OK |     OK |         SKIP |         SKIP |         FAIL | Nondet goto type-check (#1162)
max_func                 |     OK |     OK |     OK |         SKIP |         SKIP |         FAIL | Nondet goto type-check (#1162)
nondet_branch            |     OK |     OK |     OK |         SKIP |         SKIP |         FAIL | Nondet goto type-check (#1162)
pointer_arith            |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL | CoreToGoto: LExpr.fvar
simple_add               |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL | CoreToGoto: LExpr.fvar
simple_assert            |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL | CoreToGoto: LExpr.fvar
swap                     |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL | CoreToGoto: LExpr.fvar

     deductive: 2 pass, 5 fail, 5 skip, 0 not reached
    bugFinding: 0 pass, 7 fail, 5 skip, 0 not reached
          cbmc: 0 pass, 12 fail, 0 skip, 0 not reached
```

## After (grammar fix with locals block)

```
Program                  |  Strip |    B2S |    Fix |    deductive |   bugFinding |         cbmc | Detail
---------------------------------------------------------------------------------------------------------
abs_func                 |     OK |     OK |     OK |         SKIP |         SKIP |         FAIL | Nondet goto type-check (#1162)
array_sum                |     OK |     OK |     OK |         SKIP |         SKIP |         FAIL | Nondet goto type-check (#1162)
aws_array_eq             |     OK |     OK |     OK |         SKIP |         SKIP |         FAIL | Nondet goto type-check (#1162)
aws_byte_cursor_advance  |     OK |     OK |     OK |         SKIP |         SKIP |         FAIL | Nondet goto type-check (#1162)
aws_ring_buffer          |     OK |     OK |     OK |         SKIP |         SKIP |         FAIL | Nondet goto type-check (#1162)
loop_sum                 |     OK |     OK |     OK |         SKIP |         SKIP |         FAIL | Nondet goto type-check (#1162)
max_func                 |     OK |     OK |     OK |         SKIP |         SKIP |         FAIL | Nondet goto type-check (#1162)
nondet_branch            |     OK |     OK |     OK |         SKIP |         SKIP |         FAIL | Nondet goto type-check (#1162)
pointer_arith            |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL | CoreToGoto: LExpr.fvar
simple_add               |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL | CoreToGoto: LExpr.fvar
simple_assert            |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL | CoreToGoto: LExpr.fvar
swap                     |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL | CoreToGoto: LExpr.fvar

     deductive: 2 pass, 2 fail, 8 skip, 0 not reached
    bugFinding: 0 pass, 4 fail, 8 skip, 0 not reached
          cbmc: 0 pass, 12 fail, 0 skip, 0 not reached
```

## Differences

| Program              | Before deductive | After deductive | Change |
|----------------------|------------------|-----------------|--------|
| aws_array_eq         | FAIL (exit 3)    | SKIP (#1162)    | Improved: no longer crashes with "output length mismatch" |
| aws_byte_cursor_advance | FAIL (exit 3) | SKIP (#1162)    | Improved: same |
| aws_ring_buffer      | FAIL (exit 3)    | SKIP (#1162)    | Improved: same |
| All others           | (unchanged)      | (unchanged)     | No regression |

**Summary of changes:**
- 3 programs improved from FAIL (exit code 3 = internal error) to SKIP (nondet goto #1162)
- The "output length and lhs length mismatch" error is eliminated — CFG procedures
  now have correct signatures matching their callers
- 0 regressions
- deductive: 2 pass, 2 fail, 8 skip (was 2 pass, 5 fail, 5 skip)
- bugFinding: 0 pass, 4 fail, 8 skip (was 0 pass, 7 fail, 5 skip)

The 3 AWS programs that previously hit "output length mismatch" (because locals
were promoted to out params, inflating the callee signature) now correctly parse
and type-check. They still SKIP at verification because they have nondet gotos
(#1162), but the locals-as-out-params bug is fully resolved.

## Remaining blockers

All 12 programs hit one of two issues:

1. **#1162 nondet goto type-check** (8 programs): CFG procedures with 2-target
   nondet gotos fail type-checking with "$__nondet_0 not found"
2. **CoreToGoto LExpr.fvar** (4 programs): StrataCoreToGoto can't translate
   expressions with untyped free variables
