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

## After (nondet goto + local types fixes)

Two additional fixes applied:
1. `translateTransfer` now emits a `var $__nondet_N : bool;` init command for
   nondet gotos, resolving #1162
2. `procedureToGotoCtx` now seeds local variable types into the type environment

```
Program                  |  Strip |    B2S |    Fix |    deductive |   bugFinding |         cbmc | Detail
---------------------------------------------------------------------------------------------------------
abs_func                 |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL | CoreToGoto: expected structured body, got CFG
array_sum                |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL | CoreToGoto: expected structured body, got CFG
aws_array_eq             |     OK |     OK |     OK |         WARN |         WARN |         FAIL | CoreToGoto: LExpr.fvar
aws_byte_cursor_advance  |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL | CoreToGoto: LExpr.fvar
aws_ring_buffer          |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL | CoreToGoto: LExpr.fvar
loop_sum                 |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL | CoreToGoto: expected structured body, got CFG
max_func                 |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL | CoreToGoto: expected structured body, got CFG
nondet_branch            |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL | CoreToGoto: expected structured body, got CFG
pointer_arith            |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL | CoreToGoto: LExpr.fvar
simple_add               |     OK |     OK |     OK |         PASS |      PARTIAL |         FAIL | CoreToGoto: LExpr.fvar
simple_assert            |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL | CoreToGoto: LExpr.fvar
swap                     |     OK |     OK |     OK |      PARTIAL |      PARTIAL |         FAIL | CoreToGoto: LExpr.fvar

     deductive: 4 pass, 7 fail, 1 skip, 0 not reached
    bugFinding: 0 pass, 11 fail, 1 skip, 0 not reached
          cbmc: 0 pass, 12 fail, 0 skip, 0 not reached
```

## Differences (grammar fix → nondet + local types fix)

| Program       | Before deductive | After deductive | Change |
|---------------|------------------|-----------------|--------|
| abs_func      | SKIP (#1162)     | PARTIAL         | Unblocked, gets to verification |
| array_sum     | SKIP (#1162)     | **PASS**        | Fully verified |
| aws_array_eq  | SKIP (#1162)     | WARN (0 VCs)    | Unblocked, no assertions found |
| aws_byte_cursor_advance | FAIL (exit 3) | PARTIAL | Improved |
| aws_ring_buffer | FAIL (exit 3) | PARTIAL         | Improved |
| loop_sum      | SKIP (#1162)     | **PASS**        | Fully verified |
| max_func      | SKIP (#1162)     | PARTIAL         | Unblocked |
| nondet_branch | SKIP (#1162)     | PARTIAL         | Unblocked |
| pointer_arith | PASS             | **PASS**        | Unchanged |
| simple_add    | PASS             | **PASS**        | Unchanged |
| simple_assert | PARTIAL          | PARTIAL         | Unchanged |
| swap          | PARTIAL          | PARTIAL         | Unchanged |

**Summary:**
- deductive: 2 pass → **4 pass** (+array_sum, +loop_sum)
- 8 programs unblocked from SKIP (nondet goto #1162 resolved)
- 3 programs improved from FAIL/exit-3 to PARTIAL/WARN (grammar fix resolved)
- 0 regressions

## Remaining blockers

1. **CBMC "expected structured body, got CFG"** (5 programs): `coreToGotoFiles`
   calls `procedureToGotoCtx` which calls `p.body.getStructured`. Needs to use
   `procedureToGotoCtxViaCFG` for CFG bodies.
2. **CoreToGoto LExpr.fvar** (7 programs): `inout` parameters (like `_exn`)
   are assigned in the body, causing `definedVars` to collect them as locals.
   They get renamed with `mkLocalSymbol` (`main::1::_exn`) but the type env
   only has the formal version (`main::_exn`). Fix: filter out variables that
   are already in `formals` from the `locals` list before renaming.
3. **bugFinding PARTIAL** (11 programs): symbolic execution finds potential
   counterexamples for assertions — expected for SMACK programs without
   sufficient preconditions.
