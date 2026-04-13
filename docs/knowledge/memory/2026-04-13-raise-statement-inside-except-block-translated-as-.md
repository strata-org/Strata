# Raise Statement Inside Except Block Translated as Hole

## Bug
`raise` in PythonToLaurel.lean was translated as a deterministic `Hole` (`<?>`),
which has `Unknown` type. The Laurel-to-Core translator rejects `Unknown` types
with "could not infer type".

## Root Cause
Line 1448 of `PythonToLaurel.lean`: `| .Raise _ _ _ => return (ctx, [mkStmtExprMd .Hole])`

## Fix
Replaced the Hole with three statements that model exception semantics:
1. `maybe_except := <??>` — havoc (non-deterministic Error value)
2. `assume isError(maybe_except)` — constrain to be a real error, not NoError
3. `exit $body` — terminate the function (same as `return` does)

## Key Patterns Discovered
- `maybe_except` is the variable tracking exception state throughout the pipeline
- `NoError` = no exception; `isError(maybe_except)` = exception occurred
- `.Hole` (deterministic) vs `.Hole false none` (non-deterministic/havoc) distinction matters
- `Exit "$body"` is how both `return` and `raise` exit the function
- Try/except checks `isError(maybe_except)` after each statement in the try body

## Tests Affected
- `test_try_except` and `test_multiple_except` improved from inconclusive to passing
- Added `test_raise_in_except` (exact bug report case) and `test_raise_variants` (edge cases)

## Pitfalls
- The test runner only picks up tests with existing `.expected` files
- `--update` only updates existing files; new tests need manual expected file creation
