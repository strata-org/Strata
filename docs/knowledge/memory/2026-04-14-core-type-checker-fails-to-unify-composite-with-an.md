# Fix: Core type checker fails to unify Composite with Any/Box

## Date: 2026-04-14

## Root causes
Two distinct issues caused "Impossible to unify" errors:

1. **Box name collision**: The heap's `Box` datatype collided with user-defined Python classes named `Box`. Renamed to `$Box` (Python identifiers can't contain `$`, DDM identifiers can).

2. **Composite→Any coercion gaps**: Composite-typed values were passed to contexts expecting Any without coercion. Added `coerceToAny` calls in: comparisons (`is`/`is not`), list/dict literals, field assignments on non-self objects, and variable assignments where target is Any.

## Key decisions
- Used `$` prefix for heap types (`$Box`, `$BoxInt`, etc.) since it's valid in DDM but not Python.
- `coerceToAny` replaces Composite values with `Hole` (unconstrained Any). This is lossy but type-safe.
- `with` statement `as`-variables use `AnyTy` since `__enter__` returns `LaurelResult: Any`.
- Stopped hoisting `with`-variables (returned empty list from `getWithItemsVars`) to avoid duplicate declarations with wrong types.

## Files changed
- `Strata/Languages/Laurel/HeapParameterizationConstants.lean` — `Box` → `$Box` in DDM prelude
- `Strata/Languages/Laurel/HeapParameterization.lean` — All `Box`-related string literals → `$Box`
- `Strata/Languages/Python/PythonToLaurel.lean` — Added coercion in 5 places; fixed `with` statement

## Known limitations
- `test_with_statement` (pending): `__enter__` returning `self` (Composite) can't be assigned to Any-typed variable and then have fields accessed. Requires Any→Composite cast not yet modeled.
- `test_object_in_list`, `test_recursive_data` (pending): Resolution failures for field access on objects retrieved from containers. Separate issue from type unification.

## For next agent
- If adding new heap types, use `$` prefix to avoid Python name collisions.
- The `coerceToAny` pattern (Composite→Hole) is sound but loses precision. A proper `from_ClassInstance` wrapping would be more precise.
- `getWithItemsVars` now returns `[]`; with-variable declarations are handled entirely by the `With` case in `translateStmt`.
