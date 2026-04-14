# Fix: Object-to-Any coercion not supported for nested class fields

## Date: 2026-04-14

## Root cause
Four interrelated gaps prevented user-defined class fields from being used as field types on other classes:

1. `wrapFieldInAny` threw "unsupported" for `UserDefined` fields instead of returning the expression as-is.
2. `self.field` access in methods threw the same error for `UserDefined` fields.
3. `translateMethod` typed ALL non-self parameters as `Any`, causing type mismatches when passing Composite values to `__init__` methods that assign to Composite-typed fields.
4. `self.field = value` in `__init__` called `coerceToAny` on Composite RHS values, replacing them with `Hole` instead of assigning directly.

## Key decisions
- Composite field expressions are returned as-is from `wrapFieldInAny` — they don't need Any wrapping because they're either used for further field access (chained `.field.field`) or coerced later by `coerceToAny` at assignment sites.
- Method parameters annotated with composite types now get `UserDefined` type (like `translateFunction` already did), matching the heap model's `$BoxComposite` expectations.
- `self.field = value` skips coercion when the field is Composite-typed, allowing direct Composite→Composite assignment.

## Files changed
- `Strata/Languages/Python/PythonToLaurel.lean` — four targeted changes in `wrapFieldInAny`, `translateExpr` (Attribute case), `translateAssign` (self.field case), and `translateMethod`

## Patterns discovered
- The heap parameterization uses `$BoxComposite` for Composite-typed fields. The box constructor expects `Composite`, not `Any`. So the Laurel-level types must match.
- `translateFunction` already handled composite parameter types correctly; `translateMethod` was the gap.
- Resolution warnings ("'val' is not defined") appear for nested field access on composites but are non-fatal — verification still succeeds.

## For next agent
- The resolution warnings for nested composite field access are a separate issue from type unification. They don't block verification but could be cleaned up.
- If adding new composite field handling, ensure both the parameter type AND the `variableTypes` context track the composite type (not just `Any`).
- The `coerceToAny` pattern (Composite→Hole) is correct for contexts where the value flows into `Any`-typed slots, but NOT for Composite→Composite assignments.
