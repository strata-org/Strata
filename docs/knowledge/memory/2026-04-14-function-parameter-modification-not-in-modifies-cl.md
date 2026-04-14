# Fix: Function parameter modification not in modifies clause

## Date: 2026-04-14

## Root cause
`translateFunction` in `PythonToLaurel.lean` passed function parameters directly as Core procedure inputs. In Python, parameters are mutable locals, but in Core, input parameters cannot be modified. When a function body reassigned a parameter (e.g., `x = x + 10`), Core's type checker rejected it because `x` was modified but not in the modifies clause.

`translateMethod` already handled this correctly by renaming inputs to `$in_<name>` and prepending `var <name> := $in_<name>` local copies. `translateFunction` was missing this pattern.

## Fix
Applied the same parameter renaming pattern from `translateMethod` to `translateFunction`:
1. Rename all input parameters to `$in_<name>`
2. Prepend `LocalVariable` declarations copying `$in_<name>` → `<name>`
3. Update type constraint preconditions to reference `$in_<name>`

## Files changed
- `Strata/Languages/Python/PythonToLaurel.lean` — added parameter renaming in `translateFunction`
- 7 expected test outputs updated (precondition messages now show `$in_` prefix)
- 2 new test files: `test_var_shadow_func.py`, `test_param_reassign.py`

## For next agent
- Methods have a `self` parameter that is NOT renamed (filtered out). Functions have no such exception.
- The `$in_` prefix convention is shared between `translateFunction` and `translateMethod`.
- Type constraint preconditions must reference the renamed parameter names, not the originals.
