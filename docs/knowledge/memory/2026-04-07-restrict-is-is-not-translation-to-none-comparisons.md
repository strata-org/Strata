# Restrict `is`/`is not` translation to None comparisons

**Date:** 2026-04-07
**Issue:** GitHub #778 (follow-up)

## What was wrong

Task 059 mapped `is`/`is not` unconditionally to `PEq`/`PNEq` (equality).
This is unsound for non-None operands because Python's `is` checks object
identity, not equality (e.g., `True is not 1` but `True == 1`).

## Fix

In both `PythonToLaurel.lean` and `PythonToCore.lean`, the `Is`/`IsNot`
match arms now check whether the raw RHS comparator AST node is
`.Constant _ (.ConNone _) _` before translating. Non-None uses produce
an `unsupportedConstruct` error (Laurel) or `panic!` (Core).

## Key patterns

- In `PythonToCore.lean`, the raw comparator is shadowed by the translated
  version. Introduced `rawRhs` binding before the shadow to preserve access
  to the original AST for the `ConNone` check.
- In `PythonToLaurel.lean`, `comparators.val[0]!` gives the raw AST node
  directly (translation happens separately via `translateExpr`).
- Test workflow: `.py` → Ion → `strata pyAnalyzeLaurel` → diff `.expected`.
- Exit code 4 = known limitation (unsupported construct).

## Tests added

- `test_is_non_none.py` — `x is y` (non-None) → rejected
- `test_is_not_non_none.py` — `x is not y` (non-None) → rejected
- Existing `test_is_none.py` — `x is None` / `x is not None` → still works
