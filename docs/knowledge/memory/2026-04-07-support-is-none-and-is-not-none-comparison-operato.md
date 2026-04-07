# Support `is None` and `is not None` comparison operators

**Date:** 2026-04-07
**Issue:** GitHub #778

## What was wrong

The `PythonToLaurel.lean` comparison operator match was missing cases for
`cmpop.Is` and `cmpop.IsNot`. The wildcard `_` arm threw an
`unsupportedConstruct` error, causing exit code 4.

## Fix

Added two match arms in `translateExpr` for the `.Compare` case:
- `.Is _` → `"PEq"` (maps to the `PEq` prelude function)
- `.IsNot _` → `"PNEq"` (maps to the `PNEq` prelude function)

This is semantically correct because `is`/`is not` are identity checks,
and in the `Any` value model (where `None` is the singleton `from_None()`),
identity and equality coincide.

Removing the wildcard arm makes the match exhaustive, so future `cmpop`
additions will produce a compile error instead of a silent runtime failure.

Note: The legacy `PythonToCore.lean` translator also has `Is`/`IsNot` arms
but retains a wildcard `panic!` for other unhandled operators.

## Key patterns

- Comparison operators are mapped to prelude function names (`PEq`, `PLt`, etc.)
  in `PythonToLaurel.lean` around line 504.
- Prelude functions are defined in `PythonRuntimeLaurelPart.lean`.
- Test workflow: `.py` → parse to `.ion` → `strata pyAnalyzeLaurel` → diff against `.expected`.
- Run tests: `cd StrataTest/Languages/Python && bash run_py_analyze.sh laurel`
