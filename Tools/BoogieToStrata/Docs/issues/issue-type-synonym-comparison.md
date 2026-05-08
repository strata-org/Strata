# Strata verifier panics on comparison operators applied to type synonyms

## Problem

When a function uses `<=`, `<`, `>=`, or `>` on operands whose type is a synonym (e.g., `ref := i64 := int`), the Strata type checker in `translateFunction` panics with "translateExpr unexpected type for ge/le/lt/gt" instead of resolving the synonym chain to `int`.

## Minimal reproducer

```strata
program Core;

type i64 := int;
type ref := i64;

function sle_ref_bool(p1 : ref, p2 : ref) : (bool) {
  (p1 <= p2)
}

function slt_ref_bool(p1 : ref, p2 : ref) : (bool) {
  (p1 < p2)
}

procedure main(out r : int)
spec {
  ensures (r == 0);
}
{
  entry: {
    assert sle_ref_bool(1, 2);
    r := 0;
  }
};
```

## Steps to reproduce

1. Save the above as `test.core.st`
2. Run: `.lake/build/bin/strata verify test.core.st`
3. Observe panic with backtrace including `translateExpr unexpected type for { dialect := "Core", name := "le" }`

## Expected behavior

The verifier should resolve type synonym chains before checking operator compatibility. `ref := i64 := int` should be treated as `int` for the purposes of comparison operators.

## Actual behavior

Panic in `Strata.translateFunction` with a backtrace showing it cannot handle `le`/`lt`/`ge`/`gt` on non-`int` types even when those types are synonyms for `int`.

## Affected code

`Strata/Languages/Core/Verifier.lean` or the DDM translation layer — wherever operator type checking happens in `translateFunction`.

## Notes

- Equality (`==`) and arithmetic operators may or may not be affected — needs investigation.
- The fix likely involves calling a synonym-resolution helper (e.g., `resolveType` or `unfoldTypeSynonyms`) on the operand type before the pattern match that dispatches to the SMT translation for comparison operators.
