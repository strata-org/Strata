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

## Affected operators

Tested all operator categories on `ref := i64 := int`:

| Operator category | Affected? |
|---|---|
| Comparison (`<=`, `<`, `>=`, `>`) | **Yes** — panics |
| Arithmetic (`+`, `-`, `*`, `div`, `mod`) | **Yes** — panics |
| Equality (`==`, `!=`) | **No** — works correctly |

Equality works because it is handled earlier in `translateExpr` (line 819) with a wildcard type argument `_tpa` — it doesn't dispatch through `translateFn` and `isArithTy`:

```lean
| .fn _ q`Core.equal, [_tpa, xa, ya] =>
    let x ← translateExpr p bindings xa
    let y ← translateExpr p bindings ya
    return .eq () x y
```

Comparison and arithmetic go through a different path (line 1041–1056) that calls `translateLMonoTy` on the type argument and then checks `isArithTy`.

## Root cause

The error chain is:

1. `translateExpr` (line 1049) calls `translateLMonoTy bindings (dealiasTypeArg p tpa)`
2. `dealiasTypeArg` calls `dealiasTypeExpr` (line 452) which resolves **one level**: `ref` → `i64`
3. `translateLMonoTy` (line 254) handles the `.type (.syn syn)` case by returning `syn.toLHSLMonoTy` — which gives `i64` as an `LMonoTy`
4. The result is not `.int`, `.real`, or `.bitvec _`, so `isArithTy` (line 466) returns `false`
5. The error is triggered at line 1051

The fundamental issue: **`dealiasTypeExpr` resolves only one level of synonym**, not transitively. For `ref := i64 := int`, it resolves `ref` to `i64` but stops there. `i64` is itself a synonym for `int` that needs further resolution.

## Affected code

`Strata/Languages/Core/DDMTransform/Translate.lean`:

- **`dealiasTypeExpr`** (line 452) — resolves only one level of type synonym
- **`isArithTy`** (line 466) — only matches `.int`, `.real`, `.bitvec _`; doesn't handle unresolved synonyms
- **`translateLMonoTy`** (line 254) — returns synonym's LHS type without recursive resolution

## Suggested fix

**Option A — Make `dealiasTypeExpr` transitive** (simplest):

```lean
partial def dealiasTypeExpr (p : Program) (te : TypeExpr) : TypeExpr :=
  match te with
  | (.fvar _ idx #[]) =>
    match p.globalContext.kindOf! idx with
    | .expr te => dealiasTypeExpr p te    -- recurse!
    | .type [] (.some te) => dealiasTypeExpr p te  -- recurse!
    | _ => te
  | _ => te
```

This is the minimal fix — any place that calls `dealiasTypeArg` will automatically resolve the full chain.

**Option B — Resolve in `translateLMonoTy`**:

At line 254, after getting `syn.toLHSLMonoTy`, if the result is not a concrete type, look it up again. This is more localized but doesn't fix other potential consumers of `dealiasTypeExpr`.

**Option C — Make `isArithTy` resolve synonyms**:

Add a function `resolveToArithTy` that recursively unfolds type synonyms before checking if the type is arithmetic. This is more defensive but pushes complexity into the wrong place.

**Recommendation**: Option A is the cleanest — it makes `dealiasTypeExpr` do what its name promises (fully dealias) rather than only doing one step.
