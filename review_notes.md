# Review Notes — PR #537

## Summary

Extends the pySpecs Python-to-spec translator with f-string message handling, for-loop quantifiers (list and dict), conditional implication, `__init__` class field extraction, type-checked float/int comparisons, and negative integer bounds — enabling it to translate all assertion patterns found in the service specification files without warnings.

## Details

1. **F-string assertion messages**: Assertion messages using Python f-strings are now preserved as `MessagePart` arrays (string literals vs interpolated expressions) instead of flattened strings. The DDM `Assertion` op signature changed from `Str` to `Seq MessagePart`.
2. **For-loop quantification**: `for item in list` loops produce `forallList` quantifiers with element type inference from `typing.List`/`typing.Sequence` annotations. `for k, v in dict.items()` tuple unpacking produces `forallDict` with key/value type inference from `Dict`/`Mapping` annotations.
3. **Conditional implication**: `if` blocks wrapping assertions become `implies(condition, body)` via `assumeCondition`, which captures assertions from the body and wraps them. Currently handles `"key" in container` patterns.
4. **`__init__` class field extraction**: A dedicated handler for `__init__` methods extracts `self.field = self._ClassName()` assignments as `ClassField` entries with optional `constValue`, replacing the previous approach of treating `__init__` as a regular method.
5. **Type-checked numeric comparisons**: Comparison assertions dispatch to `intGe`/`intLe` or `floatGe`/`floatLe` based on inferred subject type. Float-typed fields with integer literal bounds fall back via int-to-float string conversion.
6. **Negative integer bounds**: `extractIntBound` handles `ConNeg` and `UnaryOp(USub, ConPos)`. The DDM `negSucc` encoding was fixed so `-1` round-trips correctly (stores `n+1` rather than raw `n`).
7. **DDM operator precedences**: Subscript at prec 50, comparisons at prec 15, implication at prec 10 (right-associative) to avoid unnecessary parentheses.
8. **Test coverage**: Positive tests for all new features in `main.py`/`SpecsTest.lean`. Separate negative tests in `warnings.py` checking warning emission for unsupported patterns. Test assertions throw errors instead of panicking.

## Findings

### Features

- **Clean `SpecAssertionM` monad design**: The new monad with its own `SpecAssertionContext` and `SpecAssertionState` provides a well-scoped environment for assertion extraction, with idiomatic use of `withReader` for scoped local type bindings in for-loops.
- **Thorough DDM round-trip coverage**: Every new `SpecExpr` constructor has corresponding `toDDM`/`fromDDM` arms, and the `negSucc` encoding bug fix is correctly reflected in both directions.
- **Warning-based negative testing**: The `warnings.py` + `warningTestCase` pattern cleanly separates positive and negative testing concerns, making it easy to extend.
- **Improved test diagnostics**: Tests use `throw IO.userError` with detailed diff messages showing the first diverging command index, replacing opaque `assert!` panics.
- **Zero-warnings assertion**: The positive test verifies `warnings.isEmpty`, catching regressions where clean patterns start producing warnings.

### Potential Issues

**1. ~~Missing `s!` string interpolation in 3 error messages~~ (Correctness)** — FIXED
- Added `s!` prefix to `"{dialect} already loaded"` in `Strata/Util/IO.lean` (2 occurrences) and `Strata/DDM/Elab.lean` (1 occurrence).

**2. ~~`transCondition` silently drops unrecognized if-conditions~~ (Correctness)** — FIXED
- Added warning `"if: unrecognized condition pattern: ..."` in the `If` handler when `transCondition` returns `none`. Assertions still pass through (unwrapped), but the user is now alerted.

**3. ~~`assert!` panics in For handler and class-body FunctionDef on valid Python~~ (Safety)** — FIXED
- Replaced `assert!` with `specWarning` for `type_comment` and `orelse`/`type_params` checks in both the `For` handler and the class-body `FunctionDef` handler. Valid but unsupported constructs (e.g., `for/else`) now warn instead of panicking.

**4. ~~`negSuccInt 0` edge case in `DDM.Int.ofDDM`~~ (Correctness)** — FIXED
- Renamed `negSuccInt` to `negInt` with format `"-" x`. `toDDMInt` stores `n+1` for `negSucc n`. `ofDDM` handles `negInt 0` explicitly (maps to `0`). Added round-trip `#guard` tests in `SpecsTest.lean`.

**5. ~~No test for `else`-branch / `not` expression~~ (Test Coverage)** — FIXED
- Added `else` branch to `float_and_negative_bounds` in `main.py`. Expected DDM output includes `not(Score in fp) => ...`. The `not` expression path through `toDDM`/`fromDDM` is now tested.

**6. ~~Dead code: `Pred` inductive type~~ (Structure)** — FIXED
- Removed `Pred` type, its `not` function, and the FIXME comment.

**7. ~~Dead code: `Iterable` inductive type~~ (Structure)** — FIXED
- Removed `Iterable` type.

**8. ~~`warnings.py` declares unused `LoopRequest` TypedDict~~ (Test Coverage)** — FIXED
- Added `for_else_loop` test function using `LoopRequest`. Warning test now checks for `"For: else clause not supported"`.

**9. ~~Duplicated comparison logic in `GtE`/`LtE` arms~~ (Structure)** — FIXED
- Extracted `makeComparison` helper parameterized by float/int constructors. Net reduction of ~30 lines.

**10. ~~Duplicated base-class resolution logic~~ (Structure)** — FIXED
- Extracted `resolveBaseClasses` helper used by both `pySpecClassBody` and `translate`.

**11. ~~No test for negative float bounds~~ (Test Coverage)** — FIXED
- Added `assert fp["Score"] >= -0.5` test case. Expected DDM output includes `>=_float "-0.5"`.

**12. ~~Warning test does not verify translator output~~ (Test Coverage)** — FIXED
- `warningTestCase` now checks `sigs.isEmpty` to verify the translator still produces output despite warnings.

**13. ~~Hard line-length violations in DDM.lean~~ (Style)** — FIXED
- Wrapped 2 lines exceeding 100 characters in DDM.lean.

## Agent Findings

### Correctness

- ~~**Missing `s!` interpolation**~~ — FIXED
- ~~**`transCondition` silent drops**~~ — FIXED
- ~~**`negSuccInt 0` edge case**~~ — FIXED: renamed to `negInt`, explicit `0` handling, round-trip tests added.
- **`__init__` ignores constructor args**: Only self-assignment patterns are extracted; constructor arguments are silently dropped.
- **`lookupTypedDictField` fragile indexing**: Uses `args.val[1]!` which could fail on malformed Python AST.

### Safety

- ~~**Missing `s!`** in 3 error messages~~ — FIXED
- ~~**`assert!` panics** in For handler and class-body FunctionDef~~ — FIXED
- ~~**`negSucc` fragile round-trip**~~ — FIXED: `negInt 0` now handled explicitly.
- Various forced indexing sites (`val[0]!`, `val[1]!`) were reviewed and found to be safe given the match guards.

### Style

- ~~**Missing `s!`** in 3 error messages~~ — FIXED
- ~~**Hard line violations** in DDM.lean~~ — FIXED.
- **Missing docstring** on `transAssertExpr`.
- ~~**Duplicated comparison logic** in GtE/LtE arms~~ — FIXED
- ~~**FIXME comment** on `Pred` should be resolved~~ — FIXED (removed with dead code in #6).
- **Stray blank lines** in a few locations.

### Structure

- ~~**Dead code**: `Pred` type (with FIXME), `Iterable` type~~ — FIXED (removed).
- ~~**Duplicated base-class resolution**~~ — FIXED (`resolveBaseClasses` helper).
- ~~**Duplicated comparison dispatch**~~ — FIXED (`makeComparison` helper).
- **Generic utilities** (`compareHLex`, `removeAdjDups`) in Decls.lean could belong in a utility module (pre-existing).
- **Positive**: Clean `SpecAssertionM` monad design, good `withReader` scoping, thorough DDM round-trip coverage, `baseLogEvent` refactoring.

### Test Adequacy

- ~~**No `else`-branch / `not` expression test**~~ — FIXED
- ~~**Unused `LoopRequest` in warnings.py**~~ — FIXED (added `for_else_loop` test)
- ~~**No negative float bound test**~~ — FIXED
- ~~**Warning test doesn't verify output**~~ — FIXED
- **Only `-1` tested for negSucc**: Testing with `-2` would better validate the encoding.
- **Positive**: Comprehensive happy-path coverage, improved diagnostics, zero-warnings assertion, clean negative test pattern.
