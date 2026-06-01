# `strata verify` aborts with `Stack overflow detected` on deeply nested if-then-else expression (~5000 deep)

- **Status:** present on origin/main (HEAD: `349b1cf4915d3d9357b8de7edcc94d3b9a79f0b5`)
- **Severity:** high
- **Component:** `Strata.Elab` / `Strata.Languages.Core.DDMTransform.Translate` (DDM elaboration / Core AST translator)
- **File / lines:** [`Strata/Languages/Core/DDMTransform/Translate.lean:813-1180`](https://github.com/strata-org/Strata/blob/349b1cf4915d3d9357b8de7edcc94d3b9a79f0b5/Strata/Languages/Core/DDMTransform/Translate.lean#L813-L1180)

## What's wrong

A user `.core.st` containing a structurally deep expression (e.g. ~5000 nested `if-then-else`) makes `strata verify` abort with the Lean runtime's `Stack overflow detected. Aborting.` (SIGABRT, exit 134) before the parse banner is even printed. The crash reproduces at every pre-solver pipeline stage (`--parse-only`, `--type-check`, `--check`, `--no-solve`), so the offending recursion is in DDM elaboration, not the SMT encoder.

| Aspect      | Observed                                                            |
|-------------|---------------------------------------------------------------------|
| Command     | `strata verify --check-mode deductive repro.core.st`                |
| Exit code   | `134` (SIGABRT)                                                     |
| Stderr      | `Stack overflow detected. Aborting.`                                |
| Stdout      | empty — `Successfully parsed.` is **not** printed                   |
| Wall time   | ~90 ms                                                              |
| Threshold   | reliably crashes at depth ≥ ~4100 nested `if`; canonical repro N=5000 |

The recursive walker that overflows is `partial def translateExpr` at [`Translate.lean:813`](https://github.com/strata-org/Strata/blob/349b1cf4915d3d9357b8de7edcc94d3b9a79f0b5/Strata/Languages/Core/DDMTransform/Translate.lean#L813), which descends each `Arg` branch by direct recursion with no fuel/iterative fallback. The same anti-pattern recurs across the codebase (`toSMTTerm`/`appToSMTTerm` at [`SMTEncoder.lean:259,334`](https://github.com/strata-org/Strata/blob/349b1cf4915d3d9357b8de7edcc94d3b9a79f0b5/Strata/Languages/Core/SMTEncoder.lean#L259-L334), plus several `partial def` walkers in `DDM/Elab.lean` and `DDMTransform/FormatCore.lean`); a different repro shape that survives elaboration would crash inside `toSMTTerm` instead.

## Reproduction

Generate `repro.core.st` (one procedure, body `{}`, with a 5000-deep `if-then-else` in the `ensures`):

```python
# gen.py
N = 5000
e = "0"
for i in range(1, N + 1):
    e = f"(if (x == {i}) then {e} else 0)"
print(f"program Core;\n\nprocedure Test(x : int)\nspec {{\n  ensures ({e} == 0);\n}}\n{{\n}};")
```

Then:

```
$ python3 gen.py > repro.core.st
$ strata verify --check-mode deductive repro.core.st
Stack overflow detected. Aborting.
$ echo $?
134
```

## Impact

Any `.core.st` produced by an upstream translator (e.g. Boogie→Strata or a C/CBMC harness exporter) that emits deeply nested expressions will crash the verifier without diagnostics. The user sees a one-line abort with no source range and no indication of which expression is too large. Not a soundness bug — there is no spurious "verified" verdict — but it blocks any verification workflow that can produce this shape, and it does so silently from the verifier's perspective (no SARIF, no exit-code distinction from a real solver crash).

## Fix

Two complementary directions:

- Convert the hot expression-tree walkers (`translateExpr` and its peers, plus `toSMTTerm`/`appToSMTTerm` in `SMTEncoder.lean`) from `partial def` direct recursion to an explicit-stack / CPS / `StateT (List Frame)` loop so depth is bounded by heap rather than the native stack.
- As a stop-gap, raise the Lean thread stack size at strata's `main` entry point (e.g. via a `Thread.spawn` with explicit stack size), and surface a clean error with a source range when an expression-depth threshold is exceeded.

## Plan to test

- Repro at N=5000 succeeds with the fix (parses, type-checks, returns a normal verification verdict or solver timeout — no SIGABRT).
- Repro at N=50000 fails gracefully with a typed error citing the source range, not SIGABRT.
- Existing `Examples/*.core.st` regression suite continues to pass with identical output.
