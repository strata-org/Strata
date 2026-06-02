# `strata verify` aborts with `Stack overflow detected` on deeply nested if-then-else expression (~5000 deep)

> **Corrections (2026-06-02).** The original culprit citation in this
> report was wrong. Empirical bisection on origin/main established:
> - The SIGABRT happens *before* `Successfully parsed.` is printed —
>   i.e. inside DDM elaboration, *before* `Translate.lean`'s walkers
>   ever run. A trampoline rewrite of `translateExpr` was attempted
>   (built clean) and verified to have **zero effect** on the
>   reproducer at any depth.
> - The actual overflowing walker is **`elabExpr` at
>   `StrataDDM/StrataDDM/Elab/Core.lean:1694`** (origin/main
>   `75f005566`; was at `Strata/DDM/Elab/Core.lean:1659` before
>   commit `703404f66` extracted the StrataDDM package). Recursion is
>   a 3-function monadic cycle: `elabExpr → runSyntaxElaborator →
>   elabSyntaxArg → elabExpr`, costing ~3 native frames per ITE
>   level, plus 1 frame per paren wrap.
> - A surgical paren-strip iterativization on `elabExpr`'s
>   `Init.exprParen` arm was tested and discarded — it eliminated 1
>   frame per level but left the dominant 3-frame operator-elaboration
>   chain untouched, so the SIGABRT threshold did not move. See
>   `reports/elabexpr-paren-strip-experiment.md` for the full data.
> - The correct fix is a worklist + combiner-stack rewrite of the
>   `elabExpr` / `runSyntaxElaborator` / `elabSyntaxArg` cycle.
>   Estimated 8-12 hours of careful work given the sequential typing-
>   context threading and per-arg side effects (`unifyTypes`, etc.).
>
> The `translateExpr` / `toSMTTerm` / `appToSMTTerm` /
> `FormatCore.lean lexprToExpr` walkers cited below **do** exhibit
> the same anti-pattern, but they are downstream of DDM elaboration.
> They could overflow on a different input shape (one whose syntax
> parses but whose Core IR is deep), but not on the documented N=5000
> deep-ITE input.
>
> Cross-references: `reports/stack-and-hang-conjectures-report.md`
> (issue 2 section, with the corrected diagnosis), and
> `reports/elabexpr-paren-strip-experiment.md` (the failed micro-fix).

- **Status:** present on origin/main (verified at HEADs `349b1cf49` and `75f005566`)
- **Severity:** high
- **Component:** DDM elaboration (`StrataDDM/StrataDDM/Elab/Core.lean`)
- **Walker (corrected):** [`StrataDDM/StrataDDM/Elab/Core.lean:1694`](https://github.com/strata-org/Strata/blob/main/StrataDDM/StrataDDM/Elab/Core.lean#L1694) — the 3-function monadic cycle `elabExpr` ↔ `runSyntaxElaborator` ↔ `elabSyntaxArg`

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

The recursive walker that overflows is the `elabExpr` / `runSyntaxElaborator` / `elabSyntaxArg` cycle in [`StrataDDM/StrataDDM/Elab/Core.lean:1694`](https://github.com/strata-org/Strata/blob/main/StrataDDM/StrataDDM/Elab/Core.lean#L1694) (see Corrections box at top). Each ITE level adds ~3 native frames through this cycle plus 1 frame per paren wrap, with no fuel/iterative fallback. The same anti-pattern recurs across the codebase in walkers downstream of elaboration (`partial def translateExpr` at `Strata/Languages/Core/DDMTransform/Translate.lean:818`, `toSMTTerm`/`appToSMTTerm` at `Strata/Languages/Core/SMTEncoder.lean:259,334`, and the `mutual` block in `Strata/Languages/Core/DDMTransform/FormatCore.lean:537-704`); a different repro shape that survives elaboration would crash inside one of those instead.

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

- **Primary:** Worklist + combiner-stack rewrite of the `elabExpr` / `runSyntaxElaborator` / `elabSyntaxArg` mutual cycle in `StrataDDM/StrataDDM/Elab/Core.lean`. The cycle threads typing context with sequential side effects (`tctx` for arg N+1 may depend on `trees[N].resultContext` per `runSyntaxElaborator`'s loop body; `unifyTypes` mutates the trees vector in-place), so a trampoline equivalent must model "elaborate one arg, do bookkeeping, elaborate next" as worklist tasks with intermediate state — not the simple "elaborate all sub-args, combine results" shape that `translateExpr` admitted. Estimated 8-12 hours; paren-strip alone is insufficient (see `reports/elabexpr-paren-strip-experiment.md`).
- **Secondary (still relevant):** Convert downstream expression-tree walkers (`translateExpr`, `toSMTTerm`/`appToSMTTerm`, the `lexprToExpr` mutual block in `FormatCore.lean`) from `partial def` direct recursion to explicit-stack form. These are not on the failure path for *this* reproducer, but exhibit the same anti-pattern and could overflow on inputs whose syntax parses cleanly but whose Core IR is deep.
- **Stop-gap:** Raise the Lean thread stack size at strata's `main` entry point (e.g. via a `Thread.spawn` with explicit stack size), and surface a clean error with a source range when an expression-depth threshold is exceeded. Note: as of Lean 4.29.1 there is no public API for explicit stack-size control on `Thread.spawn`; this stop-gap requires waiting for or contributing such an API.

## Plan to test

- Repro at N=5000 succeeds with the fix (parses, type-checks, returns a normal verification verdict or solver timeout — no SIGABRT).
- Repro at N=50000 fails gracefully with a typed error citing the source range, not SIGABRT.
- Existing `Examples/*.core.st` regression suite continues to pass with identical output.
