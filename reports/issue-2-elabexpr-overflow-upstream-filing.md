# Stack overflow in DDM elaboration on deeply nested expressions (`elabExpr` cycle)

**Status:** present on `origin/main` HEAD (`75f005566`); reproducible at depth ≥ ~4100.
**Severity:** high — silently blocks any verification workflow that produces deep expressions.
**Location:** `StrataDDM/StrataDDM/Elab/Core.lean` — the mutually-recursive `elabExpr` / `runSyntaxElaborator` / `elabSyntaxArg` cycle (lines `1694`, `1224-1284`, `1166-1216` respectively).
**Not a soundness bug** — no spurious "verified" verdict. The verifier crashes loudly with `SIGABRT` and `Stack overflow detected. Aborting.`

## Summary

A `.core.st` file with a structurally deep expression (e.g. ~5000 nested `if-then-else`) makes `strata verify` SIGABRT before the parse banner is printed. The crash reproduces under every pre-solver flag (`--parse-only`, `--type-check`, `--check`), so the offending recursion is in DDM elaboration, not the SMT encoder.

The overflowing walker is a **3-function monadic cycle** inside `StrataDDM/StrataDDM/Elab/Core.lean`'s `mutual` block:

1. `elabExpr` recurses on itself for `Init.exprParen` (line 1697) — 1 frame per paren wrap.
2. `elabExpr`'s op-elaboration arms call `runSyntaxElaborator` — 2nd frame.
3. `runSyntaxElaborator` (line 1224) iterates over `argElaborators` and calls `elabSyntaxArg` — 3rd frame.
4. `elabSyntaxArg` (line 1166) calls back into `elabExpr` for `.typeExpr` / `.preType` arg kinds — back to step 1 at the next nesting level.

So **each ITE level adds ~3 native frames in the cycle, plus 1 frame per paren wrap**. At N=5000 levels with the reproducer's two paren wraps per level, total ~25,000 native frames → SIGABRT well before the 8MB default stack is exhausted (Lean frames are ~1KB each).

## Reproduction

```python
# gen.py
N = 5000
e = "0"
for i in range(1, N + 1):
    e = f"(if (x == {i}) then {e} else 0)"
print(f"program Core;\n\nprocedure Test(x : int)\nspec {{\n  ensures ({e} == 0);\n}}\n{{\n}};")
```

```
$ python3 gen.py > repro.core.st
$ strata verify --check-mode deductive repro.core.st

Stack overflow detected. Aborting.
$ echo $?
134
```

Verified on `75f005566`: SIGABRT in ~80-280 ms; same exit and message under `--parse-only`, `--type-check`, `--check`.

## Earlier diagnoses were wrong about location

The original triage (in this repo's downstream `htd/smack` branch) cited `partial def translateExpr` at `Strata/Languages/Core/DDMTransform/Translate.lean:813` as the overflowing walker. **Empirically wrong:** the SIGABRT happens *before* `Successfully parsed.` is printed — i.e. inside DDM elaboration, *before* `Translate.lean` runs. A trampolined `translateExpr` was built (~382 LoC of replacement) and verified against the reproducer. Zero effect on N=5000 timing or exit code.

## A surgical paren-strip fix is also insufficient

A 2026-06-02 experiment converted `elabExpr`'s `Init.exprParen` self-recursion to a `while` loop (eliminating 1 frame per paren wrap). Build succeeded; the 5000-deep ITE reproducer was unchanged: pre-fix N=5000 SIGABRTs in ~90 ms, post-fix in ~75 ms. **Threshold did not move.** The dominant frame consumer is the 3-frame operator-elaboration chain (steps 2-4 above), not the paren wrap.

Per-ITE-level frame consumption decomposed:

| Source | Frames per level |
|---|---:|
| Outer paren wrap (`(if ...)`) | 1 (eliminated by paren-strip fix) |
| `Core.if` op-elaboration via `elabExpr → runSyntaxElaborator → elabSyntaxArg → elabExpr` | 3 (untouched) |
| Cond paren wrap (`(x == N)`) | 1 if exposed every descent (eliminated by paren-strip) |
| Then-branch paren wrap | 1 (eliminated by paren-strip) |

Paren-strip eliminates 1-3 frames per level on Family 1 inputs; the remaining ~3 frames per level from the operator-elaboration chain dominate. Eliminating those requires CPS-converting the entire `elabExpr` / `runSyntaxElaborator` / `elabSyntaxArg` cycle.

## Why a complete fix is hard

`runSyntaxElaborator` threads typing context with **sequential side effects** — arg N+1's `tctx` may depend on `trees[N].resultContext` (lines 1264-1268), and `unifyTypes` mutates the trees vector in-place. The trampoline equivalent has to model "elaborate one arg, do bookkeeping, elaborate next" as worklist tasks with intermediate state — not the simpler "elaborate all sub-args independently, combine results" shape that admits a clean per-arm rewrite.

The cycle spans 3 mutually-recursive `partial def` functions, each with its own per-arm logic (~50 cases for the operator dispatch in `elabExpr`'s catch-all). A per-function rewrite is invasive (~500-700 LoC). Lean's TCO doesn't reliably elide tail calls under `ElabM`'s monadic-effect stack, so naive CPS doesn't help.

A complete fix is estimated at 8-12 hours of careful rewriting plus extensive test coverage.

## Side observation: parser slowness independent of stack overflow

During the paren-strip experiment, inputs at N=2000-4000 *timed out* at 30s without SIGABRT, both pre- and post-fix. This is a different failure mode — likely an O(N²) cost in parsing or DDM elaboration on deep-expression shapes, unrelated to the stack-depth bug. Worth tracking as a separate issue.

## Stop-gap options

- **Raise the Lean thread stack size at strata's `main` entry point** (e.g. `Thread.spawn` with explicit stack size, or `LEAN_STACK_SIZE_MIB` env var on the wrapper script). Pushes the threshold from N≈4100 to N≈40,000+ at 100× memory cost per thread. Note: as of Lean 4.29.1 there is no public API for explicit stack-size control on `Thread.spawn`; this would require a Lean-side change.
- **Surface a clean error with a source range** when an expression-depth threshold is exceeded. Doesn't enable verification of deep inputs, but turns the SIGABRT into a typed error the user can act on.

## Diagnostic recipe

For future stack-overflow regressions in DDM elaboration:

1. **Stop-flag walk:** `--parse-only` SIGABRTs in ~80ms with no `Successfully parsed.` banner ⇒ bug is in DDM elaboration (the parser-and-elaborator step).
2. **Code reading on the elaborator entry:** `Strata.Elab.elabProgram` at `StrataDDM/StrataDDM/Elab/Core.lean:193` dispatches into the `mutual` block at line 1110. Look for direct self-recursion or mutual-recursion through `runSyntaxElaborator`/`elabSyntaxArg`.
3. **Empirical disproof of suspected walker:** Build a candidate fix, run the reproducer; if neither timing nor exit code changes, the walker isn't on the failure path. (This caught the original `translateExpr` mis-diagnosis.)

## References

- Original triage (with the now-corrected diagnosis): `reports/strata-verify-stack-overflow-deeply-nested-expr.md` on the `htd/smack` branch.
- Paren-strip experiment data: `reports/elabexpr-paren-strip-experiment.md` on the `htd/smack` branch.
- Cross-reference: `reports/stack-and-hang-conjectures-report.md` issue (2) section — covers the family of three related stack/hang issues; issues (1) and (3) are resolved, (2) is this report.
