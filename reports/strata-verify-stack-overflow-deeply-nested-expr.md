# `strata verify` SIGABRTs with `Stack overflow detected` on deeply nested if-then-else expression (~4100+ deep)

- **Status:** present on origin/main (verified at HEADs `349b1cf49` and `75f005566`)
- **Severity:** high
- **Component:** `StrataDDM.Elab.Core` (DDM elaboration — the `mutual` block containing `elabExpr` / `runSyntaxElaborator` / `elabSyntaxArg`)
- **File / lines:** [`StrataDDM/StrataDDM/Elab/Core.lean:1694`](https://github.com/strata-org/Strata/blob/75f005566eb405b774dd799d5a138faeea6e008f/StrataDDM/StrataDDM/Elab/Core.lean#L1694) (`elabExpr`); [lines 1224-1284](https://github.com/strata-org/Strata/blob/75f005566eb405b774dd799d5a138faeea6e008f/StrataDDM/StrataDDM/Elab/Core.lean#L1224-L1284) (`runSyntaxElaborator`); [lines 1166-1216](https://github.com/strata-org/Strata/blob/75f005566eb405b774dd799d5a138faeea6e008f/StrataDDM/StrataDDM/Elab/Core.lean#L1166-L1216) (`elabSyntaxArg`).
- **Cross-references:** [`stack-and-hang-conjectures-report.md`](stack-and-hang-conjectures-report.md) (issue 2 section, with the corrected diagnosis); [`elabexpr-paren-strip-experiment.md`](elabexpr-paren-strip-experiment.md) (failed micro-fix).

## What's wrong

A `.core.st` containing a deeply nested expression (e.g. ~5000 nested `if-then-else`) makes `strata verify` SIGABRT with the Lean runtime's `Stack overflow detected. Aborting.` **before** the parse banner is printed. The crash reproduces at every pre-solver pipeline stage (`--parse-only`, `--type-check`, `--check`), so the offending recursion is in DDM elaboration, not the SMT encoder.

| Aspect      | Observed                                                          |
|-------------|-------------------------------------------------------------------|
| Command     | `strata verify --check-mode deductive repro.core.st`              |
| Exit code   | `134` (SIGABRT)                                                   |
| Stderr      | `Stack overflow detected. Aborting.`                              |
| Stdout      | empty — `Successfully parsed.` is **not** printed                 |
| Wall time   | ~80-280 ms                                                        |
| Threshold   | reliably SIGABRTs at depth ≥ ~4100 nested `if`; canonical N=5000  |

The overflowing walker is `partial def elabExpr` at `StrataDDM/StrataDDM/Elab/Core.lean:1694`. The recursion is a 3-function monadic cycle inside the file's `mutual` block:

1. `elabExpr` recurses on itself for `Init.exprParen` (line 1697: `elabExpr tctx stx[1]`) — 1 stack frame per paren wrap.
2. `elabExpr`'s op-elaboration arms (`Init.exprApp` at line 1727, catch-all at line 1776) call `runSyntaxElaborator` to elaborate operator args — 2nd frame.
3. `runSyntaxElaborator` (line 1224) iterates over `se.argElaborators` and calls `elabSyntaxArg` — 3rd frame.
4. `elabSyntaxArg` (line 1166) calls back into `elabExpr` for `.typeExpr`/`.preType` arg kinds (lines 1178, 1199) — back to step 1 at the next nesting level.

So **each ITE level adds ~3 frames in the elabExpr/runSyntaxElaborator/elabSyntaxArg cycle, plus 1 frame per paren wrap**. At N=5000 levels with the reproducer's two paren wraps per level, total ~25,000 native frames → SIGABRT well before the 8MB default stack is exhausted (Lean frames are ~1KB each).

**Earlier diagnoses pointing at `Strata/Languages/Core/DDMTransform/Translate.lean:814` (`partial def translateExpr`) are wrong for this reproducer.** `translateExpr` runs *after* DDM elaboration; the SIGABRT happens before `Successfully parsed.` is printed, so `translateExpr` is never reached on this input. Verified empirically: a trampolined `translateExpr` was built (~382 LoC of replacement) and tested — it had **zero effect** on the reproducer at any depth.

The same monadic-cycle anti-pattern recurs in other walkers, but they are downstream of DDM elaboration and would only overflow on a different reproducer (one whose syntax parses but whose Core IR is deep):

- `partial def translateExpr` at `Strata/Languages/Core/DDMTransform/Translate.lean:818` (Core translation).
- `partial def toSMTTerm` / `appToSMTTerm` at `Strata/Languages/Core/SMTEncoder.lean:259, 334` (SMT encoding).
- The `mutual` block at `Strata/Languages/Core/DDMTransform/FormatCore.lean:537-704` (`lexprToExpr` family, formatter path).

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

Verified on `75f005566` (built from `StrataCLI/`): SIGABRT in ~80-280 ms; same exit and message under `--parse-only`, `--type-check`, `--check`.

## Impact

Any `.core.st` produced by an upstream translator (BoogieToStrata, a C/CBMC harness exporter, a SMACK pipeline) that emits deeply nested expressions will crash the verifier without diagnostics. The user sees a one-line abort with no source range and no exit-code distinction from a real solver crash. Not a soundness bug — there's no spurious "verified" verdict — but it silently blocks any verification workflow that can produce this shape.

## Fix

The structurally-correct fix is to break the elabExpr/runSyntaxElaborator/elabSyntaxArg cycle so depth is bounded by heap rather than native stack. Approach: CPS-defunctionalize the cycle into a worklist driver. **Caveat: this is not a small change** because:

- `runSyntaxElaborator` threads typing context with **sequential side effects** — arg N+1's `tctx` may depend on `trees[N].resultContext` (lines 1264-1268), `unifyTypes` mutates the trees vector in-place. The trampoline has to model "elaborate one arg, do bookkeeping, elaborate next" as worklist tasks with intermediate state — not the simpler "elaborate all sub-args independently, combine results" shape that admits a clean per-arm rewrite.
- The cycle spans 3 mutually-recursive `partial def` functions, each with its own per-arm logic (~50 cases for the operator dispatch in `elabExpr`'s catch-all). A per-function rewrite is invasive (~500-700 LoC).
- Lean's TCO doesn't reliably elide tail calls under `ElabM`'s monadic-effect stack, so naive CPS doesn't help.

A complete fix is estimated at 8-12 hours of careful rewriting plus extensive test coverage. An attempt was started and discarded in favour of fixing easier walkers first; the diagnosis (this document) is the deliverable.

A surgical paren-strip iterativization on `elabExpr`'s `Init.exprParen` arm was also tested and discarded — it eliminated 1 frame per level but left the dominant 3-frame operator-elaboration chain untouched, so the SIGABRT threshold did not move. See [`elabexpr-paren-strip-experiment.md`](elabexpr-paren-strip-experiment.md) for the full data.

Smaller stop-gap options that don't fully solve the bug but improve the failure mode:

- **Raise the Lean thread stack size at strata's `main` entry point** (e.g. via `Thread.spawn` with explicit stack size, or `LEAN_STACK_SIZE_MIB` env var on the wrapper script). Pushes the threshold from N≈4100 to N≈40000+ at the cost of 100× more memory per thread. Note: as of Lean 4.29.1 there is no public API for explicit stack-size control on `Thread.spawn`; this stop-gap requires waiting for or contributing such an API.
- **Surface a clean error with a source range** when an expression-depth threshold is exceeded. Doesn't enable verification of deep inputs, but makes the SIGABRT into a typed error the user can act on.

Secondary cleanup (still relevant, though not on the failure path for *this* reproducer): convert the downstream expression-tree walkers (`translateExpr`, `toSMTTerm`/`appToSMTTerm`, the `lexprToExpr` mutual block in `FormatCore.lean`) from `partial def` direct recursion to explicit-stack form. They exhibit the same anti-pattern and could overflow on inputs whose syntax parses cleanly but whose Core IR is deep.

## Plan to test

- Repro at N=5000 succeeds with the fix (parses, type-checks, returns a normal verification verdict or solver timeout — no SIGABRT).
- Repro at N=50000 fails gracefully with a typed error citing the source range, not SIGABRT.
- Existing `Examples/*.core.st` regression suite continues to pass with identical output.

## How this was diagnosed

Phase bisection on origin/main:

1. **Stop-flag walk:** `--parse-only` SIGABRTs in ~80ms with no `Successfully parsed.` banner. This rules out everything downstream of DDM elaboration (the parser-and-elaborator step, where `readStrataProgram` calls `Strata.Elab.elabProgram`).
2. **Code reading the elaborator entry point:** `Strata.Elab.elabProgram` is at `StrataDDM/StrataDDM/Elab/Core.lean:193`; it dispatches into the `mutual` block at line 1110 containing `elabOperation`/`elabSyntaxArg`/`runSyntaxElaborator`/`elabExpr`. `elabExpr`'s body has a direct self-recursion on `Init.exprParen` plus an indirect recursion through the runSyntaxElaborator/elabSyntaxArg pair — matching the failure shape.
3. **Empirical disproof of the previous diagnosis:** a trampolined version of `Strata/Languages/Core/DDMTransform/Translate.lean`'s `translateExpr` was built (~382 LoC of replacement) and verified against the reproducer. Zero effect on N=5000 timing or exit code, because the SIGABRT happens before `translateExpr` runs.
4. **Cross-validation against a paren-strip micro-fix:** an iterativization of `elabExpr`'s `Init.exprParen` arm alone did not move the threshold (N=5000 still SIGABRTs in ~75ms post-fix vs ~80-90ms pre-fix). This confirms the dominant frame consumer is the operator-elaboration chain (steps 2-4 above), not the paren wrap. Full data in [`elabexpr-paren-strip-experiment.md`](elabexpr-paren-strip-experiment.md).
