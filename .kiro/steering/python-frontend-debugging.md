---
inclusion: fileMatch
fileMatchPattern: ['Strata/Languages/Python/**/*.lean', 'Strata/Languages/Laurel/**/*.lean', 'StrataTest/Languages/Python/**/*.lean']
---

# Debugging the Python front-end

Pointers for agents investigating `pyAnalyzeLaurel` / `pyAnalyzeLaurelToGoto`
failures. For background, read [`docs/PythonFrontend.md`](../../docs/PythonFrontend.md).

## Pipeline map (where does this fail?)

```
Python AST  →  Laurel  →  (resolve, heap-param., hole-elim.)  →  Core  →  SMT
   [1]          [2]                 [3]                          [4]      [5]
```

| Stage | Error prefix / symptom | Typical file |
|-------|------------------------|--------------|
| [1] Reader | `Parse error`, malformed AST | `ReadPython.lean`, `Tools/Python` |
| [2] Python→Laurel | `Unsupported construct`, `User code error`, `Translation error` | `PythonToLaurel.lean` |
| [3] Laurel→Core passes | `Resolution failed: 'X' is not defined`, `could not infer type`, `holes should have been eliminated`, `asserts are not YET supported in functions or contracts`, `calls to procedures are not supported in functions or contracts` | `Resolution.lean`, `HeapParameterization.lean`, `EliminateHoles.lean`, `LaurelToCoreTranslator.lean` |
| [4] Core type check | `Impossible to unify`, `Variable X not found` | `LaurelToCoreTranslator.lean`, `ProgramType.lean` |
| [5] Verification | `Failures found`, `Inconclusive`, `N passed, M failed, K inconclusive` | SMT backend / specs |

Laurel→Core messages almost always name the originating PySpec or user file
with a byte range — use that first, not the Lean file that emits the
diagnostic.

## Invariants that must hold

1. **Everything user-visible is `Any`.** In the Laurel/Core program, the type
   of any user variable, argument, or return value is `Any` (see
   `PythonLaurelCorePrelude.lean`). If a user-level value appears with a
   non-`Any` type, the translator has deviated from the encoding.
2. **Tag checks precede unwraps.** `Any..as_int!(x)` (and friends) must be
   preceded by `assert Any..isfrom_int(x)`. The translator inserts these;
   if one is missing, the analysis is unsound, not just imprecise.
3. **`maybe_except` is threaded through user procedures.** Every statement
   that might raise writes to `maybe_except : Error`; subsequent statements
   guard with `if isError(maybe_except) then exit ...`.
4. **Exception-check asserts never contain user procedure calls.** If they
   would, the translator must extract the call into a temporary variable
   first (see PR #1012). Pure-context positions (assert bodies, `if`/`while`/
   `for` conditions inside a function or contract) refuse procedure calls.
5. **Holes carry back types.** `EliminateHoles` expects every hole to have
   been typed by `InferHoleTypes`. A "holes should have been eliminated"
   Laurel→Core error means the hole-typing pass gave up on that node.
6. **Procedure names are mangled.** Method `M` on class `C` becomes
   `C@M` at the Laurel level. When searching Laurel/Core output for a method
   name, use the mangled form.
7. **PySpec pre/postconditions are trusted.** Treat them like axioms when
   reasoning about verification results.

## Common failure classes and where to look

### "Resolution failed: 'X' is not defined"

* Source: `Resolution.lean::resolveRef`.
* X is an *identifier* that the translator emitted but never introduced as a
  local, parameter, imported symbol, or field-of-`self`. Look upstream in
  `PythonToLaurel.lean` for where X is written. Common causes:
  - Attribute access on a dynamic receiver (e.g. `session.region_name` where
    `session` is `Any`) — the attribute name leaked into the identifier
    namespace instead of being treated as a field read.
  - Imported but unmodelled symbols — need either a PySpec entry or a
    matching handling in `PythonToLaurel`.

### "could not infer type"

* Source: Laurel's `InferHoleTypes` giving up on a hole, or the
  Laurel→Core translator failing `translateType` on an `Unknown` high type.
* Either the hole has no context to infer from (dead value, unused
  assignment), or a Python type annotation slipped through as `Unknown`
  because the front-end did not recognise it.

### "calls to procedures are not supported in functions or contracts"

* Source: `LaurelToCoreTranslator.lean`.
* A user procedure call landed in a position the Core language forbids:
  assert bodies, pre/postconditions, `if`/`while` guards inside a function
  body. The translator in `PythonToLaurel.lean` is expected to hoist the
  call into a fresh local. Check `translateStmt` — in particular the
  `if`/`while`/`for` handling (PR #1012) and `withExceptionChecks`.

### "asserts are not YET supported in functions or contracts"

* Source: same file, assert-in-expression-position handler.
* Emitted by `translateExpr` when a `Block` with a leading `Assert` reaches
  expression position. Historically caused the entire Core program to be
  discarded; the fix is to emit a diagnostic and translate the remainder
  (see commit "Handle Assert/Assume in expression-position blocks without
  discarding program").

### "holes should have been eliminated before translation"

* Source: `LaurelToCoreTranslator.lean`, triggered when a hole survives
  past `EliminateHoles`.
* Usually means `EliminateHoles` did not descend into a new kind of block
  that a recent `PythonToLaurel` change introduced (e.g. wrapping holes in
  a `Block`). Double-check that every container the translator creates is
  visited by the hole-elimination pass.

### "N passed, 0 failed, M inconclusive" / "Inconclusive"

* Not a translator failure. The SMT solver cannot decide the VCs.
* Most common root cause: an unmodelled call was havoc'd into a hole, and
  a downstream assertion now depends on the havoc'd value.
* Before changing the translator, see whether adding a PySpec entry or
  strengthening an existing postcondition eliminates the hole.

### "Failures found" on a clean benchmark (false alarm)

* The verifier produced a counter-example for a property we believe holds.
* Check whether the counter-example relies on:
  - A missing postcondition in PySpec (frequent).
  - Aliasing (known latent unsoundness; see front-end doc).
  - A flow-sensitive narrowing (`isinstance` check) that the Core checker
    cannot exploit — the translator must either insert a tag assumption
    or the spec must be strengthened.

### GOTO pipeline timeouts or CBMC errors

* Once Core translation succeeds, the `pyAnalyzeLaurelToGoto` flow hits
  `Strata/Backends/CBMC/GOTO/`. Consult
  [`docs/CoreToGOTO_Gaps.md`](../../docs/CoreToGOTO_Gaps.md). A recurring
  theme is that CBMC's field-sensitive pointer analysis struggles with
  `Map Composite (Map Field Box)` (the Heap), so heap-heavy programs time
  out even when Strata accepts them.

## Before you edit the translator

1. **Read the relevant Laurel output.** Use `pyAnalyzeLaurel ... --verbose`
   (or pass `--keep-all-files`) to dump the intermediate Laurel program.
2. **Identify the stage.** Is the error emitted by a translator, a
   resolution pass, the hole pipeline, or the Core type checker? The list
   above helps. Fixing a "Resolution failed" in `LaurelToCoreTranslator`
   is usually the wrong layer — fix the translator that emits the bad
   identifier.
3. **Check the expect files first.** `kiro_tests_annotated/<name>.expect.*`
   encodes what we expect the benchmark to do and the historical timing.
   A regression may be against a stale baseline.
4. **Regenerate PySpecs if stale.**
   ```
   python3 run_analysis.py --strata-dir ~/Desktop/strata.git/Strata --update-botomoog
   ```
   `lenExpr`-related errors are the classic symptom of pyspec/ being older
   than the current `PythonSpecs` dialect.
5. **Match the encoding.** New translator cases must wrap user values in
   `from_*` constructors and unwrap with tag-checked `as_*` accessors.
   Do *not* introduce primitive Core types for user data.

## Test discipline

* Reproduce the failure with a self-contained benchmark under
  `StrataTest/Languages/Python/tests/`.
* Check the `expected_laurel/` output if the bug is in Python→Laurel; that
  directory contains golden files regenerated via `compare_backends.sh`.
* Resolution and hole-elimination fixes usually want a test under
  `StrataTest/Languages/Laurel/` with `#guard_msgs` on the emitted
  diagnostics, as in `DuplicateNameTests.lean`.

## Known architectural limits (don't fix these locally)

These come from Strata's type system, not from the Python translator:

* No subtyping / nominal class hierarchy at the type level — `isinstance`
  checks only affect tag discriminants.
* No flow-sensitive narrowing — conditionals do not refine variable types.
* No union/optional types at the Core level — handled by tag checks only.
* No row types for `TypedDict` — collapsed to `DictStrAny`.
* No closure model — nested `def` / lambda cannot be assigned into a
  variable.
* Aliasing on mutable containers is not modelled (value-semantics
  `ListAny`/`DictStrAny`). Do not add aliasing on the side; it needs a
  heap model change.

If a bug report hinges on one of these, say so explicitly in the response
and do not silently narrow the problem.
