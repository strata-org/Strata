# Testing Strata Dialects

This guide shows how to write tests for Strata dialects in the `StrataTest/`
directory. It focuses on **Laurel** (the path that received the most recent
ergonomic work) and notes where **Boole** uses the same primitives. For Python
test wiring, see [`StrataTest/Languages/Python/README.md`](../StrataTest/Languages/Python/README.md).

> **Quick rule of thumb:** put the dialect program inside a `#strata` block
> and call `testLaurel` (or `testLaurelResolution`) on it. If the program is
> expected to fail, annotate the expected diagnostics inline with
> `// ^^^ kind: message`. The helper auto-detects whether to expect a clean
> run or to match annotations.

## Background

- `#strata <dialect>; … #end` is a **term-elaboration block** that parses the
  inner Strata program at Lean compile time and elaborates to a
  `Strata.SourcedProgram` (the parsed `Program` plus the snippet text and the
  byte/line offset of the snippet inside the surrounding `.lean` file). Parse
  errors surface as Lean errors, so the LSP highlights them inside the block
  while you edit.
- A `Coe SourcedProgram Program` instance lets the result of `#strata` flow
  into APIs that expect a plain `Program` (e.g. `Strata.Boole.verify`); when
  consumers need `Program` directly, just write `.program`.
- `#guard_msgs` is Lean's built-in golden-test command. Used here for
  **positive tests** — wrap an `#eval` in `#guard_msgs in` and pin the
  expected output via a `/-- info: … -/` docstring directly above. Negative
  tests use inline annotations instead (see recipe 2).

Diagnostic positions in inline annotations are snippet-local: lines are
1-indexed within the `#strata` block, columns are 0-indexed. The helper
converts file-global pipeline diagnostics back to snippet-local positions
before matching, so annotations don't drift when the surrounding `.lean` file
is edited.

## Recipes

### 1. Positive test — program checks cleanly through the full pipeline

Use `testLaurel`. The helper throws if any diagnostics fire, so no
`#guard_msgs` / docstring is needed:

```lean
import StrataTest.Util.TestLaurel

open StrataTest.Util

#eval testLaurel
#strata
program Laurel;
procedure foo() opaque { assert true };
#end
```

### 2. Negative test — assert that specific errors fire

Same helper, `testLaurel`. Annotate each expected diagnostic *inline*, on the
line directly below the offending source line, with carets pointing at the
column range and the kind + (substring of the) message after the carets:

```lean
#eval testLaurel
#strata
program Laurel;
procedure unsafeDivision(x: int)
  opaque
{
  var z: int := 10 / x
//^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end
```

`testLaurel` auto-detects: when annotations are present, it requires an
**exact match on everything except the message text** — every diagnostic
annotated, every annotation fires, positions (line + column range) agree,
kind matches — and the annotation's message must appear as a **substring**
of the actual diagnostic message. When no annotations are present, it expects
no diagnostics. A mismatch throws with a precise summary of which annotations
went unmatched and which actual diagnostics had no annotation, so
`#guard_msgs` isn't needed for negative tests.

The message is matched as a substring (not a prefix, and not exact) on
purpose: real diagnostic messages often carry volatile detail — variable
names with unique-id suffixes, full type descriptions, fix suggestions — that
you don't want to pin verbatim. Annotate the stable, identifying fragment of
the message and the test stays robust as messages are reworded.

`kind` is one of `error`, `warning`, `not-yet-implemented`, `strata-bug`.

#### Reported locations

Each diagnostic is printed as `<fileLine>:<colStart>-<colEnd>  <kind>: <message>`,
where `fileLine` is the line in the enclosing `.lean` file (computed from the
snippet's base line — no manual offsets). The filename is omitted: the Lean
test runner already reports which file a diagnostic came from. This line is
always printed; pin it with `#guard_msgs` when you want to assert the
localization itself. Pass `showSnippet := true` to also append the
snippet-relative range — `… (snippet <line>:<colStart>-<colEnd>)` — which is
handy when correlating against the inline `// ^^^` annotations (those are
snippet-local, so their `line` differs from the file line).

### 3. Resolution-only tests — skip the verifier

When the test is about resolution (kind mismatches, duplicate names, scope
errors), running the verifier on a deliberately-broken program adds
unrelated noise (`dbg_trace` warnings, vacuous VCs). Use
`testLaurelResolution` — same auto-detect behavior as `testLaurel`, but
stops after `resolve`.

The gap between the two is not just the SMT call: `testLaurel` runs the full
compilation pipeline, which after `resolve` applies roughly a dozen
Laurel-to-Laurel lowering passes (type-alias elimination, heap
parameterization, type-hierarchy and modifies-clause transforms, hole-type
inference and elimination, short-circuit desugaring, imperative-expression
lifting, constrained-type elimination, …) before translating to Core and
verifying. Several of those passes re-run `resolve` on their output. So a
diagnostic that only `testLaurel` surfaces may originate from a later pass,
not the verifier. The major passes are described in the **Translation
Pipeline** section of the Laurel language manual — published at
[strata-org.github.io/Strata](https://strata-org.github.io/Strata/laurel/html-single/),
source in [`docs/verso/LaurelDoc.lean`](verso/LaurelDoc.lean) — and the full
pass list and exact ordering live in
[`Strata/Languages/Laurel/LaurelCompilationPipeline.lean`](../Strata/Languages/Laurel/LaurelCompilationPipeline.lean)
(`laurelPipeline`).

```lean
#eval testLaurelResolution
#strata
program Laurel;
procedure foo() opaque {
  var x: int := 1;
  var y: x := 2
//       ^ error: 'x' resolves to variable, but expected composite type, ...
};
#end
```

```lean
/-! Shadowing in nested blocks is OK -/
#eval testLaurelResolution
#strata
program Laurel;
procedure foo() opaque {
  var x: int := 1;
  { var x: int := 2 }
};
#end
```

### 4. Custom pipeline stage — bring your own helper

For tests that exercise a specific transform (e.g. `eliminateHoles`,
`liftExpressionAssignments`, `constrainedTypeElim`), build a small per-file
helper that takes a parsed `Strata.Program` and runs the stages you care about.
`translateLaurel` does the parse → translate step so you don't have to repeat
it.

```lean
import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.InferHoleTypes
import Strata.Languages.Laurel.EliminateHoles

open Strata
open StrataTest.Util

namespace Strata.Laurel

private def parseElimAndPrint (program : Strata.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let result := resolve laurelProgram
  let (laurelProgram, _, _) := inferHoleTypes result.model result.program
  let (laurelProgram, _) := eliminateHoles laurelProgram
  for proc in laurelProgram.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/--
info: function $hole_0()
  returns ($result: int)
  opaque;
procedure test()
{ var x: int := 1 + $hole_0() };
-/
#guard_msgs in
#eval parseElimAndPrint
#strata
program Laurel;
procedure test() { var x: int := 1 + <?> };
#end

end Strata.Laurel
```

The pattern: `translateLaurel : Strata.Program → IO Laurel.Program` is the
common entry point; everything after is dialect/test-specific.

### 5. One `#strata` block per independent unit; group only on dependency

The rule here is about **independence**, not about positive-vs-negative.
Every negative test still contains plenty of correct code — the procedure
that *does* verify so the broken one can be reached, the declarations the
failing statement refers to, and so on. That mix inside a single block is
expected and fine.

What matters is the boundary *between* blocks: give each independently
checkable unit its own `#strata` block, so a regression in one can't mask a
regression in another and a failure points at the smallest reproducing
snippet.

```lean
/-! ### Safe paths verify cleanly -/
#eval testLaurel #strata
program Laurel;
procedure safeDivision() opaque {
  var z: int := 10 / 2;
  assert z == 5
};
#end

/-! ### Unsafe division: divisor not constrained, fails verification -/
#eval testLaurel #strata
program Laurel;
procedure unsafeDivision(x: int) opaque {
  var z: int := 10 / x
//^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end
```

**The exception — and the more important point:** when the units genuinely
depend on each other (one procedure calls another, or they share a type or
declaration), they *must* live in the same `#strata` block, because
resolution needs them together. In that case, list the union of expected
diagnostics across all the contained procedures in one block.

## Practical workflow

1. Write the `#strata` block first, prefaced with `#eval testLaurel`.
2. For negative tests, sketch placeholder annotations like `// ^ error:`
   below the offending lines — column positions don't have to be right yet.
3. Run it: `lake env lean StrataTest/Languages/Laurel/<your_file>.lean`.
4. On failure: the helper prints exactly which annotations went unmatched
   and which diagnostics had no annotation, including the line/column range
   actually produced. Copy those into your annotations, save, re-run.

When `lake env lean` exits silently with no output, every assertion in the
file held.

> There is no auto-update ("bless") mode yet that rewrites the inline
> annotations to match the actual diagnostics. For now step 4 is a manual
> copy from the failure report; adding a bless mode is a natural follow-up.

## Other dialects

- **Boole** uses `#strata program Boole; … #end` directly with hand-written
  helpers (e.g. `Strata.Boole.verify`); see
  [`StrataTest/Languages/Boole/find_max.lean`](../StrataTest/Languages/Boole/find_max.lean)
  for the canonical pattern. `#strata` is dialect-agnostic — Boole could use
  inline annotations the same way once a Boole-side helper analogous to
  `testLaurel` is written.
- **Python** has its own pipeline-driven harness; see
  [`StrataTest/Languages/Python/README.md`](../StrataTest/Languages/Python/README.md).

## Where things live

| Concept | File |
| --- | --- |
| `#strata` elaborator + `SourcedProgram` | `Strata/DDM/Integration/Lean/HashCommands.lean` |
| `Diagnostic` data type | `Strata/Languages/Core/Verifier.lean` |
| Laurel test helpers | `StrataTest/Util/TestLaurel.lean` |
| Examples | `StrataTest/Languages/Laurel/Examples/**/*.lean` |
