# Testing Strata Dialects

This guide shows how to write tests for Strata dialects in the `StrataTest/`
directory. It focuses on **Laurel** (the path that received the most recent
ergonomic work) and notes where **Boole** uses the same primitives. For Python
test wiring, see [`StrataTest/Languages/Python/README.md`](../StrataTest/Languages/Python/README.md).

> **Quick rule of thumb:** put the dialect program inside a `#strata` (positive)
> or `#strata_expect` (negative) block, then call one of the `testLaurel…`
> helpers in `StrataTest.Util.TestLaurel`. Use `#guard_msgs` to pin the output.

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

Use `testLaurel`. Empty diagnostics print as `ok`.

```lean
import StrataTest.Util.TestLaurel

open StrataTest.Util

/-- info: ok -/
#guard_msgs in
#eval testLaurel
#strata
program Laurel;
procedure foo() opaque { assert true };
#end
```

### 2. Negative test — assert that specific errors fire

Use `testLaurelExpect`. Annotate each expected diagnostic *inline*, on the
line directly below the offending source line, with carets pointing at the
column range and the kind + (substring of the) message after the carets:

```lean
#eval testLaurelExpect <|
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

The helper:
- parses every `// ^^^ kind: message` annotation from the snippet,
- runs the pipeline,
- requires an **exact match**: every diagnostic must be annotated, every
  annotation must fire, line/column ranges must agree, kind must match, and
  the actual message must contain the annotation text as a substring.

A mismatch throws with a precise summary of which annotations went unmatched
and which actual diagnostics had no annotation. No `#guard_msgs` wrapper is
needed for negative tests — the throw is the assertion.

`kind` is one of `error`, `warning`, `not-yet-implemented`, `strata-bug`.

### 3. Resolution-only tests — skip the verifier

When the test is about resolution (kind mismatches, duplicate names, scope
errors), running the verifier on a deliberately-broken program adds
unrelated noise (`dbg_trace` warnings, vacuous VCs). Use the resolution-only
variants:

- `testLaurelResolution` — positive (program resolves cleanly).
- `testLaurelExpectResolution` — negative (expected resolution diagnostic).

```lean
#eval testLaurelExpectResolution <|
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
/-- info: ok -/
#guard_msgs in
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
#eval! parseElimAndPrint
#strata
program Laurel;
procedure test() { var x: int := 1 + <?> };
#end

end Strata.Laurel
```

The pattern: `translateLaurel : Strata.Program → IO Laurel.Program` is the
common entry point; everything after is dialect/test-specific.

### 5. Mixed positive / negative inside one feature

When a feature has both happy and sad paths, prefer **separate** `#strata`
blocks (one driven by `testLaurel`, the other by `testLaurelExpect`). Each
one is independently checked, and a regression in one doesn't mask a
regression in the other.

```lean
/-! ### Safe paths verify cleanly -/
/-- info: ok -/
#guard_msgs in
#eval testLaurel #strata
program Laurel;
procedure safeDivision() opaque {
  var z: int := 10 / 2;
  assert z == 5
};
#end

/-! ### Unsafe division: divisor not constrained, fails verification -/
#eval testLaurelExpect <| #strata
program Laurel;
procedure unsafeDivision(x: int) opaque {
  var z: int := 10 / x
//^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end
```

If the procedures genuinely depend on each other (one calls the other), keep
them in one `#strata` block and list the union of expected diagnostics.

## Practical workflow

1. Write the `#strata` block first.
2. For positive tests, add a `/-- info: ok -/` docstring above
   `#guard_msgs in #eval testLaurel …`.
3. For negative tests, sketch placeholder annotations like `// ^ error:`
   below the offending lines — column positions don't have to be right yet.
4. Run it: `lake env lean StrataTest/Languages/Laurel/<your_file>.lean`.
5. On failure: the helper prints exactly which annotations went unmatched
   and which diagnostics had no annotation, including the line/column range
   actually produced. Copy those into your annotations, save, re-run.

When `lake env lean` exits silently with no output, every assertion in the
file held.

## Other dialects

- **Boole** uses `#strata program Boole; … #end` directly with hand-written
  helpers (e.g. `Strata.Boole.verify`); see
  [`StrataTest/Languages/Boole/find_max.lean`](../StrataTest/Languages/Boole/find_max.lean)
  for the canonical pattern. `#strata` is dialect-agnostic — Boole could use
  inline annotations the same way once a Boole-side helper analogous to
  `testLaurelExpect` is written.
- **Python** has its own pipeline-driven harness; see
  [`StrataTest/Languages/Python/README.md`](../StrataTest/Languages/Python/README.md).

## Where things live

| Concept | File |
| --- | --- |
| `#strata` elaborator + `SourcedProgram` | `Strata/DDM/Integration/Lean/HashCommands.lean` |
| `Diagnostic` data type | `Strata/Languages/Core/Verifier.lean` |
| Laurel test helpers | `StrataTest/Util/TestLaurel.lean` |
| Migrated examples | `StrataTest/Languages/Laurel/Examples/**/*.lean` |
