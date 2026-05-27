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
  inner Strata program at Lean compile time and elaborates to a `Strata.Program`
  value. Parse errors surface as Lean errors, so the LSP highlights them
  inside the block while you edit.
- `#strata_expect <dialect>; … #end` is a sibling form for **negative tests**.
  Instead of failing when the inner program has errors, it produces a
  `Strata.ExpectedBlock` that bundles whatever was parsed plus any
  parse-time diagnostics, so the test helper can run the rest of the pipeline
  and assert against the result.
- `#guard_msgs` is Lean's built-in golden-test command. Wrap an `#eval` in
  `#guard_msgs in` and pin the expected output via a `/-- info: … -/`
  docstring directly above it.

The Laurel test helpers all print diagnostics in this stable, snippet-local
format:

```
<line>:<colStart>-<colEnd>  <kind>: <message>
```

Lines are 1-indexed within the `#strata` / `#strata_expect` block, columns are
0-indexed, and `<kind>` is one of `error`, `warning`, `not-yet-implemented`,
`strata-bug`. Because positions are snippet-local, golden output is stable
even when the surrounding `.lean` file is edited.

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

Use `testLaurelExpect`. The helper prints every diagnostic, in order. Pin them
with `#guard_msgs`.

```lean
/-- info: 5:2-22  error: assertion does not hold -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
procedure unsafeDivision(x: int)
  opaque
{
  var z: int := 10 / x
};
#end
```

`testLaurelExpect` *throws* if the block produced no diagnostics. That's the
contract: a `#strata_expect` block must always trigger at least one error.
If you find yourself wanting to express "expected no errors", you want
`testLaurel` (or `testLaurelResolution`) on a `#strata` block instead.

### 3. Resolution-only tests — skip the verifier

When the test is about resolution (kind mismatches, duplicate names, scope
errors), running the verifier on a deliberately-broken program adds
unrelated noise (`dbg_trace` warnings, vacuous VCs). Use the resolution-only
variants:

- `testLaurelResolution` — positive (program resolves cleanly).
- `testLaurelExpectResolution` — negative (expected resolution diagnostic).

```lean
/-- info: 4:9-10  error: 'x' resolves to variable, but expected composite type, ... -/
#guard_msgs in
#eval testLaurelExpectResolution <|
#strata_expect
program Laurel;
procedure foo() opaque {
  var x: int := 1;
  var y: x := 2
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
and `#strata_expect` blocks. Each one is independently checked, the output
docstrings stay focused, and a regression in one doesn't mask a regression
in the other.

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
/-- info: 4:2-22  error: assertion does not hold -/
#guard_msgs in
#eval testLaurelExpect <| #strata_expect
program Laurel;
procedure unsafeDivision(x: int) opaque {
  var z: int := 10 / x
};
#end
```

If the procedures genuinely depend on each other (one calls the other), keep
them in one `#strata_expect` and list the union of expected diagnostics.

## Practical workflow

1. Write your `#strata` / `#strata_expect` block first, with a placeholder
   docstring (`/-- info: TODO -/`).
2. Build the file: `lake build StrataTest.Languages.Laurel.<your_file>`.
3. Run it: `lake env lean StrataTest/Languages/Laurel/<your_file>.lean`.
4. The `#guard_msgs` failure message will print the actual generated output.
   Copy it into your docstring, save, re-run. Empty output means tests pass.

When `lake env lean` exits silently with no output, every `#guard_msgs` in
the file held.

## Other dialects

- **Boole** uses `#strata program Boole; … #end` directly with hand-written
  helpers (e.g. `Strata.Boole.verify`); see
  [`StrataTest/Languages/Boole/find_max.lean`](../StrataTest/Languages/Boole/find_max.lean)
  for the canonical pattern. The `#strata_expect` form is dialect-agnostic
  and would also work for Boole if you need to capture parse errors there.
- **Python** has its own pipeline-driven harness; see
  [`StrataTest/Languages/Python/README.md`](../StrataTest/Languages/Python/README.md).

## Where things live

| Concept | File |
| --- | --- |
| `#strata` / `#strata_expect` elaborators | `Strata/DDM/Integration/Lean/HashCommands.lean`, `…/HashCommandsExpect.lean` |
| `ExpectedBlock` data type | `Strata/DDM/Integration/Lean/HashCommandsExpect.lean` |
| `Diagnostic` data type | `Strata/Languages/Core/Verifier.lean` |
| Laurel test helpers | `StrataTest/Util/TestLaurel.lean` |
| Migrated examples | `StrataTest/Languages/Laurel/Examples/**/*.lean` |
