# Python → Laurel demos

Small, single-construct Python programs that, when run through Strata's
`pyAnalyzeLaurel` pipeline, produce Laurel programs which exhibit one Laurel
construct each. Useful as a reference when learning what shape Laurel takes
in practice.

## Layout

For each demo `NN_name` there are up to three files:

| File | What it is |
|------|------------|
| `NN_name.py` | Python source — kept as small as possible, one construct per file. |
| `NN_name.python.st.ion` | Strata's DDM/Ion form of the Python AST (intermediate). |
| `NN_name.full.laurel.st` | Raw Laurel emitted by the pipeline — includes the shared Python runtime prelude (datatypes `Any`, `Error`, `ListAny`, helpers like `PAdd`, `PEq`, `Any_to_bool`, …). Identical preamble across demos that exercise the same features. |
| `NN_name.laurel.st` | Trimmed view: only the user procedure(s), reformatted one statement per line. This is what you read first. |

## How the pipeline works

Two stages, both invoked from the repo root:

**1. Python source → Strata Ion** — uses the `strata.gen` Python tool to
walk the AST and emit Strata's structured Ion representation:

```bash
( cd Tools/Python && python3 -m strata.gen -q py_to_strata \
    --dialect dialects/Python.dialect.st.ion \
    "$src.py" "$dst.python.st.ion" )
```

**2. Ion → Laurel (+ Core)** — `strata pyAnalyzeLaurel`. With
`--keep-all-files <dir>` the pipeline writes one file per pass; the very
first file, `*.0.Initial.laurel.st`, is the raw Python-to-Laurel
translation before any Laurel-side rewrites:

```bash
.lake/build/bin/strata pyAnalyzeLaurel "$dst.python.st.ion" \
    --spec-dir /tmp/strata_specs \
    --skip-verification \
    --keep-all-files /tmp/laurel_demos_keep/$NN_name
```

`--skip-verification` stops after Laurel-to-Core translation so we don't
spend time on SMT solving — we only care about the Laurel artifact.
`--spec-dir` points at an empty directory because none of these demos
import PySpec specs.

The `0.Initial.laurel.st` file is then copied next to the `.py` as
`*.full.laurel.st`. The shorter `*.laurel.st` is produced by a small
extractor (`/tmp/extract_user_proc.py`) that drops the runtime prelude
plus the `__main__` shim and `$composite_*` stubs, then reformats each
procedure body so one statement appears per line — the raw output is one
giant single-line block per procedure, which makes it hard to read.

## What each demo exhibits

| Demo | Construct in the trimmed Laurel | Notes |
|------|-------|-------|
| `01_assign_assert` | `var x: (Core Any) := <?>;`, `x := from_int(1);`, `assert ... summary "..."` | Baseline — assignment and assertion. |
| `02_reassign` | `assert !Any..isexception(PAdd(...))` followed by `x := PAdd(...)` | Arithmetic as `PAdd` on `Any`. Strata inserts a "may-throw" check before each `P*` op. |
| `03_if_else` | `if Any_to_bool(flag) then { ... } else { ... }` | Conditional. |
| `04_while_loop` | `{ while(...) { ... }loop_continue_NN; }loop_break_NN;` | Labeled outer block — gives `break`/`continue` something to jump to. |
| `05_procedure_call` | Second procedure with `requires`/`ensures`/`opaque`, `$in_x` parameter, `LaurelResult`, `exit $body;` | Procedures get auto-generated type pre/postconditions from the Python annotations. |
| `06_nested_if` | Nested `if/else`. |
| `07_early_return` | `LaurelResult := ...; exit $body;` | `return` translates to assignment + `exit $body`. |
| `08_break_continue` | `exit loop_continue_NN;`, `exit loop_break_NN;` | `break`/`continue` are exits to the surrounding labeled block. |
| `09_block_scope` | (no nested `{ var ... }` shows up) | A locally-scoped Python `y` inside an `if` is **hoisted** to the procedure-level `var` block, so this demo doesn't actually feature inner-`var`. Kept as a documented null result. |
| `10_linear_search` | Adds `Any_len_to_Any`, `Any_get`, list literal as nested `ListAny_cons(...)`. Auxiliary `procedure ... invokeOn ... opaque ensures ...;` signatures (lemmas like `List_len_pos`) appear because lists are used. | Imperative loop with early `return` from inside the loop. |
| `11_binary_search` | Same list machinery + integer division `PFloorDiv`. | Mid-of-loop `return`, separate `if`/`else` branches updating `lo`/`hi`. |
| `12_merge_sort` | List concatenation as `PAdd` on `ListAny`, slicing as `Any_slice`, recursive procedure calls. | Three procedures (`merge`, `merge_sort`, `main`); shows recursion and list construction. |

## How the example list was chosen

I started by enumerating the Laurel surface that *Python* can elicit
(classes/heap and PySpec specs were intentionally out of scope here):
procedures, `var`, `assert`, `if/else`, `while`, procedure calls,
`return`, `break`, `continue`. Each got one minimal Python program —
small enough that the trimmed Laurel doesn't bury the construct in noise.

Two compromises were necessary:

- **Block-local `var`** (demo `09`) doesn't actually appear in the Laurel
  output: Strata hoists locally-scoped Python `y` to the procedure-level
  `var` declarations. The demo is left in as a documented null result.
- **Merge sort** uses list concatenation (`out = out + [x]`) and slicing
  rather than in-place index assignment, because `xs[i] = v` is not a
  shape the current Python frontend handles cleanly. The recursive
  divide-and-conquer structure still comes through.

The classic-algorithm trio (linear search, binary search, merge sort) was
added to show the same constructs composing into something recognisable,
and to surface the list-related Laurel machinery (`Any_len_to_Any`,
`Any_get`, `Any_slice`, `ListAny_cons`, the `List_*` lemma signatures).

## Reproducing

All demos were translated with `--skip-verification`. Each ran in
well under a second. To rebuild a single one from scratch:

```bash
NN=10_linear_search
( cd Tools/Python && python3 -m strata.gen -q py_to_strata \
    --dialect dialects/Python.dialect.st.ion \
    ../../Examples/Python/$NN.py \
    ../../Examples/Python/$NN.python.st.ion )
mkdir -p /tmp/keep/$NN
.lake/build/bin/strata pyAnalyzeLaurel \
    Examples/Python/$NN.python.st.ion \
    --spec-dir /tmp/strata_specs --skip-verification \
    --keep-all-files /tmp/keep/$NN
cp /tmp/keep/$NN/$NN.0.Initial.laurel.st Examples/Python/$NN.full.laurel.st
python3 /tmp/extract_user_proc.py Examples/Python/$NN.full.laurel.st \
    > Examples/Python/$NN.laurel.st
```

The extractor lives at `/tmp/extract_user_proc.py` (not committed). It is
a simple AST-unaware pass that scans for top-level `procedure` blocks,
skips `__main__`, `datetime_tostring_cancel`, and any `$composite_*`,
splits the body on top-level `;`, and recursively re-indents nested
`{ ... }` blocks. Move it into `Tools/` if you want it persisted.
