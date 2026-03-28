# Python Static Analysis (`jhx/python-static`)

This branch adds tooling for static analysis of Python programs via SSA
(Static Single Assignment) intermediate representation, built on Strata's
existing Python DDM AST infrastructure.

## Subcommands

### `strata pyFeatures <file>`

Analyzes a `.python.st.ion` file and prints constructor usage statistics,
grouped by syntactic category (statements, expressions, constants, operators,
etc.). Used for corpus-driven scope analysis — understanding which Python
features the target files actually use before designing the IR.

```
strata pyFeatures path/to/file.python.st.ion
```

### `strata pyToSSA <file>` *(planned)*

Translates a `.python.st.ion` file to PythonSSA and prints the SSA IR to
stdout. Covers 46/52 corpus files (everything except comprehensions).

## Files

### Lean sources

| File | Description |
|------|-------------|
| `Strata/Languages/Python/FeatureUsage.lean` | AST traversal that tallies every Python constructor encountered |
| `Strata/Languages/Python/SSA.lean` | *(planned)* SSA IR data types (PyType, Block, Func, Module) |
| `Strata/Languages/Python/SSAFormat.lean` | *(planned)* Pretty-printer for SSA IR |
| `Strata/Languages/Python/PythonToSSA.lean` | *(planned)* Translation from Python DDM AST to SSA IR |

### Documentation

| File | Description |
|------|-------------|
| `docs/PythonSSA.md` | Reference manual for the PythonSSA IR — data types, desugaring rules, well-formedness invariants, pretty-print notation |
| `experiment_report.md` | Methodology report describing the data-driven, AI-assisted design process |

### Analysis scripts

| File | Description |
|------|-------------|
| `tally_features.py` | Aggregates `pyFeatures` output across multiple files and sorts by frequency |
| `coverage_check.py` | Computes how many corpus files a given feature subset covers |

## Design overview

The IR uses **block arguments** (Crucible/SWIFT style) instead of phi nodes,
with **per-instruction exception precision** via `exceptArgs` and an
**`undef`/`isDefined` pattern** for tracking variable initialization across
control flow paths. See `docs/PythonSSA.md` for the full specification.
