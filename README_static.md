# Python Static Analysis (`jhx/python-static`)

This branch adds tooling for static analysis of Python programs via SSA
(Static Single Assignment) intermediate representation, built on Strata's
existing Python DDM AST infrastructure.

## Subcommands

### `strata pyFeatures <file>`

Analyzes a `.python.st.ion` file and prints constructor usage statistics,
grouped by syntactic category (statements, expressions, constants, operators,
etc.). Includes unresolved name analysis for identifying builtins.

```
strata pyFeatures path/to/file.python.st.ion
```

### `strata pyToSSA <file>` *(planned)*

Translates a `.python.st.ion` file to PythonSSA and prints the SSA IR to
stdout. Covers 46/52 corpus files (everything except comprehensions).

## Files

### Lean sources

| File | Status | Description |
|------|--------|-------------|
| `Strata/Languages/Python/FeatureUsage.lean` | Done | AST traversal: constructor tallying + unresolved name analysis |
| `Strata/Languages/Python/SSA.lean` | Done | SSA IR data types (PyType, SSAVal, Block, Func, Module, QualifiedName, prelude) |
| `Strata/Languages/Python/SSAFormat.lean` | Done | Pretty-printer with sugar (callQualified, call attr(), inline literals) |
| `Strata/Languages/Python/PythonToSSA.lean` | Planned | Translation from Python DDM AST to SSA IR |
| `Strata/Languages/Python/SSACheck.lean` | Planned | Well-formedness checker for SSA invariants |

### Documentation

| File | Description |
|------|-------------|
| [`docs/PythonSSA.md`](docs/PythonSSA.md) | Reference manual — data types, desugaring rules, well-formedness invariants, pretty-print notation |
| [`experiment_report.md`](experiment_report.md) | Methodology — corpus analysis, AI-assisted design process, test-driven development |

### Tests

| Directory | Description |
|-----------|-------------|
| `StrataTest/Languages/Python/SSA/tests/` | 25 Python test files (t01–t25) + 8 negative tests (n01–n08) |
| `StrataTest/Languages/Python/SSA/expected/` | Hand-crafted expected SSA output for all test files |

### Analysis scripts

| File | Description |
|------|-------------|
| `tally_features.py` | Aggregates `pyFeatures` output across multiple files and sorts by frequency |
| `coverage_check.py` | Computes how many corpus files a given feature subset covers |

## Design overview

The IR uses **block arguments** (Crucible/SWIFT style) instead of phi nodes,
with **per-instruction exception precision** via `exceptArgs` and an
**`undef`/`isDefined` pattern** for tracking variable initialization across
control flow paths. Key design choices:

- **Strict block-argument model**: no cross-block value references; all data
  flow is explicit through block parameters
- **Qualified name resolution**: imports and builtins resolved during
  translation via `QualifiedName` (e.g., `builtins.len`, `os.path.join`)
- **Graceful degradation**: unsupported constructs (comprehensions, lambda,
  etc.) produce `unsupported` instructions instead of crashing
- **`assert_` as first-class**: preserves programmer intent for verification

See [`docs/PythonSSA.md`](docs/PythonSSA.md) for the full specification.
