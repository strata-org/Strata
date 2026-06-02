# AGENTS.md - StrataPython

Guide for AI agents working with the StrataPython package.

## Package Purpose

StrataPython translates Python programs into Strata's intermediate representations (Core, Laurel) for formal verification. It handles the full pipeline from Python AST parsing through type specification (PySpec) resolution to SMT-based property checking.

## Architecture

### Translation Pipelines

There are two main translation paths:

1. **Direct to Core** (`PythonToCore.lean`): Simpler, bypasses Laurel. Used for `pyInterpret` and `pyAnalyzeToGoto`.
2. **Through Laurel** (`PythonToLaurel.lean` + `PySpecPipeline.lean`): Main pipeline. Combines Python source with PySpec type specifications, resolves overloads, and produces typed Laurel that compiles to Core. Used for `pyAnalyzeLaurel`.

### DDM-Generated Types

`PythonDialect.lean` uses `#load_dialect` and `#strata_gen Python` to generate the Python AST types at compile time from `Tools/Python/dialects/Python.dialect.st.ion`. Key generated types:

- `StrataPython.expr` - Python expressions
- `StrataPython.stmt` - Python statements
- `StrataPython.keyword`, `StrataPython.alias`, `StrataPython.constant`, etc.
- `StrataPython.Python` - The dialect constant (for Ion serialization)
- `StrataPython.Python_map` - Dialect map for program parsing

These live in the `StrataPython` namespace. The `#strata_gen Python` macro also creates a `Python` sub-namespace for the dialect constant itself.

### PySpec System

PySpec files (`.pyspec.st.ion`) describe the type signatures of Python libraries. The pipeline:

1. `Specs.lean` - Reads PySpec Ion files, discovers modules, manages translation
2. `Specs/DDM.lean` - PySpec DDM dialect and serialization
3. `Specs/Decls.lean` - Type system (`SpecType`, `FunctionDecl`, `ClassDef`, etc.)
4. `Specs/ToLaurel.lean` - Translates PySpec signatures into Laurel procedures and types
5. `Specs/IdentifyOverloads.lean` - Walks Python AST to find which overloaded services are used

### Namespace Structure

| Namespace | Where defined | Purpose |
|-----------|---------------|---------|
| `StrataPython` | Most files | Main namespace for public API and AST types |
| `StrataPython.ToLaurel` | `PythonToLaurel.lean` | Python→Laurel translation (separate to avoid name collision with `PythonToCore`) |
| `StrataPython.Specs` | `Specs.lean` | PySpec reading and module management |
| `StrataPython.Specs.ToLaurel` | `Specs/ToLaurel.lean` | PySpec→Laurel declaration generation |
| `StrataPython.Specs.IdentifyOverloads` | `Specs/IdentifyOverloads.lean` | Overload resolution |
| `StrataPython.Laurel` | `PythonLaurelTypedExpr.lean` | Type-safe Laurel expression builders |
| `StrataPython.ModuleName` | `Specs.lean` | Module path utilities |
| `Strata.Pipeline` | `Pipeline/PyAnalyzeLaurel.lean` | Pipeline orchestration (kept in Strata namespace for CLI compatibility) |

### Important: `open Strata` Pattern

Since StrataPython was extracted from the `Strata` package, many files use `open Strata` to access `Core.*`, `Laurel.*`, `Pipeline.*`, `DL.*`, and utility types like `SourceRange`, `FileRange`, `DiagnosticModel`. When adding new files, include `open Strata` if you reference any of these.

## How to Add a New Python Translation Feature

1. If it's a new expression/statement handler, modify `PythonToLaurel.lean` (for Laurel pipeline) or `PythonToCore.lean` (for direct-to-Core).
2. If it's a new PySpec feature (new type form, new declaration kind), modify `Specs/Decls.lean` for the data type and `Specs/ToLaurel.lean` for the translation.
3. Add compile-time tests in `StrataPythonTest/` (no Python dependency needed).
4. Add runtime integration tests in `StrataPythonTestExtra/` (requires Python + `strata.gen`).

## How to Add a New Regex Feature

1. Add parsing in `Regex/ReParser.lean` (extends the `ReToken` / `ReAST` types).
2. Add Core SMT translation in `Regex/ReToCore.lean`.
3. Add test cases to `StrataPythonTest/Regex/ReToCoreTests.lean` and corpus entries in `StrataPythonTest/Regex/diff_test.py`.

## Testing

### Compile-time tests (no external dependencies)

```bash
lake build StrataPythonTest
```

These use `#eval` and `#guard_msgs` to verify translation correctness at Lean elaboration time.

### Runtime tests (require Python strata libraries)

```bash
pip install ../Tools/Python  # from StrataPython directory
PYTHON=python lake test
```

The test runner (`StrataTestMain.lean`) discovers `.lean` files in `StrataPythonTestExtra/` and runs each via `lean`. These tests invoke the Python `strata.gen` tool to compile `.py` files to `.python.st.ion` before analysis.

### Shell-based golden-file tests

```bash
cd StrataPythonTest
./run_py_analyze.sh           # Compare analysis output against expected_laurel/
./run_py_interpret.sh         # Compare interpreter output against expected_interpret/
python run_py_analyze_sarif.py --laurel  # SARIF output validation
```

### Regex differential tests

```bash
cd StrataPythonTest/Regex
python diff_test.py
```

Runs 534 regex test cases through both Python's `re` module and Strata's `DiffTestCore` tool, reporting discrepancies.

## Dependencies

This package imports from:
- `Strata` - Core/Laurel IRs, verification, transforms, SMT, pipeline infrastructure
- `StrataDDM` (transitive) - Dialect definitions, Ion format, source ranges

Key imports:
- `Strata.Languages.Core.*` - Core IR types, factory, verifier, environment
- `Strata.Languages.Laurel.*` - Laurel AST, compilation pipeline, grammar
- `Strata.DL.Lambda.Factory` - Lambda expression factory
- `Strata.Pipeline.*` - Pipeline context, messages, diagnostics
- `StrataDDM.*` - AST, Ion, source ranges, integration utilities

## Common Patterns

### Reading a Python Ion file
```lean
let bytes ← StrataDDM.Util.readBinInputSource path
match StrataPython.readPythonStrataBytes path bytes with
| .ok stmts => ...
| .error msg => ...
```

### Running the full Laurel pipeline
```lean
let (outcome, stats, pctx) ← Strata.Pipeline.runPyAnalyzePipeline {
  filePath, specDir, dispatchModules, pyspecModules, verifyOptions, ...
}
```

### Translating PySpec to Laurel
```lean
let { program, errors, overloads, ... } :=
  StrataPython.Specs.ToLaurel.signaturesToLaurel filepath sigs moduleName
```
