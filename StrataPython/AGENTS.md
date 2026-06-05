# AGENTS.md - StrataPython

Guide for AI agents working with the StrataPython package.

For purpose, file structure, namespace table, and dependencies, see
[`README.md`](./README.md). The notes below cover only the conventions and
workflows that aren't obvious from reading the code.

## Architecture: which translation path?

There are two Python-to-IR pipelines:

1. **Through Laurel** (`PythonToLaurel.lean` + `PySpecPipeline.lean`) — main
   pipeline. Combines Python source with PySpec type specifications, resolves
   overloads, and produces typed Laurel that compiles to Core. Used by
   `pyAnalyzeLaurel`. **All new work should target this path.**
2. **Direct to Core** (`PythonToCore.lean`) — **deprecated.** Bypasses Laurel.
   Still used by `pyInterpret` and `pyAnalyzeToGoto`, but lacks PySpec /
   overload support. Do not extend this path; if you need new behavior here,
   consider porting the consumer to the Laurel path instead.

## Convention: `open Strata` pattern

Since StrataPython was extracted from the `Strata` package, many files use
`open Strata` to access `Core.*`, `Laurel.*`, `Pipeline.*`, `DL.*`, and utility
types like `SourceRange`, `FileRange`, `DiagnosticModel`. When adding new
files, include `open Strata` (and possibly `open Strata.Pipeline`) if you
reference any of these.

The pipeline orchestration framework (`PipelineM`, `MessageKind`,
`PipelineContext`, `withPhase`, `emitMessageAndAbort`) lives in
`Strata.Pipeline`. The Python-specific pipeline entry points
(`runPyAnalyzePipeline`, `PyAnalyzeOutcome`, `PyAnalyzeConfig`) live in
`StrataPython.Pipeline`.

## How to add a Python translation feature

1. If it's a new expression/statement handler, modify `PythonToLaurel.lean`
   (the Laurel path is the only one taking new work — see Architecture above).
2. If it's a new PySpec feature (new type form, new declaration kind), modify
   `Specs/Decls.lean` for the data type and `Specs/ToLaurel.lean` for the
   translation.
3. Add compile-time tests in `StrataPythonTest/` (no Python dependency).
4. Add runtime integration tests in `StrataPythonTestExtra/` (requires Python +
   `strata.gen`).

## How to add a regex feature

1. Add parsing in `Regex/ReParser.lean` (extends `ReToken` / `ReAST`).
2. Add Core SMT translation in `Regex/ReToCore.lean`.
3. Add test cases to `StrataPythonTest/Regex/ReToCoreTests.lean` and corpus
   entries in `StrataPythonTest/Regex/diff_test.py`.

## DDM-generated types

`PythonDialect.lean` uses `#load_dialect` and `#strata_gen Python` to generate
the Python AST types at compile time from
`Tools/Python/dialects/Python.dialect.st.ion`. Key generated types:

- `StrataPython.expr` — Python expressions
- `StrataPython.stmt` — Python statements
- `StrataPython.keyword`, `StrataPython.alias`, `StrataPython.constant`, etc.
- `StrataPython.Python` — the dialect constant (for Ion serialization)
- `StrataPython.Python_map` — dialect map for program parsing

These live in the `StrataPython` namespace. The `#strata_gen Python` macro
also creates a `Python` sub-namespace for the dialect constant itself, so
`StrataPython.Python.toIon` and friends are valid.

## Common code patterns

### Reading a Python Ion file

```lean
let bytes ← StrataDDM.Util.readBinInputSource path
match StrataPython.readPythonStrataBytes path bytes with
| .ok stmts => ...
| .error msg => ...
```

### Running the full Laurel pipeline

```lean
let (outcome, stats, pctx) ← StrataPython.Pipeline.runPyAnalyzePipeline {
  filePath, specDir, dispatchModules, pyspecModules, verifyOptions, ...
}
```

### Translating PySpec to Laurel

```lean
let { program, errors, overloads, ... } :=
  StrataPython.Specs.ToLaurel.signaturesToLaurel filepath sigs moduleName
```
