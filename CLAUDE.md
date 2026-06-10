# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What is Strata?

Strata is an extensible intermediate verification language platform built in Lean 4. It provides a family of composable *dialects* (inspired by MLIR) for formalizing language syntax and semantics, and implementing automated reasoning applications (deductive verification, bug-finding, symbolic execution). It currently targets capabilities similar to the Boogie Intermediate Verification Language, with a pipeline to SMT solvers (cvc5, z3).

## Build Commands

```bash
# Full build + elaboration-time tests (no output = pass)
lake build

# Run uncached extra tests (StrataTestExtra/)
lake test

# Run specific test subsets
lake test -- Languages.Python          # only Python tests
lake test -- --exclude Languages.Python  # everything except Python

# Build executables only (skip proof checking)
lake build strata:exe strata StrataToCBMC StrataCoreToGoto

# Build sub-packages (each is its own Lake workspace)
cd StrataDDM && lake build
cd StrataCLI && lake build
cd StrataPython && lake build
cd StrataBoole && lake build

# Run the linter (import checker)
lake lint

# Run verifier on a Strata program
cd StrataCLI && lake exe strata verify ../Examples/SimpleProc.core.st
```

## Project Structure (Lake Workspaces)

The repo contains multiple Lake packages with dependency relationships:

- **Root (`Strata`)** — Core library: dialects, transforms, VCG, backends, pipeline. Default targets: `Strata`, `StrataToCBMC`, `StrataCoreToGoto`.
- **`StrataDDM/`** — Dialect Definition Mechanism (standalone, no dependency on `Strata`). Provides the embedded DSL for defining dialect syntax/typing rules, parser generation, Ion serialization.
- **`StrataCLI/`** — The `strata` command-line tool. Depends on `Strata`. Entry point: `StrataMain.lean`.
- **`StrataPython/`** — Python front-end: translates Python Ion → Laurel → Core. Depends on `Strata`.
- **`StrataBoole/`** — Boolean satisfiability dialect. Depends on `Strata`.

Build order: `StrataDDM` → root `Strata` → `StrataCLI` / `StrataPython` / `StrataBoole`.

## Architecture

### Dialect Library (`Strata/DL/`)

The semantic building blocks that dialects compose. Each is heavily parameterized:

- **Lambda** (`DL/Lambda/`) — Pure typed expression language (`LExpr`, `LTy`, `LMonoTy`). Parameterized by `LExprParams` (metadata + identifier types) and a `Factory` (operation signatures + optional denotations). The Factory mechanism lets you extend type checking and evaluation for new operations without modifying core ASTs.
- **Imperative** (`DL/Imperative/`) — Control flow: `Cmd` (atomic commands), `Stmt` (structured statements), `KleeneStmt` (unstructured/guarded). Parameterized by a `PureExpr` structure (provides Expr/Ty/Ident types). Includes VCG via symbolic simulation and an inductive operational semantics.
- **SMT** (`DL/SMT/`) — SMT-Lib encoding: `Encoder`, `Solver` (process-based), `IncrementalSolver`, `AbstractSolver`. Translates Lambda expressions to SMT-Lib format.

### Languages (`Strata/Languages/`)

Concrete instantiations of the dialect building blocks:

- **Core** — Boogie-like IVL: procedures with contracts, global/local variables, axioms, abstract types. Specializes `Imperative` + `Lambda` with `CoreIdent` (scoped identifiers) and `CoreOp` (structured operator types). The primary verification target.
- **Laurel** — Higher-level IVL for Java/Python/JS. Compiled to Core via `LaurelCompilationPipeline.lean`. Compilation involves: desugaring → heap parameterization → type alias elimination → resolution → translation to Core.
- **C_Simp** — Simplified C-like language for demonstrating dialect construction.
- **B3** — Boolean/bitvector dialect with its own verifier.
- **Dyn** — Dynamically-typed dialect.

### Transforms (`Strata/Transform/`)

Program transformations with optional correctness proofs (files ending in `Correct.lean`):
`LoopElim`, `CallElim`, `ProcedureInlining`, `FilterProcedures`, `DetToKleene`, `StructuredToUnstructured`, `ProcBodyVerify`, `ANFEncoder`, etc.

Transforms run inside `CoreTransformM` (a state+except monad carrying `CoreTransformState` for fresh name generation, call graph caching, and statistics). Multiple transforms can be chained via `Core.runTransforms` which threads state across phases.

### Pipeline (`Strata/Pipeline/`)

Verification pipeline infrastructure: `PipelineContext` (telemetry), `PipelineMessage` (diagnostics with severity/phase/location), `DiagnosticModel`.

### Backends (`Strata/Backends/`)

- **CBMC** — Translation to CProver GOTO format (JSON) for model-checking with CBMC.

### Key Design Patterns

- **`PureExpr` structure**: The abstraction boundary between expressions and statements. Any language instantiates this to plug its expression/type system into the imperative framework.
- **`PipelinePhase`**: Couples a transform with its `ModelValidation` annotation (model-preserving vs. needs-validation). Adding a transform requires specifying its soundness annotation.
- **DDM flow**: Text → generic `StrataDDM.Program` AST → dialect-specific AST (e.g., `Core.Program`). The generic AST enables serialization/deserialization across languages; dialect-specific ASTs enable concise analysis.

### Verification Flow

A typical deductive verification path:
1. Parse `.st` file (dialect inferred from extension: `.core.st`, `.csimp.st`, `.laurel.st`)
2. Type-check and elaborate
3. Apply transforms (loop elimination, inlining, etc.)
4. Generate verification conditions via symbolic simulation (VCG)
5. Encode VCs to SMT-Lib
6. Invoke SMT solver (cvc5/z3)
7. Report results (text or SARIF)

### CLI Commands

The `strata` binary (built from `StrataCLI/`) provides subcommands grouped as:
- **Core**: `verify`, `transform`, `check`, `toIon`, `print`, `diff`
- **Code Generation**: `javaGen`
- **Python**: `pyAnalyzeLaurel`, `pyResolveOverloads`, `pySpecs`, etc.
- **Laurel**: `laurelAnalyze`, `laurelToCore`, `laurelParse`, `laurelPrint`, etc.

Exit codes: 0=success, 1=user error, 2=failures found, 3=internal error, 4=known limitation.

## Testing

- **Elaboration-time tests** (`StrataTest/`): Use `#guard_msgs` — run during `lake build`. No output = pass.
- **Extra tests** (`StrataTestExtra/`): File-based tests run by `lake test`. The test driver (`Scripts/StrataTestMain.lean`) walks `StrataTestExtra/`, runs each `.lean` file, and compares output.
- Sub-packages have their own test libs (`StrataPythonTest`, `StrataDDMTest`, etc.).

## Style Conventions

- **Naming**: files `UpperCamelCase.lean`, functions `lowerCamelCase`, types `UpperCamelCase`, proofs/theorems `snake_case`.
- **Line length**: ≤80 preferred, never >100.
- **No nonterminal `simp`**: Unless `simp` closes the goal, convert to `simp only [...]`.
- **Prefer total functions**: Use `partial_fixpoint` over `partial` when non-termination is needed.
- **Error handling**: Prefer `String ⊕ T` (or similar informative error types) over `Option T`. Transforms use `EIO Transform.Err`. Pipeline errors use `DiagnosticModel`.
- **Extrinsic proofs**: Keep implementation and proof separate. Prove properties externally about executable definitions.
- **Documentation**: Every major function/theorem needs a doc comment (`/-- ... -/`). Use module docstrings (`/-! ... -/`) after imports.
- **Visibility**: Every `.lean` file starts with `module`. Use `public section` / `public import` to control API surface. Mark abbreviations and accessors with `@[expose]` for cross-module unfolding.

## Prerequisites

- **Lean 4** (version in `lean-toolchain`: v4.29.1)
- **SMT solvers**: `cvc5` and `z3` on PATH (required for tests and verification)
- **Python 3.11+**: For Python tests; install with `pip install ./Tools/Python`
- **Java JDK 11+**: For Java codegen tests
- **ion-java 1.11.11**: For DDM Java integration test (see README for download)

## Strata File Extensions

Programs use the pattern `<name>.<dialect>.st`:
- `.core.st` — Strata Core
- `.csimp.st` — C_Simp
- `.laurel.st` — Laurel
- `.b3.st` — B3

The CLI infers the dialect from this extension.
