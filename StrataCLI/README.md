# StrataCLI

The `strata` command-line interface for Strata. This package builds the main executable that users interact with to parse, transform, and analyze Strata programs.

## Building

```bash
lake build
```

This produces the `strata` executable. The package depends on the parent `Strata` library (via `lakefile.toml`).

## Usage

```bash
lake exe strata <command> [flags...]
lake exe strata --help
lake exe strata <command> --help
```

## Commands

### Core

| Command | Description |
|---------|-------------|
| `verify <file>` | Verify a Strata program (`.core.st`, `.csimp.st`, or `.b3.st`) |
| `transform <file>` | Apply one or more transforms to a Core program |
| `check <file>` | Parse and validate a Strata file |
| `toIon <input> <output>` | Convert a Strata text file to Ion binary format |
| `print <file>` | Pretty-print a Strata file to stdout |
| `diff <file1> <file2>` | Compare two program files for syntactic equality |

### Python

| Command | Description |
|---------|-------------|
| `pyAnalyzeLaurel <file>` | Verify a Python Ion program via the Laurel pipeline |
| `pyResolveOverloads <python_path> <dispatch_ion>` | Identify overloaded service modules a Python program uses |
| `pySpecs <source_dir> <output_dir>` | Translate Python spec files to DDM Ion format |
| `pySpecToLaurel <python_path> <strata_path>` | Translate a PySpec Ion file to Laurel declarations |
| `pyAnalyzeLaurelToGoto <file>` | Translate Python Ion through Laurel to GOTO JSON |
| `pyAnalyzeToGoto <file>` | Translate Python Ion directly to GOTO JSON |
| `pyTranslateLaurel <file>` | Translate Python Ion through Laurel to Core, print to stdout |
| `pyInterpret <file>` | Concretely interpret a Python Ion program |

### Laurel

| Command | Description |
|---------|-------------|
| `laurelAnalyze <file>` | Analyze a Laurel source file with verification |
| `laurelAnalyzeBinary` | Verify Laurel Ion programs from stdin |
| `laurelAnalyzeToGoto <file>` | Translate Laurel to GOTO JSON |
| `laurelParse <file>` | Parse a Laurel source file (no verification) |
| `laurelPrint` | Read Laurel Ion from stdin, print concrete syntax |
| `laurelToCore <file>` | Translate Laurel to Core, print to stdout |

### Code Generation

| Command | Description |
|---------|-------------|
| `javaGen <dialect> <package> <output-dir>` | Generate Java source files to represent the language defined by a DDM dialect |

## Common Flags

Most verification commands accept:

| Flag | Description |
|------|-------------|
| `--solver <name>` | SMT solver executable (default: cvc5) |
| `--solver-timeout <seconds>` | Solver timeout (default: 10) |
| `--verbose` | Enable verbose output |
| `--quiet` | Suppress warnings |
| `--profile` | Print elapsed time per pipeline step |
| `--sarif` | Write results as SARIF |
| `--no-solve` | Generate SMT files without invoking the solver |
| `--vc-directory <dir>` | Store VCs in SMT-Lib format |
| `--check-mode <mode>` | Verification mode (deductive, bugFinding, etc.) |
| `--incremental` | Use incremental solver backend |
| `--parallel <N>` | Number of parallel solver workers |
| `--include <path>` | Add a dialect search path |

## Exit Codes

| Code | Category | Meaning |
|------|----------|---------|
| 0 | Success | Analysis passed, inconclusive, or `--no-solve` completed |
| 1 | User error | Bad input: invalid arguments, malformed source |
| 2 | Failures found | Analysis completed and found assertion violations |
| 3 | Internal error | SMT encoding failure, solver crash, or translation bug |
| 4 | Known limitation | Intentionally unsupported language construct |

Codes 1-2 are user-actionable (fix the input or the code under analysis). Codes 3-4 are tool-side (report as a bug or wait for support).

## File Structure

```
Strata-CLI/
├── StrataMain.lean       # Entry point (dispatches to runCommandMap)
├── StrataMainLib.lean    # All command definitions, flag parsing, utilities
├── lakefile.toml         # Lake build configuration
├── lean-toolchain        # Lean version pin
└── lake-manifest.json    # Dependency lock file
```

## Examples

```bash
# Verify a Core program
lake exe strata verify program.core.st

# Verify with verbose output and custom solver timeout
lake exe strata verify --verbose --solver-timeout 30 program.core.st

# Apply transforms to a program
lake exe strata transform program.core.st --pass inlineProcedures --pass loopElim

# Inline specific procedures then filter
lake exe strata transform program.core.st \
  --pass inlineProcedures --procedures helper,util \
  --pass filterProcedures --procedures main

# Parse and validate without verification
lake exe strata check program.core.st

# Analyze Python via Laurel pipeline
lake exe strata pyAnalyzeLaurel program.python.st.ion --spec-dir ./specs
```
