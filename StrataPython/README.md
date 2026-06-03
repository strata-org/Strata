# StrataPython

Python language support for Strata. This package translates Python programs into Strata's intermediate representations (Core, Laurel) for formal verification.

## Building

```bash
lake build
```

This builds the `StrataPython` library, `DiffTestCore` executable, and the `StrataPythonTest` compile-time tests.

## Package Purpose

StrataPython provides:

- **Python AST** - Types generated from the Python dialect DDM definition
- **Python-to-Laurel translation** - Translation through the Laurel IR (higher-level, supports dispatch and overloads).
- **Python-to-Core translation** - *Deprecated.* Direct translation from Python to Core IR, kept for `pyInterpret` and `pyAnalyzeToGoto`; new features should target the Laurel path
- **PySpec pipeline** - Reads Python type specifications (`.pyspec.st.ion`) and generates Laurel declarations for verification
- **Regex support** - Translates Python regular expressions to Core SMT assertions
- **Overload resolution** - Identifies and resolves dispatch-based service overloads

## Dependencies

- `Strata` (parent package) - Core IR, Laurel IR, verification infrastructure, SMT backend
- `StrataDDM` (transitive via Strata) - Dialect Definition Mechanism, Ion format

## File Structure

```
StrataPython/
├── StrataPython.lean              # Public API (readPythonIon, pySpecsDir, pyTranslateLaurel, etc.)
├── StrataPython/
│   ├── PythonDialect.lean         # DDM dialect definition + generated types (expr, stmt, etc.)
│   ├── PythonIdent.lean           # Module-qualified Python identifiers
│   ├── ReadPython.lean            # Read Python AST from Ion format
│   ├── PythonToCore.lean          # Direct Python → Core translation
│   ├── PythonToLaurel.lean        # Python → Laurel translation (main pipeline)
│   ├── PySpecPipeline.lean        # PySpec reading, overload resolution, Laurel construction
│   ├── PyFactory.lean             # Core expression factory with regex support
│   ├── CorePrelude.lean           # Python Core runtime prelude
│   ├── PythonLaurelCorePrelude.lean  # Laurel-translated runtime prelude
│   ├── PythonRuntimeLaurelPart.lean  # Runtime support as Laurel declarations
│   ├── PythonLaurelTypedExpr.lean    # Type-tagged Laurel expression builders
│   ├── FunctionSignatures.lean    # Function signature types for Core translation
│   ├── OverloadTable.lean         # Overload dispatch table
│   ├── Specs.lean                 # PySpec file reading, module discovery, translation
│   ├── Specs/
│   │   ├── DDM.lean               # PySpec DDM dialect and serialization
│   │   ├── Decls.lean             # PySpec type declarations (SpecType, FunctionDecl, etc.)
│   │   ├── IdentifyOverloads.lean # AST walker for overload resolution
│   │   ├── MessageKind.lean       # Pipeline message classification
│   │   └── ToLaurel.lean          # PySpec → Laurel translation
│   ├── Regex/
│   │   ├── ReParser.lean          # Python regex parser
│   │   └── ReToCore.lean          # Regex → Core SMT translation
│   └── Pipeline/
│       └── PyAnalyzeLaurel.lean   # Full analysis pipeline (Python → Laurel → Core → SMT)
├── StrataPythonTest/              # Compile-time tests (built with lake build)
├── StrataPythonTestExtra/         # Runtime tests (run with lake test, require Python)
├── DiffTestCore.lean              # Regex differential testing tool
├── StrataTestMain.lean            # Test driver for StrataPythonTestExtra
├── lakefile.toml
├── lean-toolchain
└── lake-manifest.json
```

## Testing

### Compile-time tests (no Python required)

```bash
lake build StrataPythonTest
```

### Runtime tests (require `pip install Tools/Python`)

```bash
PYTHON=python lake test
```

### Regex differential tests

```bash
cd StrataPythonTest/Regex
python diff_test.py
```

## Key Namespaces

| Namespace | Contents |
|-----------|----------|
| `StrataPython` | Public API, generated AST types (expr, stmt, etc.), Core translation |
| `StrataPython.ToLaurel` | Python-to-Laurel translation internals |
| `StrataPython.Specs` | PySpec reading, translation, module discovery |
| `StrataPython.Specs.ToLaurel` | PySpec-to-Laurel declaration generation |
| `StrataPython.Specs.IdentifyOverloads` | Overload resolution AST walker |
| `StrataPython.Laurel` | Type-tagged Laurel expression builders |
| `StrataPython.Pipeline` | Full pyAnalyzeLaurel pipeline |
