# BoogieToStrata

BoogieToStrata is a C# command-line tool that translates [Boogie](https://github.com/boogie-org/boogie) source files (`.bpl`) into Strata Core programs (`.core.st`). It uses the official Boogie frontend for parsing and type-checking, then emits equivalent Strata Core syntax that can be verified by the Strata toolchain.

## Overview

The translator handles most of the Boogie language including:

- Procedures with requires/ensures/modifies contracts
- Structured control flow (if/else, while loops, break)
- Unstructured control flow (goto with forward jumps, back-edge detection for loop recovery)
  - Currently, irreducible CFGs that cannot be translated to structured loops are unsupported
- Types: bool, int, real, bitvectors, maps, user-defined type constructors and synonyms
- Expressions: quantifiers (forall/exists) with triggers, lambda, let, old, map select/store
- Bitvector operations (concat, extract, arithmetic, comparisons)
- Constants (including unique constraints), axioms, pure functions with bodies
- Heap modeling (Ref/Field/Heap pattern recognition and translation)
- SMACK-generated Boogie (via `--smack` flag)

## Project Structure

```
Tools/BoogieToStrata/
├── BoogieToStrata.sln              # Visual Studio solution
├── Source/
│   ├── BoogieToStrata.csproj       # Main project
│   ├── BoogieToStrata.cs           # CLI entry point (arg parsing, Boogie pipeline invocation)
│   └── StrataGenerator.cs          # Core translation logic (Boogie AST → Strata Core text)
├── IntegrationTests/
│   ├── BoogieToStrata.IntegrationTests.csproj  # xUnit test project
│   └── BoogieToStrataIntegrationTests.cs       # Translation + verification tests
├── Tests/                          # Test inputs (.bpl) and expected outputs (.expect)
├── EqualizerTests/                 # Additional regression tests (Equalizer-derived)
├── run-integration-tests.sh        # Build + run integration tests
└── translate-all.sh                # Batch-translate all .bpl files
```

## Prerequisites

- [.NET 8 SDK](https://dotnet.microsoft.com/download/dotnet/8.0)
- The Strata `strata` binary (built via `lake build` in the repo root) — needed for integration tests that verify translated output

## Building

```bash
# From Tools/BoogieToStrata/
dotnet build Source/BoogieToStrata.csproj
```

The built executable lands in `Source/bin/Debug/net8.0/BoogieToStrata.dll`.

## Usage

```bash
# Basic translation (output goes to stdout)
dotnet Source/bin/Debug/net8.0/BoogieToStrata.dll <input.bpl> > output.core.st

# SMACK mode (infers modifies clauses, injects assert preconditions)
dotnet Source/bin/Debug/net8.0/BoogieToStrata.dll --smack <input.bpl> > output.core.st
```

The tool:
1. Parses the Boogie file using the official Boogie parser
2. Resolves and type-checks the program
3. Emits Strata Core syntax to stdout

Exit codes:
- `0` — success
- `1` — parse error, type-check failure, or unsupported construct

### SMACK Mode

The `--smack` flag enables two accommodations for
[SMACK](https://smackers.github.io/)-generated Boogie:

1. **InferModifies** — Boogie's ModSetCollector infers missing `modifies`
   clauses so programs without explicit clauses still type-check.

2. **Synthetic requires** — Procedures matching `assert_.<type>(p)` get an
   injected `requires (p != 0)` precondition, enabling the call-elimination pass to
   generate a VC checking the assertion condition.

Files can opt into SMACK mode in the integration tests by including `{:smack}`
in their first 5 lines.

## Translation Details

### Global Variables → Parameters

Boogie global variables are translated into procedure parameters:
- Globals in the `modifies` clause become `inout` parameters
- All other globals become read-only input parameters
- Call sites are updated to pass globals accordingly

### Control Flow Recovery

The translator handles Boogie's unstructured control flow (goto/labels) by:

1. Detecting back-edges to identify loops → emitted as `while (true)` with
   labeled blocks (though irreducible loops are currently unsupported)

2. Forward gotos → emitted as `exit <label>` within labeled wrapper blocks

3. Two-target gotos with opposite assume guards → emitted as `if/else`

### Heap Modeling

When the translator detects the Ref/Field/Heap pattern (common in SMACK and
other tools), it emits specialized `StrataHeapSelect_<type>` and
`StrataHeapUpdate_<type>` function calls instead of raw map operations.

### Name Sanitization

Boogie identifiers containing `@`, `.`, `#`, `^`, or `$` are sanitized (replaced
with `_`). When sanitization causes collisions between declarations, the
translator renames later declarations with a prefix (`__proc_`, `__const_`,
`__func_`, `__var_`). Procedures always win collisions.

## Testing

### Integration Tests

The integration test suite translates each `.bpl` file and optionally verifies the output with the Strata verifier:

```bash
# Run all integration tests
./run-integration-tests.sh

# Or directly with dotnet
dotnet test IntegrationTests/BoogieToStrata.IntegrationTests.csproj
```

Each test:
1. Translates the `.bpl` file to Strata Core
2. If a `.expect` file exists: runs `strata verify` and compares output to the expected results
3. If no `.expect` file exists: runs `strata verify --check` (parse + type-check only)

### Test File Format

- `Tests/<Name>.bpl` — Boogie input file
- `Tests/<Name>.expect` — Expected verification output (optional; if absent, only type-checking is tested)

### Adding a New Test

1. Create `Tests/<Name>.bpl` with the Boogie program
2. Run the translator manually to verify it works:
   ```bash
   dotnet Source/bin/Debug/net8.0/BoogieToStrata.dll Tests/<Name>.bpl
   ```
3. If the program should verify, run it through Strata and capture the expected output:
   ```bash
   dotnet Source/bin/Debug/net8.0/BoogieToStrata.dll Tests/<Name>.bpl > Tests/<Name>.core.st
   ../../.lake/build/bin/strata verify Tests/<Name>.core.st > Tests/<Name>.expect
   rm Tests/<Name>.core.st
   ```
4. Run the integration tests to confirm everything passes

### Batch Translation

To translate all test files at once (useful for inspecting output):

```bash
./translate-all.sh
```

This produces `.boogie.st` files alongside each `.bpl` input.

## Known Limitations

- Datatypes are not yet supported (throws `StrataConversionException`)
- Irreducible control flow (overlapping loop regions) is rejected
- Multi-target gotos (3+ targets) are not supported unless they can be decomposed
- Real constants have limited support

## License

Apache-2.0 OR MIT
