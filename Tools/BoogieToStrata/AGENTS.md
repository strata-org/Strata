# AGENTS.md — BoogieToStrata

Guidelines for AI agents working on the BoogieToStrata translator.

## Tool Purpose

BoogieToStrata translates Boogie verification language (`.bpl`) files into Strata Core (`.core.st`) programs. It is a C# .NET 8 console application that uses the official Boogie library (`Boogie.ExecutionEngine 3.5.2`) for parsing and type-checking, then walks the resolved AST to emit Strata Core syntax.

## Architecture

```
Source/
├── BoogieToStrata.cs      # CLI entry point, arg parsing, Boogie pipeline setup
└── StrataGenerator.cs     # AST visitor that emits Strata Core text (~2100 lines)
```

### Key Classes

| Class | Role |
|-------|------|
| `BoogieToStrata` | `Main` entry point. Parses args, configures Boogie options, invokes parse → resolve → typecheck → emit pipeline. |
| `StrataGenerator` | Extends `ReadOnlyVisitor`. Walks the Boogie AST and writes Strata Core to a `TokenTextWriter`. Contains all translation logic. |
| `StrataConversionException` | Thrown for unsupported constructs. Includes source location. |
| `LoopRegion` | Data structure for detected loop regions (back-edge analysis). |
| `FieldTypeCollector` | Visitor that collects types used with Field constructors (for heap modeling). |

### Data Flow

```
.bpl file → Boogie parser → Boogie AST (Program)
         → ResolveAndTypecheck
         → InferAndVerify (with UseResolvedProgram hook)
         → StrataGenerator.EmitProgramAsStrata
             → FindSpecialTypes (Ref/Field/Heap detection)
             → ClaimOrRename (collision resolution)
             → Emit: types → constants → functions → axioms → procedures → implementations
         → stdout (Strata Core text)
```

## Key Design Decisions

### Global Variables as Parameters

Boogie globals are not emitted as `var` declarations. Instead:
- Modified globals (`modifies` clause) → `inout` parameters on procedures
- Read-only globals → regular input parameters
- Call sites prepend global arguments in the same order

This is handled by `WriteProcedureHeader` and `VisitCallCmd`.

### Name Collision Resolution

Boogie allows different declaration kinds to share names (e.g., a procedure and a constant both named `main`). The translator:
1. Sanitizes all names (`@.#^$` → `_`)
2. Claims names in priority order: procedures > implementations > constants > functions > globals
3. Colliding declarations get prefixed (`__proc_`, `__const_`, `__func_`, `__var_`)

Stored in `_renames` dictionary, keyed by `Declaration` object. Always use `NameOf(decl, name)` to get the correct output name.

### Control Flow Translation

The translator handles two modes:

**Structured** (BigBlocks with `IfCmd`/`WhileCmd`/`BreakCmd`):
- Emitted directly as `if`/`while`/`exit` in Strata Core

**Unstructured** (goto/labels):
- Forward gotos → labeled wrapper blocks with `exit <label>`
- Back-edges → detected via `DetectBackEdges`, emitted as `while (true)` loops
- Two-target gotos with opposite assumes → `if/else`
- Nested loops → recursive `EmitLoopRegion`
- Irreducible control flow → rejected with `StrataConversionException`

### Heap Pattern Recognition

When the program uses the Ref/Field/Heap idiom (common in SMACK):
- `_refTypeCtor` — type constructor for references
- `_fieldTypeCtor` — type constructor for fields (arity 1)
- `_heapTypeSyn` — type synonym for the heap map

Map operations on these types are emitted as `StrataHeapSelect_<type>` / `StrataHeapUpdate_<type>` calls.

### SMACK Mode (`--smack`)

Gated by the `_smack` field:
1. `InferModifies = true` on Boogie options (infers missing modifies clauses)
2. Procedures matching `assert_.<type>(p)` get synthetic `requires (p != 0)`

## Before Making Changes

1. **Read `StrataGenerator.cs` thoroughly** — it's one large file with all translation logic
2. **Understand the visitor pattern** — `StrataGenerator` extends Boogie's `ReadOnlyVisitor`; override `Visit*` methods to handle each AST node
3. **Check existing tests** — look for a `.bpl` file that exercises similar constructs
4. **Understand the output format** — read `Strata/Languages/Core/` in the main Strata package to understand what valid Core syntax looks like

## Common Tasks

### Adding support for a new Boogie construct

1. Identify the Boogie AST node type (check [Boogie source](https://github.com/boogie-org/boogie))
2. Add a `Visit*` or handle the case in the appropriate `switch` in `StrataGenerator.cs`
3. If unsupported, throw `StrataConversionException` with a clear message
4. Add a test `.bpl` file in `Tests/`
5. Generate the `.expect` file by running through the full pipeline

### Adding a new test

1. Create `Tests/<Name>.bpl` with the Boogie program
2. Run translation: `dotnet run --project Source -- Tests/<Name>.bpl > /dev/null` (check exit code)
3. For verification tests, generate expected output:
   ```bash
   dotnet run --project Source -- Tests/<Name>.bpl > Tests/<Name>.core.st
   ../../.lake/build/bin/strata verify Tests/<Name>.core.st > Tests/<Name>.expect
   rm Tests/<Name>.core.st
   ```
4. Run `dotnet test IntegrationTests/` to confirm

### Fixing a translation bug

1. Create a minimal `.bpl` reproducer
2. Run the translator and inspect the output Strata Core
3. Compare against what valid Core syntax should look like (check `Strata/Languages/Core/`)
4. Fix the emission logic in `StrataGenerator.cs`
5. Add the reproducer as a regression test with `.expect` file

### Fixing a name collision bug

1. Check the `ClaimOrRename` logic and registration order
2. The `_renames` dictionary maps `Declaration` → renamed string
3. Always use `NameOf(decl, originalName)` — never `Name(originalName)` alone for declarations
4. Add a test like `NamespaceCollision.bpl` or `OldExprRenameCollision.bpl`

## Testing

### Running Tests

```bash
# Build and run all integration tests
./run-integration-tests.sh

# Or directly
dotnet test IntegrationTests/BoogieToStrata.IntegrationTests.csproj

# Run a specific test
dotnet test IntegrationTests/ --filter "TranslateTestFileWithoutErrors(Gauss.bpl)"
```

### Test Structure

The integration tests have two parameterized test methods per `.bpl` file:
- `TranslateTestFileWithoutErrors` — translation succeeds (exit code 0, non-empty output)
- `VerifyTestFile` — translated output passes Strata verification (matches `.expect` if present)

Plus specific regression tests as `[Fact]` methods.

### Test Conventions

- `.bpl` files in `Tests/` are derived from the [Boogie test suite](https://github.com/boogie-org/boogie/tree/master/Test)
- `.expect` files contain the exact expected stdout from `strata verify`
- Files with `{:smack}` in the first 5 lines trigger `--smack` mode in tests
- `.boogie.st` / `.out` / `.err` files are generated artifacts (gitignored)

## Build Commands

```bash
# Build the translator
dotnet build Source/BoogieToStrata.csproj

# Run the translator
dotnet run --project Source -- <file.bpl>
dotnet run --project Source -- --smack <file.bpl>

# Run integration tests
dotnet test IntegrationTests/BoogieToStrata.IntegrationTests.csproj

# Batch translate all test files
./translate-all.sh
```

## Important Patterns in StrataGenerator.cs

### Emission Helpers

- `WriteText(s)` — write raw text (no newline)
- `WriteLine(s)` — write text + newline
- `Indent(s)` — write with current indentation
- `IndentLine(s)` — indent + newline
- `IncIndent()` / `DecIndent()` — manage indentation level
- `EmitSeparated(items, action, sep)` — emit items with separator
- `Name(s)` — sanitize a name string
- `NameOf(decl, s)` — get the (possibly renamed) output name for a declaration

### State Fields

- `_indentLevel` — current output indentation
- `_globalVariables` — collected globals (used for parameter generation)
- `_renames` — collision rename map
- `_uniqueConstants` — tracks unique constants for axiom generation
- `_userAxiomNames` — tracks emitted axiom names (for uniqueness)
- `_breakLabels` — stack of break target labels (for while loops)
- `_enclosingLabels` — set of currently open wrapper block labels
- `_refTypeCtor`, `_fieldTypeCtor`, `_heapTypeSyn` — detected heap types
- `_smack` — SMACK mode flag

### Emission Order

The generator emits declarations in this fixed order:
1. Header (`program Core;` + built-in type declarations)
2. Type constructors
3. Type synonyms
4. Constants
5. Heap functions (if Field types detected)
6. Functions
7. Unique constant axioms
8. User axioms
9. Procedures (without bodies)
10. Implementations (with bodies)

## Pitfalls

- **Always use `NameOf(decl, name)` for declarations** — using `Name(name)` directly will miss renames and produce incorrect output for collision cases.
- **The Boogie AST is post-resolution** — `IdentifierExpr.Decl` should always be non-null. If it's null, something went wrong in Boogie's resolution pass.
- **`old()` expressions need special handling** — `EmitOldExpr` distributes `old` inward through map accesses. Don't emit `old(complex_expr)` directly.
- **Back-edge detection excludes `_exit`** — the synthetic exit label represents procedure return, not a loop target.
- **Integration tests require the `strata` binary** — build the main Strata package first (`lake build` in repo root).
- **The `.expect` files are exact-match** — any change to output formatting (whitespace, label names) will break tests. Update `.expect` files when intentionally changing output format.
- **Map store with 4 args** — Boogie can produce 4-argument MapStore for nested maps. The translator handles this by emitting nested select+store.
