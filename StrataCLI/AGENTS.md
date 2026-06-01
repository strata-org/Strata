# AGENTS.md - StrataCLI

Guide for AI agents working with the StrataCLI package.

## Package Purpose

StrataCLI is the command-line frontend for Strata. It builds the `strata` executable that orchestrates parsing, type-checking, transformation, and analysis (including SMT-based verification) of programs written in Strata dialects (Core, Laurel, Python, C_Simp, B3).

## Architecture

### File Layout

- `StrataMain.lean` - Minimal entry point. Calls `runCommandMap commandMap commandGroups args`. Do not add logic here.
- `StrataMainLib.lean` - Contains everything else: command definitions, flag parsing infrastructure, exit code constants, and helper utilities. This is the file you will modify for almost all CLI changes.
- `lakefile.toml` - Build config. Declares dependency on parent `Strata` package via `path = ".."`. Exposes `StrataMainLib` as a library and `strata` as an executable.
- `lean-toolchain` - Lean version pin (currently v4.29.1).

### Key Abstractions

**`Command`** - A CLI subcommand. Fields:
- `name : String` - subcommand name (e.g., "verify")
- `args : List String` - positional argument names (determines arity)
- `flags : List Flag` - accepted flags
- `help : String` - help text
- `callback : Vector String args.length → ParsedFlags → IO Unit` - implementation

**`Flag`** - A CLI flag definition. Fields:
- `name : String` - flag name without `--`
- `help : String` - description
- `takesArg : FlagArg` - `.none` (boolean), `.arg name` (single value), or `.repeat name` (multi-value)

**`ParsedFlags`** - Ordered array of `(String × Option String)` entries preserving command-line position. Key methods: `getBool`, `getString`, `getRepeated`, `buildDialectFileMap`.

**`CommandGroup`** - Groups commands for help display. Groups: Core, Code Generation, Python, Laurel.

**`runCommandMap`** - Top-level dispatcher. Parses the subcommand name, handles `--help`, splits flags from positional args, validates arity, then calls the command's callback.

### Exit Codes (namespace `ExitCode`)

| Constant | Value | When to use |
|----------|-------|-------------|
| (success) | 0 | Analysis passed, inconclusive, or `--no-solve` |
| `userError` | 1 | Bad CLI args, malformed source, type errors |
| `failuresFound` | 2 | Verification found assertion violations |
| `internalError` | 3 | SMT encoding bug, solver crash, translation error |
| `knownLimitation` | 4 | Unsupported language construct |

### Exit Helpers

- `exitFailure` / `exitCmdFailure` - exit 1 with message and help hint
- `exitUserError` - exit 1
- `exitFailuresFound` - exit 2
- `exitInternalError` - exit 3
- `exitKnownLimitation` - exit 4

The `pyAnalyzeLaurel` command has its own exit helpers (`exitPyAnalyze*`) that additionally emit structured `RESULT:`/`DETAIL:` lines on stdout.

## How to Add a New Command

1. Define a `Command` value in `StrataMainLib.lean`:
   ```lean
   def myNewCommand : Command where
     name := "myNew"
     args := [ "file" ]           -- positional args
     flags := [includeFlag]       -- reuse common flags as needed
     help := "Description of what this command does."
     callback := fun v pflags => do
       let file := v[0]
       -- implementation here
   ```

2. Add it to the appropriate `CommandGroup` in `commandGroups`.

3. The command automatically appears in `commandMap` and `--help` output.

### Adding Flags

- Reuse `verifyOptionsFlags` or `laurelVerifyOptionsFlags` for verification commands.
- Reuse `includeFlag` for commands that load dialect files.
- For new flags, add a `Flag` to the command's `flags` list.
- Access flag values via `pflags.getBool "name"`, `pflags.getString "name"`, or `pflags.getRepeated "name"`.

### Verification Options

Most verification commands build a `VerifyOptions` via `parseVerifyOptions pflags`. This handles all standard flags (solver, timeout, check-mode, etc.). Start from `VerifyOptions.default` or a custom base and the function fills in CLI overrides.

For Laurel commands, use `parseLaurelVerifyOptions` which wraps `parseVerifyOptions` and adds `LaurelTranslateOptions`.

## How to Modify an Existing Command

1. Find the command definition in `StrataMainLib.lean` (search for `def <commandName>Command`).
2. Modify the `callback` implementation, `flags` list, or `args` list.
3. If changing arity (`args`), update the callback's vector indexing accordingly.

## Conventions

- Commands that read Strata files should use `pflags.buildDialectFileMap` to construct the dialect search path (handles `--include` flags and built-in dialects).
- Use `readStrataProgram` for reading and parsing program files with error formatting.
- Prefer the structured exit helpers over raw `IO.Process.exit`.
- The `transform` command uses positional flag binding: `--procedures`/`--functions` bind to the most recent `--pass`. This is handled by `buildPassConfigs` which walks `pflags.entries` in order.
- The `pyAnalyzeLaurel` command emits machine-readable `RESULT:` and `DETAIL:` lines on stdout for downstream tooling. Other commands use human-readable output.

## Dependencies

This package imports from:
- `Strata` (parent package) - Core verification logic, languages, transforms, backends
- `StrataDDM` - Dialect Definition Mechanism (parsing, elaboration, Ion format)
- `Lean` - Parser extensions, JSON utilities

Key imports in `StrataMainLib.lean`:
- `Strata.Languages.Core.Verifier` - Core verification pipeline
- `Strata.Languages.Core.SarifOutput` - SARIF report generation
- `Strata.Languages.C_Simp.Verify` - C_Simp verification
- `Strata.Languages.B3.Verifier.Program` - B3 verification
- `Strata.Languages.Laurel.LaurelCompilationPipeline` - Laurel compilation
- `Strata.Pipeline.PyAnalyzeLaurel` - Python-to-Laurel pipeline
- `Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline` - GOTO translation
- `Strata.Transform.ProcedureInlining` - Transform passes
- `Strata.SimpleAPI` - High-level API functions

## Testing

Build and run:
```bash
lake build
lake exe strata --help
lake exe strata verify ${STRATA_PACKAGE_ROOT}/Examples/SimpleProc.core.st
```

## Common Patterns

### Reading a file and running verification
```lean
let fm ← pflags.buildDialectFileMap
let (pgm, inputCtx) ← readStrataProgram fm file
let vcResults ← Strata.Core.verify pgm inputCtx proceduresToVerify opts mkDischarge
```

### Running the Python-to-Laurel pipeline
```lean
let (outcome, stats, pctx) ← Strata.Pipeline.runPyAnalyzePipeline { ... }
```

### Applying transforms
```lean
match ← (Strata.Core.runTransforms initProgram passes).toBaseIO with
| .ok (program, _) => IO.print (Core.formatProgram program)
| .error e => exitFailure s!"Transform failed: {e}"
```

### Translating to GOTO
```lean
match procedureToGotoCtx Env p sourceText (axioms := axioms) (distincts := distincts) with
| .error e => exitInternalError s!"{e}"
| .ok (ctx, liftedFuncs) => ...
```
