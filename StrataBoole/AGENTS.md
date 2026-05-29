# AGENTS.md — StrataBoole

Guidelines for AI agents working on the StrataBoole package.

## Package Purpose

StrataBoole implements the **Boole dialect** — a high-level imperative verification language that compiles to Strata Core. It lives in its own Lake package with a dependency on the parent `Strata` package.

## Architecture

```
StrataBoole/
├── Grammar.lean       # DDM dialect grammar (syntax definition)
├── Boole.lean         # Generated AST types via #strata_gen
├── Verify.lean        # Boole → Core translation (toCoreProgram, toCoreExpr, toCoreStmt)
├── MetaVerifier.lean  # Lean tactic infrastructure (gen_smt_vcs_boole)
```

**Data flow**: Boole source (in `#strata` block) → DDM parser → `BooleDDM.Program` → `toCoreProgram` → `Core.Program` → VCG → SMT VCs → solver or Lean proof.

## Key Types and Functions

| Symbol | Location | Role |
|--------|----------|------|
| `Strata.Boole.Program` | `Boole.lean` | Boole program AST (generated) |
| `Strata.Boole.Expr` | `Boole.lean` | Boole expression AST (generated) |
| `Strata.Boole.toCoreProgram` | `Verify.lean` | Main translation entry point |
| `Strata.Boole.toCoreExpr` | `Verify.lean` | Expression translation |
| `Strata.Boole.toCoreStmt` | `Verify.lean` | Statement translation |
| `Strata.Boole.TranslateM` | `Verify.lean` | Translation monad (`StateT TranslateState (Except DiagnosticModel)`) |
| `Strata.genSMTVCsBoole` | `MetaVerifier.lean` | Full pipeline: program → SMT VCs |
| `Strata.smtVCsCorrectBoole` | `MetaVerifier.lean` | Prop asserting all VCs are valid |
| `gen_smt_vcs_boole` | `MetaVerifier.lean` | Tactic to unfold VCs into Lean goals |
| `Strata.Boole.verify` | `Verify.lean` | Runtime verification via external solver |

## Before Making Changes

1. **Read the relevant source files first.** Never assume structure — the DDM-generated types in `Boole.lean` come from the grammar in `Grammar.lean`.
2. **Understand the translation layer.** Most logic lives in `Verify.lean`. The `TranslateState` tracks bound variables, type variables, global variable types, and the modifies map.
3. **Check existing tests** in `StrataBooleTest/` for usage patterns and expected behavior.
4. **Build from the `StrataBoole/` directory** using `lake build`. Run tests with `lake build StrataBooleTest`.

## Common Tasks

### Adding a new Boole language feature

1. Add the syntax to `Grammar.lean` using DDM `op` or `fn` declarations
2. Rebuild to regenerate AST constructors (`lake build StrataBoole.Boole`)
3. Add translation cases in `Verify.lean` (in `toCoreExpr` or `toCoreStmt`)
4. Add a test file in `StrataBooleTest/` demonstrating the feature
5. Import the new test in `StrataBooleTest.lean`

### Adding a new test

1. Create a `.lean` file in `StrataBooleTest/` (or `StrataBooleTest/FeatureRequests/` for experimental features)
2. Import `StrataBoole.MetaVerifier`
3. Define the program with `#strata program Boole; ... #end`
4. Verify with `#eval Strata.Boole.verify "cvc5" prog (options := .quiet)` and/or a `theorem` using `gen_smt_vcs_boole`
5. Pin output with `#guard_msgs in` where appropriate
6. Add the import to `StrataBooleTest.lean`

### Fixing a translation bug

1. Identify which Boole AST constructor is involved (check `Grammar.lean` for the syntax rule)
2. Find the corresponding case in `toCoreExpr` or `toCoreStmt` in `Verify.lean`
3. Compare the generated Core output against what Core expects (see `Strata/Languages/Core/`)
4. Write a minimal test case that reproduces the issue before fixing

## Important Patterns

### The TranslateState

The translation is stateful. Key fields:
- `bvars` — stack of bound variable expressions (locally nameless representation)
- `tyBVars` — stack of bound type variable names
- `modifiesMap` — procedure name → list of modified globals (collected in a pre-pass)
- `globalVarTypes` — global variable name → type (for adding as procedure parameters)
- `currentInoutNames` — names of inout params for the current procedure (used by `old`)

Use `withBVars`, `withBVarExprs`, `withTypeBVars` to scope variable bindings.

### Boole's global variable convention

Boole `var` declarations and `modifies` clauses are **not** directly representable in Core. They are translated into extra `inout` (modified) or `in` (read-only) parameters prepended to every procedure signature and call site. The `getGlobalParamPrefix` and `constructProcArgsPrefix` functions handle this.

### Mutual recursion in translation

`toCoreExpr` and `toCoreStmt`/`toCoreBlock` are mutually recursive (expressions can appear in statements, statements contain blocks with nested expressions). They use Lean's `mutual ... end` with `termination_by SizeOf.sizeOf`.

### DDM grammar conventions

- `op` defines a syntactic production (statement, command, etc.)
- `fn` defines an expression-level operator
- `@[scope(x)]` marks parameters that are in scope of binding `x`
- `@[prec(n)]` sets precedence for parsing/printing
- Categories (`Statement`, `Command`, `Program`, etc.) organize productions

## Testing Conventions

- Each test file is self-contained (imports `StrataBoole.MetaVerifier`, defines program, verifies)
- Use `#guard_msgs` to pin `#eval` output for regression testing
- Proof-mode tests use `theorem ... : smtVCsCorrectBoole prog := by gen_smt_vcs_boole; all_goals (try grind)`
- Feature request tests in `FeatureRequests/` may contain `sorry` for unimplemented features

## Build and Verification

```bash
# Build the library
lake build

# Build and check all tests
lake test

# Verify a specific test file (useful during development)
lake build StrataBooleTest.demo
```

## Dependencies

- **Strata** (parent package, via `path = ".."`) — provides Core dialect, VCG, SMT encoding, DDM infrastructure
- **Lean 4** — version specified in `lean-toolchain`

## Pitfalls

- **Do not use Core's `out`/`inout` call argument syntax in Boole programs.** Boole's calling convention separates inputs (positional args) from outputs (returns declarations consumed by call lhs := f(args)). The `out` qualifier is unnecessary because the translator already emits `Core.CallArg.outArg` from each call's LHS, and `inout` would conflict with the implicit global-variable prefix added by `constructProcArgsPrefix` based on `modifies` clauses. So both exist at the Core level but are generated implicitly from Boole syntax.
- **The `#strata_gen` macro in `Boole.lean` is expensive** (`maxHeartbeats 400000`). Avoid unnecessary rebuilds of this file.
- **Grammar changes regenerate the AST.** After modifying `Grammar.lean`, all downstream files (`Boole.lean`, `Verify.lean`, tests) may need updates to match new/changed constructors.
- **`old(x)` only applies to inout parameters.** For other variables, `old x = x`. This is handled by `oldifyExpr` checking against `currentInoutNames`.
- **Source positions matter for `#guard_msgs` tests.** Moving code around can shift source ranges in diagnostic output, requiring test updates.
