---
inclusion: always
---

# Strata Repository Structure

## Overview

Strata is a Lean4 verification framework using **dialects** as composable language building blocks. The primary target is the **Strata Core dialect** for deductive program verification.

## Repository Structure

### Directory Structure

- `Strata/` - Core implementation (DDM, dialects, languages, transforms, backends)
- `StrataTest/` - Unit tests (mirrors Strata/ structure)
- `Examples/` - Sample programs (`.st` files, naming: `<name>.<dialect>.st`)
- `Tools/` - External tools (BoogieToStrata, Python utilities)
- `vcs/` - Generated SMT2 verification conditions

### Core Components

**`Strata/DDM/`** - Dialect Definition Mechanism
- Parser, elaborator, AST for defining dialects
- Lean integration and Ion format support

**`Strata/DL/`** - Dialect Library
- `Lambda/` - Pure functional expressions (base layer)
- `Imperative/` - Statements with control flow (builds on Lambda)
- `SMT/` - The SMT-LIB standard definition and its solver interface
- `Util/` - Shared utilities (maps, lists, string generation)

**`Strata/Languages/`** - Concrete Language Implementations
- `Core/` - Primary verification language (procedures, contracts, VCG, SMT encoding)
- `C_Simp/` - Simplified C-like language
- `Dyn/` - Dynamic language example
- `Laurel/` - A common representation for front-end languages like Java, Python and JavaScript.
Translated to Core.
- `Python/` - The well-known Python language

**`Strata/Transform/`** - Program Transformations
- Each transformation has implementation + optional correctness proof (`*Correct.lean`)
- `CallElim` - Procedure call elimination via inlining the contract
- `DetToNondet` - Deterministic to non-deterministic control flow
- `LoopElim` - Loop elimination using invariants
- `ProcedureInlining` - Procedure call elimination via inlining the body

**`Strata/Backends/`** - Verification Backends
- `CBMC/` - C Bounded Model Checker integration

## Core Concepts

### Dialect Composition

Dialects are composable language layers, each defining syntax, types, and semantics:
- **Lambda** - Base expression layer (functional)
- **Imperative** - Adds statements and control flow (uses Lambda expressions)
- **Strata Core (or simply Core)** - Adds procedures, contracts, and verification (uses Imperative statements)

### Lambda Dialect (Expressions)

**Location:** `Strata/DL/Lambda/`

Base expression language with:
- Constants, operations, variables, abstractions, quantifiers (with triggers), application, conditionals
- Locally nameless representation (de Bruijn indices for bound variables)
- First-order and higher-order support

**Key files:**
- `LExpr.lean` - AST definition
- `LExprEval.lean` - Evaluator
- `LExprType*.lean` - Type checking
- `LTy.lean` - Type system

### Imperative Dialect (Statements)

**Location:** `Strata/DL/Imperative/`

Statement-level constructs parameterized by expression and command types:
- `cmd` - Atomic command execution
- `block` - Labeled statement sequences
- `ite` - Conditional branching
- `loop` - While loops with optional invariants and measures
- `goto` - Unconditional jumps

**Key files:**
- `Stmt.lean` - AST definition
- `StmtSemantics.lean` - Operational semantics
- `Cmd.lean` - Command interface

## The Strata Core Dialect

**Location:** `Strata/Languages/Core/`

Intermediate Verification Language for deductive program verification.
Its syntax is highly motivated by the [Boogie verifier](https://github.com/boogie-org/boogie),
but has additional convenient syntactic features.

### Types (`Factory.lean`)
- Primitives: `bool`, `int`, `real`, `bv<n>`, `string`
- Constructors: `Map a b`, function types, polymorphic types
- User-defined: abstract types, type synonyms

### Expressions (`Expressions.lean`, `Factory.lean`)
Lambda expressions with Boogie operators:
- Boolean: `And`, `Or`, `Not`, `Implies`
- Arithmetic: `Add`, `Sub`, `Mul`, `Div`, `Mod`
- Comparison: `Lt`, `Le`, `Gt`, `Ge`
- Bitvector: `BV.Add`, `BV.Shl`, `BV.ULt`, etc.
- Map: `Select`, `Store`

### Commands (`Statement.lean`)
Atomic operations:
- `init` - Declare/initialize variable
- `set` - Assignment
- `havoc` - Non-deterministic assignment
- `assert` - Proof obligation (generates VC)
- `assume` - State restriction
- `call` - Procedure invocation

### Procedures (`Procedure.lean`)
Main verification unit with:
- Parameters (input/output)
- Contracts: `requires` (preconditions), `ensures` (postconditions), `modifies` (frame)
- Optional body (implementation)
- `old(expr)` in postconditions refers to pre-state

### Programs (`Program.lean`)
Top-level structure:
- Type declarations, constants, globals
- Pure functions (with optional definitions)
- Axioms (assumed facts)
- Procedures (specifications + bodies)

## Other Languages

**C_Simp** (`Strata/Languages/C_Simp/`) - Simplified C-like language
- Verification via transformation to Strata Core
- Pipeline: Parse → Transform loops → Translate to Strata Core → VCG → SMT

**Dyn** (`Strata/Languages/Dyn/`) - Dynamic language example demonstrating dialect extensibility

## Transformations (`Strata/Transform/`)

Program-to-program translations for simplification and verification. Each has optional correctness proof (`*Correct.lean`).

**DetToNondet** - Deterministic to non-deterministic control flow
- Replaces `if-then-else` with `choice` + `assume`

**CallElim** - Procedure call elimination via contract inlining
- `call y := f(x)` → `assert requires; havoc y, globals; assume ensures`
- Enables modular verification

**LoopElim** - Loop elimination using invariants
- `while guard invariant I { body }` → entry check + arbitrary iteration + exit assumption
- Produces loop-free programs for symbolic execution

## Key Files Quick Reference

| Component | File |
|-----------|------|
| Expression AST | `Strata/DL/Lambda/LExpr.lean` |
| Expression eval | `Strata/DL/Lambda/LExprEval.lean` |
| Expression types | `Strata/DL/Lambda/LTy.lean` |
| Statement AST | `Strata/DL/Imperative/Stmt.lean` |
| Statement semantics | `Strata/DL/Imperative/StmtSemantics.lean` |
| Strata Core expressions | `Strata/Languages/Core/Expressions.lean` |
| Strata Core commands | `Strata/Languages/Core/Statement.lean` |
| Strata Core procedures | `Strata/Languages/Core/Procedure.lean` |
| Strata Core programs | `Strata/Languages/Core/Program.lean` |
| Strata Core operators | `Strata/Languages/Core/Factory.lean` |
| Strata Core VCG | `Strata/Languages/Core/Verifier.lean` |
| SMT encoding | `Strata/Languages/Core/SMTEncoder.lean` |
| SMT solver | `Strata/DL/SMT/Solver.lean` |
| Transformations | `Strata/Transform/*.lean` |

## Build System

**Configuration:** `lakefile.toml`, `lean-toolchain`
**Main module:** `Strata.lean`

**Executables:**
- `StrataVerify` - Main verifier
- `StrataCoreToGoto` - Strata Core to GOTO translation
- `StrataToCBMC` - CBMC backend

**Commands:**
```bash
lake build                                          # Build all
lake test                                           # Run tests
lake exe StrataVerify Examples/SimpleProc.core.st   # Verify program
```

## Verification Workflow

1. Write program (`.core.st` file)
2. Parse (DDM parser)
3. Type check (Strata Core's type system)
4. Transform (optional: eliminate calls/loops)
5. Generate VCs (symbolic execution)
6. Encode to SMT (SMT-LIB format)
7. Solve (cvc5 or Z3)
8. Report results (verified/counterexample/unknown)

Generated VCs saved in `vcs/*.smt2`

## Implementation Workflow

**CRITICAL: Always read relevant files before implementing**

Before starting any implementation task:

1. **Identify the layer** you're working on (Lambda, Imperative, Strata Core, Transform)
2. **Read the core files** for that layer from the Key Files Quick Reference table
3. **Read related files** in the same directory to understand patterns and conventions
4. **Check for similar implementations** in other dialects or transformations
5. **Review tests** in the corresponding `StrataTest/` directory for usage examples

**Example workflows:**

- **Adding a feature to Strata Core:** Read `Expressions.lean`, `Statement.lean`, `Factory.lean`, then check `StrataTest/Languages/Core/` for test patterns
- **Creating a transformation:** Read existing transforms (`DetToNondet.lean`, `CallElim.lean`), their correctness proofs, and tests in `StrataTest/Transform/`
- **Modifying expressions:** Read `Strata/DL/Lambda/LExpr.lean`, `LExprEval.lean`, `LTy.lean` to understand the AST, evaluation, and type system
- **Working with statements:** Read `Strata/DL/Imperative/Stmt.lean` and `StmtSemantics.lean` before making changes

**Never assume structure or conventions - always verify by reading the actual implementation files first.**

## Coding Conventions

- **File organization:** Mirror test structure in `StrataTest/` to match `Strata/`
- **Naming:** Use descriptive names; transformations end with `Correct.lean` for proofs
- **Example files:** Use pattern `<name>.<dialect>.st` (e.g., `SimpleProc.core.st`)
- **Proofs:** Transformation correctness proofs are optional but encouraged
- **Documentation:** Reference `docs/Architecture.md` for design philosophy, `docs/GettingStarted.md` for tutorials

## Working with Dialects

- **Expressions:** Start with Lambda dialect (`Strata/DL/Lambda/`)
- **Statements:** Build on Imperative dialect (`Strata/DL/Imperative/`)
- **New languages:** Extend existing dialects, follow Strata Core as reference
- **Transformations:** Implement in `Strata/Transform/`, add tests in `StrataTest/Transform/`
- **Testing:** Add examples in `Examples/`, unit tests and property-based tests in `StrataTest/`
