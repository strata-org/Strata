/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.Conversion
import Strata.Languages.B3.Verifier.Formatter
import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Batch
import Strata.Languages.B3.Verifier.Diagnosis

/-!
# B3 Verifier

Converts B3 programs to SMT and verifies them using Z3/CVC5.

## Architecture Overview

```
B3 Program (CST)
      ↓
   Parse (DDM)
      ↓
  B3 AST (de Bruijn indices)
      ↓
FunctionToAxiom Transform
      ↓
  B3 AST (declarations + axioms)
      ↓
expressionToSMT (Conversion)
      ↓
  SMT Terms
      ↓
formatTermDirect (Formatter)
      ↓
  SMT-LIB strings
      ↓
  Solver (Z3/CVC5)
      ↓
  Results (proved/counterexample/unknown)
      ↓
Diagnosis (if failed)
```

## Module Organization

- **State.lean** - Pure state types and basic operations
- **Conversion.lean** - B3 AST → SMT Term conversion with error handling
- **Formatter.lean** - SMT Term → SMT-LIB string formatting
- **Statements.lean** - Statement execution (check, assert, assume, reach)
- **Batch.lean** - Batch verification API and program state building
- **Diagnosis.lean** - Automatic failure diagnosis and batch verification with diagnosis
- **Transform/FunctionToAxiom.lean** - Function definition → axiom transformation

## Architecture

**Incremental API** (for interactive debugging):
- `initVerificationState` - Spawn solver and create initial state
- `addFunctionDecl` - Declare a function (sends to solver)
- `addAxiom` - Add an axiom (sends to solver)
- `push` - Push solver scope
- `pop` - Pop solver scope
- `prove` - Prove a property holds (check statement)
- `reach` - Check if a property is reachable (reach statement)
- `closeVerificationState` - Exit solver cleanly

**Batch API** (built on incremental):
- `verifyProgram` - Verify entire B3 program
- `verifyWithDiagnosis` - Verify with automatic failure diagnosis
- `programToSMTCommands` - Generate SMT commands for inspection

**Diagnosis API** (automatic debugging):
- `diagnoseFailure` - Automatically narrow down root cause of failure
- Strategies: conjunction splitting, when-clause testing (future), inlining (future)

## Usage

```lean
-- Batch verification
let results ← verifyProgram myB3Program

-- Batch with automatic diagnosis
let reports ← verifyWithDiagnosis myB3Program

-- Incremental verification
let state ← initVerificationState
let state ← addFunctionDecl state myFunctionDecl
let state ← addAxiom state myAxiomTerm
let result ← prove state myPropertyTerm sourceDecl sourceStmt
closeVerificationState state
```

## Key Design Principles

1. **Single solver reuse** - ONE solver for entire program
2. **Push/pop for isolation** - Each check uses push/pop
3. **Provable equivalence** - Batch mode = incremental API in sequence
4. **Automatic diagnosis** - Failures automatically narrowed to root cause
5. **SMT Term intermediate** - B3 AST → SMT Term → Solver
-/
