/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.Conversion
import Strata.Languages.B3.Verifier.Formatter
import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Core
import Strata.Languages.B3.Verifier.Diagnosis
import Strata.Languages.B3.Verifier.AutoDiagnose

/-!
# B3 Verifier

Converts B3 programs to SMT and verifies them using Z3/CVC5.

## Architecture

**Incremental API** (for interactive debugging):
- `initVerificationState` - Spawn solver and create initial state
- `addFunctionDecl` - Declare a function (sends to solver)
- `addAssertion` - Add an axiom (sends to solver)
- `push` - Push solver scope
- `pop` - Pop solver scope
- `checkProperty` - Assert negation and check-sat (caller manages push/pop)
- `checkPropertyIsolated` - Convenience wrapper (does push/pop automatically)
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

-- Incremental verification with explicit scope management
let state ← initVerificationState
let state ← addFunctionDecl state "f" ["Int"] "Int"
let state ← addAssertion state myAxiom
let state ← push state
let result ← checkProperty state myProperty sourceDecl sourceStmt
let state ← pop state
closeVerificationState state

-- Or use the convenience wrapper
let state ← initVerificationState
let state ← addFunctionDecl state "f" ["Int"] "Int"
let result ← checkPropertyIsolated state myProperty sourceDecl sourceStmt
closeVerificationState state
```

## Key Design Principles

1. **Single solver reuse** - ONE solver for entire program, not fresh per check
2. **Push/pop for isolation** - Each check uses push/pop, not full re-initialization
3. **Provable equivalence** - Batch mode = incremental API called in sequence
4. **Automatic diagnosis** - Failures are automatically narrowed to root cause
5. **SMT Term intermediate** - B3 AST → SMT Term → Solver (provable conversion)
-/
