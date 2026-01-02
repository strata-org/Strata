/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.Conversion
import Strata.Languages.B3.Verifier.Formatter
import Strata.Languages.B3.Verifier.State
import Strata.Languages.B3.Verifier.Core

/-!
# B3 Verifier

Converts B3 programs to SMT and verifies them using Z3/CVC5.

## Architecture

**Incremental API** (for interactive debugging):
- `initVerificationState` - Create empty state
- `addFunctionDecl` - Declare a function
- `addAssertion` - Add an axiom
- `checkProperty` - Verify a property

**Batch API** (built on incremental):
- `verifyProgram` - Verify entire B3 program
- `programToSMTCommands` - Generate SMT commands for inspection

## Usage

```lean
-- Batch verification
let results ← verifyProgram myB3Program

-- Incremental verification
let state := initVerificationState
let state := addFunctionDecl state "f" ["Int"] "Int"
let state := addAssertion state myAxiom
let result ← checkProperty state myProperty sourceDecl
```
-/
