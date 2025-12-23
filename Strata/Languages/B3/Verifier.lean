/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-!
# B3 Verifier Interface

This module provides an interface to the B3 verifier, which is an intermediate
verification language (IVL) similar to Boogie 2.

B3 is invoked as an external process. It reads a `.b3` file and outputs
verification results to stdout.

## Usage

```lean
-- Verify a B3 file
let result ← B3.verify "path/to/file.b3"
match result with
| .success output => IO.println s!"Verified: {output}"
| .error msg => IO.println s!"Error: {msg}"
```
-/

namespace Strata.B3

/-- Result of B3 verification -/
inductive VerifyResult where
  | success (output : String)
  | error (message : String)
deriving Repr, Inhabited

namespace VerifyResult

def isSuccess : VerifyResult → Bool
  | .success _ => true
  | .error _ => false

def isError : VerifyResult → Bool
  | .success _ => false
  | .error _ => true

def getOutput : VerifyResult → Option String
  | .success output => some output
  | .error _ => none

def getError : VerifyResult → Option String
  | .success _ => none
  | .error msg => some msg

end VerifyResult

/--
Verify a B3 file using the b3 executable.
Assumes `b3` is available in PATH.

Parameters:
- `filePath`: Path to the `.b3` file to verify
- `solver`: Optional solver to use ("z3" or "cvc5", defaults to "z3")
- `showProofObligations`: Whether to show proof obligations (default: false)

Returns:
- `VerifyResult.success` with the verification output if successful
- `VerifyResult.error` with error message if verification fails or b3 is not found
-/
def verify (filePath : String) (solver : String := "z3")
    (showProofObligations : Bool := false) : IO VerifyResult := do
  -- Build command arguments
  let mut args := #["verify", filePath]

  -- Add solver flag
  if solver == "cvc5" then
    args := args.push "--cvc5"
  else
    args := args.push "--z3"

  -- Add proof obligations flag if requested
  if showProofObligations then
    args := args.push "--show-proof-obligations"

  try
    -- Spawn b3 process
    let proc ← IO.Process.spawn {
      cmd := "b3"
      args := args
      stdin := .null
      stdout := .piped
      stderr := .piped
    }

    -- Wait for process to complete
    let exitCode ← proc.wait

    -- Read stdout and stderr
    let stdout ← proc.stdout.readToEnd
    let stderr ← proc.stderr.readToEnd

    -- Check exit code
    if exitCode == 0 then
      return .success stdout
    else
      let errorMsg := if stderr.isEmpty then stdout else stderr
      return .error s!"B3 verification failed (exit code {exitCode}):\n{errorMsg}"
  catch e =>
    return .error s!"Failed to run b3: {e}"

/--
Parse a B3 file without verification.
This runs b3 in parse-only mode to check syntax.

Parameters:
- `filePath`: Path to the `.b3` file to parse

Returns:
- `VerifyResult.success` if parsing succeeds
- `VerifyResult.error` with parse error message if parsing fails
-/
def parseOnly (filePath : String) : IO VerifyResult := do
  try
    let proc ← IO.Process.spawn {
      cmd := "b3"
      args := #[filePath, "--parse-only"]
      stdin := .null
      stdout := .piped
      stderr := .piped
    }

    let exitCode ← proc.wait
    let stdout ← proc.stdout.readToEnd
    let stderr ← proc.stderr.readToEnd

    if exitCode == 0 then
      return .success stdout
    else
      let errorMsg := if stderr.isEmpty then stdout else stderr
      return .error s!"B3 parsing failed (exit code {exitCode}):\n{errorMsg}"
  catch e =>
    return .error s!"Failed to run b3: {e}"

/--
Helper function to write to stdin and wait for process.
Uses takeStdin to properly close stdin before waiting.
-/
private def runWithStdin (args : Array String) (input : String) : IO (UInt32 × String × String) := do
  let mut child ← IO.Process.spawn {
    cmd := "b3"
    args := args
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }

  -- Take ownership of stdin so we can close it
  let (stdin, child') ← child.takeStdin

  -- Write to stdin
  stdin.putStr input
  stdin.flush

  -- stdin will be closed when it goes out of scope here

  -- Wait for process to complete
  let exitCode ← child'.wait

  -- Read outputs
  let stdout ← child'.stdout.readToEnd
  let stderr ← child'.stderr.readToEnd

  return (exitCode, stdout, stderr)

/--
Verify B3 program text by passing it via stdin.

Parameters:
- `programText`: The B3 program as a string
- `solver`: Optional solver to use ("z3" or "cvc5", defaults to "z3")
- `showProofObligations`: Whether to show proof obligations (default: false)

Returns:
- `VerifyResult.success` with the verification output if successful
- `VerifyResult.error` with error message if verification fails
-/
def verifyText (programText : String) (solver : String := "z3")
    (showProofObligations : Bool := false) : IO VerifyResult := do
  -- Build command arguments
  let mut args := #["verify", "--stdin"]

  -- Add solver flag
  if solver == "cvc5" then
    args := args.push "--cvc5"
  else
    args := args.push "--z3"

  -- Add proof obligations flag if requested
  if showProofObligations then
    args := args.push "--show-proof-obligations"

  try
    let (exitCode, stdout, stderr) ← runWithStdin args programText

    -- Check exit code
    if exitCode == 0 then
      return .success stdout
    else
      let errorMsg := if stderr.isEmpty then stdout else stderr
      return .error s!"B3 verification failed (exit code {exitCode}):\n{errorMsg}"
  catch e =>
    return .error s!"Failed to run b3: {e}"

/--
Check if b3 is available in PATH.

Returns:
- `true` if b3 can be executed
- `false` otherwise
-/
def isAvailable : IO Bool := do
  try
    let proc ← IO.Process.spawn {
      cmd := "b3"
      args := #[]
      stdin := .null
      stdout := .piped
      stderr := .piped
    }
    let _ ← proc.wait
    return true
  catch _ =>
    return false

end Strata.B3
