/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.SimpleAPI
meta import Strata.Languages.Python.PySpecPipeline
meta import Strata.Languages.Core.Options
meta import Strata.Languages.Core.Verifier
meta import Strata.Transform.ProcedureInlining
meta import StrataTest.Util.Python

/-! ## End-to-end tests for PySpec precondition assertion translation

These tests verify that PySpec `assert` preconditions are translated into
Laurel assertions, inlined at call sites, and checked by the solver.

- `test_precondition_pass.py`: calls `send(url="https://example.com", body="hello")`
  — all preconditions satisfied, no errors expected.
- `test_precondition_fail.py`: calls `send(url="https://example.com", body="")`
  — `len(body) >= 1` is violated, expect "always false" detection.
-/

namespace Strata.Python.PreconditionTest

open Strata (pyAnalyzeLaurel translateCombinedLaurel verifyCore pySpecs)

private meta def testDir : System.FilePath :=
  "StrataTest/Languages/Python/Specs/precondition_test"

/-- Compile a Python source file to a `.pyspec.st.ion` Ion file. -/
private meta def compilePySpec
    (dialectFile : System.FilePath) (pyFile : System.FilePath)
    (outDir : System.FilePath) : IO System.FilePath := do
  match ← pySpecs pyFile outDir dialectFile
      (warningOutput := .none) |>.toBaseIO with
  | .ok () => pure ()
  | .error msg => throw <| .userError s!"pySpecs failed for {pyFile}: {msg}"
  let some stem := pyFile.fileStem
    | throw <| .userError s!"No stem for {pyFile}"
  return outDir / s!"{stem}.pyspec.st.ion"

/-- Compile a Python source file to a `.python.st.ion` Ion file. -/
private meta def compilePython
    (dialectFile : System.FilePath) (pyFile : System.FilePath)
    (outDir : System.FilePath) : IO System.FilePath := do
  let some stem := pyFile.fileStem
    | throw <| .userError s!"No stem for {pyFile}"
  let ionPath := outDir / s!"{stem}.python.st.ion"
  let spawnArgs : IO.Process.SpawnArgs := {
    cmd := "python"
    args := #["-m", "strata.gen", "py_to_strata",
              "--dialect", dialectFile.toString,
              pyFile.toString, ionPath.toString]
    cwd := none
    inheritEnv := true
    stdin := .null
    stdout := .piped
    stderr := .piped
  }
  let child ← IO.Process.spawn spawnArgs
  let _stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  if exitCode ≠ 0 then
    throw <| .userError s!"py_to_strata failed for {pyFile} (exit {exitCode}): {stderr}"
  return ionPath

/-- Run the full pipeline: pyAnalyzeLaurel → translateCombinedLaurel → inline → verify.
    Returns the verification results. -/
private meta def runPipeline (pyspecIon testIon : System.FilePath)
    : IO (Array Core.VCResult) := do
  let laurel ←
    match ← pyAnalyzeLaurel testIon.toString
        (pyspecPaths := #[pyspecIon.toString]) |>.toBaseIO with
    | .ok r => pure r
    | .error err => throw <| .userError s!"pyAnalyzeLaurel failed: {err}"
  let coreProgram ←
    match translateCombinedLaurel laurel with
    | .error diagnostics => throw <| .userError s!"Laurel→Core failed: {diagnostics}"
    | .ok (core, _) => pure core
  -- Inline procedures
  let coreProgram ← match Core.Transform.runProgram (targetProcList := .none)
        (Core.ProcedureInlining.inlineCallCmd
          (doInline := λ name _ => name ≠ "__main__"))
        coreProgram .emp with
    | ⟨.error e, _⟩ => throw <| .userError s!"Inlining failed: {e}"
    | ⟨.ok (_, inlined), _⟩ => pure inlined
  let options : Core.VerifyOptions :=
    { Core.VerifyOptions.default with
      stopOnFirstError := false, verbose := .quiet, solver := "z3",
      checkMode := .bugFinding, checkLevel := .full }
  match ← verifyCore coreProgram options |>.toBaseIO with
  | .ok r => pure r
  | .error msg => throw <| .userError s!"Verification failed: {msg}"

/-- Check if a string contains a substring. -/
private meta def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Count inlined assertion results that are "always false if reached". -/
private meta def countAlwaysFalse (results : Array Core.VCResult) : Nat :=
  results.foldl (init := 0) fun count r =>
    let label := r.obligation.label
    if hasSubstr label "MessageService_send" then
      match r.outcome with
      | .ok o => if o.alwaysFalseAndReachable || o.alwaysFalseReachabilityUnknown then count + 1 else count
      | .error _ => count
    else count

/-- Count inlined assertion results that are "always true if reached". -/
private meta def countAlwaysTrue (results : Array Core.VCResult) : Nat :=
  results.foldl (init := 0) fun count r =>
    let label := r.obligation.label
    if hasSubstr label "MessageService_send" then
      match r.outcome with
      | .ok o => if o.passAndReachable || o.passReachabilityUnknown then count + 1 else count
      | .error _ => count
    else count

#eval Strata.Python.withPython fun _pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    IO.FS.withTempFile fun _handle dialectFile => do
      IO.FS.writeBinFile dialectFile Python.Python.toIon
      let pyspecIon ← compilePySpec dialectFile (testDir / "MessageService.py") tmpDir

      -- Test 1: preconditions satisfied
      let testPassIon ← compilePython dialectFile (testDir / "test_precondition_pass.py") tmpDir
      let passResults ← runPipeline pyspecIon testPassIon
      let falseCount := countAlwaysFalse passResults
      if falseCount > 0 then
        throw <| .userError s!"test_precondition_pass: expected 0 always-false assertions, got {falseCount}"
      let trueCount := countAlwaysTrue passResults
      if trueCount < 3 then
        throw <| .userError s!"test_precondition_pass: expected >= 3 always-true assertions, got {trueCount}"
      IO.println s!"✅ test_precondition_pass: {trueCount} assertions always true, 0 always false"

      -- Test 2: precondition violated (empty body)
      let testFailIon ← compilePython dialectFile (testDir / "test_precondition_fail.py") tmpDir
      let failResults ← runPipeline pyspecIon testFailIon
      let falseCount := countAlwaysFalse failResults
      if falseCount < 1 then
        throw <| .userError s!"test_precondition_fail: expected >= 1 always-false assertion, got {falseCount}"
      IO.println s!"✅ test_precondition_fail: {falseCount} assertion(s) always false (bug detected)"

end Strata.Python.PreconditionTest
