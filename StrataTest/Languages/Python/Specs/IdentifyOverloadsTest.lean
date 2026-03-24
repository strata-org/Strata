/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.SimpleAPI
meta import Strata.SimpleAPI.Python
meta import Strata.Languages.Python.Specs
meta import Strata.Languages.Python.Specs.IdentifyOverloads
meta import StrataTest.Util.Python

/-! ## Unit tests for `resolveOverloads`

These tests call `resolveOverloads` directly and assert exact module
sets, ensuring we identify precisely the needed specs — no more, no
fewer.
-/

namespace Strata.Python.Specs.IdentifyOverloadsTest

open Strata (pySpecs withPythonDialect pyParsePythonFile readDispatchOverloads)
open Strata.Python.Specs (ModuleName)
open Strata.Python.Specs.IdentifyOverloads (resolveOverloads)
open Strata.Python (OverloadTable)

private meta def testDir : System.FilePath :=
  "StrataTest/Languages/Python/Specs/dispatch_test"

/-- Compile the dispatch pyspec and return the overload table. -/
private meta def buildOverloadTable
    (outDir : System.FilePath) : IO OverloadTable := do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile Python.Python.toIon
    -- Compile servicelib dispatch file to pyspec Ion
    let pyFile := testDir / "servicelib" / "__init__.py"
    match ← pySpecs pyFile outDir dialectFile
        (warningOutput := .none) |>.toBaseIO with
    | .ok () => pure ()
    | .error msg =>
      throw <| .userError s!"pySpecs failed for {pyFile}: {msg}"
    let .ok dispatchMod := ModuleName.ofString "servicelib"
      | throw <| .userError "Invalid module name"
    match ← readDispatchOverloads outDir #[dispatchMod] |>.toBaseIO with
    | .ok tbl => return tbl
    | .error msg =>
      throw <| .userError s!"readDispatchOverloads failed: {msg}"

/-- Run resolveOverloads on a test file and return the module set. -/
private meta def resolveFile
    (tbl : OverloadTable) (pyFile : System.FilePath)
    : IO (Std.HashSet String) := do
  let stmts ←
    match ← withPythonDialect (fun df => pyParsePythonFile df pyFile) |>.toBaseIO with
    | .ok s => pure s
    | .error msg => throw <| .userError s!"pyParsePythonFile failed: {msg}"
  return (resolveOverloads tbl stmts.stmts).modules

/-- A test case: Python file and exact expected module set. -/
private structure TestCase where
  file : String
  expected : List String

private meta def testCases : List TestCase := [
  -- Single service at top level
  { file := "test_single_service.py"
    expected := ["Storage"] },
  -- Multiple services
  { file := "test_multi_service.py"
    expected := ["Storage", "Messaging"] },
  -- Dispatch inside a class method
  { file := "test_class_dispatch.py"
    expected := ["Storage"] },
  -- Dispatch in both branches of an if/else
  { file := "test_dispatch_in_conditional.py"
    expected := ["Storage", "Messaging"] },
  -- Dispatch inside a try block
  { file := "test_dispatch_in_try.py"
    expected := ["Storage"] },
  -- No dispatch calls at all
  { file := "test_no_dispatch.py"
    expected := [] },
  -- Loop with variable (not string literal) — not resolved
  { file := "test_dispatch_in_loop.py"
    expected := [] }
]

/-- Run a single test case and return an error message on failure. -/
private meta def runTestCase
    (tbl : OverloadTable)
    (tc : TestCase) : IO (Option String) := do
  let modules ← resolveFile tbl (testDir / tc.file)
  let expected : Std.HashSet String :=
    tc.expected.foldl (init := {}) fun s m => s.insert m
  if modules == expected then return none
  let got := modules.toList
  let exp := expected.toList
  return some
    s!"{tc.file}: expected modules {exp}, got {got}"

#eval withPython fun _pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    let tbl ← buildOverloadTable tmpDir
    -- Launch all tests concurrently
    let mut seen : Std.HashSet String := {}
    let mut tasks : Array (String × Task (Except IO.Error (Option String))) := #[]
    for tc in testCases do
      if tc.file ∈ seen then
        throw <| IO.userError s!"Duplicate test filename: {tc.file}"
      seen := seen.insert tc.file
      let task ← IO.asTask (runTestCase tbl tc)
      tasks := tasks.push (tc.file, task)
    -- Collect results
    let mut errors : Array String := #[]
    for (_, task) in tasks do
      match ← IO.wait task with
      | .ok (some err) => errors := errors.push err
      | .ok none => pure ()
      | .error e => errors := errors.push s!"Task error: {e}"
    if errors.size > 0 then
      throw <| IO.userError ("\n".intercalate errors.toList)

end Strata.Python.Specs.IdentifyOverloadsTest
