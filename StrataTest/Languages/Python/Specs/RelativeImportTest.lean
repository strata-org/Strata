/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Python.Specs
meta import Strata.Languages.Python.Specs.DDM
import Strata.DDM.Ion
import Strata.Languages.Python.PythonDialect
meta import StrataTest.Util.Python

/-! ## Tests for relative import support in PySpec

Positive tests verify that relative imports translate successfully.
Negative tests verify that unsupported import forms produce clear,
actionable error messages.
-/

namespace Strata.Python.Specs.RelativeImportTest

open Strata.Python.Specs (translateFile)

private meta def testDir : System.FilePath :=
  "StrataTest/Languages/Python/Specs/import_test"

/-- Check if `needle` is a substring of `haystack`. -/
private meta def containsSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length != 1

/-- A positive test case: translation should succeed without errors. -/
private structure PositiveCase where
  file : String
  /-- Substrings that should NOT appear in warnings. -/
  noWarnings : Array String := #[]

/-- A negative test case: translation should fail with an error containing
    each of the expected substrings. -/
private structure NegativeCase where
  file : String
  expectedErrors : Array String

/-- Run a positive test: translate the file and expect success. -/
private meta def runPositive (pythonCmd : System.FilePath) (dialectFile : System.FilePath)
    (tc : PositiveCase) : IO (Option String) := do
  IO.FS.withTempDir fun strataDir => do
    let pythonFile := testDir / tc.file
    let r ← translateFile
      (pythonCmd := toString pythonCmd)
      (dialectFile := dialectFile)
      (strataDir := strataDir)
      (pythonFile := pythonFile)
      |>.toBaseIO
    match r with
    | .ok (_sigs, warnings) =>
      for nw in tc.noWarnings do
        if warnings.any (containsSubstr · nw) then
          return some s!"{tc.file}: unexpected warning containing \"{nw}\""
      return none
    | .error e =>
      return some s!"{tc.file}: expected success but got error:\n{e}"

/-- Run a negative test: translate the file and expect a specific error. -/
private meta def runNegative (pythonCmd : System.FilePath) (dialectFile : System.FilePath)
    (tc : NegativeCase) : IO (Option String) := do
  IO.FS.withTempDir fun strataDir => do
    let pythonFile := testDir / tc.file
    let r ← translateFile
      (pythonCmd := toString pythonCmd)
      (dialectFile := dialectFile)
      (strataDir := strataDir)
      (pythonFile := pythonFile)
      |>.toBaseIO
    match r with
    | .ok _ =>
      return some s!"{tc.file}: expected error but translation succeeded"
    | .error msg =>
      for expected in tc.expectedErrors do
        if !containsSubstr msg expected then
          return some s!"{tc.file}: error missing expected substring \"{expected}\"\nActual error:\n{msg}"
      return none

-- ============================================================
-- Test case definitions
-- ============================================================

private meta def positiveCases : Array PositiveCase := #[
  -- Level 1 relative import: from .SiblingModule import SiblingClass
  { file := "rel_import_basic.py" },
  -- Level 1 relative import with alias: from .SiblingModule import SiblingClass as SC
  { file := "rel_import_alias.py" },
  -- Mixed absolute and relative imports in the same file
  { file := "mixed_imports.py" },
  -- Bare import: import SiblingModule
  { file := "bare_import.py" }
]

-- Single negative test file exercises all unsupported import forms.
-- Each expected substring must appear somewhere in the combined error output.
private meta def negativeCases : Array NegativeCase := #[
  { file := "negative_imports.py"
    expectedErrors := #[
      "from . import",      -- from . import X (no module name)
      "not yet supported",  -- from ..Module import X (level 2)
      "not found"           -- from .NonExistent import X (missing module)
    ] }
]

-- ============================================================
-- Test runner
-- ============================================================

private meta def runAllTests : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile Strata.Python.Python.toIon
    let mut errors : Array String := #[]

    -- Run positive tests
    for tc in positiveCases do
      match ← runPositive pythonCmd dialectFile tc with
      | some err => errors := errors.push err
      | none => pure ()

    -- Run negative tests
    for tc in negativeCases do
      match ← runNegative pythonCmd dialectFile tc with
      | some err => errors := errors.push err
      | none => pure ()

    if errors.size > 0 then
      let msg := s!"{errors.size} import test(s) failed:\n"
      let msg := errors.foldl (init := msg) fun msg e => s!"{msg}\n{e}\n"
      throw <| IO.userError msg

#guard_msgs in
#eval runAllTests

end Strata.Python.Specs.RelativeImportTest
