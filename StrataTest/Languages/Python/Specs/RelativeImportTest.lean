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

/-- Run a single test case. An empty `expectedErrors` array means the file
    should translate successfully; a non-empty array means translation should
    fail with an error containing each substring. -/
private meta def runTest (pythonCmd : System.FilePath) (dialectFile : System.FilePath)
    (file : String) (expectedErrors : Array String) : IO (Option String) := do
  IO.FS.withTempDir fun strataDir => do
    let pythonFile := testDir / file
    let r ← translateFile
      (pythonCmd := toString pythonCmd)
      (dialectFile := dialectFile)
      (strataDir := strataDir)
      (pythonFile := pythonFile)
      (searchPath := pythonFile.parent.getD pythonFile)
      |>.toBaseIO
    if expectedErrors.isEmpty then
      match r with
      | .ok _ => return none
      | .error e => return some s!"{file}: expected success but got error:\n{e}"
    else
      match r with
      | .ok _ => return some s!"{file}: expected error but translation succeeded"
      | .error msg =>
        for expected in expectedErrors do
          if !containsSubstr msg expected then
            return some s!"{file}: error missing expected substring \"{expected}\"\nActual error:\n{msg}"
        return none

-- ============================================================
-- Test case definitions
-- ============================================================

private meta def testCases : Array (String × Array String) := #[
  -- Level 1 relative import: from .SiblingModule import SiblingClass
  ("rel_import_basic.py", #[]),
  -- Level 1 relative import with alias: from .SiblingModule import SiblingClass as SC
  ("rel_import_alias.py", #[]),
  -- Mixed absolute and relative imports in the same file
  ("mixed_imports.py", #[]),
  -- Bare import: import SiblingModule
  ("bare_import.py", #[]),
  -- Package dotted import: from service.module import ServiceClass
  ("pkg_import_dotted.py", #[]),
  -- Package import via __init__.py: from service import ServiceClass
  ("pkg_import_from.py", #[]),
  -- Package-level relative import: from . import module (inside service/)
  ("service/alt_init_module.py", #[]),
  -- Unsupported import forms: level 2 relative and missing module
  ("negative_imports.py", #[
    "not yet supported",  -- from ..Module import X (level 2)
    "not found"           -- from .NonExistent import X (missing module)
  ])
]

-- ============================================================
-- Test runner
-- ============================================================

private meta def runAllTests : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile Strata.Python.Python.toIon
    let mut errors : Array String := #[]
    for (file, expectedErrors) in testCases do
      match ← runTest pythonCmd dialectFile file expectedErrors with
      | some err => errors := errors.push err
      | none => pure ()
    if errors.size > 0 then
      let msg := s!"{errors.size} import test(s) failed:\n"
      let msg := errors.foldl (init := msg) fun msg e => s!"{msg}\n{e}\n"
      throw <| IO.userError msg

#guard_msgs in
#eval runAllTests

end Strata.Python.Specs.RelativeImportTest
