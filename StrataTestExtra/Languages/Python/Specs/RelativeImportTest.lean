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

open Strata.Python.Specs (translateFile ModuleName)
open Strata.Python (containsSubstr)

private meta def testDir : System.FilePath :=
  "StrataTestExtra/Languages/Python/Specs/import_test"

/-- Run a single test case. An empty `expectedErrors` array means the file
    should translate successfully; a non-empty array means translation should
    fail with an error containing each substring.
    When `searchFromTestDir` is true, uses `testDir` as the search path
    (needed for files inside packages like `service/`). -/
private meta def runTest (pythonCmd : System.FilePath) (dialectFile : System.FilePath)
    (file : String) (expectedErrors : Array String)
    (searchFromTestDir : Bool := false) : IO (Option String) := do
  IO.FS.withTempDir fun strataDir => do
    let pythonFile := testDir / file
    let searchPath := if searchFromTestDir then testDir
      else pythonFile.parent.getD pythonFile
    -- When searching from testDir, derive a multi-component module name
    -- from the relative path so that currentModulePrefix is non-empty
    -- (e.g. "service/rel_import_basic.py" → "service.rel_import_basic").
    let moduleName ← if searchFromTestDir then
      let stem := if (file : String).endsWith "/__init__.py" then
        ((file : String).dropEnd "/__init__.py".length).toString
      else
        ((file : String).dropEnd ".py".length).toString
      let dotted := stem.replace "/" "."
      match ModuleName.ofString dotted with
      | .ok m => pure (some m)
      | .error e => return some s!"{file}: bad module name: {e}"
    else pure none
    let r ← translateFile
      (pythonCmd := toString pythonCmd)
      (dialectFile := dialectFile)
      (strataDir := strataDir)
      (pythonFile := pythonFile)
      (searchPath := searchPath)
      (moduleName := moduleName)
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

private structure TestCase where
  file : String
  expectedErrors : Array String := #[]
  /-- Use `testDir` as searchPath (needed for files inside packages). -/
  searchFromTestDir : Bool := false

private meta def testCases : Array TestCase := #[
  -- Level 1 relative import: from .module import ServiceClass (inside package)
  { file := "service/rel_import_basic.py", searchFromTestDir := true },
  -- Level 1 relative import with alias: from .module import ServiceClass as SC
  { file := "service/rel_import_alias.py", searchFromTestDir := true },
  -- Bare import: import SiblingModule
  { file := "bare_import.py" },
  -- Bare import with alias: import SiblingModule as SM
  { file := "bare_import_alias.py" },
  -- Package dotted import: from service.module import ServiceClass
  { file := "pkg_import_dotted.py" },
  -- Package import via __init__.py: from service import ServiceClass
  { file := "pkg_import_from.py" },
  -- Package-level relative import: from . import module (inside service/)
  { file := "service/alt_init_module.py", searchFromTestDir := true },
  -- Package-level relative import with alias: from . import module as mod
  { file := "service/rel_import_alias_init.py", searchFromTestDir := true },
  -- Mixed absolute and relative imports in the same file (inside package)
  { file := "service/mixed_imports.py", searchFromTestDir := true },
  -- Level 2 relative import: from ..module import ServiceClass (inside sub/)
  { file := "service/sub/rel_import_parent.py", searchFromTestDir := true },
  -- Nested import (depth 2): error in leaf module should include source location
  { file := "nested_import_error.py", expectedErrors := #["already defined"] },
  -- Bare import of missing module: import NonExistentModule
  { file := "bare_import_missing.py", expectedErrors := #["not found"] },
  -- Relative import from a top-level module (no package): should error
  { file := "toplevel_relative.py"
    expectedErrors := #["relative import from a top-level module"] },
  -- Level 2 relative into nonexistent sibling package: should fail
  { file := "service/sub/rel_import_cross_pkg.py"
    searchFromTestDir := true
    expectedErrors := #["not found"] },
  -- Level 3 relative from depth-2 package: escapes root
  { file := "service/sub/rel_import_escape_root.py"
    searchFromTestDir := true
    expectedErrors := #["goes beyond the top-level package"] },
  -- Top-level relative imports (level 1 and 2, no package prefix)
  { file := "negative_imports.py"
    expectedErrors := #[
      "relative import from a top-level module",  -- from ..Module (level 2)
      "relative import from a top-level module"   -- from .NonExistent (level 1)
    ] }
]

-- ============================================================
-- Test runner
-- ============================================================

private meta def runAllTests : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile Strata.Python.Python.toIon
    let mut errors : Array String := #[]
    for tc in testCases do
      match ← runTest pythonCmd dialectFile tc.file tc.expectedErrors
          tc.searchFromTestDir with
      | some err => errors := errors.push err
      | none => pure ()
    if errors.size > 0 then
      let msg := s!"{errors.size} import test(s) failed:\n"
      let msg := errors.foldl (init := msg) fun msg e => s!"{msg}\n{e}\n"
      throw <| IO.userError msg

#guard_msgs in
#eval runAllTests

end Strata.Python.Specs.RelativeImportTest
