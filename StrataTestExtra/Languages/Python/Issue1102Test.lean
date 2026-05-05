/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Python.TestExamples
import StrataTest.Util.TestDiagnostics

open StrataTest.Util
open Strata.Python (processPythonFile withPython)
open Strata.Parser (stringInputContext)
open Strata

namespace Strata.Python.Issue1102

/-! Regression test for #1102: `isinstance(...)` inside `assert` must not
produce a translation-time type error. Fixtures live alongside this file
under `Issue1102/`. -/

private meta def fixtureDir : System.FilePath :=
  "StrataTestExtra/Languages/Python/Issue1102"

private def translationErrors (ds : Array Diagnostic) : Array Diagnostic :=
  ds.filter fun d =>
    d.type == Strata.DiagnosticType.UserError ||
    d.type == Strata.DiagnosticType.StrataBug

private def expectNoTranslationErrors
    (pythonCmd : System.FilePath) (pyFile : String) : IO Unit := do
  let path := fixtureDir / pyFile
  let source ← IO.FS.readFile path
  let diags ← processPythonFile pythonCmd (stringInputContext pyFile source)
  let errs := translationErrors diags
  if errs.size ≠ 0 then
    throw <| .userError
      s!"{pyFile}: expected 0 translation errors, got {errs.size}: {errs.map (·.message)}"

#guard_msgs in
#eval withPython fun pythonCmd =>
  expectNoTranslationErrors pythonCmd "isinstance_int.py"

#guard_msgs in
#eval withPython fun pythonCmd =>
  expectNoTranslationErrors pythonCmd "isinstance_list.py"

end Strata.Python.Issue1102
