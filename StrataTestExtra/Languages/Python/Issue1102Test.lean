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
crash the Python-to-Laurel-to-Core translation pipeline. Before the fix
these programs failed in Laurel type checking with
"Impossible to unify (arrow Any bool) with (arrow bool $__ty…)".

Each fixture snapshots both the diagnostic `type` and the full rendered
message, so a silent-drop regression (translating the assert to a no-op)
or a message reword would also fail. Fixtures live in `Issue1102/`.

Note: compound assert conditions such as `isinstance(x, T) and x > 0` or
`not isinstance(x, T)` currently trip a *separate* StrataBug ("block
expression should have been lowered in a separate pass") that is
independent of #1102 and should be tracked in its own issue. -/

private meta def fixtureDir : System.FilePath :=
  "StrataTestExtra/Languages/Python/Issue1102"

/-- Render a diagnostic as a single deterministic line:
"type @ line:colStart-colEnd :: message". -/
private def renderDiag (d : Diagnostic) : String :=
  s!"{repr d.type} @ {d.start.line}:{d.start.column}-{d.ending.column} :: {d.message}"

/-- Load a fixture and print each diagnostic on its own line, prefixed
with the fixture name. Prefer this over ad-hoc prose filters: it asserts
structurally on `type` and keeps the full message in the snapshot. -/
private def snapshotDiags (pythonCmd : System.FilePath) (pyFile : String) : IO Unit := do
  let path := fixtureDir / pyFile
  let source ← IO.FS.readFile path
  let diags ← processPythonFile pythonCmd (stringInputContext pyFile source)
  for d in diags do
    IO.println s!"{pyFile}: {renderDiag d}"
  -- Belt-and-braces structural check: any StrataBug is a regression.
  if diags.any (fun d => d.type == Strata.DiagnosticType.StrataBug) then
    throw <| .userError s!"{pyFile}: unexpected StrataBug diagnostic"

-- `assert isinstance(5, int)` — the minimal fuzz reproduction. Before
-- the fix this raised a Laurel type error; after the fix the pipeline
-- completes and the verifier reports the assertion as unprovable
-- (expected, since `isinstance` is unmodelled).
/--
info: isinstance_int.py: Strata.DiagnosticType.UserError @ 2:4-29 :: assertion could not be proved
-/
#guard_msgs in
#eval withPython fun pythonCmd => snapshotDiags pythonCmd "isinstance_int.py"

-- `assert isinstance([1], list)` — the original fuzz_semantic_0004 shape.
/--
info: isinstance_list.py: Strata.DiagnosticType.UserError @ 2:4-32 :: assertion could not be proved
-/
#guard_msgs in
#eval withPython fun pythonCmd => snapshotDiags pythonCmd "isinstance_list.py"

-- `if isinstance(x, int): assert x > 0` — the non-hoisting .If path,
-- included to show the fix does not affect the path that already worked.
/--
info: isinstance_if.py: Strata.DiagnosticType.UserError @ 4:8-20 :: assertion could not be proved
-/
#guard_msgs in
#eval withPython fun pythonCmd => snapshotDiags pythonCmd "isinstance_if.py"

end Strata.Python.Issue1102
