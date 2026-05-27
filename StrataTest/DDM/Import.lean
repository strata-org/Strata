/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataTest.DDM.Elab
import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects
-- This tests that we can import a module and see dialects declared there.

/--
error: Unknown dialect FailTest.
-/
#guard_msgs in
def testPgmFail :=
#strata
program FailTest;
#end

def testPgm :=
#strata
program Test;
assert;
#end

-- Test that a failed import does not remain in dialect.imports (#1243)
#eval do
  let src := "dialect TestBugB;\nimport NonExistent;\n"
  let inputCtx : Lean.Parser.InputContext := {
    inputString := src
    fileName := "<test>"
    fileMap := Lean.FileMap.ofString src
  }
  let loaded := Strata.Elab.LoadedDialects.builtin
  let fm ← (Strata.DialectFileMap.new loaded).toIO
  let (d, _) ← (Strata.Elab.elabDialect fm inputCtx).toIO
  if d.imports.contains "NonExistent" then
    throw <| IO.userError "Failed import 'NonExistent' should not be in dialect.imports"
