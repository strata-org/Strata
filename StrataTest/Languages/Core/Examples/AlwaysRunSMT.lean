/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

/-- A program with a trivially true assertion that PE resolves without the solver. -/
def alwaysRunSMTPgm :=
#strata
program Core;
procedure Test(x : int) returns (y : int)
spec {
  ensures (y == x);
}
{
  y := x;
};
#end

def runAndCheckForSMTFiles : IO Unit := do
  let vcDir : System.FilePath := "_test_vcs"
  -- Ensure vcDir exists and is empty
  if ← vcDir.pathExists then
    IO.FS.removeDirAll vcDir
  IO.FS.createDirAll vcDir
  let _ ← verify alwaysRunSMTPgm (options := { Core.VerifyOptions.default with
    alwaysRunSMT := true,
    vcDirectory := vcDir})
  -- Check that vcDir has exactly one `.smt2` file in it
  let entries ← vcDir.readDir
  let smt2Files := entries.filter (fun e => e.fileName.endsWith ".smt2")
  println! f!"Number of `.smt2` files: {smt2Files.size}"
  -- Clean up
  IO.FS.removeDirAll vcDir

-- With alwaysRunSMT, an `.smt2` file is always created even for a trivial VC.
/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: Test_ensures_0
Property: assert
Obligation:
true

Number of `.smt2` files: 1
-/
#guard_msgs in
#eval runAndCheckForSMTFiles

---------------------------------------------------------------------
