/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Backends.CBMC.CoreToCBMC
meta import Strata.Languages.Core.DDMTransform.Translate
import StrataDDM.Integration.Lean.HashCommands

/-!
# CBMC symbol generation from Core procedures

Exercises `Core.testSymbols`: contract and implementation symbols, parameter
symbols, and the local-variable symbol generated for a simple procedure.
-/

meta section

namespace StrataTest.CBMC.CoreToCBMC

private def simpleTestPgm :=
#strata
program Core;

procedure simpleTest(x : int, y : int, out ret : int)
spec {
  requires [x_positive]:    int.gt(x, 0);
}
{
  var z : int;
  z := x;
  z := int.add(z, 1);
  ret := 0;
};
#end

private def simpleTestProc : Except String Core.Procedure := do
  let ast := Strata.TransM.run Inhabited.default (Strata.translateProgram simpleTestPgm)
  match ast.fst.decls.head!.getProc? with
  | .some p => return p
  | .none => throw "Expected procedure"

/-- The generated symbol table contains the contract symbol, the
    implementation symbol, one symbol per input parameter, and the local `z`.
    `simpleTest::ret` is probed but absent: `testSymbols` only emits symbols
    for `inputs`, not `out` parameters. -/
private def symbolKeys : Except String (List String) := do
  let proc ← simpleTestProc
  let json ← Core.testSymbols proc
  -- Key presence is what this pins; the full JSON is large and volatile.
  let keys := ["contract::simpleTest", "\"simpleTest\"", "simpleTest::x",
               "simpleTest::y", "simpleTest::ret", "simpleTest::1::z"]
  return keys.filter (fun k => (json.splitOn k).length > 1)

/-- info: Except.ok ["contract::simpleTest", "\"simpleTest\"", "simpleTest::x", "simpleTest::y", "simpleTest::1::z"] -/
#guard_msgs in
#eval symbolKeys

end StrataTest.CBMC.CoreToCBMC
