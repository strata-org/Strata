/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the Core verification pipeline produces the expected statistics
counters for a simple program. Uses `Core.typeCheckAndEval` which
returns `Statistics` directly.
-/

import Strata.Languages.Core.Core
import Strata.Languages.Core.Verifier
import Strata.Util.Statistics

open Strata

/-! ## Core Statistics: simple procedure -/

def statsPgm : Strata.Program :=
#strata
program Core;

procedure Test(inout g : bool, x : bool, out y : bool)
spec {
  ensures (y == x);
}
{
  y := x;
};
#end

/--
info: [statistics] Evaluator.factoryOps: 286
[statistics] Evaluator.procedures: 1
[statistics] Evaluator.simulatedStmts: 2
[statistics] Evaluator.verificationEnvironments: 1
-/
#guard_msgs in
#eval do
  let (program, errors) := Core.getProgram statsPgm
  if !errors.isEmpty then
    IO.println s!"Errors: {repr errors}"
    return
  match Core.typeCheckAndEval .quiet program with
  | .error e => IO.println s!"Error: {e.message}"
  | .ok (_, stats) => IO.print stats.format

/-! ## Core Statistics: two procedures with a function -/

def statsPgm2 : Strata.Program :=
#strata
program Core;

function add(a : int, b : int) : int
{ a + b }

procedure P1(x : int, out y : int)
spec {
  ensures (y == add(x, 1));
}
{
  y := add(x, 1);
};

procedure P2(x : int, out y : int)
spec {
  ensures (y == add(x, 2));
}
{
  y := add(x, 2);
};
#end

/--
info: [statistics] Evaluator.factoryOps: 286
[statistics] Evaluator.functions: 1
[statistics] Evaluator.procedures: 2
[statistics] Evaluator.simulatedStmts: 4
[statistics] Evaluator.verificationEnvironments: 1
-/
#guard_msgs in
#eval do
  let (program, errors) := Core.getProgram statsPgm2
  if !errors.isEmpty then
    IO.println s!"Errors: {repr errors}"
    return
  match Core.typeCheckAndEval .quiet program with
  | .error e => IO.println s!"Error: {e.message}"
  | .ok (_, stats) => IO.print stats.format
