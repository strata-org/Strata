/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def simpleProcPgm : Program :=
#strata
program Boogie;
var g : bool;
procedure Test(x : bool) returns (y : bool)
spec {
  ensures (y == x);
  ensures (x == y);
  ensures (g == old(g));
}
{
  y := x || x;
};
#end

-- Translation from DDM AST to Boogie/Strata AST

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run (translateProgram (simpleProcPgm.commands)) |>.snd |>.isEmpty

/--
info: var (g : bool) := init_g_0
(procedure Test :  ((x : bool)) → ((y : bool)))
modifies: []
preconditions: ⏎
postconditions: (Test_ensures_0, (y == x)) (Test_ensures_1, (x == y)) (Test_ensures_2, (g == (~old g)))
body: y := (((~Bool.Or : (arrow bool (arrow bool bool))) x) x)

Errors: #[]
-/
#guard_msgs in
#eval TransM.run (translateProgram (simpleProcPgm.commands))

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: Test_ensures_0
Assumptions:
Proof Obligation:
(((~Bool.Or $__x0) $__x0) == $__x0)

Label: Test_ensures_1
Assumptions:
Proof Obligation:
($__x0 == ((~Bool.Or $__x0) $__x0))

Label: Test_ensures_2
Assumptions:
Proof Obligation:
#true

Wrote problem to vcs/Test_ensures_0.smt2.
Wrote problem to vcs/Test_ensures_1.smt2.
Wrote problem to vcs/Test_ensures_2.smt2.
---
info:
Obligation: Test_ensures_0
Result: verified

Obligation: Test_ensures_1
Result: verified

Obligation: Test_ensures_2
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" simpleProcPgm

---------------------------------------------------------------------
