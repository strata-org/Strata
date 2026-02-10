/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def simpleProcPgm : Program :=
#strata
program Core;
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

-- Translation from DDM AST to Strata Core AST

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram simpleProcPgm) |>.snd |>.isEmpty

/--
info: var (g : bool) := init_g_0
(procedure Test :  ((x : bool)) → ((y : bool)))
modifies: []
preconditions: ⏎
postconditions: (Test_ensures_0, ((y : bool) == (x : bool))) (Test_ensures_1, ((x : bool) == (y : bool))) (Test_ensures_2, ((g : bool) == ((~old : (arrow a a)) (g : bool))))
body: y := (((~Bool.Or : (arrow bool (arrow bool bool))) (x : bool)) (x : bool))

Errors: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram simpleProcPgm)

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: Test_ensures_0
Property: assert
Assumptions:


Proof Obligation:
(((~Bool.Or $__x0) $__x0) == $__x0)

Label: Test_ensures_1
Property: assert
Assumptions:


Proof Obligation:
($__x0 == ((~Bool.Or $__x0) $__x0))

Label: Test_ensures_2
Property: assert
Assumptions:


Proof Obligation:
#true

---
info:
Obligation: Test_ensures_0
Property: assert
Result: ✅ pass

Obligation: Test_ensures_1
Property: assert
Result: ✅ pass

Obligation: Test_ensures_2
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" simpleProcPgm

---------------------------------------------------------------------
