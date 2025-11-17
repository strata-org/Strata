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
  modifies g;
  ensures (y == x);
  ensures (x == y);
  ensures (g == old(g));
}
{
  g := g && true;
  y := x || x;
  assert g == old(g);
};
#end

-- Translation from DDM AST to Boogie/Strata AST

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run (translateProgram simpleProcPgm) |>.snd |>.isEmpty

/--
info: var (g : bool) := init_g_0
(procedure Test :  ((x : bool)) → ((y : bool)))
modifies: [g]
preconditions: ⏎
postconditions: (Test_ensures_1, ((y : bool) == (x : bool))) (Test_ensures_2, ((x : bool) == (y : bool))) (Test_ensures_3, ((g : bool) == (~old (g : bool))))
body: init (old$g : bool) := (g : bool)
g := (((~Bool.And : (arrow bool (arrow bool bool))) (g : bool)) #true)
y := (((~Bool.Or : (arrow bool (arrow bool bool))) (x : bool)) (x : bool))
assert [assert_0] ((g : bool) == (old$g : bool))

Errors: #[]
-/
#guard_msgs in
#eval TransM.run (translateProgram simpleProcPgm)

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: assert_0
Assumptions:


Proof Obligation:
(((~Bool.And $__g0) #true) == $__g0)

Label: Test_ensures_1
Assumptions:


Proof Obligation:
(((~Bool.Or $__x1) $__x1) == $__x1)

Label: Test_ensures_2
Assumptions:


Proof Obligation:
($__x1 == ((~Bool.Or $__x1) $__x1))

Label: Test_ensures_3
Assumptions:


Proof Obligation:
(((~Bool.And $__g0) #true) == $__g0)

Wrote problem to vcs/assert_0.smt2.
Wrote problem to vcs/Test_ensures_1.smt2.
Wrote problem to vcs/Test_ensures_2.smt2.
Wrote problem to vcs/Test_ensures_3.smt2.
---
info:
Obligation: assert_0
Result: verified

Obligation: Test_ensures_1
Result: verified

Obligation: Test_ensures_2
Result: verified

Obligation: Test_ensures_3
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" simpleProcPgm

---------------------------------------------------------------------
