/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def oldExprEnv : Environment :=
#strata
program Boogie;
var g : bool;
var g2 : bool;

procedure T1() returns (y : bool, z : bool)
spec {
  modifies g2;
  ensures  [T1_g_unchanged]: (g == old(g));
  ensures  [T1_g2_eq_old_g]: (g2 == old(g));
  ensures  [T1_y_eq_old_g2]: (y == old(g2));
  ensures  [T1_z_eq_y]:      (z == old(y));
}
{
  y := old(g2);
  g2 := old(g);
  z := old(g);
  assert [T1_z_eq_g]: (z == g);
  z := old(g2);
  assert [T1_z_eq_old_g2]: (z == old(g2));
};

procedure T2 () returns ()
spec {
  modifies g;
  modifies g2;
}
{
  var a : bool, b : bool;
  g := true;
  g2 := false;
  call a, b := T1();
  assert [T2_g2_eq_g]:     (g2 == g);
  assert [T2_g_true]:      (g == true);
  assert [T2_a_eq_false]:  (old(a) == false);
  assert [T2_b_eq_false]:  (b == false);
};
#end

/--
info: [Strata.Boogie] Type checking succeeded.


Obligation T1_z_eq_g proved via evaluation!


Obligation T1_z_eq_old_g2 proved via evaluation!


Obligation T1_g_unchanged proved via evaluation!


Obligation T1_g2_eq_old_g proved via evaluation!


Obligation T1_y_eq_old_g2 proved via evaluation!


Obligation T1_z_eq_y proved via evaluation!


Obligation T2_g_true proved via evaluation!


VCs:
Label: T2_g2_eq_g
Assumptions:
(<Origin:T1_Ensures>T1_g_unchanged, (g == #true))
(<Origin:T1_Ensures>T1_g2_eq_old_g, ($__g27 == #true))
(<Origin:T1_Ensures>T1_y_eq_old_g2, ($__a5 == #false))
(<Origin:T1_Ensures>T1_z_eq_y, ($__b6 == $__a5))
Proof Obligation:
($__g27 == #true)

Label: T2_a_eq_false
Assumptions:
(<Origin:T1_Ensures>T1_g_unchanged, (g == #true))
(<Origin:T1_Ensures>T1_g2_eq_old_g, ($__g27 == #true))
(<Origin:T1_Ensures>T1_y_eq_old_g2, ($__a5 == #false))
(<Origin:T1_Ensures>T1_z_eq_y, ($__b6 == $__a5))
Proof Obligation:
($__a5 == #false)

Label: T2_b_eq_false
Assumptions:
(<Origin:T1_Ensures>T1_g_unchanged, (g == #true))
(<Origin:T1_Ensures>T1_g2_eq_old_g, ($__g27 == #true))
(<Origin:T1_Ensures>T1_y_eq_old_g2, ($__a5 == #false))
(<Origin:T1_Ensures>T1_z_eq_y, ($__b6 == $__a5))
Proof Obligation:
($__b6 == #false)

Wrote problem to vcs/T2_g2_eq_g.smt2.
Wrote problem to vcs/T2_a_eq_false.smt2.
Wrote problem to vcs/T2_b_eq_false.smt2.
---
info:
Obligation: T2_g2_eq_g
Result: verified

Obligation: T2_a_eq_false
Result: verified

Obligation: T2_b_eq_false
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" oldExprEnv

---------------------------------------------------------------------
