/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Core.Verifier


---------------------------------------------------------------------
namespace Strata


def oldModifiesPgm :=
#strata
program Core;

procedure f(x : bool, g : bool) returns (g : bool, z : bool)
spec {
  ensures (z == old g);
  // g is not listed in modifies
}
{
  z := g;
};

procedure h_correct(g : bool, i : bool) returns (g : bool, r : bool)
spec {
  requires (g == false);
  ensures (r == true);
}
{
  g := true;
  call g, r := f(i, g);
};

procedure h_incorrect(g : bool, i : bool) returns (g : bool, r : bool)
spec {
  requires (g == false);
  ensures (r == false);
}
{
  g := true;
  call g, r := f(i, g);
};
#end

/--
info:
Obligation: f_ensures_0
Property: assert
Result: ✅ pass

Obligation: h_correct_ensures_1
Property: assert
Result: ✅ pass

Obligation: h_incorrect_ensures_1
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval verify oldModifiesPgm (options := .quiet)

/--
info:
Obligation: h_correct_ensures_1
Property: assert
Result: ✅ pass

Obligation: h_incorrect_ensures_1
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval verify oldModifiesPgm (options := .quiet) (proceduresToVerify := ["h_correct", "h_incorrect"])
