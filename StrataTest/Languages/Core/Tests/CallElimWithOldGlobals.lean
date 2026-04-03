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

var g : bool;
var i : bool;

procedure f(x : bool) returns (z : bool)
spec {
  ensures (z == old g);
  // g is not listed in modifies
}
{
  z := g;
};

procedure h_correct() returns (r : bool)
spec {
  requires (g == false);
  ensures (r == true);
  modifies g;
}
{
  g := true;
  call r := f(i);
};

procedure h_incorrect() returns (r : bool)
spec {
  requires (g == false);
  ensures (r == false);
  modifies g;
}
{
  g := true;
  call r := f(i);
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
Result: ❌ fail
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
