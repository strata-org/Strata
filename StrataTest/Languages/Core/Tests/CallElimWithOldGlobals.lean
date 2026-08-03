/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section

---------------------------------------------------------------------
namespace Strata


def oldModifiesPgm :=
#strata
program Core;

procedure f(x : bool, inout g : bool, out z : bool)
spec {
  ensures (z == old g);
  // g is not listed in modifies
}
{
  z := g;
};

procedure h_correct(inout g : bool, i : bool, out r : bool)
spec {
  requires (g == false);
  ensures (r == true);
}
{
  g := true;
  call f(i, g, out g, out r);
};

procedure h_incorrect(inout g : bool, i : bool, out r : bool)
spec {
  requires (g == false);
  ensures (r == false);
}
{
  g := true;
  call f(i, g, out g, out r);
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
#eval Core.verify oldModifiesPgm (options := .quiet)

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
#eval Core.verify oldModifiesPgm (options := .quiet) (proceduresToVerify := ["h_correct", "h_incorrect"])


-- An inout call whose caller argument variable (`y`) differs in name from the
-- callee parameter (`x`), where the callee's postcondition mentions `old x`.
-- The `old x` substitution must key off the callee parameter name, not the
-- caller variable name; otherwise `old x` survives as a dangling free variable
-- and the call site fails to type-check.
private def oldInoutRenamedPgm :=
#strata
program Core;

procedure inc(inout x : int)
spec { ensures (x == old x + 1); }
{ x := x + 1; };

procedure caller(out r : int)
spec { ensures (r == 1); }
{
  var y : int := 0;
  call inc(inout y);
  r := y;
};
#end

/--
info:
Obligation: inc_ensures_0
Property: assert
Result: ✅ pass

Obligation: caller_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify oldInoutRenamedPgm (options := .quiet)


-- Multiple inout params, all renamed at the call site, each postcondition
-- referencing the *other* parameter's `old` value. Distinct initial values and
-- asymmetric ensures make a mis-aligned positional pairing (`lhs.zip
-- outputNames`) produce a detectably wrong result, exercising the alignment at
-- index > 0 rather than only the first slot.
private def oldInoutMultiPgm :=
#strata
program Core;

procedure shift(inout x : int, inout y : int)
spec {
  ensures (x == old y + 1);
  ensures (y == old x + 2);
}
{
  var tx : int := x;
  x := y + 1;
  y := tx + 2;
};

procedure caller2(out r1 : int, out r2 : int)
spec {
  ensures (r1 == 21);
  ensures (r2 == 12);
}
{
  var a : int := 10;
  var b : int := 20;
  call shift(inout a, inout b);
  r1 := a;
  r2 := b;
};
#end

/--
info:
Obligation: shift_ensures_0
Property: assert
Result: ✅ pass

Obligation: shift_ensures_1
Property: assert
Result: ✅ pass

Obligation: caller2_ensures_0
Property: assert
Result: ✅ pass

Obligation: caller2_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify oldInoutMultiPgm (options := .quiet)


-- Swapped-names regression: the caller declares locals named exactly like the
-- callee parameters (`x`, `y`) but passes them in *exchanged* positions
-- (`shift(inout y, inout x)`).  Verifies that `old x` in the callee's spec is
-- bound to the argument in `x`'s position (the caller's `y`), so all four
-- obligations discharge to the swapped values (`r1 == 22`, `r2 == 11`).
private def oldInoutSwapPgm :=
#strata
program Core;

procedure shift(inout x : int, inout y : int)
spec {
  ensures (x == old y + 1);
  ensures (y == old x + 2);
}
{
  var tx : int := x;
  x := y + 1;
  y := tx + 2;
};

procedure callerSwap(out r1 : int, out r2 : int)
spec {
  ensures (r1 == 22);
  ensures (r2 == 11);
}
{
  var x : int := 10;
  var y : int := 20;
  call shift(inout y, inout x);
  r1 := x;
  r2 := y;
};
#end

/--
info:
Obligation: shift_ensures_0
Property: assert
Result: ✅ pass

Obligation: shift_ensures_1
Property: assert
Result: ✅ pass

Obligation: callerSwap_ensures_0
Property: assert
Result: ✅ pass

Obligation: callerSwap_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify oldInoutSwapPgm (options := .quiet)

end Strata

end
