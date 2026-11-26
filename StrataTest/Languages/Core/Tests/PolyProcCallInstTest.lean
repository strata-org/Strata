/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)

/-!
# A polymorphic procedure called at several types

Call elimination inlines a polymorphic procedure's contract at each call site, at
that call's type instance, so one procedure called at two concrete types in one
body type-checks.

`Core.verify` reports each obligation by label and verdict, so these tests pin
which obligation fails. The callees use `free ensures`, so the postcondition is
inlined as an assume at the call site without a proof obligation for the
polymorphic body; the final case adds a non-free `requires`, inlined as a
per-site assert.
-/

namespace Strata.PolyProcCallInstMulti

-- One polymorphic procedure called at `int` and at `bool` in a single body. Each
-- call instantiates `a` at its own argument type, so both obligations pass.
def multiInstPgm : Program :=
#strata
program Core;
procedure idp<a>(x : a, out r : a)
spec {
  free ensures (r == x);
};
procedure Test() spec { ensures true; }
{
  var ai : int;
  call idp(7, out ai);
  assert (ai == 7);
  var bb : bool;
  call idp(true, out bb);
  assert (bb == true);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Assumptions:
callElimPost_idp_ensures_0_2: ai@2 == 7
Obligation:
ai@2 == 7

Label: assert_1
Property: assert
Assumptions:
callElimPost_idp_ensures_0_2: ai@2 == 7
callElimPost_idp_ensures_0_5: bb@2 == true
Obligation:
bb@2 == true

Label: Test_ensures_0
Property: assert
Assumptions:
callElimPost_idp_ensures_0_2: ai@2 == 7
callElimPost_idp_ensures_0_5: bb@2 == true
Obligation:
true

---
info:
Obligation: assert_0
Property: assert
Result: ✅ pass

Obligation: assert_1
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify multiInstPgm

end Strata.PolyProcCallInstMulti

---------------------------------------------------------------------

namespace Strata.PolyProcCallInstSoundness

-- The multi-instantiation case with a false `bool` assertion (`bb == false` after
-- `idp(true)`): exactly `assert_1` fails and `assert_0` passes.
def wrongBoolPgm : Program :=
#strata
program Core;
procedure idp<a>(x : a, out r : a)
spec {
  free ensures (r == x);
};
procedure Test() spec { ensures true; }
{
  var ai : int;
  call idp(7, out ai);
  assert (ai == 7);
  var bb : bool;
  call idp(true, out bb);
  assert (bb == false);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Assumptions:
callElimPost_idp_ensures_0_2: ai@2 == 7
Obligation:
ai@2 == 7

Label: assert_1
Property: assert
Assumptions:
callElimPost_idp_ensures_0_2: ai@2 == 7
callElimPost_idp_ensures_0_5: bb@2 == true
Obligation:
bb@2 == false

Label: Test_ensures_0
Property: assert
Assumptions:
callElimPost_idp_ensures_0_2: ai@2 == 7
callElimPost_idp_ensures_0_5: bb@2 == true
Obligation:
true

---
info:
Obligation: assert_0
Property: assert
Result: ✅ pass

Obligation: assert_1
Property: assert
Result: ❌ fail
Model:
(bb@2, true) (ai@2, 7) 

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify wrongBoolPgm

end Strata.PolyProcCallInstSoundness

---------------------------------------------------------------------

namespace Strata.PolyProcCallInstOtherBug

-- A procedure that calls `idp` at `int` and at `bool` does not hide a bug elsewhere:
-- the false `assert (1 == 2)` in `RealBug` is reported at its own label, `assert_0`.
def otherBugPgm : Program :=
#strata
program Core;
procedure idp<a>(x : a, out r : a)
spec {
  free ensures (r == x);
};
procedure RealBug() spec { ensures true; }
{
  assert (1 == 2);
};
procedure TwoInstances() spec { ensures true; }
{
  var ai : int;
  call idp(7, out ai);
  var bb : bool;
  call idp(true, out bb);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Obligation:
false

Label: RealBug_ensures_0
Property: assert
Obligation:
true

Label: TwoInstances_ensures_0
Property: assert
Assumptions:
callElimPost_idp_ensures_0_2: ai@2 == 7
callElimPost_idp_ensures_0_5: bb@2 == true
Obligation:
true



Obligation assert_0: failed!

Result obtained during evaluation.
---
info:
Obligation: assert_0
Property: assert
Result: ❌ fail

Obligation: RealBug_ensures_0
Property: assert
Result: ✅ pass

Obligation: TwoInstances_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify otherBugPgm

end Strata.PolyProcCallInstOtherBug

---------------------------------------------------------------------

namespace Strata.PolyProcCallInstOldInout

-- `bump<a>` takes an inout `g : a` and has `free ensures (z == old g)`, so the temporary
-- for `old g` has the callee's type variable `a` and is instantiated like the other
-- parameters. `g := 5` before the call makes `old g` differ from the post-call `g`, and
-- the inlined assume becomes `r == 5`, so `assert (r == 5)` passes only if the
-- temporary has the right type.
def oldInoutPgm : Program :=
#strata
program Core;
procedure bump<a>(inout g : a, out z : a)
spec {
  free ensures (z == old g);
}
{
  z := g;
};
procedure Test(inout g : int, out r : int) spec { ensures true; }
{
  g := 5;
  call bump(inout g, out r);
  assert (r == 5);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Assumptions:
$__callElimAssume_bump_ensures_0_4: r@2 == 5
Obligation:
r@2 == 5

Label: Test_ensures_0
Property: assert
Assumptions:
$__callElimAssume_bump_ensures_0_4: r@2 == 5
Obligation:
true

---
info:
Obligation: assert_0
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify oldInoutPgm

end Strata.PolyProcCallInstOldInout

---------------------------------------------------------------------

namespace Strata.PolyProcCallInstTypeParams

-- A callee with two type parameters, `swap<a, b>`, called at two different instances in
-- one body: `swap(1, true, ...)` binds `(a, b) = (int, bool)` and `swap(false, 2, ...)`
-- binds `(a, b) = (bool, int)`. Each site's contract is inlined at its own instance and
-- all four assertions pass.
def multiTypeParamPgm : Program :=
#strata
program Core;
procedure swap<a, b>(x : a, y : b, out rx : b, out ry : a)
spec {
  free ensures (rx == y);
  free ensures (ry == x);
};
procedure Test() spec { ensures true; }
{
  var i : int;
  var b : bool;
  call swap(1, true, out b, out i);
  assert (b == true);
  assert (i == 1);
  var b2 : bool;
  var i2 : int;
  call swap(false, 2, out i2, out b2);
  assert (i2 == 2);
  assert (b2 == false);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Assumptions:
callElimPost_swap_ensures_0_4: b@2 == true
callElimPost_swap_ensures_1_5: i@2 == 1
Obligation:
b@2 == true

Label: assert_1
Property: assert
Assumptions:
callElimPost_swap_ensures_0_4: b@2 == true
callElimPost_swap_ensures_1_5: i@2 == 1
Obligation:
i@2 == 1

Label: assert_2
Property: assert
Assumptions:
callElimPost_swap_ensures_0_4: b@2 == true
callElimPost_swap_ensures_1_5: i@2 == 1
callElimPost_swap_ensures_0_10: i2@2 == 2
callElimPost_swap_ensures_1_11: b2@2 == false
Obligation:
i2@2 == 2

Label: assert_3
Property: assert
Assumptions:
callElimPost_swap_ensures_0_4: b@2 == true
callElimPost_swap_ensures_1_5: i@2 == 1
callElimPost_swap_ensures_0_10: i2@2 == 2
callElimPost_swap_ensures_1_11: b2@2 == false
Obligation:
b2@2 == false

Label: Test_ensures_0
Property: assert
Assumptions:
callElimPost_swap_ensures_0_4: b@2 == true
callElimPost_swap_ensures_1_5: i@2 == 1
callElimPost_swap_ensures_0_10: i2@2 == 2
callElimPost_swap_ensures_1_11: b2@2 == false
Obligation:
true

---
info:
Obligation: assert_0
Property: assert
Result: ✅ pass

Obligation: assert_1
Property: assert
Result: ✅ pass

Obligation: assert_2
Property: assert
Result: ✅ pass

Obligation: assert_3
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify multiTypeParamPgm

end Strata.PolyProcCallInstTypeParams

---------------------------------------------------------------------

namespace Strata.PolyProcCallInstQuantPost

-- A quantified postcondition whose binder has the callee's type variable
-- (`forall y : a :: ...`): `pick<a>` at `int` and `bool` yields `forall y : int` at the
-- first site and `forall y : bool` at the second, and all obligations pass.
def quantPostPgm : Program :=
#strata
program Core;
procedure pick<a>(x : a, out r : a)
spec {
  free ensures (forall y : a :: (y == x) ==> (y == r));
};
procedure Test() spec { ensures true; }
{
  var ai : int;
  call pick(7, out ai);
  assert (ai == 7);
  var bb : bool;
  call pick(true, out bb);
  assert (bb == true);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Assumptions:
callElimPost_pick_ensures_0_2: forall y : int :: y == 7 ==> y == ai@2
Obligation:
ai@2 == 7

Label: assert_1
Property: assert
Assumptions:
callElimPost_pick_ensures_0_2: forall y : int :: y == 7 ==> y == ai@2
callElimPost_pick_ensures_0_5: forall y : bool :: y == true ==> y == bb@2
Obligation:
bb@2 == true

Label: Test_ensures_0
Property: assert
Assumptions:
callElimPost_pick_ensures_0_2: forall y : int :: y == 7 ==> y == ai@2
callElimPost_pick_ensures_0_5: forall y : bool :: y == true ==> y == bb@2
Obligation:
true

---
info:
Obligation: assert_0
Property: assert
Result: ✅ pass

Obligation: assert_1
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify quantPostPgm

end Strata.PolyProcCallInstQuantPost

---------------------------------------------------------------------

namespace Strata.PolyProcCallInstRequires

-- A non-free `requires` is inlined as an assert at each call site, at two instances:
-- the labels are per site (`callElimAssert_req_requires_0_2` and `_0_6`) and so are
-- the binder types (`forall y : int` and `forall y : bool`).
def reqPgm : Program :=
#strata
program Core;
procedure req<a>(x : a, out r : a)
spec {
  requires (forall y : a :: (y == x) ==> (y == x));
  free ensures (r == x);
};
procedure Test() spec { ensures true; }
{
  var ai : int;
  call req(7, out ai);
  assert (ai == 7);
  var bb : bool;
  call req(true, out bb);
  assert (bb == true);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: callElimAssert_req_requires_0_2
Property: assert
Obligation:
forall y : int :: y == 7 ==> y == 7

Label: assert_0
Property: assert
Assumptions:
callElimPost_req_ensures_1_3: ai@2 == 7
Obligation:
ai@2 == 7

Label: callElimAssert_req_requires_0_6
Property: assert
Assumptions:
callElimPost_req_ensures_1_3: ai@2 == 7
Obligation:
forall y : bool :: y == true ==> y == true

Label: assert_1
Property: assert
Assumptions:
callElimPost_req_ensures_1_3: ai@2 == 7
callElimPost_req_ensures_1_7: bb@2 == true
Obligation:
bb@2 == true

Label: Test_ensures_0
Property: assert
Assumptions:
callElimPost_req_ensures_1_3: ai@2 == 7
callElimPost_req_ensures_1_7: bb@2 == true
Obligation:
true

---
info:
Obligation: callElimAssert_req_requires_0_2
Property: assert
Result: ✅ pass

Obligation: assert_0
Property: assert
Result: ✅ pass

Obligation: callElimAssert_req_requires_0_6
Property: assert
Result: ✅ pass

Obligation: assert_1
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify reqPgm

end Strata.PolyProcCallInstRequires

end
