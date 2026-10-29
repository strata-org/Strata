/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)
---------------------------------------------------------------------
namespace Strata

def realPgm : Program :=
#strata
program Core;

const x : real;
const y : real;

axiom [real_x_ge_1]: real.ge(x, 1.0);
axiom [real_y_ge_2]: real.ge(y, 2.0);

procedure P()
{
  assert [real_add_ge_good]: real.ge(real.add(x, y), 3.0);
  assert [real_add_ge_bad]: real.ge(real.add(x, y), 4.0);
};
#end

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram realPgm) |>.snd |>.isEmpty

/--
info: program Core;

function x () : real;
function y () : real;
axiom [real_x_ge_1]: real.ge(x, 1.0);
axiom [real_y_ge_2]: real.ge(y, 2.0);
procedure P ()
{
  assert [real_add_ge_good]: real.ge(real.add(x, y), 3.0);
  assert [real_add_ge_bad]: real.ge(real.add(x, y), 4.0);
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram realPgm) |>.fst

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: real_add_ge_good
Property: assert
Assumptions:
real_x_ge_1: real.ge(x, 1.0)
real_y_ge_2: real.ge(y, 2.0)
Obligation:
real.ge(real.add(x, y), 3.0)

Label: real_add_ge_bad
Property: assert
Assumptions:
real_x_ge_1: real.ge(x, 1.0)
real_y_ge_2: real.ge(y, 2.0)
Obligation:
real.ge(real.add(x, y), 4.0)

---
info:
Obligation: real_add_ge_good
Property: assert
Result: ✅ pass

Obligation: real_add_ge_bad
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify realPgm

---------------------------------------------------------------------

def bvPgm : Program :=
#strata
program Core;

const x : bv W8;
const y : bv W8;

axiom [bv_x_ge_1]: bv8.uLe(bv{8}(1), x);
axiom [bv_y_ge_2]: bv8.uLe(bv{8}(2), y);

procedure P()
{
  assert [bv_add_ge]: bv8.add(x, y) == bv8.add(y, x);
};

procedure Q(x: bv W1, out r: bv W1)
spec {
  ensures r == bv1.sub(x, x);
} {
  r := bv1.add(x, x);
};
#end

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram bvPgm) |>.snd |>.isEmpty

/--
info: program Core;

function x () : bv W8;
function y () : bv W8;
axiom [bv_x_ge_1]: bv8.uLe(bv{8}(1), x);
axiom [bv_y_ge_2]: bv8.uLe(bv{8}(2), y);
procedure P ()
{
  assert [bv_add_ge]: bv8.add(x, y) == bv8.add(y, x);
};
procedure Q (x : bv W1, out r : bv W1)
spec {
  ensures [Q_ensures_0]: r == bv1.sub(x, x);
  } {
  r := bv1.add(x, x);
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram bvPgm) |>.fst

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: bv_add_ge
Property: assert
Assumptions:
bv_x_ge_1: bv8.uLe(bv{8}(1), x)
bv_y_ge_2: bv8.uLe(bv{8}(2), y)
Obligation:
bv8.add(x, y) == bv8.add(y, x)

Label: Q_ensures_0
Property: assert
Assumptions:
bv_x_ge_1: bv8.uLe(bv{8}(1), x)
bv_y_ge_2: bv8.uLe(bv{8}(2), y)
Obligation:
bv1.add(x@1, x@1) == bv1.sub(x@1, x@1)

---
info:
Obligation: bv_add_ge
Property: assert
Result: ✅ pass

Obligation: Q_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify bvPgm

def bvMoreOpsPgm : Program :=
#strata
program Core;

procedure P(x: bv W8, y: bv W8, z: bv W8) {
  assert [add_comm]: bv8.add(x, y) == bv8.add(y, x);
  assert [xor_cancel]: bv8.xor(x, x) == bv{8}(0);
  assert [div_shift]: bv8.uDiv(x, bv{8}(2)) == bv8.uShr(x, bv{8}(1));
  assert [mul_shift]: bv8.mul(x, bv{8}(2)) == bv8.shl(x, bv{8}(1));
  assert [demorgan]: bv8.not(bv8.and(x, y)) == bv8.or(bv8.not(x), bv8.not(y));
  assert [mod_and]: bv8.uMod(x, bv{8}(2)) == bv8.and(x, bv{8}(1));
  assert [bad_shift]: bv8.uShr(x, y) == bv8.shl(x, y);
  var xy : bv W16 := bvconcat{8}{8}(x, y);
  var xy2 : bv W32 := bvconcat{16}{16}(xy, xy);
  var xy4 : bv W64 := bvconcat{32}{32}(xy2, xy2);
};
#end

/--
info:
Obligation: add_comm
Property: assert
Result: ✅ pass

Obligation: xor_cancel
Property: assert
Result: ✅ pass

Obligation: div_shift
Property: assert
Result: ✅ pass

Obligation: mul_shift
Property: assert
Result: ✅ pass

Obligation: demorgan
Property: assert
Result: ✅ pass

Obligation: mod_and
Property: assert
Result: ✅ pass

Obligation: bad_shift
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify bvMoreOpsPgm (options := .quiet)

end Strata
end
