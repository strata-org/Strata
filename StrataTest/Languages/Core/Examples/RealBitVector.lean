/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def realPgm : Program :=
#strata
program Core;

const x : real;
const y : real;

axiom [real_x_ge_1]: x >= 1.0;
axiom [real_y_ge_2]: y >= 2.0;

procedure P() returns ()
{
  assert [real_add_ge_good]: x + y >= 3.0;
  assert [real_add_ge_bad]: x + y >= 4.0;
};
#end

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram realPgm) |>.snd |>.isEmpty

/--
info: function x () : real;
function y () : real;
axiom [real_x_ge_1]: x >= 1.0;
axiom [real_y_ge_2]: y >= 2.0;
procedure P () returns ()
{
  assert [real_add_ge_good]: x + y >= 3.0;
  assert [real_add_ge_bad]: x + y >= 4.0;
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
real_x_ge_1: x >= 1.0
real_y_ge_2: y >= 2.0
Obligation:
x + y >= 3.0

Label: real_add_ge_bad
Property: assert
Assumptions:
real_x_ge_1: x >= 1.0
real_y_ge_2: y >= 2.0
Obligation:
x + y >= 4.0



Result: Obligation: real_add_ge_bad
Property: assert
Result: ❌ fail


[DEBUG] Evaluated program:
function x () : real;
function y () : real;
axiom [real_x_ge_1]: x >= 1.0;
axiom [real_y_ge_2]: y >= 2.0;
procedure P () returns ()
{
  assert [real_add_ge_good]: x + y >= 3.0;
  assert [real_add_ge_bad]: x + y >= 4.0;
  };

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
#eval verify realPgm

---------------------------------------------------------------------

def bvPgm : Program :=
#strata
program Core;

const x : bv8;
const y : bv8;

axiom [bv_x_ge_1]: bv{8}(1) <= x;
axiom [bv_y_ge_2]: bv{8}(2) <= y;

procedure P() returns ()
{
  assert [bv_add_ge]: x + y == y + x;
};

procedure Q(x: bv1) returns (r: bv1)
spec {
  ensures r == x - x;
} {
  r := x + x;
};
#end

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram bvPgm) |>.snd |>.isEmpty

/--
info: function x () : bv8;
function y () : bv8;
axiom [bv_x_ge_1]: bv{8}(1) <= x;
axiom [bv_y_ge_2]: bv{8}(2) <= y;
procedure P () returns ()
{
  assert [bv_add_ge]: x + y == y + x;
  };
procedure Q (x : bv1) returns (r : bv1)
spec {
  ensures [Q_ensures_0]: r == x - x;
  } {
  r := x + x;
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
bv_x_ge_1: bv{8}(1) <= x
bv_y_ge_2: bv{8}(2) <= y
Obligation:
x + y == y + x

Label: Q_ensures_0
Property: assert
Assumptions:
bv_x_ge_1: bv{8}(1) <= x
bv_y_ge_2: bv{8}(2) <= y
Obligation:
$__x0 + $__x0 == $__x0 - $__x0

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
#eval verify bvPgm

def bvMoreOpsPgm : Program :=
#strata
program Core;

procedure P(x: bv8, y: bv8, z: bv8) returns () {
  assert [add_comm]: x + y == y + x;
  assert [xor_cancel]: x ^ x == bv{8}(0);
  assert [div_shift]: x div bv{8}(2) == x >> bv{8}(1);
  assert [mul_shift]: x * bv{8}(2) == x << bv{8}(1);
  assert [demorgan]: ~(x & y) == ~x | ~y;
  assert [mod_and]: x mod bv{8}(2) == x & bv{8}(1);
  assert [bad_shift]: x >> y == x << y;
  var xy : bv16 := bvconcat{8}{8}(x, y);
  var xy2 : bv32 := bvconcat{16}{16}(xy, xy);
  var xy4 : bv64 := bvconcat{32}{32}(xy2, xy2);
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
#eval verify bvMoreOpsPgm (options := .quiet)
