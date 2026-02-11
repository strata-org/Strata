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

/-

info: func x :  () → real;
func y :  () → real;
axiom real_x_ge_1: ((~Real.Ge : (arrow real (arrow real bool))) (~x : real) #1);
axiom real_y_ge_2: ((~Real.Ge : (arrow real (arrow real bool))) (~y : real) #2);
procedure P :  () → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  assert [real_add_ge_good] ((~Real.Ge : (arrow real (arrow real bool)))
   ((~Real.Add : (arrow real (arrow real real))) (~x : real) (~y : real))
   #3)
  assert [real_add_ge_bad] ((~Real.Ge : (arrow real (arrow real bool)))
   ((~Real.Add : (arrow real (arrow real real))) (~x : real) (~y : real))
   #4)
}
Errors: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram realPgm)

/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval verify "cvc5" realPgm

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

/-

info: func x :  () → bv8;
func y :  () → bv8;
axiom bv_x_ge_1: ((~Bv8.ULe : (arrow bv8 (arrow bv8 bool))) #1 (~x : bv8));
axiom bv_y_ge_2: ((~Bv8.ULe : (arrow bv8 (arrow bv8 bool))) #2 (~y : bv8));
procedure P :  () → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  assert [bv_add_ge] (((~Bv8.Add : (arrow bv8 (arrow bv8 bv8)))
    (~x : bv8)
    (~y : bv8)) == ((~Bv8.Add : (arrow bv8 (arrow bv8 bv8))) (~y : bv8) (~x : bv8)))
}
procedure Q :  ((x : bv1)) → ((r : bv1))
  modifies: []
  preconditions: 
  postconditions: (Q_ensures_0, ((r : bv1) == ((~Bv1.Sub : (arrow bv1 (arrow bv1 bv1))) (x : bv1) (x : bv1))))
{
  r := ((~Bv1.Add : (arrow bv1 (arrow bv1 bv1))) (x : bv1) (x : bv1))
}
Errors: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram bvPgm)

/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval verify "cvc5" bvPgm

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

/-

info:
Obligation: add_comm
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" bvMoreOpsPgm (options := .quiet)
