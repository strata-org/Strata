/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def realPgm : Program :=
#strata
program Boogie;

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
info: func x :  () → real;
func y :  () → real;
axiom real_x_ge_1: (((~Real.Ge : (arrow real (arrow real bool))) (~x : real)) #1);
axiom real_y_ge_2: (((~Real.Ge : (arrow real (arrow real bool))) (~y : real)) #2);
(procedure P :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: assert [real_add_ge_good] (((~Real.Ge : (arrow real (arrow real bool))) (((~Real.Add : (arrow real (arrow real real))) (~x : real)) (~y : real))) #3)
assert [real_add_ge_bad] (((~Real.Ge : (arrow real (arrow real bool))) (((~Real.Add : (arrow real (arrow real real))) (~x : real)) (~y : real))) #4)

Errors: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram realPgm)

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: real_add_ge_good
Property: assert
Assumptions:

(real_x_ge_1, ((~Real.Ge ~x) #1))
(real_y_ge_2, ((~Real.Ge ~y) #2))
Proof Obligation:
((~Real.Ge ((~Real.Add ~x) ~y)) #3)

Label: real_add_ge_bad
Property: assert
Assumptions:

(real_x_ge_1, ((~Real.Ge ~x) #1))
(real_y_ge_2, ((~Real.Ge ~y) #2))
Proof Obligation:
((~Real.Ge ((~Real.Add ~x) ~y)) #4)

Wrote problem to vcs/real_add_ge_good.smt2.
Wrote problem to vcs/real_add_ge_bad.smt2.


Result: Obligation: real_add_ge_bad
Property: assert
Result: ❌ fail


Evaluated program:
func x :  () → real;
func y :  () → real;
axiom real_x_ge_1: (((~Real.Ge : (arrow real (arrow real bool))) (~x : real)) #1);
axiom real_y_ge_2: (((~Real.Ge : (arrow real (arrow real bool))) (~y : real)) #2);
(procedure P :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: assert [real_add_ge_good] ((~Real.Ge ((~Real.Add ~x) ~y)) #3)
assert [real_add_ge_bad] ((~Real.Ge ((~Real.Add ~x) ~y)) #4)

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
#eval verify "cvc5" realPgm

---------------------------------------------------------------------

def bvPgm : Program :=
#strata
program Boogie;

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
info: func x :  () → bv8;
func y :  () → bv8;
axiom bv_x_ge_1: (((~Bv8.ULe : (arrow bv8 (arrow bv8 bool))) #1) (~x : bv8));
axiom bv_y_ge_2: (((~Bv8.ULe : (arrow bv8 (arrow bv8 bool))) #2) (~y : bv8));
(procedure P :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: assert [bv_add_ge] ((((~Bv8.Add : (arrow bv8 (arrow bv8 bv8))) (~x : bv8)) (~y : bv8)) == (((~Bv8.Add : (arrow bv8 (arrow bv8 bv8))) (~y : bv8)) (~x : bv8)))

(procedure Q :  ((x : bv1)) → ((r : bv1)))
modifies: []
preconditions: ⏎
postconditions: (Q_ensures_0, ((r : bv1) == (((~Bv1.Sub : (arrow bv1 (arrow bv1 bv1))) (x : bv1)) (x : bv1))))
body: r := (((~Bv1.Add : (arrow bv1 (arrow bv1 bv1))) (x : bv1)) (x : bv1))

Errors: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram bvPgm)

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: bv_add_ge
Property: assert
Assumptions:

(bv_x_ge_1, ((~Bv8.ULe #1) ~x))
(bv_y_ge_2, ((~Bv8.ULe #2) ~y))
Proof Obligation:
(((~Bv8.Add ~x) ~y) == ((~Bv8.Add ~y) ~x))

Label: Q_ensures_0
Property: assert
Assumptions:

(bv_x_ge_1, ((~Bv8.ULe #1) ~x))
(bv_y_ge_2, ((~Bv8.ULe #2) ~y))
Proof Obligation:
(((~Bv1.Add $__x0) $__x0) == ((~Bv1.Sub $__x0) $__x0))

Wrote problem to vcs/bv_add_ge.smt2.
Wrote problem to vcs/Q_ensures_0.smt2.
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
#eval verify "cvc5" bvPgm

def bvMoreOpsPgm : Program :=
#strata
program Boogie;

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
Model:
($__x0, #b10011001) ($__y1, #b00000010)
-/
#guard_msgs in
#eval verify "cvc5" bvMoreOpsPgm Inhabited.default Options.quiet
