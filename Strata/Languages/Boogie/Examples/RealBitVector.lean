/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def realEnv : Environment :=
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
#eval TransM.run (translateProgram (realEnv.commands)) |>.snd |>.isEmpty

/--
info: func x :  () → real;
func y :  () → real;
axiom real_x_ge_1: (((~Real.Ge : (arrow real (arrow real bool))) ~x) (#1.0 : real));
axiom real_y_ge_2: (((~Real.Ge : (arrow real (arrow real bool))) ~y) (#2.0 : real));
(procedure P :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: assert [real_add_ge_good] (((~Real.Ge : (arrow real (arrow real bool))) (((~Real.Add : (arrow real (arrow real real))) ~x) ~y)) (#3.0 : real))
assert [real_add_ge_bad] (((~Real.Ge : (arrow real (arrow real bool))) (((~Real.Add : (arrow real (arrow real real))) ~x) ~y)) (#4.0 : real))

Errors: #[]
-/
#guard_msgs in
#eval TransM.run (translateProgram (realEnv.commands))

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: real_add_ge_good
Assumptions:
(real_y_ge_2, ((~Real.Ge ~y) #2.0))
(real_x_ge_1, ((~Real.Ge ~x) #1.0))
Proof Obligation:
((~Real.Ge ((~Real.Add ~x) ~y)) #3.0)

Label: real_add_ge_bad
Assumptions:
(real_y_ge_2, ((~Real.Ge ~y) #2.0))
(real_x_ge_1, ((~Real.Ge ~x) #1.0))
Proof Obligation:
((~Real.Ge ((~Real.Add ~x) ~y)) #4.0)

Wrote problem to vcs/real_add_ge_good.smt2.
Wrote problem to vcs/real_add_ge_bad.smt2.


Obligation real_add_ge_bad: could not be proved!

Result: failed
CEx: ⏎

Evaluated program:
func x :  () → real;
func y :  () → real;
axiom real_x_ge_1: (((~Real.Ge : (arrow real (arrow real bool))) (~x : real)) (#1.0 : real));
axiom real_y_ge_2: (((~Real.Ge : (arrow real (arrow real bool))) (~y : real)) (#2.0 : real));
(procedure P :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: assert [real_add_ge_good] ((~Real.Ge ((~Real.Add ~x) ~y)) #3.0)
assert [real_add_ge_bad] ((~Real.Ge ((~Real.Add ~x) ~y)) #4.0)

---
info:
Obligation: real_add_ge_good
Result: verified

Obligation: real_add_ge_bad
Result: failed
CEx:
-/
#guard_msgs in
#eval verify "cvc5" realEnv

---------------------------------------------------------------------

def bvEnv : Environment :=
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
#eval TransM.run (translateProgram (bvEnv.commands)) |>.snd |>.isEmpty

/--
info: func x :  () → bv8;
func y :  () → bv8;
axiom bv_x_ge_1: (((~Bv8.Le : (arrow bv8 (arrow bv8 bool))) (#1 : bv8)) ~x);
axiom bv_y_ge_2: (((~Bv8.Le : (arrow bv8 (arrow bv8 bool))) (#2 : bv8)) ~y);
(procedure P :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: assert [bv_add_ge] ((((~Bv8.Add : (arrow bv8 (arrow bv8 bv8))) ~x) ~y) == (((~Bv8.Add : (arrow bv8 (arrow bv8 bv8))) ~y) ~x))

(procedure Q :  ((x : bv1)) → ((r : bv1)))
modifies: []
preconditions: ⏎
postconditions: (Q_ensures_0, (r == (((~Bv1.Sub : (arrow bv1 (arrow bv1 bv1))) x) x)))
body: r := (((~Bv1.Add : (arrow bv1 (arrow bv1 bv1))) x) x)

Errors: #[]
-/
#guard_msgs in
#eval TransM.run (translateProgram (bvEnv.commands))

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: bv_add_ge
Assumptions:
(bv_y_ge_2, ((~Bv8.Le #2) ~y))
(bv_x_ge_1, ((~Bv8.Le #1) ~x))
Proof Obligation:
(((~Bv8.Add ~x) ~y) == ((~Bv8.Add ~y) ~x))

Label: Q_ensures_0
Assumptions:
(bv_x_ge_1, ((~Bv8.Le #1) ~x))
Proof Obligation:
(((~Bv1.Add $__x0) $__x0) == ((~Bv1.Sub $__x0) $__x0))

Wrote problem to vcs/bv_add_ge.smt2.
Wrote problem to vcs/Q_ensures_0.smt2.
---
info:
Obligation: bv_add_ge
Result: verified

Obligation: Q_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" bvEnv
