/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Boogie.Verifier
import Strata.Languages.Boogie.CallGraph

---------------------------------------------------------------------
namespace Strata

def axiomPgm1 :=
#strata
program Boogie;

const x : int;
axiom [a1]: x == 5;

const y : int;
axiom [a2]: y == 2;

function f(x: int): int;
axiom [f1]: (forall y : int :: f(y) > y);

procedure P() returns (ret : int)
  spec {
    ensures [use_f1]: ret > 7;
  }
{
  assert [use_a1_a2]: x > y;
  ret := f(x + y);
};

procedure P2() returns ()
{
  assert [use_a1_again]: y == 2;
  assert [use_a2_again]: f(y) > y;
};

#end

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: use_a1_a2
Property: assert
Assumptions:

(a1, (~x == #5))
(a2, (~y == #2)) (f1, (∀ ((~Int.Gt (~f %0)) %0)))
Proof Obligation:
((~Int.Gt ~x) ~y)

Label: use_f1
Property: assert
Assumptions:

(a1, (~x == #5))
(a2, (~y == #2)) (f1, (∀ ((~Int.Gt (~f %0)) %0)))
Proof Obligation:
((~Int.Gt (~f ((~Int.Add ~x) ~y))) #7)

Label: use_a1_again
Property: assert
Assumptions:

(a1, (~x == #5))
(a2, (~y == #2)) (f1, (∀ ((~Int.Gt (~f %0)) %0)))
Proof Obligation:
(~y == #2)

Label: use_a2_again
Property: assert
Assumptions:

(a1, (~x == #5))
(a2, (~y == #2)) (f1, (∀ ((~Int.Gt (~f %0)) %0)))
Proof Obligation:
((~Int.Gt (~f ~y)) ~y)

---
info:
Obligation: use_a1_a2
Property: assert
Result: ✅ pass

Obligation: use_f1
Property: assert
Result: ✅ pass

Obligation: use_a1_again
Property: assert
Result: ✅ pass

Obligation: use_a2_again
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" axiomPgm1

---------------------------------------------------------------------

def axiomPgm2 :=
#strata
program Boogie;

function f(x : int) : int;
function g(x : int) : int;

axiom [f_g_ax]: (forall x : int :: { f(x) } f(x) == g(x) + 1);
// NOTE the trigger `f(x)` in `g_ax` below, which causes the
// dependency analysis to include this axiom in all goals involving `f(x)`.
axiom [g_ax]:   (forall x : int :: { g(x), f(x) } g(x) == x * 2);

procedure main (x : int) returns () {

assert [axiomPgm2_main_assert]: (x >= 0 ==> f(x) > x);
};
#end

/-- info: [] -/
#guard_msgs in
#eval let (program, _) := Boogie.getProgram axiomPgm2
      Std.format (Boogie.Program.getIrrelevantAxioms program ["f"])

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: axiomPgm2_main_assert
Property: assert
Assumptions:

(f_g_ax, (∀ ((~f %0) == ((~Int.Add (~g %0)) #1))))
(g_ax, (∀ ((~g %0) == ((~Int.Mul %0) #2))))
Proof Obligation:
((~Bool.Implies ((~Int.Ge $__x0) #0)) ((~Int.Gt (~f $__x0)) $__x0))

---
info:
Obligation: axiomPgm2_main_assert
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "z3" axiomPgm2

---------------------------------------------------------------------
