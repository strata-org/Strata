/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

private def verification_coverage :=
#strata
program Boole;

procedure testRequiresAssign(n: int) returns ()
spec
{
  requires n > 0; // was {:id "r0"} covered
  requires n < 10; // was {:id "r_not_1"} not covered
}
{
    var x: int;
    x := n + 1; // was {:id "a0"} covered
    assert x == n + 1; // was {:id "assert_a0"} covered
    x := 0; // was {:id "a_not_1"} not covered
    assert n > 0; // was {:id "assert_r0"} covered
};

procedure sum(n: int) returns (s: int)
spec
{
  requires n >= 0; // {:id "spre1"} covered
  ensures s == (n * (n + 1)) div 2; // {:id "spost"} covered
}
{
  var foo: int;

  s := 0;
  foo := 27;
  for i: int := 0 to (n - 1)
    invariant (0 <= i && i <= n)
    invariant (s == (i * (i + 1)) div 2)
    invariant (n >= 0)
  {
    s := s + (i + 1);
    foo := foo * 2; // {:id "update_foo"} not covered
  }
};

procedure contradictoryAssume(n: int) returns ()
{
    assume n > 0; // {:id "cont_assume_1"} covered
    assume n < 0; // {:id "cont_assume_2"} covered
    assume n == 5; // {:id "unreach_assume_1"} not covered
    assert n < 10; // {:id "unreach_assert_1"} not covered
};

// NB: an explicit `requires false` leads to _nothing_ being covered
procedure falseRequires(n: int) returns ()
spec
{
  requires n != n; // {:id "false_req"} covered
}
{
    assert false; // {:id "false_assert"} not covered
};

procedure contradictoryRequires(n: int) returns ()
spec
{
  requires n > 0; // {:id "cont_req_1"} covered
  requires n < 0; // {:id "cont_req_2"} covered
}
{
    assume n == 5; // {:id "n_eq_5"} not covered
    assert n > 10; // {:id "n_lt_10"} not covered
};

procedure assumeFalse() returns ()
{
  assume false; // {:id "assumeFalse"} covered
  assert 1 + 1 == 2; // {:id "assertSimple"} not covered
};

procedure testEnsuresCallee(n: int) returns (r: int)
spec
{
  requires n > 0; // {:id "ter0"} covered
  ensures r > n;  // {:id "tee0"} covered
  ensures r > 0;  // {:id "tee1"} covered when proving this procedure
}
{
  r := n + 1;
};

procedure testEnsuresCaller(n: int) returns (r: int)
spec
{
  requires n > 0; // {:id "ter1"} covered
  ensures r > n;  // {:id "tee_not_1"} covered
}
{
  var x: int;
  var y: int;
  call x := testEnsuresCallee(n + 1); // {:id "call1"} requires/ensures covered
  call y := testEnsuresCallee(n + 1); // {:id "call2"} requires/ensures covered
  assert y > 0; // {:id "call2_tee1"} covered
  r := x + y; // {:id "xy_sum"} covered
};

procedure obviouslyUnconstrainedCode(x: int) returns (a: int, b: int)
spec
{
  requires x > 10; // {:id "x_gt_10"} covered
  requires x < 100; // {:id "x_lt_100"} not covered
  ensures a > 10; // {:id "a_gt_10"} covered
}
{
  a := x + 1; // {:id "constrained"} covered
  b := x - 1; // {:id "not_constrained"} not covered: not constrained by ensures clause
};


procedure contradictoryEnsuresClause(x: int) returns (r: int)
spec
{
  requires x > 1; // {:id "xpos_abs"} covered (established by caller)
  ensures r > x; // {:id "cont_ens_abs"} covered (used by caller proof)
}
{
    r := x + 1;
};

// Call function that has contradictory ensures clauses.
procedure callContradictoryFunction(x: int) returns (r: int)
spec
{
  requires x > 1; // {:id "xpos_caller"} covered
  //ensures r < 0; // {:id "caller_ensures"} not covered
}
{
  call r := contradictoryEnsuresClause(x); // {:id "call_cont"} requires/ensures covered
  //r := r - 1; // {:id "unreachable_assignment"} not covered
};

function someInteger(i: int) : int
{
  3
}

axiom (∀ i: int . someInteger(i) == 3); // {:id "someInteger_value_axiom"}

procedure usesSomeInteger() returns (r: bool)
spec
{
  ensures r;
}
{
  r := someInteger(7) == 3;
};

#end

/-- info:
Obligation: assert_2_406
Property: assert
Result: ✅ pass

Obligation: assert_3_509
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: sum_ensures_5_652
Property: assert
Result: ✅ pass

Obligation: assert_10_1185
Property: assert
Result: ✅ pass

Obligation: assert_12_1419
Property: assert
Result: ✅ pass

Obligation: assert_16_1684
Property: assert
Result: ✅ pass

Obligation: assert_18_1820
Property: assert
Result: ✅ pass

Obligation: testEnsuresCallee_ensures_20_1983
Property: assert
Result: ✅ pass

Obligation: testEnsuresCallee_ensures_21_2025
Property: assert
Result: ✅ pass

Obligation: callElimAssert_testEnsuresCallee_requires_19_1941_7
Property: assert
Result: ✅ pass

Obligation: callElimAssert_testEnsuresCallee_requires_19_1941_2
Property: assert
Result: ✅ pass

Obligation: assert_24_2458
Property: assert
Result: ✅ pass

Obligation: testEnsuresCaller_ensures_23_2219
Property: assert
Result: ✅ pass

Obligation: obviouslyUnconstrainedCode_ensures_27_2723
Property: assert
Result: ✅ pass

Obligation: contradictoryEnsuresClause_ensures_29_3049
Property: assert
Result: ✅ pass

Obligation: callElimAssert_contradictoryEnsuresClause_requires_28_2979_12
Property: assert
Result: ✅ pass

Obligation: usesSomeInteger_ensures_32_3711
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" verification_coverage (options := .quiet)

example : Strata.smtVCsCorrect verification_coverage := by
  gen_smt_vcs
  all_goals grind
