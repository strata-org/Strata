/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

private def code_expression :=
#strata
program Boole;

type StrataHeap;
type StrataRef;
type StrataField (t: Type);

// Type constructors
type T;

// Constants
const zero : T;

// Functions
function IsProperIndex(i : int, size : int) : (bool);

// Uninterpreted procedures
// Implementations
procedure P(a : (Map int T), n : int) returns ()
spec {
  requires (∀ i: int . (IsProperIndex(i, n) ==> (a[i] == zero)));
}
{
  call Q(a, n);
};

procedure Q(a : (Map int T), n : int) returns ()
spec {
  requires (∀ i: int . (IsProperIndex(i, n) ==> (a[i] == zero)));
}
{
  call P(a, n);
};

procedure A(a : (Map int T), n : int) returns ()
{
  assert ((∀ i: int . (IsProperIndex(i, n) ==> (a[i] == zero))) ==> (∀ i: int . (IsProperIndex(i, n) ==> (a[i] == zero))));
};

procedure B(a : (Map int T), n : int) returns ()
{
  assert ((∀ i: int . (IsProperIndex(i, n) ==> (a[i] == zero))) ==> (∀ i: int . (IsProperIndex(i, n) ==> (a[i] == zero))));
};

procedure C(a : (Map int T), n : int) returns ()
{
  assume (∀ i: int . (IsProperIndex(i, n) ==> (a[i] == zero)));
  assert (∀ i: int . (IsProperIndex(i, n) ==> (a[i] == zero)));
};

procedure D(a : (Map int T), n : int) returns ()
{
  assume (∀ i: int . (IsProperIndex(i, n) ==> (a[i] == zero)));
  assert (∀ i: int . (IsProperIndex(i, n) ==> (a[i] == zero)));
};

#end

/--
info:
Obligation: callElimAssert_Q_requires_1_630_2
Property: assert
Result: ✅ pass

Obligation: callElimAssert_P_requires_0_481_5
Property: assert
Result: ✅ pass

Obligation: assert_2_774
Property: assert
Result: ✅ pass

Obligation: assert_3_959
Property: assert
Result: ✅ pass

Obligation: assert_5_1211
Property: assert
Result: ✅ pass

Obligation: assert_7_1400
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" code_expression (options := .quiet)

example : Strata.smtVCsCorrectBoole code_expression := by
  gen_smt_vcs_boole
  all_goals (try grind)
