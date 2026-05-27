/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-!
Smoke test for Boole grammar extensions introduced in `Boole.Grammar`.

This covers:
- `for ... to`
- `for ... downto`
- `for ... by`
- multiple loop invariants
- array update / nested map syntax
- quantifiers inside invariants
-/

private def grammarExtensions : Strata.Program :=
#strata
program Boole;

procedure f () returns ()
{
  for i : int := 0 to 10
    invariant 0 <= i
  {
    assert 0 <= i;
  }
};

procedure h_down_to () returns ()
{
  for k : int := 20 downto 0
      invariant k >= -1
  {
      assert k >= 0;
  }
};

procedure h_down_to_by () returns ()
{
  for k : int := 20 downto 0 by 2
      invariant k mod 2 == 0
      invariant k >= -2
  {
      assert k mod 2 == 0;
      assert k >= 0;
  }
};

procedure w () returns ()
{
  for j : int := 0 to 9
    invariant 0 <= j
    invariant j <= 10
    invariant j == 0 || j > 0
  {
    assert j <= 9;
  }
};

procedure test_arrays () returns ()
{
  var arr : Map int int;
  var idx : int;
  var sum : int;

  arr[0] := 5;
  arr[1] := 10;
  arr[2] := 15;

  sum := arr[0] + arr[1] + arr[2];

  idx := 0;
  for i : int := 0 to 9
    invariant 0 <= i && i <= 10
    invariant (∀ k : int . 0 <= k && k < i ==> arr[k] >= 0)
  {
    arr[i] := i * 2;
  }
};

#end

/--
info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: assert_0_523
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: assert_2_645
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: assert_4_804
Property: assert
Result: ✅ pass

Obligation: assert_5_831
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
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

Obligation: assert_7_987
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

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" grammarExtensions (options := .quiet)

example : Strata.smtVCsCorrectBoole grammarExtensions := by
  gen_smt_vcs_boole
  all_goals (try grind)
