/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

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
    i := i + 1;
  }
};

procedure h_down_to () returns ()
{
  for k : int := 20 downto 0
      invariant k div 2 == 0
      invariant k >= 0
  {
      k := k - 2;
  }
};

procedure h_down_to_by () returns ()
{
  for k : int := 20 downto 0 by 2
      invariant k div 2 == 0
      invariant k >= 0
  {
      k := k - 2;
  }
};

procedure w () returns ()
{
  var j : int;
  j := 0;

  while (j < 10)
    invariant 0 <= j
    invariant j <= 10
    invariant j == 0 || j > 0
  {
    j := j + 1;
  }
};

procedure test_arrays () returns ()
{
  var arr : Map int int;
  var i : int;
  var sum : int;

  arr[0] := 5;
  arr[1] := 10;
  arr[2] := 15;

  sum := arr[0] + arr[1] + arr[2];

  i := 0;
  for i : int := 0 to 9
    invariant 0 <= i && i <= 10
    invariant (forall k : int :: 0 <= k && k < i ==> arr[k] >= 0)
  {
    arr[i] := i * 2;
  }
};

#end

#guard_msgs (drop info) in
#eval Strata.Boole.verify "cvc5" grammarExtensions

example : Strata.smtVCsCorrect grammarExtensions := by
  gen_smt_vcs
  all_goals (try grind)
