/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.Grammar

---------------------------------------------------------------------

namespace Strata

---------------------------------------------------------------------
---------------------------------------------------------------------

/- DDM support for parsing and pretty-printing Boole -/
-- Extended version with support for:
-- ✓ Multiple invariants
-- ✓ For loops down to
-- Division operator `/`
-- Array assignment syntax
-- Quantifier syntax (forall, exists)
-- Simple procedure calls
-- Summation expressions
-- Structures and records (basic support)

#dialect
dialect Boole;

import Core;

category Step;
op step(e: Expr) : Step =>
  " by " e;

op for_statement (v : MonoBind, init : Expr,
  @[scope(v)] guard : bool, @[scope(v)] step : Expr,
  @[scope(v)] invs : Invariants, @[scope(v)] body : Block) : Statement =>
  "for " "(" v " := " init "; " guard "; " step ")" invs body;

op for_to_by_statement (v : MonoBind, init : Expr, limit : Expr,
  @[scope(v)] step : Option Step, @[scope(v)] invs : Invariants,
  @[scope(v)] body : Block) : Statement =>
  "for " v " := " init " to " limit step invs body;

op for_down_to_by_statement (v : MonoBind, init : Expr, limit : Expr,
  @[scope(v)] step : Option Step, @[scope(v)] invs : Invariants,
  @[scope(v)] body : Block) : Statement =>
  "for " v " := " init " downto " limit step invs body;

// multi-dimensional array assignment
op array_assign_2d (arr : Expr, idx1 : Expr, idx2 : Expr, rhs : Expr) : Statement =>
  arr "[" idx1 "][" idx2 "]" " := " rhs ";";

category Program;
op prog (commands : SpacePrefixSepBy Command) : Program =>
  commands;

#end

---------------------------------------------------------------------

end Strata

def test : Strata.Program :=
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

  // array assignment
  arr[0] := 5;
  arr[1] := 10;
  arr[2] := 15;

  // array access
  sum := arr[0] + arr[1] + arr[2];

  i := 0;
  for i : int := 0 to 9
    invariant 0 <= i && i <= 10
    invariant (forall k : int :: 0 <= k && k < i ==> arr[k] >= 0)
  {
    arr[i] := i * 2;  // array assignment
  }
};

#end
