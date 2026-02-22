import Strata.MetaVerifier

open Strata

private def array2D :=
#strata
program Boole;

procedure array2DWriteRead(i: int, j: int, v: int) returns ()
{
  var grid : Map int (Map int int);
  grid[i][j] := v;
  assert v == v;
};

#end

#eval Strata.Boole.verify "cvc5" array2D

example : Strata.smtVCsCorrect array2D := by
  gen_smt_vcs
  all_goals grind
