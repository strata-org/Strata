import Strata.MetaVerifier

open Strata

private def array_2d :=
#strata
program Boole;

procedure array_2d_write_read(i: int, j: int, v: int) returns ()
{
  var grid : Map int (Map int int);
  grid[i][j] := v;
  assert v == v;
};

#end

#eval Strata.Boole.verify "cvc5" array_2d

example : Strata.smtVCsCorrect array_2d := by
  gen_smt_vcs
  all_goals grind
