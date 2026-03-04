import Strata.MetaVerifier

open Strata

def matrix_transpose_example : Strata.Program :=
#strata
program Boole;

type Matrix := Map int (Map int int);

procedure matrix_transpose (A: Matrix, m: int, n: int) returns (B: Matrix)
{
  var i: int;
  var j: int;

  i := 0;
  while (i < m)
  {
    j := 0;
    while (j < n)
    {
      // Array assignment is parsed as regular assignment over recursive LHS
      // indexing (`arr[i][j]... := v`).
      // Lowering recursively nests map `select`/`update`, so any index depth works.
      B[i][j] := A[j][i];
      // Previously would have been:
      // B := B[i := (B[i])[j := (A[j])[i]]];
      j := j + 1;
    }
    i := i + 1;
  }
};
#end

#eval Strata.Boole.verify "cvc5" matrix_transpose_example

theorem matrix_transpose_smt_vcs_correct : Strata.smtVCsCorrect matrix_transpose_example := by
  gen_smt_vcs
  all_goals (try grind)
