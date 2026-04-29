/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

def matrix_transpose_example : Strata.Program :=
#strata
program Boole;

type Matrix := Map int (Map int int);

procedure matrix_transpose (A: Matrix, m: int, n: int) returns (B: Matrix)
{
  var j: int;

  for i: int := 0 to (m - 1)
  {
    j := 0;
    while (j < n)
    {
      // Array assignment is parsed as regular assignment over recursive LHS
      // indexing (`arr[i][j]... := v`).
      // Lowering recursively nests map `select`/`update`, so any index depth works.
      B[i][j] := A[j][i];
      j := j + 1;
    }
  }
};
#end

/-- info: -/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" matrix_transpose_example (options := .quiet)

theorem matrix_transpose_smt_vcs_correct : Strata.smtVCsCorrect matrix_transpose_example := by
  gen_smt_vcs
  all_goals (try grind)
