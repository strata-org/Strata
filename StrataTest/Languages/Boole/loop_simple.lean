import Strata.MetaVerifier

open Strata

def loop_simple_program : Strata.Program :=
#strata
program Boole;

procedure loop_simple (n: int) returns (r: int)
spec {
  requires [non_negative]: (n >= 0);
  ensures [sum_assert]: ((n * (n-1)) div 2 == r);
}
{
  var sum : int := 0;
  for i : int := 0 to (n - 1) by 1
    invariant i <= n
    invariant (i * (i-1)) div 2 == sum
  {
    sum := sum + i;
  }
  r := sum;
};
#end

#eval Strata.Boole.verify "cvc5" loop_simple_program

open Strata.SMT

theorem loop_simple_smt_vcs_correct : smtVCsCorrect loop_simple_program := by
  gen_smt_vcs
  all_goals (try grind)
