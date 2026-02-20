import Strata.MetaVerifier

open Strata

def loopSimple : Strata.Program :=
#strata
program Boole;

procedure loopSimple (n: int) returns (r: int)
spec {
  requires [non_negative]: (n >= 0);
  ensures [sum_assert]: ((n * (n-1)) div 2 == r);
}
{
  var sum : int := 0;
  for (i : int := 0; i < n; i + 1)
    invariant (i <= n && ((i * (i-1)) div 2 == sum))
  {
    sum := sum + i;
  }
  r := sum;
};
#end

#eval Strata.Boole.verify "cvc5" loopSimple

open Strata.SMT

theorem loopSimple_smtVCsCorrect : smtVCsCorrect loopSimple := by
  gen_smt_vcs
  all_goals (try grind)
