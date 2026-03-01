import Strata.MetaVerifier

open Strata

private def findMaxPgm: Strata.Program :=
#strata
program Boole;

type Array := Map int int;

procedure FindMax(A : Array, n : int) returns (max : int)
spec
{
  requires n >= 1;
  ensures (forall i:int :: 0 <= i && i < n ==> A[i] <= max);
}
{
  max := A[0];
  for i : int := 1 to (n - 1) by 1
    invariant 1 <= i && i <= n
    invariant forall j:int :: 0 <= j && j < i ==> A[j] <= max
  {
    if (A[i] > max) {
      max := A[i];
    }
  }
};
#end

#eval Strata.Boole.verify "cvc5" findMaxPgm

theorem findMaxPgm_smtVCsCorrect : Strata.smtVCsCorrect findMaxPgm := by
  gen_smt_vcs
  all_goals (try grind)
