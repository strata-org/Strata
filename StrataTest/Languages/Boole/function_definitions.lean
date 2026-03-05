import Strata.MetaVerifier

open Strata

private def function_definitions :=
#strata
program Boole;

function foo2(x:int) : int
  { x + 1 }
function foo(x:int) : bool
  { foo2(x) > 0 }

procedure test(x:int) returns (r:int)
spec {
  ensures (r > 0);
}
{
  if (foo(x)) {
    r := foo2(x);
  } else {
    r := 1;
  }
};

#end

#eval Strata.Boole.verify "cvc5" function_definitions

example : Strata.smtVCsCorrect function_definitions := by
  gen_smt_vcs
  all_goals (try grind)
