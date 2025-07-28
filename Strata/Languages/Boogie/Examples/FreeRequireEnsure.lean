/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def freeReqEnsEnv : Environment :=
#strata
program Boogie;
var g : int;
procedure Proc() returns ()
spec {
  modifies g;
  free requires [g_eq_15]: g == 15;
  // `g_lt_10` is not checked by this procedure.
  free ensures [g_lt_10]: g < 10;
}
{
  assert [g_gt_10_internal]: (g > 10);
  g := g + 1;
};

procedure ProcCaller () returns (x : int) {
  call := Proc();
  // Fails; `g_eq_15` requires of Proc ignored here.
  assert [g_eq_15_internal]: (g == 15);
};
#end

/--
info: [Strata.Boogie] Type checking succeeded.


Obligation g_lt_10 proved via evaluation!


Obligation <Origin:Proc_Requires>g_eq_15 is free!


VCs:
Label: g_gt_10_internal
Assumptions:
(g_eq_15, ($__g0 == #15))
Proof Obligation:
((~Int.Gt $__g0) #10)

Label: g_eq_15_internal
Assumptions:
(<Origin:Proc_Ensures>g_lt_10, ((~Int.Lt $__g2) #10))
Proof Obligation:
($__g2 == #15)

Wrote problem to vcs/g_gt_10_internal.smt2.
Wrote problem to vcs/g_eq_15_internal.smt2.


Obligation g_eq_15_internal: could not be proved!

Result: failed
CEx: ($__g2, 0)
---
info:
Obligation: g_gt_10_internal
Result: verified

Obligation: g_eq_15_internal
Result: failed
CEx: ($__g2, 0)
-/
#guard_msgs in
#eval verify "cvc5" freeReqEnsEnv

---------------------------------------------------------------------
