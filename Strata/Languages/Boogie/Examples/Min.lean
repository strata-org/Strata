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

def testEnv : Environment :=
#strata
program Boogie;

procedure min(n : int, m : int) returns (k : int)
spec {
  ensures ((k <= n) && (k <= m));
}
{
  k := if (n < m) then n else m;
  k := k;
};
#end


/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: min_ensures_0
Assumptions:
Proof Obligation:
((~Bool.And ((~Int.Le (if ((~Int.Lt $__n0) $__m1) then $__n0 else $__m1)) $__n0)) ((~Int.Le (if ((~Int.Lt $__n0) $__m1) then $__n0 else $__m1)) $__m1))

Wrote problem to vcs/min_ensures_0.smt2.
---
info:
Obligation: min_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" testEnv

---------------------------------------------------------------------
