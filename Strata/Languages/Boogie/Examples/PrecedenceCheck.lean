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

def precEnv : Environment :=
#strata
program Boogie;

function foo(a : bool, b : bool, c : bool, d : bool) : bool {
  (((!a) || b) && ((!c) || d))
}

procedure TestFoo () returns () {
  var a : bool, b : bool, c : bool, d : bool, imp_expr : bool, foo_expr : bool;

  assert [implies_and_eq_not_or_1]: (((a ==> b) && (c ==> d)) == foo(a, b, c, d));

  imp_expr := ((a ==> b) && (c ==> d));
  foo_expr := foo(a, b, c, d);

  assert [implies_and_eq_not_or_2]: (imp_expr == foo_expr);
  assert [implies_and_eq_not_or_3]: (imp_expr == foo(a, b, c, d));
  assert [implies_and_eq_not_or_4]: (((a ==> b) && (c ==> d)) == foo_expr);
  assert [implies_equiv]: (a ==> b) <==> ((!a) || b);
};

#end

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: implies_and_eq_not_or_1
Assumptions:
Proof Obligation:
(((~Bool.And ((~Bool.Implies init_a_0) init_b_1)) ((~Bool.Implies init_c_2) init_d_3)) == ((((~foo init_a_0) init_b_1) init_c_2) init_d_3))

Label: implies_and_eq_not_or_2
Assumptions:
Proof Obligation:
(((~Bool.And ((~Bool.Implies init_a_0) init_b_1)) ((~Bool.Implies init_c_2) init_d_3)) == ((((~foo init_a_0) init_b_1) init_c_2) init_d_3))

Label: implies_and_eq_not_or_3
Assumptions:
Proof Obligation:
(((~Bool.And ((~Bool.Implies init_a_0) init_b_1)) ((~Bool.Implies init_c_2) init_d_3)) == ((((~foo init_a_0) init_b_1) init_c_2) init_d_3))

Label: implies_and_eq_not_or_4
Assumptions:
Proof Obligation:
(((~Bool.And ((~Bool.Implies init_a_0) init_b_1)) ((~Bool.Implies init_c_2) init_d_3)) == ((((~foo init_a_0) init_b_1) init_c_2) init_d_3))

Label: implies_equiv
Assumptions:
Proof Obligation:
((~Bool.Equiv ((~Bool.Implies init_a_0) init_b_1)) ((~Bool.Or (~Bool.Not init_a_0)) init_b_1))

Wrote problem to vcs/implies_and_eq_not_or_1.smt2.
Wrote problem to vcs/implies_and_eq_not_or_2.smt2.
Wrote problem to vcs/implies_and_eq_not_or_3.smt2.
Wrote problem to vcs/implies_and_eq_not_or_4.smt2.
Wrote problem to vcs/implies_equiv.smt2.
---
info:
Obligation: implies_and_eq_not_or_1
Result: verified

Obligation: implies_and_eq_not_or_2
Result: verified

Obligation: implies_and_eq_not_or_3
Result: verified

Obligation: implies_and_eq_not_or_4
Result: verified

Obligation: implies_equiv
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" precEnv

end Strata

---------------------------------------------------------------------
