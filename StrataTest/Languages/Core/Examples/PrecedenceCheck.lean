/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def precPgm : Program :=
#strata
program Core;

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
info: [Strata.Core] Type checking succeeded.


VCs:
Label: implies_and_eq_not_or_1
Property: assert
Assumptions:


Proof Obligation:
((~Bool.And
  (~Bool.Implies init_a_0 init_b_1)
  (~Bool.Implies init_c_2 init_d_3)) == (~foo init_a_0 init_b_1 init_c_2 init_d_3))

Label: implies_and_eq_not_or_2
Property: assert
Assumptions:


Proof Obligation:
((~Bool.And
  (~Bool.Implies init_a_0 init_b_1)
  (~Bool.Implies init_c_2 init_d_3)) == (~foo init_a_0 init_b_1 init_c_2 init_d_3))

Label: implies_and_eq_not_or_3
Property: assert
Assumptions:


Proof Obligation:
((~Bool.And
  (~Bool.Implies init_a_0 init_b_1)
  (~Bool.Implies init_c_2 init_d_3)) == (~foo init_a_0 init_b_1 init_c_2 init_d_3))

Label: implies_and_eq_not_or_4
Property: assert
Assumptions:


Proof Obligation:
((~Bool.And
  (~Bool.Implies init_a_0 init_b_1)
  (~Bool.Implies init_c_2 init_d_3)) == (~foo init_a_0 init_b_1 init_c_2 init_d_3))

Label: implies_equiv
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Equiv (~Bool.Implies init_a_0 init_b_1) (~Bool.Or (~Bool.Not init_a_0) init_b_1))

---
info:
Obligation: implies_and_eq_not_or_1
Property: assert
Result: ✅ pass

Obligation: implies_and_eq_not_or_2
Property: assert
Result: ✅ pass

Obligation: implies_and_eq_not_or_3
Property: assert
Result: ✅ pass

Obligation: implies_and_eq_not_or_4
Property: assert
Result: ✅ pass

Obligation: implies_equiv
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify precPgm

end Strata

---------------------------------------------------------------------
