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

/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval verify "cvc5" precPgm

end Strata

---------------------------------------------------------------------
