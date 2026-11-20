/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

meta import Strata.Languages.Core.Options
meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

/-! A polymorphic function whose type parameters first occur in the signature
out of declaration order verifies the same as its in-order twin, both with a
body (`h`) and without one (`k`).

This is a sanity check that the order of type parameters does not change a
verdict, not a regression test for it: it also passes with the older type
checker that renamed type parameters in first-occurrence order, because that
renaming was consistent across the whole signature. The order itself is pinned
in `FunctionTypeTests`. `k_decl` fails in both programs because `k` has no
body. -/

meta section
namespace Strata

def outOfOrderTypeArgsPgm :=
#strata
program Core;
function h<a, b>(x : b, y : a) : a {
  y
}
function k<a, b>(x : b, y : a) : a;
procedure P()
{
  assert [h_body]: (h(1, true) == true);
  assert [k_decl]: (k(1, true) == true);
};
#end

def inOrderTypeArgsPgm :=
#strata
program Core;
function h<a, b>(x : a, y : b) : b {
  y
}
function k<a, b>(x : a, y : b) : b;
procedure P()
{
  assert [h_body]: (h(1, true) == true);
  assert [k_decl]: (k(1, true) == true);
};
#end

/--
info:
Obligation: h_body
Property: assert
Result: ✅ pass

Obligation: k_decl
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify outOfOrderTypeArgsPgm (options := .quiet)

/--
info:
Obligation: h_body
Property: assert
Result: ✅ pass

Obligation: k_decl
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify inOrderTypeArgsPgm (options := .quiet)

end Strata
end
