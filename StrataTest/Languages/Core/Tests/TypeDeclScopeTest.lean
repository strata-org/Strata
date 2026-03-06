/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-! ## Test that a statement-level type is not visible in another procedure -/

namespace Strata

/--
error: Undeclared type or category T.
-/
#guard_msgs in
def typeScopeError :=
#strata
program Core;
procedure P1 () returns () {
  type T;
  var x : T;
};
procedure P2 () returns () {
  var y : T;
};
#end

end Strata
