/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-! ## Tests for statement-level type scoping -/

namespace Strata

-- A top-level type cannot be shadowed by a statement-level one
def shadowTopLevelType : Program :=
#strata
program Core;
type T;
procedure P () returns () {
  type T;
  var x : T;
};
#end

/--
error:  ❌ Type checking error.
Type 'T' is already declared
-/
#guard_msgs in
#eval verify shadowTopLevelType

-- A statement-level type is not visible in another procedure
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
