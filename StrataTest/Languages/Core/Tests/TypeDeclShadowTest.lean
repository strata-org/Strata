/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-! ## Test that a top-level type cannot be shadowed by a statement-level one -/

namespace Strata

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

end Strata
