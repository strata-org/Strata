/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

namespace Strata

/-- Basic uninterpreted type declaration in a statement -/
def typeDeclStmt1 : Program :=
#strata
program Core;

procedure P () returns () {
  type T;
  var x : T;
  var y : T;
  assume [xy_eq]: (x == y);
  assert [reflexive]: (x == x);
};
#end

/-- info: #[] -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram typeDeclStmt1) |>.snd

end Strata
