/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

/-
When the two branches of an `if/else` have different but subtype-related
types, the construct synthesizes their join (least upper bound) — not the
then-branch arbitrarily. So `if c then new Left else new Right`, with
`Left, Right <: Top`, synthesizes `Top`. Storing it in a `Top`-typed
variable succeeds, but storing it in a `Left`-typed variable is rejected.
-/

def program := r"
composite Top { }
composite Left extends Top { }
composite Right extends Top { }
procedure test(c: bool) opaque {
  var x: Top := if c then new Left else new Right;
  var y: Left := if c then new Left else new Right
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: expected 'Left', got 'Top'
};
"

#guard_msgs (drop info) in
#eval testInputWithOffset "IfBranchJoin" program 22 processLaurelFile
