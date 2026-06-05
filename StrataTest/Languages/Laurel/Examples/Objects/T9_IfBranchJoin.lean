/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataTest.Util.TestDiagnostics
meta import all StrataTest.Languages.Laurel.TestExamples

meta section

open StrataTest.Util

namespace Strata
namespace Laurel

/-
When an `if/else` is checked against an expected type, the rule pushes
that type into both branches rather than going through synth + subsumption
at the boundary. So `var y: Left := if c then new Left else new Right`,
with `Left, Right <: Top`, errors at the *else-branch*: `new Right` is
checked against `Left`, and since `Right` is not a subtype of `Left`, a
"expected 'Left', got 'Right'" diagnostic fires there. The then-branch
(`new Left`) and the `var x: Top := …` assignment both pass.
-/

def program := r"
composite Top { }
composite Left extends Top { }
composite Right extends Top { }
procedure test(c: bool) opaque {
  var x: Top := if c then new Left else new Right;
  var y: Left := if c then new Left else new Right
//                                       ^^^^^^^^^ error: expected 'Left', got 'Right'
};
"

#guard_msgs (drop info) in
#eval testInputWithOffset "IfBranchJoin" program 22 processLaurelFile
