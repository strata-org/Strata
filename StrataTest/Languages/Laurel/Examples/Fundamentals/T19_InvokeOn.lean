/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

def program := r#"
function P(x: int): bool;
function Q(x: int): bool;

procedure PAndQ(x: int)
  invokeOn P(x)
  ensures P(x) && Q(x);

// The axiom fires because P(x) appears in the goal.
procedure fireAxiomUsingPattern(x: int) {
  assert P(x)
};

procedure axiomDoesNotFireBecauseOfPattern(x: int) {
  assert Q(x)
//^^^^^^^^^^^ error: assertion does not hold
};

function Z(x: real): bool;
procedure PAndZ(x: int, y: real)
  invokeOn P(x)
  ensures P(x) && Z(y);

procedure invokePAndZ(x: int, y :real) {
  assert P(x) && Z(y)
};

"#

#guard_msgs (drop info, error) in
#eval testInputWithOffset "InvokeOn" program 14 processLaurelFile

end Strata.Laurel
