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

function assertP(x: int): int requires P(x);
function needsPAndQsInvoke1(): int {
  assertP(3)
};

procedure PAndQ(x: int)
  invokeOn P(x)
  opaque
  ensures P(x) && Q(x);

function needsPAndQsInvoke2(): int {
  assertP(3)
};

// The axiom fires because P(x) appears in the goal.
procedure fireAxiomUsingPattern(x: int) {
  assert P(x)
};

procedure axiomDoesNotFireBecauseOfPattern(x: int) {
  assert Q(x)
//^^^^^^^^^^^ error: assertion could not be proved
};

function A(x: int, y: real): bool;
function B(x: real): bool;
procedure AAndB(x: int, y: real)
  invokeOn A(x, y)
  opaque
  ensures A(x, y) && B(y);

procedure invokeA(x: int, y :real) {
  assert A(x, y)
};

procedure invokeB(x: int, y :real) {
  assert B(y)
//^^^^^^^^^^^ error: assertion could not be proved
};

function R(x: int): bool;
procedure badPostcondition(x: int)
  invokeOn R(x)
  opaque
  ensures R(x)
//        ^^^^ error: assertion
{
};

"#

#guard_msgs (drop info, error) in
#eval testInputWithOffset "InvokeOn" program 14
  (Strata.Laurel.processLaurelFileWithOptions { verifyOptions := { Core.VerifyOptions.default with solver := "z3" } })

end Strata.Laurel
