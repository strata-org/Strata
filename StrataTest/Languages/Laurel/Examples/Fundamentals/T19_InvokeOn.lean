/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataTest.Util.TestDiagnostics
meta import all StrataTest.Languages.Laurel.TestExamples

meta section

open StrataTest.Util
open Strata

namespace Strata.Laurel

def program := r#"
procedure P(x: int): bool;
procedure Q(x: int): bool;

procedure assertP(x: int): int requires P(x);
procedure needsPAndQsInvoke1(): int {
  return assertP(3)
};

procedure PAndQ(x: int)
  invokeOn P(x)
  opaque
  ensures P(x) && Q(x);

procedure needsPAndQsInvoke2(): int {
  return assertP(3)
};

// The axiom fires because P(x) appears in the goal.
procedure fireAxiomUsingPattern(x: int)
  opaque
{
  assert P(x)
};

procedure axiomDoesNotFireBecauseOfPattern(x: int)
  opaque
{
  assert Q(x)
//^^^^^^^^^^^ error: assertion could not be proved
};

procedure A(x: int, y: real): bool;
procedure B(x: real): bool;
procedure AAndB(x: int, y: real)
  invokeOn A(x, y)
  opaque
  ensures A(x, y) && B(y);

procedure invokeA(x: int, y :real)
  opaque
{
  assert A(x, y)
};

procedure invokeB(x: int, y :real)
  opaque
{
  assert B(y)
//^^^^^^^^^^^ error: assertion could not be proved
};

procedure R(x: int): bool;
procedure badPostcondition(x: int)
  invokeOn R(x)
  opaque
  ensures R(x)
//        ^^^^ error: postcondition could not be proved
{
};

"#

#guard_msgs (drop info, error) in
#eval testInputWithOffset "InvokeOn" program 14
  (Strata.Laurel.processLaurelFileWithOptions { verifyOptions := { Core.VerifyOptions.default with solver := "z3" } })

end Strata.Laurel
