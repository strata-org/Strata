/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

-- `invokeOn` under `--vcgen wp`: a procedure is not checked against its own invokeOn
-- axiom, so `badPostcondition` stays unproved, as in the default mode (InvokeOn.lean).
-- The diagnostics are those of the default mode except for the wording of
-- `badPostcondition`'s failure: this mode reports "postcondition does not hold", the
-- default mode "postcondition could not be proved".
#eval testLaurelVerification
    (options := { verifyOptions :=
      { Core.VerifyOptions.quiet with solver := "z3", vcgen := .wp } }) <|
#strata
program Laurel;
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
//        ^^^^ error: postcondition does not hold
{
};
#end
