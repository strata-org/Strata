/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelVerification
    (options := { verifyOptions := { Core.VerifyOptions.quiet with solver := "z3" } }) <|
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
//        ^^^^ error: postcondition could not be proved
{
};
#end

/-! ## A trigger over a composite-valued file-scope global's heap field

`invokeOn P(c#value)` names hidden state: `c` is a file-scope global and `c#value`
lives in the heap, so by the time `contractPass` builds the axiom both have become
inputs of `cellTrigger` (`heapParameterizationPass` and `globalParameterizationPass`
run before it). The axiom is therefore quantified over them with `P(c#value)` as its
pattern, and `usesCellTrigger` receives the `ensures` without ever calling
`cellTrigger`.

`unimpliedArgument` is the control that rules out the two assertions above holding
vacuously: the axiom says nothing about `c#value + 1`, so the same shape one argument
away stays unprovable.

`bumpCell`/`observesBump` carry the other piece of hidden-state metadata on the same
global: `modifies c` is what makes the field write legal and what lets the caller
observe it. Deleting the `invokeOn` line, or either `modifies c`, makes this program
fail — the point of writing it as a source program rather than as a count of
translation diagnostics. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite MetadataCell {
  var value: int
}
var c: MetadataCell := <??>
procedure P(x: int): bool;
procedure Q(x: int): bool;
procedure cellTrigger()
  invokeOn P(c#value)
  opaque
  ensures P(c#value) && Q(c#value)
  reads c;
procedure usesCellTrigger()
  opaque
{
  assert P(c#value);
  assert Q(c#value)
};
procedure unimpliedArgument()
  opaque
{
  assert P(c#value + 1)
//^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
procedure bumpCell()
  opaque
  ensures c#value == 7
  modifies c
{
  c#value := 7
};
procedure observesBump()
  opaque
  modifies c
{
  bumpCell();
  assert c#value == 7
};
#end

/-! ## A trigger that is itself a quantifier

`invokeOn forall(x: nat) => P(x) & g == g` is the one `invokeOn` shape nothing else here
reaches: the clause is a quantified term rather than a bare predicate application. The global
`g` is what makes it bite. `trigger` has an implementation, so its effects are inferred (it
cannot carry an explicit `reads g`), `globalParameterizationPass` turns the read into an input
parameter, and `contractPass` then quantifies the axiom over that parameter with the clause as
the innermost quantifier's PATTERN (`mkInvokeOnAxiom`). The pattern slot therefore receives a
`forall`.

The `ensures` is what makes this a verification case at all. `contractPass`
discards an `invokeOn` whose procedure has no postcondition — `if postconds.isEmpty then
{ proc with invokeOn := none }` — so without `ensures g >= 0` no axiom is built, nothing is
encoded, and the program verifies silently. A version of this case that only counted translation
diagnostics passed for exactly that reason while asserting nothing; deleting either the
`invokeOn` line or the `ensures` line below now makes the test fail.

TRANSITIONAL. The SMT text encoder has no serialization for a `forall` in a pattern position, so
this does not yet encode. The resulting `strata-bug` is pinned rather than hidden, so the gap is
visible in the test suite instead of living only in a comment. The pin is self-clearing: when the
encoder learns this shape the diagnostic stops firing, the annotation reports "expected but never
fired", and the build fails until the case is updated — which is exactly when it should become an
ordinary clean verification.

Only the stable headline is matched. The real message continues for another ~130 lines with a
`repr` dump of the offending `Strata.SMTDDM.Term`, which no test should pin.

The reported RANGE is WRONG, and recording that is part of the point. The diagnostic is blamed on
the `0` witness of the `constrained nat` declaration, which has nothing to do with the trigger,
so the annotation sits under the witness literal — where the diagnostic actually lands — rather
than under the `invokeOn` line it is really about. -/

#eval testLaurelVerification <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
//                                            ^ strata-bug: analysis error: SMT Encoding Error! SMT text encoding failed: term serialization: Doesn't know how to convert Strata.SMTDDM.Term.forall_smt
var g: nat := 0
procedure P(x: int): bool;
procedure trigger()
  invokeOn forall(x: nat) => P(x) & g == g
  opaque
  ensures g >= 0
{ };
#end
