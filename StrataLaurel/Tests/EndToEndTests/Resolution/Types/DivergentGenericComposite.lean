/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation

open StrataTest.Util
open Strata

/-! # A generic composite whose instantiations do not terminate

`composite L<T> { var next: L<L<T>> }` asks the monomorphizer for `L<int>`, which needs
`L<L<int>>`, which needs `L<L<L<int>>>`. The fixpoint that finds nested instantiations (see
`Execution/Types/Composites/GenericComposite.lean`) has no fixed point here, so it is cut off
at a depth bound and the program is rejected LOUD.

What matters is the failure MODE, and there are three bad ones this rules out: hanging, which
a bound prevents; emitting the monomorphs produced before the cut, which would leave a
program referring to a type that was never completed; and reporting an internal error, which
tells the user nothing actionable. The diagnostic is `not-yet-implemented` and names the
composite and the bound. That THIS TEST TERMINATES is itself part of the assertion.

Unlike every other rejection in this folder, the diagnostic carries no source range — the cut
happens inside monomorphization, with no user token to blame — so it cannot be pinned with an
inline `// ^^^` annotation, whose matcher requires a location. The message is pinned with a
golden instead.
-/

private def divergentGeneric : StrataDDM.Program :=
#strata
program Laurel;
composite L<T> { var next: L<L<T>> }
procedure useL()
  opaque
  modifies *
{
  var x: L<int> := new L;
  assert 1 == 1
};
#end

/-- Report every non-warning diagnostic as `<category>: <message>`, so each golden pins the
    kind as well as the wording. The category alone is used rather than the whole
    `MessageKind`, whose `repr` also carries an `impact` field these tests are not about. -/
private def runDivergentProgram (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let dms ← Laurel.verifyToMessagesCapturing laurelProgram
  for dm in dms.filter (·.kind != .warning) do
    IO.println s!"{dm.kind.category}: {dm.message}"

/--
info: notYetImplemented: recursive generic composite 'L' is not supported: its instantiations grow without bound (depth exceeds 8)
-/
#guard_msgs in
#eval runDivergentProgram divergentGeneric

/-! ## A divergent generic PROCEDURE

`grow<T>(b: Box<T>)` calls itself with a `Box<Box<T>>`, so each clone needs a deeper one. The
same depth bound applies, and BOTH diagnostics fire: the procedure's instantiations diverge and
so do the composite's, since one drives the other. Both are reported rather than the first
winning, which is what a caller needs in order to see that the two are the same problem.

The important part is what is ABSENT. Once the depth cap has rejected, the monomorphs it
declined to emit are missing, so re-resolution finds dangling references — and that must not be
reported as an internal error on top of a rejection the compiler already made deliberately.
These goldens list every non-warning diagnostic, so a `strataBug` cascade folded on top would
show up here as extra lines. -/

private def divergentProcedureCalled : StrataDDM.Program :=
#strata
program Laurel;
composite Box<T> { var val: T }
procedure grow<T>(b: Box<T>) returns (r: T)
  opaque
  ensures true
{
  var bb: Box<Box<T>> := new Box<Box<T>>;
  var x: Box<T> := grow(bb);
  r := b#val
};
procedure callsGrow()
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  var got: int := grow(bx);
  assert 1 == 1
};
#end

/-- The same divergent procedure, never CALLED. It still has to be rejected: an uncalled
    polymorphic procedure over a generic composite is checked at a synthetic witness, so the
    depth cap has to hold on the witness path too — otherwise a divergent procedure could be
    smuggled past simply by not calling it. -/
private def divergentProcedureUncalled : StrataDDM.Program :=
#strata
program Laurel;
composite Box<T> { var val: T }
procedure grow<T>(b: Box<T>) returns (r: T)
  opaque
  ensures true
{
  var bb: Box<Box<T>> := new Box<Box<T>>;
  var x: Box<T> := grow(bb);
  r := b#val
};
procedure main() opaque { assert 1 == 1 };
#end

/--
info: notYetImplemented: recursive generic procedure 'grow' is not supported: its instantiations grow without bound (depth exceeds 8)
notYetImplemented: recursive generic composite 'Box' is not supported: its instantiations grow without bound (depth exceeds 8)
-/
#guard_msgs in
#eval runDivergentProgram divergentProcedureCalled

/--
info: notYetImplemented: recursive generic procedure 'grow' is not supported: its instantiations grow without bound (depth exceeds 8)
notYetImplemented: recursive generic composite 'Box' is not supported: its instantiations grow without bound (depth exceeds 8)
-/
#guard_msgs in
#eval runDivergentProgram divergentProcedureUncalled

/-- A call written at an instantiation past the bound is rejected by the bound alone, without an
    internal error for the clone the bound declined. -/
private def callPastTheBound : StrataDDM.Program :=
#strata
program Laurel;
composite Box<T> { var val: T }
procedure get<T>(b: Box<T>) returns (r: T) opaque { r := b#val };
procedure deep(b: Box<Box<Box<Box<Box<Box<Box<Box<Box<int>>>>>>>>>) opaque { var x := get(b) };
#end

/--
info: notYetImplemented: recursive generic composite 'Box' is not supported: its instantiations grow without bound (depth exceeds 8)
notYetImplemented: recursive generic procedure 'get' is not supported: its instantiations grow without bound (depth exceeds 8)
-/
#guard_msgs in
#eval runDivergentProgram callPastTheBound
