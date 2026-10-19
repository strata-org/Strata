/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # A contract that quantifies over the procedure's OWN type variable

`ensures forall(y: T) => …` is different from every other use of `T` in a polymorphic
procedure's contract, and the difference is where the type comes from. Ordinarily `T` reaches
the encoder inside the obligation term, so grounding the call site grounds it. Here `T` is the
quantifier BINDER's type: it is synthesized during SMT encoding, is not part of the obligation
term, and so is invisible to the obligation-level scan that seeds free type variables.
Monomorphizing at the call sites therefore does NOT close it — the encoder has to declare that
type variable as a fresh arity-0 uninterpreted sort of its own accord.

"Uninterpreted" is doing real work, and the twins below are what check it. Declaring the sort as
a SINGLETON would be the easy mistake: `forall(y: T) => y == x` would then hold, since there
would be only one inhabitant for `y` to be. So that case must FAIL, while
`forall(y: T) => y == y` — valid in every interpretation, singleton or not — must verify. One
without the other proves nothing.
-/

/-! ## Valid in every interpretation

`y == y` holds whatever `T` turns out to be, so this case is purely about ENCODABILITY: the
binder's sort has to be declared at all.

TRANSITIONAL. This does not yet encode cleanly. `GenOpaqueTypeParams` substitutes a fresh
opaque type for the type variable in place, but the procedure's own body-VC is emitted at the
caller site under the ORIGINAL type variable, which then reaches the encoder ungrounded. The
resulting `strata-bug` is pinned below rather than hidden, so the gap is visible in the test
suite instead of living only in a comment.

The pin is self-clearing: when the body-VC emitter is tightened the diagnostic stops firing,
this annotation reports "expected but never fired", and the build fails until it is deleted —
which is exactly when the case should become an ordinary clean verification. Only the stable
part of the message is matched; the `$__tyNN` name in the full text is generated and would
otherwise churn. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure allEq<T>(x: T) returns (r: bool) opaque ensures forall(y: T) => (y == y) { r := true };
//                                                        ^^^^^^^^^^^^^^^^^^^^^^^^ strata-bug: SMT encoding: unexpected type variable

procedure callsAllEq() opaque {
  var b: bool := allEq(5);
  assert 1 == 1
};
#end

/-! ## Falsifiable once the sort has two inhabitants

`forall(y: T) => y == x` says every value of `T` equals the particular `x` passed in — true only
if `T` is a singleton. An uninterpreted sort is not forced to be one, so this must fail. This is
the case that makes the one above non-vacuous. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure allEqBad<T>(x: T) returns (r: bool)
  opaque
  ensures forall(y: T) => (y == x)
//        ^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition does not hold
{ r := true };

procedure callsAllEqBad() opaque {
  var b: bool := allEqBad(5);
  assert 1 == 1
};
#end

/-! ## One such helper, referenced at several instantiations

The generated postcondition helper is referenced three times — by the procedure's own body
self-check, and by the `int` and `bool` call sites. Each reference becomes a separate specialized
copy, each body-encoded with a monomorphic signature, so a sort declared for one instantiation
must not bleed into another.

The count is ONE failure, not three: the helper has a single body self-check obligation, and call
sites contribute assumptions rather than obligations. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure allEqM<T>(x: T) returns (r: bool)
  opaque
  ensures forall(y: T) => (y == x)
//        ^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition does not hold
{ r := true };

procedure callsAllEqMTwice() opaque {
  var bi: bool := allEqM(5);
  var bb: bool := allEqM(true);
  assert 1 == 1
};
#end
