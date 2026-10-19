/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Polymorphic procedures through the full pipeline

Most cases here run through the *entire* pipeline with `testLaurelExecution {}` —
translate + all lowering passes + verify + **interpret** — checking both modes against
the same inline annotations.

That second mode is the point. Polymorphic procedures ride per-call-site type-variable
freshening in `CallElim`, which rewrites each call's contract before Core sees it; nothing
else here checks that the concrete interpreter agrees with the verifier about what a
polymorphic call actually computes. A freshening bug that produced a *consistent but wrong*
instantiation could satisfy the verifier's own obligations and still execute the wrong
value.

Bodies are TRANSPARENT unless a case needs a contract: an `opaque ensures` on a
polymorphic procedure emits that procedure's own body VC. With `MonomorphizeFunctions`
inserted after `typeCheckPhase` (see
`Strata/Transform/MonomorphizeFunctions.lean`), each such body is specialized at the
ground instantiations reached from its call sites before SMT encoding, so both value
assertions and the dual-mode interpreter/verifier check succeed for every case in this
file.

A `T` instantiated at a *reference* type works in both modes too, as long as the entry
declares `modifies *` (an entry's heap is a body local, so no narrower frame can be stated
about it). Generic composites — `T` as a composite's own field type, which needs
monomorphization rather than freshening — live in `Types/Composites/GenericComposite.lean`.
-/

-- Multi-instantiation in one caller: the same `idp` at `int` and at `bool`. Per-call-site
-- freshening means the two sites do not share one `T`; without it the shared variable
-- would have to unify with both `int` and `bool`. Both modes must agree on the values.
#eval testLaurelExecution {} <|
#strata
program Laurel;

procedure idp<T>(x: T): T { return x };

procedure multiInstantiation()
  entry
  opaque
{
  var a: int := idp(5);
  assert a == 5;
  var b: bool := idp(true);
  assert b == true;
  var s: string := idp("hi");
  assert s == "hi"
};
#end

-- SOUNDNESS twin: a FALSE assertion on a polymorphic result must fail in both modes.
-- Guards against the instantiated result becoming unconstrained (which would let the
-- verifier pass it vacuously) and against the interpreter computing something else.
#eval testLaurelExecution {} <|
#strata
program Laurel;

procedure idp<T>(x: T): T { return x };

procedure falseOnPolyResult()
  entry
  opaque
{
  var a: int := idp(5);
  assert a == 6
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- The type variable used in a COMPUTED position, not just passed through: `dup` returns
-- its argument combined with itself, so a wrong instantiation changes the value rather
-- than merely the type. Pins that freshening keeps the input and output slots coupled.
#eval testLaurelExecution {} <|
#strata
program Laurel;

procedure pick<T>(useFirst: bool, a: T, b: T): T {
  return if useFirst then a else b
};

procedure computedPolySlot()
  entry
  opaque
{
  var i: int := pick(true, 7, 9);
  assert i == 7;
  var j: int := pick(false, 7, 9);
  assert j == 9;
  var t: bool := pick(true, false, true);
  assert t == false
};
#end

-- A polymorphic procedure calling ANOTHER polymorphic procedure at its own type variable.
-- The inner call's freshened variable must resolve to the outer instantiation, not to a
-- second independent one.  After `MonomorphizeFunctions` pre-encoding, `wrap<int>` and
-- `wrap<bool>` are specialized before SMT so the poly-to-poly call encodes cleanly and
-- both value assertions verify in both modes.
#eval testLaurelExecution {} <|
#strata
program Laurel;

procedure idp<T>(x: T): T { return x };
procedure wrap<T>(x: T): T { return idp(x) };

procedure nestedPoly()
  entry
  opaque
{
  var a: int := wrap(3);
  assert a == 3;
  var b: bool := wrap(false);
  assert b == false
};
#end

/-! ## Two type parameters, with the returned one differing from the discarded one

`firstOf` returns its FIRST argument, and is called at both orderings so the returned and
discarded parameters have different types each time. A substitution that crossed or dropped a
slot returns the wrong value here rather than failing to typecheck. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure firstOf<A, B>(a: A, b: B): A { return a };

procedure twoTypeParams()
  entry
  opaque
{
  var a: int := firstOf(1, true);
  assert a == 1;
  var b: bool := firstOf(false, 9);
  assert b == false
};
#end

/-! ## The two-parameter result is really observed

A wrong expected value must FAIL, so the asserts above are pinning an evaluated result rather
than passing on a body the pipeline silently dropped. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure firstOf<A, B>(a: A, b: B): A { return a };

procedure twoTypeParamsWrong()
  entry
  opaque
{
  var a: int := firstOf(1, true);
  assert a == 2
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- DISCARDED calls to a contracted polymorphic callee, at two instantiations. A discarded call's
-- only observable effect is its precondition check, so the second one passes 6 where
-- `requires n == 5`.
#eval testLaurelExecution {} <|
#strata
program Laurel;

procedure dup<T>(n: int, x: T) returns (a: T, b: T)
  requires n == 5
  opaque ensures a == x ensures b == x
{ a := x; b := x };

procedure discardContractedPolyOutputs()
  entry
  opaque
{
  dup(5, 1);
  dup(6, true)
//^^^^^^^^^^^^ error: precondition does not hold
};
#end

-- A contracted polymorphic call nested in another inside a GENERIC caller: `wrap<U>` forwards its
-- own `U` through `sink(idp(x))`, and verifies at both instantiations. The last assertion is false,
-- so the others are not vacuous.
#eval testLaurelExecution {} <|
#strata
program Laurel;

procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };
procedure sink<T>(x: T) returns (r: T) opaque ensures r == x { r := x };
procedure wrap<U>(x: U) returns (w: U) opaque ensures w == x { w := sink(idp(x)) };

procedure nestedPolyInGenericCaller()
  entry
  opaque
{
  var a: int := wrap(5);
  assert a == 5;
  var b: bool := wrap(true);
  assert b;
  assert a == 6
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Polymorphic calls inside a GENERIC caller whose result types mix the caller's `U` with a concrete
-- type, `Pair<U, int>` and then `Pair<U, bool>`: as a contracted call's argument, as a contracted
-- call's result, and as a global-writing call's result. The last assertion is false, so the others are
-- not vacuous.
#eval testLaurelExecution {} <|
#strata
program Laurel;
var g: int := 0
datatype Pair<A, B> { MkPair(fst: A, snd: B) }

procedure mkp<A, B>(a: A, b: B) returns (r: Pair<A, B>) opaque { r := MkPair(a, b) };
procedure mkc<A, B>(a: A, b: B) returns (r: Pair<A, B>) opaque ensures r == MkPair(a, b)
{ r := MkPair(a, b) };
procedure mkg<A, B>(a: A, b: B) returns (r: Pair<A, B>) opaque ensures r == MkPair(a, b)
{ g := g + 1; r := MkPair(a, b) };
procedure f<T>(x: T) returns (r: T) opaque ensures r == x { r := x };
procedure keep<T>(x: T): T { return x };
procedure w<U>(x: U) returns (r: U) opaque ensures r == x {
  var i: Pair<U, int> := f(mkp(x, 5));
  var j: Pair<U, bool> := f(mkp(x, true));
  var k: Pair<U, int> := keep(mkc(x, 5));
  var l: Pair<U, bool> := keep(mkc(x, true));
  var m: Pair<U, int> := keep(mkg(x, 5));
  var n: Pair<U, bool> := keep(mkg(x, true));
  r := x
};

procedure mixedBindingsInGenericCaller()
  entry
  opaque
{
  var a: int := w(1);
  assert a == 1;
  assert a == 2
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Two instantiations of one polymorphic callee in `ensures` clauses, which are lowered into helper
-- procedures rather than into the body. Each clause holds by `o == k`, since a clause does not
-- assume its callee's postcondition. Verifier-only: an `entry` cannot have an `ensures` clause.
#eval testLaurelVerification <|
#strata
program Laurel;

procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };

procedure twoInstantiationsInEnsures(k: int) returns (o: int)
  opaque
  ensures o == k || idp(1) > 0
  ensures o == k || idp(true)
{ o := k };
#end

-- Generic calls nested in one another at two instantiations, `idp(idp(5))` and `idp(idp(true))`, and
-- `idp(mk())`, where only the context fixes `mk`'s type argument. The lowering introduces a local for
-- each inner call.
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure idp<T>(x: T) returns (r: T) opaque { r := x };
procedure mk<T>() returns (r: T) opaque { };

procedure nestedCallsAtTwoTypes()
  entry
  opaque
{
  var a: int := idp(idp(5));
  var b: bool := idp(idp(true));
  var c: int := idp(mk());
  var d: bool := idp(mk())
};
#end

-- Contracted calls at two instantiations whose argument's type comes from a datatype value: from a
-- constructor's own argument (`unwrap(Some(5))`) and from a destructor's receiver
-- (`Option..value!(o)`), also as the argument of a call inside another or with a contracted call as
-- the receiver. The last assertion is false, so the others are not vacuous.
#eval testLaurelExecution {} <|
#strata
program Laurel;
datatype Option<T> { Nothing(), Some(value: T) }

procedure unwrap<T>(o: Option<T>) returns (r: T) opaque { };
procedure f<T>(x: T) returns (r: T) opaque ensures r == x { r := x };
procedure keep<T>(x: T): T { return x };

procedure datatypeArgumentsAtTwoTypes()
  entry
  opaque
{
  var a: int := f(unwrap(Some(5)));
  var b: bool := f(unwrap(Some(true)));
  var o: Option<int> := Some(5);
  var p: Option<bool> := Some(true);
  var c: int := f(Option..value!(o));
  var d: bool := f(Option..value!(p));
  var k: int := keep(f(Option..value!(o)));
  var l: bool := keep(f(Option..value!(p)));
  var m: int := f(Option..value!(f(o)));
  var n: bool := f(Option..value!(f(p)));
  assert c == 5;
  assert d;
  assert k == 5;
  assert l;
  assert m == 5;
  assert n;
  assert c == 6
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Arguments of a contracted call whose own arguments do not determine their result's type
-- variable: `mk()` has none, and `Nothing()` fixes no type argument of its own, as the argument or
-- as a branch of it. Only the call's context determines it, which re-resolution of the argument's
-- local lacks, so this fails if such a local is left undeclared.
#eval testLaurelExecution {} <|
#strata
program Laurel;
datatype Option<T> { Nothing(), Some(value: T) }

procedure mk<T>() returns (r: T) opaque { };
procedure unwrap<T>(o: Option<T>) returns (r: T) opaque { };
procedure f<T>(x: T) returns (r: T) opaque ensures r == x { r := x };

procedure undeterminedTypeVarArgument()
  entry
  opaque
{
  var b: bool := true;
  var y: int := f(mk());
  var z: int := f(unwrap(Nothing()));
  var w: int := f(unwrap(if b then Nothing() else Nothing()))
};
#end

-- A generic caller whose type parameter is spelled like its callee's: inside `g<T>`, the argument
-- `seqBuild(ss, s)` of the contracted `seqSelect` has type `Sequence<Sequence<T>>` with `g`'s `T`,
-- at the instantiation `Sequence<T>` of `seqBuild`'s `T`. Its local must be declared at exactly that
-- type, so this fails if `seqBuild`'s `T` is replaced by name, which replaces `g`'s too.
-- Verifier-only: the Core interpreter does not evaluate sequence operations.
#eval testLaurelVerification <|
#strata
program Laurel;
procedure g<T>(ss: Sequence<Sequence<T>>, s: Sequence<T>) returns (x: Sequence<T>) opaque {
  x := seqSelect(seqBuild(ss, s), 0)
};

procedure callerTypeVarSpelledLikeCallee() opaque {
  var a: Sequence<int> := g(seqEmpty(), seqEmpty())
};
#end

/-! ## `T` instantiated at a REFERENCE type

A polymorphic procedure applied to a composite argument needs no separate erasure pass:
every composite lowers to the single `tcons "Composite"` type, and Core's HM unifies
`ftvar T` with it exactly as it does with `int`. So the pass-through path is
*kind-agnostic*, and this pins that — a reference `T` reaching machinery that assumed a
value type would show up as a translation failure rather than a wrong answer.

Both blocks mark an `entry` (and so declare `modifies *`, which an entry that touches the
heap must), so the composite really is allocated, passed through `idc` and read back by two
interpreters as well as proved. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Cir { var r: int }

procedure idc<T>(x: T): T { return x };

procedure referenceTypeArg()
  entry
  opaque
  modifies *
{
  var c: Cir := new Cir;
  c#r := 7;
  var d: Cir := idc(c);
  assert d#r == 7
};
#end

-- SOUNDNESS twin: the returned reference really is `c`, so a FALSE claim about the field
-- read through it must fail. Without this, `referenceTypeArg` would also pass if `idc`
-- returned an unconstrained reference.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Cir { var r: int }

procedure idc<T>(x: T): T { return x };

procedure referenceTypeArgFalse()
  entry
  opaque
  modifies *
{
  var c: Cir := new Cir;
  c#r := 7;
  var d: Cir := idc(c);
  assert d#r == 8
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end


/-! ## Freshening COUPLES the input and output slots

`ensures r == x` ties the output's type to the input's at every call site. The same fresh
substitution has to reach the input types, the output types AND the contract expressions — if
one slot freshened to a different instantiation, the coupled obligation would be either
ill-formed or, worse, vacuous. Vacuous is the dangerous direction: it is invisible to the type
checker, so a twin per slot is the guardrail. Both instantiations appear in one body, and the
two twins each falsify one slot. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };

procedure crossSlotCoupling()
  entry
  opaque
{
  var gi: int := idp(7);
  var gb: bool := idp(true);
  assert gi == 7 && gb == true
};
#end

-- Twin falsifying the INT slot.
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };

procedure crossSlotWrongInt()
  entry
  opaque
{
  var gi: int := idp(7);
  var gb: bool := idp(true);
  assert gi == 8 && gb == true
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Twin falsifying the BOOL slot — the other half of the coupling.
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };

procedure crossSlotWrongBool()
  entry
  opaque
{
  var gi: int := idp(7);
  var gb: bool := idp(true);
  assert gi == 7 && gb == false
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A poison instantiation must not abort whole-program checking

If a multi-instantiation call that the pipeline struggles with aborted the run, every OTHER
procedure's obligations would silently go unchecked — a green build hiding real bugs. So
`realBug`'s plain `assert 1 == 2` sits beside a two-instantiation body, and it is the failure
being pinned: it proves checking reached the rest of the program. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure idp<T>(x: T) returns (y: T) opaque ensures y == x { y := x };

procedure realBug()
  entry
  opaque
{
  assert 1 == 2
//^^^^^^^^^^^^^ error: assertion does not hold
};

procedure poison()
  opaque
{
  var a: int := idp(5);
  assert a == 5;
  var b: bool := idp(true);
  assert b == true
};
#end

-- A false claim about the THIRD instantiation in one body. Per-site freshening must not drift
-- across many sites, and no site's assumed postcondition may become vacuous — either failure
-- mode would let this false assert pass.
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure idp<T>(x: T) returns (y: T) opaque ensures y == x { y := x };

procedure falseAmongManyInstantiations()
  entry
  opaque
{
  var a: int := idp(5);
  var b: bool := idp(true);
  var c: int := idp(9);
  assert a == 5;
  assert b == true;
  assert c == 99
//^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A freshened PRECONDITION still gates

`pos` requires `x > 0` and is called with `-3`. Freshening rewrites the contract at the call
site, so the risk is that the precondition is rewritten into something trivially true rather
than merely retyped. The failure is reported at the CALL, which is where the obligation
lives. -/

-- The Core interpreter runs this and reproduces the precondition failure at the annotated
-- range. The STANDALONE Laurel interpreter is skipped because it localizes the same failure
-- differently: it reports the call expression `pos(-3, 9)` (snippet cols 16-26) where the
-- verifier and the Core interpreter both report the whole declaration statement (cols 2-26),
-- and one annotation cannot pin both ranges.
#eval testLaurelExecution { skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure pos<T>(x: int, t: T) returns (y: T) requires x > 0 opaque ensures y == t { y := t };

procedure freshenedPreconditionGates()
  entry
  opaque
{
  var g: int := pos(-3, 9);
//^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
  assert 1 == 1
};
#end

/-! ## An UNCALLED polymorphic procedure is still checked

With no call site there is no instantiation to freshen at, so a naive implementation would
emit nothing and the contract would go unchecked — silently, since there is no diagnostic to
notice. `GenOpaqueTypeParams` substitutes an opaque type for the type variable so the body
VC encodes anyway. The pair below is what makes that visible: a true contract verifies and a
false one fails, both with the procedure never called.

The true half marks its `uncalledTrueContract` stub `entry`, so both interpreters at least
run the program that carries the uncalled declaration. The false half cannot: the failure it
pins is `bad`'s own body VC, and with no call site a concrete run never enters that body, so
the annotation would have nothing to fire on. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure idp<T>(x: T) returns (r: T) opaque ensures r == x { r := x };
procedure uncalledTrueContract() entry opaque { assert 1 == 1 };
#end

-- Verification-only: the annotated `postcondition does not hold` is `bad`'s own body VC, and
-- `bad` is never called, so no entry point can reach it — an interpreter run reports nothing
-- and the annotation would never fire.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure bad<T>(x: T, z: T) returns (r: T)
  opaque
  ensures r == z
//        ^^^^^^ error: postcondition does not hold
{ r := x };
procedure uncalledFalseContract() opaque { assert 1 == 1 };
#end
