/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Generic composites through the full pipeline

`UnitTests/GenericCompositeTest.lean` drives generic composites through the corpus
harness, which asserts four counters (`translated`/`numVCs`/`numFailures`/
`numErrorOutcomes`) and — for rejections — a `MessageKind`. It deliberately does not pin
diagnostic LOCATIONS; that file's own `monomorphCollisionIsLocated` helper says so, and
works around it for one case. These tests use the inline-annotation form instead, so a
failure's reported RANGE is part of the expectation and a drift in location fails the
build.

Every case here is an `entry`, so each runs through both paths: the verifier, and the
concrete interpreter reading and writing the same fields
(`Core.Program.interpretMapsInFactory` reduces the heap's `select`/`update`). A
monomorphization bug that crossed two clones' field ids would then have to survive
both symbolic proof and concrete execution to go unnoticed.

The exception is a case calling a procedure whose body WRITES THE HEAP, which the Core
interpreter cannot run: every assert in the caller reports `condition did not reduce to bool`.
Such a case says `skipCoreInterpreter := true`; the standalone Laurel interpreter executes it. Its
false twin is verification-only, because the verifier reports that failure as `could not be
proved` where an interpreter says `does not hold`.

What monomorphization has to get right, and what each case pins:
* one instantiation — the field's declared `T` becomes the concrete type at the clone;
* two instantiations of the SAME composite in one program — the clones must not
  cross-link (a shared field id would make one instantiation's write visible to the other);
* a false twin per shape — so a clone's field read is not left unconstrained, which would
  let a false assertion pass vacuously.

The false twins pin that a clone's field read is constrained: a false assertion fails rather
than passing vacuously (a vacuous pass would show up as no diagnostic at all).
-/

-- Single instantiation: write then read a `T`-typed field at `int`.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }

procedure oneInstantiation()
  entry
  opaque
  modifies *
{
  var b: Box<int> := new Box<int>;
  b#val := 42;
  assert b#val == 42
};
#end

-- SOUNDNESS twin for the read: a FALSE assertion on the instantiated field must fail.
-- If the clone's field type were erased to something unconstrained, this would pass.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }

procedure oneInstantiationFalse()
  entry
  opaque
  modifies *
{
  var b: Box<int> := new Box<int>;
  b#val := 42;
  assert b#val == 43
//^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- TWO instantiations of one generic composite in a single program. The keystone: each
-- clone must own its own field, so writing through the `int` instance cannot be observed
-- through the `bool` one. Cross-linked clone ids would break this.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }

procedure twoInstantiations()
  entry
  opaque
  modifies *
{
  var bi: Box<int> := new Box<int>;
  var bb: Box<bool> := new Box<bool>;
  bi#val := 7;
  bb#val := true;
  assert bi#val == 7;
  assert bb#val == true
};
#end

-- Independence twin: the two instantiations are distinct allocations, so a false claim
-- about one is caught even though the other's assertion holds.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }

procedure twoInstantiationsFalse()
  entry
  opaque
  modifies *
{
  var bi: Box<int> := new Box<int>;
  var bb: Box<bool> := new Box<bool>;
  bi#val := 7;
  bb#val := true;
  assert bi#val == 7;
  assert bb#val == false
//^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Two type parameters, one field of each — pins that the per-instantiation substitution is
-- positional (a swapped substitution would type `first` as `bool`).
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Pair<A, B> { var first: A
 var second: B }

procedure twoTypeParams()
  entry
  opaque
  modifies *
{
  var p: Pair<int, bool> := new Pair<int, bool>;
  p#first := 3;
  p#second := false;
  assert p#first == 3;
  assert p#second == false
};
#end

-- A NON-generic composite alongside a generic one: the monomorphizer must leave the
-- ordinary composite completely untouched.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }
composite Plain { var n: int }

procedure genericAndPlainCoexist()
  entry
  opaque
  modifies *
{
  var b: Box<int> := new Box<int>;
  var q: Plain := new Plain;
  b#val := 1;
  q#n := 2;
  assert b#val + q#n == 3
};
#end

-- A HEAP-MUTATING polymorphic call nested in the argument of another polymorphic call, at two
-- instantiations in one non-generic caller. A fresh `Container`'s `value` is arbitrary, so
-- `c#value == 0` holds only if the inner calls ran and their postconditions reached the caller.
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
composite Container { var value: int }

procedure setget<T>(c: Container, x: T) returns (r: T) opaque ensures r == x ensures c#value == 0 modifies c { c#value := 0; r := x };
procedure sink<T>(x: T) returns (r: T) opaque ensures r == x { r := x };

procedure nestedHeapWriterPolyValues()
  entry
  opaque
  modifies *
{
  var c: Container := new Container;
  var i: int := sink(setget(c, 5));
  var b: bool := sink(setget(c, true));
  assert i == 5;
  assert b;
  assert c#value == 0
};
#end

-- Its twin, so the value assertions above are not vacuous.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Container { var value: int }

procedure setget<T>(c: Container, x: T) returns (r: T) opaque ensures r == x ensures c#value == 0 modifies c { c#value := 0; r := x };
procedure sink<T>(x: T) returns (r: T) opaque ensures r == x { r := x };

procedure nestedHeapWriterPolyValuesFalseTwin()
  opaque
{
  var c: Container := new Container;
  var i: int := sink(setget(c, 5));
  var b: bool := sink(setget(c, true));
  assert i == 6
//^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

-- A poly heap-writer whose result is DISCARDED, at two instantiations. Its heap effect is not
-- discarded, so `c#value == 0` holds only if a call's postcondition reached the caller.
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
composite Container { var value: int }

procedure setget<T>(c: Container, x: T) returns (r: T) opaque ensures r == x ensures c#value == 0 modifies c { c#value := 0; r := x };

procedure discardPolyResultTwice()
  entry
  opaque
  modifies *
{
  var c: Container := new Container;
  setget(c, 5);
  setget(c, true);
  assert c#value == 0
};
#end

-- Its twin, so the assertion above is not vacuous.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Container { var value: int }

procedure setget<T>(c: Container, x: T) returns (r: T) opaque ensures r == x ensures c#value == 0 modifies c { c#value := 0; r := x };

procedure discardPolyResultTwiceFalseTwin()
  opaque
{
  var c: Container := new Container;
  setget(c, 5);
  setget(c, true);
  assert c#value == 1
//^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

-- A generic call whose ARGUMENT is another generic call, in a non-generic caller. Like every case
-- below, it ends with a false assertion, so the true one is not vacuous.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }

procedure inr<T>(b: Box<T>) returns (r: Box<T>) opaque ensures r#val == b#val { r := b };
procedure otr<T>(b: Box<T>) returns (r: T)      opaque ensures r == b#val    { r := b#val };

procedure nestedGenericCallInArgument()
  entry
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 7;
  var got: int := otr(inr(bx));
  assert got == 7;
  assert got == 8
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- The same one level deeper: `otr(mid(inr(bx)))`.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }

procedure inr<T>(b: Box<T>) returns (r: Box<T>) opaque ensures r#val == b#val { r := b };
procedure mid<T>(b: Box<T>) returns (r: Box<T>) opaque ensures r#val == b#val { r := b };
procedure otr<T>(b: Box<T>) returns (r: T)      opaque ensures r == b#val    { r := b#val };

procedure nestedGenericDepth3()
  entry
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 7;
  var got: int := otr(mid(inr(bx)));
  assert got == 7;
  assert got == 8
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- The same nesting inside a GENERIC caller, so it is rewritten in a cloned body.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }

procedure inr<T>(b: Box<T>) returns (r: Box<T>) opaque ensures r#val == b#val { r := b };
procedure mid<T>(b: Box<T>) returns (r: T)      opaque ensures r == b#val    { r := b#val };
procedure wrapper<S>(b: Box<S>) returns (r: S)  opaque ensures r == b#val    { r := mid(inr(b)) };

procedure nestedGenericInCloneBody()
  entry
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 7;
  var got: int := wrapper(bx);
  assert got == 7;
  assert got == 8
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- The inner generic call need not involve a generic composite: `idp` only passes the box along.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }

procedure idp<T>(x: T) returns (r: T)           opaque ensures r == x        { r := x };
procedure otr<T>(b: Box<T>) returns (r: T)      opaque ensures r == b#val    { r := b#val };

procedure nestedValueGenericCallInArgument()
  entry
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 7;
  var got: int := otr(idp(bx));
  assert got == 7;
  assert got == 8
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- The same inside a GENERIC caller, where `idp`'s instantiation is solved under the clone's
-- substitution.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }

procedure idp<T>(x: T) returns (r: T)           opaque ensures r == x        { r := x };
procedure otr<T>(b: Box<T>) returns (r: T)      opaque ensures r == b#val    { r := b#val };
procedure wrapper<S>(b: Box<S>) returns (r: S)  opaque ensures r == b#val    { r := otr(idp(b)) };

procedure nestedValueGenericInCloneBody()
  entry
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 7;
  var got: int := wrapper(bx);
  assert got == 7;
  assert got == 8
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- A `new` as the argument, the only thing that determines `T`.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }

procedure one<T>(b: Box<T>) returns (r: int) opaque ensures r == 1 { r := 1 };

procedure newInArgument()
  entry
  opaque
  modifies *
{
  var got: int := one(new Box<int>);
  assert got == 1;
  assert got == 2
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end
