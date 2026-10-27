/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Generic composites through the full pipeline

Failures are pinned with inline `// ^^^` annotations, so a failure's reported RANGE is part
of the expectation and a drift in location fails the build.

Nearly every case marks an `entry`, so it runs through all three paths: the verifier, the
concrete Core interpreter reading and writing the same fields
(`Core.Program.interpretMapsInFactory` reduces the heap's `select`/`update`), and the
standalone Laurel interpreter allocating and mutating the same objects. A
monomorphization bug that crossed two clones' field ids would then have to survive
symbolic proof and two independent concrete executions to go unnoticed. The handful of
cases that cannot be run name their reason at the block.

The false twin of a case calling a procedure whose body WRITES THE HEAP is verification-only,
because the verifier reports that failure as `could not be proved` where an interpreter says
`does not hold`.

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
#eval testLaurelExecution {} <|
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
#eval testLaurelExecution {} <|
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

/-! # Instantiation at a COLLECTION type

The cases above instantiate at scalars. A `TotalMap` argument is different because the
monomorph tag has to be built from a *compound* type: `instTagCommon` recurses into `.TMap`
to produce `TotalMap$a2$int$int`, and the heap box functions key off the same tag. If two
different `(K, V)` pairs produced the same tag, two distinct fields would share one box and
a write through one would be visible through the other — which is why the distinctness case
below reads BOTH fields back.

The first pair below is one of this file's few verification-only cases, and for a reason worth
recording: BOTH interpreters refuse it. `new Box<TotalMap int int>` leaves the monomorphized
field with no value, so reading it back (which `update(b#val, …)` does) hits an uninitialized
slot — the Laurel interpreter says `builtin 'update' applied to [.unset, .int, .int]` and the
Core interpreter says the assert `condition did not reduce to bool`. The NON-generic shape
two blocks down (`composite H { var mib: TotalMap int bool … }`) does the same read-before-write
and runs fine, so this is specific to allocating a generic composite instantiated at a
collection type, not to map fields in general.
-/

-- No Laurel interpreter: it cannot allocate a generic composite instantiated at a collection
-- type. The Core interpreter can, and runs this block.
#eval testLaurelExecution { skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Box<T> { var val: T }

// A generic composite instantiated at `TotalMap int int`: the boxed field round-trips.
procedure boxedMapArgument() entry
  opaque
  modifies *
{
  var b: Box<TotalMap int int> := new Box<TotalMap int int>;
  b#val := update(b#val, 1, 2);
  assert select(b#val, 1) == 2
};
#end

-- SOUNDNESS twin: the boxed `TotalMap` field is constrained, so a false read must fail.
-- No Laurel interpreter, as above; the Core interpreter runs it and fires the assert itself.
#eval testLaurelExecution { skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Box<T> { var val: T }

procedure boxedMapArgumentFalse() entry
  opaque
  modifies *
{
  var b: Box<TotalMap int int> := new Box<TotalMap int int>;
  b#val := update(b#val, 1, 2);
  assert select(b#val, 1) == 3
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Two `TotalMap` fields with DIFFERENT (K, V) pairs on one composite. This is the case that
-- catches a tag collision: both fields are read back, so a collision that made them share one
-- box shows up here.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite H { var mib: TotalMap int bool
 var mii: TotalMap int int }

procedure distinctMapFieldsStayDistinct()
  entry
  opaque
  modifies *
{
  var h: H := new H;
  h#mib := update(h#mib, 1, true);
  h#mii := update(h#mii, 1, 9);
  assert select(h#mib, 1) == true;
  assert select(h#mii, 1) == 9
};
#end

-- SOUNDNESS twin for the second of the two distinct fields.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite H { var mib: TotalMap int bool
 var mii: TotalMap int int }

procedure distinctMapFieldsFalse()
  entry
  opaque
  modifies *
{
  var h: H := new H;
  h#mib := update(h#mib, 1, true);
  h#mii := update(h#mii, 1, 9);
  assert select(h#mii, 1) == 8
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A nested `TotalMap` field

`TotalMap int TotalMap int int` (the grammar takes it without parentheses) makes the tag
build recursively — `TotalMap$a2$int$TotalMap$a2$int$int`. Only a recursive `.TMap` arm
produces that; a one-level arm would stop at the outer map. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite H { var m: TotalMap int TotalMap int int }

procedure nestedMapField()
  entry
  opaque
  modifies *
{
  var h: H := new H;
  var inner: TotalMap int int := update(select(h#m, 1), 2, 3);
  h#m := update(h#m, 1, inner);
  assert select(select(h#m, 1), 2) == 3
};
#end

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite H { var m: TotalMap int TotalMap int int }

procedure nestedMapFieldFalse()
  entry
  opaque
  modifies *
{
  var h: H := new H;
  var inner: TotalMap int int := update(select(h#m, 1), 2, 3);
  h#m := update(h#m, 1, inner);
  assert select(select(h#m, 1), 2) == 4
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A concrete collection passed to a GENERIC parameter

`TotalMap K V` as a parameter type is not a generic composite — it is a generic slot in the
consistency relation, which has to recurse into `.TMap` element-wise so a concrete
`TotalMap int bool` reaches the `K`/`V` wildcards. The `ensures r == m` is what makes the
accept observable: without it the case would pass merely by translating. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure idm<K, V>(m: TotalMap K V) returns (r: TotalMap K V) opaque ensures r == m { r := m };

procedure concreteMapIntoGenericParam()
  entry
  opaque
{
  var mm: TotalMap int bool;
  var rr: TotalMap int bool := idm(mm);
  assert rr == mm
};
#end

-- SOUNDNESS twin: the returned map is the one passed in, not an arbitrary map of the right
-- type — so comparing it to an unrelated `nn` must fail.
-- Verification-only because the negative is verifier-only: `mm` and `nn` are two
-- uninitialized maps, which the verifier keeps distinct but either interpreter gives the
-- same empty value, so `rr == nn` holds concretely and the annotation never fires.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure idm<K, V>(m: TotalMap K V) returns (r: TotalMap K V) opaque ensures r == m { r := m };

procedure concreteMapIntoGenericParamFalse()
  opaque
{
  var mm: TotalMap int bool;
  var nn: TotalMap int bool;
  var rr: TotalMap int bool := idm(mm);
  assert rr == nn
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## Instantiations in every type POSITION, not just a local's declaration

The monomorphizer collects instantiations by walking type slots and then rewrites them. A
slot it fails to walk leaves `Box<int>` un-lowered, which surfaces as a translation failure
far from the omission. So each case below puts the instantiation somewhere structurally
different: a datatype constructor argument, a quantifier binder in a body, a quantifier
binder in a CONTRACT, and a declaration with no initializer (which parses to
`.Var (.Declare …)` rather than the `.Assign [.Declare …] e` form the initialized case
takes). -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }
datatype Wrap { MkWrap(b: Box<int>) }

// Instantiation as a datatype constructor's argument type.
procedure instantiationInDatatype()
  entry
  opaque
{
  assert 1 == 1
};

// Instantiation as a quantifier binder's type, in a body. Deliberately NOT an `entry`:
// neither interpreter evaluates a quantifier (the Laurel one says
// `unsupported expression: quantifier`, the Core one that the assert's condition "did not
// reduce to bool"), so the monomorphized binder is pinned symbolically only.
procedure instantiationInQuantifierBinder()
  opaque
{
  var p: bool := forall(b: Box<int>) => true;
  assert p
};

// Instantiation in a declaration with NO initializer.
procedure instantiationInBareDeclaration()
  entry
  opaque
{
  var b: Box<int>;
  assert 1 == 1
};

// Instantiation in a CONTRACT position rather than the body. Cannot be an `entry`: an
// entry procedure may not carry a `requires` clause, because it initializes its globals as
// locals inside its body, which a contract cannot see.
procedure instantiationInPrecondition()
  requires forall(b: Box<int>) => true
  opaque
{
  assert 1 == 1
};
#end

-- SOUNDNESS twin for the quantifier binder: the quantified claim is a real obligation, so a
-- false body must fail rather than the binder's type making it vacuous.
-- Verification-only: neither interpreter evaluates a quantifier, so there is nothing to run.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Box<T> { var val: T }

procedure instantiationInQuantifierBinderFalse()
  opaque
{
  var p: bool := forall(b: Box<int>) => false;
  assert p
//^^^^^^^^ error: assertion does not hold
};
#end

-- A field SELECT inside a quantifier BODY. The heap-read analysis descends into a triggerless
-- quantifier's body, so `c#v` is eliminated there rather than surviving to fail at
-- translation. Verification-only, like the pair above: neither interpreter evaluates a
-- quantifier, so this and its false twin have nothing to run.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite C { var v: int }

procedure fieldReadInQuantifierBody()
  opaque
{
  var p: bool := forall(c: C) => c#v == c#v;
  assert p
};
#end

-- Verification-only for the same reason: the quantifier is not evaluated.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite C { var v: int }

procedure fieldReadInQuantifierBodyFalse()
  opaque
{
  var p: bool := forall(c: C) => c#v == 5;
  assert p
//^^^^^^^^ error: assertion does not hold
};
#end

-- A generic instantiated at a collection, reached through a datatype constructor argument:
-- the `.TMap` tag has to work in this position too. Equality on the constructed value is
-- what observes it.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }
datatype Wrap { MkWrap(b: Box<TotalMap int int>) }

procedure boxedMapInDatatype()
  entry
  opaque
  modifies *
{
  var b: Box<TotalMap int int> := new Box<TotalMap int int>;
  var w: Wrap := MkWrap(b);
  assert w == MkWrap(b)
};
#end

/-! ## NESTED generics, and the fixpoint that finds them

`Nest<T> { b: Box<T> }` instantiated at `int` requires `Box<int>` as well — the inner
instantiation comes from SUBSTITUTING into the outer one's field, not from anything the
program spells. The second pair is the discriminating case: `q#b := p#b` mentions `Box<int>`
nowhere, so it is reachable only by taking the fixpoint of "instantiate, then collect what
the instantiation's fields need". A single collection pass finds `Nest<int>` and stops. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }
composite Nest<T> { var b: Box<T> }

// The inner instantiation is also named directly.
procedure nestedGeneric()
  entry
  opaque
  modifies *
{
  var inner: Box<int> := new Box;
  inner#val := 5;
  var p: Nest<int> := new Nest;
  p#b := inner;
  var got: Box<int> := p#b;
  assert got#val == 5
};

// The inner instantiation is reachable ONLY through the outer's substituted field.
procedure nestedGenericViaFieldOnly()
  entry
  opaque
  modifies *
{
  var p: Nest<int> := new Nest;
  var q: Nest<int> := new Nest;
  q#b := p#b;
  assert 1 == 1
};
#end

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }
composite Nest<T> { var b: Box<T> }

procedure nestedGenericFalse()
  entry
  opaque
  modifies *
{
  var inner: Box<int> := new Box;
  inner#val := 5;
  var p: Nest<int> := new Nest;
  p#b := inner;
  var got: Box<int> := p#b;
  assert got#val == 6
//^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## Explicit `new C<τ>`

The allocation carries its own instantiation, so it works in positions where no declared
type is available to read one from. The self-seeding case is the one that needs it: the
`new Box<bool>` is the SOLE mention of `Box<bool>` in the program — it flows into a generic
sink, so nothing annotates it — which means collection has to happen at the allocation site
itself. The bare `new Box` form still works where a declared type supplies the arguments. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }
composite Holder { var b: Box<int> }
procedure take(x: Box<int>) opaque { assert 1 == 1 };
procedure sink<T>(x: T): int { return 0 };

// `new Box<int>` as the value of a field write.
procedure newWithTypeArgsIntoField()
  entry
  opaque
  modifies *
{
  var h: Holder := new Holder;
  var inner: Box<int> := new Box<int>;
  inner#val := 7;
  h#b := inner;
  var got: Box<int> := h#b;
  assert got#val == 7
};

// `new Box<int>` as a call argument.
procedure newWithTypeArgsAsArgument()
  entry
  opaque
  modifies *
{
  take(new Box<int>);
  assert 1 == 1
};

// Two explicit instantiations pick distinct monomorphs.
procedure newWithTypeArgsTwoInstantiations()
  entry
  opaque
  modifies *
{
  var a: Box<int> := new Box<int>;
  a#val := 5;
  var b: Box<bool> := new Box<bool>;
  b#val := true;
  assert a#val == 5
};

// The bare legacy form: arguments come from the declared type.
procedure newBareTakesArgsFromDeclaredType()
  entry
  opaque
  modifies *
{
  var b: Box<int> := new Box;
  b#val := 1;
  assert b#val == 1
};

// SELF-SEEDING: `new Box<bool>` is the only mention of that instantiation anywhere.
procedure newWithTypeArgsSelfSeeds()
  entry
  opaque
  modifies *
{
  var r: int := sink(new Box<bool>);
  assert r == 0
};
#end

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }
composite Holder { var b: Box<int> }

procedure newWithTypeArgsIntoFieldFalse()
  entry
  opaque
  modifies *
{
  var h: Holder := new Holder;
  var inner: Box<int> := new Box<int>;
  inner#val := 7;
  h#b := inner;
  var got: Box<int> := h#b;
  assert got#val == 8
//^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## `is` and `as` with a generic instantiation as the target

The `is`/`as` target is a full type rather than a bare name, so it can be an instantiation.
`is` keys off the monomorph's runtime type tag (`Box$a1$int`), and `as` lowers through the
same is-guard — so the target has to be monomorphized before either is lowered, and a
nested target (`Box<Pair<int, bool>>`) has to produce the nested tag. The monomorphic
baseline is here as the control: it must keep working. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Plain { var v: int }
composite Box<T> { var val: T }
composite Pair<A, B> { var a: A
 var b: B }

// Baseline: a non-generic target.
procedure isMonomorphicTarget()
  entry
  opaque
  modifies *
{
  var p: Plain := new Plain;
  assert p is Plain
};

// The target is a specific instantiation.
procedure isGenericInstantiation()
  entry
  opaque
  modifies *
{
  var b: Box<int> := new Box<int>;
  assert b is Box<int>
};

// `as` to the matching instantiation.
procedure asGenericInstantiation()
  entry
  opaque
  modifies *
{
  var b: Box<int> := new Box<int>;
  var c: Box<int> := b as Box<int>;
  assert c#val == c#val
};

// A NESTED instantiation as the target: the tag nests too (`Box$a1$Pair$a2$int$bool`).
procedure isNestedGenericTarget()
  entry
  opaque
  modifies *
{
  var b: Box<Pair<int, bool>> := new Box<Pair<int, bool>>;
  assert b is Box<Pair<int, bool>>
};
#end

/-! ## SOURCE COMPATIBILITY: the name `Box` belongs to user programs

`HeapParameterization` generates a boxing datatype, and it is called `$Box` — in Laurel's
reserved `$`-namespace — precisely so that user declarations spelled `Box` do not collide
with it. Rejecting any of the three forms below would be a regression, and each is paired
with a false twin so "accepted" cannot be mistaken for "verified vacuously".

A generic `composite Box<T>` is legal for a different reason and so is not repeated here:
it is monomorphized to `Box$a1$int`, so the plain name never reaches heap lowering. The
forms below are the ones that do. (Contrast `Heap`, `Field`, `TypeTag` and `Composite`,
whose generated forms carry no `$` and so genuinely are reserved.) -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
datatype Box { MkB(v: int) }

procedure userDatatypeNamedBox()
  entry
  opaque
{
  var b: Box := MkB(7);
  assert Box..v(b) == 7
};
#end

#eval testLaurelExecution {} <|
#strata
program Laurel;
datatype Box { MkB(v: int) }

procedure userDatatypeNamedBoxFalse()
  entry
  opaque
{
  var b: Box := MkB(7);
  assert Box..v(b) == 8
//^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- The GENERIC datatype form matters most: a generic datatype is NOT monomorphized, so it
-- reaches heap lowering under its own name and has to survive there.
#eval testLaurelExecution {} <|
#strata
program Laurel;
datatype Box<T> { MkB(v: T) }

procedure userGenericDatatypeNamedBox()
  entry
  opaque
{
  var b: Box<int> := MkB(7);
  assert Box..v(b) == 7
};
#end

#eval testLaurelExecution {} <|
#strata
program Laurel;
datatype Box<T> { MkB(v: T) }

procedure userGenericDatatypeNamedBoxFalse()
  entry
  opaque
{
  var b: Box<int> := MkB(7);
  assert Box..v(b) == 8
//^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box { var val: int }

procedure userCompositeNamedBox()
  entry
  opaque
  modifies *
{
  var b: Box := new Box;
  b#val := 7;
  assert b#val == 7
};
#end

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box { var val: int }

procedure userCompositeNamedBoxFalse()
  entry
  opaque
  modifies *
{
  var b: Box := new Box;
  b#val := 7;
  assert b#val == 8
//^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- SOUNDNESS twin for the FIXPOINT-discovered monomorph specifically: the clone reached only
-- through the outer composite's substituted field is a real composite with a real field, so a
-- false read of it must fail. `nestedGenericFalse` above pins the directly-named inner
-- instantiation; this one pins the one only the fixpoint found.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }
composite Nest<T> { var b: Box<T> }

procedure nestedGenericViaFieldOnlyFalse()
  entry
  opaque
  modifies *
{
  var p: Nest<int> := new Nest;
  var inner: Box<int> := new Box;
  inner#val := 7;
  p#b := inner;
  var got: Box<int> := p#b;
  assert got#val == 8
//^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- A generic method calling a generic procedure at its composite's `T` and at its own `U`.
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure f<T>(x: T) returns (r: T) opaque ensures r == x { r := x };
composite Box<T> {
  var val: T
  procedure both<U>(self: Box<T>, u: U) opaque {
    var a := f(self#val);
    var b := f(u);
    assert a == self#val && b == u;
    assert b != u
//  ^^^^^^^^^^^^^ error: assertion does not hold
  };
}

procedure methodCallsAtBothTypeParameters()
  entry
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 1;
  bx#both(true)
};
#end
