/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
One object seen at two instantiations of a generic composite has one copy of each field, so a
write through one view is seen through the other, and no constraint is assumed for a field two
instantiations declare at different types. The views can be one object when a composite extends
two instantiations, or whenever a generic procedure's type variables are instantiated alike.
Tests that need a constrained instantiation such as `Box<int8>` reach it through a
`TotalMap int int8` argument, since Resolution rejects `Box<int8>` as a declared type.
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

-- A composite extending two instantiations is both at once, so `y`'s write is seen through `x`.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var n: int }
composite D extends Box<int>, Box<bool> { }

procedure multipleInheritance()
  opaque
  modifies *
{
  var d: D := new D;
  var x: Box<int> := d;
  var y: Box<bool> := d;
  x#n := 1;
  y#n := 2;
  assert x#n == 2;
  assert x#n == 1
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Two type variables, verified at a witness type each: `x` and `y` can be one object when `A = B`.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var n: int }

procedure twoTypeVariables<A, B>(x: Box<A>, y: Box<B>)
  opaque
  modifies *
{
  x#n := 1;
  y#n := 2;
  assert x#n == 1
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- A field of the type variable: after `y#v := b`, `x#v` may be `b`.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var v: T }

procedure typeVariableField<A, B>(x: Box<A>, y: Box<B>, a: A, b: B)
  opaque
  modifies *
{
  x#v := a;
  y#v := b;
  assert x#v == a
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Parameters at two concrete instantiations are not assumed to be different objects, though no
-- composite here extends both.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Item { }
composite Box<T> { var n: int }

procedure twoInstantiations(x: Box<Item>, y: Box<int>)
  opaque
  modifies *
{
  x#n := 1;
  y#n := 2;
  assert x#n == 1
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- A field-granular frame through one instantiation does not preserve the field of an object
-- that may be the same one through another.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var n: int }

procedure setN(y: Box<int>)
  opaque
  modifies y#n
{
  y#n := 2
};

procedure framedAcrossInstantiations<A>(x: Box<A>, y: Box<int>)
  opaque
  modifies *
{
  x#n := 1;
  setN(y);
  assert x#n == 1
//^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

-- An inherited field is stored under the family of the composite declaring it, not the receiver's.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var n: int }
composite Sub<T> extends Box<T> { }

procedure inheritedField<A, B>(x: Box<A>, y: Sub<B>)
  opaque
  modifies *
{
  x#n := 1;
  y#n := 2;
  assert x#n == 1
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Control: the frame names the same location the write updates, so a disjoint object keeps
-- its field.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var n: int }

procedure setN(y: Box<int>)
  opaque
  modifies y#n
{
  y#n := 2
};

procedure framedDisjoint(x: Box<int>, y: Box<int>)
  requires x != y
  opaque
  modifies *
{
  x#n := 1;
  setN(y);
  assert x#n == 1
};
#end

-- Control: separate allocations at two instantiations are different objects.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var n: int }

procedure separateAllocations()
  opaque
  modifies *
{
  var x: Box<int> := new Box<int>;
  var y: Box<bool> := new Box<bool>;
  x#n := 1;
  y#n := 2;
  assert x#n == 1
};
#end

-- Control: the family parent is no type tag, so where `Box<int>` is the only composite, `is` still
-- holds for a parameter.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var n: int }

procedure isInstantiation(x: Box<int>)
  opaque
{
  assert x is Box<int>
};
#end

-- Control: nor is it a parent to join at, so a `try` throwing two instantiations binds at their
-- common parent `Base`.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Base { }
composite Box<T> extends Base { var n: int }

procedure joinInstantiations(k: int) returns (r: int)
  opaque
  ensures r == 5
{
  r := 0;
  try {
    if k > 0 then { var b: Box<bool> := new Box<bool>; throw b }
    else { var i: Box<int> := new Box<int>; throw i }
  } catch e { r := 5 }
};
#end

-- A constraint only one instantiation has does not reach another: `toBox(m)` instantiates
-- `Box<int8>`, whose `v` is an `int8`, and a `Box<int>`'s `v` may hold 1000.
#eval testLaurelVerification <|
#strata
program Laurel;
constrained int8 = x: int where x >= -128 && x <= 127 witness 0
composite Box<T> { var v: T }
procedure toBox<T>(m: TotalMap int T) returns (r: Box<T>)
  opaque
{
  r := new Box<T>
};
procedure user(m: TotalMap int int8)
  opaque
{
  toBox(m)
};
procedure unconstrainedInstantiation(b: Box<int>)
  opaque
{
  assert b#v <= 127
//^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Nor is it assumed for the instantiation that has it, as one object can be both: a `D<int8>` is a
-- `Box<int8>` and a `Box<int>`, through which `y` sets its `v` to 1000.
#eval testLaurelVerification <|
#strata
program Laurel;
constrained int8 = x: int where x >= -128 && x <= 127 witness 0
composite Box<T> { var v: T }
composite D<S> extends Box<S>, Box<int> { }
procedure toD<S>(m: TotalMap int S) returns (r: D<S>)
  opaque
{
  r := new D<S>
};
procedure constrainedInstantiation<S>(m: TotalMap int S, d: D<S>)
  opaque
  modifies *
{
  var x: Box<S> := d;
  var y: Box<int> := d;
  y#v := 1000;
  var t: S := x#v
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
procedure user(m: TotalMap int int8)
  opaque
  modifies *
{
  constrainedInstantiation(m, toD(m))
};
#end

-- Nor where the other instantiation stores another type: through `P<bool, bool>`, `a` and `b` hold
-- one `bool` box, which read as an `int8` and as a `big` would contradict.
#eval testLaurelVerification <|
#strata
program Laurel;
constrained int8 = x: int where x >= -128 && x <= 127 witness 0
constrained big = x: int where x >= 1000 witness 1000
composite P<S, T> { var a: S var b: T }
composite D<S, T> extends P<S, T>, P<bool, bool> { }
procedure toD<S, T>(m: TotalMap int S, n: TotalMap int T) returns (r: D<S, T>)
  opaque
{
  r := new D<S, T>
};
procedure boxedApart<S, T>(m: TotalMap int S, n: TotalMap int T, d: D<S, T>)
  opaque
  modifies *
{
  var x: P<S, T> := d;
  var y: P<bool, bool> := d;
  y#a := true;
  y#b := true;
  var s: S := x#a;
//^^^^^^^^^^^^^^^ error: assertion does not hold
  var t: T := x#b;
//^^^^^^^^^^^^^^^ error: assertion does not hold
  assert false
//^^^^^^^^^^^^ error: assertion does not hold
};
procedure user(m: TotalMap int int8, n: TotalMap int big)
  opaque
  modifies *
{
  boxedApart(m, n, toD(m, n))
};
#end

-- Control: with no other instantiation, a `Box<int8>`'s `v` keeps its bound.
#eval testLaurelVerification <|
#strata
program Laurel;
constrained int8 = x: int where x >= -128 && x <= 127 witness 0
composite Box<T> { var v: T }
procedure toBox<T>(m: TotalMap int T) returns (r: Box<T>)
  opaque
{
  r := new Box<T>
};
procedure onlyInstantiation<T>(m: TotalMap int T, x: Box<T>)
  opaque
{
  var t: T := x#v
};
procedure user(m: TotalMap int int8)
  opaque
{
  onlyInstantiation(m, toBox(m))
};
#end

-- A constraint all instantiations share still holds where only the field's axiom supplies it: a
-- postcondition over parameters of two instantiations.
#eval testLaurelVerification <|
#strata
program Laurel;
constrained natInv = x: int where x >= 0 witness 0
composite Box<T> { var n: natInv }
procedure sharedConstraint(x: Box<int>, y: Box<bool>)
  opaque
  ensures x#n >= 0 && y#n >= 0
{
};
#end
