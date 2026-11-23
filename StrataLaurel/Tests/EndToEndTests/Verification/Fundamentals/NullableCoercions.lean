/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata


#eval testLaurelVerification <|
#strata
program Laurel;
procedure wrapAndUnwrap(x: int) returns (r: int)
  opaque
  ensures r == x
{
  var n: NullableRef<int> := x;
  assert NullableRef..isNonNull(n);
  var m: int := n;
  return m
};
#end


#eval testLaurelVerification <|
#strata
program Laurel;
procedure unwrapMaybeNull(n: NullableRef<int>) returns (r: int)
  opaque
{
  var m: int := n;
//              ^ error: the reference is not null does not hold
  return m
};
#end


#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { }
procedure legsOrZero(a: NullableRef<Animal>) returns (r: int)
  opaque
{
  if NullableRef..isNull(a) then { return 0 };
  var b: Animal := a;
  return b#legs
};
procedure orNull(d: Dog, keep: bool) returns (r: NullableRef<Dog>)
  opaque
  ensures keep ==> NullableRef..isNonNull(r)
{
  if keep then { return d };
  return Null()
};
procedure caller() opaque {
  var d: Dog := new Dog;
  var x: int := legsOrZero(d);
  var y: int := legsOrZero(Null());
  var e: Dog := orNull(d, true)
};
#end


#eval testLaurelVerification <|
#strata
program Laurel;
procedure id<T>(x: T) returns (r: T) opaque ensures r == x { return x };
procedure keep(n: NullableRef<int>) returns (r: NullableRef<int>)
  opaque
  ensures r == n
//        ^^^^^^ error: postcondition does not hold
{
  var m: NullableRef<int> := id(n);
//                              ^ error: the reference is not null does not hold
  return m
};
#end


#eval testLaurelVerification <|
#strata
program Laurel;
composite Cell {
  var v: int
  procedure get(self: Cell) returns (r: int) opaque ensures r == self#v { return self#v };
}
procedure useCell(c: NullableRef<Cell>) returns (r: int)
  opaque
  modifies *
{
  if NullableRef..isNonNull(c) then {
    c#v := 3;
    var x: int := c#get();
    assert x == 3
  };
  return c#v
//       ^ error: the reference is not null does not hold
};
#end


#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
procedure takesAnimal(a: Animal) opaque;
procedure passNull() opaque {
  takesAnimal(Null())
//            ^^^^^^ error: the reference is not null does not hold
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { }
procedure compare(a: Animal, d: Dog, n: NullableRef<Animal>) opaque {
  assert NullableRef..isNull(n) ==> a != n;
  if NullableRef..isNonNull(n) then { assert n != a || a == n };
  var b: bool := d == n
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
procedure f<T>(n: NullableRef<T>, x: T) opaque;
procedure caller() opaque { f(5, 5) };
#end

#eval testLaurelVerification <|
#strata
program Laurel;
procedure g<T>(n: NullableRef<T>) returns (r: bool) opaque ensures r == NullableRef..isNonNull(n);
procedure caller() opaque { var b: bool := g(5); assert b };
#end

#eval testLaurelVerification <|
#strata
program Laurel;
procedure deref<T>(n: NullableRef<T>) returns (r: T) opaque {
  var y: T := n;
//            ^ error: the reference is not null does not hold
  return y
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
procedure wrap<T>(x: T) returns (r: NullableRef<T>) opaque ensures NullableRef..isNonNull(r) {
  var n: NullableRef<T> := x;
  return n
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { }
procedure up(d: NullableRef<Dog>) returns (r: NullableRef<Animal>) opaque { return d };
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { }
procedure takesAnimal(n: NullableRef<Animal>) opaque;
procedure passDog(d: NullableRef<Dog>) opaque { takesAnimal(d) };
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { }
procedure sameRef(d: NullableRef<Dog>, a: NullableRef<Animal>) opaque {
  var b: bool := d == a;
  assert NullableRef..isNull(d) && NullableRef..isNull(a) ==> b
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { }
procedure down(a: NullableRef<Animal>) returns (r: NullableRef<Dog>) opaque { return a };
//                                                                                   ^ error: expected 'NullableRef<Dog>', got 'NullableRef<Animal>'
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Box<T> { var v: T }
datatype Holder<T> { H(b: Box<T>) }
composite Dog extends Animal { }
procedure up(h: Holder<Dog>) returns (r: Holder<Animal>) opaque { return h };
//                                                                       ^ error: expected 'Holder<Animal>', got 'Holder<Dog>'
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Base { var x: int }
composite Sub extends Base { }
procedure isSubOfNullable(b: NullableRef<Base>) returns (r: bool) opaque ensures NullableRef..isNull(b) ==> !r { return b is Sub };
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Base { var x: int }
composite Sub extends Base { }
procedure isSubOfNullableUnconditional(b: NullableRef<Base>) returns (r: bool) opaque ensures !r { return b is Sub };
//                                                                                            ^^ error: postcondition does not hold
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var v: int }
procedure joinField(b: bool, c: C) returns (r: int) opaque {
  var k: int := (if b then c else Null())#v;
//               ^^^^^^^^^^^^^^^^^^^^^^^ error: the reference is not null does not hold
  return k
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var v: int }
procedure joinEq(b: bool, c: C) returns (r: bool) opaque {
  var k: bool := (if b then c else Null()) == c;
  return k
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { }
procedure joinCovariant(b: bool, a: Animal, d: NullableRef<Dog>) returns (r: int)
  requires NullableRef..isNonNull(d)
  opaque
{
  var k: int := (if b then a else d)#legs;
  return k
};
procedure joinCovariantReversed(b: bool, a: Animal, d: NullableRef<Dog>) returns (r: int)
  requires NullableRef..isNonNull(d)
  opaque
{
  var k: int := (if b then d else a)#legs;
  return k
};
procedure joinCovariantMaybeNull(b: bool, a: Animal, d: NullableRef<Dog>) returns (r: bool)
  opaque
{
  var k: bool := (if b then d else a) == a;
  return k
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite E { var v: int }
procedure throwUnchecked(e: NullableRef<E>) throws (x: E) opaque {
  throw e
//      ^ error: the reference is not null does not hold
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite E { var v: int }
procedure throwChecked(e: NullableRef<E>) throws (x: E) opaque {
  if NullableRef..isNonNull(e) then { throw e }
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var v: int }
composite Base { procedure m(self: Base, c: NullableRef<C>) returns (r: int) opaque ensures r >= 0 { r := 0 }; }
composite Sub extends Base { procedure m(self: Sub, c: NullableRef<C>) returns (r: int) opaque ensures r == 1 { r := 1 }; }
procedure caller(d: C) opaque {
  var b: Base := new Sub;
  var x: int := b#m(d);
  assert x == 1
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var v: int }
composite Base { procedure m(self: Base, c: NullableRef<C>) returns (r: int) opaque ensures r >= 0 { r := 0 }; }
composite Sub extends Base { procedure m(self: Sub, c: C) returns (r: int) opaque ensures r == -1 { r := -1 }; }
procedure g(b: Base) opaque {
  var x: int := b#m(Null());
  assert x >= 0
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var v: int }
composite Base<T> { procedure m(self: Base<T>, c: NullableRef<T>) opaque {}; }
composite Sub extends Base<C> { procedure m(self: Sub, c: C) opaque {}; }
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var v: int }
composite Base { procedure mk(self: Base) returns (r: NullableRef<C>) opaque { r := Null() }; }
composite Sub extends Base { procedure mk(self: Sub) returns (r: C) opaque { r := new C }; }
//                                     ^^ error: override 'Sub.mk' has an output signature incompatible with the method it overrides on 'Base': each output must have the same type as, or a subtype of, the overridden method's corresponding output (1 output(s) vs 1).
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { }
composite Base { procedure mk(self: Base) returns (r: NullableRef<Animal>) opaque { r := Null() }; }
composite Sub extends Base { procedure mk(self: Sub) returns (r: NullableRef<Dog>) opaque { r := Null() }; }
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var v: int }
composite Base { procedure mk(self: Base) returns (r: C) opaque { r := new C }; }
composite Sub extends Base { procedure mk(self: Sub) returns (r: NullableRef<C>) opaque { r := Null() }; }
//                                     ^^ error: override 'Sub.mk' has an output signature incompatible with the method it overrides on 'Base': each output must have the same type as, or a subtype of, the overridden method's corresponding output (1 output(s) vs 1).
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var v: int }
procedure joinFieldRev(b: bool, c: C) returns (r: int) opaque {
  var k: int := (if b then Null() else c)#v;
//               ^^^^^^^^^^^^^^^^^^^^^^^ error: the reference is not null does not hold
  return k
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var v: int }
procedure joinEqRev(b: bool, c: C) returns (r: bool) opaque {
  var k: bool := (if b then Null() else c) == c;
  return k
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var x: int }
procedure set(c: NullableRef<C>)
  opaque
  modifies c
{
  if NullableRef..isNonNull(c) then { c#x := 1 }
};
procedure callNull() opaque modifies * {
  set(Null())
};
procedure keepsFresh(c: C) opaque modifies * {
  var a: C := new C;
  a#x := 7;
  set(c);
  assert a#x == 7
};
procedure keepsOther(c: C, d: C) opaque modifies * {
  d#x := 7;
  assume d != c;
  set(c);
  assert d#x == 7
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var x: int }
procedure set(c: NullableRef<C>)
  opaque
  modifies c
{
  if NullableRef..isNonNull(c) then { c#x := 1 }
};
procedure changes(c: C) opaque modifies * {
  c#x := 7;
  set(c);
  assert c#x == 7
//^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var x: int }
procedure setUnguarded(c: NullableRef<C>)
//        ^^^^^^^^^^^^ error: modifies clause could not be proved
  opaque
  modifies c
{
  c#x := 1
//^ error: the reference is not null does not hold
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var x: int }
procedure takesC(c: C) returns (r: int) opaque { return c#x };
procedure assignExpr(m: NullableRef<C>) returns (r: int) opaque {
  var n: NullableRef<C> := Null();
  var k: int := takesC(n := m);
//                     ^^^^^^ error: the reference is not null does not hold
  return k
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var x: int }
procedure takesC(c: C) returns (r: int) opaque { return c#x };
procedure assignExprGuarded(m: NullableRef<C>) returns (r: int) opaque {
  var n: NullableRef<C> := Null();
  if NullableRef..isNull(m) then { return 0 };
  var k: int := takesC(n := m);
  return k
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var x: int }
procedure takesC(c: C) returns (r: int) opaque { return c#x };
procedure declExpr(m: NullableRef<C>) returns (r: int) opaque {
  var k: int := takesC(var n := m);
//                     ^^^^^^^^^^ error: the reference is not null does not hold
  return k
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var x: int }
procedure takesC(c: C) returns (r: int) opaque { return c#x };
procedure declExprGuarded(m: NullableRef<C>) returns (r: int) opaque {
  if NullableRef..isNull(m) then { return 0 };
  var k: int := takesC(var n := m);
  return k
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var v: int }
procedure present<T>(t: T) returns (r: bool) opaque ensures r { return t == t };
procedure bareTypeParameterStopgap_unwrapsAtBareParameter(n: NullableRef<C>) opaque {
  var b: bool := present(n)
//                       ^ error: the reference is not null does not hold
};
procedure bareTypeParameterStopgap_guardedArgument(n: NullableRef<C>) opaque {
  if NullableRef..isNonNull(n) then { var b: bool := present(n) }
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var v: int }
procedure nn<T>(x: NullableRef<T>, d: T) returns (r: T) opaque;
procedure bareTypeParameterStopgap_notNested(n: NullableRef<C>, m: NullableRef<C>) opaque {
  var c: C := nn(n, m)
//                  ^ error: the reference is not null does not hold
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var v: int }
procedure keep<T>(n: NullableRef<T>) returns (r: T) opaque;
procedure bareTypeParameterStopgap_nullableParameterBindsPayload(n: NullableRef<C>) opaque {
  var c: C := keep(n)
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var v: int }
procedure bareTypeParameterStopgap_externalEquality(a: NullableRef<C>, b: NullableRef<C>) opaque {
  var e: bool := a == b;
  var d: bool := a != b;
  assert e == !d;
  assert NullableRef..isNull(a) && NullableRef..isNull(b) ==> e
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var v: int }
composite Holder {
  procedure put<T>(self: Holder, x: T) returns (r: bool) opaque ensures r { return x == x };
}
procedure bareTypeParameterStopgap_unwrapsAtInstanceMethod(h: Holder, n: NullableRef<C>) opaque {
  var b: bool := h#put(n)
//                     ^ error: the reference is not null does not hold
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { }
procedure compareNullableWithSupertype(d: NullableRef<Dog>, a: Animal) opaque {
  var e: bool := d == a;
  var f: bool := a == d;
  var g: bool := d != a;
  assert e == f;
  assert e == !g;
  assert e ==> NullableRef..isNonNull(d)
};
procedure nullNeverEqualsSupertype(a: Animal) opaque {
  var d: NullableRef<Dog> := Null();
  assert !(d == a)
};
procedure payloadEqualsSupertype(p: Dog) opaque {
  var d: NullableRef<Dog> := NonNull(p);
  var a: Animal := p;
  assert d == p;
  assert d == a
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Dog { var legs: int }
composite Cat { var lives: int }
procedure compareUnrelated(d: NullableRef<Dog>, c: Cat) returns (r: bool) opaque {
  return d == c
//       ^^^^^^ error: cannot compare 'NullableRef<Dog>' with 'Cat' using '=='
};
#end
