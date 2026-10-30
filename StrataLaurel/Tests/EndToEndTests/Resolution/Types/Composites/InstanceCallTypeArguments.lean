/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # An instance call's type arguments

`obj#m(…)` takes the declaring composite's type parameters from the receiver and infers the
method's own from the arguments and the expected type. Each block pins calls this rejects at
resolution, most beside a call it accepts. Calls like these run through the whole pipeline in
`Execution/Types/Composites/InstanceProcedures.lean`. -/

/-! ## The receiver fixes the composite's parameters, through an `extends` remap

`Flip<X, Y> extends Base<Y, X>`, so `Flip<int, bool>` reaches `Base`'s methods at `X := bool`,
not at the `int` its own first type argument would suggest, in parameters and results alike. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Base<X, Y> {
  var a: X
  var b: Y
  procedure fst(self: Base<X, Y>)
    returns (r: X)
    opaque
    ensures r == self#a
  { r := self#a };
  procedure same(self: Base<X, Y>, x: X)
    returns (r: X)
    opaque
    ensures r == x
  { r := x };
}
composite Flip<X, Y> extends Base<Y, X> { var z: int }

procedure remappedOwnerParameter()
  opaque
{
  var f: Flip<int, bool> := new Flip<int, bool>;
  var h: bool := f#fst();
  var g: int := f#fst();
//              ^^^^^^^ error: expected 'int', got 'bool'
  var k: bool := f#same(true);
  var j: bool := f#same(1);
//                      ^ error: cannot pass 'int' as the 'bool' parameter of 'same'
  assert 1 == 1
};
#end

/-! ## A method's own type parameter is inferred from the argument -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Box<T> {
  var val: T
  procedure idu<U>(self: Box<T>, x: U)
    returns (r: U)
    opaque
    ensures r == x
  { r := x };
}

procedure ownParameter()
  opaque
{
  var b: Box<int> := new Box<int>;
  var y: int := b#idu(5);
  var z: bool := b#idu(5);
//               ^^^^^^^^ error: expected 'bool', got 'int'
  assert 1 == 1
};
#end

/-! ## A repeated type parameter couples its arguments -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Box<T> {
  var val: T
  procedure two<U>(self: Box<T>, x: U, y: U)
    returns (r: U)
    opaque
    ensures r == x
  { r := x };
}

procedure coupledOwnParameter()
  opaque
{
  var b: Box<int> := new Box<int>;
  var w: int := b#two(1, 2);
  var z: int := b#two(1, true);
//              ^^^^^^^^^^^^^^ error: cannot infer type argument 'U' of 'two': 'int' and 'bool' disagree
  assert 1 == 1
};
#end

/-! ## Several outputs, and an `inout` parameter, are instantiated too -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Box<T> {
  var val: T
  procedure both<U>(self: Box<T>, x: U)
    returns (a: U, b: T)
    opaque
    ensures a == x
  { a := x; b := self#val };
  procedure keep<U>(self: Box<T>, x: U)
    returns (x: U)
    opaque
    ensures true
  { };
}

procedure instantiatedOutputs()
  opaque
{
  var b: Box<int> := new Box<int>;
  var y: int := 0;
  var z: int := 0;
  var w: bool := true;
  assign y, z := b#both(5);
  assign y, w := b#both(5);
//               ^^^^^^^^^ error: expected '(int, bool)', got '(int, int)'
  assign z := b#keep(z);
  assign w := b#keep(7);
//            ^^^^^^^^^ error: expected 'bool', got 'int'
  assert 1 == 1
};
#end

/-! ## In a generic method, the receiver still fixes the composite's parameters

On a `Box<int>`, `mix`'s `a: T` is an `int` slot and its result an `int`, whatever the arguments
say: `true` is the wrong argument, rather than a binding of `T`, even where two arguments meet
in `T` as in `pair`. A wrong variable is reported where it is passed, not where it is declared,
and alone: not with `fill`'s `V`, which it would have bound, as undetermined too. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Box<T> {
  var v: T
  procedure mix<U>(self: Box<T>, a: T, b: U)
    returns (r: T)
    opaque
    ensures r == a
  { r := a };
  procedure pair<U>(self: Box<T>, a: T, c: T, b: U)
    returns (r: T)
    opaque
    ensures r == a
  { r := a };
  procedure fill<V>(self: Box<T>, s: Set<V>)
    opaque
    ensures true;
}

procedure ownerParameterInGenericMethod(flag: bool)
  opaque
{
  var bi: Box<int> := new Box<int>;
  var g: int := bi#mix(2, 5);
  var h: int := bi#mix(true, 5);
//                     ^^^^ error: cannot pass 'bool' as the 'int' parameter of 'mix'
  var k: int := bi#mix(flag, 5);
//                     ^^^^ error: cannot pass 'bool' as the 'int' parameter of 'mix'
  var w: bool := bi#mix(2, 5);
//               ^^^^^^^^^^^^ error: expected 'bool', got 'int'
  var p: int := bi#pair(1, 2, 5);
  var q: int := bi#pair(true, 2, 5);
//                      ^^^^ error: cannot pass 'bool' as the 'int' parameter of 'pair'
  bi#fill(5);
//        ^ error: cannot pass 'int' as the 'Set<V>' parameter of 'fill'
  assert 1 == 1
};
#end

/-! ## An argument wider than the receiver's binding

`a` is an `Animal`, which `b`'s `T := Dog` does not admit. The lifted call would bind `T := Animal`
and reject `b`; here `a` is the one blamed. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Animal { }
composite Dog extends Animal { }
composite Box<T> {
  var v: T
  procedure put(self: Box<T>, x: T)
    opaque
    ensures true;
}

procedure widerArgument(b: Box<Dog>, d: Dog, a: Animal)
  opaque
{
  b#put(d);
  b#put(a);
//      ^ error: cannot pass 'Animal' as the 'Dog' parameter of 'put'
  assert 1 == 1
};
#end

/-! ## A type parameter only the binding can fix

`mk<V>` mentions `V` in its result alone: an annotated binding determines it, an unannotated one
leaves it undetermined. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Box<T> {
  var v: T
  procedure mk<V>(self: Box<T>)
    returns (r: V)
    opaque
    ensures true;
}

procedure determinedByTheBinding()
  opaque
{
  var bi: Box<int> := new Box<int>;
  var g: int := bi#mk();
  var x := bi#mk();
//         ^^^^^^^ error: cannot infer type argument 'V' of 'mk': annotate the variable or output it is assigned to with a concrete type
  assert 1 == 1
};
#end

/-! ## A receiver in the caller's type variables

`b`'s `T := U` in `outer<U>` is what the arguments are passed at, as in the static call the lift
makes: a `Dog` and a `Cat` both go, and `b#put(5)` is a `U`, for which `show` has no single
overload. With no argument at `T`, `b#get()` is a `U` too, which `idf` can infer its `V` from. In
`inMap<U>`, `m`'s `T := Map<int, U>` outranks `5`, which contradicts it. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Animal { }
composite Dog extends Animal { }
composite Cat extends Animal { }
composite Box<T> {
  var v: T
  procedure put(self: Box<T>, a: T)
    returns (r: T)
    opaque
    ensures r == a
  { r := a };
  procedure pick(self: Box<T>, a: T, c: T)
    returns (r: T)
    opaque
    ensures r == a
  { r := a };
  procedure get(self: Box<T>)
    returns (r: T)
    opaque
    ensures r == self#v
  { r := self#v };
}
procedure idf<V>(a: V)
  returns (r: V)
  opaque
  ensures r == a
{ r := a };
procedure show(x: int) opaque;
procedure show(x: bool) opaque;

procedure outer<U>(b: Box<U>, u: U, d: Dog, c: Cat)
  opaque
{
  var g := b#get();
  var h := idf(g);
  var w: U := b#put(u);
  var p: U := b#pick(d, c);
  show(b#put(5));
//^^^^^^^^^^^^^^ error: ambiguous call to 'show': the argument types match more than one overload
  assert 1 == 1
};

procedure inMap<U>(m: Box<Map<int, U>>)
  opaque
{
  var y: Map<int, U> := m#put(5);
//                            ^ error: cannot pass 'int' as the 'Map<int, U>' parameter of 'put'
  assert 1 == 1
};
#end

/-! The same at a gradual type argument, here a frontend's `Any`. `m`'s `Pair<U, int>` stays
against a less precise `Pair<Any, Any>`, and against a `Pair<int, Any>`, which is neither more nor
less precise. A more precise `Pair<bool, int>` replaces a receiver's `Pair<Any, int>`. -/

#eval testLaurelResolution (gradualTypes := ({} : Std.HashSet String).insert "Any") <|
#strata
program Laurel;
composite Any { }
composite Pair<A, B> {
  var a: A
  var b: B
}
composite Box<T> {
  var v: T
  procedure pair<V>(self: Box<T>, a: T, c: T, b: V)
    returns (r: T)
    opaque
    ensures r == a
  { r := a };
}

procedure gradualReceiver()
  opaque
{
  var b: Box<Any> := new Box<Any>;
  var p: Any := b#pair(1, 2, 5);
  var q: Any := b#pair(1, true, 5);
//              ^^^^^^^^^^^^^^^^^^ error: cannot infer type argument 'T' of 'pair': 'int' and 'bool' disagree
  assert 1 == 1
};

procedure gradualArgument<U>(m: Box<Pair<U, int>>, x: Pair<Any, Any>)
  opaque
{
  var y: Pair<bool, bool> := m#pair(x, x, 5);
//                           ^^^^^^^^^^^^^^^ error: expected 'Pair<bool, bool>', got 'Pair<U, int>'
  assert 1 == 1
};

procedure gradualInstantiation<U>(m: Box<Pair<U, int>>, x: Pair<int, Any>)
  opaque
{
  var y: Pair<int, bool> := m#pair(x, x, 5);
//                          ^^^^^^^^^^^^^^^ error: expected 'Pair<int, bool>', got 'Pair<U, int>'
  assert 1 == 1
};

procedure gradualReceiverPart(m: Box<Pair<Any, int>>, x: Pair<bool, int>)
  opaque
{
  var y: Pair<int, int> := m#pair(x, x, 5);
//                         ^^^^^^^^^^^^^^^ error: expected 'Pair<int, int>', got 'Pair<bool, int>'
  assert 1 == 1
};
#end

/-! ## In a static call, an instance call's inferred type reaches only the arguments after it

`bs#put(s)` is a `Set<int>`, so `same2`'s `U` is determined and `setEmpty()` after it typed, but
not one before it: after the lift `Box$put(bs, s)` is a deferred argument, resolved after it. What
an instance call's declared result says before inference types those before it too, here through
methods `SubBox` inherits: all of `getSet`'s `Set<int>`, and the `int` of `getMap`'s
`Map<int, T>`. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Box<T> {
  var v: T
  procedure put(self: Box<T>, a: T)
    returns (r: T)
    opaque
    ensures r == a
  { r := a };
  procedure getSet(self: Box<T>)
    returns (r: Set<int>)
    opaque
    ensures true;
  procedure getMap(self: Box<T>)
    returns (r: Map<int, T>)
    opaque
    ensures true;
}
composite SubBox<T> extends Box<T> { var w: int }
procedure same2<U>(x: U, y: U)
  opaque
  ensures true;
procedure pick<U>(x: U, y: U)
  returns (r: U)
  opaque
  ensures r == x
{ r := x };
procedure mkThing<A>()
  returns (r: A)
  opaque
  ensures true;
procedure keyOf<K>(k: K, m: Map<K, bool>)
  returns (r: K)
  opaque
  ensures r == k
{ r := k };

procedure instanceCallsInAStaticCall(s: Set<int>)
  opaque
{
  var bs: Box<Set<int>> := new Box<Set<int>>;
  same2(bs#put(s), setEmpty());
  same2(setEmpty(), bs#put(s));
//      ^^^^^^^^^^ error: cannot infer type argument 'T' of 'setEmpty'
  var sb: SubBox<bool> := new SubBox<bool>;
  var n := pick(setEmpty(), sb#getSet());
  var k := keyOf(mkThing(), sb#getMap());
  assert 1 == 1
};
#end

/-! ## An unresolved receiver is the only error

With no composite to look the method up in, the call falls back to the bare name, here a generic
procedure that nothing determines; nothing is inferred for it. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure mk<V>()
  returns (r: V)
  opaque
  ensures true;

procedure unresolvedReceiver()
  opaque
{
  var x := nope#mk();
//         ^^^^ error: Resolution failed: 'nope' is not defined
  assert 1 == 1
};
#end
