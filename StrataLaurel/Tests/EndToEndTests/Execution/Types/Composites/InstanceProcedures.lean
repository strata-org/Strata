/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
/-
Tests for the `obj#method(args)` syntax for calling instance procedures.

Each instance procedure declared inside a `composite` block is lifted to a
top-level static procedure named `<CompositeName>$<methodName>` by the
`LiftInstanceProcedures` pass. Resolution registers the instance proc in
global scope under the lifted key, so two composites can share a method
name without colliding. `c#m(args)` parses as `InstanceCall c m args` and
the lifting pass rewrites it to `StaticCall Counter$m (c :: args)`.
-/

meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## 1. Basic instance method call: `c#reset()` -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Counter {
  var count: int
  procedure reset(self: Counter)
    opaque
    ensures self#count == 0
    modifies self
  {
    self#count := 0
  };
}

procedure useCounter()
  opaque
{
  var c: Counter := new Counter;
  c#reset();
  assert c#count == 0
};

procedure runAll() entry
  opaque
  modifies *
{
  useCounter()
};
#end

/-! ## 2. Two composites with the same method name resolve independently.
    Without per-composite scoping, `tick` would collide in the global scope
    during pre-registration. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Counter {
  var count: int
  procedure tick(self: Counter)
    opaque
    ensures self#count == 1
    modifies self
  {
    self#count := 1
  };
}

composite Clock {
  var time: int
  procedure tick(self: Clock)
    opaque
    ensures self#time == 1
    modifies self
  {
    self#time := 1
  };
}

procedure runCounter()
  opaque
{
  var c: Counter := new Counter;
  c#tick();
  assert c#count == 1
};

procedure runClock()
  opaque
{
  var k: Clock := new Clock;
  k#tick();
  assert k#time == 1
};

procedure runAll() entry
  opaque
  modifies *
{
  runCounter();
  runClock()
};
#end

/-! ## 3. Method with multiple parameters: `c#setTo(v)` -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Cell {
  var value: int
  procedure setTo(self: Cell, v: int)
    opaque
    ensures self#value == v
    modifies self
  {
    self#value := v
  };
}

procedure useCell(x: int)
  opaque
{
  var b: Cell := new Cell;
  b#setTo(x);
  assert b#value == x
};

procedure runAll() entry
  opaque
  modifies *
{
  useCell(7)
};
#end

/-! ## 4. Boolean-typed field updated through an instance method, and read
    back via field access in the caller's `assert`. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Widget {
  var enabled: bool
  procedure activate(self: Widget)
    opaque
    ensures self#enabled
    modifies self
  {
    self#enabled := true
  };
}

procedure useWidget()
  opaque
{
  var w: Widget := new Widget;
  w#activate();
  assert w#enabled == true
};

procedure runAll() entry
  opaque
  modifies *
{
  useWidget()
};
#end

/-! ## 5. Calling an instance method from a top-level procedure that takes
    the receiver as a parameter. The caller's own modifies clause covers
    only `a`; the unused `b` parameter is included to confirm method
    dispatch picks the right receiver. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Counter {
  var count: int
  procedure reset(self: Counter)
    opaque
    ensures self#count == 0
    modifies self
  {
    self#count := 0
  };
}

procedure resetTwoCounters(a: Counter, b: Counter)
  opaque
  ensures a#count == 0
  modifies a
{
  a#reset()
};

procedure runAll() entry
  opaque
  modifies *
{
  var a: Counter := new Counter;
  var b: Counter := new Counter;
  resetTwoCounters(a, b)
};
#end

/-! ## 6. Instance method whose extra parameter is unused in the body:
    confirms an extra (unused) method parameter doesn't break call
    dispatch or framing. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Account {
  var balance: int
  procedure deposit(self: Account, amount: int)
    opaque
    ensures self#balance == 1
    modifies self
  {
    self#balance := 1
  };
}

procedure useAccount()
  opaque
{
  var a: Account := new Account;
  a#deposit(100);
  assert a#balance == 1
};

procedure runAll() entry
  opaque
  modifies *
{
  useAccount()
};
#end

/-! ## 7. Instance method called through a field-selected receiver:
    `obj#field#method()`. -/

-- No interpreters: `o#inner` is never written, so a concrete run reads an unset field.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Inner {
  var x: int
  procedure isOne(self: Inner) returns (r: bool)
    opaque
    ensures r == (self#x == 1)
  ;
}

composite Outer {
  var inner: Inner
}

procedure useOuter()
  opaque
{
  var o: Outer := new Outer;
  var b: bool := o#inner#isOne()
};
#end

/-! ## 8. Chained field read: `obj#field#x`. -/

-- No interpreters: `o#inner` is never written, so a concrete run reads an unset field.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Inner { var x: int }
composite Outer { var inner: Inner }

procedure useOuter()
  opaque
{
  var o: Outer := new Outer;
  var v: int := o#inner#x
};
#end

/-! ## Instance methods on a GENERIC composite

A method on `Box<T>` is lifted by `liftInstanceProceduresPass` to a top-level POLYMORPHIC
procedure carrying the composite's type parameters (`Box$get<T>(self: Box<T>)`), and the
procedure monomorphizer then clones it per call-site instantiation. So generic methods reuse
the procedure-monomorphization machinery rather than introducing a second mechanism — the
lift runs BEFORE monomorphization for exactly that reason.

What that leaves to check: the clone's `self#val` reads the clone's field (not the generic
declaration's `T`-typed one), two instantiations get independent clones, and the method's
contract is still checked at each clone rather than dropped by the lift. A method may also
declare its OWN type parameter, in which case the lift has to carry both lists — the
composite's and the method's.

Every block from here on marks an `entry`, so the clone is also CALLED: `self#val` is read
concretely through the monomorphized method and the negative cases' contract failures are
reproduced at runtime. Those that skip an interpreter say why at the block. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite BoxM<T> {
  var val: T
  procedure get(self: BoxM<T>) returns (r: T)
    opaque
    ensures r == self#val
  { r := self#val };
}

procedure genericMethodRead()
  entry
  opaque
  modifies *
{
  var bx: BoxM<int> := new BoxM<int>;
  bx#val := 7;
  var got: int := bx#get();
  assert got == 7
};

// Two instantiations: each clone reads its own field, at its own type.
procedure genericMethodTwoInstantiations()
  entry
  opaque
  modifies *
{
  var bi: BoxM<int> := new BoxM<int>;
  bi#val := 7;
  var gi: int := bi#get();
  var bb: BoxM<bool> := new BoxM<bool>;
  bb#val := true;
  var gb: bool := bb#get();
  assert gi == 7 && gb == true
};
#end

-- SOUNDNESS twin: the value the method returns is the field's, so a false claim must fail.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite BoxM<T> {
  var val: T
  procedure get(self: BoxM<T>) returns (r: T)
    opaque
    ensures r == self#val
  { r := self#val };
}

procedure genericMethodReadFalse()
  entry
  opaque
  modifies *
{
  var bx: BoxM<int> := new BoxM<int>;
  bx#val := 7;
  var got: int := bx#get();
  assert got == 8
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- The method's own CONTRACT survives the lift: a false `ensures` has to fail at the clone.
-- The caller asserts only `1 == 1`, so the single failure is the method's body VC.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite BoxB<T> {
  var val: T
  procedure bad(self: BoxB<T>) returns (r: int)
    opaque
    ensures r == 0
//          ^^^^^^ error: postcondition does not hold
  { r := 1 };
}

procedure genericMethodFalsePostcondition()
  entry
  opaque
  modifies *
{
  var bx: BoxB<int> := new BoxB<int>;
  var g: int := bx#bad();
  assert 1 == 1
};
#end

-- And the method's PRECONDITION still gates the call: the caller writes 5 where the method
-- requires 7, so the precondition VC at the call site is the one that fails.
-- The Core interpreter runs this and reproduces the failure at the annotated range. The
-- STANDALONE Laurel interpreter is skipped because it localizes the same failure differently:
-- it reports the call expression `bx#get7()` (snippet cols 16-25) where the verifier and the
-- Core interpreter both report the whole declaration statement (cols 2-25), and one
-- annotation cannot pin both ranges.
#eval testLaurelExecution { skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite BoxP<T> {
  var val: T
  procedure get7(self: BoxP<T>) returns (r: T)
    requires self#val == 7
    opaque
    ensures r == self#val
  { r := self#val };
}

procedure genericMethodPreconditionGated()
  entry
  opaque
  modifies *
{
  var bx: BoxP<int> := new BoxP<int>;
  bx#val := 5;
  var g: int := bx#get7();
//^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
  assert 1 == 1
};
#end

/-! ### A method with its OWN type parameter

`id2<U>` on `BoxU<T>` has a type parameter of its own, independent of the composite's. The
lift carries both lists, so the monomorphizer sees `BoxU$id2<T, U>` and instantiates `U`
from the ARGUMENT at each call while `T` comes from the receiver. Calling it at two
different `U`s from one receiver is what separates the two. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite BoxU<T> {
  var v: T
  procedure id2<U>(self: BoxU<T>, x: U) returns (r: U)
    opaque
    ensures r == x
  { r := x };
}

procedure methodOwnTypeParam()
  entry
  opaque
  modifies *
{
  var b: BoxU<int> := new BoxU<int>;
  var y: bool := b#id2(true);
  assert y == true
};

// One receiver, two different `U` instantiations of the same method.
procedure methodOwnTypeParamTwoInstantiations()
  entry
  opaque
  modifies *
{
  var b: BoxU<int> := new BoxU<int>;
  var p: int := b#id2(7);
  var q: bool := b#id2(false);
  assert p == 7 && q == false
};
#end

-- SOUNDNESS twin: a false `ensures` on a method-own-type-parameter method must fail too.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite BoxW<T> {
  var v: T
  procedure bad<U>(self: BoxW<T>, x: U) returns (r: int)
    opaque
    ensures r == 0
//          ^^^^^^ error: postcondition does not hold
  { r := 1 };
}

procedure methodOwnTypeParamFalsePostcondition()
  entry
  opaque
  modifies *
{
  var b: BoxW<int> := new BoxW<int>;
  var z: int := b#bad(true);
  assert 1 == 1
};
#end

-- A method's own type parameter cannot reuse its composite's name. The clash is reported by the
-- re-resolution after `LiftInstanceProcedures`, where both stand in one type-parameter list, not
-- by the first resolution. No interpreters: each words the clash its own way
-- (`interpret: Laurel→Core failed: …`), which one annotation cannot pin.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite BoxC<T> {
  var v: T
  procedure f<T>(self: BoxC<T>, x: T)
//            ^ error: Duplicate definition 'T' is already defined in this scope
    returns (r: T)
    opaque
    ensures r == x
  { r := x };
}

procedure methodTypeParamSpelledLikeTheComposites()
  entry
  opaque
  modifies *
{
  var b: BoxC<int> := new BoxC<int>;
  var z: bool := b#f(true);
  assert 1 == 1
};
#end

/-! ### Type arguments the receiver brings in

`b#m(5)` in `outer<U>` instantiates `m`'s `T` at the caller's `U`, which `m`'s own `U` must not
capture; likewise the composite `E` and `n`'s own `E`. Inside the composite, a call on `self` is
at its own type parameters. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite E { var k: int }
composite BoxR<T> {
  var v: T
  procedure m<U>(self: BoxR<T>, x: U)
    returns (r: T)
    opaque
    ensures r == self#v
  { r := self#v };
  procedure n<E>(self: BoxR<T>, x: E)
    returns (r: T)
    opaque
    ensures r == self#v
  { r := self#v };
  procedure idu<U>(self: BoxR<T>, x: U)
    returns (r: U)
    opaque
    ensures r == x
  { r := x };
  procedure viaSelf<W>(self: BoxR<T>, w: W)
    returns (r: W)
    opaque
    ensures r == w
  { r := self#idu(w) };
  procedure getV(self: BoxR<T>)
    returns (r: T)
    opaque
    ensures r == self#v
  { r := self#idu(self#v) };
}

procedure outer<U>(b: BoxR<U>)
  opaque
{
  var z: bool := b#m(5);
  assert 1 == 1
};

procedure receiverTypesAreNotCaptured()
  entry
  opaque
  modifies *
{
  var bb: BoxR<bool> := new BoxR<bool>;
  bb#v := true;
  outer(bb);
  var be: BoxR<E> := new BoxR<E>;
  var e: E := new E;
  be#v := e;
  var y: E := be#n(5);
  var bi: BoxR<int> := new BoxR<int>;
  bi#v := 3;
  var w: bool := bi#viaSelf(true);
  var g: int := bi#getV();
  assert w == true && g == 3
};
#end

/-! ### A receiver's type argument in the caller's type parameter

`b#put(x)` in `inCell<U>` passes a `Cell<int>` at the receiver's `T := Cell<U>`, as the static call
the lift makes does, and runs at `U := int`. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Cell<X> { var c: X }
composite BoxN<T> {
  var v: T
  procedure put(self: BoxN<T>, a: T)
    returns (r: T)
    opaque
    ensures r == a
  { r := a };
}

procedure inCell<U>(b: BoxN<Cell<U>>, x: Cell<int>)
  returns (r: Cell<int>)
  opaque
  ensures r == x
{ r := b#put(x) };

procedure receiverInstantiatedByTheArgument()
  entry
  opaque
  modifies *
{
  var b: BoxN<Cell<int>> := new BoxN<Cell<int>>;
  var x: Cell<int> := new Cell<int>;
  x#c := 4;
  var r: Cell<int> := inCell(b, x);
  assert r#c == 4
};
#end

/-! ### An argument is resolved against its instantiated parameter

So a generic call in argument position, also inside an `if` or a block, takes its type argument
from the slot, whether the receiver, a sibling argument, a later sibling call's declared result or
the expected type fixes it. -/

-- No standalone Laurel interpreter: it has no backend for the external `setEmpty`.
#eval testLaurelExecution { skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite BoxS<T> {
  var v: T
  procedure take(self: BoxS<T>, a: T)
    opaque
    ensures true
  { };
  procedure mix<U>(self: BoxS<T>, a: T, b: U)
    returns (r: T)
    opaque
    ensures r == a
  { r := a };
  procedure same<U>(self: BoxS<T>, x: U, y: U)
    opaque
    ensures true
  { };
  procedure choose<U>(self: BoxS<T>, x: U, y: U)
    returns (r: U)
    opaque
    ensures r == x
  { r := x };
  procedure getSet(self: BoxS<T>)
    returns (r: Set<int>)
    opaque
    ensures true
  { r := setEmpty() };
}
composite Holder {
  var k: int
  procedure mkEmpty<V>(self: Holder)
    returns (r: Set<V>)
    opaque
    ensures true
  { r := setEmpty() };
  procedure getS(self: Holder)
    returns (r: Set<int>)
    opaque
    ensures true
  { r := setEmpty() };
}
procedure same2<U>(x: U, y: U)
  opaque
  ensures true
{ };

procedure slotsOfNestedGenericCalls()
  entry
  opaque
  modifies *
{
  var h: Holder := new Holder;
  var s: Set<int> := setEmpty();
  var c: bool := true;
  var bs: BoxS<Set<int>> := new BoxS<Set<int>>;
  bs#take(setEmpty());
  bs#take(if c then setEmpty() else s);
  bs#take({ var n: int := 1; setEmpty() });
  var m := bs#mix(setEmpty(), 5);
  bs#same(setEmpty(), s);
  bs#same(bs#getSet(), setEmpty());
  bs#same(setEmpty(), h#getS());
  same2(setEmpty(), h#getS());
  bs#same(h#mkEmpty(), s);
  same2(h#mkEmpty(), s);
  var e: Set<int> := bs#choose(setEmpty(), setEmpty());
  assert 1 == 1
};
#end

/-! ### An argument to a parameter without type variables is checked against it

As for a non-generic method, so the `if` joins its branches at the `Animal` the parameter
declares. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Animal { var a: int }
composite Dog extends Animal { var d: int }
composite Cat extends Animal { var k: int }
composite BoxA<T> {
  var v: T
  procedure feed(self: BoxA<T>, x: Animal)
    opaque
    ensures true
  { };
}

procedure checkedArgument()
  entry
  opaque
  modifies *
{
  var b: BoxA<int> := new BoxA<int>;
  var c: bool := true;
  var dog: Dog := new Dog;
  var cat: Cat := new Cat;
  b#feed(if c then dog else cat);
  assert 1 == 1
};
#end
