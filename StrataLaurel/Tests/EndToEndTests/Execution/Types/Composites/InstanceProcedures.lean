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
reproduced at runtime. One of them runs the Core interpreter only, for a localization reason
it states at the block. -/

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
