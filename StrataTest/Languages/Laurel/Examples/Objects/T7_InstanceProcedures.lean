/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests for the `obj#method(args)` syntax for calling instance procedures.

Each instance procedure declared inside a `composite` block is lifted to a
top-level static procedure named `<CompositeName>$<methodName>` by the
`LiftInstanceProcedures` pass. Resolution registers the instance proc in
global scope under the lifted key, so two composites can share a method
name without colliding. `c#m(args)` parses as `InstanceCall c m args` and
the lifting pass rewrites it to `StaticCall Counter$m (c :: args)`.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## 1. Basic instance method call: `c#reset()` -/

#eval testLaurel <|
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
#end

/-! ## 2. Two composites with the same method name resolve independently.
    Without per-composite scoping, `tick` would collide in the global scope
    during pre-registration. -/

#eval testLaurel <|
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
#end

/-! ## 3. Method with multiple parameters: `c#setTo(v)` -/

#eval testLaurel <|
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
#end

/-! ## 4. Boolean-typed field updated through an instance method, and read
    back via field access in the caller's `assert`. -/

#eval testLaurel <|
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
#end

/-! ## 5. Calling an instance method from a top-level procedure that takes
    the receiver as a parameter. The caller's own modifies clause covers
    only `a`; the unused `b` parameter is included to confirm method
    dispatch picks the right receiver. -/

#eval testLaurel <|
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
#end

/-! ## 6. Instance method whose extra parameter is unused in the body:
    confirms an extra (unused) method parameter doesn't break call
    dispatch or framing. -/

#eval testLaurel <|
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
#end

/-! ## 7. Instance method called through a field-selected receiver:
    `obj#field#method()`. -/

#eval testLaurel <|
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

#eval testLaurel <|
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
