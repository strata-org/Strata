/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Comprehensive tests for **value-returning instance procedures** (methods
declared inside a `composite` block that return a value via a `return expr`
statement in their body).

These exercise the interaction between the `EliminateValueInReturns` pass and
the `LiftInstanceProcedures` pass. `EliminateValueInReturns` rewrites
`return expr` into `outParam := expr; return`, and it must do so for instance
procedures *while they still live inside their composite* (it runs before
`LiftInstanceProcedures` lifts them to static scope). If it skipped instance
procedures, the leftover `return expr` would later trip a `StrataBug` during
Core translation.

Positive cases below all verify cleanly (no diagnostics). Negative cases pin
the diagnostics emitted by `EliminateValueInReturns` for unsupported valued
returns, proving the pass now reaches instance procedures.

See also `T7_InstanceProcedures.lean` for the surface-syntax / call-dispatch
tests of `obj#method(args)`.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## 1. Basic: instance method body returns a field via `return expr`. -/

#eval testLaurel <|
#strata
program Laurel;
composite Num {
  var v: int
  procedure get(self: Num) returns (r: int)
    opaque
    ensures r == self#v
  {
    return self#v
  };
}

procedure useGet()
  opaque
{
  var b: Num := new Num;
  var x: int := b#get();
  assert x == b#v
};
#end

/-! ## 2. Return a computed expression. -/

#eval testLaurel <|
#strata
program Laurel;
composite Num {
  var v: int
  procedure incd(self: Num) returns (r: int)
    opaque
    ensures r == self#v + 1
  {
    return self#v + 1
  };
}

procedure useIncd()
  opaque
{
  var b: Num := new Num;
  var x: int := b#incd();
  assert x == b#v + 1
};
#end

/-! ## 3. Return an expression that uses a (non-self) parameter. -/

#eval testLaurel <|
#strata
program Laurel;
composite Num {
  var v: int
  procedure addTo(self: Num, d: int) returns (r: int)
    opaque
    ensures r == self#v + d
  {
    return self#v + d
  };
}

procedure useAddTo()
  opaque
{
  var b: Num := new Num;
  var x: int := b#addTo(5);
  assert x == b#v + 5
};
#end

/-! ## 4. Conditional / early returns: a valued `return` in each branch of an
    if-then-else inside the method body. -/

#eval testLaurel <|
#strata
program Laurel;
composite Num {
  var v: int
  procedure clampPos(self: Num) returns (r: int)
    opaque
    ensures r >= 0
  {
    if self#v >= 0 then {
      return self#v
    } else {
      return 0
    }
  };
}

procedure useClampPos()
  opaque
{
  var b: Num := new Num;
  var x: int := b#clampPos();
  assert x >= 0
};
#end

/-! ## 5. Method that mutates a field (modifies clause) and then returns. -/

#eval testLaurel <|
#strata
program Laurel;
composite Num {
  var v: int
  procedure setAndGet(self: Num, n: int) returns (r: int)
    opaque
    ensures self#v == n
    ensures r == n
    modifies self
  {
    self#v := n;
    return n
  };
}

procedure useSetAndGet()
  opaque
{
  var b: Num := new Num;
  var x: int := b#setAndGet(7);
  assert x == 7;
  assert b#v == 7
};
#end

/-! ## 6. Boolean return type. -/

#eval testLaurel <|
#strata
program Laurel;
composite Num {
  var v: int
  procedure isPos(self: Num) returns (r: bool)
    opaque
    ensures r == (self#v > 0)
  {
    return self#v > 0
  };
}

procedure useIsPos()
  opaque
{
  var b: Num := new Num;
  var p: bool := b#isPos();
  assert p == (b#v > 0)
};
#end

/-! ## 7. Two composites sharing a method name, both with value-returning
    bodies. Confirms lifting + value-return elimination keep them distinct. -/

#eval testLaurel <|
#strata
program Laurel;
composite A {
  var v: int
  procedure read(self: A) returns (r: int)
    opaque
    ensures r == self#v
  {
    return self#v
  };
}

composite B {
  var w: int
  procedure read(self: B) returns (r: int)
    opaque
    ensures r == self#w
  {
    return self#w
  };
}

procedure useBoth()
  opaque
{
  var a: A := new A;
  var b: B := new B;
  var x: int := a#read();
  var y: int := b#read();
  assert x == a#v;
  assert y == b#w
};
#end

/-! ## 8. Value-returning method invoked through a field-selected receiver:
    `o#inner#getX()`. -/

#eval testLaurel <|
#strata
program Laurel;
composite Inner {
  var x: int
  procedure getX(self: Inner) returns (r: int)
    opaque
    ensures r == self#x
  {
    return self#x
  };
}

composite Outer {
  var inner: Inner
}

procedure useOuter()
  opaque
{
  var o: Outer := new Outer;
  var v: int := o#inner#getX();
  assert v == o#inner#x
};
#end

/-! ## 9. Local variable in the body before a valued return. -/

#eval testLaurel <|
#strata
program Laurel;
composite Num {
  var v: int
  procedure doubleV(self: Num) returns (r: int)
    opaque
    ensures r == self#v + self#v
  {
    var t: int := self#v;
    return t + t
  };
}

procedure useDoubleV()
  opaque
{
  var b: Num := new Num;
  var x: int := b#doubleV();
  assert x == b#v + b#v
};
#end

/-! ## 10. Negative: valued return in an instance method with NO output
    parameter is rejected by `EliminateValueInReturns`. -/

#eval testLaurel <|
#strata
program Laurel;
composite C {
  var v: int
  procedure noOut(self: C)
    opaque
  {
    return 5
//  ^^^^^^^^ error: void procedure cannot return a value
  };
}
#end

/-! ## 11. Negative: valued return in an instance method with MULTIPLE output
    parameters is rejected by `EliminateValueInReturns`. -/

#eval testLaurel <|
#strata
program Laurel;
composite D {
  var v: int
  procedure twoOut(self: D) returns (a: int, b: int)
    opaque
  {
    return 1
//  ^^^^^^^^  error: multi-output procedure cannot use 'return e'; assign to named outputs instead
  };
}
#end
