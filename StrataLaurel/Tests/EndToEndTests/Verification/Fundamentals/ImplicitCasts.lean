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
datatype Meters { MkMeters(m: int) }
procedure fromInt(x: int) : Meters
  implicit
  return MkMeters(x);
procedure toInt(d: Meters) : int
  requires Meters..m!(d) >= 0 summary "the distance is not negative"
  implicit
  return Meters..m!(d);
procedure twice(d: Meters) returns (r: Meters)
  opaque
  ensures Meters..m!(r) == 2 * Meters..m!(d)
{
  return MkMeters(2 * Meters..m!(d))
};
procedure useCasts() opaque {
  var d: Meters := twice(21);
  assert Meters..m!(d) == 42;
  var n: int := d;
  assert n == 42;
  var neg: int := MkMeters(-1)
//                ^^^^^^^^^^^^ error: the distance is not negative does not hold
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
procedure twoInputs(x: int, y: int) : bool
//        ^^^^^^^^^ error: implicit procedure 'twoInputs' must take one input and return one output
  implicit
  return x == y;
#end

#eval testLaurelVerification <|
#strata
program Laurel;
procedure f(x: int) returns (r: int) opaque ensures r == 1 { return 1 };
procedure f(x: NullableRef<int>) returns (r: int) opaque ensures r == 2 { return 2 };
procedure caller() opaque {
  var a: int := f(3);
  assert a == 1;
  var n: NullableRef<int> := Null();
  var b: int := f(n);
  assert b == 2
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C {
  var v: int
  procedure toInt(self: C) : int
//          ^^^^^ error: implicit procedure 'toInt' must be a static procedure, not a procedure of 'C'
    implicit
    return self#v;
}
#end

#eval testLaurelVerification <|
#strata
program Laurel;
procedure badFrame(x: int) : int
//        ^^^^^^^^ error: frame procedure 'badFrame' must take one input and return one output whose type is a composite or a Set of composites
  frame
  return x;
#end

#eval testLaurelVerification <|
#strata
program Laurel;
datatype Meters { MkMeters(m: int) }
procedure castA(x: int) : Meters implicit return MkMeters(x);
procedure castB(x: int) : Meters implicit return MkMeters(x + 1);
procedure use() opaque {
  var d: Meters := 5;
//                 ^ error: ambiguous implicit conversion from 'int' to 'Meters': 'castA' and 'castB' both apply
  assert Meters..m!(d) == 5
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
procedure conv(x: bool) : int
  implicit
  return if x then 1 else 0;
procedure conv(x: real) : int
//        ^^^^ error: implicit procedure 'conv' is declared more than once; implicit procedures must have distinct names
  implicit
  return 2;
procedure use() opaque {
  var n: int := true;
  assert n == 1
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var x: int }
procedure xOf(c: C) : int
  implicit
  return c#x;
procedure useHeapReadingCast(c: C)
  requires c#x == 5
  opaque
{
  var n: int := c;
  assert n == 5
};
#end
