/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
/-
Tests which receivers BindFieldReceivers binds, by comparing its output against expected Laurel.

Uses `runPassForIdiomaticity`, the shared idiomaticity driver: parse, resolve, run
`bindFieldReceiversPass`, print the result for the `#guard_msgs` golden.
-/

meta import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.BindFieldReceivers

open Strata
open StrataTest.Util

namespace Strata.Laurel

/- An update operator's receiver stays like a store's, unless it has an effect. -/
/--
info: composite Box { var b: bool var g: int var r: Box }
procedure setB(q: Box)
  opaque
  ensures q#b
  modifies q
{
  q#b := true
};
procedure updateOperators(x: Box)
  opaque
  modifies x
{
  x#r#g++;
  x#r#g += 1;
  var $receiver0: Box := {
    setB(x);
    x
  };
  $receiver0#g++
};
-/
#guard_msgs in
#eval runPassForIdiomaticity bindFieldReceiversPass <|
#strata
program Laurel;
composite Box {
  var b: bool
  var g: int
  var r: Box
}
procedure setB(q: Box)
  opaque
  ensures q#b
  modifies q
{
  q#b := true
};
procedure updateOperators(x: Box)
  opaque
  modifies x
{
  x#r#g++;
  x#r#g += 1;
  { setB(x); x }#g++
};
#end

/- A call in a store's value changes the globals its callee writes, and every field if the callee
   writes the heap: `setB` changes no local and `noop` nothing. -/
/--
info: composite Box { var b: bool var g: int var r: Box }
 var gb: Box
procedure setB(q: Box)
  opaque
  ensures q#b
  modifies q
{
  q#b := true
};
procedure setGb(q: Box)
  opaque
  ensures gb == q
{
  gb := q
};
procedure noop()
  opaque
{

};
procedure calls(x: Box, y: Box)
  opaque
  modifies x, y
{
  x#r#g := {
    noop();
    1
  };
  x#g := {
    setB(y);
    2
  };
  var $receiver0: Box := x#r;
  $receiver0#g := {
    setB(y);
    3
  };
  x#g := {
    setGb(y);
    4
  };
  gb#g := {
    noop();
    5
  };
  var $receiver1: Box := gb;
  $receiver1#g := {
    setGb(y);
    6
  }
};
-/
#guard_msgs in
#eval runPassForIdiomaticity bindFieldReceiversPass <|
#strata
program Laurel;
composite Box {
  var b: bool
  var g: int
  var r: Box
}
var gb: Box := <?>
procedure setB(q: Box)
  opaque
  ensures q#b
  modifies q
{
  q#b := true
};
procedure setGb(q: Box)
  opaque
  ensures gb == q
{
  gb := q
};
procedure noop()
  opaque
{
};
procedure calls(x: Box, y: Box)
  opaque
  modifies x, y
{
  x#r#g := { noop(); 1 };
  x#g := { setB(y); 2 };
  x#r#g := { setB(y); 3 };
  x#g := { setGb(y); 4 };
  gb#g := { noop(); 5 };
  gb#g := { setGb(y); 6 }
};
#end

/- A read's receiver stays only where it reads nothing but locals and fields: `x#r` stays, while a
   call is bound, even to the transparent `pick`. -/
/--
info: composite Box { var g: int var r: Box }
procedure pick(q: Box)
  returns (p: Box)
{
  q
};
procedure fieldReads(x: Box)
  opaque
{
  var a: int := x#r#g;
  var b: int := {
    var $receiver0: Box := pick(x);
    $receiver0#g
  }
};
-/
#guard_msgs in
#eval runPassForIdiomaticity bindFieldReceiversPass <|
#strata
program Laurel;
composite Box {
  var g: int
  var r: Box
}
procedure pick(q: Box) returns (p: Box)
{
  q
};
procedure fieldReads(x: Box)
  opaque
{
  var a: int := x#r#g;
  var b: int := pick(x)#g
};
#end

/- A `yield` may change any global: a store's receiver that reads one is bound where the value
   yields. -/
/--
info: composite Box { var g: int }
 var gb: Box
procedure storer()
  opaque
  modifies *
{
  v := 0;
  var $receiver0: Box := gb;
  $receiver0#g := {
    yield;
    5
  }
};
-/
#guard_msgs in
#eval runPassForIdiomaticity bindFieldReceiversPass <|
#strata
program Laurel;
composite Box {
  var g: int
}
var gb: Box := <?>
coroutine storer() yields (v: int)
  modifies *
{
  v := 0;
  gb#g := { yield; 5 }
};
#end

/- Nothing in a loop's condition is bound, though `pick(x)` would be elsewhere; its body is, as
   anywhere else. -/
/--
info: composite Box { var g: int }
procedure pick(q: Box)
  returns (p: Box)
{
  q
};
procedure loops(x: Box, y: Box)
  opaque
  modifies x, y
{
  while(pick(x)#g > 0) {
    var $receiver0: Box := x;
    $receiver0#g := {
      x := y;
      0
    }
  }
};
-/
#guard_msgs in
#eval runPassForIdiomaticity bindFieldReceiversPass <|
#strata
program Laurel;
composite Box {
  var g: int
}
procedure pick(q: Box) returns (p: Box)
{
  q
};
procedure loops(x: Box, y: Box)
  opaque
  modifies x, y
{
  while (pick(x)#g > 0) {
    x#g := { x := y; 0 }
  }
};
#end
