/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testCortexVerification <|
#strata
program Laurel;
procedure inc(x: int) returns (r: int)
  opaque
{
    r := x + 1
};

procedure loops()
  opaque
{
    var i: int := 0;
    {
        if i >= 10 then { exit loop };
        i := inc(i);
        goto loop
    } loop;
    var x: int := 5;
    var result: int := 0;
    if x == 5 then { result := 10 } else { result := 20 };
    assert result == 10;
    assert result == 11
//  ^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#eval testCortexVerification <|
#strata
program Laurel;
composite Exn { var code: int }
composite IOExn extends Exn { }
composite Other extends Exn { }
composite Node { var value: int }
constrained pos = x: int where x > 0 witness 1

procedure heapAndExceptions(p: Node)
  opaque
  modifies *
{
    var a: Node := new Node;
    var b: Node := new Node;
    a#value := 3;
    b#value := 4;
    a#value := 7;
    p#value := 9;
    assert a#value == 7 && b#value == 4;
    assert a is Node;
    var caught: int := 0;
    try {
      var x: IOExn := new IOExn;
      x#code := 5;
      throw x
    } catch err when err is Other {
      caught := 2
    } catch err2 {
      caught := 1;
      assert err2 is IOExn && err2#code == 5
    };
    var f: int := 0;
    try { f := 1 } finally { f := f + 10 };
    assert caught == 1 && f == 11;
    var q: pos := 1;
    q := q - 1
//  ^^^^^^^^^^ error: assertion does not hold
};

procedure uncaught()
  opaque
{
    var e: Exn := new Exn;
    throw e
//  ^^^^^^^ error: uncaught exception 'Exn' is not thrown does not hold
};
#end

#eval testCortexVerification <|
#strata
program Laurel;
composite Animal { var age: int }
composite Dog extends Animal { }
composite Cat extends Animal { }

procedure declaredTypePinsTag(d: Dog, a: Animal)
  opaque
{
    assert d is Dog;
    assert d is Animal;
    assert a is Dog
//  ^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure downcast(a: Animal) returns (r: Dog)
  opaque
{
    r := a as Dog
//       ^^^^^^^^ error: assertion does not hold
};
#end
