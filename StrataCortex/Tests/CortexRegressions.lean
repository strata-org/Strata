/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExecution { skipVerification := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
composite Exn { var code: int }
constrained pos = x: int where x > 0 witness 1

procedure alwaysThrows() returns (r: int)
  throws (e: Exn)
  opaque
{
    r := 0 - 5;
    var ex: Exn := new Exn;
    throw ex
};

procedure main() entry
  opaque
  modifies *
{
    var x: int := 1;
    var r: int := x + x++;
    assert r == 2;
    { var t: int := 1; assert t == 1 };
    { var t: bool := true; assert t };
    var hit: int := 0;
    try { var q: pos := alwaysThrows() } catch err { hit := 1 };
    assert hit == 1
};
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
composite TypeTag { var x: int }
constrained pos = x: int where x > 0 witness 1

procedure evaluationOrder() entry
  opaque
{
    var x: int := 1;
    var r: int := x + x++;
    assert r == 2
};

procedure siblingScopes() entry
  opaque
{
    { var t: int := 1; assert t == 1 };
    { var t: bool := true; assert t }
};

procedure userTypeNamedTypeTag() entry
  opaque
  modifies *
{
    var f: TypeTag := new TypeTag;
    f#x := 1;
    assert f#x == 1
};
#end

#eval testLaurelExecution { skipVerification := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
constrained pos = x: int where x > 0 witness 1

procedure main() entry
  opaque
{
    var q: pos := 0 - 5
//  ^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
constrained pos = x: int where x > 0 witness 1

procedure main() entry
  opaque
{
    var q: pos;
    assert q > 0
};
#end

#eval testLaurelExecution { skipVerification := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
procedure main() entry
  opaque
{
    var d: int := 0;
    var x: int := 10;
    x /= d
//  ^^^^^^ error: divisor is non-zero does not hold
};
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
constrained even = x: int where x % 2 == 0 witness 0

procedure modInConstraint() entry
  opaque
{
    var e: even := 4;
    assert e % 2 == 0
};

procedure divInQuantifier()
  opaque
{
    var b: bool := forall(i: int) => i / 2 <= i / 2
};
#end

#eval testCortexTranslation <|
#strata
program Laurel;
procedure needsPos(x: int) returns (r: int)
//        ^^^^^^^^ not-yet-implemented: Cortex does not support the contract of procedure 'needsPos'
  requires x > 0
  opaque;

procedure caller()
  opaque
{
    var y: int := needsPos(0)
};
#end

#eval testCortexTranslation <|
#strata
program Laurel;
composite Node { var v: int }

procedure writesUnframed(n: Node)
//        ^^^^^^^^^^^^^^ not-yet-implemented: Cortex does not support the frame of procedure 'writesUnframed'
  opaque
{
    n#v := 3
};

procedure narrowFrame(n: Node, m: Node)
//        ^^^^^^^^^^^ not-yet-implemented: Cortex does not support the frame of procedure 'narrowFrame'
  opaque
  modifies m
{
    m#v := 3
};

procedure callsWildcard(n: Node)
//        ^^^^^^^^^^^^^ not-yet-implemented: Cortex does not support the frame of procedure 'callsWildcard'
  opaque
{
    wildcardFrame(n)
};

procedure wildcardFrame(n: Node)
  opaque
  modifies *
{
    n#v := 3
};
#end

#eval testCortexTranslation <|
#strata
program Laurel;
composite Err {}
procedure mk(e0: Err) throws (e: Err) opaque
//        ^^ not-yet-implemented: Cortex does not support the contract of procedure 'mk'
  throwsOn false { }
{ throw e0 };
#end

#eval testCortexTranslation <|
#strata
program Laurel;
composite Err {}
procedure mk(e0: Err) throws (e: Err) opaque
//        ^^ not-yet-implemented: Cortex does not support the contract of procedure 'mk'
  throwsOn true { ensures e == e0 }
{ throw e0 };
procedure caller(x: Err) opaque
{ try { mk(x) } catch err { assert err == x } };
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
composite Node { var v: int }

procedure wildcardFrame(n: Node)
  opaque
  modifies *
{
    n#v := 3
};

procedure allocatesOnly()
  opaque
{
    var a: Node := new Node
};

procedure wildcardWithoutHeap()
  opaque
  modifies *
{
    var x: int := 1
};

procedure callsWildcardWithoutHeap() entry
  opaque
{
    wildcardWithoutHeap()
};

procedure caller() entry
  opaque
  modifies *
{
    var a: Node := new Node;
    allocatesOnly();
    wildcardFrame(a);
    a#v := 1;
    assert a#v == 1
};
#end

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure main() entry
  opaque
{
    var q: int := 0;
    var z: int := 10 % q;
//                ^^^^^^ error: modulus is non-zero does not hold
    assert 1 == 2
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
procedure main() entry
  opaque
{
    var q: int := 0;
    var z: int := 10 % q;
//                ^^^^^^ error: modulus is non-zero does not hold
    assert 1 == 2
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure main() entry
  opaque
{
    var q: int := 0;
    var z: int := 10 / q;
//                ^^^^^^ error: divisor is non-zero does not hold
    assert 1 == 2
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
procedure main() entry
  opaque
{
    var q: int := 0;
    var z: int := 10 / q;
//                ^^^^^^ error: divisor is non-zero does not hold
    assert 1 == 2
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-- error: cortex-interpret: 'main': an assertion could not be evaluated (diagnostics: []) -/
#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
procedure main() entry
  opaque
{
    assert forall(i: int) => i < 0
};
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
datatype Color { Red(), Green() }
composite Node { var v: int }

procedure uninitialisedDatatype() entry
  opaque
{
    var c: Color;
    assert Color..isRed(c) || Color..isGreen(c)
};

procedure initialisedDatatype() entry
  opaque
{
    var c: Color := Red();
    assert Color..isRed(c)
};

procedure uninitialisedComposite() entry
  opaque
  modifies *
{
    var n: Node;
    n := new Node;
    n#v := 1;
    assert n#v == 1
};
#end

-- A call to a procedure without a body fails the run there: the interpreter has nothing to
-- run, and does not make up the callee's results. A contract on the callee does not change that.
/-- error: cortex-interpret: 'main': a call to 'lib', which has no body to run (diagnostics: [the interpreter fails here: a call to 'lib', which has no body to run]) -/
#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
procedure lib(x: int) returns (r: int) opaque;

procedure main() entry
  opaque
{
    var a: int := lib(3);
    assert a == 0
};
#end

/-- error: cortex-interpret: 'main': a call to 'lib', which has no body to run (diagnostics: [the interpreter fails here: a call to 'lib', which has no body to run]) -/
#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
procedure lib(x: int) returns (r: int)
  requires x >= 0
  opaque
  ensures r == x;

procedure main() entry
  opaque
{
    var a: int := lib(3);
    assert a == 3
};
#end

-- Only a called procedure may lack a body: an entry procedure has nothing to run.
/-- error: cortex-interpret: 'main': entry procedure main has no body (diagnostics: []) -/
#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
procedure main() entry opaque;
#end

#eval testCortexTranslation <|
#strata
program Laurel;
procedure tryCatchInt() entry
  opaque
{
  try {
    throw 7
//        ^ not-yet-implemented: Cortex does not support a non-composite thrown value
  } catch e {
    assert e == 7
  }
};
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
composite Exn { var code: int }

procedure f()
  throws (e: Exn)
  opaque
  modifies *
{
    var ex: Exn := new Exn;
    ex#code := 3;
    throw ex
};

procedure caught() entry
  opaque
  modifies *
{
    var hit: int := 0;
    try { f() } catch e { hit := 1 };
    assert hit == 1
};

procedure caughtWrong() entry
  opaque
  modifies *
{
    var hit: int := 0;
    try { f() } catch e { hit := 1 };
    assert hit == 0
//  ^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
composite Node { var value: int }

procedure set(n: Node)
  opaque
  modifies *
{
    n#value := 1
};

procedure threaded() entry
  opaque
  modifies *
{
    var a: Node := new Node;
    a#value := 0;
    set(a);
    assert a#value == 1
};

procedure threadedWrong() entry
  opaque
  modifies *
{
    var a: Node := new Node;
    a#value := 0;
    set(a);
    assert a#value == 0
//  ^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
composite Exn { var code: int }

procedure inc(x: int) returns (x: int)
  throws (e: Exn)
  opaque
{
    x := x + 1;
    if x > 100 then { var ex: Exn := new Exn; throw ex }
};

procedure main() entry
  opaque
  modifies *
{
    var y: int := 1;
    while (y < 3) {
      try { y := inc(y) } catch err { assert false }
    };
    assert y == 3;
    assert y == 4
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
composite Exn { var code: int }

procedure incT(x: int) returns (x: int)
  throws (e: Exn)
  opaque
{
    x := x + 1;
    if x > 1 then { var ex: Exn := new Exn; throw ex }
};

procedure main() entry
  opaque
  modifies *
{
    var y: int := 1;
    try { y := incT(y) } catch err { };
    assert y == 1;
    assert y == 2
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
composite Exn { var code: int }

procedure incT(x: int) returns (x: int)
  throws (e: Exn)
  opaque
{
    x := x + 1;
    if x > 1 then { var ex: Exn := new Exn; throw ex }
};

procedure main() entry
  opaque
  modifies *
{
    var z: int := 1;
    var y: int := 0;
    try { y := incT(z) } catch err { };
    assert y == 0;
    assert y == 1
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
procedure inc(x: int) returns (x: int)
  opaque
{
    x := x + 1
};

procedure main() entry
  opaque
{
    var y: int := 1;
    y := inc(y);
    assert y == 2;
    assert y == 3
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
procedure inc(x: int) returns (x: int)
  opaque
{
    x := x + 1
};

procedure main() entry
  opaque
{
    var z: int := 1;
    var y: int := 0;
    y := inc(z);
    assert y == 2;
    assert y == 3
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
procedure inc(x: int) returns (x: int)
  opaque
{
    x := x + 1
};

procedure main() entry
  opaque
{
    var y: int := 1;
    y := inc(y + 1);
    assert y == 3;
    assert y == 4
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
procedure inc(x: int) returns (x: int)
  opaque
{
    x := x + 1
};

procedure main() entry
  opaque
{
    var z: int := 1;
    var y: int := 0;
    var i: int := 0;
    while (i < 2) {
      y := inc(z);
      z := y;
      i := i + 1
    };
    assert y == 3;
    assert y == 4
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
procedure inc(x: int) returns (x: int)
  opaque
{
    x := x + 1
};

procedure main() entry
  opaque
{
    var y: int := 1;
    var i: int := 0;
    while (i < 2) {
      y := inc(y + 1);
      i := i + 1
    };
    assert y == 5;
    assert y == 6
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
composite Exn { var code: int }

procedure q() throws (e: Exn)
  opaque
{
    var ex: Exn := new Exn;
    throw ex
};

procedure p()
  opaque
  modifies *
{
    q()
};

procedure main() entry
  opaque
  modifies *
{
    var y: int := 0;
    try { p(); y := 1 } catch err { y := 2 };
    assert y == 2
};
#end

/-! A type constrained over a class holds the instances of the class that meet its constraint. A
reference to no object, such as a field nobody has written, stops the run at a type test: at the
dispatch of a call and at an `is`. -/

/--
error: cortex-interpret: 'dispatchOnNoObject': an expression did not evaluate; 'isOnNoObject': an expression did not evaluate (diagnostics: [the interpreter fails here: an expression did not evaluate, the interpreter fails here: an expression did not evaluate])
-/
#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
composite A {
  procedure m(self: A) returns (r: int) opaque { r := 1 };
}
composite B extends A {
  procedure m(self: B) returns (r: int) opaque { r := 2 };
}
constrained AnyB = b: B where true witness new B
constrained NoB = b: B where false witness new B
composite Holder { var a: A }

procedure constrainedTypes() entry
  opaque
  modifies *
{
    var a: A := new A;
    var b: B := new B;
    assert b is AnyB;
    assert !(b is NoB);
    assert !(a is AnyB)
};

procedure dispatchOnNoObject() entry
  opaque
  modifies *
{
    var h: Holder := new Holder;
    var x: int := h#a#m();
    assert x == 1
};

procedure isOnNoObject() entry
  opaque
  modifies *
{
    var h: Holder := new Holder;
    assert h#a is AnyB
};
#end
