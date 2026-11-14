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

procedure wildcardWithoutHeap() entry
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
//  ^^^^^^^^^^^^^^^^^^^^ error: modulus is non-zero does not hold
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
//  ^^^^^^^^^^^^^^^^^^^^ error: divisor is non-zero does not hold
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

-- A call to a procedure without a body returns the default value of each output
-- that is not of composite type and leaves the existing objects as they are,
-- and the caller runs on: the assertions after the call are checked.
#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
composite Node { var v: int }
procedure lib(x: int) returns (r: int) opaque;
procedure touch(n: Node) opaque modifies *;

procedure main() entry
  opaque
{
    var a: int := lib(3);
    assert a == 0;
    assert 1 == 2
//  ^^^^^^^^^^^^^ error: assertion does not hold
};

procedure heapUnchanged() entry
  opaque
  modifies *
{
    var n: Node := new Node;
    n#v := 1;
    touch(n);
    assert n#v == 1
};
#end

-- A result of composite type of a procedure without a body is a fresh object
-- whose fields hold their default values, so the caller can read and write
-- them. Each call allocates its own object: the write to `a` shows in neither
-- `b` nor `k`.
#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
composite Node { var v: int }
procedure mk() returns (r: Node) opaque;

procedure main() entry
  opaque
  modifies *
{
    var k: Node := new Node;
    k#v := 5;
    var a: Node := mk();
    var b: Node := mk();
    assert a#v == 0;
    a#v := 3;
    assert a#v == 3;
    assert b#v == 0;
    assert k#v == 5;
    assert 1 == 2
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- The value a procedure without a body returns is the default of the base type,
-- here 0, which need not satisfy a constrained output type: the interpreter
-- does not act on what such a callee guarantees, so `v > 0` is reported.
#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
constrained pos = x: int where x > 0 witness 1
procedure g() returns (r: pos) opaque;
procedure main() entry
  opaque
{
    var v: pos := g();
    assert v > 0
//  ^^^^^^^^^^^^ error: assertion does not hold
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
