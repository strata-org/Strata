/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Global variables through the Cortex pipeline

A global is an arbitrary value at the start of every procedure except an entry procedure,
where it starts with its initializer. A caller keeps what it knows about a global that the
callee does not write, and knows nothing about one that the callee writes: Cortex procedures
have no contracts. -/

#eval testCortexVerification <|
#strata
program Laurel;
var g: int := 0
var h: int := 3

procedure setG(v: int)
  opaque
{
    g := v
};

procedure sum() returns (r: int)
  opaque
{
    r := g + h
};

procedure startsArbitrary()
  opaque
{
    assert g == 0
//  ^^^^^^^^^^^^^ error: assertion does not hold
};

procedure readsAndWrites()
  opaque
{
    g := 1;
    h := 2;
    assert g + h == 3
};

procedure unwrittenGlobalIsKept()
  opaque
{
    h := 9;
    setG(42);
    assert h == 9
};

procedure writtenGlobalIsUnknown()
  opaque
{
    setG(42);
    assert g == 42
//  ^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure readerLeavesGlobalsAlone()
  opaque
{
    g := 1;
    h := 2;
    var s: int := sum();
    assert g == 1 && h == 2
};

procedure entryStartsFromInitializers() entry
  opaque
{
    assert g == 0 && h == 3;
    setG(42);
    assert h == 3
};
#end

/-! A local with the name of a global is a different variable. -/

#eval testCortexVerification <|
#strata
program Laurel;
var g: int := 0

procedure localHidesGlobal()
  opaque
{
    var g: int := 1;
    g := g + 1
};

procedure caller()
  opaque
{
    g := 5;
    localHidesGlobal();
    assert g == 5
};
#end

/-! A global of a constrained type holds a value of that type wherever a procedure starts
    or returns. A procedure that may leave another value in it is reported at its name, which
    is where the check on return is located. -/

#eval testCortexVerification <|
#strata
program Laurel;
constrained small = x: int where 0 <= x && x < 10 witness 0
var c: small := 0

procedure read() returns (r: small)
  opaque
{
    r := c
};

procedure increment()
//        ^^^^^^^^^ error: assertion does not hold
  opaque
{
    assert c < 10;
    c := c + 1
};

procedure reset()
  opaque
{
    c := 0
};

procedure caller()
  opaque
{
    reset();
    assert 0 <= c && c < 10;
    var r: small := read()
};
#end

/-! Inlining a named procedure lets the caller rely on what it does. The pattern below is a
    flag-guarded, run-once initializer. -/

#eval testCortexVerification (inline := ["init"]) <|
#strata
program Laurel;
var x: int := 0
var y: int := 0
var ready: bool := false

procedure init()
  opaque
{
    x := 5
};

procedure reader() returns (r: int)
  opaque
{
    var before: int := y;
    if !ready then { ready := true; init() };
    assert ready;
    assert y == before;
    r := x
};

procedure fromEntry() entry
  opaque
{
    assert !ready;
    if !ready then { ready := true; init() };
    assert x == 5
};

procedure notInitialized()
  opaque
{
    assert x == 5
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! Without inlining, the same caller does not know what the initializer wrote. -/

#eval testCortexVerification <|
#strata
program Laurel;
var x: int := 0
var ready: bool := false

procedure init()
  opaque
{
    x := 5
};

procedure fromEntry() entry
  opaque
{
    if !ready then { ready := true; init() };
    assert x == 5
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! Procedures that call each other are not inlined, so the callers still verify, and know
    nothing about what the cycle wrote. -/

#eval testCortexVerification (inline := ["initA", "initB"]) <|
#strata
program Laurel;
var a: int := 0
var b: int := 0
var readyA: bool := false
var readyB: bool := false

procedure initA()
  opaque
{
    a := 1;
    if !readyB then { readyB := true; initB() }
};

procedure initB()
  opaque
{
    b := 2;
    if !readyA then { readyA := true; initA() }
};

procedure caller()
  opaque
{
    if !readyA then { readyA := true; initA() };
    assert a == 1
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! An entry procedure may use a global of a constrained type: the constraint is checked where
    the global is initialized and at each assignment. -/

#eval testCortexVerification <|
#strata
program Laurel;
constrained small = x: int where 0 <= x && x < 10 witness 0
var c: small := 3

procedure startsFromInitializer() entry
  opaque
{
    assert c == 3;
    c := c + 1;
    assert c == 4
};

procedure leavesRange() entry
  opaque
{
    c := c + 7
//  ^^^^^^^^^^ error: assertion does not hold
};
#end

/-! An initializer outside the global's constrained type is reported in the entry procedure, where
    the global is initialized. -/

#eval testCortexVerification <|
#strata
program Laurel;
constrained small = x: int where 0 <= x && x < 10 witness 0
var c: small := 30
//  ^ error: assertion does not hold

procedure startsOutOfRange() entry
  opaque
{
    assert c < 10
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#eval testCortexVerification <|
#strata
program Laurel;
var g: int := 0

procedure f() returns (r: int)
  opaque
{
    g := 5;
    r := 8
};

procedure assignsResultToWrittenGlobal()
  opaque
{
    g := f()
};
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
var g: int := 0

procedure f() returns (r: int)
  opaque
{
    g := 5;
    r := 8
};

procedure main() entry
  opaque
{
    g := f();
    assert g == 8;
    assert g == 5
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#eval testCortexVerification (inline := ["f"]) <|
#strata
program Laurel;
composite Exn { var code: int }
var g: int := 0

procedure f() returns (r: int)
  throws (e: Exn)
  opaque
  modifies *
{
    r := 8;
    g := 5;
    var ex: Exn := new Exn;
    throw ex
};

procedure handlerSeesCalleeWrite()
  opaque
  modifies *
{
    try { g := f() } catch err { assert g == 5 }
};

procedure handlerDoesNotSeeResult()
  opaque
  modifies *
{
    try { g := f() } catch err { assert g == 8 }
//                               ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
composite Exn { var code: int }
var g: int := 0

procedure f() returns (r: int)
  throws (e: Exn)
  opaque
  modifies *
{
    r := 8;
    g := 5;
    var ex: Exn := new Exn;
    throw ex
};

procedure main() entry
  opaque
  modifies *
{
    try { g := f() } catch err { assert g == 5 };
    try { g := f() } catch err { assert g == 8 }
//                               ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! A call that throws assigns none of its results, also when the callee is inlined: the
handler sees the local's value from before the call. -/
#eval testCortexVerification (inline := ["f"]) <|
#strata
program Laurel;
composite Exn { var code: int }

procedure f() returns (r: int)
  throws (e: Exn)
  opaque
{
    r := 8;
    var ex: Exn := new Exn;
    throw ex
};

procedure handlerKeepsLocal()
  opaque
  modifies *
{
    var y: int := 1;
    try { y := f() } catch err { assert y == 1 }
};

procedure handlerDoesNotSeeLocalResult()
  opaque
  modifies *
{
    var y: int := 1;
    try { y := f() } catch err { assert y == 8 }
//                               ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
composite Exn { var code: int }

procedure f() returns (r: int)
  throws (e: Exn)
  opaque
{
    r := 8;
    var ex: Exn := new Exn;
    throw ex
};

procedure main() entry
  opaque
  modifies *
{
    var y: int := 1;
    try { y := f() } catch err { assert y == 1 };
    try { y := f() } catch err { assert y == 8 }
//                               ^^^^^^^^^^^^^ error: assertion does not hold
};
#end
