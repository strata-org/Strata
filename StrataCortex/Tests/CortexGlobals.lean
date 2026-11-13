/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Global variables through the Cortex pipeline

Every entry procedure starts with each global at its initializer, and sees what the
procedures it calls write to the globals. -/

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
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

procedure startsFromInitializers() entry
  opaque
{
    assert g == 0 && h == 3;
    assert g == 1
//  ^^^^^^^^^^^^^ error: assertion does not hold
};

procedure readsAndWrites() entry
  opaque
{
    g := 1;
    h := 2;
    assert g + h == 3
};

procedure unwrittenGlobalIsKept() entry
  opaque
{
    h := 9;
    setG(42);
    assert h == 9
};

procedure calleeWriteIsSeen() entry
  opaque
{
    setG(42);
    assert g == 42;
    assert g == 0
//  ^^^^^^^^^^^^^ error: assertion does not hold
};

procedure readerLeavesGlobalsAlone() entry
  opaque
{
    g := 1;
    h := 2;
    var s: int := sum();
    assert s == 3;
    assert g == 1 && h == 2
};

procedure otherEntriesLeaveNoTrace() entry
  opaque
{
    assert g == 0 && h == 3;
    setG(42);
    assert h == 3
};
#end

/-! A local with the name of a global is a different variable. -/

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
var g: int := 0

procedure localHidesGlobal()
  opaque
{
    var g: int := 1;
    g := g + 1
};

procedure caller() entry
  opaque
{
    g := 5;
    localHidesGlobal();
    assert g == 5;
    assert g == 2
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! A global of a constrained type holds a value of that type wherever a procedure
    returns. A procedure that leaves another value in it is reported at its name, which
    is where the check on return is located. -/

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
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
    c := c + 1
};

procedure reset()
  opaque
{
    c := 0
};

procedure staysInRange() entry
  opaque
{
    increment();
    assert c == 1;
    reset();
    assert 0 <= c && c < 10;
    var r: small := read()
};

procedure leavesRange() entry
  opaque
{
    c := 9;
    increment()
};
#end

/-! A flag-guarded, run-once initializer: the caller sees what the initializer wrote, and
    a procedure that does not run it sees the declared initializers. -/

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
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

procedure reader() returns (r: int) entry
  opaque
{
    var before: int := y;
    if !ready then { ready := true; init() };
    assert ready;
    assert y == before;
    r := x;
    assert r == 5
};

procedure fromEntry() entry
  opaque
{
    assert !ready;
    if !ready then { ready := true; init() };
    assert x == 5
};

procedure notInitialized() entry
  opaque
{
    assert x == 5
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! Initializers that call each other each run once. -/

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
var a: int := 0
var b: int := 0
var readyA: bool := false
var readyB: bool := false

procedure initA()
  opaque
{
    a := a + 1;
    if !readyB then { readyB := true; initB() }
};

procedure initB()
  opaque
{
    b := b + 2;
    if !readyA then { readyA := true; initA() }
};

procedure caller() entry
  opaque
{
    if !readyA then { readyA := true; initA() };
    assert a == 1 && b == 2;
    assert b == 0
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! An entry procedure may use a global of a constrained type: the constraint is checked where
    the global is initialized and at each assignment. -/

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
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

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
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

/-! A call result assigned to a global that the callee also writes: the result wins. -/

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

/-! A call that throws keeps what the callee wrote to a global, and assigns none of its
    results. -/

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

/-! A call that throws assigns none of its results: the handler sees the local's value from
    before the call. -/

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
