/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! A field of a constrained type is checked at each write, and a value read into a
    constrained local or global is checked at that assignment. -/

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
constrained pos = x: int where x > 0 witness 1
composite Cell { var v: pos var w: int }
var g: pos := 1

procedure writeInRange() entry
  opaque
  modifies *
{
    var c: Cell := new Cell;
    c#v := 5;
    assert c#v == 5
};

procedure readIntoConstrainedLocal() entry
  opaque
  modifies *
{
    var c: Cell := new Cell;
    c#w := 0;
    var y: pos := c#w
//  ^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure globalIntoField() entry
  opaque
  modifies *
{
    var c: Cell := new Cell;
    c#v := g;
    assert c#v == 1
};

procedure fieldIntoGlobal() entry
  opaque
  modifies *
{
    var c: Cell := new Cell;
    c#v := 7;
    g := c#v;
    assert g == 7
};

procedure globalOutOfRange()
//        ^^^^^^^^^^^^^^^^ error: assertion does not hold
  opaque
{
    g := 0
};

procedure calleeLeavesRange() entry
  opaque
{
    globalOutOfRange()
};
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
constrained pos = x: int where x > 0 witness 1
composite Cell { var v: pos }

procedure main() entry
  opaque
  modifies *
{
    var c: Cell := new Cell;
    c#v := 0
//  ^^^^^^^^ error: assertion does not hold
};
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
constrained pos = x: int where x > 0 witness 1
var g: pos := 1

procedure main() entry
  opaque
{
    g := 0
//  ^^^^^^ error: assertion does not hold
};
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
composite Exn { var code: int }
var g: int := 0

procedure thrower()
  throws (e: Exn)
  opaque
  modifies *
{
    g := 5;
    var ex: Exn := new Exn;
    throw ex
};

procedure main() entry
  opaque
  modifies *
{
    try { thrower() } catch err { assert g == 5 };
    try { thrower() } catch err { assert g == 6 }
//                                ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
var g: int := 3
composite A {
  var x: int
  procedure get(self: A) returns (r: int) opaque { r := g };
}

procedure main() entry
  opaque
  modifies *
{
    var a: A := new A;
    var r: int := a#get();
    assert r == 3;
    assert r == 4
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end
