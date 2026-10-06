/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
# Shadowing the `throws` binding

Each shadowed spelling is paired with an unshadowed twin that must behave
identically.
-/

#guard_msgs in
-- No interpreters: any caller turns the verdict into "could not be proved", and neither interpreter checks a quantified postcondition.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Err { var code: int }
procedure quantShadows()
  throws (e: Err)
  opaque
  throwsOn true {
    ensures forall(e: Err) => e#code > 0
//          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition does not hold
  }
{
  var x: Err := new Err;
  x#code := 5;
  throw x
};
procedure quantFresh()
  throws (e: Err)
  opaque
  throwsOn true {
    ensures forall(q: Err) => q#code > 0
//          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition does not hold
  }
{
  var x: Err := new Err;
  x#code := 5;
  throw x
};
#end

#guard_msgs in
-- No interpreters: the annotated failures are "could not be proved", which a concrete run cannot produce.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Err { var code: int }
procedure existsShadows()
  throws (e: Err)
  opaque
  throwsOn true {
    ensures exists(e: Err) => e#code > 0
//          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
  }
{
  var x: Err := new Err;
  x#code := 5;
  throw x
};
procedure existsFresh()
  throws (e: Err)
  opaque
  throwsOn true {
    ensures exists(q: Err) => q#code > 0
//          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
  }
{
  var x: Err := new Err;
  x#code := 5;
  throw x
};
#end

#guard_msgs in
-- No Core interpreter: its quantified postcondition "did not reduce to bool".
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
composite Err { var code: int }
procedure declShadows()
  throws (e: Err)
  opaque
  throwsOn true {
    ensures { var e: int := 3; e > 0 }
  }
{
  var x: Err := new Err;
  x#code := 5;
  throw x
};
procedure declFresh()
  throws (e: Err)
  opaque
  throwsOn true {
    ensures { var q: int := 3; q > 0 }
  }
{
  var x: Err := new Err;
  x#code := 5;
  throw x
};
procedure quantEnclosedDecl()
  throws (e: Err)
  opaque
  throwsOn true {
    ensures forall(e: int) => ({ var e: int := e; e } == e)
  }
{
  var x: Err := new Err;
  x#code := 5;
  throw x
};
procedure quantEnclosedDeclFresh()
  throws (e: Err)
  opaque
  throwsOn true {
    ensures forall(q: int) => ({ var q: int := q; q } == q)
  }
{
  var x: Err := new Err;
  x#code := 5;
  throw x
};
procedure runAll() entry
  opaque
  modifies *
{
  try { declShadows() } catch e { assert true };
  try { declFresh() } catch e { assert true };
  try { quantEnclosedDecl() } catch e { assert true };
  try { quantEnclosedDeclFresh() } catch e { assert true }
};
#end

#guard_msgs in
-- No interpreters: the annotated errors are Laurel→Core translation rejections, not runtime failures.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Err { var code: int }
procedure bareUninitShadow()
  throws (e: Err)
  opaque
  throwsOn true {
    ensures { var e: int; e := 3; e > 0 }
//            ^^^^^^^^^^ error: local variables must have initializers in transparent bodies or contracts
//                        ^^^^^^ error: destructive assignments are not supported in transparent bodies or contracts
  }
{
  var x: Err := new Err;
  x#code := 5;
  throw x
};
#end

#guard_msgs in
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Err { var code: int }
procedure valueShadows() returns (n: int)
  throws (e: Err)
  opaque
  ensures { var n: int := 3; n > 0 }
{
  n := -1
};
procedure valueFresh() returns (n: int)
  throws (e: Err)
  opaque
  ensures { var q: int := 3; q > 0 }
{
  n := -1
};
procedure valueStillBinds() returns (n: int)
  throws (e: Err)
  opaque
  ensures n > 0
{
  n := 1
};
procedure runAll() entry
  opaque
  modifies *
{
  try {
    var a: int := valueShadows();
    var b: int := valueFresh();
    var c: int := valueStillBinds();
    assert c > 0
  } catch e { assert true }
};
#end

#guard_msgs in
-- No Core interpreter: a quantified postcondition "did not reduce to bool".
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
composite Err { var code: int }
procedure bindingStillWorks()
  throws (e: Err)
  opaque
  throwsOn true {
    ensures e#code > 0
  }
{
  var x: Err := new Err;
  x#code := 5;
  throw x
};
procedure mixed()
  throws (e: Err)
  opaque
  throwsOn true {
    ensures e#code > 0
    ensures forall(e: Err) => e#code > 0 || e#code <= 0
  }
{
  var x: Err := new Err;
  x#code := 5;
  throw x
};
procedure readBeforeShadow()
  throws (e: Err)
  opaque
  throwsOn true {
    ensures { var c: int := e#code; var e: int := 0; c > 0 }
  }
{
  var x: Err := new Err;
  x#code := 5;
  throw x
};
procedure nestedBlockShadow()
  throws (e: Err)
  opaque
  throwsOn true {
    ensures { var c: int := { var e: int := 0; e + 1 }; c > 0 && e#code > 0 }
  }
{
  var x: Err := new Err;
  x#code := 5;
  throw x
};
procedure quantInsideBlock()
  throws (e: Err)
  opaque
  throwsOn true {
    ensures { var c: int := 1; (forall(e: Err) => e#code >= e#code) && c > 0 && e#code > 0 }
  }
{
  var x: Err := new Err;
  x#code := 5;
  throw x
};
procedure runAll() entry
  opaque
  modifies *
{
  try { bindingStillWorks() } catch e { assert true };
  try { mixed() } catch e { assert true };
  try { readBeforeShadow() } catch e { assert true };
  try { nestedBlockShadow() } catch e { assert true };
  try { quantInsideBlock() } catch e { assert true }
};
#end

#guard_msgs in
-- No interpreters: Core says the quantifier "did not reduce to bool"; Laurel says "unsupported expression: quantifier".
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Err { var code: int }
procedure catchQuantShadows() returns (r: int)
  throws (t: Err)
  opaque
  ensures r == 5
{
  var x: Err := new Err;
  x#code := 5;
  r := 0;
  try {
    throw x
  } catch e when e is Err {
    assert (forall(e: int) => e >= e);
    r := e#code
  }
};
procedure catchQuantFresh() returns (r: int)
  throws (t: Err)
  opaque
  ensures r == 5
{
  var x: Err := new Err;
  x#code := 5;
  r := 0;
  try {
    throw x
  } catch e when e is Err {
    assert (forall(q: int) => q >= q);
    r := e#code
  }
};
procedure catchGuardQuantShadows() returns (r: int)
  throws (t: Err)
  opaque
  ensures r == 5
{
  var x: Err := new Err;
  x#code := 5;
  r := 0;
  try {
    throw x
  } catch e when (forall(e: int) => e >= e) && e is Err {
    r := e#code
  }
};
procedure catchGuardQuantFresh() returns (r: int)
  throws (t: Err)
  opaque
  ensures r == 5
{
  var x: Err := new Err;
  x#code := 5;
  r := 0;
  try {
    throw x
  } catch e when (forall(q: int) => q >= q) && e is Err {
    r := e#code
  }
};
#end

#guard_msgs in
-- No interpreters: Core says the quantifier "did not reduce to bool"; Laurel says "unsupported expression: quantifier".
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Err { var code: int }
procedure catchBindingFullyShadowed() returns (r: int)
  throws (t: Err)
  opaque
  ensures r == 1
{
  var x: Err := new Err;
  x#code := 5;
  r := 0;
  try {
    throw x
  } catch e when e is Err {
    assert (forall(e: int) => e >= e);
    r := 1
  }
};
procedure catchBindingFullyFresh() returns (r: int)
  throws (t: Err)
  opaque
  ensures r == 1
{
  var x: Err := new Err;
  x#code := 5;
  r := 0;
  try {
    throw x
  } catch e when e is Err {
    assert (forall(q: int) => q >= q);
    r := 1
  }
};
#end

#guard_msgs in
-- No Core interpreter: calling an allocating procedure fails with "condition did not reduce to bool".
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
composite Err { var code: int }
procedure nestedCatchSameName() returns (r: int)
  throws (t: Err)
  opaque
  ensures r == 7
{
  var x: Err := new Err;
  x#code := 5;
  r := 0;
  try {
    throw x
  } catch e when e is Err {
    var y: Err := new Err;
    y#code := 2;
    try {
      throw y
    } catch e when e is Err {
      r := e#code
    };
    r := r + e#code
  }
};
procedure nestedCatchFresh() returns (r: int)
  throws (t: Err)
  opaque
  ensures r == 7
{
  var x: Err := new Err;
  x#code := 5;
  r := 0;
  try {
    throw x
  } catch e when e is Err {
    var y: Err := new Err;
    y#code := 2;
    try {
      throw y
    } catch q when q is Err {
      r := q#code
    };
    r := r + e#code
  }
};
procedure runAll() entry
  opaque
  modifies *
{
  try {
    var a: int := nestedCatchSameName();
    var b: int := nestedCatchFresh();
    assert a == 7 && b == 7
  } catch e { assert true }
};
#end
