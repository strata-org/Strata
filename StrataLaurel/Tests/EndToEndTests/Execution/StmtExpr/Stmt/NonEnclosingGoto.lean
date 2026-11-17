/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Jumps to blocks that do not enclose them

A `goto L` or `exit L` may name any labelled block in a statement position of
the procedure body, not only an enclosing one. `RestructureGotos` nests the
blocks so the verifier sees structured control flow; the interpreters run the
jumps directly. Each program below is checked by the verifier and the
interpreters alike. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure forwardToSibling()
  entry
  opaque
{
    var x: int := 0;
    { if (x == 0) then { goto done }; x := 5 } first;
    { x := 7 } skipped;
    { assert x == 0 } done
};

procedure loopClosedFromNested()
  entry
  opaque
{
    var i: int := 0;
    var s: int := 0;
    { s := s + 1 } head
      invariant 0 <= i && i <= 3 && s == i;
    {
        { i := i + 1; if (i <= 3) then { goto head } } inner
    } tail;
    assert i == 4;
    assert s == 4
};

procedure overlappingRanges(p: bool, q: bool)
  opaque
{
    var r: int := 0;
    { if (p) then { goto c }; r := r + 1 } a;
    { if (q) then { goto d }; r := r + 10 } b;
    { r := r + 100 } c;
    { assert r == 111 || r == 101 || r == 100 || r == 1 } d
};

procedure runOverlapping()
  entry
  opaque
{
    overlappingRanges(false, false);
    overlappingRanges(false, true);
    overlappingRanges(true, false);
    overlappingRanges(true, true)
};

procedure exitPastSibling()
  entry
  opaque
{
    var x: int := 1;
    { if (x > 0) then { exit second }; x := 2 } first;
    { x := 3 } second;
    assert x == 1
};
#end

/-! A wrong assertion after the overlapping jumps fails on both paths: the
interpreters reach it when the second jump skips `r := r + 100`. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure overlappingRangesWrong(p: bool, q: bool)
  opaque
{
    var r: int := 0;
    { if (p) then { goto c }; r := r + 1 } a;
    { if (q) then { goto d }; r := r + 10 } b;
    { r := r + 100 } c;
    { assert r >= 100 } d
//    ^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure runAll()
  entry
  opaque
{
    overlappingRangesWrong(false, true)
};
#end

/-! A loop entered at two blocks is irreducible: the restructuring refuses it
rather than duplicating code. The Laurel interpreter runs it as written. -/

#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure irreducible(c: bool)
  opaque
{
    var i: int := 0;
    { if (c) then { goto second } } start;
    { i := i + 1 } first;
    { i := i + 2; if (i < 10) then { goto first } } second
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: the jumps in this block form a loop that is entered other than through its first statement at 'second'; irreducible control flow cannot be restructured
};
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure irreducible()
  entry
  opaque
{
    var c: bool := true;
    var i: int := 0;
    { if (c) then { goto second } } start;
    { i := i + 1 } first;
    { i := i + 2; if (i < 10) then { goto first } } second;
    assert i == 11
};
#end

/-! A jump out of a `try` runs its `finally` on the way out, on every path. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure outOfTry()
  entry
  opaque
{
    var x: int := 0;
    var cleanups: int := 0;
    try {
        if (x == 0) then { goto after };
        x := 5
    } finally { cleanups := cleanups + 1 };
    { assert false } skipped;
    { assert x == 0 && cleanups == 1 } after
};
#end

/-! Nested loops whose outer latch is where the inner loop exits: the latch follows
the inner loop rather than sitting inside it, so the inner loop does not change the
outer counter and the invariants prove the result. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure nestedLoops()
  entry
  opaque
{
    var i: int := 0;
    var j: int := 0;
    var x: int := 0;
    { if (!(i < 3)) then { goto done }; j := 0 } outer
      invariant 0 <= i && i <= 3 && x == i * 2;
    { if (!(j < 2)) then { goto latch }; x := x + 1; j := j + 1; goto inner } inner
      invariant 0 <= i && i < 3 && 0 <= j && j <= 2 && x == i * 2 + j;
    { i := i + 1; goto outer } latch;
    { assert x == 6 } done
};
#end

/-! A block after a `throw` that a jump reaches is kept when the exception is
lowered. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure throwThenTarget()
  entry
  opaque
{
    var r: int := 0;
    try {
        if (r == 0) then { goto ok };
        throw 1;
        { r := 5 } ok
    } catch c { r := 7 };
    assert r == 5
};
#end

/-! Locals of the same name in sibling blocks stay apart when the blocks are
nested into structured control flow. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure siblingLocals()
  entry
  opaque
{
    var r: int := 0;
    { var t: int := 1; r := r + t; goto second } first;
    { var t: int := 10; r := r + t; if (r < 30) then { goto second } } second
      invariant r >= 1;
    assert r >= 30
};
#end

/-! Resolution refuses the jumps that cannot be restructured faithfully, on every
path. -/

#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure pastDeclaration()
  entry
  opaque
{
    var x: int := 0;
    { if (x == 0) then { goto use } } first;
//                       ^^^^^^^^ error: a jump to 'use' would enter the scope of 'y' past its declaration
    var y: int := 1;
    { assert y == 1 } use
};

procedure intoLoop()
  entry
  opaque
{
    var i: int := 0;
    goto body;
//  ^^^^^^^^^ error: a jump to 'body' would enter a loop body from outside it
    while (i < 3) { { i := i + 1 } body }
};

procedure ambiguous()
  entry
  opaque
{
    { goto twice } first;
//    ^^^^^^^^^^ error: label 'twice' names more than one block, so a jump from outside it is ambiguous
    { { } twice } a;
    { { } twice } b
};
#end

/-! The Laurel interpreter refuses the same program, at resolution. -/

/-- error: laurel-interpret: resolution failed: #[a jump to 'use' would enter the scope of 'y' past its declaration, a jump to 'body' would enter a loop body from outside it, label 'twice' names more than one block, so a jump from outside it is ambiguous] -/
#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure pastDeclaration()
  entry
  opaque
{
    var x: int := 0;
    { if (x == 0) then { goto use } } first;
    var y: int := 1;
    { assert y == 1 } use
};

procedure intoLoop()
  entry
  opaque
{
    var i: int := 0;
    goto body;
    while (i < 3) { { i := i + 1 } body }
};

procedure ambiguous()
  entry
  opaque
{
    { goto twice } first;
    { { } twice } a;
    { { } twice } b
};
#end

/-! A jump between blocks of a `finally` arm stays inside it: it does not leave the
`try` around it, so the outer `finally` runs once, when that `try` ends. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure jumpInsideNestedFinally()
  entry
  opaque
{
    var z: int := 0;
    try {
        try { z := z } finally {
            if (z == 0) then { goto b };
            { z := 100 } a;
            { } b
        }
    } finally { z := z + 1 };
    assert z == 1
};
#end

/-! Restructuring moves a block's locals to the top of the region, so a local of
the same name declared later inside an `if`, a loop or a block value, which is
kept whole, is renamed rather than left in the moved local's scope. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure hoistedClashesWithKeptIf()
  entry
  opaque
{
    { var x: int := 0; if (x == 0) then { goto b } } a;
    { } b;
    if (true) then { var x: int := 2; assert x == 2 }
};
procedure hoistedClashesWithKeptWhile()
  entry
  opaque
{
    var i: int := 0;
    { var x: int := 0; if (x == 0) then { goto b } } a;
    { } b;
    while (i < 1) { var x: int := 2; i := i + 1 }
};
procedure hoistedClashesWithBlockValue()
  entry
  opaque
{
    var r: int := 0;
    { var x: int := 0; if (x == 0) then { goto b } } a;
    { } b;
    r := { var x: int := 9; x };
    assert r == 9
};
procedure hoistedClashesWithBlockInitializer()
  entry
  opaque
{
    { var x: int := 0; if (x == 0) then { goto b } } a;
    { } b;
    var s: int := { var x: int := 4; x + 1 };
    assert s == 5
};
#end

/-! Locals declared by one assignment of several targets are moved and renamed like
single ones. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure pair(a: int) returns (x: int, y: int)
  opaque
  ensures x == a && y == a + 1
{
  return a, a + 1
};
procedure multiTargetSiblings()
  entry
  opaque
{
    var r: int := 0;
    { assign var t: int, var u: int := pair(1); r := t + u; goto second } first;
    { assign var t: int, var u: int := pair(10); r := r + t + u } second;
    assert r == 24
};
procedure multiTargetClash()
  entry
  opaque
{
    { assign var x: int, var y: int := pair(0); if (x == 0) then { goto b } } a;
    { } b;
    if (true) then { var y: int := 5; assert y == 5 }
};
#end

/-! A block that no jump names is still kept when a jump targets a block inside it. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure intoNested()
  entry
  opaque
{
    var x: int := 0;
    { x := 1; goto inner } a;
    { x := 2; { assert x == 1 } inner } outer
};
#end

#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure intoNestedWrong(p: bool)
  opaque
{
    var x: int := 0;
    { x := 1; if (p) then { goto inner } } a;
    { x := 2; { assert x == 2 } inner } outer
//              ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! A local declared with neither a type nor an initializer takes the type of its
first assignment, so a jump target can rethrow a caught exception at the type the
`catch` binding was inferred at, as javac's `finally` handler does through a local.
When the `catch` can never fire, the blocks only it jumps to are dropped with it. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Failure {}
procedure fails() throws (e: Failure) opaque {
    var f: Failure := new Failure;
    throw f
};
procedure untypedLocalInferred() entry opaque {
    var t;
    { t := 3 } a;
    assert t == 3
};
procedure rethrows() throws (e: Failure) opaque {
    var t;
    { try { fails() } catch e { t := e; goto handler } } tr;
    { goto done } normal;
    { throw t } handler;
    { } done
};
procedure callsRethrows() entry opaque modifies * {
    try { rethrows() } catch e { assert true }
};
#end

#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure rethrowAfterDeadCatch() entry opaque {
    var r: int := 0;
    var t;
    { try { r := 1 } catch e { t := e; goto handler } } tr;
//    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ warning: the `catch` clause(s) of this `try` can never fire: no exception type could be determined for the `try` body, so they are discarded and the body is verified as if no handler were present
    { r := r + 1; goto done } normal;
    { r := r + 1; throw t } handler;
    { assert r == 2 } done
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
procedure neverAssigned() opaque {
    var u;
//  ^^^^^ error: cannot infer a type for 'u'
    assert true
};
#end

/-! A coroutine body is split into states at its suspension points, so it may
not jump to a block that does not enclose the jump. -/

#eval testLaurelResolution <|
#strata
program Laurel;
coroutine counter() yields (x: int)
  modifies *
{
    { x := 1; goto second } first;
//            ^^^^^^^^^^^ error: a jump to 'second', a block that does not enclose it, is not supported in a coroutine
    { x := 2; yield } second
};
#end

/-! A jump into a `try` inside a loop enters the loop first, and says so. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure intoTryInLoop()
  opaque
{
    var i: int := 0;
    goto inside;
//  ^^^^^^^^^^^ error: a jump to 'inside' would enter a loop body from outside it
    while (i < 3) {
        try { { i := i + 1 } inside } finally { }
    }
};
#end
