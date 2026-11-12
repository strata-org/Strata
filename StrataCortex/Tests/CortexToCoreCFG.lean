/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

/-!
# Cortex to Core with CFG bodies

Each test translates a Laurel program through Cortex to Core with CFG bodies
(`Cortex.ToCore.programToCoreCFG`), pins the emitted procedures, and pins that
the whole program type-checks with Core's CFG type checker.
-/

open StrataTest.Util
open Strata

-- Straight-line code, a branch that merges, and a loop.
/--
info: procedure branchAndLoop (n : int, out r : int)
cfg $heapEntry {
  $heapEntry: {
    goto $exnEntry;
  }
  $exnEntry: {
    goto $entry;
  }
  $entry: {
    var s : int;
    var i : int;
    goto $start;
  }
  $start: {
    branch (int.gt(n, 0)) goto $then$0 else goto $else$1;
  }
  $then$0: {
    s := 1;
    goto $endif$2;
  }
  $else$1: {
    s := 2;
    goto $endif$2;
  }
  $endif$2: {
    i := 0;
    goto loop$start$4;
  }
  loop$start$4: {
    branch (int.ge(i, n)) goto $then$6 else goto $else$7;
  }
  $then$6: {
    goto $region$9;
  }
  $region$9: {
    goto loop$end$5;
  }
  $else$7: {
    goto $endif$8;
  }
  $endif$8: {
    s := int.add(s, i);
    i := int.add(i, 1);
    goto $region$12;
  }
  $region$12: {
    goto loop$start$4;
  }
  loop$end$5: {
    r := s;
    goto $return;
  }
  $return: {
    return;
  }
};
type check: ok
-/
#guard_msgs in
#eval printCortexCoreCFG (procs := ["branchAndLoop"]) <|
#strata
program Laurel;
procedure branchAndLoop(n: int) returns (r: int)
  opaque
{
    var s: int := 0;
    if n > 0 then { s := 1 } else { s := 2 };
    var i: int := 0;
    {
        if i >= n then { exit loop };
        s := s + i;
        i := i + 1;
        goto loop
    } loop;
    r := s
};
#end

-- A local declared in a loop body, and nested loops left by `exit`.
/--
info: procedure nested (n : int)
cfg $heapEntry {
  $heapEntry: {
    goto $exnEntry;
  }
  $exnEntry: {
    goto $entry;
  }
  $entry: {
    var i : int;
    var j : int;
    var t : int;
    goto $start;
  }
  $start: {
    i := 0;
    goto $loop_head$0;
  }
  $loop_head$0: {
    branch (int.lt(i, n)) goto $loop_body$1 else goto $loop_exit$2;
  }
  $loop_body$1: {
    j := 0;
    goto $loop_head$3;
  }
  $loop_head$3: {
    branch (int.lt(j, i)) goto $loop_body$4 else goto $loop_exit$5;
  }
  $loop_body$4: {
    t := int.add(j, 1);
    j := t;
    goto $loop_head$3;
  }
  $loop_exit$5: {
    i := int.add(i, 1);
    goto $loop_head$0;
  }
  $loop_exit$2: {
    goto $return;
  }
  $return: {
    return;
  }
};
type check: ok
-/
#guard_msgs in
#eval printCortexCoreCFG (procs := ["nested"]) <|
#strata
program Laurel;
procedure nested(n: int)
  opaque
{
    var i: int := 0;
    while (i < n) {
        var j: int := 0;
        while (j < i) {
            var t: int := j + 1;
            j := t
        };
        i := i + 1
    }
};
#end

-- An assigned input is copied from `x$in` at the start of the entry block.
/--
info: procedure assignInput (x$in : int, out r : int)
cfg $heapEntry {
  $heapEntry: {
    var x : int := x$in;
    goto $exnEntry;
  }
  $exnEntry: {
    goto $entry;
  }
  $entry: {
    goto $start;
  }
  $start: {
    x := int.add(x, 1);
    r := x;
    goto $return;
  }
  $return: {
    return;
  }
};
type check: ok
-/
#guard_msgs in
#eval printCortexCoreCFG (procs := ["assignInput"]) <|
#strata
program Laurel;
procedure assignInput(x: int) returns (r: int)
  opaque
{
    x := x + 1;
    r := x
};
#end

-- A call, after `LowerHeap` and `LowerGlobals`, and field accesses.
/--
info: procedure callAndHeap (inout $heap : $Heap)
cfg $cteEntry {
  $cteEntry: {
    goto $heapEntry;
  }
  $heapEntry: {
    var $fieldValue5 : int;
    goto $exnEntry;
  }
  $exnEntry: {
    goto $entry;
  }
  $entry: {
    var $c1 : $Composite;
    assume [constraint_Node_0]: $Composite..typeTag!($c1) == Node$TypeTag;
    var $c2 : int;
    var $c3 : int;
    goto $start;
  }
  $start: {
    $c1 := $MkComposite($Heap..nextReference!($heap), Node$TypeTag);
    $heap := $MkHeap($Heap..data!($heap), int.add($Heap..nextReference!($heap), 1));
    call inc(3, out $c2);
    $fieldValue5 := $c2;
    $heap := $MkHeap(($Heap..data!($heap))[$Composite..ref!($c1):=(($Heap..data!($heap))[$Composite..ref!($c1)])[$field$Node.value:=$Box$int($fieldValue5)]], $Heap..nextReference!($heap));
    $c3 := $Box..$val$int!((($Heap..data!($heap))[$Composite..ref!($c1)])[$field$Node.value]);
    assert [assert_4]: $c3 == 4;
    goto $return;
  }
  $return: {
    return;
  }
};
type check: ok
-/
#guard_msgs in
#eval printCortexCoreCFG (procs := ["callAndHeap"]) <|
#strata
program Laurel;
composite Node { var value: int }
procedure inc(x: int) returns (r: int)
  opaque
{
    r := x + 1
};
procedure callAndHeap()
  opaque
  modifies *
{
    var a: Node := new Node;
    a#value := inc(3);
    assert a#value == 4
};
#end

-- try/catch/finally after `LowerExceptions`. `PruneUnreachable` drops the
-- handler of the `finally` region, which no `throw` reaches.
/--
info: procedure handlers (inout $heap : $Heap)
cfg $cteEntry {
  $cteEntry: {
    goto $heapEntry;
  }
  $heapEntry: {
    goto $exnEntry;
  }
  $exnEntry: {
    var $exv : $Composite;
    var $callThrown : bool;
    var $callExc : $Composite;
    var $exnTest : bool;
    goto $entry;
  }
  $entry: {
    var caught : int;
    var $c0 : $Composite;
    var $c6 : $Composite;
    assume [constraint_Exn_0]: $Composite..typeTag!($c6) == Exn$TypeTag;
    var f : int;
    var $c12 : $Composite;
    var $c14 : $Composite;
    goto $start;
  }
  $start: {
    goto $region$5;
  }
  $catch$exn0: {
    $c0 := $exv;
    goto $catch_dispatch$1;
  }
  $region$5: {
    $c6 := $MkComposite($Heap..nextReference!($heap), Exn$TypeTag);
    $heap := $MkHeap($Heap..data!($heap), int.add($Heap..nextReference!($heap), 1));
    $exv := $c6;
    goto $catch$exn0;
  }
  $catch_dispatch$1: {
    caught := 1;
    goto $try_end$4;
  }
  $try_end$4: {
    goto $region$17;
  }
  $region$17: {
    f := 1;
    goto $region$18;
  }
  $region$18: {
    goto $try_end$16;
  }
  $try_end$16: {
    f := int.add(f, 10);
    assert [assert_22]: if caught == 1 then f == 11 else false;
    goto $return;
  }
  $return: {
    return;
  }
};
type check: ok
-/
#guard_msgs in
#eval printCortexCoreCFG (procs := ["handlers"]) <|
#strata
program Laurel;
composite Exn { var code: int }
procedure handlers()
  opaque
  modifies *
{
    var caught: int := 0;
    try {
      var x: Exn := new Exn;
      throw x
    } catch err {
      caught := 1
    };
    var f: int := 0;
    try { f := 1 } finally { f := f + 10 };
    assert caught == 1 && f == 11
};
#end

-- A dynamically dispatched call after `LowerDispatch`.
/--
info: procedure dispatch (a : $Composite, $heap : $Heap, out r : int)
cfg $cteEntry {
  $cteEntry: {
    assume [constraint_A_0]: $Composite..typeTag!(a) == A$TypeTag || $Composite..typeTag!(a) == B$TypeTag;
    goto $heapEntry;
  }
  $heapEntry: {
    assume [allocated]: int.lt($Composite..ref!(a), $Heap..nextReference!($heap));
    goto $exnEntry;
  }
  $exnEntry: {
    goto $dispatchEntry;
  }
  $dispatchEntry: {
    var $dispatchTest : bool;
    goto $entry;
  }
  $entry: {
    goto $start;
  }
  $dispatch_default$vd1: {
    call A$get(a, $heap, out r);
    goto $dispatch_join$vd0;
  }
  $dispatch$vd2: {
    call B$get(a, $heap, out r);
    goto $dispatch_join$vd0;
  }
  $dispatch_test$vd3: {
    $dispatchTest := $Composite..typeTag!(a) == B$TypeTag;
    branch ($dispatchTest) goto $dispatch$vd2 else goto $dispatch_default$vd1;
  }
  $start: {
    goto $dispatch_test$vd3;
  }
  $dispatch_join$vd0: {
    goto $return;
  }
  $return: {
    return;
  }
};
type check: ok
-/
#guard_msgs in
#eval printCortexCoreCFG (procs := ["dispatch"]) <|
#strata
program Laurel;
composite A {
  procedure get(self: A) returns (r: int) opaque { r := 1 };
}
composite B extends A {
  procedure get(self: B) returns (r: int) opaque { r := 2 };
}
procedure dispatch(a: A) returns (r: int)
  opaque
{
    r := a#get()
};
#end

-- A typed catch: the dispatch block tests the type of the thrown object and
-- falls through to the next clause when it does not match.
/--
info: procedure typedCatch (inout $heap : $Heap, out r : int)
cfg $cteEntry {
  $cteEntry: {
    goto $heapEntry;
  }
  $heapEntry: {
    goto $exnEntry;
  }
  $exnEntry: {
    var $exv : $Composite;
    var $callThrown : bool;
    var $callExc : $Composite;
    var $exnTest : bool;
    goto $entry;
  }
  $entry: {
    var $c0 : $Composite;
    var $c6 : $Composite;
    assume [constraint_Exn_0]: $Composite..typeTag!($c6) == Exn$TypeTag || $Composite..typeTag!($c6) == Special$TypeTag;
    var $c10 : bool;
    goto $start;
  }
  $start: {
    goto $region$5;
  }
  $catch$exn0: {
    $c0 := $exv;
    goto $catch_dispatch$1;
  }
  $region$5: {
    $c6 := $MkComposite($Heap..nextReference!($heap), Exn$TypeTag);
    $heap := $MkHeap($Heap..data!($heap), int.add($Heap..nextReference!($heap), 1));
    $exv := $c6;
    goto $catch$exn0;
  }
  $catch_dispatch$1: {
    $c10 := $Composite..typeTag!($c0) == Special$TypeTag;
    branch ($c10) goto $catch$11 else goto $catch_next$12;
  }
  $catch$11: {
    r := 2;
    goto $try_end$4;
  }
  $catch_next$12: {
    r := 1;
    goto $try_end$4;
  }
  $try_end$4: {
    goto $return;
  }
  $return: {
    return;
  }
};
type check: ok
-/
#guard_msgs in
#eval printCortexCoreCFG (procs := ["typedCatch"]) <|
#strata
program Laurel;
composite Exn { var code: int }
composite Special extends Exn { }
procedure typedCatch() returns (r: int)
  opaque
  modifies *
{
    try {
      var x: Exn := new Exn;
      throw x
    } catch err when err is Special {
      r := 2
    } catch err2 {
      r := 1
    }
};
#end

-- A callee that throws: its body sets the exception outputs and jumps to the
-- exit block. The caller propagates an exception that it does not catch.
/--
info: procedure thrower (inout $heap : $Heap, out $thrown : bool, out $exc : $Composite)
cfg $cteEntry {
  $cteEntry: {
    goto $heapEntry;
  }
  $heapEntry: {
    goto $exnEntry;
  }
  $exnEntry: {
    var $exv : $Composite;
    var $callThrown : bool;
    var $callExc : $Composite;
    var $exnTest : bool;
    $thrown := false;
    goto $entry;
  }
  $exnExit: {
    return;
  }
  $entry: {
    var $c0 : $Composite;
    assume [constraint_Exn_0]: $Composite..typeTag!($c0) == Exn$TypeTag;
    goto $start;
  }
  $uncaught$exn0: {
    $exc := $exv;
    $thrown := true;
    goto $exnExit;
  }
  $start: {
    $c0 := $MkComposite($Heap..nextReference!($heap), Exn$TypeTag);
    $heap := $MkHeap($Heap..data!($heap), int.add($Heap..nextReference!($heap), 1));
    $exv := $c0;
    goto $uncaught$exn0;
  }
};
procedure propagates (inout $heap : $Heap, out r : int, out $thrown : bool, out $exc : $Composite)
cfg $cteEntry {
  $cteEntry: {
    goto $heapEntry;
  }
  $heapEntry: {
    var $heapNextSnap : int;
    goto $exnEntry;
  }
  $exnEntry: {
    var $exv : $Composite;
    var $callThrown : bool;
    var $callExc : $Composite;
    var $exnTest : bool;
    $thrown := false;
    goto $entry;
  }
  $exnExit: {
    return;
  }
  $entry: {
    goto $start;
  }
  $uncaught$exn0: {
    $exc := $exv;
    $thrown := true;
    goto $exnExit;
  }
  $raise$exn1: {
    $exv := $callExc;
    goto $uncaught$exn0;
  }
  $start: {
    $heapNextSnap := $Heap..nextReference!($heap);
    call thrower(out $callThrown, out $callExc, inout $heap);
    assume [heapMonotone]: int.le($heapNextSnap, $Heap..nextReference!($heap));
    assume [allocated]: int.lt($Composite..ref!($callExc), $Heap..nextReference!($heap));
    branch ($callThrown) goto $raise$exn1 else goto $noThrow$exn2;
  }
  $noThrow$exn2: {
    r := 1;
    goto $return;
  }
  $return: {
    return;
  }
};
type check: ok
-/
#guard_msgs in
#eval printCortexCoreCFG (procs := ["thrower", "propagates"]) <|
#strata
program Laurel;
composite Exn { var code: int }
procedure thrower()
  throws (e: Exn)
  opaque
  modifies *
{
    var ex: Exn := new Exn;
    throw ex
};
procedure propagates() returns (r: int)
  throws (e: Exn)
  opaque
  modifies *
{
    thrower();
    r := 1
};
#end

-- try/catch in a loop: the handler blocks are on the loop's cycle, and every
-- local is declared before the loop.
/--
info: procedure catchInLoop (inout $heap : $Heap, out r : int)
cfg $cteEntry {
  $cteEntry: {
    goto $heapEntry;
  }
  $heapEntry: {
    var $heapNextSnap : int;
    goto $exnEntry;
  }
  $exnEntry: {
    var $exv : $Composite;
    var $callThrown : bool;
    var $callExc : $Composite;
    var $exnTest : bool;
    goto $entry;
  }
  $entry: {
    var hit : int;
    var i : int;
    var $c6 : $Composite;
    goto $start;
  }
  $start: {
    hit := 0;
    i := 0;
    goto $loop_head$3;
  }
  $loop_head$3: {
    branch (int.lt(i, 2)) goto $loop_body$4 else goto $loop_exit$5;
  }
  $loop_body$4: {
    goto $region$11;
  }
  $catch$exn0: {
    $c6 := $exv;
    goto $catch_dispatch$7;
  }
  $raise$exn1: {
    $exv := $callExc;
    goto $catch$exn0;
  }
  $region$11: {
    $heapNextSnap := $Heap..nextReference!($heap);
    call thrower(out $callThrown, out $callExc, inout $heap);
    assume [heapMonotone]: int.le($heapNextSnap, $Heap..nextReference!($heap));
    assume [allocated]: int.lt($Composite..ref!($callExc), $Heap..nextReference!($heap));
    branch ($callThrown) goto $raise$exn1 else goto $noThrow$exn2;
  }
  $noThrow$exn2: {
    goto $region$12;
  }
  $region$12: {
    goto $try_end$10;
  }
  $catch_dispatch$7: {
    hit := int.add(hit, 1);
    goto $try_end$10;
  }
  $try_end$10: {
    i := int.add(i, 1);
    goto $loop_head$3;
  }
  $loop_exit$5: {
    r := hit;
    goto $return;
  }
  $return: {
    return;
  }
};
type check: ok
-/
#guard_msgs in
#eval printCortexCoreCFG (procs := ["catchInLoop"]) <|
#strata
program Laurel;
composite Exn { var code: int }
procedure thrower()
  throws (e: Exn)
  opaque
  modifies *
{
    var ex: Exn := new Exn;
    throw ex
};
procedure catchInLoop() returns (r: int)
  opaque
  modifies *
{
    var hit: int := 0;
    var i: int := 0;
    while (i < 2) {
      try { thrower() } catch e { hit := hit + 1 };
      i := i + 1
    };
    r := hit
};
#end

-- A procedure without a body keeps its structured body, next to a procedure
-- with a CFG body that calls it.
/--
info: procedure declared (x : int, inout $heap : $Heap, out r : int)
{
  assume [assume_true]: true;
};
procedure callsDeclared (x : int, inout $heap : $Heap, out r : int)
cfg $heapEntry {
  $heapEntry: {
    var $heapNextSnap : int;
    goto $exnEntry;
  }
  $exnEntry: {
    goto $entry;
  }
  $entry: {
    goto $start;
  }
  $start: {
    $heapNextSnap := $Heap..nextReference!($heap);
    call declared(x, out r, inout $heap);
    assume [heapMonotone]: int.le($heapNextSnap, $Heap..nextReference!($heap));
    goto $return;
  }
  $return: {
    return;
  }
};
type check: ok
-/
#guard_msgs in
#eval printCortexCoreCFG (procs := ["declared", "callsDeclared"]) <|
#strata
program Laurel;
procedure declared(x: int) returns (r: int);
procedure callsDeclared(x: int) returns (r: int)
  opaque
{
    r := declared(x)
};
#end
