/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Shows what the file-scope global variable encoding looks like after the
`GlobalParameterization` pass. Globals are eliminated by threading them
through procedure signatures:

- a procedure that only *reads* a global gains an extra input parameter;
- a procedure that *writes* a global gains both an input and a same-named
  output (an "inout" parameter), so the updated value flows back to callers;
- call sites thread the caller's copy of the state: calls to writers become
  assignments (`g := writer(g)`), and a writer call in *value* position is
  rewritten into a block expression that first captures the hidden outputs
  (`assign g, var $g_tmp0: int := f(g); $g_tmp0`) and then yields the original
  result.

The first four fixtures are the encoding itself, printed without the
`staticFields:` count so the threaded signatures read cleanly. Everything after
them pins a structural edge case of the same rewrite — generated-name collisions,
recursion, shadowing, loop bodies, and argument evaluation order. Those print the
count as well, since a global that failed to be eliminated shows up there first.

The last group starts from a `#strata` program like the rest, but its helper
then needs something beyond parse-resolve-run-one-pass-and-print: it adds a
declaration the surface grammar has no syntax for — a `constants` initializer
referring to a global — the way a front end would.

The pass also rewrites the contract metadata slots (`modifies`, `invokeOn`) that
mention a global, but none of that is checked here. A count of translation
diagnostics only reports that translation did not fail, which it does whether or
not the metadata survived; those cases are source programs in
`EndToEndTests/Verification/Fundamentals/InvokeOn.lean` instead, where deleting a
clause changes the verdict.

This test does NOT use the shared `runPassForIdiomaticity` driver: reaching
`GlobalParameterization`'s input takes `EliminateValueInReturns` and a
re-resolve first, which is more than the one-pass-after-resolve the driver runs, and several
fixtures also print the `staticFields:` count rather than only the program. The
`printGlobalParameterization` helper in `Tests/Util/TestLaurel.lean` carries that
multi-step flow.
-/

import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.GlobalParameterization
import StrataLaurel.Implementation.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

private def printGlobalParam := printGlobalParameterization false

private def testGlobalParam := printGlobalParameterization true

private def testRejectsGlobalConstant (transitive : Bool)
    (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let initializer : StmtExprMd := if transitive then
    ⟨.StaticCall (mkId "readG") [] [], default⟩
  else
    ⟨.Var (.Local (mkId "g")), default⟩
  let withConstant := { laurelProgram with constants := [{
    name := mkId "globalConstant"
    type := ⟨.TInt, default⟩
    initializer := some initializer
  }] }
  for diagnostic in (resolve (withBuiltins withConstant)).errors do
    IO.println s!"resolution diagnostic: {diagnostic.message}"

/-! ## The encoding: readers get inputs, writers get inout parameters -/

/--
info: procedure outer(someGlobal: int)
  returns (someGlobal: int)
{
  someGlobal := writer(someGlobal);
  var x: int := reader(someGlobal)
};
procedure writer(someGlobal: int)
  returns (someGlobal: int)
{
  someGlobal := 3
};
procedure reader(someGlobal: int)
  returns (r: int)
{
  r := someGlobal + 1;
  return
};
-/
#guard_msgs in
#eval printGlobalParam <|
#strata
program Laurel;
var someGlobal: int := 0
procedure outer() {
  writer();
  var x: int := reader()
};
procedure writer() {
  someGlobal := 3
};
procedure reader() returns (r: int) {
  return someGlobal + 1
};
#end

/--
info: procedure bump(g: int)
  returns (g: int, r: int)
{
  g := g + 1;
  r := g;
  return
};
procedure useValue(g: int)
  returns (g: int, r: int)
{
  r := {
    assign g, var $g_tmp0: int := bump(g);
    $g_tmp0
  } + 1;
  return
};
-/
#guard_msgs in
#eval printGlobalParam <|
#strata
program Laurel;
var g: int := 0
procedure bump() returns (r: int) {
  g := g + 1;
  return g
};
procedure useValue() returns (r: int) {
  return bump() + 1
};
#end

/--
info: procedure writesA(a: int)
  returns (a: int)
{
  a := 1
};
procedure readsB(b: int)
  returns (r: int)
{
  r := b;
  return
};
procedure both(a: int, b: int)
  returns (a: int, r: int)
{
  a := writesA(a);
  r := readsB(b);
  return
};
-/
#guard_msgs in
#eval printGlobalParam <|
#strata
program Laurel;
var a: int := 0
var b: int := 0
procedure writesA() {
  a := 1
};
procedure readsB() returns (r: int) {
  return b
};
procedure both() returns (r: int) {
  writesA();
  return readsB()
};
#end

/--
info: procedure main()
  entry
  opaque
{
  var someGlobal: int := 0;
  var other: bool := true;
  {
    someGlobal := writer(someGlobal);
    var x: int := reader(someGlobal);
    assert other
  }
};
procedure writer(someGlobal: int)
  returns (someGlobal: int)
{
  someGlobal := 3
};
procedure reader(someGlobal: int)
  returns (r: int)
{
  r := someGlobal + 1;
  return
};
-/
#guard_msgs in
#eval printGlobalParam <|
#strata
program Laurel;
var someGlobal: int := 0
var other: bool := true
procedure main()
  entry
  opaque
{
  writer();
  var x: int := reader();
  assert other
};
procedure writer() {
  someGlobal := 3
};
procedure reader() returns (r: int) {
  return someGlobal + 1
};
#end
/-! ## Structural edge cases of the same rewrite

These print the `staticFields:` count as well: a global the pass failed to
eliminate shows up there before it shows up in a signature. -/

/-! Multiple hidden outputs preserve declaration order for discarded and consumed calls. -/

/--
info: staticFields: 0
procedure writeBoth(a: int, b: int, v: int)
  returns (a: int, b: int, r: int)
{
  a := v;
  b := v + 1;
  r := a + b;
  return
};
procedure useBoth(a: int, b: int)
  returns (a: int, b: int, r: int)
{
  assign a, b, var $g_tmp0: int := writeBoth(a, b, 1);
  r := {
    assign a, b, var $g_tmp1: int := writeBoth(a, b, 2);
    $g_tmp1
  };
  return
};
-/
#guard_msgs in
#eval testGlobalParam <|
#strata
program Laurel;
var a: int := 0
var b: int := 0
procedure writeBoth(v: int) returns (r: int) {
  a := v;
  b := v + 1;
  return a + b
};
procedure useBoth() returns (r: int) {
  writeBoth(1);
  return writeBoth(2)
};
#end

/-! Explicit assignment to a written global consumes the call's value. -/

/--
info: staticFields: 0
procedure setAndGet(g: int, v: int)
  returns (g: int, r: int)
{
  g := v;
  r := v;
  return
};
procedure useIt(g: int)
  returns (g: int)
  opaque
{
  g := {
    assign g, var $g_tmp0: int := setAndGet(g, 5);
    $g_tmp0
  };
  assert g == 5
};
-/
#guard_msgs in
#eval testGlobalParam <|
#strata
program Laurel;
var g: int := 0
procedure setAndGet(v: int) returns (r: int) {
  g := v;
  return v
};
procedure useIt() opaque {
  g := setAndGet(5);
  assert g == 5
};
#end

/-! Existing binders keep their names; only the threaded global is renamed. -/

/--
info: staticFields: 0
procedure inc(g: int)
  returns (g: int)
  opaque
{
  g := g + 1
};
procedure withParameter($global_g: int, g: int)
  returns ($global_g: int)
  opaque
{
  $global_g := inc($global_g)
};
procedure withLocal($global_g: int)
  returns ($global_g: int)
  opaque
{
  var g: int := 7;
  $global_g := inc($global_g)
};
-/
#guard_msgs in
#eval testGlobalParam <|
#strata
program Laurel;
var g: int := 0
procedure inc() opaque {
  g := g + 1
};
procedure withParameter(g: int) opaque {
  inc()
};
procedure withLocal() opaque {
  var g: int := 7;
  inc()
};
#end

/-! Loop bodies and invariants receive the same threaded state. -/

/--
info: staticFields: 0
procedure bump(g: int)
  returns (g: int)
{
  g := g + 1
};
procedure loop(g: int, n: int)
  returns (g: int)
  opaque
{
  var i: int := 0;
  while(i < n)
    invariant i <= n {
    g := bump(g);
    i := i + 1
  }
};
-/
#guard_msgs in
#eval testGlobalParam <|
#strata
program Laurel;
var g: int := 0
procedure bump() {
  g := g + 1
};
procedure loop(n: int) opaque {
  var i: int := 0;
  while (i < n)
    invariant i <= n {
    bump();
    i := i + 1
  }
};
#end

/-! Assignments in value position preserve the source value. -/

/--
info: staticFields: 0
procedure weird(g: int)
  returns (g: int, r: int)
  opaque
{
  g := 100;
  r := 7;
  return
};
procedure useAssign(g: int)
  returns (g: int, r: int)
  opaque
{
  var x: int := 0;
  r := (x := {
    assign g, var $g_tmp0: int := weird(g);
    $g_tmp0
  }) + 1;
  return
};
-/
#guard_msgs in
#eval testGlobalParam <|
#strata
program Laurel;
var g: int := 0
procedure weird() returns (r: int) opaque {
  g := 100;
  return 7
};
procedure useAssign() returns (r: int) opaque {
  var x: int := 0;
  return (x := weird()) + 1
};
#end

/-! Effectful explicit arguments finish before hidden globals are sampled. -/

/--
info: staticFields: 0
procedure writeAndReturn(g: int, v: int)
  returns (g: int, r: int)
{
  g := v;
  r := v;
  return
};
procedure readAfter(g: int, x: int)
  returns (r: int)
{
  r := g + x;
  return
};
procedure caller(g: int)
  returns (g: int, r: int)
{
  r := {
    var $g_tmp1: int := {
      assign g, var $g_tmp0: int := writeAndReturn(g, 5);
      $g_tmp0
    };
    readAfter(g, $g_tmp1)
  };
  return
};
-/
#guard_msgs in
#eval testGlobalParam <|
#strata
program Laurel;
var g: int := 0
procedure writeAndReturn(v: int) returns (r: int) {
  g := v;
  return v
};
procedure readAfter(x: int) returns (r: int) {
  return g + x
};
procedure caller() returns (r: int) {
  return readAfter(writeAndReturn(5))
};
#end

/-! Generated global aliases retry when the first candidate is already bound. -/

/--
info: staticFields: 0
procedure inc(g: int)
  returns (g: int)
  opaque
{
  g := g + 1
};
procedure collides($global_g_1: int, g: int)
  returns ($global_g_1: int)
  opaque
{
  var $global_g: int := 0;
  $global_g_1 := inc($global_g_1)
};
-/
#guard_msgs in
#eval testGlobalParam <|
#strata
program Laurel;
var g: int := 0
procedure inc() opaque { g := g + 1 };
procedure collides(g: int) opaque {
  var $global_g: int := 0;
  inc()
};
#end

/-! A quantifier binder counts too, and nothing else here notices: the pass splices the alias
    into the binder's scope, so drop that arm and `$global_g_1` below is `$global_g` -- the
    read is of the bound variable, not the global. -/

/--
info: staticFields: 0
procedure readsUnderBinder($global_g_1: int)
  returns (r: bool)
  opaque
{
  r := forall($global_g: int) => $global_g_1 > 0;
  var g: int := 1;
  assert g == 1
};
-/
#guard_msgs in
#eval testGlobalParam <|
#strata
program Laurel;
var g: int := 0
procedure readsUnderBinder() returns (r: bool) opaque {
  r := forall($global_g: int) => g > 0;
  var g: int := 1;
  assert g == 1
};
#end

/-! Generated argument temporaries retry around source-local names. -/

/--
info: staticFields: 0
procedure writeAndReturn(g: int, v: int)
  returns (g: int, r: int)
{
  g := v;
  r := v;
  return
};
procedure readAfter(g: int, x: int)
  returns (r: int)
{
  r := g + x;
  return
};
procedure tempCollides(g: int)
  returns (g: int, r: int)
{
  r := {
    var $g_tmp0: int := 0;
    var $g_tmp2: int := {
      assign g, var $g_tmp1: int := writeAndReturn(g, 5);
      $g_tmp1
    };
    readAfter(g, $g_tmp2)
  };
  return
};
-/
#guard_msgs in
#eval testGlobalParam <|
#strata
program Laurel;
var g: int := 0
procedure writeAndReturn(v: int) returns (r: int) {
  g := v;
  return v
};
procedure readAfter(x: int) returns (r: int) {
  return g + x
};
procedure tempCollides() returns (r: int) {
  return {
    var $g_tmp0: int := 0;
    readAfter(writeAndReturn(5))
  }
};
#end

/-! Recursive writers thread the same inout global through self-calls. -/

/--
info: staticFields: 0
procedure recur(g: int, n: int)
  returns (g: int)
  opaque
{
  if n > 0
    then {
      g := g + 1;
      g := recur(g, n - 1)
    }
};
-/
#guard_msgs in
#eval testGlobalParam <|
#strata
program Laurel;
var g: int := 0
procedure recur(n: int) opaque {
  if n > 0 then {
    g := g + 1;
    recur(n - 1)
  }
};
#end
/-! ## Cases the one-pass-and-print shape cannot express

Each `#strata` block below is an ordinary Laurel program — the bespoke part is what its helper
does with it afterwards. It injects a declaration the surface grammar has no syntax for, which
is why the thing under test appears in no snippet: `testRejectsGlobalConstant` adds a `constant` whose initializer
references a global (the rejected `globalConstant`).

The pass also rewrites the contract metadata slots that mention a global — `modifies`, and an
`invokeOn` trigger — but none of that is checked here. Counting translation diagnostics would
report success whether or not the metadata survived, so those cases are source programs in
`EndToEndTests/Verification/Fundamentals/InvokeOn.lean`, where deleting a clause changes the
verdict. That includes the quantified `invokeOn` over a constrained-type global, whose
SMT-encoding failure is pinned inline there. -/

/-! Constant initializers reject direct and transitive global dependencies. -/

/--
info: resolution diagnostic: constant initializer 'globalConstant' cannot depend on file-scope globals
-/
#guard_msgs in
#eval testRejectsGlobalConstant false <|
#strata
program Laurel;
var g: int := 0
procedure readG() returns (r: int) { return g };
#end

/--
info: resolution diagnostic: constant initializer 'globalConstant' cannot depend on file-scope globals
-/
#guard_msgs in
#eval testRejectsGlobalConstant true <|
#strata
program Laurel;
var g: int := 0
procedure readG() returns (r: int) { return g };
#end

/--
info: procedure bump<T>(g: int, x: T)
  returns (g: int, r: T)
{
  g := g + 1;
  r := x;
  return
};
procedure useTwo(g: int)
  returns (g: int, r: int)
{
  var a: int := {
    assign g, var $g_tmp0: int := bump(g, 5);
    $g_tmp0
  };
  var b: bool := {
    assign g, var $g_tmp1: bool := bump(g, true);
    $g_tmp1
  };
  r := a;
  return
};
-/
#guard_msgs in
#eval printGlobalParam <|
#strata
program Laurel;
var g: int := 0
procedure bump<T>(x: T) returns (r: T) {
  g := g + 1;
  return x
};
procedure useTwo() returns (r: int) {
  var a: int := bump(5);
  var b: bool := bump(true);
  return a
};
#end

end Strata.Laurel
