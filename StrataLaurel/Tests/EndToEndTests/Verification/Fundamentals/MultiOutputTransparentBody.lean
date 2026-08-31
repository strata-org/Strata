/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Transparent bodies with several outputs

Each case asserts both what is provable and — with an intentionally failing
assertion — what is not, so none can pass vacuously. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;

// Named-output assignment, the pre-existing way to fill several outputs.
procedure divmod(a: int, b: int) returns (q: int, r: int)
  requires b > 0
{
  q := a / b;
  r := a - q * b
};

// A transparent caller that binds both outputs. The call is rewritten to one call
// yielding the packaged value plus one projection per target.
procedure divmodSum(a: int, b: int) returns (s: int)
  requires b > 0
{
  var q: int;
  var r: int;
  assign q, r := divmod(a, b);
  return q + r
};

procedure testDivmod() opaque {
  assert divmodSum(7, 2) == 4;
  assert divmodSum(7, 2) == 5
//^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// A valued return supplies one value per output.
procedure swap(a: int, b: int) returns (x: int, y: int)
{
  return b, a
};

procedure swapFirst(a: int, b: int) returns (r: int)
{
  var x: int;
  var y: int;
  assign x, y := swap(a, b);
  return x
};

procedure testSwap() opaque {
  assert swapFirst(1, 2) == 2;
  assert swapFirst(1, 2) == 1
//^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// A valued return that reads the outputs themselves: the values are written
// simultaneously, so this really swaps rather than duplicating the first write.
procedure swapOutputs() returns (p: int, q: int)
{
  p := 1;
  q := 2;
  return q, p
};

procedure swapOutputsFirst() returns (r: int)
{
  var p: int;
  var q: int;
  assign p, q := swapOutputs();
  return p
};

procedure testSwapOutputs() opaque {
  assert swapOutputsFirst() == 2;
  assert swapOutputsFirst() == 1
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// An early exit in a multi-output body: the multi-value return is the value of
// every exit, so both branches yield both outputs.
procedure clampBoth(x: int) returns (lo: int, hi: int)
{
  if x < 0 then {
    lo := 0;
    hi := 0;
    return lo, hi
  };
  lo := x;
  hi := x + 1
};

procedure clampBothSum(x: int) returns (s: int)
{
  var lo: int;
  var hi: int;
  assign lo, hi := clampBoth(x);
  return lo + hi
};

procedure testClampBoth() opaque {
  assert clampBothSum(-5) == 0;
  assert clampBothSum(3) == 7;
  assert clampBothSum(3) == 6
//^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// An output no path assigns holds an arbitrary-but-fixed value, exactly as with a
// single output: equal to itself, but not provably any particular value.
procedure onlyFirst(a: int) returns (p: int, q: int)
{
  p := a
};

procedure onlyFirstSecond(a: int) returns (r: int)
{
  var p: int;
  var q: int;
  assign p, q := onlyFirst(a);
  return q
};

procedure testOnlyFirst() opaque {
  assert onlyFirstSecond(1) == onlyFirstSecond(1);
  assert onlyFirstSecond(1) == 0
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// An *inout* — an output sharing an input's name, which resolution binds to the same
// variable. It is neither re-declared nor holed: the parameter already holds the value it
// starts out with, and assigning it is an ordinary output write rather than a destructive
// write to an input. This holds with a single output too, so it is tested on its own.
procedure incr(x: int) returns (x: int)
{
  x := x + 1
};

procedure testIncr() opaque {
  assert incr(3) == 4;
  assert incr(3) == 5
//^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// An inout among several outputs: the packaging datatype's first field is the inout,
// so the value read back out is the assigned one and not the incoming argument.
procedure bumpAndDouble(x: int, y: int) returns (x: int, d: int)
{
  x := x + 1;
  d := y * 2
};

procedure bumpAndDoubleSum(a: int, b: int) returns (s: int)
{
  var x: int;
  var d: int;
  assign x, d := bumpAndDouble(a, b);
  return x + d
};

procedure testBumpAndDouble() opaque {
  assert bumpAndDoubleSum(1, 5) == 12;
  assert bumpAndDoubleSum(1, 5) == 11
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// A multi-output body that itself destructures a multi-output call: both `inner` and
// `outer` get their own datatype, so the projection rewrite, the hole prelude and the
// packaging constructor all compose in one body.
procedure inner() returns (a: int, b: int)
{
  a := 1;
  b := 2
};

procedure outer() returns (p: int, q: int)
{
  var x: int;
  var y: int;
  assign x, y := inner();
  p := x + 1;
  q := y + 1
};

procedure outerSum() returns (s: int)
{
  var p: int;
  var q: int;
  assign p, q := outer();
  return p * 10 + q
};

procedure testNested() opaque {
  assert outerSum() == 23;
  assert outerSum() == 32
//^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// Two multi-output calls in one body. Each rewrite declares its own temporary for the
// packaged value in the block that held the call, so the two must be named apart —
// `$callOutputs_0` and `$callOutputs_1` — rather than declare one name twice.
procedure twoCallsInOneBody() returns (s: int)
{
  var a: int;
  var b: int;
  assign a, b := inner();
  var c: int;
  var d: int;
  assign c, d := swap(a, b);
  return c * 10 + d
};

procedure testTwoCallsInOneBody() opaque {
  assert twoCallsInOneBody() == 21;
  assert twoCallsInOneBody() == 12
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// The *declaring* form of the assignment: each target is declared by the assignment
// rather than pre-declared above it. The bind and the projections replace the assignment
// where it stood, so `q` and `r` are declared in the enclosing block and the statements
// after it can read them.
procedure divmodSumDeclaring(a: int, b: int) returns (s: int)
  requires b > 0
{
  assign var q: int, var r: int := divmod(a, b);
  return q + r
};

procedure testDivmodDeclaring() opaque {
  assert divmodSumDeclaring(7, 2) == 4;
  assert divmodSumDeclaring(7, 2) == 5
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// Two *declaring* calls in one block: the collision case and the declaring case at
// once. Both replacements are flattened into the same block, so the temporaries holding
// the two packaged values are siblings rather than nested and the per-call-site
// numbering is the only thing keeping them apart.
procedure twoDeclaringCallsInOneBody() returns (s: int)
{
  assign var a: int, var b: int := inner();
  assign var c: int, var d: int := swap(a, b);
  return c * 10 + d
};

procedure testTwoDeclaringCalls() opaque {
  assert twoDeclaringCallsInOneBody() == 21;
  assert twoDeclaringCallsInOneBody() == 12
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// Three outputs, not two. The packaging is list-based throughout — the constructor takes
// one argument per output and the call site projects one per target — so a pair is the
// minimal case rather than the general one. Each output is pinned separately via
// place value, so no permutation of the three satisfies the assertion.
procedure threeOuts(n: int) returns (a: int, b: int, c: int)
{
  a := n;
  b := n + 1;
  c := n + 2
};

procedure threeOutsPacked(n: int) returns (r: int)
{
  var a: int;
  var b: int;
  var c: int;
  assign a, b, c := threeOuts(n);
  return a * 100 + b * 10 + c
};

procedure testThreeOuts() opaque {
  assert threeOutsPacked(1) == 123;
  assert threeOutsPacked(1) == 321
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// A multi-output call from an *opaque* body. `packAndSwap` is transparent and holds no
// assert or assume, so `needsProcTwin` is false: it has no imperative twin, its function
// copy keeps the plain name, and the call below already names the packaged function. So
// the call-site rewrite has to reach an opaque implementation too, not only a function's
// body — otherwise the call binds two targets from a callee that now yields one packaged
// value, and the pass boundary re-resolves to
// "expected '(int, int)', got '$outputs_packAndSwap'".
procedure packAndSwap() returns (x: int, y: int)
{
  return 2, 3
};

procedure testPackAndSwapFromOpaque() opaque {
  var a: int;
  var b: int;
  assign a, b := packAndSwap();
  assert a == 2;
  assert b == 3;
  assert a == 3
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A multi-output callee *with* an imperative twin -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;

procedure twinnedSwap() returns (x: int, y: int)
{
  assert 1 == 1;
  return 2, 3
};

procedure testTwinnedSwapFromOpaque() opaque {
  var a: int;
  var b: int;
  assign a, b := twinnedSwap();
  assert a == 2;
  assert b == 3;
  assert a == 3
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A return must supply one value per declared output -/

#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;

procedure tooFewValues() returns (p: int, q: int)
{
  return 1
//^^^^^^^^ error: procedure declares 2 outputs, so 'return' takes 2 values, not 1
};

procedure tooManyValues() returns (p: int)
{
  return 1, 2
//^^^^^^^^^^^ error: procedure declares 1 outputs, so 'return' takes 1 values, not 2
};

procedure voidReturnsValues()
{
  return 1, 2
//^^^^^^^^^^^ error: void procedure cannot return a value
};

// The same arity error with more than one declared output, so the counts in the
// message are both plural.
procedure tooManyForTwo() returns (p: int, q: int)
{
  return 1, 2, 3
//^^^^^^^^^^^^^^ error: procedure declares 2 outputs, so 'return' takes 2 values, not 3
};
#end

/-! ## A multi-output call in a pure context must bind one target per output -/

#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;

procedure twoOuts() returns (p: int, q: int)
{
  p := 1;
  q := 2
};

procedure callInValuePosition() returns (r: int)
{
  return twoOuts()
//       ^^^^^^^^^ error: expected 'int', got '(int, int)'
//       ^^^^^^^^^ error: calling multi-output procedure 'twoOuts' is not supported from a transparent procedure or contract: such a call must assign one target per output
};
#end

/-! ## An opaque callee's outputs are packaged too

The failing assertion is that the two outputs are equal: it must be refutable, which is
what shows the two destructors project *different* fields rather than both landing on
the first. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;

procedure opaqueTwoOuts(k: int) returns (a: int, b: int) opaque;

procedure opaqueSum(k: int) returns (s: int)
{
  var a: int;
  var b: int;
  assign a, b := opaqueTwoOuts(k);
  return a + b
};

procedure opaqueFirst(k: int) returns (r: int)
{
  var a: int;
  var b: int;
  assign a, b := opaqueTwoOuts(k);
  return a
};

procedure opaqueSecond(k: int) returns (r: int)
{
  var a: int;
  var b: int;
  assign a, b := opaqueTwoOuts(k);
  return b
};

procedure testOpaqueTwoOuts() opaque {
  assert opaqueSum(3) == opaqueFirst(3) + opaqueSecond(3);
  assert opaqueFirst(3) == opaqueSecond(3)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// The declaring form against an opaque callee. Nothing is known about either output, so what is provable is only that the
// projections decompose one value — but that is already more than the declaring form
// could express at all, since `x` and `y` were undefined from the next statement on.
procedure opaquePair() returns (a: int, b: int) opaque;

procedure opaquePairSum() returns (s: int)
{
  assign var x: int, var y: int := opaquePair();
  return x + y
};

procedure opaquePairFirst() returns (r: int)
{
  assign var x: int, var y: int := opaquePair();
  return x
};

procedure opaquePairSecond() returns (r: int)
{
  assign var x: int, var y: int := opaquePair();
  return y
};

procedure testOpaquePairDeclaring() opaque {
  assert opaquePairSum() == opaquePairFirst() + opaquePairSecond();
  assert opaquePairFirst() == opaquePairSecond()
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// Outputs of different types: the datatype's fields are typed one per output, so the
// `bool` projection only type-checks if it is wired to the `bool` field.
procedure opaqueMixed(k: int) returns (n: int, ok: bool) opaque;

procedure opaqueMixedFlag(k: int) returns (r: bool)
{
  var n: int;
  var ok: bool;
  assign n, ok := opaqueMixed(k);
  return ok
};

procedure testOpaqueMixed() opaque {
  assert opaqueMixedFlag(3) == opaqueMixedFlag(3);
  assert opaqueMixedFlag(3)
//^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A polymorphic body with several outputs

The generated datatype takes the procedure's own type parameters, so the packed output is
typed `$outputs_polyTwoOuts<T>`. The temporary a destructuring call site binds is declared
with no type annotation, which is what lets the re-resolve name the instantiation the pass
itself cannot see. Each output is pinned separately via place value, so no permutation of
the two satisfies the assertion. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;

procedure polyTwoOuts<T>(a: T, b: T) returns (p: T, q: T)
{
  p := b;
  q := a
};

procedure polyTwoOutsFirst(a: int, b: int) returns (r: int)
{
  var p: int;
  var q: int;
  assign p, q := polyTwoOuts(a, b);
  return p * 10 + q
};

procedure testPolyTwoOuts() opaque {
  assert polyTwoOutsFirst(1, 2) == 21;
  assert polyTwoOutsFirst(1, 2) == 12
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## One polymorphic callee destructured at two different types

The datatype is declared once for the callee, generic in its `T`, and each call site
packages at its own instantiation — `int` in `swapInts`, `bool` in `swapBools`. This is
what the unannotated temporary buys: were the instantiation fixed where the datatype is
declared, or named by the pass from the callee's declared `T`, one of the two sites could
not resolve. The `bool` case also pins that the projections are typed per field, since a
`bool` target only type-checks against a `bool` field. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;

procedure polySwap<T>(a: T, b: T) returns (x: T, y: T)
{
  return b, a
};

procedure swapInts(a: int, b: int) returns (r: int)
{
  var x: int;
  var y: int;
  assign x, y := polySwap(a, b);
  return x * 10 + y
};

procedure swapBools(a: bool, b: bool) returns (r: bool)
{
  var x: bool;
  var y: bool;
  assign x, y := polySwap(a, b);
  return x && !y
};

procedure testTwoInstantiations() opaque {
  assert swapInts(1, 2) == 21;
  assert swapBools(false, true);
  assert swapBools(true, false)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A polymorphic output left unassigned on one path

On the path that never assigns `r`, the result is the output's hole: arbitrary, but fixed
for the same arguments. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;

procedure polyMaybe<T>(x: T, b: bool) returns (r: T)
{
  if b then { r := x }
};

procedure polyMaybeAssigned() opaque
{
  var r: int := polyMaybe(5, true);
  assert r == 5
};

procedure polyMaybeUnassignedIsFixed() opaque
{
  var r1: int := polyMaybe(5, false);
  var r2: int := polyMaybe(5, false);
  assert r1 == r2;
  assert r1 == 5
//^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A multi-output callee that also touches a global

`GlobalParameterization.transformAssignWithCall` threads the written global through the
call and prepends a hidden receiver for it to the destructuring target list, in the
callee's output order, so the call site binds the global's new value alongside the two
ordinary outputs. The write reaching the caller is the substantive part, so `g` is
asserted as well as the outputs. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;

var g: int := 0

procedure writesGlobal() returns (a: int, b: int)
{
  g := 1;
  a := 1;
  b := 2
};

procedure callsWritesGlobal() opaque
{
  var x: int;
  var y: int;
  assign x, y := writesGlobal();
  assert x == 1;
  assert y == 2;
  assert g == 1;
  assert x == 2
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## The write survives a *transparent* caller

The case above has one transparent level: the writer's caller is opaque, so the
threaded receiver lands at statement level in an imperative body. Add a transparent
wrapper between them and the write has to cross a block-valued initializer, because
that is how `GlobalParameterization` lowers a call in a value position:

    var x: int := { assign g, var $tmp: int := writesGlobal(); $tmp }

`FunctionalRewrite` turns the `g := …` inside that block into a shadowing
declaration, which has to stay in scope for everything after the block — the
packaged-output constructor included, which would otherwise read the incoming `g`.

Both directions are pinned here, through two levels of transparent wrapper, so
neither can pass by the clause being dropped. `wrapsWriter` has a single declared
output, so this is not about multi-output packaging: it covers any transparent global
writer reached through a transparent caller. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;

var g: int := 0

procedure writesGlobal() returns (a: int, b: int)
{
  g := 1;
  a := 1;
  b := 2
};

procedure wrapsWriter() returns (r: int)
{
  var x: int;
  var y: int;
  assign x, y := writesGlobal();
  r := x + y
};

procedure wrapsWrapper() returns (r: int)
{
  var s: int := wrapsWriter();
  r := s
};

procedure writesGlobalThroughWrapper() opaque
{
  g := 0;
  var s: int := wrapsWrapper();
  assert s == 3;
  assert g == 1;
  assert g == 0
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A single-output transparent global writer, reached transparently

The same shape without any multi-output procedure in sight. `setG` declares one
output; the second is the global the pass threads in. Asserting the *incoming* value
pins that the write is not a pass-through: after a call that sets `g := 5`, `g == 7`
is refuted. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;

var g: int := 0

procedure setG(v: int) returns (r: int)
{
  g := v;
  r := 0
};

procedure wrapsSetG(v: int) returns (r: int)
{
  var x: int := setG(v);
  r := x
};

procedure callsWrapsSetG() opaque
{
  g := 7;
  var s: int := wrapsSetG(5);
  assert g == 5;
  assert g == 7
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A polymorphic multi-output callee that writes a global

`polySetG` is generic in its outputs and also writes `g`, called both directly from an
opaque caller and through a transparent wrapper. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;

var g: int := 0

procedure polySetG<T>(v: T, n: int) returns (a: T, b: T)
{
  g := n;
  a := v;
  b := v
};

procedure wrapsPolySetG(v: int, n: int) returns (r: int)
{
  var a: int;
  var b: int;
  assign a, b := polySetG(v, n);
  r := a + b
};

procedure callsPolySetG() opaque
{
  g := 0;
  var a: int;
  var b: int;
  assign a, b := polySetG(3, 5);
  assert a == 3;
  assert b == 3;
  assert g == 5;
  assert g == 0
//^^^^^^^^^^^^^ error: assertion does not hold
};

procedure callsWrapsPolySetG() opaque
{
  g := 0;
  var s: int := wrapsPolySetG(4, 6);
  assert s == 8;
  assert g == 6;
  assert g == 0
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A global writer nested inside an expression

The call is an operand rather than the whole value, so the block
`GlobalParameterization` lowers it to sits inside `+` or inside another call. Its
statements are hoisted ahead of the assignment, and the write reaches the caller just
as in the direct-initializer case above. In `discardsPlusOne` the expression is a
trailing statement whose value is discarded; the write still happens. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;

var g: int := 0

procedure setG(v: int) returns (r: int)
{
  g := v;
  r := v
};

procedure id(v: int) returns (r: int)
{
  r := v
};

procedure plusOne(v: int) returns (r: int)
{
  r := setG(v) + 1
};

procedure wrapped(v: int) returns (r: int)
{
  r := id(setG(v))
};

procedure discardsPlusOne(v: int) returns (r: int)
{
  r := 1;
  setG(v) + 1
};

procedure callsPlusOne() opaque
{
  g := 0;
  var r: int := plusOne(4);
  assert r == 5;
  assert g == 4;
  assert r == 4
//^^^^^^^^^^^^^ error: assertion does not hold
};

procedure callsPlusOneWrongWrite() opaque
{
  g := 0;
  var r: int := plusOne(4);
  assert g == 0
//^^^^^^^^^^^^^ error: assertion does not hold
};

procedure callsWrapped() opaque
{
  g := 0;
  var r: int := wrapped(6);
  assert r == 6;
  assert g == 6;
  assert g == 0
//^^^^^^^^^^^^^ error: assertion does not hold
};

procedure callsDiscardsPlusOne() opaque
{
  g := 0;
  var r: int := discardsPlusOne(3);
  assert r == 1;
  assert g == 3;
  assert g == 0
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## Operands are evaluated left to right

A read of `g` to the left of the call happens before the call writes it, and a read to
the right happens after. The left read is bound to a snapshot before the hoisted
statements run, so the two orders give different results. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;

var g: int := 0

procedure setG(v: int) returns (r: int)
{
  g := v;
  r := v
};

procedure readBefore() returns (r: int)
{
  g := 0;
  r := g + setG(5)
};

procedure readAfter() returns (r: int)
{
  g := 0;
  r := setG(5) + g
};

procedure callsReadBefore() opaque
{
  var r: int := readBefore();
  assert r == 5;
  assert g == 5;
  assert r == 10
//^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure callsReadAfter() opaque
{
  var r: int := readAfter();
  assert r == 10;
  assert g == 5;
  assert r == 5
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A heap writer nested inside an expression -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Cell { var v: int }

procedure bump(c: Cell) returns (r: int)
{
  c#v := c#v + 1;
  r := c#v
};

procedure bumpPlusOne(c: Cell) returns (r: int)
{
  r := bump(c) + 1
};

procedure callsBumpPlusOne(c: Cell) opaque modifies c
{
  c#v := 1;
  var r: int := bumpPlusOne(c);
  assert r == 3;
  assert c#v == 2;
  assert r == 2
//^^^^^^^^^^^^^ error: assertion does not hold
};

procedure callsBumpPlusOneWrongWrite(c: Cell) opaque modifies c
{
  c#v := 1;
  var r: int := bumpPlusOne(c);
  assert c#v == 1
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A global writer in a conditionally evaluated operand

A call in one branch of an if-expression, or in the right operand of a short-circuit
operator, runs only on that path. The enclosing assignment becomes a statement-level
`if` with the call hoisted into its own branch, so the write happens exactly when the
call is evaluated. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;

var g: int := 0

procedure setG(v: int) returns (r: int)
{
  g := v;
  r := v
};

procedure inBranch(b: bool, v: int) returns (r: int)
{
  r := (if b then setG(v) else 0) + 1
};

procedure shortCircuit(b: bool, v: int) returns (r: bool)
{
  r := b && setG(v) > 0
};

procedure callsInBranch() opaque
{
  g := 1;
  var t: int := inBranch(true, 7);
  assert t == 8;
  assert g == 7;
  var f: int := inBranch(false, 9);
  assert f == 1;
  assert g == 7;
  assert g == 9
//^^^^^^^^^^^^^ error: assertion does not hold
};

procedure callsShortCircuit() opaque
{
  g := 1;
  var f: bool := shortCircuit(false, 9);
  assert !f;
  assert g == 1;
  var t: bool := shortCircuit(true, 9);
  assert t;
  assert g == 9;
  assert g == 1
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A transparent heap writer

`HeapParameterization` lowers a body's last statement to a value-producing block, so a
heap-writing body arrives at `FunctionalRewrite` ending in a trailing value: the `x` of a
final `x := 2`, or the written value of a final `c#v := 9`. Laurel discards a body's
trailing expression rather than assigning it to an output, so the function copy's result
is the outputs: the packaged outputs in the first case, and the heap — an inout that
`GlobalParameterization` added — in the second.

Both shapes are pinned in both directions: the caller learns the output *and* the write,
and a wrong value for either is refuted. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Cell { var v: int }

procedure writesHeapReturnsValue(c: Cell) returns (x: int)
{
  c#v := 9;
  x := 2
};

procedure callsWritesHeapReturnsValue(c: Cell) opaque modifies c
{
  var x: int := writesHeapReturnsValue(c);
  assert x == 2;
  assert c#v == 9;
  assert x == 3
//^^^^^^^^^^^^^ error: assertion does not hold
};

procedure callsWritesHeapReturnsValueWrongWrite(c: Cell) opaque modifies c
{
  var x: int := writesHeapReturnsValue(c);
  assert c#v == 8
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Cell { var v: int }

procedure writesHeapVoid(c: Cell)
{
  c#v := 9
};

procedure callsWritesHeapVoid(c: Cell) opaque modifies c
{
  writesHeapVoid(c);
  assert c#v == 9;
  assert c#v == 8
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A trailing expression is never the result

A body's trailing expression is discarded, so the function copy's result is the output as
the body leaves it. An output the body never assigns keeps its arbitrary-but-fixed value,
and that is accepted without a diagnostic. Each case pins the true value proved and the
trailing expression's value refuted. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;

procedure incrTail(x: int) returns (x: int)
{
  x := x + 1;
  x * 10
};

procedure callsIncrTail() opaque
{
  assert incrTail(3) == 4;
  assert incrTail(3) == 40
//^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Cell { var v: int }

procedure readsThenClobbersLocal(c: Cell) returns (r: int)
{
  var t: int := c#v;
  r := t;
  t := 0
};

procedure callsReadsThenClobbersLocal(c: Cell) opaque modifies c
{
  c#v := 5;
  assert readsThenClobbersLocal(c) == 5;
  assert readsThenClobbersLocal(c) == 0
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;

procedure tailWithoutReturn(x: int): int
{
  x + 1
};

procedure callsTailWithoutReturn() opaque
{
  assert tailWithoutReturn(1) == 2
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A transparent heap writer called from a transparent body

A heap writer with a single declared output is a single-output call: the heap is a global,
and `GlobalParameterization` adds its receiver at the call site itself. So a transparent
body may call one, and the caller of *that* body learns both the output and the write,
through two transparent levels. A wrong value for either is refuted. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Cell { var v: int }

procedure writesHeap(c: Cell) returns (x: int)
{
  c#v := 9;
  x := 2
};

procedure wrapsHeapWriter(c: Cell) returns (r: int)
{
  var x: int := writesHeap(c);
  r := x
};

procedure callsWrapsHeapWriter(c: Cell) opaque modifies c
{
  var r: int := wrapsHeapWriter(c);
  assert r == 2;
  assert c#v == 9;
  assert c#v == 8
//^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure callsWrapsHeapWriterWrongOutput(c: Cell) opaque modifies c
{
  var r: int := wrapsHeapWriter(c);
  assert r == 3
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A multi-output call in a contract

Each clause below is paired with a case that must fail, so none of them can be passing
because the clause was dropped. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;

procedure swapPair(a: int, b: int) returns (x: int, y: int)
{
  return b, a
};

// In a precondition. `x` is `swapPair(n, 0)`'s first output, so it is 0 whatever `n` is
// and the precondition holds at every call site.
procedure needsZero(n: int)
  requires { var x: int; var y: int; assign x, y := swapPair(n, 0); x == 0 }
  opaque
{
};

procedure callsNeedsZero() opaque {
  needsZero(4)
};

// The same clause asking for `x == 1`, which `swapPair(n, 0)` never gives. The call must
// be rejected — that is what shows the projections are really evaluated rather than the
// clause being vacuous.
procedure needsOne(n: int)
  requires { var x: int; var y: int; assign x, y := swapPair(n, 0); x == 1 }
  opaque
{
};

procedure callsNeedsOne() opaque {
  needsOne(4)
//^^^^^^^^^^^ error: precondition does not hold
};

// The declaring form in a precondition. A clause's block is a scope like a body's, so
// the flattened declarations land in it and the condition after them reads them. The
// clause means the same thing as `needsZero`'s above; what it pins is that the
// declaring form survives being rewritten in a contract.
procedure needsZeroDeclaring(n: int)
  requires { assign var x: int, var y: int := swapPair(n, 0); x == 0 }
  opaque
{
};

procedure callsNeedsZeroDeclaring() opaque {
  needsZeroDeclaring(4)
};

// And the same clause asking for `x == 1`, which must reject its call site — otherwise
// the clause could be passing vacuously.
procedure needsOneDeclaring(n: int)
  requires { assign var x: int, var y: int := swapPair(n, 0); x == 1 }
  opaque
{
};

procedure callsNeedsOneDeclaring() opaque {
  needsOneDeclaring(4)
//^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
};

// In a postcondition: `y` is `swapPair(n, 1)`'s *second* output, so the clause says
// `r == n`. The caller learns it, and cannot learn more.
procedure echoes(n: int) returns (r: int)
  opaque
  ensures { var x: int; var y: int; assign x, y := swapPair(n, 1); r == y }
{
  r := n
};

procedure callsEchoes() opaque {
  var v: int := echoes(7);
  assert v == 7;
  assert v == 8
//^^^^^^^^^^^^^ error: assertion does not hold
};

// And the body has to prove it: this one returns `n + 1`.
procedure badEchoes(n: int) returns (r: int)
  opaque
  ensures { var x: int; var y: int; assign x, y := swapPair(n, 1); r == y }
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition does not hold
{
  r := n + 1
};
#end

/-! ## A void twinned callee is redirected too, and still checks its precondition

`redirectNames` keys on the body being transparent rather than on the output count, so a
*void* transparent procedure with an assert in its body — which gives it an imperative
twin — has its calls redirected to the pure twin as well. `FunctionalRewrite` replaces
that twin's body with the `true` placeholder, so the call lowers to an unused init and
the twin carries no meaning of its own.

What must survive is the obligation: the callee's `requires` is checked at the call site
by `ContractPass`, independently of the redirect. Both cases below pin that — the
satisfied one verifies, and the one passing an unconstrained argument does not. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure voidTwinned(x: int)
  requires x > 0
{
  assert 1 == 1
};

procedure callsVoidTwinnedSatisfied() opaque {
  voidTwinned(5)
};

procedure callsVoidTwinnedUnsatisfied(y: int) opaque {
  voidTwinned(y)
//^^^^^^^^^^^^^^ error: precondition does not hold
};
#end
