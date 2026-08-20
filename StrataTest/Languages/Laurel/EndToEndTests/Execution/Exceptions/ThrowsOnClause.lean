/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
The `throwsOn` clause, end to end. A case is
`throwsOn C { ensures … modifies … }`, and one rule generates everything below:
**a case's guard forces its throw.** `throwsOn C { … }` lowers to
`C ==> Result..isBad($result)`, plus `C ∧ Result..isBad($result) ==> P` for each
`ensures P`, plus that case's frame on that path only.

Three consequences, and the sections follow them in order:

1. *Forcing.* A body that returns normally on a guarded path fails, so a case is an
   obligation rather than a note. Contrast the declared-type postcondition
   `isBad ==> err is T`, which is derived and needs no clause.
2. *Exhaustiveness.* Because each guard forces its throw, stating any case is a
   claim to have enumerated them — so `ModifiesClauses` emits a checked
   `isBad($result) ==> (C₁ ∨ … ∨ Cₙ)`. A throwing path matching no guard is
   reported rather than left unframed, since every case's frame is vacuous there.
   Stating *no* case is therefore different from stating `throwsOn false`: the
   former constrains nothing, the latter claims the procedure never throws.
3. *Per-case obligations.* Each case carries its own `ensures` and its own frame,
   guarded by `isBad ∧ Cᵢ`, so a procedure that throws different things for
   different reasons says which for which instead of unioning them.

The last two sections take the caller's side, with an opaque (bodiless) callee, since
that is where the clause earns its keep: the caller sees no body, so everything it
concludes comes from the cases. Both directions appear — forwards, where establishing
a guard proves the call throws, and backwards, where refuting every guard proves it
did not.

Not covered here, by design: `free`/`checked` variants of a case's `ensures` and a
wildcard case frame do not exist. See the exceptions section of the Laurel Designer
Guide for why (in short: an empty case frame already means "unframed", so a wildcard
would be a second spelling of it).

Using `testLaurelExecution` but skiping the Core interpreter test path: these cases
throw composite values, which live on the heap, and the interpret path does not
support the heap yet. Where a construct can be exercised without the heap it is run
both ways instead; see `Throw.lean`.
-/

/-! ## The clause: a guard forces its throw

`throwsOn C { … }` exceptional behavior cases.

A case pairs a pre-state guard `C` with the contract for the throwing path it
selects. Its meaning is that `C` *forces* the throw: it lowers to a Core
postcondition `C ==> (Result..isBad($result) ∧ P)` for each `ensures P` in the
block — checked on exit, so the body must honor it, and assumed at call sites, so
a caller that establishes `C` can prove a throw *will* happen and what then holds.
Guards are pre-state predicates over the inputs. A guard may not read the heap:
the lowering places it in a postcondition, which is read in the post-state, so a
heap-reading guard would silently mean "held on exit" instead. Resolution rejects
that shape — see `Resolution/Exceptions/UnsupportedExceptionShapes.lean` — and a
guard that needs to test heap state hoists the read into a parameter, as the
array-bounds case below does.

The thrown value is named by the `throws (e: T)` clause, which scopes `e` over every
case's `ensures` — but not over the guards, which are evaluated on entry, before any
throw. There is no unbound form: `throws` always names its value, whether or not any
case mentions it.

Using `testLaurelExecution` but skiping the Core interpreter test path: these cases
allocate on the heap — a thrown exception is a composite value, and some cases also
`new` inside the region — and the interpret path does not support the heap yet. Where
a construct can be exercised without the heap it is run both ways instead; see
`TryCatchThrow.lean`.
-/

-- Positive: the body throws exactly when `b == 0`, and the thrown value is an
-- `ArithmeticException`, so the case holds.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exception {}
composite ArithmeticException extends Exception {}
procedure div(a: int, b: int)
  returns (r: int)
  throws (e: Exception)
  opaque
  throwsOn b == 0 {
    ensures e is ArithmeticException
  }
{
  if b == 0 then {
    var ae: ArithmeticException := new ArithmeticException;
    throw ae
  };
  r := a / b
};
#end

-- Negative: the case declares a throw when `b == 0`, but the body never throws,
-- so the forcing part cannot be proved on exit.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exception {}
composite ArithmeticException extends Exception {}
procedure divBad(a: int, b: int)
  returns (r: int)
  throws (e: Exception)
  opaque
  throwsOn b == 0 {
//         ^^^^^^ error: throwsOn case forces a throw does not hold
    ensures e is ArithmeticException
  }
{
  r := 0
};
#end

-- Caller-side use: from an opaque (bodiless) procedure's behavior case, the
-- caller proves the throw definitely happens — calling with `b == 0` must take
-- the `catch` branch (so `out` ends at 99, never 1). A case with nothing to say
-- about the thrown value needs no `ensures` at all; the guard alone forces the
-- throw.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exception {}
procedure mustThrow(a: int, b: int)
  returns (r: int)
  throws (e: Exception)
  opaque
  throwsOn b == 0 {
  };
procedure caller()
  returns (out: int)
  opaque
  ensures out == 99
{
  out := 0;
  try {
    var z: int := mustThrow(5, 0);
    out := 1
  } catch c {
    out := 99
  }
};
#end

/-! ## Exhaustiveness over the cases

The exhaustiveness claim over `throwsOn` cases:
`Result..isBad($result) ==> (C₁ ∨ … ∨ Cₙ)`.

A case's guard *forces* its throw, so stating any case is a claim to have enumerated
them. `ModifiesClauses` therefore emits this alongside the per-case frames, which closes
what would otherwise be a silent hole: each frame's antecedent is `isBad ∧ Cᵢ`, so a
throwing path matching no guard satisfies every frame vacuously and is left completely
unconstrained. Without the claim, forgetting a case verifies clean while forgetting an
entry *inside* a case fails loudly — the two mistakes would fail in opposite directions,
and the more dangerous one silently.

Two boundary readings follow from the same rule, and both are exercised below:
`throwsOn true` is "throws unconditionally", and `throwsOn false` is "never throws"
(nothing forces the throw, and the disjunction rules every throwing path out).

Stating *no* case is not the same as stating `throwsOn false`: it claims nothing about
the throwing paths, so no exhaustiveness claim is emitted and they are left
unconstrained. That is the only way to leave a conditional throwing path unframed,
since a guard would have to name the condition.

Known limitation: a guard is documented as a pre-state predicate, but the claims it is
lowered into are postconditions, and its heap reads are *not* wrapped in `old(...)` — so
a guard like `c#value < 0` is evaluated against the post-state heap and does not verify
against a body that branched on the pre-state value. The guards below are therefore over
parameters, which are immutable and so read the same in both states. Heap-reading guards
are therefore unsupported rather than merely untested.

Using `testLaurelExecution` but skiping the Core interpreter test path: a thrown
exception is a composite, and the interpret path does not support the heap yet.
-/

-- Positive: one case, and it covers the only throwing path.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Cell {
  value: int
}
composite Err {}
procedure oneCase(c: Cell, logCell: Cell, fail: bool)
  returns (r: int)
  throws (e: Err)
  opaque
  modifies c
  throwsOn fail {
    modifies logCell
  }
{
  if fail then {
    logCell#value := 1;
    var e: Err := new Err;
    throw e
  };
  c#value := 42;
  r := 0
};
#end

-- Negative: a second throwing path that no guard covers. Before the exhaustiveness
-- claim this verified — the `fail` frame is vacuous on that path, so the write to
-- `logCell` went unchecked.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Cell {
  value: int
}
composite Err {}
procedure missedCase(c: Cell, logCell: Cell, fail: bool)
//        ^^^^^^^^^^ error: throwsOn cases cover every throwing path does not hold
  returns (r: int)
  throws (e: Err)
  opaque
  modifies c
  throwsOn fail {
    modifies logCell
  }
{
  if fail then {
    logCell#value := 1;
    var e1: Err := new Err;
    throw e1
  };
  if c#value < 0 then {
    logCell#value := 2;
    var e2: Err := new Err;
    throw e2
  };
  c#value := 42;
  r := 0
};
#end

-- The fix is to state the missing case.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Cell {
  value: int
}
composite Err {}
procedure bothCases(c: Cell, logCell: Cell, fail: bool, alsoFail: bool)
  returns (r: int)
  throws (e: Err)
  opaque
  modifies c
  throwsOn fail {
    modifies logCell
  }
  throwsOn alsoFail {
    modifies logCell
  }
{
  if fail then {
    logCell#value := 1;
    var e1: Err := new Err;
    throw e1
  };
  if alsoFail then {
    logCell#value := 2;
    var e2: Err := new Err;
    throw e2
  };
  c#value := 42;
  r := 0
};
#end

-- `throwsOn false` states that the procedure never throws. Verifies here, because it
-- does not.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Err {}
procedure neverThrows(x: int)
  returns (r: int)
  throws (e: Err)
  opaque
  throwsOn false {
  }
{
  r := x
};
#end

-- ...and fails when it does throw, since no guard can cover that path.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Err {}
procedure claimsNeverThrows(x: int)
//        ^^^^^^^^^^^^^^^^^ error: throwsOn cases cover every throwing path does not hold
  returns (r: int)
  throws (e: Err)
  opaque
  throwsOn false {
  }
{
  if x < 0 then {
    var e: Err := new Err;
    throw e
  };
  r := x
};
#end

-- Stating no case at all leaves the throwing paths unconstrained rather than ruled
-- out: the same body as above verifies, because no exhaustiveness claim is emitted.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Err {}
procedure saysNothing(x: int)
  returns (r: int)
  throws (e: Err)
  opaque
{
  if x < 0 then {
    var e: Err := new Err;
    throw e
  };
  r := x
};
#end

/-! ## Per-case `ensures` -/
-- A case's `ensures` is checked on the exceptional path: `alwaysThrows` throws a value
-- of type `Err`, so `ensures e is Err` holds on the Bad path. (The normal
-- `ensures r > 0` is vacuous here — the Good path is never taken.)
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Err {}
procedure alwaysThrows()
  returns (r: int)
  throws (e: Err)
  opaque
  ensures r > 0
  throwsOn true {
    ensures e is Err
  }
{
  var x: Err := new Err;
  throw x
};
#end

-- Negative: the case claims the escaping value is `Other`, but `wrongThrownType`
-- throws an `Err` (a disjoint sibling), so the exceptional postcondition cannot
-- be proved on the Bad path.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite AppException {}
composite Err extends AppException {}
composite Other extends AppException {}
procedure wrongThrownType()
  returns (r: int)
  throws (e: AppException)
  opaque
  ensures r > 0
  throwsOn true {
    ensures e is Other
//          ^^^^^^^^^^ error: postcondition could not be proved
  }
{
  var x: Err := new Err;
  throw x
};
#end
/-! ## A per-type case dereferencing a composite parameter

An array read `value(a, i)`, translated as a Java front-end would emit it: the
array bounds check is made explicit (Core has no implicit exceptions), and the
case's guard records the pre-state that causes the exception. The array is a
composite `IntArray` carrying its `length`; the element store is a separate
`TotalMap int int` (composite fields cannot be map-typed).

The *body* dereferences the composite — `i >= a#length` — while the case's
guard tests the same bound through an `alen` parameter tied to the field by a
`requires`. A guard may not read the heap at all: guards are pre-state
predicates, but the lowering places them in postconditions, so a heap-reading
guard would silently be read in the post-state. `Resolution.lean` rejects that
shape; the rejection is pinned in
`EndToEndTests/Resolution/Exceptions/UnsupportedExceptionShapes.lean`. Passing
the bound as a parameter is the workaround the diagnostic recommends, and it is
what a front end would emit.

(The Java source also throws `NullPointerException` when `a == null`; that arm
is omitted because Laurel does not yet model null composite references.)

Where the "constraining the thrown value by type" section below keys its cases on the
thrown value's type, this one keys on a pre-state condition over an argument, and
the body throws on exactly that condition — so the guard is discharged against a
real throwing path rather than vacuously. -/

-- Positive: the out-of-bounds path throws `IndexError` (with `i >= a#length`),
-- and the in-bounds fall-through returns `select(elems, i)` — so the case
-- clause and the `ensures` discharge.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exception {}
composite IndexError extends Exception {}
composite IntArray {
  length: int
}
procedure value(a: IntArray, elems: TotalMap int int, i: int, alen: int)
  returns (r: int)
  throws (e: Exception)
  requires alen == a#length
  opaque
  ensures r == select(elems, i)
  throwsOn (i < 0) || (i >= alen) {
    ensures e is IndexError
  }
{
  if (i < 0) || (i >= a#length) then {
    var ei: IndexError := new IndexError;
    throw ei
  };
  r := select(elems, i)
};
#end

-- Negative: a wrong case postcondition — claiming `IndexError` implies the index
-- is in bounds, when it is thrown precisely when out of bounds — cannot be
-- proved on the Bad path.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exception {}
composite IndexError extends Exception {}
composite IntArray {
  length: int
}
procedure valueBad(a: IntArray, elems: TotalMap int int, i: int, alen: int)
  returns (r: int)
  throws (e: Exception)
  requires alen == a#length
  opaque
  ensures r == select(elems, i)
  throwsOn (i < 0) || (i >= alen) {
    ensures e is IndexError ==> (i >= 0) && (i < alen)
//          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
  }
{
  if (i < 0) || (i >= a#length) then {
    var ei: IndexError := new IndexError;
    throw ei
  };
  r := select(elems, i)
};
#end
/-! ## A case postcondition dereferencing the thrown value

A case's `ensures` may narrow the thrown value with a cast and read a field of it:
`ensures e is T ==> (e as T)#f ...`. It is an exceptional
postcondition of the form "if the procedure exits by throwing a `T`, then this
property of the thrown value holds".

Here the offending index is recorded on the exception (`IndexError#badIndex`) and
the case states the *condition* that it is out of bounds — not a specific
value. The array is a `TotalMap int int` with a separate `alen` length. -/

-- Positive: `value(a, i)` throws `IndexError` recording the offending index when
-- `i` is out of bounds, and the case states that the recorded index is out
-- of bounds (a condition, no specific value) — which holds because it equals `i`
-- on the throwing path.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exception {}
composite IndexError extends Exception {
  badIndex: int
}
procedure value(a: TotalMap int int, alen: int, i: int)
  returns (r: int)
  throws (e: Exception)
  opaque
  ensures r == select(a, i)
  throwsOn (i < 0) || (i >= alen) {
    ensures e is IndexError ==> ((e as IndexError)#badIndex < 0) || ((e as IndexError)#badIndex >= alen)
  }
{
  if (i < 0) || (i >= alen) then {
    var ei: IndexError := new IndexError;
    ei#badIndex := i;
    throw ei
  };
  r := select(a, i)
};
#end

-- Negative: the case claims the recorded index is *in* bounds, which
-- contradicts the throwing condition, so it cannot be proved.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exception {}
composite IndexError extends Exception {
  badIndex: int
}
procedure valueBadContract(a: TotalMap int int, alen: int, i: int)
  returns (r: int)
  throws (e: Exception)
  opaque
  ensures r == select(a, i)
  throwsOn (i < 0) || (i >= alen) {
    ensures e is IndexError ==> ((e as IndexError)#badIndex >= 0) && ((e as IndexError)#badIndex < alen)
//          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
  }
{
  if (i < 0) || (i >= alen) then {
    var ei: IndexError := new IndexError;
    ei#badIndex := i;
    throw ei
  };
  r := select(a, i)
};
#end

/-! ## Constraining the thrown value by type

A case's `ensures` narrows what was thrown below the declared `throws` type. That is
how a coarsened declaration stays useful: the signature names an ancestor, and the
case names the actual set. Several `ensures` in one case *conjoin*, so a per-type
claim has to be written as an implication keyed on the type, not as a bare
conjunction of type tests. -/

-- Multi-throws modeling: a coarsened `throws` type plus the precise set in a case's
-- `ensures` (this is how a Java `throws A, B` is represented).
--
-- Note the bodies in this section actually throw. A case's guard *forces* its throw, so
-- `throwsOn true` on a body that returns normally would fail its forcing claim. The
-- contracts here are therefore exercised rather than merely recorded.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exception {}
composite ParseError extends Exception {}
composite ArithError extends Exception {}
procedure multiThrows(pick: bool)
  throws (e: Exception)
  opaque
  throwsOn true {
    ensures e is ParseError || e is ArithError
  }
{
  if pick then {
    var p: ParseError := new ParseError;
    throw p
  };
  var a: ArithError := new ArithError;
  throw a
};
#end

-- Per-type claims inside one case. The `ensures` clauses of a case conjoin, so each
-- is written as a guarded implication `e is T ==> <property of a T>`: the guard scopes
-- the claim to its own type, so the clauses coexist. (Contrast bare
-- `ensures e is A` + `ensures e is B`, which conjoin to "the value is both A and B" —
-- a contradiction for disjoint siblings, i.e. "throws neither".)
--
-- Per-type *value* properties use the same shape with a cast in the consequent, e.g.
-- `ensures e is ParseError ==> (e as ParseError)#position >= 0`; the `e is T`
-- antecedent is what discharges the cast's embedded type-test assertion; the
-- "dereferencing the thrown value" section above exercises that form.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exception {}
composite ParseError extends Exception {}
composite ArithError extends Exception {}
procedure perTypeClaims(pick: bool)
  throws (e: Exception)
  opaque
  throwsOn true {
    ensures e is ParseError ==> !(e is ArithError)
    ensures e is ArithError ==> !(e is ParseError)
  }
{
  if pick then {
    var p: ParseError := new ParseError;
    throw p
  };
  var a: ArithError := new ArithError;
  throw a
};
#end

-- Deeper hierarchy: a tighter `throws` type (an intermediate ancestor).
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite AppException {}
composite ParseError extends AppException {}
procedure tighterThrows()
  throws (e: AppException)
  opaque
  throwsOn true {
    ensures e is ParseError
  }
{
  var p: ParseError := new ParseError;
  throw p
};
#end

/-! ## Per-case `modifies`

Exceptional frames: the `modifies` clauses inside a `throwsOn` behavior case,
which apply on *that case's* throwing path, mirroring the top-level `modifies`
that applies on the normal-return path.

A throwing procedure's normal `modifies` frame is lowered (via `ModifiesClauses`
+ the Good-path wrap) to `Result..isGood($result) ==> <only normal targets
change>`, so it says nothing when the procedure throws. Each case contributes the
complementary Bad-path frame `Result..isBad($result) ∧ Cᵢ ==> <only that case's
targets change>`. So the paths can name different frames, and each is *checked* on
the body and *assumed* at call sites.

Because a case's guard `Cᵢ` *forces* its throw (`Cᵢ ==> isBad`), stating any case is
a claim to have enumerated them, and `ModifiesClauses` emits a checked
`isBad ==> (C₁ ∨ … ∨ Cₙ)` alongside the frames. Two consequences visible below: a
throwing path matching no guard is rejected rather than silently unframed, and a
caller that refutes every guard learns the call cannot have thrown.

Using `testLaurelExecution` but skiping the Core interpreter test path: these cases
allocate on the heap — a thrown exception is a composite value, and some cases also
`new` inside the region — and the interpret path does not support the heap yet. Where
a construct can be exercised without the heap it is run both ways instead; see
`TryCatchThrow.lean`.
-/

-- Positive: the body honours both frames — on the normal path only `c` changes,
-- on the `fail` throwing path only `logCell` changes (the freshly-allocated `Err`
-- is excluded from the frame, since it did not exist in the pre-state heap).
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Cell {
  value: int
}
composite Err {}
procedure doWork(c: Cell, logCell: Cell, fail: bool)
  returns (r: int)
  throws (e: Err)
  opaque
  modifies c
  throwsOn fail {
    modifies logCell
  }
{
  if fail then {
    logCell#value := 1;
    var e: Err := new Err;
    throw e
  };
  c#value := 42;
  r := 0
};
#end

-- Negative: on the throwing path this modifies `c`, but the case's frame claims
-- only `logCell` may change there, so the exceptional frame check fails. The
-- guard is `true` because this procedure throws (e: unconditionally).
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Cell {
  value: int
}
composite Err {}
procedure doWorkBad(c: Cell, logCell: Cell)
//        ^^^^^^^^^ error: throwsOn modifies clause does not hold
  returns (r: int)
  throws (e: Err)
  opaque
  modifies c
  throwsOn true {
    modifies logCell
  }
{
  c#value := 99;
  var e: Err := new Err;
  throw e
};
#end

-- Field-granular exceptional frame: `modifies logCell#value` inside a case frames
-- only the `(logCell, value)` pair on that throwing path, exactly as `modifies o#f`
-- does on the normal path. This needs the clause's refs to parse at precedence 0
-- (see `throwsOnModifies` in the grammar); otherwise `logCell#value` does not
-- parse as a field target here.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Cell {
  value: int
  other: int
}
composite Err {}
procedure fieldGranularThrowFrame(c: Cell, logCell: Cell, fail: bool)
  returns (r: int)
  throws (e: Err)
  opaque
  modifies c#value
  throwsOn fail {
    modifies logCell#value
  }
{
  if fail then {
    logCell#value := 1;
    var e: Err := new Err;
    throw e
  };
  c#value := 42;
  r := 0
};
#end

-- Negative for the same shape: the throwing path writes `logCell#other`, which
-- the field-granular exceptional frame does not name, so the check fails.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Cell {
  value: int
  other: int
}
composite Err {}
procedure fieldGranularThrowFrameBad(logCell: Cell)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^ error: throwsOn modifies clause does not hold
  returns (r: int)
  throws (e: Err)
  opaque
  throwsOn true {
    modifies logCell#value
  }
{
  logCell#other := 7;
  var e: Err := new Err;
  throw e
};
#end

/-! ### What stating a case buys the caller

A case's guard forces its throw, and the cases are checked to cover every throwing
path, so together they pin down *when* the procedure throws — not just what holds if
it does. A caller that can refute every guard therefore learns the call cannot have
thrown, which makes its handler dead code and keeps its own normal-path frame intact.

The pair below is the evidence, and it is the answer to "a modifies clause for
throwing, without a condition for throwing, seems strange": the condition is not an
extra, it is what the case is keyed on. -/

-- With a case: `fail` is passed `false`, and the exhaustiveness claim gives
-- `isBad ==> fail`, hence `!isBad`. The handler is unreachable (`assert false`
-- holds) and the caller frames only `c`, even though the callee's exceptional
-- frame mentions `logCell`.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Err {}
composite Cell {
  value: int
}
procedure doWorkGuarded(c: Cell, logCell: Cell, fail: bool)
  returns (r: int)
  throws (e: Err)
  opaque
  ensures r == 0
  modifies c
  throwsOn fail {
    ensures e is Err
    modifies logCell
  }
{
  if fail then {
    logCell#value := 1;
    var ex: Err := new Err;
    throw ex
  };
  c#value := 42;
  r := 0
};
procedure handlerIsDead(c: Cell, l: Cell)
  returns (out: int)
  opaque
  modifies c
{
  out := 0;
  try {
    out := doWorkGuarded(c, l, false)
  } catch e {
    assert false
  }
};
#end

-- Stating no case at all leaves the throwing path undescribed: only the
-- synthesized `isBad ==> err is Err` is available, which says nothing about when a
-- throw happens or what it may change. The same caller now fails twice — it cannot
-- rule the handler out, and it cannot keep `modifies c`, because with no
-- exceptional frame the callee may have changed anything on a path the caller can
-- no longer exclude.
--
-- Note this is also the *only* way to leave the throwing path unframed. A case's
-- guard forces its throw, so `throwsOn true` would claim the procedure always
-- throws, which is false here; there is no way to frame a conditional throwing path
-- without naming its condition.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Err {}
composite Cell {
  value: int
}
procedure doWorkUnguarded(c: Cell, logCell: Cell, fail: bool)
  returns (r: int)
  throws (e: Err)
  opaque
  ensures r == 0
  modifies c
{
  if fail then {
    logCell#value := 1;
    var e: Err := new Err;
    throw e
  };
  c#value := 42;
  r := 0
};
procedure handlerNotDead(c: Cell, l: Cell)
//        ^^^^^^^^^^^^^^ error: modifies clause could not be proved
  returns (out: int)
  opaque
  modifies c
{
  out := 0;
  try {
    out := doWorkUnguarded(c, l, false)
  } catch e {
    assert false
//  ^^^^^^^^^^^^ error: assertion could not be proved
  }
};
#end

/-! ## What a caller learns from the cases

`try` / `catch` around a call to an **opaque** throwing procedure: the `throw` is not
in the caller's body, and the caller cannot see the callee's body either, so
everything it knows comes from the exceptional contract: a `throwsOn` case's guard for
what forces a throw, and the exhaustiveness claim over the guards for what a throw
implies.

This is the combination a front end actually emits for a checked-exception call, and
it is where the two contract directions pay off separately:

- from the exhaustiveness claim, a handler reasons *backwards* — it caught something, so
  the stated property held;
- from a case's guard, the caller reasons *forwards* — it passed an input that
  forces a throw, so the handler definitely runs.

Using `testLaurelExecution` but skiping the Core interpreter test path: these cases
allocate a composite exception value, which the interpret path does not support yet.
-/

-- Backwards direction: the handler learns `id < 0` without seeing the body. The case
-- guards on `id < 0`, and because stating cases enumerates them, the exhaustiveness
-- claim `isBad ==> id < 0` is available to callers.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite NotFound {}
procedure fetch(id: int) returns (r: int)
  throws (e: NotFound)
  opaque
  ensures r > 0
  throwsOn id < 0 {
  }
;
procedure caller(id: int) returns (out: int)
  opaque
{
  out := 0;
  try {
    out := fetch(id);
    assert out > 0
  } catch e when e is NotFound {
    assert id < 0;
    out := -1
  }
};
#end

-- Forwards direction: the case's guard *forces* the throw for that input, so the
-- normal path is unreachable and the handler's assignment is the only outcome.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite NotFound {}
procedure fetchStrict(id: int) returns (r: int)
  throws (e: NotFound)
  opaque
  throwsOn id == 0 {
    ensures e is NotFound
  }
;
procedure callerKnowsItThrows() returns (out: int)
  opaque
  ensures out == 99
{
  out := 0;
  try {
    out := fetchStrict(0);
    assert false
  } catch e when e is NotFound {
    out := 99
  }
};
#end

/-! ## What a caller learns from the case frames

`try` / `catch` around a call to an opaque throwing procedure that declares **frames**:
`modifies` for its normal exit and a `throwsOn` case's `modifies` for its throwing one. The caller sees
no body, so everything it can conclude about the heap comes from those two clauses,
which are guarded by complementary halves of the callee's result.

What the caller gets:

- after catching, only the case's frame locations may have changed;
- after falling through, only the `modifies` locations may have changed.

The callers below allocate the objects they pass, which is how they know those objects
are distinct — the same shape the user guide's modifies example uses. Distinctness via
a `requires c != l` precondition alone is not enough for this reasoning, which is a
property of the modifies encoding rather than of exceptions.

Note the callers declare no case of their own: they catch, so they have no exceptional
exit, and a case without a `throws` type is rejected.

Using `testLaurelExecution` but skiping the Core interpreter test path: these cases
allocate composite values, which the interpret path does not support yet.
-/

-- Caught the exception: the callee's exceptional frame covers only `logCell`, so the
-- caller's snapshot of `c` still holds.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Err {}
composite Cell {
  value: int
}
procedure doWork(c: Cell, logCell: Cell, fail: bool)
  returns (r: int)
  throws (e: Err)
  opaque
  ensures r == 0
  modifies c
  throwsOn fail {
    modifies logCell
  }
{
  if fail then {
    logCell#value := 1;
    var e: Err := new Err;
    throw e
  };
  c#value := 42;
  r := 0
};
procedure callerAfterCatch()
  returns (out: int)
  opaque
{
  var c: Cell := new Cell;
  var l: Cell := new Cell;
  var snapshot: int := c#value;
  out := 0;
  try {
    out := doWork(c, l, true)
  } catch e when e is Err {
    assert snapshot == c#value;
    out := -1
  }
};
#end

-- Fell through normally: the normal frame covers only `c`, so `logCell` is unchanged
-- and the callee's `ensures` is available.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Err {}
composite Cell {
  value: int
}
procedure doWork2(c: Cell, logCell: Cell, fail: bool)
  returns (r: int)
  throws (e: Err)
  opaque
  ensures r == 0
  modifies c
  throwsOn fail {
    modifies logCell
  }
{
  if fail then {
    logCell#value := 1;
    var e: Err := new Err;
    throw e
  };
  c#value := 42;
  r := 0
};
procedure callerNormalPath()
  returns (out: int)
  opaque
{
  var c: Cell := new Cell;
  var l: Cell := new Cell;
  var snapshot: int := l#value;
  out := 0;
  try {
    out := doWork2(c, l, false);
    assert snapshot == l#value;
    assert out == 0
  } catch e when e is Err {
    out := -1
  }
};
#end

/-! ### Per-case frames are separate, not unioned

Each `throwsOn` case carries its own frame, guarded by `Result..isBad ∧ Cᵢ`, so a callee
that writes `parseLog` on one throwing path and `ioLog` on another declares them
separately rather than only their union — and a caller that rules out one case can
conclude the other's targets are unchanged.

The case below is the evidence: its `mode == 1` path writes `ioLog` and then throws a
`ParseError`, and that write is rejected because it is checked against the `mode == 1`
case's own frame, which names only `parseLog`. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exception {}
composite ParseError extends Exception {}
composite IOError extends Exception {}
composite Cell {
  value: int
}
procedure loadCrossed(c: Cell, parseLog: Cell, ioLog: Cell, mode: int)
//        ^^^^^^^^^^^ error: throwsOn modifies clause does not hold
  returns (r: int)
  throws (e: Exception)
  opaque
  modifies c
  throwsOn mode == 1 {
    modifies parseLog
  }
{
  if mode == 1 then {
    ioLog#value := 99;
    var pe: ParseError := new ParseError;
    throw pe
  };
  c#value := 0;
  r := 0
};
#end

/-! ## A case's `ensures` accepts a `summary`

Exactly as a normal `ensures` does, and the summary replaces the default text when the
obligation fails — so a front end can phrase an exceptional postcondition in its own
terms. This is the one place the `throwsOn` clause surface is *not* narrower than the
normal one; `free`/`checked` have no case equivalent, and a wildcard frame would be
redundant with an empty one. See the Laurel Designer Guide. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exception {}
composite ParseError extends Exception {}
composite ArithError extends Exception {}
procedure summarisedCase(b: int)
  returns (r: int)
  throws (e: Exception)
  opaque
  throwsOn b == 0 {
    ensures e is ParseError summary "the zero case throws a ParseError"
//          ^^^^^^^^^^^^^^^ error: the zero case throws a ParseError could not be proved
  }
{
  if b == 0 then {
    var a: ArithError := new ArithError;
    throw a
  };
  r := b
};
#end
