/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Exercises the E4/E7 exceptional *contract* on the verification side: a throwing
procedure's normal (`ensures`) postconditions and its `onThrow` exceptional
postconditions (see `docs/design/laurel_extensions.md`, extension E4).

A procedure that declares `throws` lowers to one returning a single
`Result<Val, Composite>` (`$result`). Its contract is split by which channel it
describes:
  - a normal `ensures P` holds only on the *Good* path, so it lowers to
    `Result..isGood($result) ==> P[out := Result..value($result)]`;
  - each `onThrow (e) Q` holds only on the *Bad* path, lowering to
    `Result..isBad($result) ==> Q[e := Result..err($result)]`.
Both become ordinary Core postconditions, so each is *checked* on the
procedure's exit (when it has a body) and *assumed* at call sites. These tests
pin both directions: proven-on-exit, assumed-by-caller, and the two failing
cases.

`onThrow` predicates constrain the caught value only by *reference* (e.g.
`e is T`); field dereference on the binding remains a known gap (see
`ExceptionScenarios.lean`).
-/

-- Good-path `ensures` is checked on exit: `safeInc` establishes `r > x` on the
-- (only, non-throwing) path, so the guarded postcondition discharges.
#eval testLaurel <|
#strata
program Laurel;
composite Err extends BaseException {}
procedure safeInc(x: int)
  returns (r: int)
  throws Err
  opaque
  ensures r > x
{
  r := x + 1
};
#end

-- Good-path `ensures` is assumed at a call site: inside the `try`, the call to
-- `produce` returns on the Good path, so the caller may rely on `ensures r > 10`
-- for the unwrapped value and prove `out > 10`.
#eval testLaurel <|
#strata
program Laurel;
composite Err extends BaseException {}
procedure produce()
  returns (r: int)
  throws Err
  opaque
  ensures r > 10
{
  r := 20
};
procedure consume()
  returns (out: int)
  opaque
{
  try {
    out := produce();
    assert out > 10
  } catch c {
    out := 0
  }
};
#end

-- `onThrow` is checked on the exceptional path: `alwaysThrows` throws a value of
-- type `Err`, so `onThrow (e) e is Err` holds on the Bad path. (The normal
-- `ensures r > 0` is vacuous here — the Good path is never taken.)
#eval testLaurel <|
#strata
program Laurel;
composite Err extends BaseException {}
procedure alwaysThrows()
  returns (r: int)
  throws Err
  onThrow (e) e is Err
  opaque
  ensures r > 0
{
  var x: Err := new Err;
  throw x
};
#end

-- Negative: the good-path `ensures` does not hold — `badInc` returns `x - 1`,
-- which is not `> x` — so the guarded postcondition fails on the Good path.
#eval testLaurel <|
#strata
program Laurel;
composite Err extends BaseException {}
procedure badInc(x: int)
  returns (r: int)
  throws Err
  opaque
  ensures r > x
//        ^^^^^ error: assertion does not hold
{
  r := x - 1
};
#end

-- Negative: `onThrow` claims the escaping value is `Other`, but `wrongOnThrow`
-- throws an `Err` (a disjoint sibling), so the exceptional postcondition cannot
-- be proved on the Bad path.
#eval testLaurel <|
#strata
program Laurel;
composite Err extends BaseException {}
composite Other extends BaseException {}
procedure wrongOnThrow()
  returns (r: int)
  throws Err
  onThrow (e) e is Other
//            ^^^^^^^^^^ error: assertion could not be proved
  opaque
  ensures r > 0
{
  var x: Err := new Err;
  throw x
};
#end
/-! ## Per-type `onThrow` dereferencing a composite parameter

An array read `value(a, i)`, translated as a Java front-end would emit it: the
array bounds check is made explicit (Core has no implicit exceptions), and the
`onThrow` clause records the pre-state that causes the exception. The array is a
composite `IntArray` carrying its `length`; the element store is a separate
`Map int int` (composite fields cannot be map-typed). The out-of-bounds
`onThrow` consequent *dereferences the composite parameter* — `i >= a#length` —
which is heap-parameterized just like a normal postcondition.

(The Java source also throws `NullPointerException` when `a == null`; that arm
is omitted because Laurel does not yet model null composite references.)

Unlike the `perTypeOnThrow` scenario in `ExceptionScenarios.lean` (whose body
never throws, so its `onThrow` clause holds vacuously), the body here actually
throws on the out-of-bounds condition, so the clause is checked non-vacuously. -/

-- Positive: the out-of-bounds path throws `IndexError` (with `i >= a#length`),
-- and the in-bounds fall-through returns `select(elems, i)` — so the `onThrow`
-- clause and the `ensures` discharge.
#eval testLaurel <|
#strata
program Laurel;
composite Exception extends BaseException {}
composite IndexError extends Exception {}
composite IntArray {
  length: int
}
procedure value(a: IntArray, elems: Map int int, i: int)
  returns (r: int)
  throws Exception
  onThrow (e) e is IndexError ==> (i < 0) || (i >= a#length)
  opaque
  ensures r == select(elems, i)
{
  if (i < 0) || (i >= a#length) then {
    var ei: IndexError := new IndexError;
    throw ei
  };
  r := select(elems, i)
};
#end

-- Negative: a wrong `onThrow` clause — claiming `IndexError` implies the index
-- is in bounds, when it is thrown precisely when out of bounds — cannot be
-- proved on the Bad path.
#eval testLaurel <|
#strata
program Laurel;
composite Exception extends BaseException {}
composite IndexError extends Exception {}
composite IntArray {
  length: int
}
procedure valueBad(a: IntArray, elems: Map int int, i: int)
  returns (r: int)
  throws Exception
  onThrow (e) e is IndexError ==> (i >= 0) && (i < a#length)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  opaque
  ensures r == select(elems, i)
{
  if (i < 0) || (i >= a#length) then {
    var ei: IndexError := new IndexError;
    throw ei
  };
  r := select(elems, i)
};
#end
/-! ## `onThrow` dereferencing the exception binding

An `onThrow` predicate may narrow the binding with a cast and read a field of the
thrown value: `onThrow (e) e is T ==> (e as T)#f ...`. It is an exceptional
postcondition of the form "if the procedure exits by throwing a `T`, then this
property of the thrown value holds".

Here the offending index is recorded on the exception (`IndexError#badIndex`) and
the `onThrow` states the *condition* that it is out of bounds — not a specific
value. The array is a `Map int int` with a separate `alen` length. -/

-- Positive: `value(a, i)` throws `IndexError` recording the offending index when
-- `i` is out of bounds, and the `onThrow` states that the recorded index is out
-- of bounds (a condition, no specific value) — which holds because it equals `i`
-- on the throwing path.
#eval testLaurel <|
#strata
program Laurel;
composite Exception extends BaseException {}
composite IndexError extends Exception {
  badIndex: int
}
procedure value(a: Map int int, alen: int, i: int)
  returns (r: int)
  throws Exception
  onThrow (e) e is IndexError ==> ((e as IndexError)#badIndex < 0) || ((e as IndexError)#badIndex >= alen)
  opaque
  ensures r == select(a, i)
{
  if (i < 0) || (i >= alen) then {
    var ei: IndexError := new IndexError;
    ei#badIndex := i;
    throw ei
  };
  r := select(a, i)
};
#end

-- Negative: the `onThrow` claims the recorded index is *in* bounds, which
-- contradicts the throwing condition, so it cannot be proved.
#eval testLaurel <|
#strata
program Laurel;
composite Exception extends BaseException {}
composite IndexError extends Exception {
  badIndex: int
}
procedure valueBadContract(a: Map int int, alen: int, i: int)
  returns (r: int)
  throws Exception
  onThrow (e) e is IndexError ==> ((e as IndexError)#badIndex >= 0) && ((e as IndexError)#badIndex < alen)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  opaque
  ensures r == select(a, i)
{
  if (i < 0) || (i >= alen) then {
    var ei: IndexError := new IndexError;
    ei#badIndex := i;
    throw ei
  };
  r := select(a, i)
};
#end
/-! ## Simple field-value demos (concrete numbers)

The same binding field-dereference, in its simplest form: the thrown exception
carries a concrete value and the `onThrow` / `catch` reads it back. Easier to
follow at a glance than the relational versions above. -/

-- onThrow reads back a concrete field value (42).
#eval testLaurel <|
#strata
program Laurel;
composite Exception extends BaseException {}
composite IndexError extends Exception {
  index: int
}
procedure throwsFortyTwo()
  throws Exception
  onThrow (e) e is IndexError ==> (e as IndexError)#index == 42
  opaque
{
  var ei: IndexError := new IndexError;
  ei#index := 42;
  throw ei
};
#end

-- catch handler reads back a concrete field value (5), so `... - 5 == 0`.
#eval testLaurel <|
#strata
program Laurel;
composite Exception extends BaseException {}
composite IndexError extends Exception {
  index: int
}
procedure catchReadsFortyTwo()
  returns (r: int)
  opaque
  ensures r == 0
{
  r := 0;
  var ei: IndexError := new IndexError;
  ei#index := 5;
  try {
    throw ei
  } catch c when c is IndexError {
    r := (c as IndexError)#index - 5
  }
};
#end
