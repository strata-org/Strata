/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Broad coverage of the exception-handling surface implemented so far
(E1–E4; see `docs/design/laurel_extensions.md`): the `BaseException`
hierarchy, `throw`, predicate-based `try`/`catch`/`finally`, and the
`throws`/`onThrow` procedure contract.

Two observable behaviors are pinned down here:
  * well-formed `throw` (in a procedure declaring `throws`) and `try` / `catch` /
    `finally` constructs lower to Core (E7) and verify;
  * well-formed `throws`/`onThrow` contracts are recorded, ignored at
    translation, and so verify cleanly (no diagnostics);
  * ill-typed constructs are rejected during resolution.

Handler bodies are kept free of calls and of dereferences of the catch/onThrow
binding, to stay clear of the known post-`heapParameterization` rough edges.
-/

/-! ## Structured handlers (E3/E5) -/

-- Multiple ordered catch clauses (first-match-wins).
#eval testLaurel <|
#strata
program Laurel;
composite ParseError extends BaseException {}
composite ArithError extends BaseException {}
procedure multipleCatches() opaque {
  try {
    assert true
  } catch e when e is ParseError {
    assert true
  } catch e when e is ArithError {
    assert true
  }
};
#end

-- Union multi-catch: one clause matching either type (F11).
#eval testLaurel <|
#strata
program Laurel;
composite ParseError extends BaseException {}
composite ArithError extends BaseException {}
procedure unionCatch() opaque {
  try {
    assert true
  } catch e when e is ParseError || e is ArithError {
    assert true
  }
};
#end

-- Catch-all clause (no guard).
#eval testLaurel <|
#strata
program Laurel;
procedure catchAll() opaque {
  try {
    assert true
  } catch e {
    assert true
  }
};
#end

-- `try` with only a `finally` arm (no catch).
#eval testLaurel <|
#strata
program Laurel;
procedure tryFinally() opaque {
  try {
    assert true
  } finally {
    assert true
  }
};
#end

-- Nested try/catch (the outer handler is what reaches lowering first).
#eval testLaurel <|
#strata
program Laurel;
composite ParseError extends BaseException {}
procedure nestedTry() opaque {
  try {
    try {
      assert true
    } catch inner {
      assert true
    }
  } catch outer when outer is ParseError {
    assert true
  }
};
#end

/-! ## Throwing (E1/E2) -/

-- Throw a value of a declared subtype of BaseException. The procedure declares
-- `throws`, so this lowers to a `Result`-returning Core procedure (E7) and
-- verifies (no proof obligations).
#eval testLaurel <|
#strata
program Laurel;
composite ParseError extends BaseException {}
procedure throwsSubtype() throws BaseException opaque {
  var e: ParseError := new ParseError;
  throw e
};
#end

/-! ## Exceptional contract (E4) — recorded, verifies clean -/

-- Multi-throws modeling: a coarsened `throws` type plus the precise set in an
-- `onThrow` predicate (this is how a Java `throws A, B` is represented).
#eval testLaurel <|
#strata
program Laurel;
composite ParseError extends BaseException {}
composite ArithError extends BaseException {}
procedure multiThrows()
  throws BaseException
  onThrow (e) e is ParseError || e is ArithError
  opaque
{
  assert true
};
#end

-- Per-type `onThrow` clauses. Multiple clauses conjoin, so each is written as a
-- guarded implication `e is T ==> <property of a T>`: the guard scopes the claim
-- to its own type, so the clauses coexist. (Contrast bare `onThrow (e) e is A` +
-- `onThrow (e) e is B`, which conjoin to "the value is both A and B" — a
-- contradiction for disjoint siblings, i.e. "throws neither".)
--
-- With field access on the binding, this same shape would let us state per-type
-- *value* properties, e.g.
--     onThrow (e) e is ParseError ==> (e as ParseError)#position >= 0
-- Dereferencing the binding (`(e as T)#field`) is deliberately omitted here: it
-- type-checks, but re-resolution after `heapParameterization` (which moves
-- composite fields into the heap) can no longer find the field, so it currently
-- trips a strata-bug. The consequents are kept field-free until that gap is
-- closed (and until E7 lowering actually consumes these contracts).
#eval testLaurel <|
#strata
program Laurel;
composite ParseError extends BaseException {}
composite ArithError extends BaseException {}
procedure perTypeOnThrow()
  throws BaseException
  onThrow (e) e is ParseError ==> !(e is ArithError)
  onThrow (e) e is ArithError ==> !(e is ParseError)
  opaque
{
  assert true
};
#end

-- Deeper hierarchy: a tighter `throws` type (an intermediate ancestor).
#eval testLaurel <|
#strata
program Laurel;
composite AppException extends BaseException {}
composite ParseError extends AppException {}
procedure tighterThrows()
  throws AppException
  onThrow (e) e is ParseError
  opaque
{
  assert true
};
#end

/-! ## Negative cases -/

-- A union guard whose operand is not boolean.
#eval testLaurel <|
#strata
program Laurel;
composite ParseError extends BaseException {}
procedure badUnionGuard() opaque {
  try {
    assert true
  } catch e when e is ParseError || 5 {
//                                  ^ error: expected 'bool', got 'int'
    assert true
  }
};
#end

-- A `throws` type that is a composite but not a BaseException subtype.
#eval testLaurel <|
#strata
program Laurel;
composite NotAnError {}
procedure badThrowsComposite()
  throws NotAnError
//       ^^^^^^^^^^ error: throws type must be a subtype of 'BaseException'
  opaque
{
  assert true
};
#end
