/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
`try` / `catch` + `throw`: which handler runs, and what it can see. No `finally`
(that is `TryFinallyThrow.lean`) and no calls (`ThrowsClause.lean` and
`ThrowsOnClause.lean`).

The lowering turns a `try` into a labeled block whose exits reach a chain of guarded
handlers, so the observable claims are:
  * a caught `throw` abandons the rest of the body, and control resumes after the
    handler rather than at the throw;
  * dispatch is first-match-wins in source order — an earlier non-matching guard is
    skipped, and an earlier *matching* guard wins even when a later one is more
    specific;
  * a guard may be a union (`e is A || e is B`) or absent altogether (catch-all);
  * the binding is per handler, so a nested `try` inside a handler does not clobber
    the value the outer handler caught;
  * the binding's *type* is the least common ancestor of what the body can throw,
    which is a hard requirement — unrelated thrown types have no join and are
    rejected.

The first two cases are the construct's smoke test: they check that the whole shape,
`finally` arm included, parses, resolves, type-checks, lowers, and runs. They throw
nothing, so they need no exception objects and hence no heap, which lets them run
under `testLaurelMultiple` — verifier *and* interpreter. Everything after them throws
a composite, so its exception values live on the heap and the interpret path cannot
run it yet. The other file that runs both ways is `Throw.lean`, whose primitive
section allocates nothing either.

Exceptions are constructed *before* the `try` (a `new` inside a `try` body hits a
known lifting-pass gap), and all throws are direct so the verifier knows each value's
runtime type and can discharge the `is`-guards precisely.

The typing rejections for the same construct live in
`EndToEndTests/Resolution/Exceptions/CatchGuardTyping.lean`.
-/

-- Well-typed try / catch / finally: parses, resolves, type-checks, lowers, and both
-- verifies and interprets (the bodies have no failing proof obligations).
#eval testLaurelMultiple <|
#strata
program Laurel;

procedure tryCatchFinally() entry
  opaque
{
  try {
    assert true
  } catch e {
    assert true
  } finally {
    assert true
  }
};
#end

-- Well-typed catch with a boolean `when` guard.
#eval testLaurelMultiple <|
#strata
program Laurel;

procedure tryWithGuard() entry
  opaque
{
  try {
    assert true
  } catch e when true {
    assert true
  }
};
#end

/-! ## Handler selection and the caught binding -/

-- A caught `throw` skips the rest of the try body; the handler runs and control
-- resumes after the `try`, so the handler's assignment is what is observed. The
-- guard `c is MyError` is satisfied by the thrown value, so the clause fires.
#eval testLaurel <|
#strata
program Laurel;
composite MyError {}
procedure caughtResumes()
  returns (r: int)
  opaque
{
  var e: MyError := new MyError;
  r := 0;
  try {
    throw e;
    r := 1
  } catch c when c is MyError {
    r := 2
  };
  assert r == 2
};
#end

-- Predicate dispatch skips a non-matching earlier clause and takes the matching
-- later one. `ErrorA` is a subtype of `ErrorB`, and the thrown value is a plain
-- `ErrorB`: it is not the more-specific `ErrorA` (so `is ErrorA` skips), but it
-- is an `ErrorB` (so `is ErrorB` matches).
#eval testLaurel <|
#strata
program Laurel;
composite ErrorB {}
composite ErrorA extends ErrorB {}
procedure dispatchSkipsNonMatching()
  returns (r: int)
  opaque
{
  var b: ErrorB := new ErrorB;
  r := 0;
  try {
    throw b
  } catch c when c is ErrorA {
    r := 1
  } catch c when c is ErrorB {
    r := 2
  };
  assert r == 2
};
#end

-- First-match-wins with overlapping guards: a `ChildError` matches both the
-- earlier `is ParentError` clause and the later `is ChildError` clause; the
-- earlier one wins (r == 1, not 2).
#eval testLaurel <|
#strata
program Laurel;
composite ParentError {}
composite ChildError extends ParentError {}
procedure firstMatchWinsOnOverlap()
  returns (r: int)
  opaque
{
  var ce: ChildError := new ChildError;
  r := 0;
  try {
    throw ce
  } catch c when c is ParentError {
    r := 1
  } catch c when c is ChildError {
    r := 2
  };
  assert r == 1
};
#end

-- Multiple ordered catch clauses (first-match-wins).
#eval testLaurel <|
#strata
program Laurel;
composite ParseError {}
composite ArithError {}
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

-- Union multi-catch: one clause matching either type.
#eval testLaurel <|
#strata
program Laurel;
composite ParseError {}
composite ArithError {}
procedure unionCatch() opaque {
  try {
    assert true
  } catch e when e is ParseError || e is ArithError {
    assert true
  }
};
#end

-- The same union written with `|` instead of `||`. Laurel has two disjunctions — `|`
-- is `Or`, `||` is the short-circuiting `OrElse` — and `catchGuardCatches` matches
-- each in its own arm. Both arms feed the escape check and the least-common-ancestor
-- collection, so a guard shape that stopped being recognised there would silently
-- change which exceptions count as caught. The case above covers `OrElse`; this one
-- covers `Or`.
#eval testLaurel <|
#strata
program Laurel;
composite ParseError {}
composite ArithError {}
procedure unionCatchNonShortCircuit() opaque {
  try {
    assert true
  } catch e when e is ParseError | e is ArithError {
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

-- Nested try/catch (the outer handler is what reaches lowering first).
#eval testLaurel <|
#strata
program Laurel;
composite ParseError {}
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

-- A `catch` handler dereferences a field of the (cast) exception binding and
-- checks a *condition* on it: the caught `IndexError` records the offending
-- index, and on the handler path (reached only via the out-of-bounds throw) that
-- recorded index is provably out of bounds.
#eval testLaurel <|
#strata
program Laurel;
composite Exception {}
composite IndexError extends Exception {
  badIndex: int
}
procedure catchReadsField(alen: int, i: int)
  returns (r: int)
  opaque
  ensures r >= 0
{
  r := 0;
  var ei: IndexError := new IndexError;
  ei#badIndex := i;
  try {
    if (i < 0) || (i >= alen) then {
      throw ei
    };
    r := i
  } catch c when c is IndexError {
    assert ((c as IndexError)#badIndex < 0) || ((c as IndexError)#badIndex >= alen);
    r := 0
  }
};
#end

-- Nested `catch`: a handler's binding must survive a throw that occurs *inside*
-- that handler and is caught by a nested `try`/`catch`. The outer handler binds
-- `a` (an `Outer` carrying tag == 1); inside it a nested `try` throws `Inner`,
-- which is caught. Afterwards the outer handler reads `a` again — it must still
-- refer to the original `Outer` (tag == 1), not the inner exception. This
-- exercises the per-handler snapshot of the caught value (a single shared `$exc`
-- is overwritten by the inner throw).
#eval testLaurel <|
#strata
program Laurel;
composite Outer {
  tag: int
}
composite Inner {}
procedure nestedCatchKeepsBinding()
  returns (r: int)
  opaque
  ensures r == 1
{
  var outerExn: Outer := new Outer;
  outerExn#tag := 1;
  var innerExn: Inner := new Inner;
  r := 0;
  try {
    throw outerExn
  } catch a when a is Outer {
    try {
      throw innerExn
    } catch b when b is Inner {
      r := 0
    };
    assert (a as Outer)#tag == 1;
    r := (a as Outer)#tag
  }
};
#end

/-! ## Typing the catch binding at its least common ancestor

A `catch` binding is typed at the least common ancestor of everything the `try` body
can throw - direct `throw`s plus the declared `throws` of callees - so a handler may
use that supertype's members without a downcast, and each front end keeps its own
hierarchy with no built-in root imposed.

Negative first: the LCA typing is a *requirement*, not a
best-effort. Two exception types with no shared ancestor cannot be joined, so
there is no type to bind `e` at and resolution rejects the `try` — the binding
would otherwise be silently untyped, and a handler could then dereference a field
no reaching value has. This is the one hard error in the LCA rule (an
undeterminable/empty thrown set falls back to `Unknown` instead).
-/
#eval testLaurel <|
#strata
program Laurel;
composite Unrelated1 {}
composite Unrelated2 {}
procedure noCommonAncestor(pick: bool)
  opaque
{
  var a: Unrelated1 := new Unrelated1;
  var b: Unrelated2 := new Unrelated2;
  try {
//^ error: the exception types thrown in this `try` block (Unrelated1, Unrelated2) have no common ancestor; a `catch` binding needs a single least-common-ancestor type
    if pick then {
      throw a
    } else {
      throw b
    }
  } catch e {
    assert true
  }
};
#end

-- A `try` body that can throw two related types: the catch binding is typed at
-- their least common ancestor (`Exception`), so a guard `e is Exception`
-- type-checks and the program verifies. (A body throwing two *unrelated* types
-- would be rejected — no common ancestor to type the binding at.)
#eval testLaurel <|
#strata
program Laurel;
composite Exception {}
composite ParseError extends Exception {}
composite ArithError extends Exception {}
procedure catchAtLca(pick: bool) opaque {
  var p: ParseError := new ParseError;
  var a: ArithError := new ArithError;
  try {
    if pick then {
      throw p
    } else {
      throw a
    }
  } catch e when e is Exception {
    assert true
  }
};
#end

-- A nested `try` whose own catches fully absorb the types thrown in its body
-- must not leak those into the *outer* catch binding's least-common-ancestor.
-- Here the inner body throws `Alpha`/`Beta` (both caught by `is InnerRoot`), and
-- the only type that escapes the outer body is the unrelated `Gamma`. So the
-- outer binding is typed at `Gamma` and the program verifies — rather than being
-- rejected for "no common ancestor" over `Alpha`/`Beta`, which never reach it.
#eval testLaurel <|
#strata
program Laurel;
composite InnerRoot {}
composite Alpha extends InnerRoot {}
composite Beta extends InnerRoot {}
composite Gamma {}
procedure nestedFullyCaught(c: bool) opaque {
  var a: Alpha := new Alpha;
  var b: Beta := new Beta;
  var g: Gamma := new Gamma;
  try {
    try {
      if c then {
        throw a
      } else {
        throw b
      }
    } catch e when e is InnerRoot {
      assert true
    };
    throw g
  } catch outer when outer is Gamma {
    assert true
  }
};
#end

/-! ## Loops inside an exception region

`eliminateDoWhile` runs *before* `eliminateExceptions`, so by the time the exceptional
channel is lowered a loop has already become its guarded/havoc encoding. The two
lowerings therefore genuinely meet, and these cases pin that the meeting point works:
a `throw` leaving a loop body still reaches the handler with its type intact, and a
loop invariant still discharges inside a `try` region.

Note what is *not* claimed. Under the loop encoding the verifier knows only the
invariant and the negated condition after the loop, not how many iterations ran — so
whether the throwing branch was taken is not provable, and neither case asserts it.
Instead the handler asserts what must hold *if* it runs, which is a real obligation
that a broken `$exc` would fail. -/

-- A `throw` from inside a loop body: the handler still binds the thrown value at its
-- type, even though the throw crossed the loop's lowered guard/havoc encoding on the
-- way out. `assert c is Err` is vacuous if the handler never runs, and a genuine
-- obligation if it does.
#eval testLaurel <|
#strata
program Laurel;
composite Err {}
procedure loopBodyThrowIsCaught(n: int)
  returns (r: int)
  opaque
  ensures r >= 0
{
  var e: Err := new Err;
  r := 0;
  try {
    var i: int := 0;
    while(i < n)
      invariant i >= 0
    {
      if i > 2 then {
        throw e
      };
      i := i + 1
    };
    r := 1
  } catch c {
    assert c is Err;
    r := 2
  }
};
#end

-- A `try` wrapping a loop that carries invariants: the invariants discharge inside the
-- exception region exactly as they would outside it. `assert i == n` after the loop
-- follows from `i <= n` plus the negated condition, so it is the evidence that the
-- invariant survived being lowered inside a `try` body.
#eval testLaurel <|
#strata
program Laurel;
composite Err {}
procedure invariantHoldsInsideTry(n: int)
  returns (r: int)
  requires n >= 0
  opaque
  ensures r >= 0
{
  r := 0;
  try {
    var i: int := 0;
    while(i < n)
      invariant i >= 0
      invariant i <= n
    {
      i := i + 1
    };
    assert i == n;
    r := i
  } catch c {
    r := 0
  }
};
#end
