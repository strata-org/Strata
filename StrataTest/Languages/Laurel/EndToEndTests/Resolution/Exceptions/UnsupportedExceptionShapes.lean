/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Five exception source shapes that `EliminateExceptions` cannot yet lower are
rejected up front at resolution (`validateExceptionLowerability`) with a "not yet supported"
diagnostic, rather than surfacing downstream as an internal `strata-bug` or a
silent miscompile:

  1. a call to a `throws` procedure in a nested expression position (only a whole
     statement / whole assignment RHS is lowerable);
  2. a `catch` handler that re-declares its own exception binding (the name-based
     binding substitution is not scope-aware, so it would miscompile);
  3. a program that both uses exceptions and declares its own type named
     `Result`, which the injected result datatype would collide with;
  4. an exception escaping a `try` whose exception type is unrelated to the
     procedure's declared `throws` type, reachable under multiple inheritance —
     the propagation edge has no copy that type-checks, so the procedure-level
     exception variable would be left unassigned;
  5. a `throwsOn` guard that reads the heap — guards are pre-state predicates but
     the lowering places them in postconditions, so such a guard would silently
     be read in the post-state.

(An `exit` leaving a `try`/`finally` is *not* in this list: the lowering unwinds
it through the crossed `finally` arms, and its behavior is pinned in
`TryFinallyThrow`.)
-/

-- (1) A call to a `throws` procedure nested in an expression (`1 + f()`) is
-- rejected. `g` declares `throws` so the escape check is satisfied; only the
-- position guard fires.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite MyError {}
procedure f() returns (r: int) throws (e: MyError) opaque { r := 1 };
procedure g() returns (s: int) throws (e: MyError) opaque {
  s := 1 + f()
//         ^^^ not-yet-implemented: a call to a procedure that `throws` is not yet supported in this expression position
};
#end

-- (2) A `catch` handler that re-declares its binding name (`c`) is rejected.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite MyError {}
procedure catchShadowsBinding()
  opaque
{
  var e: MyError := new MyError;
  try {
    throw e
  } catch c {
    var c: int := 5;
//  ^^^^^^^^^^^^^^^ not-yet-implemented: re-declaring the `catch` binding 'c' inside its handler is not yet supported
    assert c == 5
  }
};
#end

-- (3) A user type named `Result` in a program that uses exceptions is rejected at
-- the declaration, naming the collision. Without this guard the program reaches
-- `EliminateExceptions`, which prepends its own `Result`, and the re-resolution
-- after the pass reports a duplicate definition plus a cascade of type errors
-- against the wrong `Result` — all of them internal-error diagnostics anchored on
-- synthesized nodes rather than on the user's declaration.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite MyError {}
datatype Result<A, B> {
//       ^^^^^^ not-yet-implemented: a program that uses exceptions may not declare a type named 'Result'
  Ok(a: A),
  Fail(b: B)
}
procedure usesExceptions() returns (r: int) throws (e: MyError) opaque {
  var e: MyError := new MyError;
  throw e
};
#end

-- A user type named `Result` is fine in a program that does *not* use exceptions:
-- nothing is injected, so there is nothing to collide with. This pins the guard to
-- the collision rather than to the name.
#eval testLaurelExecution {} <|
#strata
program Laurel;
datatype Result<A, B> {
  Ok(a: A),
  Fail(b: B)
}
procedure usesOwnResult() returns (r: Result<int, bool>) opaque {
  r := Ok(1)
};
#end


-- (4) Multiple inheritance makes the "unrelated propagation edge" reachable. `C`
-- extends both `A` and `B`, so a `try` whose thrown types join at `B` can escape a
-- `C` — which is a legal escape from a `throws A` procedure, since `C <: A`. The
-- lowering has no copy for that edge (`B` and `A` are unrelated, so neither a
-- widening nor a downcast type-checks), and before this guard the procedure-level
-- exception variable was simply left unassigned: the case below then failed with a
-- misleading "postcondition could not be proved".
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite A {}
composite B {}
composite B2 extends B {}
composite C extends A, B {}
procedure propagatesUnrelated(pick: bool)
  throws (e: A)
  opaque
  throwsOn true {
    ensures e is C
  }
{
  var c: C := new C;
  var b2: B2 := new B2;
  try {
//^ not-yet-implemented: an exception escaping this `try` is not yet supported here: the `try`'s exception type 'B' is unrelated to 'A'
    if pick then { throw c } else { throw b2 }
  } catch e when e is B2 {
    assert true
  }
};
#end

-- The same unrelated pair is fine when nothing escapes the `try`: the catch-all
-- absorbs both thrown types, so the lowering never needs a copy. This pins the
-- guard to an actual escape rather than to the types alone — the earlier,
-- single-inheritance-only reasoning would have rejected this too.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite A {}
composite B {}
composite B2 extends B {}
composite C extends A, B {}
procedure handlesUnrelated(pick: bool)
  throws (e: A)
  opaque
{
  var c: C := new C;
  var b2: B2 := new B2;
  try {
    if pick then { throw c } else { throw b2 }
  } catch e {
    assert true
  }
};
#end


-- A throwing procedure lowers to a single `Result<Val, T>` output for its
-- declared `throws T`, so it can carry at most one value output. A `throws`
-- procedure with two value outputs is rejected loudly (rather than silently
-- degrading the `Result` payload to a placeholder). The diagnostic names the
-- exceptional cause, not just the arity, so a front end reading it can tell why
-- an otherwise legal two-output signature was refused.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite E {}
procedure twoOut()
//        ^^^^^^ not-yet-implemented: a procedure that declares `throws` may return at most one value, because exception lowering packs its two possible outcomes into a single result
  returns (a: int, b: int)
  throws (e: E)
  opaque
{
  a := 1;
  b := 2
};
#end

-- (5) A `throwsOn` guard that reads the heap is rejected. A guard is a pre-state
-- predicate, but `EliminateExceptions` splices it into the forcing claim and each
-- case postcondition's antecedent, and `ModifiesClauses` into the exhaustiveness
-- disjunct — all postconditions, all read in the post-state. Over parameters that
-- is invisible, because an input holds the same value in both states; over the
-- heap it is not, and it is wrong in both directions. This shape is the unsound
-- one: the guard holds on entry (forced by the `requires`) and the body clears the
-- field *without* throwing, so under the documented semantics it must fail — yet
-- before this rejection it verified, letting a caller prove from the contract that
-- the call throws when it does not.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exception {}
composite Counter { var value: int }
procedure guardHeldNoThrow(c: Counter)
  throws (e: Exception)
  requires c#value > 0
  opaque
  modifies c
  throwsOn c#value > 0 {
//         ^^^^^^^^^^^ not-yet-implemented: a `throwsOn` guard that reads the heap is not yet supported
    modifies c
  }
{
  c#value := 0
};
#end

-- The other direction of the same reading: this body throws on exactly the
-- condition its guard names, but flips the field first. Under the documented
-- pre-state semantics it is correct; read in the post-state the exhaustiveness
-- disjunct sees the flipped value and cannot prove the cases cover the throwing
-- path. Rejecting the guard replaces that misleading failure with the real cause.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exception {}
composite Counter { var value: int }
procedure flipThenThrow(c: Counter)
  throws (e: Exception)
  opaque
  modifies c
  throwsOn c#value > 0 {
//         ^^^^^^^^^^^ not-yet-implemented: a `throwsOn` guard that reads the heap is not yet supported
    modifies c
  }
{
  if c#value > 0 then {
    c#value := -1;
    var ex: Exception := new Exception;
    throw ex
  }
};
#end

-- A guard over parameters alone is accepted: an input binding holds the same
-- value in the pre- and post-state, so placing it in a postcondition preserves
-- its meaning. This is the shape a front end emits, and the workaround the
-- diagnostic recommends — hoist the heap read into a parameter and tie it to the
-- field with a `requires`, as `Execution/Exceptions/ThrowsOnClause.lean` does for
-- the array-bounds case. The guard may still be *about* heap state; it just may
-- not read it.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exception {}
composite Counter { var value: int }
procedure guardOverParameter(c: Counter, seen: int)
  throws (e: Exception)
  requires seen == c#value
  opaque
  modifies c
  throwsOn seen > 0 {
    modifies c
  }
{
  if seen > 0 then {
    c#value := -1;
    var ex: Exception := new Exception;
    throw ex
  }
};
#end
