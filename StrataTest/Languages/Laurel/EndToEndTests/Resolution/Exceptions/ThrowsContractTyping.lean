/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Typing and well-formedness of the exceptional contract: the `throws (e: T)` clause
and the `throwsOn` behavior cases (see the Exceptions section of the Laurel User
Guide). Enforcement of what may escape is `ThrowsEscape.lean`; shapes the lowering
cannot express are `UnsupportedExceptionShapes.lean`.

What is checked here:
  * the `throws` type may be any composite from the front end's own hierarchy —
    there is no built-in root it must extend;
  * a case's guard and each of its `ensures` are checked at `bool`;
  * a case is rejected when the procedure declares no `throws`, since there is no
    exceptional exit for it to describe and neither `EliminateExceptions` nor
    `ModifiesClauses` would lower it;
  * the thrown-value binding is in scope exactly in the cases' `ensures`, and a
    case may not name a value output, which does not exist on a throwing path.
-/


-- Valid: `throws` a composite. Recorded and ignored at translation, so the
-- procedure verifies with no diagnostics.
#eval testLaurelExecution {} <|
#strata
program Laurel;

composite ArithError {}

procedure mightThrow()
  throws (e: ArithError)
  opaque
{
  assert true
};
#end

-- Valid: a `throwsOn` case with a boolean guard and a boolean postcondition. The body
-- has to throw, because the guard `true` forces it.
#eval testLaurelExecution {} <|
#strata
program Laurel;

composite ArithError {}

procedure mightThrow2()
  throws (e: ArithError)
  opaque
  throwsOn true {
    ensures true
  }
{
  var x: ArithError := new ArithError;
  throw x
};
#end

-- Valid: a `throws` type is any composite from the front end's own hierarchy —
-- there is no built-in exception root it must extend.
#eval testLaurelExecution {} <|
#strata
program Laurel;

composite Failure {}

procedure throwsBareComposite()
  throws (e: Failure)
  opaque
{
  assert true
};
#end

-- Ill-typed: a case's postcondition is an int, not a bool.
#eval testLaurelExecution {} <|
#strata
program Laurel;

composite BadCondError {}

procedure badCaseEnsures()
  throws (e: BadCondError)
  opaque
  throwsOn true {
    ensures 5
//          ^ error: expected 'bool', got 'int'
  }
{
  assert true
};
#end

-- Ill-typed the other way: a case's *guard* is an int, not a bool.
#eval testLaurelExecution {} <|
#strata
program Laurel;

composite BadGuardError {}

procedure badThrowsOnGuard()
  throws (e: BadGuardError)
  opaque
  throwsOn 5 {
//         ^ error: expected 'bool', got 'int'
  }
{
  assert true
};
#end

-- A `throwsOn` case without a `throws` type is rejected: the procedure has no
-- exceptional exit for it to describe, and neither `EliminateExceptions` nor
-- `ModifiesClauses` would lower it, so it would be silently ignored rather than
-- checked. One diagnostic per case.
#eval testLaurelExecution {} <|
#strata
program Laurel;

composite Cell {
  value: int
}

procedure clausesWithoutThrows(c: Cell)
  opaque
  throwsOn true {
//         ^^^^ error: a `throwsOn` case describes the exceptional exit, so procedure 'clausesWithoutThrows' must declare a `throws` type
    ensures true
    modifies c
  }
  throwsOn false {
//         ^^^^^ error: a `throwsOn` case describes the exceptional exit, so procedure 'clausesWithoutThrows' must declare a `throws` type
  }
{
  assert true
};
#end

/-! ## Scope of the thrown-value binding

`throws (e: T)` scopes `e` over the `throwsOn` cases' `ensures` clauses only. It is not
in scope in a `requires`, in a top-level `ensures`, or in a case's *guard*: all three are
evaluated where there is no exception — the first two on the normal path, the guard on
entry, before any throw. No dedicated check is needed for this; the binding simply is not
defined there.

`throws` always binds, so there is no unbound form to test against: a procedure that
mentions nothing about its exception still names it. -/

-- The binding is not in scope in a `requires`.
#eval testLaurelExecution {} <|
#strata
program Laurel;

composite Err {}

procedure bindingInRequires(x: int)
  returns (r: int)
  throws (e: Err)
  requires e is Err
//         ^ error: 'e' is not defined
  opaque
  throwsOn x < 0 {
  }
{
  r := x
};
#end

-- Nor in a case's guard, which is a pre-state predicate.
#eval testLaurelExecution {} <|
#strata
program Laurel;

composite Err {}

procedure bindingInGuard(x: int)
  returns (r: int)
  throws (e: Err)
  opaque
  throwsOn e is Err {
//         ^ error: 'e' is not defined
  }
{
  r := x
};
#end

/-! ## A value output does not exist on the throwing path

A throwing procedure returns a single `Result` whose exceptional arm carries only the
thrown value, so a case that referred to a value output would read
`Result..value($result)` off a `Bad` result — an underspecified postcondition rather than
a diagnosable error. Inout parameters are exempt: they survive as outputs of the lowered
procedure. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;

composite Err {}

procedure valueOutputInCase(x: int)
  returns (r: int)
  throws (e: Err)
  opaque
  throwsOn x < 0 {
    ensures r == 0
//          ^^^^^^ error: a `throwsOn` case of procedure 'valueOutputInCase' refers to the value output 'r', which does not exist on the throwing path: a throwing procedure returns a single result whose exceptional arm carries only the thrown value
  }
{
  r := x
};
#end
