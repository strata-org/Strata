/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Typing of the structured handler, rejection side: a `catch` clause's `when` guard is
an ordinary boolean expression, so a non-boolean guard is a type error reported
during resolution — the pipeline never reaches translation.

The well-typed cases, which also run through the interpreter, live in
`EndToEndTests/Execution/Exceptions/TryCatchThrow.lean`.
-/

-- Ill-typed: the `when` guard is an int, not a bool.
#eval testLaurelExecution {} <|
#strata
program Laurel;

procedure badGuard()
  opaque
{
  try {
    assert true
  } catch e when 5 {
//               ^ error: expected 'bool', got 'int'
    assert true
  }
};
#end

-- A union guard whose operand is not boolean.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite ParseError {}
procedure badUnionGuard() opaque {
  try {
    assert true
  } catch e when e is ParseError || 5 {
//                                  ^ error: expected 'bool', got 'int'
    assert true
  }
};
#end
