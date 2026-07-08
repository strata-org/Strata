/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
The `when C throws (e) P` exceptional behavior case (E4).

`onThrow (e) P` is a postcondition on the Bad path ("if it throws, `P` holds").
`when C throws (e) P` is a *behavior case*: it pairs a pre-state trigger `C` with an
exceptional postcondition `P` (with `e` bound to the thrown value). Meaning: "if
`C` holds on entry, the procedure exits exceptionally and `P` holds of the thrown
value." It lowers to a Core postcondition
`C ==> (Result..isBad($result) ∧ P[e := err])` — checked on exit (so the body
must honor it) and assumed at call sites (so a caller can prove a throw *will*
happen and what then holds). Scoped to triggers over inputs, partial semantics.
-/

-- Positive: the body throws exactly when `b == 0`, and the thrown value is an
-- `ArithmeticException`, so `when b == 0 throws (e) e is ArithmeticException` holds.
#eval testLaurel <|
#strata
program Laurel;
composite Exception extends BaseException {}
composite ArithmeticException extends Exception {}
procedure div(a: int, b: int)
  returns (r: int)
  throws Exception
  when b == 0 throws (e) e is ArithmeticException
  opaque
{
  if b == 0 then {
    var ae: ArithmeticException := new ArithmeticException;
    throw ae
  };
  r := a / b
};
#end

-- Negative: the case declares a throw when `b == 0`, but the body never throws,
-- so the trigger part cannot be proved on exit.
#eval testLaurel <|
#strata
program Laurel;
composite Exception extends BaseException {}
composite ArithmeticException extends Exception {}
procedure divBad(a: int, b: int)
  returns (r: int)
  throws Exception
  when b == 0 throws (e) e is ArithmeticException
//     ^^^^^^ error: assertion could not be proved
  opaque
{
  r := 0
};
#end

-- Caller-side use: from an opaque (bodiless) procedure's behavior case, the
-- caller proves the throw definitely happens — calling with `b == 0` must take
-- the `catch` branch (so `out` ends at 99, never 1).
#eval testLaurel <|
#strata
program Laurel;
composite Exception extends BaseException {}
procedure mustThrow(a: int, b: int)
  returns (r: int)
  throws Exception
  when b == 0 throws (e) true;
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
