/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Typing of a `catch` binding, rejection side: a generic thrower throws at the instantiation its
call records, so a binding holding a `Cell` is a `Cell`, and passing it where a `BoxI` is
expected is rejected. Accepted, the write through `BoxI`'s `v` would leave the `Cell`'s unchanged
to the verifier, and `assert out == 5` would be proved.

The well-typed case, which also runs through the interpreters, lives in
`EndToEndTests/Execution/Exceptions/PolyProcedureThrows.lean`.
-/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Cell { var v: int }
composite BoxI { var v: int }
procedure setI(b: BoxI, x: int) opaque ensures b#v == x modifies b#v { b#v := x };
procedure thrS<S>(x: S) throws (e: S) opaque throwsOn true { ensures e == x } { throw x };

procedure asOtherComposite() returns (out: int) opaque modifies * {
  var c: Cell := new Cell;
  c#v := 5;
  try { thrS(c) } catch e { setI(e, 7) };
//                               ^ error: expected 'BoxI', got 'Cell'
  out := c#v;
  assert out == 5
};
#end
