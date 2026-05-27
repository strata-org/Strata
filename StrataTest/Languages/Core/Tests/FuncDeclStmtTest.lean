/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core
import Strata.Languages.Core.DDMTransform.Translate

open Core
open Strata

def translate (t : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

def simpleFuncDeclPgm :=
#strata
program Core;

procedure test()
{
  var x : int := 1;
  function addX(y : int) : int
  { y + x }
  var z : int := addX(5);
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure test ()
{
  var x : int := 1;
  function addX (y : int) : int { y + x }
  var z : int := addX(5);
};
-/
#guard_msgs in
#eval (Std.format ((Core.typeCheck .default (translate simpleFuncDeclPgm).stripMetaData)))

-- Regression test for issue #1226: local function with ≥3 distinct-type args
-- Previously built wrong arrow type (int → real → bool → int instead of int → bool → real → int)
def localFuncDistinctTypesPgm :=
#strata
program Core;

procedure test()
{
  function f(x : int, b : bool, r : real) : int
  { x }
  var z : int := f(1, true, 0.0);
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure test ()
{
  function f (x : int, b : bool, r : real) : int { x }
  var z : int := f(1, true, 0.0);
};
-/
#guard_msgs in
#eval (Std.format ((Core.typeCheck .default (translate localFuncDistinctTypesPgm).stripMetaData)))
