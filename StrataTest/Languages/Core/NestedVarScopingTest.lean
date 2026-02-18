/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core
import Strata.Languages.Core.DDMTransform.Translate

namespace Strata

open Core

def translatePgm (p : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

---------------------------------------------------------------------
-- Regression test for issue #436: function declared in if-branches
-- should have correct bodies. Without the fix, the second function's
-- body captured variables from the then-branch instead of the else-branch.
---------------------------------------------------------------------

def issue436Pgm : Strata.Program :=
#strata
program Core;

procedure test(cond : bool, x : int, y : int) returns () {
  if (cond) {
    function f(a : int) : int { a + x }
    var r1 : int := f(10);
  } else {
    function f(a : int) : int { a + y }
    var r2 : int := f(20);
  }
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: procedure test (cond : bool, x : int, y : int) returns ()
{
  if(cond){
    |$_then|: {
      function f (a : int) : int { a + x }
      var r1 : int := f(10);
      }}else{
    |$_else|: {
      function f (a : int) : int { a + y }
      var r2 : int := f(20);
      }}};

-/
#guard_msgs in
#eval (Std.format (Core.typeCheck Options.default (translatePgm issue436Pgm).stripMetaData))

---------------------------------------------------------------------
-- Regression test for issue #445: function declaration statement
-- had wrong arg order and scope, causing the body, subsequent
-- variable references, and function calls to resolve incorrectly.
---------------------------------------------------------------------

def issue445Pgm :=
#strata
program Core;

procedure test() returns ()
{
  var x : int := 1;
  function safeDiv(y : int) : int
    { y div x }
  assert 5 div x > 0;
  var z : int := safeDiv(5);
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: procedure test () returns ()
{
  var x : int := 1;
  function safeDiv (y : int) : int { y div x }
  assert [assert_0]: 5 div x > 0;
  var z : int := safeDiv(5);
  };

-/
#guard_msgs in
#eval (Std.format (Core.typeCheck Options.default (translatePgm issue445Pgm).stripMetaData))
