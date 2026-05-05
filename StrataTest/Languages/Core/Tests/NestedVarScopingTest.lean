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

procedure test(cond : bool, x : int, y : int) {
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
info: ok: program Core;

procedure test (cond : bool, x : int, y : int)
{
  if (cond) {
    function f (a : int) : int { a + x }
    var r1 : int := f(10);
  } else {
    function f (a : int) : int { a + y }
    var r2 : int := f(20);
  }
};
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm issue436Pgm).stripMetaData))

---------------------------------------------------------------------
-- Regression test: variables declared inside a named block must not
-- leak to the parent scope.  Before the fix in Translate.lean,
-- `block_statement` propagated all bindings (including `var y`) to
-- the enclosing scope, causing `x` in `assert [use_x]: x == 2`
-- to resolve to `y` instead (wrong de Bruijn index).
---------------------------------------------------------------------

def blockScopePgm :=
#strata
program Core;

procedure test() {
  var x : int;
  x := 1;
  blk: {
    var y : int;
    y := 2;
    x := y;
  }
  assert [use_x]: x == 2;
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure test ()
{
  var x : int;
  x := 1;
  blk: {
    var y : int;
    y := 2;
    x := y;
  }
  assert [use_x]: x == 2;
};
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm blockScopePgm).stripMetaData))

---------------------------------------------------------------------
-- Regression test for issue #445: function declaration statement
-- had wrong arg order and scope, causing the body, subsequent
-- variable references, and function calls to resolve incorrectly.
---------------------------------------------------------------------

def issue445Pgm :=
#strata
program Core;

procedure test()
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
info: ok: program Core;

procedure test ()
{
  var x : int := 1;
  function safeDiv (y : int) : int { y div x }
  assert [assert_0]: 5 div x > 0;
  var z : int := safeDiv(5);
};
-/
#guard_msgs in
#eval (Std.format (Core.typeCheck .default (translatePgm issue445Pgm).stripMetaData))
