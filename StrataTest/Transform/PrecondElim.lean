/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.Languages.Core.Core
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.ProgramType
import Strata.Transform.PrecondElim

open Core
open Core.PrecondElim
open Strata

/-! ## PrecondElim Tests

These test the result of the `PrecondElim` transformation.
For the full verification pipeline with function preconditions,
see `StrataTest/Languages/Core/Examples/FunctionPreconditions.lean`.
-/

section PrecondElimTests

def translate (t : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

def transformProgram (t : Strata.Program) : Core.Program :=
  let program := translate t
  match Core.Transform.run program (PrecondElim.precondElim · Core.Factory) with
  | .error e => panic! s!"PrecondElim failed: {e}"
  | .ok (_changed, program) =>
    match Core.typeCheck Options.default program with
    | .error e => panic! s!"Type check failed: {Std.format e}"
    | .ok program => program.eraseTypes.stripMetaData

/-! ### Test 1: Procedure body with div call gets assert for y != 0 -/

def divInBodyPgm :=
#strata
program Core;

procedure test(a : int) returns ()
{
  var z : int := 10 / a;
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: procedure test (a : int) returns ()
{
  assert [init_calls_Int.SafeDiv_0]: !(a == 0);
  var z : int := 10 / a;
  };
-/
#guard_msgs in
#eval (Std.format (transformProgram divInBodyPgm))

/-! ### Test 2: Function whose precondition calls a partial function -/

def funcWithPrecondPgm :=
#strata
program Core;

function safeMod(x : int, y : int) : int
  requires y != 0;
{ x % y }

function foo(x : int, y : int) : int
  requires safeMod(x, y) > 0;
{ x + y }

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: procedure |safeMod$$wf| (x : int, y : int) returns ()
{
  assume [precond_safeMod_0]: !(y == 0);
  assert [safeMod_body_calls_Int.SafeMod_0]: !(y == 0);
  };
function safeMod (x : int, y : int) : int {
  x % y
}
procedure |foo$$wf| (x : int, y : int) returns ()
{
  assert [foo_precond_calls_safeMod_0]: !(y == 0);
  assume [precond_foo_0]: safeMod(x, y) > 0;
  };
function foo (x : int, y : int) : int {
  x + y
}
-/
#guard_msgs in
#eval (Std.format (transformProgram funcWithPrecondPgm))

/-! ### Test 3: Procedure with ADT destructor (has implicit precondition) in requires -/

def procContractADTPgm :=
#strata
program Core;

datatype List { Nil(), Cons(head : int, tail : List) };

inline function safeHead(xs : List) : int
  requires List..isCons(xs);
{ List..head(xs) }

procedure test(xs : List) returns ()
spec {
  requires List..isCons(xs);
  requires safeHead(xs) > 0;
}
{
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: datatype List {(
  (Nil())),
  (Cons(head : int, tail : List))
};
function safeHead (xs : List) : int {
  List..head(xs)
}
procedure |test$$wf| (xs : List) returns ()
{
  assume [test_requires_0]: List..isCons(xs);
  assert [test_pre_test_requires_1_calls_safeHead_0]: List..isCons(xs);
  assume [test_requires_1]: safeHead(xs) > 0;
  };
procedure test (xs : List) returns ()
spec {
  requires [test_requires_0]: List..isCons(xs);
  requires [test_requires_1]: safeHead(xs) > 0;
  } {
  };
-/
#guard_msgs in
#eval (Std.format (transformProgram procContractADTPgm))

/-! ### Test 4: Multiple requires, second depends on first for well-formedness -/

def dependentRequiresPgm :=
#strata
program Core;

datatype List { Nil(), Cons(head : int, tail : List) };

inline function safeHead(xs : List) : int
  requires List..isCons(xs);
{ List..head(xs) }

inline function safeTail(xs : List) : List
  requires List..isCons(xs);
{ List..tail(xs) }

procedure test(xs : List) returns ()
spec {
  requires List..isCons(xs);
  ensures safeHead(xs) > 0;
  ensures safeHead(safeTail(xs)) > 0;
}
{
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: datatype List {(
  (Nil())),
  (Cons(head : int, tail : List))
};
function safeHead (xs : List) : int {
  List..head(xs)
}
function safeTail (xs : List) : List {
  List..tail(xs)
}
procedure |test$$wf| (xs : List) returns ()
{
  assume [test_requires_0]: List..isCons(xs);
  assert [test_post_test_ensures_1_calls_safeHead_0]: List..isCons(xs);
  assume [test_ensures_1]: safeHead(xs) > 0;
  assert [test_post_test_ensures_2_calls_safeHead_0]: List..isCons(safeTail(xs));
  assert [test_post_test_ensures_2_calls_safeTail_1]: List..isCons(xs);
  assume [test_ensures_2]: safeHead(safeTail(xs)) > 0;
  };
procedure test (xs : List) returns ()
spec {
  requires [test_requires_0]: List..isCons(xs);
  ensures [test_ensures_1]: safeHead(xs) > 0;
  ensures [test_ensures_2]: safeHead(safeTail(xs)) > 0;
  } {
  };
-/
#guard_msgs in
#eval (Std.format (transformProgram dependentRequiresPgm))

/-! ### Test 5: Function decl statement with precondition referencing local variable -/

def funcDeclPrecondPgm :=
#strata
program Core;

procedure test() returns ()
{
  var x : int := 1;
  function safeDiv(y : int) : int
    requires y / x > 0;
    { y / x }
  var z : int := safeDiv(5);
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: procedure test () returns ()
{
  var x : int := 1;
  |safeDiv$$wf|: {
    var y : int;
    assert [safeDiv_precond_calls_Int.SafeDiv_0]: !(x == 0);
    assume [precond_safeDiv_0]: y / x > 0;
    assert [safeDiv_body_calls_Int.SafeDiv_0]: !(x == 0);
    }
  function safeDiv (y : int) : int { y / x }
  assert [init_calls_safeDiv_0]: 5 / x > 0;
  var z : int := safeDiv(5);
  };
-/
#guard_msgs in
#eval (Std.format (transformProgram funcDeclPrecondPgm))

/-! ### Test 6: Inline function declarations in both branches of if-then-else with different preconditions -/

def inlineFuncInIteSimplePgm :=
#strata
program Core;

procedure test(cond : bool, x : int, y : int) returns ()
{
  if (cond) {
    function f(a : int) : int
      requires x != 0;
      { a / x }
    var r1 : int := f(10);
  } else {
    function f(a : int) : int
      requires y != 0;
      { a / y }
    var r2 : int := f(20);
  }
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: procedure test (cond : bool, x : int, y : int) returns ()
{
  if (cond) {
    |f$$wf|: {
      var a : int;
      assume [precond_f_0]: !(x == 0);
      assert [f_body_calls_Int.SafeDiv_0]: !(x == 0);
      }
    function f (a : int) : int { a / x }
    assert [init_calls_f_0]: !(x == 0);
    var r1 : int := f(10);
    } else {
    |f$$wf|: {
      var a : int;
      assume [precond_f_0]: !(y == 0);
      assert [f_body_calls_Int.SafeDiv_0]: !(y == 0);
      }
    function f (a : int) : int { a / y }
    assert [init_calls_f_0]: !(y == 0);
    var r2 : int := f(20);
    }
  };
-/
#guard_msgs in
#eval (Std.format (transformProgram inlineFuncInIteSimplePgm))

/-! ### Test 7: Same function name in multiple procedures with different preconditions -/

def funcInMultipleProcsPgm :=
#strata
program Core;

procedure proc1(x : int) returns ()
{
  function f(a : int) : int
    requires x != 0;
    { a / x }
  var r : int := f(10);
};

procedure proc2(y : int) returns ()
{
  function f(a : int) : int
    requires y != 0;
    { a / y }
  var r : int := f(20);
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: procedure proc1 (x : int) returns ()
{
  |f$$wf|: {
    var a : int;
    assume [precond_f_0]: !(x == 0);
    assert [f_body_calls_Int.SafeDiv_0]: !(x == 0);
    }
  function f (a : int) : int { a / x }
  assert [init_calls_f_0]: !(x == 0);
  var r : int := f(10);
  };
procedure proc2 (y : int) returns ()
{
  |f$$wf|: {
    var a : int;
    assume [precond_f_0]: !(y == 0);
    assert [f_body_calls_Int.SafeDiv_0]: !(y == 0);
    }
  function f (a : int) : int { a / y }
  assert [init_calls_f_0]: !(y == 0);
  var r : int := f(20);
  };
-/
#guard_msgs in
#eval (Std.format (transformProgram funcInMultipleProcsPgm))

end PrecondElimTests
