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
  match Core.Transform.run program PrecondElim.precondElim { Core.Transform.CoreTransformState.emp with factory := some Core.Factory } with
  | .error e => panic! s!"PrecondElim failed: {e}"
  | .ok (_changed, program) =>
    match Core.typeCheck Core.VerifyOptions.default program with
    | .error e => panic! s!"Type check failed: {Std.format e}"
    | .ok program => program.eraseTypes.stripMetaData

/-! ### Test 1: Procedure body with div call gets assert for y != 0 -/

def divInBodyPgm :=
#strata
program Core;

procedure test(a : int)
{
  var z : int := 10 / a;
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

procedure test (a : int)
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
info: program Core;

procedure safeMod$$wf (x : int, y : int)
{
  assume [precond_safeMod_0]: !(y == 0);
  assert [safeMod_body_calls_Int.SafeMod_0]: !(y == 0);
};
function safeMod (x : int, y : int) : int {
  x % y
}
procedure foo$$wf (x : int, y : int)
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

procedure test(xs : List)
spec {
  requires List..isCons(xs);
  requires List..head(xs) > 0;
}
{
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

datatype List {
  Nil(),
  Cons(head : int, tail : List)
};
procedure test$$wf (xs : List)
{
  assume [test_requires_0]: List..isCons(xs);
  assert [test_pre_test_requires_1_calls_List..head_0]: List..isCons(xs);
  assume [test_requires_1]: List..head(xs) > 0;
};
procedure test (xs : List)
spec {
  requires [test_requires_0]: List..isCons(xs);
  requires [test_requires_1]: List..head(xs) > 0;
  } {
  ⏎
};
-/
#guard_msgs in
#eval (Std.format (transformProgram procContractADTPgm))

/-! ### Test 4: Multiple requires, second depends on first for well-formedness -/

def dependentRequiresPgm :=
#strata
program Core;

datatype List { Nil(), Cons(head : int, tail : List) };

procedure test(xs : List)
spec {
  requires List..isCons(xs);
  ensures List..head(xs) > 0;
  ensures List..head(List..tail(xs)) > 0;
}
{
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

datatype List {
  Nil(),
  Cons(head : int, tail : List)
};
procedure test$$wf (xs : List)
{
  assume [test_requires_0]: List..isCons(xs);
  assert [test_post_test_ensures_1_calls_List..head_0]: List..isCons(xs);
  assume [test_ensures_1]: List..head(xs) > 0;
  assert [test_post_test_ensures_2_calls_List..tail_0]: List..isCons(xs);
  assert [test_post_test_ensures_2_calls_List..head_1]: List..isCons(List..tail(xs));
  assume [test_ensures_2]: List..head(List..tail(xs)) > 0;
};
procedure test (xs : List)
spec {
  requires [test_requires_0]: List..isCons(xs);
  ensures [test_ensures_1]: List..head(xs) > 0;
  ensures [test_ensures_2]: List..head(List..tail(xs)) > 0;
  } {
  ⏎
};
-/
#guard_msgs in
#eval (Std.format (transformProgram dependentRequiresPgm))

/-! ### Test 5: Function decl statement with precondition referencing local variable -/

def funcDeclPrecondPgm :=
#strata
program Core;

procedure test()
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
info: program Core;

procedure test ()
{
  var x : int := 1;
  safeDiv$$wf: {
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

procedure test(cond : bool, x : int, y : int)
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
info: program Core;

procedure test (cond : bool, x : int, y : int)
{
  if (cond) {
    f$$wf: {
      var a : int;
      assume [precond_f_0]: !(x == 0);
      assert [f_body_calls_Int.SafeDiv_0]: !(x == 0);
    }
    function f (a : int) : int { a / x }
    assert [init_calls_f_0]: !(x == 0);
    var r1 : int := f(10);
  } else {
    f$$wf: {
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

procedure proc1(x : int)
{
  function f(a : int) : int
    requires x != 0;
    { a / x }
  var r : int := f(10);
};

procedure proc2(y : int)
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
info: program Core;

procedure proc1 (x : int)
{
  f$$wf: {
    var a : int;
    assume [precond_f_0]: !(x == 0);
    assert [f_body_calls_Int.SafeDiv_0]: !(x == 0);
  }
  function f (a : int) : int { a / x }
  assert [init_calls_f_0]: !(x == 0);
  var r : int := f(10);
};
procedure proc2 (y : int)
{
  f$$wf: {
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

/-! ### Test 8: Division in if-then-else condition generates precondition -/

def iteCondPrecondPgm :=
#strata
program Core;

procedure test(x : int, y : int)
{
  if (x / y > 0) {
    var z : int := 1;
  } else {
    var z : int := 2;
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

procedure test (x : int, y : int)
{
  assert [ite_cond_calls_Int.SafeDiv_0]: !(y == 0);
  if (x / y > 0) {
    var z : int := 1;
  } else {
    var z : int := 2;
  }
};
-/
#guard_msgs in
#eval (Std.format (transformProgram iteCondPrecondPgm))

/-! ### Test 9: Division in loop guard generates precondition -/

def loopGuardPrecondPgm :=
#strata
program Core;
procedure test(inout g : int, y : int)
{
  while (y / (y / g) > 0) { g := g - 1; }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

procedure test (inout g : int, y : int)
{
  assert [loop_guard_calls_Int.SafeDiv_0]: !(g == 0);
  assert [loop_guard_calls_Int.SafeDiv_1]: !(y / g == 0);
  while (y / (y / g) > 0)
  {
    g := g - 1;
    assert [loop_guard_end_calls_Int.SafeDiv_0]: !(g == 0);
    assert [loop_guard_end_calls_Int.SafeDiv_1]: !(y / g == 0);
  }
};
-/
#guard_msgs in
#eval (Std.format (transformProgram loopGuardPrecondPgm))

/-! ### Test 10: Sequence.select without a bounds guard produces an out-of-bounds obligation

PrecondElim is intentionally unconditional: it inserts the bounds assert
regardless of any surrounding `requires` guard, and lets the SMT solver
discharge it. Same pattern as `Int.SafeDiv`. -/

def seqSelectNoGuardPgm :=
#strata
program Core;

procedure test(s : Sequence int, i : int)
{
  var x : int := Sequence.select(s, i);
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

procedure test (s : Sequence int, i : int)
{
  assert [init_calls_Sequence.select_0]: 0 <= i && i < Sequence.length(s);
  var x : int := Sequence.select(s, i);
};
-/
#guard_msgs in
#eval (Std.format (transformProgram seqSelectNoGuardPgm))

/-! ### Test 10c: Sequence.select inside a requires clause generates a $$wf procedure

Exercises the pure-position path (`mkContractWFProc`), distinct from the
imperative-body path of tests 10/10b. -/

def seqSelectInRequiresPgm :=
#strata
program Core;

procedure test(s : Sequence int, i : int)
spec {
  requires Sequence.select(s, i) > 0;
}
{
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

procedure test$$wf (s : Sequence int, i : int)
{
  assert [test_pre_test_requires_0_calls_Sequence.select_0]: 0 <= i && i < Sequence.length(s);
  assume [test_requires_0]: Sequence.select(s, i) > 0;
};
procedure test (s : Sequence int, i : int)
spec {
  requires [test_requires_0]: Sequence.select(s, i) > 0;
  } {
  ⏎
};
-/
#guard_msgs in
#eval (Std.format (transformProgram seqSelectInRequiresPgm))

/-! ### Test 10d: Sequence.select inside a function body generates a $$wf procedure

Exercises the function-body path (`mkFuncWFStmts`), distinct from the
procedure-body path in tests 10/10b and the contract path in test 10c. -/

def seqSelectInFuncBodyPgm :=
#strata
program Core;

function get_first(s : Sequence int) : int { Sequence.select(s, 0) }

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

procedure get_first$$wf (s : Sequence int)
{
  assert [get_first_body_calls_Sequence.select_0]: 0 <= 0 && 0 < Sequence.length(s);
};
function get_first (s : Sequence int) : int {
  Sequence.select(s, 0)
}
-/
#guard_msgs in
#eval (Std.format (transformProgram seqSelectInFuncBodyPgm))

/-! ### Test 11: `collectPrecondAsserts` tags Sequence bounds obligations with `outOfBoundsAccess`

Exercises the full `collectPrecondAsserts` path — the code called by
`transformStmt` / `mkContractWFProc` / `mkFuncWFProc` — and inspects the
metadata on the generated assert. Mirrors `OverflowCheckTest.lean`. -/

open Strata Core Lambda Core.PrecondElim Imperative in
#eval do
  let selExpr := LExpr.mkApp () Core.seqSelectOp [
    .fvar () ⟨"s", ()⟩ (some (Core.seqTy .int)),
    .fvar () ⟨"i", ()⟩ (some .int)]
  let stmts := collectPrecondAsserts Core.Factory selExpr "test" #[]
  assert! stmts.length == 1
  let md : MetaData Core.Expression := match stmts[0]! with
    | Statement.assert _ _ md => md | _ => #[]
  assert! md.getPropertyType == some MetaData.outOfBoundsAccess

open Strata Core Lambda Core.PrecondElim Imperative in
#eval do
  let updExpr := LExpr.mkApp () Core.seqUpdateOp [
    .fvar () ⟨"s", ()⟩ (some (Core.seqTy .int)),
    .fvar () ⟨"i", ()⟩ (some .int),
    .fvar () ⟨"v", ()⟩ (some .int)]
  let stmts := collectPrecondAsserts Core.Factory updExpr "test" #[]
  assert! stmts.length == 1
  let md : MetaData Core.Expression := match stmts[0]! with
    | Statement.assert _ _ md => md | _ => #[]
  assert! md.getPropertyType == some MetaData.outOfBoundsAccess

open Strata Core Lambda Core.PrecondElim Imperative in
#eval do
  let takeExpr := LExpr.mkApp () Core.seqTakeOp [
    .fvar () ⟨"s", ()⟩ (some (Core.seqTy .int)),
    .fvar () ⟨"n", ()⟩ (some .int)]
  let stmts := collectPrecondAsserts Core.Factory takeExpr "test" #[]
  assert! stmts.length == 1
  let md : MetaData Core.Expression := match stmts[0]! with
    | Statement.assert _ _ md => md | _ => #[]
  assert! md.getPropertyType == some MetaData.outOfBoundsAccess

open Strata Core Lambda Core.PrecondElim Imperative in
#eval do
  let dropExpr := LExpr.mkApp () Core.seqDropOp [
    .fvar () ⟨"s", ()⟩ (some (Core.seqTy .int)),
    .fvar () ⟨"n", ()⟩ (some .int)]
  let stmts := collectPrecondAsserts Core.Factory dropExpr "test" #[]
  assert! stmts.length == 1
  let md : MetaData Core.Expression := match stmts[0]! with
    | Statement.assert _ _ md => md | _ => #[]
  assert! md.getPropertyType == some MetaData.outOfBoundsAccess

-- `Sequence.length` is total: no precondition obligations generated.
open Strata Core Lambda Core.PrecondElim Imperative in
#eval do
  let lenExpr := LExpr.mkApp () Core.seqLengthOp [
    .fvar () ⟨"s", ()⟩ (some (Core.seqTy .int))]
  let stmts := collectPrecondAsserts Core.Factory lenExpr "test" #[]
  assert! stmts.isEmpty

-- Nested: `Sequence.select(Sequence.update(s, i, v), j)` emits two
-- obligations (one per partial call), both tagged `outOfBoundsAccess`.
open Strata Core Lambda Core.PrecondElim Imperative in
#eval do
  let updExpr := LExpr.mkApp () Core.seqUpdateOp [
    .fvar () ⟨"s", ()⟩ (some (Core.seqTy .int)),
    .fvar () ⟨"i", ()⟩ (some .int),
    .fvar () ⟨"v", ()⟩ (some .int)]
  let selExpr := LExpr.mkApp () Core.seqSelectOp [updExpr,
    .fvar () ⟨"j", ()⟩ (some .int)]
  let stmts := collectPrecondAsserts Core.Factory selExpr "test" #[]
  assert! stmts.length == 2
  -- Both obligations classified as outOfBoundsAccess.
  let md0 : MetaData Core.Expression := match stmts[0]! with
    | Statement.assert _ _ md => md | _ => #[]
  assert! md0.getPropertyType == some MetaData.outOfBoundsAccess
  let md1 : MetaData Core.Expression := match stmts[1]! with
    | Statement.assert _ _ md => md | _ => #[]
  assert! md1.getPropertyType == some MetaData.outOfBoundsAccess

/-! ### Test 12: `Sequence.empty` printer regression

The `handleZeroaryOps` fallback used to emit `re.none()` for any 0-ary op
outside the regex set (e.g. `Sequence.empty`). It should now emit a
generic call via `mkGenericCall`, preserving the op name. -/

/--
info: "assert [empty_len]: Sequence.length(Sequence.empty) == 0;\n\n-- Errors encountered during conversion:\nUnsupported construct in handleZeroaryOps: unknown operation, rendering as generic call: Sequence.empty\nContext: Global scope:"
-/
#guard_msgs in
#eval do
  let seqEmpty : Core.Expression.Expr := Lambda.LExpr.op () ⟨"Sequence.empty", ()⟩ none
  let seqLen   : Core.Expression.Expr := Lambda.LExpr.op () ⟨"Sequence.length", ()⟩ none
  let zero     : Core.Expression.Expr := Lambda.LExpr.const () (.intConst 0)
  let body     := Lambda.LExpr.eq () (Lambda.LExpr.app () seqLen seqEmpty) zero
  let stmt     := Core.Statement.assert "empty_len" body #[]
  IO.println (repr (Core.formatStatement stmt).pretty)

end PrecondElimTests
