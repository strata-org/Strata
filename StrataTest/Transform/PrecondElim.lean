/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.ProgramType
meta import Strata.Transform.PrecondElim
meta import Strata.Transform.GenOpaqueTypeParams
meta import StrataTest.Languages.Core.Tests.TestUtil

meta section

open Core
open Core.PrecondElim
open Strata

/-! ## PrecondElim Tests

These test the result of the `PrecondElim` transformation.
For the full verification pipeline with function preconditions,
see `StrataTest/Languages/Core/Examples/FunctionPreconditions.lean`.
-/

section PrecondElimTests

def translate (t : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

private def translationErrors (t : StrataDDM.Program) : Array String :=
  (TransM.run Inhabited.default (translateProgram t)).snd

/-- The empty transform state with the Core factory. -/
private def coreFactoryState : Core.Transform.CoreTransformState :=
  { Core.Transform.CoreTransformState.emp with factory := Core.Factory }

def transformProgram (t : StrataDDM.Program) : Core.Program :=
  let program := translate t
  match Core.Transform.run program PrecondElim.precondElim coreFactoryState with
  | .error e => panic! s!"PrecondElim failed: {e}"
  | .ok (_, program) =>
    match Core.typeCheck Core.VerifyOptions.default program with
    | .error e => panic! s!"Type check failed: {Std.format e}"
    | .ok program => program.stripMetaData

/-- Run `precondElim` and report whether the output `CoreTransformState.factory`
    still matches the input factory.

    Note: `LFunc` carries a function-valued `concreteEval` field, which has no
    `BEq`/`DecidableEq`, so the whole `LFunc` cannot be compared structurally.
    We compare the base `Func` projection (`.toFunc`) instead — that is every
    field of `LFunc` except `concreteEval` — via decidable equality. -/
def factoryRestored (t : StrataDDM.Program) : Bool :=
  let program := translate t
  let (_, finalState) :=
    Core.Transform.runWith program PrecondElim.precondElim coreFactoryState
  decide (finalState.factory.toArray.map (·.toFunc) =
    coreFactoryState.factory.toArray.map (·.toFunc))

/-! ### Test 1: Procedure body with div call gets assert for y != 0 -/

def divInBodyPgm :=
#strata
program Core;

procedure test(a : int)
{
  var z : int := int.safeDiv(10, a);
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

procedure test (a : int)
{
  assert [init_calls_Int.SafeDiv_0]: !(a == 0);
  var z : int := int.safeDiv(10, a);
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
{ int.safeMod(x, y) }

function foo(x : int, y : int) : int
  requires int.gt(safeMod(x, y), 0);
{ int.add(x, y) }

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

lemma [safeMod_body_calls_Int.SafeMod_0] (x : int, y : int): !(y == 0) ==> !(y == 0);
function safeMod (x : int, y : int) : int {
  int.safeMod(x, y)
}
lemma [foo_precond_calls_safeMod_0] (x : int, y : int): !(y == 0);
function foo (x : int, y : int) : int {
  int.add(x, y)
}
-/
#guard_msgs in
#eval (Std.format (transformProgram funcWithPrecondPgm))

/- Regression test for the factory save/restore invariant: `precondElim`
   accumulates `safeMod`/`foo` into the factory while collecting WF obligations,
   but the output state's factory must be identical to the input (built-in)
   factory. If a future edit drops the `setFactory savedF` restore in
   `PrecondElim.precondElim`, this `#guard` fails at elaboration time. -/
#guard factoryRestored funcWithPrecondPgm

/-! ### Test 3: Procedure with ADT destructor (has implicit precondition) in requires -/

def procContractADTPgm :=
#strata
program Core;

datatype List { Nil(), Cons(head : int, tail : List) };

procedure test(xs : List)
spec {
  requires List..isCons(xs);
  requires int.gt(List..head(xs), 0);
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
lemma [test_pre_test_requires_1_calls_List..head_0] (xs : List): List..isCons(xs) ==> List..isCons(xs);
procedure test (xs : List)
spec {
  requires [test_requires_0]: List..isCons(xs);
  requires [test_requires_1]: int.gt(List..head(xs), 0);
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

procedure test(xs : List)
spec {
  requires List..isCons(xs);
  ensures int.gt(List..head(xs), 0);
  ensures int.gt(List..head(List..tail(xs)), 0);
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
lemma [test_post_test_ensures_1_calls_List..head_0] (xs : List): List..isCons(xs) ==> List..isCons(xs);
lemma [test_post_test_ensures_2_calls_List..tail_0] (xs : List): List..isCons(xs) ==> int.gt(List..head(xs), 0) ==> List..isCons(xs);
lemma [test_post_test_ensures_2_calls_List..head_1] (xs : List): List..isCons(xs) ==> int.gt(List..head(xs), 0) ==> List..isCons(List..tail(xs));
procedure test (xs : List)
spec {
  requires [test_requires_0]: List..isCons(xs);
  ensures [test_ensures_1]: int.gt(List..head(xs), 0);
  ensures [test_ensures_2]: int.gt(List..head(List..tail(xs)), 0);
  } {
  
};
-/
#guard_msgs in
#eval (Std.format (transformProgram dependentRequiresPgm))

/-! ### Tests 5–7: local function preconditions are rejected during translation

Lambda abstractions cannot represent function preconditions, so the Core DDM
translator rejects these declarations before `PrecondElim` runs. Keep coverage
for a declaration in a straight-line body, in conditional branches, and in
separate procedures. -/

def funcDeclPrecondPgm :=
#strata
program Core;

procedure test()
{
  var x : int := 1;
  function safeDiv(y : int) : int
    requires int.gt(int.safeDiv(y, x), 0);
    { int.safeDiv(y, x) }
  var z : int := safeDiv(5);
};

#end

#guard (translationErrors funcDeclPrecondPgm).any
  (· == "local function 'safeDiv': preconditions are not supported")

def inlineFuncInIteSimplePgm :=
#strata
program Core;

procedure test(cond : bool, x : int, y : int)
{
  if (cond) {
    function f(a : int) : int
      requires x != 0;
      { int.safeDiv(a, x) }
    var r1 : int := f(10);
  } else {
    function f(a : int) : int
      requires y != 0;
      { int.safeDiv(a, y) }
    var r2 : int := f(20);
  }
};

#end

#guard (translationErrors inlineFuncInIteSimplePgm).any
  (· == "local function 'f': preconditions are not supported")

def funcInMultipleProcsPgm :=
#strata
program Core;

procedure proc1(x : int)
{
  function f(a : int) : int
    requires x != 0;
    { int.safeDiv(a, x) }
  var r : int := f(10);
};

procedure proc2(y : int)
{
  function f(a : int) : int
    requires y != 0;
    { int.safeDiv(a, y) }
  var r : int := f(20);
};

#end

#guard (translationErrors funcInMultipleProcsPgm).any
  (· == "local function 'f': preconditions are not supported")

/-! ### Test 8: Division in if-then-else condition generates precondition -/

def iteCondPrecondPgm :=
#strata
program Core;

procedure test(x : int, y : int)
{
  if (int.gt(int.safeDiv(x, y), 0)) {
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
  if (int.gt(int.safeDiv(x, y), 0)) {
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
  while (int.gt(int.safeDiv(y, int.safeDiv(y, g)), 0)) { g := int.sub(g, 1); }
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

procedure test (inout g : int, y : int)
{
  assert [loop_guard_calls_Int.SafeDiv_0]: !(g == 0);
  assert [loop_guard_calls_Int.SafeDiv_1]: !(int.safeDiv(y, g) == 0);
  while (int.gt(int.safeDiv(y, int.safeDiv(y, g)), 0))
  {
    g := int.sub(g, 1);
    assert [loop_guard_end_calls_Int.SafeDiv_0]: !(g == 0);
    assert [loop_guard_end_calls_Int.SafeDiv_1]: !(int.safeDiv(y, g) == 0);
  }
};
-/
#guard_msgs in
#eval (Std.format (transformProgram loopGuardPrecondPgm))

/-! ### Test 10: `collectPrecondAsserts` tags Sequence bounds obligations with `outOfBoundsAccess`

Exercises the full `collectPrecondAsserts` path — the code called by
`transformStmt` / `mkContractWFLemma` / `mkFuncWFLemma` — and inspects the
metadata on the generated assert. Mirrors `OverflowCheckTest.lean`. -/

section SeqBoundsObligations

open Strata Core Lambda Core.PrecondElim Imperative

/-- Shared fvar fixtures so each per-op case below is a one-liner. -/
private def fxS : Core.Expression.Expr := .fvar Core.coreLoc ⟨"s", ()⟩ (some (Core.seqTy .int))
private def fxI : Core.Expression.Expr := .fvar Core.coreLoc ⟨"i", ()⟩ (some .int)
private def fxV : Core.Expression.Expr := .fvar Core.coreLoc ⟨"v", ()⟩ (some .int)
private def fxN : Core.Expression.Expr := .fvar Core.coreLoc ⟨"n", ()⟩ (some .int)
private def fxJ : Core.Expression.Expr := .fvar Core.coreLoc ⟨"j", ()⟩ (some .int)

/-- Check that `collectPrecondAsserts` produces exactly `expectedCount`
    obligations from `expr`, each tagged with `outOfBoundsAccess`. -/
private def assertOutOfBoundsObligations
    (expr : Core.Expression.Expr) (expectedCount : Nat) : IO Unit := do
  let stmts := collectPrecondAsserts Core.Factory expr "test" #[]
  assert! stmts.length == expectedCount
  for s in stmts do
    let md : MetaData Core.Expression := match s with
      | Statement.assert _ _ md => md | _ => #[]
    assert! md.getPropertyType == some MetaData.outOfBoundsAccess

-- Sequence.select / update / take / drop each emit one out-of-bounds obligation.
#eval assertOutOfBoundsObligations (LExpr.mkApp Core.coreLoc Core.seqSelectOp [fxS, fxI]) 1
#eval assertOutOfBoundsObligations (LExpr.mkApp Core.coreLoc Core.seqUpdateOp [fxS, fxI, fxV]) 1
#eval assertOutOfBoundsObligations (LExpr.mkApp Core.coreLoc Core.seqTakeOp   [fxS, fxN]) 1
#eval assertOutOfBoundsObligations (LExpr.mkApp Core.coreLoc Core.seqDropOp   [fxS, fxN]) 1

-- Nested: `Sequence.select(Sequence.update(s, i, v), j)` emits two
-- obligations (one per partial call), both tagged `outOfBoundsAccess`.
#eval assertOutOfBoundsObligations
  (LExpr.mkApp Core.coreLoc Core.seqSelectOp [LExpr.mkApp Core.coreLoc Core.seqUpdateOp [fxS, fxI, fxV], fxJ]) 2

-- Sequence.length is total: no precondition obligations generated.
#eval do
  let stmts := collectPrecondAsserts Core.Factory
    (LExpr.mkApp Core.coreLoc Core.seqLengthOp [fxS]) "test" #[]
  assert! stmts.isEmpty

/-! #### Test 10a: Pretty-printed obligation shape per partial op

Catches regressions that preserve count and metadata tag but corrupt the
obligation body (e.g. swapping `.Lt` for `.Le` at a call site, changing
the bound variable name, or swapping the lower/upper bound inside
`mkSeqBoundsPrecond`). -/

private def printFirstObligation (expr : Core.Expression.Expr) : IO Unit := do
  let stmts := collectPrecondAsserts Core.Factory expr "test" #[]
  match stmts.head? with
  | some (Statement.assert _ e _) => IO.println s!"{Std.format e}"
  | _ => IO.println "<unexpected>"

/-- info: int.le(0, i) && int.lt(i, Sequence.length(s)) -/
#guard_msgs in
#eval printFirstObligation (LExpr.mkApp Core.coreLoc Core.seqSelectOp [fxS, fxI])

/-- info: int.le(0, i) && int.lt(i, Sequence.length(s)) -/
#guard_msgs in
#eval printFirstObligation (LExpr.mkApp Core.coreLoc Core.seqUpdateOp [fxS, fxI, fxV])

/-- info: int.le(0, n) && int.le(n, Sequence.length(s)) -/
#guard_msgs in
#eval printFirstObligation (LExpr.mkApp Core.coreLoc Core.seqTakeOp [fxS, fxN])

/-- info: int.le(0, n) && int.le(n, Sequence.length(s)) -/
#guard_msgs in
#eval printFirstObligation (LExpr.mkApp Core.coreLoc Core.seqDropOp [fxS, fxN])

end SeqBoundsObligations

/-! ### Test: nested quantifiers with a partial-function call (regression)

A hypothesis captured outside a nested quantifier (`p == Outer_A(m)`) must have
its de Bruijn indices shifted when the accessor-call obligation for the inner
quantifier is generated. Otherwise `m` silently rebinds to the inner bound
variable `j` and the generated obligation fails to type-check with
"Impossible to unify (arrow Inner Outer) with (arrow int ...)".

`Inner` carries a second constructor so that `Inner..x` is a partial accessor
whose tester precondition reaches the generated `$$wf` lemma. -/

def nestedExistsWFPgm :=
#strata
program Core;
datatype Inner { Inner_Cons(x : int), Inner_Nil() };
datatype Outer { Outer_A(v : Inner) };

function bug(p: Outer): bool {
  exists m: Inner ::
    p == Outer_A(m)
    && (exists j: int :: Inner..x(m) == j)
}
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

datatype Inner {
  Inner_Cons(x : int),
  Inner_Nil()
};
datatype Outer {
  Outer_A(v : Inner)
};
lemma [bug_body_calls_Inner..x_0] (p : Outer, m : Inner, j : int): p == Outer_A(m) ==> Inner..isInner_Cons(m);
function bug (p : Outer) : bool {
  exists m : Inner :: p == Outer_A(m) && (exists j : int :: Inner..x(m) == j)
}
-/
#guard_msgs in
#eval (Std.format (transformProgram nestedExistsWFPgm))

/-! ### Test: a single-constructor datatype's accessor carries no obligation

`Inner..x` above is guarded by `Inner..isInner_Cons` because `Inner` has a
second constructor for that tester to rule out. Where the datatype has a single
constructor the tester holds for every value of the type, so the accessor is
total and the function needs no `$$wf` lemma at all. -/

def nestedExistsSingleConstrPgm :=
#strata
program Core;
datatype Inner { Inner_Cons(x : int) };
datatype Outer { Outer_A(v : Inner) };

function bug(p: Outer): bool {
  exists m: Inner ::
    p == Outer_A(m)
    && (exists j: int :: Inner..x(m) == j)
}
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

datatype Inner {
  Inner_Cons(x : int)
};
datatype Outer {
  Outer_A(v : Inner)
};
function bug (p : Outer) : bool {
  exists m : Inner :: p == Outer_A(m) && (exists j : int :: Inner..x(m) == j)
}
-/
#guard_msgs in
#eval (Std.format (transformProgram nestedExistsSingleConstrPgm))

/-! ### Test: `changed` flag for a nullary internal function whose body calls a
    precondition-carrying function

A nullary internal function has no abstraction binders, so it translates
straight to an initialized value. Its partial-call obligation is asserted at
the initialization site, and the pass reports `changed := true`. -/

/-- Run `PrecondElim` and return only its `changed` flag (`none` if the pass
    errors). -/
private def transformChanged (t : StrataDDM.Program) : Option Bool :=
  let program := translate t
  match Core.Transform.run program PrecondElim.precondElim coreFactoryState with
  | .error _ => none
  | .ok (changed, _) => some changed

private def nestedFuncCallsPartialPgm :=
#strata
program Core;

procedure P0()
{
  function bB() : int { int.safeModT(0, 2) }
};

#end

/-- info: some true -/
#guard_msgs in
#eval transformChanged nestedFuncCallsPartialPgm

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

procedure P0 ()
{
  assert [init_calls_Int.SafeModT_0]: !(2 == 0);
  var bB : int := int.safeModT(0, 2);
};
-/
#guard_msgs in
#eval (Std.format (transformProgram nestedFuncCallsPartialPgm))

/-! ### Test: polymorphic calls inside a polymorphic procedure

A procedure with type variable `tv` calls `g<a, b>` and `Sequence.select` at
instances that mention `tv`. -/

section PolyCallerTypeVars

open Lambda

/-- `g<a, b>(x : a, y : b) : bool`, uninterpreted, requires `y == y`. -/
private def gFunc : Core.Function :=
  { name := ⟨"g", ()⟩
    typeArgs := ["a", "b"]
    inputs := [(⟨"x", ()⟩, .ftvar "a"), (⟨"y", ()⟩, .ftvar "b")]
    output := .bool
    preconditions :=
      [⟨.eq Core.coreLoc (.fvar Core.coreLoc ⟨"y", ()⟩ none) (.fvar Core.coreLoc ⟨"y", ()⟩ none),
        Core.coreLoc⟩] }

/-- `assert g(true, x)` with `x : tv`. -/
private def callG (tv : String) : Core.Statement :=
  Core.Statement.assert "callG"
    (LExpr.mkApp Core.coreLoc (.op Core.coreLoc ⟨"g", ()⟩ none)
      [.boolConst Core.coreLoc true, .fvar Core.coreLoc ⟨"x", ()⟩ (some (.ftvar tv))]) .empty

/-- `var t : Sequence tv := Sequence.select(s, 0)` with
    `s : Sequence (Sequence tv)`. -/
private def selectHead (tv : String) : Core.Statement :=
  Core.Statement.init ⟨"t", ()⟩ (.forAll [] (Core.seqTy (.ftvar tv)))
    (.det (LExpr.mkApp Core.coreLoc (.op Core.coreLoc ⟨"Sequence.select", ()⟩ none)
      [.fvar Core.coreLoc ⟨"s", ()⟩ (some (Core.seqTy (Core.seqTy (.ftvar tv)))),
       .intConst Core.coreLoc 0])) .empty

/-- `g` and `procedure P<tv>(s : Sequence (Sequence tv), x : tv)` with body
    `body`. -/
private def polyCallerPgm (tv : String) (body : List Core.Statement) :
    Core.Program :=
  { decls := [
    .func gFunc .empty,
    .proc { header := { name := ⟨"P", ()⟩
                        typeArgs := [tv]
                        inputs :=
                          [(⟨"s", ()⟩, Core.seqTy (Core.seqTy (.ftvar tv))),
                           (⟨"x", ()⟩, .ftvar tv)]
                        outputs := [] }
            spec := { preconditions := [], postconditions := [] }
            body := .structured body false }
      .empty] }

/-- Run `precondElim` and `genOpaqueTypeParams`, then type check; show the
    program or the error. -/
private def precondElimThenCheck (p : Core.Program) : Std.Format :=
  let passes := fun p => do
    let (_, p) ← PrecondElim.precondElim p
    Core.genOpaqueTypeParams p
  match Core.Transform.run p passes coreFactoryState with
  | .error e => f!"transform failed: {e}"
  | .ok (_, p) =>
    match Core.typeCheck Core.VerifyOptions.default p with
    | .error e => f!"type error: {Std.format e}"
    | .ok p => Std.format p.stripMetaData

-- `g(true, x)` in `P<a>`: `g`'s `a` is `bool` and its `b` is `P`'s `a`.
/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

function g<a, b> (x : a, y : b) : bool;
type $__opaque_P_a_0;
procedure P (s : Sequence (Sequence $__opaque_P_a_0), x : $__opaque_P_a_0)
{
  assert [assert_callG_calls_g_0]: x == x;
  assert [callG]: g(true, x);
};
-/
#guard_msgs in
#eval precondElimThenCheck (polyCallerPgm "a" [callG "a"])

-- `Sequence.select(s, 0)` in `P<a>`: `Sequence.select`'s `a` is `Sequence a`.
/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

function g<a, b> (x : a, y : b) : bool;
type $__opaque_P_a_0;
procedure P (s : Sequence (Sequence $__opaque_P_a_0), x : $__opaque_P_a_0)
{
  assert [init_calls_Sequence.select_0]: int.le(0, 0) && int.lt(0, Sequence.length(s));
  var t : Sequence $__opaque_P_a_0 := Sequence.select(s, 0);
};
-/
#guard_msgs in
#eval precondElimThenCheck (polyCallerPgm "a" [selectHead "a"])

-- Both calls in `P<c>`, whose type variable is named unlike any of the
-- callees'.
/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

function g<a, b> (x : a, y : b) : bool;
type $__opaque_P_c_0;
procedure P (s : Sequence (Sequence $__opaque_P_c_0), x : $__opaque_P_c_0)
{
  assert [assert_callG_calls_g_0]: x == x;
  assert [callG]: g(true, x);
  assert [init_calls_Sequence.select_0]: int.le(0, 0) && int.lt(0, Sequence.length(s));
  var t : Sequence $__opaque_P_c_0 := Sequence.select(s, 0);
};
-/
#guard_msgs in
#eval precondElimThenCheck (polyCallerPgm "c" [callG "c", selectHead "c"])

/-- `k<c>(z : c) : bool`, uninterpreted. -/
private def kFunc : Core.Function :=
  { name := ⟨"k", ()⟩
    typeArgs := ["c"]
    inputs := [(⟨"z", ()⟩, .ftvar "c")]
    output := .bool }

/-- `h<a, b>(x : a, y : b) : bool`, uninterpreted, requires `k(y)`. -/
private def hFunc : Core.Function :=
  { name := ⟨"h", ()⟩
    typeArgs := ["a", "b"]
    inputs := [(⟨"x", ()⟩, .ftvar "a"), (⟨"y", ()⟩, .ftvar "b")]
    output := .bool
    preconditions :=
      [⟨.app Core.coreLoc (.op Core.coreLoc ⟨"k", ()⟩ (some (.arrow (LMonoTy.ftvar "b") .bool)))
          (.fvar Core.coreLoc ⟨"y", ()⟩ none), Core.coreLoc⟩] }

/-- `k`, `h` and `procedure P<tv>(x : tv)` with body
    `assert forall y : int :: h(x, y)`, where `y` carries no annotation. -/
private def forallHPgm (tv : String) : Core.Program :=
  let callH := LExpr.mkApp Core.coreLoc (.op Core.coreLoc ⟨"h", ()⟩ none)
    [.fvar Core.coreLoc ⟨"x", ()⟩ (some (LMonoTy.ftvar tv)), .bvar Core.coreLoc 0]
  { decls := [
    .func kFunc .empty,
    .func hFunc .empty,
    .proc { header := { name := ⟨"P", ()⟩
                        typeArgs := [tv]
                        inputs := [(⟨"x", ()⟩, .ftvar tv)]
                        outputs := [] }
            spec := { preconditions := [], postconditions := [] }
            body := .structured
              [Core.Statement.assert "forallH" (LExpr.all Core.coreLoc "y" (some .int) callH)
                .empty] false }
      .empty] }

-- `h(x, y)` in `P<b>` with `y : int` bound by the quantifier: `h`'s `b` is
-- instantiated at `int`, not at the caller's `b`, so the inlined precondition
-- is `forall y : int :: k(y)`.
/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

function k<c> (z : c) : bool;
function h<a, b> (x : a, y : b) : bool;
type $__opaque_P_b_0;
procedure P (x : $__opaque_P_b_0)
{
  assert [assert_forallH_calls_h_0]: forall y : int :: k(y);
  assert [forallH]: forall y : int :: h(x, y);
};
-/
#guard_msgs in
#eval precondElimThenCheck (forallHPgm "b")

-- The same program with the caller's type parameter named `$__precond_1`, which has a reserved
-- prefix: type checking, which runs before this pass, renames it, so no type variable the pass
-- generates captures it.
/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

function k<c> (z : c) : bool;
function h<a, b> (x : a, y : b) : bool;
type $__opaque_P_a_0;
procedure P (x : $__opaque_P_a_0)
{
  assert [assert_forallH_calls_h_0]: forall y : int :: k(y);
  assert [forallH]: forall y : int :: h(x, y);
};
-/
#guard_msgs in
#eval match Core.typeCheck .quiet (forallHPgm "$__precond_1") with
  | .ok p => precondElimThenCheck p
  | .error e => f!"type error: {Std.format e}"

/-- `f<a>(x : int) : a`, uninterpreted, requires `forall y : a :: k(y)`. -/
private def fResFunc : Core.Function :=
  { name := ⟨"f", ()⟩
    typeArgs := ["a"]
    inputs := [(⟨"x", ()⟩, .int)]
    output := .ftvar "a"
    preconditions :=
      [⟨LExpr.all Core.coreLoc "y" (some (.ftvar "a"))
          (.app Core.coreLoc (.op Core.coreLoc ⟨"k", ()⟩ none) (.bvar Core.coreLoc 0)),
              Core.coreLoc⟩] }

/-- `k`, `f` and `procedure P<tv>()` with body `var t : tv := f(0)`. -/
private def fResPgm (tv : String) : Core.Program :=
  { decls := [
    .func kFunc .empty,
    .func fResFunc .empty,
    .proc { header := { name := ⟨"P", ()⟩, typeArgs := [tv], inputs := [], outputs := [] }
            spec := { preconditions := [], postconditions := [] }
            body := .structured
              [Core.Statement.init ⟨"t", ()⟩ (.forAll [] (.ftvar tv))
                (.det (.app Core.coreLoc (.op Core.coreLoc ⟨"f", ()⟩ none)
                       (.intConst Core.coreLoc 0))) .empty] false }
      .empty] }

/-- Type check, then run `precondElim`; show the program or the error. -/
private def checkThenPrecondElim (p : Core.Program) : Std.Format :=
  match Core.typeCheck Core.VerifyOptions.default p with
  | .error e => f!"type error: {Std.format e}"
  | .ok p =>
    match Core.Transform.run p PrecondElim.precondElim coreFactoryState with
    | .error e => f!"transform failed: {e}"
    | .ok (_, p) => Std.format p.stripMetaData

-- `f(0)` in `P<a>`, annotated by the type check at `int → a`, `f`'s declared
-- type: `f`'s `a` is `P`'s `a`.
/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

function k<c> (z : c) : bool;
function f<a> (x : int) : a;
procedure P<a> ()
{
  assert [init_calls_f_0]: forall y : a :: k(y);
  var t : a := f(0);
};
-/
#guard_msgs in
#eval checkThenPrecondElim (fResPgm "a")

-- The same program with `P`'s type parameter named `c`: the same output with
-- `a` renamed to `c`.
/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

function k<c> (z : c) : bool;
function f<a> (x : int) : a;
procedure P<c> ()
{
  assert [init_calls_f_0]: forall y : c :: k(y);
  var t : c := f(0);
};
-/
#guard_msgs in
#eval checkThenPrecondElim (fResPgm "c")

end PolyCallerTypeVars

/-! ### Nested calls to a recursive block

Both calls use the same variable `nest_fn` for `nest`, so the well-formedness
lemma states the division's precondition for the nested call as written. -/

def nestedRecCallPgm :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function nest (@[cases] xs : IntList, acc : int) : int
{
  if IntList..isNil(xs) then acc
  else int.safeDiv(1, nest(IntList..tl(xs), nest(IntList..tl(xs), acc)))
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

datatype IntList {
  Nil(),
  Cons(hd : int, tl : IntList)
};
lemma [nest_body_calls_IntList..tl_0] (xs : IntList, acc : int): !(IntList..isNil(xs)) ==> IntList..isCons(xs);
lemma [nest_body_calls_IntList..tl_1] (xs : IntList, acc : int): !(IntList..isNil(xs)) ==> IntList..isCons(xs);
lemma [nest_body_calls_Int.SafeDiv_2] (xs : IntList, acc : int, nest_fn : (IntList -> int -> int)): !(IntList..isNil(xs)) ==> !(nest_fn(IntList..tl(xs), nest_fn(IntList..tl(xs), acc)) == 0);
rec function nest (@[cases] xs : IntList, acc : int) : int
{
  if IntList..isNil(xs) then acc else int.safeDiv(1, nest(IntList..tl(xs), nest(IntList..tl(xs), acc)))
};
-/
#guard_msgs in
#eval (Std.format (transformProgram nestedRecCallPgm))

/-! ### Identical polymorphic calls at different instantiations

The two calls `g(Nil())` stand at `MyList int` and `MyList bool`. The program is
type checked first, so each call is annotated at its instantiation, and each
gets its own variable for `g` of that type. `g`'s own lemma keeps `g`'s type
parameter `b`. -/

def polymorphicCallsAtTwoTypesPgm :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };

rec function f (@[cases] xs : MyList int) : int
{
  if MyList..isNil(xs) then 0
  else if g(Nil()) == Cons(1, Nil()) then (if g(Nil()) == Cons(true, Nil()) then f(MyList..tl(xs)) else 1)
  else 2
}
function g<b> (@[cases] ys : MyList b) : MyList b
{
  if MyList..isNil(ys) then ys else if int.lt(f(Nil()), 0) then ys else g(MyList..tl(ys))
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

datatype MyList (a : Type) {
  Nil(),
  Cons(hd : a, tl : MyList a)
};
lemma [f_body_calls_MyList..tl_0] (xs : (MyList int), g_fn : (MyList bool -> MyList bool), g_fn_1 : (MyList int -> MyList int)): g_fn(Nil) == Cons(true, Nil) ==> g_fn_1(Nil) == Cons(1, Nil) ==> !(MyList..isNil(xs)) ==> MyList..isCons(xs);
lemma [g_body_calls_MyList..tl_0] <b>(ys : (MyList b), f_fn : (MyList int -> int)): !(int.lt(f_fn(Nil), 0)) ==> !(MyList..isNil(ys)) ==> MyList..isCons(ys);
rec function f (@[cases] xs : MyList int) : int
{
  if MyList..isNil(xs) then 0 else if g(Nil) == Cons(1, Nil) then if g(Nil) == Cons(true, Nil) then f(MyList..tl(xs)) else 1 else 2
}
function g<b> (@[cases] ys : MyList b) : MyList b
{
  if MyList..isNil(ys) then ys else if int.lt(f(Nil), 0) then ys else g(MyList..tl(ys))
};
-/
#guard_msgs in
#eval checkThenPrecondElim (translate polymorphicCallsAtTwoTypesPgm)

/-! ### Partial functions in a CFG body

A call in a block command gets its precondition check right before the command; a call in a
branch condition gets its check after the block's last command. The contract's
well-formedness lemma is generated as for a structured body. -/

private def divInCFGPgm :=
#strata
program Core;

procedure test(a : int, b : int, out r : int)
spec { requires [b_ok]: int.gt(int.safeDiv(10, b), 0); }
cfg entry {
  entry: { r := int.safeDiv(10, a);
    branch (int.gt(int.safeDiv(r, b), 0)) goto pos else goto done; }
  pos: { r := int.add(r, 1); goto done; }
  done: { return; }
};

#end

/--
info: [Strata.Core] Type checking succeeded.

program Core;

lemma [test_pre_b_ok_calls_Int.SafeDiv_0] (a : int, b : int, r : int): !(b == 0);
procedure test (a : int, b : int, out r : int)
spec {
  requires [b_ok]: int.gt(int.safeDiv(10, b), 0);
  } cfg entry {
  entry: {
    assert [set_r_calls_Int.SafeDiv_0]: !(a == 0);
    r := int.safeDiv(10, a);
    assert [branch_cond_calls_Int.SafeDiv_0]: !(b == 0);
    branch (int.gt(int.safeDiv(r, b), 0)) goto pos else goto done;
  }
  pos: {
    r := int.add(r, 1);
    goto done;
  }
  done: {
    return;
  }
};
-/
#guard_msgs (whitespace := lax) in
#eval IO.println ((Std.format (transformProgram divInCFGPgm)).pretty 96)

/-! ### Test: a call keeps the type arguments it stores

The argument `int.safeDiv(10, a)` makes the transform emit an assertion in front of the call; the
call itself, in a structured body and in a control-flow graph block, keeps its stored type
argument `int`. -/

section StoredTyArgs

open Lambda Lambda.LExpr.SyntaxMono Core.Syntax
open Core.TestUtil (cfgProc identityDecl mkProc programText tyArgsOfResult)

/-- The argument `int.safeDiv(10, a)`, whose precondition `a != 0` the transform asserts. -/
private def safeDivArg : Expression.Expr := eb[((~Int.SafeDiv #10) a)]

/-- A structured `Caller` that calls `Identity` with the stored type argument `int`. -/
private def storedTyArgsStructured : Core.Program := { decls :=
  [identityDecl,
   mkProc "Caller" [] [("a", .int)] [("m", .int)]
     [Statement.call "Identity" (some [.forAll [] .int]) [.inArg safeDivArg, .outArg "m"]
        .empty]] }

/-- A `Caller` with a control-flow graph body that calls `Identity` with the stored type
    argument `int`. -/
private def storedTyArgsCfg : Core.Program := { decls :=
  [identityDecl,
   cfgProc "Caller" [("a", .int)] [("m", .int)]
     [("entry",
       { cmds := [.call "Identity" (some [.forAll [] .int])
                    [.inArg safeDivArg, .outArg "m"] .empty],
         transfer := .finish .empty })]] }

/-- The program that `precondElim` produces for `pgm`. -/
private def precondElimResult (pgm : Core.Program) :=
  (Core.Transform.run pgm PrecondElim.precondElim coreFactoryState).map (·.2)

/-- info: [some ["int"]] -/
#guard_msgs in
#eval tyArgsOfResult (precondElimResult storedTyArgsStructured)

/-- info: [some ["int"]] -/
#guard_msgs in
#eval tyArgsOfResult (precondElimResult storedTyArgsCfg)

/--
info: program Core;

procedure Identity<T> (x : T, out y : T)
{
  y := x;
};
procedure Caller (a : int, out m : int)
{
  assert [call_Identity_arg_calls_Int.SafeDiv_0]: !(a == 0);
  call Identity(int.safeDiv(10, a), out m);
};
-/
#guard_msgs in
#eval IO.println (programText (precondElimResult storedTyArgsStructured))

/--
info: program Core;

procedure Identity<T> (x : T, out y : T)
{
  y := x;
};
procedure Caller (a : int, out m : int)
cfg entry {
  entry: {
    assert [call_Identity_arg_calls_Int.SafeDiv_0]: !(a == 0);
    call Identity(int.safeDiv(10, a), out m);
    return;
  }
};
-/
#guard_msgs in
#eval IO.println (programText (precondElimResult storedTyArgsCfg))

end StoredTyArgs

/-! A generated lemma name avoids the program's assert labels: the lemma for the
body of `f` would be named `f_body_calls_Int.SafeDiv_0`, which a procedure's
assert already uses, so it gets a fresh name. -/

def assertLabelClashPgm :=
#strata
program Core;

function f(x : int) : int
  requires x != 0;
{ int.safeDiv(10, x) }

procedure P(y : int) {
  assert [f_body_calls_Int.SafeDiv_0]: y == 2;
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

lemma [f_body_calls_Int.SafeDiv_0_1] (x : int): !(x == 0) ==> !(x == 0);
function f (x : int) : int {
  int.safeDiv(10, x)
}
procedure P (y : int)
{
  assert [f_body_calls_Int.SafeDiv_0]: y == 2;
};
-/
#guard_msgs in
#eval (Std.format (transformProgram assertLabelClashPgm))

/-! The same holds for an assert at any depth of a procedure body: here inside
an `if` branch. -/

def nestedAssertLabelClashPgm :=
#strata
program Core;

function f(x : int) : int
  requires x != 0;
{ int.safeDiv(10, x) }

procedure P(y : int) {
  if (int.gt(y, 0)) {
    assert [f_body_calls_Int.SafeDiv_0]: y == 2;
  }
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

lemma [f_body_calls_Int.SafeDiv_0_1] (x : int): !(x == 0) ==> !(x == 0);
function f (x : int) : int {
  int.safeDiv(10, x)
}
procedure P (y : int)
{
  if (int.gt(y, 0)) {
    assert [f_body_calls_Int.SafeDiv_0]: y == 2;
  }
};
-/
#guard_msgs in
#eval (Std.format (transformProgram nestedAssertLabelClashPgm))

/-! And for a loop invariant's label. -/

def invariantLabelClashPgm :=
#strata
program Core;

function f(x : int) : int
  requires x != 0;
{ int.safeDiv(10, x) }

procedure P(n : int) {
  var i : int := 0;
  while (int.lt(i, n))
    invariant [f_body_calls_Int.SafeDiv_0]: int.ge(i, 0)
  {
    i := int.add(i, 1);
  }
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

lemma [f_body_calls_Int.SafeDiv_0_1] (x : int): !(x == 0) ==> !(x == 0);
function f (x : int) : int {
  int.safeDiv(10, x)
}
procedure P (n : int)
{
  var i : int := 0;
  while (int.lt(i, n))
  invariant [f_body_calls_Int.SafeDiv_0]: int.ge(i, 0)
  {
    i := int.add(i, 1);
  }
};
-/
#guard_msgs in
#eval (Std.format (transformProgram invariantLabelClashPgm))

/-! And for a postcondition's label, which the procedure check asserts. -/

def ensuresLabelClashPgm :=
#strata
program Core;

function f(x : int) : int
  requires x != 0;
{ int.safeDiv(10, x) }

procedure P(y : int)
spec { ensures [f_body_calls_Int.SafeDiv_0]: y == y; }
{
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

lemma [f_body_calls_Int.SafeDiv_0_1] (x : int): !(x == 0) ==> !(x == 0);
function f (x : int) : int {
  int.safeDiv(10, x)
}
procedure P (y : int)
spec {
  ensures [f_body_calls_Int.SafeDiv_0]: y == y;
  } {
  
};
-/
#guard_msgs in
#eval (Std.format (transformProgram ensuresLabelClashPgm))

/-! And for a precondition's label, which the procedure check assumes. -/

def requiresLabelClashPgm :=
#strata
program Core;

function f(x : int) : int
  requires x != 0;
{ int.safeDiv(10, x) }

procedure P(y : int)
spec { requires [f_body_calls_Int.SafeDiv_0]: y == y; }
{
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

lemma [f_body_calls_Int.SafeDiv_0_1] (x : int): !(x == 0) ==> !(x == 0);
function f (x : int) : int {
  int.safeDiv(10, x)
}
procedure P (y : int)
spec {
  requires [f_body_calls_Int.SafeDiv_0]: y == y;
  } {
  
};
-/
#guard_msgs in
#eval (Std.format (transformProgram requiresLabelClashPgm))

/-! And for a `cover` in a structured body. -/

def coverLabelClashPgm :=
#strata
program Core;

function f(x : int) : int
  requires x != 0;
{ int.safeDiv(10, x) }

procedure P(y : int) {
  if (int.gt(y, 0)) {
    cover [f_body_calls_Int.SafeDiv_0]: y == 2;
  }
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

lemma [f_body_calls_Int.SafeDiv_0_1] (x : int): !(x == 0) ==> !(x == 0);
function f (x : int) : int {
  int.safeDiv(10, x)
}
procedure P (y : int)
{
  if (int.gt(y, 0)) {
    cover [f_body_calls_Int.SafeDiv_0]: y == 2;
  }
};
-/
#guard_msgs in
#eval (Std.format (transformProgram coverLabelClashPgm))

/-! And for an `assume` in a structured body. -/

def assumeLabelClashPgm :=
#strata
program Core;

function f(x : int) : int
  requires x != 0;
{ int.safeDiv(10, x) }

procedure P(y : int) {
  assume [f_body_calls_Int.SafeDiv_0]: y == 2;
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

lemma [f_body_calls_Int.SafeDiv_0_1] (x : int): !(x == 0) ==> !(x == 0);
function f (x : int) : int {
  int.safeDiv(10, x)
}
procedure P (y : int)
{
  assume [f_body_calls_Int.SafeDiv_0]: y == 2;
};
-/
#guard_msgs in
#eval (Std.format (transformProgram assumeLabelClashPgm))

/-! The checks inserted in a procedure are named apart within that procedure
and from the program's declarations, not from the other procedures' checks, so
their labels do not depend on which other procedures the program has or on
their order: here both procedures get `init_calls_Int.SafeDiv_0`. -/

def twoProcsChecksPgm :=
#strata
program Core;

procedure A(a : int) {
  var z : int := int.safeDiv(1, a);
};
procedure B(b : int) {
  var w : int := int.safeDiv(1, b);
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

procedure A (a : int)
{
  assert [init_calls_Int.SafeDiv_0]: !(a == 0);
  var z : int := int.safeDiv(1, a);
};
procedure B (b : int)
{
  assert [init_calls_Int.SafeDiv_0]: !(b == 0);
  var w : int := int.safeDiv(1, b);
};
-/
#guard_msgs in
#eval (Std.format (transformProgram twoProcsChecksPgm))

/-! The pass renames only the checks it inserts in this run: a check of its
input keeps its label whatever metadata it carries, here an assert written with
the annotation `wellFormednessCheck`. -/

def taggedCheckPgm :=
#strata
program Core;

procedure P(y : int) {
  @[wellFormednessCheck] assert [mine]: y == 2;
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: program Core;

procedure P (y : int)
{
  assert [mine]: y == 2;
};
-/
#guard_msgs in
#eval (Std.format (transformProgram taggedCheckPgm))

/-! So running the pass on its own output renames none of the checks the first
run inserted: the first run's check keeps `init_calls_Int.SafeDiv_0`, and the
check the second run inserts again for the same call takes the suffix. -/

def secondRunPgm :=
#strata
program Core;

procedure P(a : int) {
  var z : int := int.safeDiv(1, a);
};

#end

private def precondElimTwice (t : StrataDDM.Program) : Core.Program :=
  match Core.Transform.run (translate t) PrecondElim.precondElim coreFactoryState with
  | .error e => panic! s!"PrecondElim failed: {e}"
  | .ok (_, once) =>
    match Core.Transform.run once PrecondElim.precondElim coreFactoryState with
    | .error e => panic! s!"PrecondElim failed: {e}"
    | .ok (_, twice) => twice.stripMetaData

/--
info: program Core;

procedure P (a : int)
{
  assert [init_calls_Int.SafeDiv_0]: !(a == 0);
  assert [init_calls_Int.SafeDiv_0_1]: !(a == 0);
  var z : int := int.safeDiv(1, a);
};
-/
#guard_msgs in
#eval (Std.format (precondElimTwice secondRunPgm))

/-! And for the `assert` and `cover` commands of a CFG body: the lemma for `f`'s
body would be named `f_body_calls_Int.SafeDiv_0` and the one for `g`'s body
`g_body_calls_Int.SafeDiv_0`, the labels of a block's cover and assert. -/

def cfgLabelClashPgm :=
#strata
program Core;

function f(x : int) : int
  requires x != 0;
{ int.safeDiv(10, x) }

function g(x : int) : int
  requires x != 0;
{ int.safeDiv(20, x) }

procedure P(y : int)
cfg entry {
  entry: { cover [f_body_calls_Int.SafeDiv_0]: y == 2;
    assert [g_body_calls_Int.SafeDiv_0]: y == y; return; }
};

#end

/--
info: [Strata.Core] Type checking succeeded.

program Core;

lemma [f_body_calls_Int.SafeDiv_0_1] (x : int): !(x == 0) ==> !(x == 0);
function f (x : int) : int {
  int.safeDiv(10, x)
}
lemma [g_body_calls_Int.SafeDiv_0_1] (x : int): !(x == 0) ==> !(x == 0);
function g (x : int) : int {
  int.safeDiv(20, x)
}
procedure P (y : int)
cfg entry {
  entry: {
    cover [f_body_calls_Int.SafeDiv_0]: y == 2;
    assert [g_body_calls_Int.SafeDiv_0]: y == y;
    return;
  }
};
-/
#guard_msgs (whitespace := lax) in
#eval IO.println ((Std.format (transformProgram cfgLabelClashPgm)).pretty 96)

/-! Verifying the nested case reports the lemma, which holds, and the assert,
which fails, each under its own name and with its own verdict. -/

/--
info:
Obligation: f_body_calls_Int.SafeDiv_0_1
Property: division by zero check
Result: ✅ pass

Obligation: f_body_calls_Int.SafeDiv_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Strata.Core.verify nestedAssertLabelClashPgm (options := .quiet)

end PrecondElimTests
end
