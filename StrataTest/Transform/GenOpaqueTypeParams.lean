/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.ProgramType
meta import Strata.Transform.GenOpaqueTypeParams
meta import StrataTest.Languages.Core.Tests.TestUtil

meta section

open Strata
open Core.TestUtil (translateWithMetaData)

/-! ## `GenOpaqueTypeParams` tests

`GenOpaqueTypeParams` makes every polymorphic procedure monomorphic by minting a
fresh opaque nullary type per declared type parameter (`header.typeArgs`) and
substituting it throughout the procedure's signature, spec, and body.

It runs in `corePipelinePhases` after `typeCheckPipelinePhase` and `CallElim`, so no procedure
body contains a `call`. The tests run the pass on a parsed program and check the output and that
it type-checks.
-/

section GenOpaqueTypeParamsTests

/-- Run the `GenOpaqueTypeParams` pass on a program (fresh generator state, so
    opaque-type counters start at 0). -/
private def runMono (p : Core.Program) : Core.Program :=
  match Core.Transform.run p Core.GenOpaqueTypeParams.run with
  | .ok p' => p'
  | .error _ => p

private def quietOpts : Core.VerifyOptions :=
  { Core.VerifyOptions.default with verbose := .quiet }

/-- Translate a surface program and run the pass on it without type checking. -/
private def monoParsed (t : StrataDDM.Program) : Core.Program :=
  runMono (translateWithMetaData t)

/-- Run the pass on a parsed program and format the result as surface syntax. -/
private def fmtMono (t : StrataDDM.Program) : Std.Format :=
  Std.format (monoParsed t).stripMetaData

/-- Every procedure in the program is monomorphic: no declared type parameters
    (`typeArgs`) remain.  (That the substitution left no *free* type variable
    behind is checked more directly by the exact formatted output of each
    example and by the `typeChecks` guards.) -/
private def allProcsMonomorphic (p : Core.Program) : Bool :=
  p.decls.all fun
    | .proc proc _ => proc.header.typeArgs.isEmpty
    | _ => true

/-- Count the opaque type declarations introduced by the pass.  These are
    nullary type *constructors* (`TypeDecl.con`); polymorphic `datatype`
    declarations (`TypeDecl.data`) present in the input are not counted. -/
private def opaqueTypeCount (p : Core.Program) : Nat :=
  (p.decls.filter fun
    | .type (.con _) _ => true
    | _ => false).length

/-- True when the program type-checks successfully. -/
private def typeChecks (p : Core.Program) : Bool :=
  match Core.typeCheck quietOpts p with
  | .ok _ => true
  | .error _ => false

/-- Run the full verification pipeline (which includes `GenOpaqueTypeParams`
    after type checking) on a parsed program and print the VC verdicts.  Routes
    through `Core.verifyProgram` on the translated `Core.Program` — the same
    pipeline `Core.verify` uses. -/
private def verifyMono (t : StrataDDM.Program)
    (options : Core.VerifyOptions := .default) : IO Core.VCResults :=
  EIO.toIO (fun s => IO.userError s) (Core.verifyProgram (translateWithMetaData t) options)

---------------------------------------------------------------------
/-! ### Example 1: single type variable, body with a local declaration -/

private def idPgm :=
#strata
program Core;
procedure id<T>(x : T, out y : T)
spec {
  ensures y == x;
}
{
  var z : T := x;
  y := z;
};
#end

/--
info: program Core;

type $__opaque_id_T_0;
procedure id (x : $__opaque_id_T_0, out y : $__opaque_id_T_0)
spec {
  ensures [id_ensures_0]: y == x;
  } {
  var z : $__opaque_id_T_0 := x;
  y := z;
};
-/
#guard_msgs in
#eval fmtMono idPgm

#guard allProcsMonomorphic (monoParsed idPgm)
#guard opaqueTypeCount (monoParsed idPgm) == 1
#guard typeChecks (monoParsed idPgm)

---------------------------------------------------------------------
/-! ### Example 1b: a CFG body, with a local declaration and a branch guard at `T` -/

private def pickPgm :=
#strata
program Core;
procedure pick<T>(c : bool, x : T, y : T, out r : T)
spec {
  ensures (r == x) || (r == y);
}
cfg entry {
  entry: { var z : T := y; branch (x == z) goto a else goto b; }
  a: { r := x; goto done; }
  b: { r := z; goto done; }
  done: { return; }
};
#end

/--
info: program Core;

type $__opaque_pick_T_0;
procedure pick (c : bool, x : $__opaque_pick_T_0, y : $__opaque_pick_T_0,
  out r : $__opaque_pick_T_0)
spec {
  ensures [pick_ensures_0]: r == x || r == y;
  } cfg entry {
  entry: {
    var z : $__opaque_pick_T_0 := y;
    branch (x == z) goto a else goto b;
  }
  a: {
    r := x;
    goto done;
  }
  b: {
    r := z;
    goto done;
  }
  done: {
    return;
  }
};
-/
#guard_msgs (whitespace := lax) in
#eval fmtMono pickPgm

#guard allProcsMonomorphic (monoParsed pickPgm)
#guard opaqueTypeCount (monoParsed pickPgm) == 1
#guard typeChecks (monoParsed pickPgm)

---------------------------------------------------------------------
/-! ### Example 2: a monomorphic procedure is left unchanged -/

private def incPgm :=
#strata
program Core;
procedure inc(x : int, out y : int)
{
  y := x;
};
#end

/--
info: program Core;

procedure inc (x : int, out y : int)
{
  y := x;
};
-/
#guard_msgs in
#eval fmtMono incPgm

#guard allProcsMonomorphic (monoParsed incPgm)
#guard opaqueTypeCount (monoParsed incPgm) == 0
#guard typeChecks (monoParsed incPgm)

---------------------------------------------------------------------
/-! ### Example 3: two type variables -/

private def swapPgm :=
#strata
program Core;
procedure swap<A, B>(a : A, b : B, out c : A, out d : B)
{
  c := a;
  d := b;
};
#end

/--
info: program Core;

type $__opaque_swap_A_0;
type $__opaque_swap_B_1;
procedure swap (a : $__opaque_swap_A_0, b : $__opaque_swap_B_1, out c : $__opaque_swap_A_0, out d : $__opaque_swap_B_1)
{
  c := a;
  d := b;
};
-/
#guard_msgs in
#eval fmtMono swapPgm

#guard allProcsMonomorphic (monoParsed swapPgm)
#guard opaqueTypeCount (monoParsed swapPgm) == 2
#guard typeChecks (monoParsed swapPgm)

---------------------------------------------------------------------
/-! ### Example 4: a type parameter used in the spec -/

private def polyReflPgm :=
#strata
program Core;
procedure useT<a>(x : a)
spec {
  requires x == x;
}
{
  assert x == x;
};
#end

/--
info: program Core;

type $__opaque_useT_a_0;
procedure useT (x : $__opaque_useT_a_0)
spec {
  requires [useT_requires_0]: x == x;
  } {
  assert [assert_0]: x == x;
};
-/
#guard_msgs in
#eval fmtMono polyReflPgm

#guard allProcsMonomorphic (monoParsed polyReflPgm)
#guard opaqueTypeCount (monoParsed polyReflPgm) == 1
#guard typeChecks (monoParsed polyReflPgm)

---------------------------------------------------------------------
/-! ### Example 5: a polymorphic datatype (`List a`) in a constructor

The datatype `List` stays polymorphic — only the *procedure* gets opaque types —
so the opaque type introduced for `T` appears as a type *argument* of `List`
(`List $__opaque_prepend_T_0`). -/

private def prependPgm :=
#strata
program Core;
datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };
procedure prepend<T>(x : T, xs : List T, out r : List T)
spec {
  ensures List..isCons(r);
}
{
  r := Cons(x, xs);
};
#end

/--
info: program Core;

datatype List (a : Type) {
  Nil(),
  Cons(head : a, tail : List a)
};
type $__opaque_prepend_T_0;
procedure prepend (x : $__opaque_prepend_T_0, xs : List $__opaque_prepend_T_0, out r : List $__opaque_prepend_T_0)
spec {
  ensures [prepend_ensures_0]: List..isCons(r);
  } {
  r := Cons(x, xs);
};
-/
#guard_msgs in
#eval fmtMono prependPgm

#guard allProcsMonomorphic (monoParsed prependPgm)
#guard opaqueTypeCount (monoParsed prependPgm) == 1
#guard typeChecks (monoParsed prependPgm)

---------------------------------------------------------------------
/-! ### Example 6: a polymorphic datatype (`List a`) with a destructor and a
local variable -/

private def headOfPgm :=
#strata
program Core;
datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };
procedure headOf<T>(xs : List T, out h : T)
spec {
  requires List..isCons(xs);
}
{
  var first : T := List..head!(xs);
  h := first;
};
#end

/--
info: program Core;

datatype List (a : Type) {
  Nil(),
  Cons(head : a, tail : List a)
};
type $__opaque_headOf_T_0;
procedure headOf (xs : List $__opaque_headOf_T_0, out h : $__opaque_headOf_T_0)
spec {
  requires [headOf_requires_0]: List..isCons(xs);
  } {
  var first : $__opaque_headOf_T_0 := List..head!(xs);
  h := first;
};
-/
#guard_msgs in
#eval fmtMono headOfPgm

#guard allProcsMonomorphic (monoParsed headOfPgm)
#guard opaqueTypeCount (monoParsed headOfPgm) == 1
#guard typeChecks (monoParsed headOfPgm)

---------------------------------------------------------------------
/-! ### Example 7: a Lambda-valued local's types are substituted too

Internal function syntax translates to an ordinary function-typed `init`.
The input below intentionally remains `function` syntax so this test covers
both `funcDecl_statement` lowering and the subsequent opaque-type substitution. The
pass substitutes both the initializer's declared arrow type and the type
annotations on its nested abstraction, so a local value referencing the
procedure's type parameter gets the same opaque type everywhere. -/

private def internalFuncPgm :=
#strata
program Core;
procedure Q<T>(x : T, out r : T)
{
  function f(y : T) : T { y }
  r := f(x);
};
#end

/--
info: program Core;

type $__opaque_Q_T_0;
procedure Q (x : $__opaque_Q_T_0, out r : $__opaque_Q_T_0)
{
  var f : $__opaque_Q_T_0 -> $__opaque_Q_T_0 := fun y : $__opaque_Q_T_0 => y;
  r := f(x);
};
-/
#guard_msgs in
#eval fmtMono internalFuncPgm

#guard allProcsMonomorphic (monoParsed internalFuncPgm)
#guard opaqueTypeCount (monoParsed internalFuncPgm) == 1

---------------------------------------------------------------------
/-! ### Example 8: a lemma's leftover type variables become opaque types

A lemma built without a type check can quantify at a type variable that is
not among its type parameters. The whole phase replaces each such variable by
a new opaque type, after replacing the declared type parameters as for a
procedure. -/

/-- Run the whole phase, including the closing of leftover lemma type
    variables, and format the result. -/
private def fmtPhase (p : Core.Program) : Std.Format :=
  match Core.Transform.run p Core.genOpaqueTypeParams with
  | .ok (_, p') => Std.format p'.stripMetaData
  | .error e => Std.format e

/-- `∀ x : ty. body`. -/
private def allAt (x : String) (ty : Lambda.LMonoTy)
    (body : Core.Expression.Expr) : Core.Expression.Expr :=
  .quant Core.coreLoc .all x (some ty) (.const Core.coreLoc (.boolConst true)) body

/-- A program with the single lemma `name`. -/
private def lemmaPgm (typeArgs : List String) (e : Core.Expression.Expr)
    (name : Core.CoreLabel := "L") : Core.Program :=
  { decls := [.lemma { name := name, typeArgs := typeArgs, e := e } .empty] }

-- A lemma with no type parameters quantifying at a leftover type variable `t`.
/--
info: program Core;

type $__free_L_0;
lemma [L] (z : $__free_L_0) { true }
  : z == z;
-/
#guard_msgs in
#eval fmtPhase (lemmaPgm []
  (allAt "z" (.ftvar "t") (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0))))

-- A lemma with type parameter `a` and a leftover type variable `t`.
/--
info: program Core;

type $__opaque_L_a_0;
type $__free_L_0;
lemma [L] (y : $__opaque_L_a_0) { true }
  : forall z : $__free_L_0 ::  { true }
  y == y;
-/
#guard_msgs in
#eval fmtPhase (lemmaPgm ["a"]
  (allAt "y" (.ftvar "a")
    (allAt "z" (.ftvar "t") (.eq Core.coreLoc (.bvar Core.coreLoc 1) (.bvar Core.coreLoc 1)))))

-- A lemma with nothing left over once its type parameters are replaced gets
-- no `$__free_` type.
/--
info: program Core;

type $__opaque_L_a_0;
lemma [L] (y : $__opaque_L_a_0) { true }
  : y == y;
-/
#guard_msgs in
#eval fmtPhase (lemmaPgm ["a"]
  (allAt "y" (.ftvar "a") (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0))))

-- Type checking accepts a lemma whose name contains `#` when it has a type
-- variable in its annotations: the opaque type built from its name has the `#`
-- replaced.
/--
info: accepted
-/
#guard_msgs in
#eval
  match Core.typeCheck quietOpts (lemmaPgm ["a"]
      (allAt "z" (.ftvar "a") (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0)))
          "L#1") with
  | .ok _ => Std.format "accepted"
  | .error e => Std.format e

-- The phase itself does only the closing: given such a lemma, it builds the type named
-- after it, with the `#` replaced by `_`; the lemma keeps its name.
/--
info: program Core;

type $__free_L_1_0;
lemma [|L#1|] (z : $__free_L_1_0) { true }
  : z == z;
-/
#guard_msgs in
#eval fmtPhase (lemmaPgm []
  (allAt "z" (.ftvar "t") (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0))) "L#1")

-- A declared type parameter of such a lemma gets an opaque type whose name has the `#`
-- replaced too; the lemma keeps its name.
/--
info: program Core;

type $__opaque_L_1_a_0;
lemma [|L#1|] (z : $__opaque_L_1_a_0) { true }
  : z == z;
-/
#guard_msgs in
#eval fmtPhase (lemmaPgm ["a"]
  (allAt "z" (.ftvar "a") (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0))) "L#1")


---------------------------------------------------------------------
/-! ### Example 9: the opaque type avoids a type declared in the body

The assumption makes the local `$__opaque_P_a_0` a singleton, so the assertion over the type
parameter must be checked at another type. -/

private def localOpaqueNamePgm :=
#strata
program Core;
procedure P<a> ()
{
  type $__opaque_P_a_0;
  assume [one]: forall x : $__opaque_P_a_0, y : $__opaque_P_a_0 :: x == y;
  assert [aa]: forall x : a, y : a :: x == y;
};
#end

/--
info:
Obligation: aa
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval verifyMono localOpaqueNamePgm quietOpts

---------------------------------------------------------------------
/-! ### Examples: end-to-end verification via `Core.verify`

These run the *whole* pipeline (so `GenOpaqueTypeParams` runs before the SMT
encoder) and check the solver verdicts.  The point: after this pass a
procedure's type parameter is a *declared* opaque type rather than a free type
variable, so a quantified contract over it is encoded as a quantifier over an
uninterpreted sort — a valid contract verifies, a false one is refuted. -/

/-! #### End-to-end Example 1: a valid contract quantified over the type parameter verifies -/

private def reflPgm : StrataDDM.Program :=
#strata
program Core;
procedure Refl<a>(x : a, out r : a)
spec {
  ensures (forall y : a :: y == y);
}
{
  r := x;
};
procedure Test() spec { ensures true; }
{
  var h : int;
  call Refl(1, out h);
};
#end

/--
info:
Obligation: Refl_ensures_0
Property: assert
Result: ✅ pass

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyMono reflPgm quietOpts

/-! #### End-to-end Example 2: a false ("singleton") contract over the type parameter is
refuted — the opaque type has arbitrary cardinality, so `forall y :: y == x`
does not hold. -/

private def singletonPgm : StrataDDM.Program :=
#strata
program Core;
procedure ConstAll<a>(x : a, out r : a)
spec {
  ensures (forall y : a :: y == x);
}
{
  r := x;
};
procedure Test() spec { ensures true; }
{
  var h : int;
  call ConstAll(1, out h);
};
#end

/--
info:
Obligation: ConstAll_ensures_0
Property: assert
Result: ❌ fail

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyMono singletonPgm quietOpts

/-! #### End-to-end Example 3: a type parameter whose source name is a builtin sort
(`Map`).  The pass renames it to a fresh opaque type regardless, and the
false contract is refuted. -/

private def builtinNamedPgm : StrataDDM.Program :=
#strata
program Core;
procedure P<Map>(x : Map, out r : Map)
spec {
  ensures (forall y : Map :: y == x);
}
{
  r := x;
};
#end

/--
info:
Obligation: P_ensures_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verifyMono builtinNamedPgm quietOpts

/-! #### End-to-end Example 4: two distinct type parameters get two distinct opaque types.
`Two`'s well-sorted reflexive contract verifies; `TwoBad`'s singleton claim over
one parameter is refuted (the other parameter's sort does not constrain it). -/

private def twoTyVarsPgm : StrataDDM.Program :=
#strata
program Core;
procedure Two<a, b>(x : a, w : b, out r : a)
spec {
  ensures (forall y : a :: forall z : b :: y == y && z == z);
}
{
  r := x;
};
procedure TwoBad<a, b>(x : a, w : b, out r : a)
spec {
  ensures (forall y : a :: y == x);
}
{
  r := x;
};
procedure Test() spec { ensures true; }
{
  var h : int;
  call Two(1, true, out h);
  var g : int;
  call TwoBad(2, false, out g);
};
#end

/--
info:
Obligation: Two_ensures_0
Property: assert
Result: ✅ pass

Obligation: TwoBad_ensures_0
Property: assert
Result: ❌ fail

Obligation: Test_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyMono twoTyVarsPgm quietOpts

/-! #### End-to-end Example 5: the same singleton program under bug-finding (z3 + mbqi).

`forall y : a :: y == x` is satisfiable over a one-element interpretation of the
opaque sort(!). -/

private def satLegOpts : Core.VerifyOptions :=
  { Core.VerifyOptions.default with
    verbose := .quiet, checkMode := .bugFinding,
    solver := "z3", solverOptions := #[("smt.mbqi", "true")] }

/--
info:
Obligation: ConstAll_ensures_0
Property: assert
Result: ❓ satisfiable

Obligation: Test_ensures_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verifyMono singletonPgm satLegOpts

/-! #### End-to-end Example 6: a polymorphic datatype (`List`) end-to-end.

A procedure over `List T` whose postcondition follows from the datatype axioms
(`head!(Cons(x, xs)) == x`) verifies after the pass — `T` is a declared
opaque type and `List` remains generic, applied to it. -/

private def listHeadPgm : StrataDDM.Program :=
#strata
program Core;
datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };
procedure headOfCons<T>(x : T, xs : List T, out h : T)
spec {
  ensures h == x;
}
{
  var ys : List T := Cons(x, xs);
  h := List..head!(ys);
};
#end

/--
info:
Obligation: headOfCons_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyMono listHeadPgm quietOpts

/-! #### End-to-end Example 7: a recursive polymorphic procedure.

`CallElim` inlines the recursive call's *contract* (it never duplicates the
body), so recursion — even were it non-uniform — does not affect this
Skolemization-style pass: each procedure's own type parameter is replaced by one
fresh opaque type, independently of any (recursive or not) call. -/

private def recPgm : StrataDDM.Program :=
#strata
program Core;
procedure idRec<T>(x : T, out r : T)
spec {
  ensures r == x;
}
{
  r := x;
  call idRec(x, out r);
};
#end

/--
info:
Obligation: idRec_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyMono recPgm quietOpts

/-! #### End-to-end Example 8: a generic procedure whose body uses `List int`.

The program type-checks and verifies. -/

private def concreteListInGenericPgm : StrataDDM.Program :=
#strata
program Core;
datatype List (a : Type) { Nil(), Cons(head: a, tail: List a) };
procedure store<a>(x : a, out r : a)
spec {
  ensures r == x;
}
{
  var xs : List int := Cons(1, Nil());
  r := x;
};
#end

/--
info:
Obligation: store_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyMono concreteListInGenericPgm quietOpts

end GenOpaqueTypeParamsTests

end
