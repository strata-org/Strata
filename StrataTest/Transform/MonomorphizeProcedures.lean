/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.ProgramType
meta import Strata.Transform.MonomorphizeProcedures

meta section

open Strata

/-! ## `MonomorphizeProcedures` tests

`MonomorphizeProcedures` monomorphizes every polymorphic procedure by minting a
fresh opaque nullary type per declared type parameter (`header.typeArgs`) and
substituting it throughout the procedure's signature, spec, and body.

It runs in `corePipelinePhases` just *before* `typeCheckPhase` (after `CallElim`
has removed every `call`), while each procedure still carries its type
parameters under their source names.  The tests below therefore feed the pass a
freshly-*parsed* (translated, not yet type-checked) program — exactly what it
sees in the pipeline — and check both the substituted output and that the result
subsequently type-checks.
-/

section MonomorphizeProceduresTests

/-- Run the monomorphization pass on a program (fresh generator state, so
    opaque-type counters start at 0). -/
private def runMono (p : Core.Program) : Core.Program :=
  match Core.Transform.run p Core.MonomorphizeProcedures.run with
  | .ok p' => p'
  | .error _ => p

private def translate (t : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

private def quietOpts : Core.VerifyOptions :=
  { Core.VerifyOptions.default with verbose := .quiet }

/-- Translate (parse) a surface program, then monomorphize — mirroring the
    pipeline position where the pass runs just before `typeCheckPhase`, while
    `header.typeArgs` are still intact under their source names. -/
private def monoBeforeTypeCheck (t : StrataDDM.Program) : Core.Program :=
  runMono (translate t)

/-- Monomorphize a parsed program and format the result as surface syntax. -/
private def fmtMono (t : StrataDDM.Program) : Std.Format :=
  Std.format (monoBeforeTypeCheck t).stripMetaData

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

/-- Run the full verification pipeline (which includes `MonomorphizeProcedures`
    before type checking) on a parsed program and print the VC verdicts.  Routes
    through `Core.verifyProgram` on the translated `Core.Program` — the same
    pipeline `Core.verify` uses. -/
private def verifyMono (t : StrataDDM.Program)
    (options : Core.VerifyOptions := .default) : IO Core.VCResults :=
  EIO.toIO (fun s => IO.userError s) (Core.verifyProgram (translate t) options)

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

#guard allProcsMonomorphic (monoBeforeTypeCheck idPgm)
#guard opaqueTypeCount (monoBeforeTypeCheck idPgm) == 1
#guard typeChecks (monoBeforeTypeCheck idPgm)

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

#guard allProcsMonomorphic (monoBeforeTypeCheck incPgm)
#guard opaqueTypeCount (monoBeforeTypeCheck incPgm) == 0
#guard typeChecks (monoBeforeTypeCheck incPgm)

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

#guard allProcsMonomorphic (monoBeforeTypeCheck swapPgm)
#guard opaqueTypeCount (monoBeforeTypeCheck swapPgm) == 2
#guard typeChecks (monoBeforeTypeCheck swapPgm)

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

#guard allProcsMonomorphic (monoBeforeTypeCheck polyReflPgm)
#guard opaqueTypeCount (monoBeforeTypeCheck polyReflPgm) == 1
#guard typeChecks (monoBeforeTypeCheck polyReflPgm)

---------------------------------------------------------------------
/-! ### Example 5: a polymorphic datatype (`List a`) in a constructor

The datatype `List` stays polymorphic — only the *procedure* is monomorphized —
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

#guard allProcsMonomorphic (monoBeforeTypeCheck prependPgm)
#guard opaqueTypeCount (monoBeforeTypeCheck prependPgm) == 1
#guard typeChecks (monoBeforeTypeCheck prependPgm)

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

#guard allProcsMonomorphic (monoBeforeTypeCheck headOfPgm)
#guard opaqueTypeCount (monoBeforeTypeCheck headOfPgm) == 1
#guard typeChecks (monoBeforeTypeCheck headOfPgm)

---------------------------------------------------------------------
/-! ### Example 7: an internal function declaration's types are substituted too

The pass reuses the type checker's `Statement.subst`, whose `funcDecl` case
substitutes the internal function's input / output / body types.  So even a
statement-level `function` referencing the procedure's type parameter is
monomorphized correctly (in the pipeline `LiftInternalFuncDecls` lifts these to
the top level before this pass runs, so it does not arise there). -/

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
  function f (y : $__opaque_Q_T_0) : $__opaque_Q_T_0 { y }
  r := f(x);
};
-/
#guard_msgs in
#eval fmtMono internalFuncPgm

#guard allProcsMonomorphic (monoBeforeTypeCheck internalFuncPgm)
#guard opaqueTypeCount (monoBeforeTypeCheck internalFuncPgm) == 1


---------------------------------------------------------------------
/-! ### Examples: end-to-end verification via `Core.verify`

These run the *whole* pipeline (so `MonomorphizeProcedures` runs before the SMT
encoder) and check the solver verdicts.  The point: after monomorphization a
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
(`Map`).  Monomorphization renames it to a fresh opaque type regardless, and the
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
(`head!(Cons(x, xs)) == x`) verifies after monomorphization — `T` is a declared
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

end MonomorphizeProceduresTests

end
