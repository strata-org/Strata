/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import StrataDDM.Util.Format
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.ProgramType
meta import Strata.Languages.Core.ProgramWF
meta import Strata.Languages.Core.StatementSemantics
meta import Strata.Transform.CoreTransform
meta import Strata.Transform.CallElim
meta import Strata.Languages.Core.Verifier
meta import StrataTest.Transform.CallFixtures
meta import StrataTest.Languages.Core.Tests.TestUtil

meta section


open Core
private abbrev testLoc : ExprSourceLoc := ExprSourceLoc.synthesized "test"
open Core.Transform
open CallElim
open Strata

/-! ## Call Elimination Examples -/
section CallElimExamples

def CallElimTest1 :=
#strata
program Core;
procedure f(i : bool, inout j : bool, x : bool, out y : bool)
spec {
  requires (i == !x);
  ensures (y == x);
  ensures (y == j);
};
procedure h(i : bool, inout j : bool, k : bool) {
  var b : bool;
  call f(i, inout j, k, out b);
};
#end

def CallElimTest1Ans :=
#strata
program Core;
procedure f(i : bool, inout j : bool, x : bool, out y : bool)
spec {
  requires (i == !x);
  ensures (y == x);
  ensures (y == j);
};
procedure h(i : bool, inout j : bool, k : bool) {
  var b : bool;
  var tmp_arg_0 : bool := i;
  var tmp_arg_1 : bool := j;
  var tmp_arg_2 : bool := k;
  var tmp_j_3 : bool := j;
  var tmp_b_4 : bool := b;
  assert [callElimAssert_f_requires_0_5]: (tmp_arg_0 == (!tmp_arg_2));
  havoc j;
  havoc b;
  assume [callElimPost_f_ensures_1_6]: (b == tmp_arg_2);
  assume [callElimPost_f_ensures_2_7]: (b == j);
};
#end

def CallElimTest2 :=
#strata
program Core;
procedure f(i : bool, inout j : bool, k : bool, x : bool, y : bool, out z : bool)
spec {
  requires (i == !x);
  ensures (z == (k && old j));
  ensures (z == old j);
};
procedure h(i : bool, inout j : bool, k : bool, l : bool) {
  var b : bool;
  call f(i, inout j, k, k, l, out b);
};
#end

def CallElimTest2Ans :=
#strata
program Core;
procedure f(i : bool, inout j : bool, k : bool, x : bool, y : bool, out z : bool)
spec {
  requires (i == !x);
  ensures (z == (k && old j));
  ensures (z == old j);
};
procedure h(i : bool, inout j : bool, k : bool, l : bool) {
  var b : bool;
  var tmp_arg_0 : bool := i;
  var tmp_arg_1 : bool := j;
  var tmp_arg_2 : bool := k;
  var tmp_arg_3 : bool := k;
  var tmp_arg_4 : bool := l;
  var tmp_j_5 : bool := j;
  var tmp_b_6 : bool := b;
  var old_j_7 : bool := j;
  assert [callElimAssert_f_requires_0_8]: tmp_arg_0 == !tmp_arg_3;
  havoc j;
  havoc b;
  assume [callElimPost_f_ensures_1_9]: b == (tmp_arg_2 && old_j_7);
  assume [callElimPost_f_ensures_2_10]: b == old_j_7;
};
#end

def CallElimTest3 :=
#strata
program Core;
procedure f(i : bool, inout j : bool, k : bool, x : bool, y : bool, out z : bool)
spec {
  requires (i == !x);
  ensures (z == (k && old j));
  ensures (z == old j);
};
procedure h(i : bool, inout j : bool, k : bool, l : bool) {
  var b : bool;
  call f(i, inout j, k, k && i || j, l, out b);
};
#end

def CallElimTest3Ans :=
#strata
program Core;
procedure f(i : bool, inout j : bool, k : bool, x : bool, y : bool, out z : bool)
spec {
  requires (i == !x);
  ensures (z == (k && old j));
  ensures (z == old j);
};
procedure h(i : bool, inout j : bool, k : bool, l : bool) {
  var b : bool;
  var tmp_arg_0 : bool := i;
  var tmp_arg_1 : bool := j;
  var tmp_arg_2 : bool := k;
  var tmp_arg_3 : bool := k && i || j;
  var tmp_arg_4 : bool := l;
  var tmp_j_5 : bool := j;
  var tmp_b_6 : bool := b;
  var old_j_7 : bool := j;
  assert [callElimAssert_f_requires_0_8]: tmp_arg_0 == !tmp_arg_3;
  havoc j;
  havoc b;
  assume [callElimPost_f_ensures_1_9]: b == (tmp_arg_2 && old_j_7);
  assume [callElimPost_f_ensures_2_10]: b == old_j_7;
};
#end

-- Free preconditions should NOT be asserted at call sites
def CallElimTestFreeRequires :=
#strata
program Core;
procedure f(inout j : bool, k : bool, x : bool, out y : bool)
spec {
  free requires (x == k);
  requires (x == j);
  ensures (y == x);
};
procedure h(inout j : bool, k : bool) {
  var b : bool;
  call f(inout j, k, k, out b);
};
#end

def CallElimTestFreeRequiresAns :=
#strata
program Core;
procedure f(inout j : bool, k : bool, x : bool, out y : bool)
spec {
  free requires (x == k);
  requires (x == j);
  ensures (y == x);
};
procedure h(inout j : bool, k : bool) {
  var b : bool;
  var tmp_arg_0 : bool := j;
  var tmp_arg_1 : bool := k;
  var tmp_arg_2 : bool := k;
  var tmp_j_3 : bool := j;
  var tmp_b_4 : bool := b;
  assert [callElimAssert_f_requires_1_5]: (tmp_arg_2 == tmp_arg_0);
  havoc j;
  havoc b;
  assume [callElimPost_f_ensures_2_6]: (b == tmp_arg_2);
};
#end

def translate (t : StrataDDM.SourcedProgram) : Core.Program := (TransM.run Inhabited.default (translateProgram t)).fst

def env : Lambda.LContext CoreLParams := .default (functions := Core.Factory)

def tests : List (Core.Program × Core.Program) := [
  (CallElimTest1, CallElimTest1Ans),
  (CallElimTest2, CallElimTest2Ans),
  (CallElimTest3, CallElimTest3Ans),
  (CallElimTestFreeRequires, CallElimTestFreeRequiresAns),
].map (Prod.map translate translate)

def callElim (p : Core.Program)
  : Core.Program :=
  match (run p callElim') with
  | .ok (_changed, res) => res
  | .error e => panic! (toString e) -- nopanic:ok

/-- info: 4 of 4 examples equal their expected results -/
#guard_msgs in
#eval IO.println
  s!"{(tests.filter (λ (test, ans) ↦
    (toString (callElim test).eraseTypes) == (toString ans.eraseTypes))).length} of \
    {tests.length} examples equal their expected results"

end CallElimExamples

/-! ## Temporaries avoid the program's variable names

`h` declares a variable with the name each kind of temporary would get: `tmp_arg_0` for the first
argument, `tmp_j_3` for the output `j`, and, after the call, `old_j_6` for `old j`. Each temporary
takes the next name the program does not declare, so no `init` of a temporary overwrites a
program variable. -/
section CallElimFreshTemporaries

def CallElimTestTakenNames :=
#strata
program Core;
procedure f(x : int, inout j : int, out y : int)
spec {
  ensures (y == x);
  ensures (j == old j);
};
procedure h(inout j : int) {
  var tmp_arg_0 : int := 5;
  var tmp_j_3 : int := 6;
  var b : int;
  call f(7, inout j, out b);
  var old_j_6 : int := 7;
};
#end

/--
info: program Core;

procedure f (x : int, inout j : int, out y : int)
spec {
  ensures [f_ensures_0]: y == x;
  ensures [f_ensures_1]: j == old j;
  } ;
procedure h (inout j : int)
{
  var tmp_arg_0 : int := 5;
  var tmp_j_3 : int := 6;
  var b : int;
  var tmp_arg_1 : int := 7;
  var tmp_arg_2 : int := j;
  var tmp_j_4 : int := j;
  var tmp_b_5 : int := b;
  var old_j_7 : int := j;
  havoc j;
  havoc b;
  assume [callElimPost_f_ensures_0_8]: b == tmp_arg_1;
  assume [callElimPost_f_ensures_1_9]: j == old_j_7;
  var old_j_6 : int := 7;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim (translate CallElimTestTakenNames)))

end CallElimFreshTemporaries

/-! ## Call elimination at the call's type instance

Each program below except `unknownProg` and `conflictProg` is a fully annotated Core AST.
The printed result shows the types call elimination gives the temporaries; the `#guard` checks
that every expression of the result carries its type annotations. -/
section CallInstanceTests
open Lambda
open Core.CallFixtures Core.TestUtil

private def idpP : Decl :=
  mkProc "idp" ["a"] [("x", tv "a")] [("r", tv "a")]
    (post := [eqE (v "r" (tv "a")) (v "x" (tv "a"))])
private def swapP : Decl :=
  mkProc "swap" ["a"] [("x", tv "a"), ("y", tv "a")] [("x", tv "a"), ("y", tv "a")]
    (post := [eqE (v "x" (tv "a")) (v (CoreIdent.mkOld "y").name (tv "a"))])
private def seqP : Decl :=
  mkProc "p" ["a"] [("s", seqTy (seqTy (tv "a")))] []
    (pre := [eqE (v "s" (seqTy (seqTy (tv "a")))) (v "s" (seqTy (seqTy (tv "a"))))])
/-- `Take<a>(x : a)` with a precondition on `x`. -/
private def takeP : Decl :=
  mkProc "Take" ["a"] [("x", tv "a")] []
    (pre := [eqE (v "x" (tv "a")) (v "x" (tv "a"))])
/-- `Both<a, b>(x : a, y : b)` with a precondition on `x`. -/
private def bothP : Decl :=
  mkProc "Both" ["a", "b"] [("x", tv "a"), ("y", tv "b")] []
    (pre := [eqE (v "x" (tv "a")) (v "x" (tv "a"))])
private def pairP : Decl :=
  mkProc "pair" ["a", "b"] [("x", tv "a"), ("y", tv "b")] [("r", tv "a")]
    (post := [eqE (v "r" (tv "a")) (v "x" (tv "a"))])
/-- `r<a, b>(x : a)` with `b` only in a precondition. -/
private def rP : Decl :=
  mkProc "r" ["a", "b"] [("x", tv "a")] []
    (pre := [eqE (v "x" (tv "a")) (v "x" (tv "a")), reflAll (tv "b")])

/--
info: program Core;

procedure idp<a> (x : a, out r : a)
spec {
  ensures [idp_ensures_0]: r == x;
  } {
  
};
procedure Caller ()
{
  var ai : int;
  var tmp_arg_0 : int := 7;
  var tmp_ai_1 : int := ai;
  havoc ai;
  assume [$__callElimAssume_idp_ensures_0_2]: ai == tmp_arg_0;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim (idpProg idpP)))
#guard (callElim (idpProg idpP)).allExprs LExpr.fullyAnnotated

/--
info: program Core;

procedure swap<a> (inout x : a, inout y : a)
spec {
  ensures [swap_ensures_0]: x == old y;
  } {
  
};
procedure Caller ()
{
  var i : int;
  var j : int;
  var tmp_arg_0 : int := i;
  var tmp_arg_1 : int := j;
  var tmp_i_2 : int := i;
  var tmp_j_3 : int := j;
  var old_j_4 : int := j;
  havoc i;
  havoc j;
  assume [$__callElimAssume_swap_ensures_0_5]: i == old_j_4;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim (swapProg swapP)))
#guard (callElim (swapProg swapP)).allExprs LExpr.fullyAnnotated

/--
info: program Core;

procedure p<a> (s : Sequence (Sequence a))
spec {
  requires [p_requires_0]: s == s;
  } {
  
};
procedure Caller (t : Sequence (Sequence int))
{
  var tmp_arg_0 : Sequence (Sequence int) := t;
  assert [callElimAssert_p_requires_0_1]: tmp_arg_0 == tmp_arg_0;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim (seqProg seqP)))
#guard (callElim (seqProg seqP)).allExprs LExpr.fullyAnnotated

/--
info: program Core;

procedure idp<a> (x : a, out r : a)
spec {
  ensures [idp_ensures_0]: r == x;
  } {
  
};
procedure Caller<a> (z : a)
{
  var w : a;
  var tmp_arg_0 : a := z;
  var tmp_w_1 : a := w;
  havoc w;
  assume [$__callElimAssume_idp_ensures_0_2]: w == tmp_arg_0;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim (sameNameProg idpP)))
#guard (callElim (sameNameProg idpP)).allExprs LExpr.fullyAnnotated

/--
info: program Core;

procedure pair<a, b> (x : a, y : b, out r : a)
spec {
  ensures [pair_ensures_0]: r == x;
  } {
  
};
procedure Caller<a, b> (x : a, y : b)
{
  var w : b;
  var tmp_arg_0 : b := y;
  var tmp_arg_1 : a := x;
  var tmp_w_2 : b := w;
  havoc w;
  assume [$__callElimAssume_pair_ensures_0_3]: w == tmp_arg_0;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim (pairProg pairP)))
#guard (callElim (pairProg pairP)).allExprs LExpr.fullyAnnotated

/--
info: program Core;

type $__cety_0;
procedure q<a> ()
spec {
  requires [q_requires_0]: forall y : a :: y == y;
  } {
  
};
procedure Caller ()
{
  assert [callElimAssert_q_requires_0_1]: forall y : $__cety_0 :: y == y;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim (qProg qReflDecl)))
#guard (callElim (qProg qReflDecl)).allExprs LExpr.fullyAnnotated

/--
info: program Core;

type $__cety_0;
procedure r<a, b> (x : a)
spec {
  requires [r_requires_0]: x == x;
  requires [r_requires_1]: forall y : b :: y == y;
  } {
  
};
procedure Caller ()
{
  var tmp_arg_1 : int := 7;
  assert [callElimAssert_r_requires_0_2]: tmp_arg_1 == tmp_arg_1;
  assert [callElimAssert_r_requires_1_3]: forall y : $__cety_0 :: y == y;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim (rProg rP)))
#guard (callElim (rProg rP)).allExprs LExpr.fullyAnnotated

-- Stored type arguments give the type of a parameter that the call's arguments do not determine,
-- so no opaque type is declared.
/--
info: program Core;

procedure q<a> ()
spec {
  requires [q_requires_0]: forall y : a :: y == y;
  } {
  
};
procedure Caller ()
{
  assert [callElimAssert_q_requires_0_0]: forall y : int :: y == y;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim (qTyArgsProg qReflDecl (some [.forAll [] .int]))))
#guard (callElim (qTyArgsProg qReflDecl (some [.forAll [] .int]))).allExprs LExpr.fullyAnnotated

-- `q<a>()` has no arguments, so the call does not determine `a`, and the checker rejects the
-- caller. The unchecked `qProg` test above shows the opaque type call elimination gives `a`.
/--
info: Procedure 'Caller': the call to 'q' does not determine one of its type
parameters
-/
#guard_msgs (whitespace := lax) in
#eval match Core.typeCheck .quiet (qProg qReflDecl) with
  | .ok p => IO.println (toString (callElim p).stripMetaData)
  | .error e => IO.println e.message

-- The caller `P<b>(y : b)` calls `q<a>(x : a)` with `y`, so `a` is the caller's own type
-- parameter `b`.
/-- info: [some ["b"]] -/
#guard_msgs in
#eval tyArgsOfResult (Core.typeCheck .quiet (qParamProg qArgDecl))

/--
info: program Core;

procedure q<a> (x : a)
spec {
  requires [q_requires_0]: forall y : a :: y == y;
  } {
  
};
procedure P<b> (y : b)
{
  var tmp_arg_0 : b := y;
  assert [callElimAssert_q_requires_0_1]: forall y : b :: y == y;
};
-/
#guard_msgs in
#eval match Core.typeCheck .quiet (qParamProg qArgDecl) with
  | .ok p => IO.println (toString (callElim p).stripMetaData)
  | .error e => IO.println e.message

-- The pipeline order: type check, call elimination, then opaque type parameters.
/--
info: program Core;

type $__opaque_q_a_0;
procedure q (x : $__opaque_q_a_0)
spec {
  requires [q_requires_0]: forall y : $__opaque_q_a_0 :: y == y;
  } {
  
};
type $__opaque_P_b_1;
procedure P (y : $__opaque_P_b_1)
{
  var tmp_arg_0 : $__opaque_P_b_1 := y;
  assert [callElimAssert_q_requires_0_1]: forall y : $__opaque_P_b_1 :: y == y;
};
-/
#guard_msgs in
#eval match Core.typeCheck .quiet (qParamProg qArgDecl) with
  | .ok p =>
    match Core.Transform.run (callElim p) Core.genOpaqueTypeParams with
    | .ok (_, p') => IO.println (toString p'.stripMetaData)
    | .error e => IO.println e.message
  | .error e => IO.println e.message

-- A stored type that still contains a generated type variable is not used: `b` gets an opaque
-- type, while `a` is read from the stored type arguments.
/--
info: program Core;

type $__cety_0;
procedure r<a, b> (x : a)
spec {
  requires [r_requires_0]: x == x;
  requires [r_requires_1]: forall y : b :: y == y;
  } {
  
};
procedure Caller ()
{
  var tmp_arg_1 : int := 7;
  assert [callElimAssert_r_requires_0_2]: tmp_arg_1 == tmp_arg_1;
  assert [callElimAssert_r_requires_1_3]: forall y : $__cety_0 :: y == y;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim
  (rTyArgsProg rP (some [.forAll [] .int, .forAll [] (.ftvar "$__ty3")]))))
#guard (callElim
  (rTyArgsProg rP (some [.forAll [] .int, .forAll [] (.ftvar "$__ty3")]))).allExprs
  LExpr.fullyAnnotated

-- A stored type that is an instance of the type the argument gives is accepted: the argument
-- `s : Sequence $__ty0` gives `a = Sequence $__ty0`, and the stored `a = Sequence int` binds
-- `$__ty0` to `int`. The temporary for the argument has the type `Sequence int`.
/--
info: program Core;

procedure Take<a> (x : a)
spec {
  requires [Take_requires_0]: x == x;
  } {
  
};
procedure Caller ()
{
  var s : (Sequence $__ty0);
  var tmp_arg_0 : Sequence int := s;
  assert [callElimAssert_Take_requires_0_1]: tmp_arg_0 == tmp_arg_0;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim (genArgProg takeP "Take" (some [.forAll [] (seqTy .int)]))))

-- A generated variable that two arguments share is bound once for the whole call: the stored
-- `a = int, b = bool` cannot both instantiate `$__ty0`, so it is an error.
/--
info: Call elimination requires every call to be well-formed: the call to Both stores b = bool,
but its arguments give b = int
-/
#guard_msgs in
#eval match run (genPairArgProg bothP "Both"
    (some [.forAll [] .int, .forAll [] .bool])) callElim' with
  | .ok _ => IO.println "ok"
  | .error e => IO.println e.message

-- The stored `a = int, b = int` instantiate `$__ty0` consistently, so the call is accepted.
/--
info: program Core;

procedure Both<a, b> (x : a, y : b)
spec {
  requires [Both_requires_0]: x == x;
  } {
  
};
procedure Caller ()
{
  var s : $__ty0;
  var tmp_arg_0 : int := s;
  var tmp_arg_1 : int := s;
  assert [callElimAssert_Both_requires_0_2]: tmp_arg_0 == tmp_arg_0;
};
-/
#guard_msgs in
#eval match run (genPairArgProg bothP "Both"
    (some [.forAll [] .int, .forAll [] .int])) callElim' with
  | .ok (_, p) => IO.println (toString p)
  | .error e => IO.println e.message

-- The stored `b = $__ty0` mentions a generated variable, so it is dropped: `a` is `int`, and
-- `b` gets an opaque type as on a call without that entry.
/--
info: program Core;

type $__cety_0;
procedure Both<a, b> (x : a, y : b)
spec {
  requires [Both_requires_0]: x == x;
  } {
  
};
procedure Caller ()
{
  var s : $__ty0;
  var tmp_arg_1 : int := s;
  var tmp_arg_2 : $__cety_0 := s;
  assert [callElimAssert_Both_requires_0_3]: tmp_arg_1 == tmp_arg_1;
};
-/
#guard_msgs in
#eval match run (genPairArgProg bothP "Both"
    (some [.forAll [] .int, .forAll [] (.ftvar "$__ty0")])) callElim' with
  | .ok (_, p) => IO.println (toString p)
  | .error e => IO.println e.message

-- A stored type that is not an instance of the type the argument gives is an error, even though
-- that type contains a generated variable: `a` is stored as `bool`, but `s` is a `Sequence`.
/--
info: Call elimination requires every call to be well-formed: the call to Take stores a = bool,
but its arguments give a = (Sequence _)
-/
#guard_msgs in
#eval match run (genArgProg takeP "Take" (some [.forAll [] .bool])) callElim' with
  | .ok _ => IO.println "ok"
  | .error e => IO.println e.message

-- Stored type arguments that are not one entry per type parameter are ignored, and the call's
-- arguments determine the types as for a program that was not type-checked.
/--
info: program Core;

type $__cety_0;
procedure r<a, b> (x : a)
spec {
  requires [r_requires_0]: x == x;
  requires [r_requires_1]: forall y : b :: y == y;
  } {
  
};
procedure Caller ()
{
  var tmp_arg_1 : int := 7;
  assert [callElimAssert_r_requires_0_2]: tmp_arg_1 == tmp_arg_1;
  assert [callElimAssert_r_requires_1_3]: forall y : $__cety_0 :: y == y;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim (rTyArgsProg rP (some [.forAll [] .bool]))))
#guard (callElim (rTyArgsProg rP (some [.forAll [] .bool]))).allExprs LExpr.fullyAnnotated

-- A stored type that disagrees with the type the call's argument gives is an error: `a` is
-- stored as `bool`, but the argument `7` is an `int`.
/--
info: Call elimination requires every call to be well-formed: the call to r stores a = bool,
but its arguments give a = int
-/
#guard_msgs in
#eval match run (rTyArgsProg rP (some [.forAll [] .bool, .forAll [] .int])) callElim' with
  | .ok _ => IO.println "no error"
  | .error e => IO.println e.message

-- The disagreement is also found through an output argument: `a` is stored as `int`, the first
-- argument's type is unknown, and the output variable `bb` is a `bool`.
/--
info: Call elimination requires every call to be well-formed: the call to idp stores a = int,
but its arguments give a = bool
-/
#guard_msgs in
#eval match run { decls := [idpP, caller [] [] [declNondet "bb" .bool,
      .cmd (.call "idp" (some [.forAll [] .int]) [.inArg unknownArg, .outArg "bb"] .empty)]] }
    callElim' with
  | .ok _ => IO.println "no error"
  | .error e => IO.println e.message

-- A stored `$__callty` variable is not dropped, and no argument type is an instance of it:
-- `a` is stored as `$__callty0`, but the argument `7` is an `int`. The message writes the
-- generated variable as `_`.
/--
info: Call elimination requires every call to be well-formed: the call to r stores a = _,
but its arguments give a = int
-/
#guard_msgs in
#eval match run (rTyArgsProg rP (some [.forAll [] (.ftvar "$__callty0"), .forAll [] .int]))
    callElim' with
  | .ok _ => IO.println "no error"
  | .error e => IO.println e.message

-- An argument type with a `$__callty` variable is matched like one with a `$__ty` variable:
-- the stored `Sequence int` is an instance of the argument type `Sequence $__callty0`.
/--
info: program Core;

procedure Take<a> (x : a)
spec {
  requires [Take_requires_0]: x == x;
  } {
  
};
procedure Caller ()
{
  var s : (Sequence $__callty0);
  var tmp_arg_0 : Sequence int := s;
  assert [callElimAssert_Take_requires_0_1]: tmp_arg_0 == tmp_arg_0;
};
-/
#guard_msgs in
#eval match run { decls := [takeP, caller [] [] [declNondet "s" (seqTy (tv "$__callty0")),
      .cmd (.call "Take" (some [.forAll [] (seqTy .int)])
        [.inArg (v "s" (seqTy (tv "$__callty0")))] .empty)]] } callElim' with
  | .ok (_, p) => IO.println (toString p)
  | .error e => IO.println e.message

-- A stored type that is not an instance of the argument type `Sequence $__callty0` is an error;
-- the message writes the variable as `_`.
/--
info: Call elimination requires every call to be well-formed: the call to Take stores a = bool,
but its arguments give a = (Sequence _)
-/
#guard_msgs in
#eval match run { decls := [takeP, caller [] [] [declNondet "s" (seqTy (tv "$__callty0")),
      .cmd (.call "Take" (some [.forAll [] .bool])
        [.inArg (v "s" (seqTy (tv "$__callty0")))] .empty)]] } callElim' with
  | .ok _ => IO.println "no error"
  | .error e => IO.println e.message

-- The disagreement is also found through an in-out argument: `a` is stored as `bool`, but the
-- in-out variables `i` and `j` are `int`.
/--
info: Call elimination requires every call to be well-formed: the call to swap stores a = bool,
but its arguments give a = int
-/
#guard_msgs in
#eval match run { decls := [swapP, caller [] [] [declNondet "i" .int, declNondet "j" .int,
      .cmd (.call "swap" (some [.forAll [] .bool]) [.inoutArg "i", .inoutArg "j"] .empty)]] }
    callElim' with
  | .ok _ => IO.println "no error"
  | .error e => IO.println e.message

-- Stored type arguments with more entries than type parameters are ignored likewise.
/--
info: program Core;

type $__cety_0;
procedure r<a, b> (x : a)
spec {
  requires [r_requires_0]: x == x;
  requires [r_requires_1]: forall y : b :: y == y;
  } {
  
};
procedure Caller ()
{
  var tmp_arg_1 : int := 7;
  assert [callElimAssert_r_requires_0_2]: tmp_arg_1 == tmp_arg_1;
  assert [callElimAssert_r_requires_1_3]: forall y : $__cety_0 :: y == y;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim
  (rTyArgsProg rP (some [.forAll [] .int, .forAll [] .bool, .forAll [] .int]))))
#guard (callElim
  (rTyArgsProg rP (some [.forAll [] .int, .forAll [] .bool, .forAll [] .int]))).allExprs
  LExpr.fullyAnnotated

/--
info: program Core;

type $__cety_0;
type $__cety_1;
procedure r<a, b> (x : a)
spec {
  requires [r_requires_0]: x == x;
  requires [r_requires_1]: forall y : b :: y == y;
  } {
  
};
procedure Caller ()
{
  var tmp_arg_2 : $__cety_0 := int.neg(7);
  assert [callElimAssert_r_requires_0_3]: tmp_arg_2 == tmp_arg_2;
  assert [callElimAssert_r_requires_1_4]: forall y : $__cety_1 :: y == y;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim (unknownProg rP)))

-- The type checker rejects this program: the call needs `a` at both `int` and
-- `bool`. Call elimination still runs on it and keeps the result annotated.
/--
info: program Core;

type $__cety_0;
procedure idp<a> (x : a, out r : a)
spec {
  ensures [idp_ensures_0]: r == x;
  } {
  
};
procedure Caller ()
{
  var bb : bool;
  var tmp_arg_1 : $__cety_0 := 7;
  var tmp_bb_2 : $__cety_0 := bb;
  havoc bb;
  assume [$__callElimAssume_idp_ensures_0_3]: bb == tmp_arg_1;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim (conflictProg idpP)))
#guard (callElim (conflictProg idpP)).allExprs LExpr.fullyAnnotated

-- Two arguments that force different types on `a` (`7` is an `int`, `bb` is a `bool`) make the
-- matching fail, so the stored `a = int` is used unchecked.
/--
info: program Core;

procedure idp<a> (x : a, out r : a)
spec {
  ensures [idp_ensures_0]: r == x;
  } {
  
};
procedure Caller ()
{
  var bb : bool;
  var tmp_arg_0 : int := 7;
  var tmp_bb_1 : int := bb;
  havoc bb;
  assume [$__callElimAssume_idp_ensures_0_2]: bb == tmp_arg_0;
};
-/
#guard_msgs in
#eval match run { decls := [idpP, caller [] [] [declNondet "bb" .bool,
      .cmd (.call "idp" (some [.forAll [] .int]) [.inArg int7, .outArg "bb"] .empty)]] }
    callElim' with
  | .ok (_, p) => IO.println (toString p)
  | .error e => IO.println e.message

end CallInstanceTests

/-! ## The opaque types of a call avoid the program's type names

A program may declare a type named like the opaque type call elimination gives a callee type
parameter that the call does not determine. Here the axiom makes `$__cety_0` a singleton, under
which the precondition of `Q` holds, so the precondition must be checked at another type. The
checker rejects such a call, so the pass is run directly on the unchecked program. -/
section CallInstanceAvoidsTypeNames
open Core.CallFixtures Core.TestUtil

def capturedCallTypePgm : Program :=
  capturedTypeProg "$__cety_0" [singletonAll (tv "a")] []

/--
info: program Core;

type $__cety_1;
type $__cety_0;
axiom [one]: forall x : $__cety_0 :: forall y : $__cety_0 :: x == y;
procedure Q<a> ()
spec {
  requires [Q_requires_0]: forall x : a :: forall y : a :: x == y;
  } {
  
};
procedure P ()
{
  assert [callElimAssert_Q_requires_0_2]: forall x : $__cety_1 :: forall y : $__cety_1 :: x == y;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim capturedCallTypePgm).stripMetaData)

/--
info: Procedure 'P': the call to 'Q' does not determine one of its type
parameters
-/
#guard_msgs (whitespace := lax) in
#eval match Core.typeCheck .quiet capturedCallTypePgm with
  | .ok p => IO.println (toString (callElim p).stripMetaData)
  | .error e => IO.println e.message

/-- A type declared inside a procedure body is avoided as well. Here the assumption makes the
    local `$__cety_0` a singleton, so the precondition of `Q` must be checked at another type. -/
def capturedLocalCallTypePgm : Program :=
  capturedLocalTypeProg "$__cety_0" [singletonAll (tv "a")] []

-- The printed program cannot be shown with `#guard_msgs`: the local type declaration has no
-- printable form, so the printer reports a conversion error with a scope dump after the program.
-- Check the generated type directly: the assertion is at `$__cety_1`, not at the declared type.
#guard ((toString (callElim capturedLocalCallTypePgm).stripMetaData).splitOn
  "forall x : $__cety_1 ::").length > 1

/--
error: ❌ Type checking error.
Procedure 'P': the call to 'Q' does not determine one of its type
parameters
-/
#guard_msgs (whitespace := lax) in
#eval EIO.toIO (fun s => IO.userError s)
  (Core.verifyProgram capturedLocalCallTypePgm
    { Core.VerifyOptions.default with verbose := .quiet })

end CallInstanceAvoidsTypeNames

/-! ## Call elimination in CFG bodies

A call in a block is replaced in place by the commands that declare its temporaries, check the
callee's preconditions, havoc its results and assume its postconditions. The block's other
commands and its transfer are kept. -/
section CallElimCFG
open Lambda Core.CallFixtures
open Core.TestUtil (mkProc tv)

/-- The program `callElim'` makes of `t`, printed at width 96, or the error. -/
private def callElimShown (t : StrataDDM.SourcedProgram) : String :=
  match run (translate t) callElim' with
  | .ok (_, p) => (Std.format p.eraseTypes).pretty 96
  | .error e => s!"error: {e}"

/-- Two calls in one block between other commands, and a call in a block ending in a branch. -/
private def cfgCallsPgm :=
#strata
program Core;
procedure Inc(x : int, out y : int)
spec { requires [inc_pre]: int.ge(x, 0); ensures [inc_post]: y == int.add(x, 1); };
procedure P(a : int, out b : int, out c : int)
cfg entry {
  entry: { b := a; call Inc(b, out c); call Inc(c, out b); assert [b_big]: int.gt(b, a);
    goto check; }
  check: { call Inc(b, out c); branch (int.gt(c, b)) goto up else goto down; }
  up: { return; }
  down: { return; }
};
#end

/--
info: program Core;

procedure Inc (x : int, out y : int)
spec {
  requires [inc_pre]: int.ge(x, 0);
  ensures [inc_post]: y == int.add(x, 1);
  } ;
procedure P (a : int, out b : int, out c : int)
cfg entry {
  entry: {
    b := a;
    var tmp_arg_0 : int := b;
    var tmp_c_1 : int := c;
    assert [callElimAssert_inc_pre_2]: int.ge(tmp_arg_0, 0);
    havoc c;
    assume [callElimPost_inc_post_3]: c == int.add(tmp_arg_0, 1);
    var tmp_arg_4 : int := c;
    var tmp_b_5 : int := b;
    assert [callElimAssert_inc_pre_6]: int.ge(tmp_arg_4, 0);
    havoc b;
    assume [callElimPost_inc_post_7]: b == int.add(tmp_arg_4, 1);
    assert [b_big]: int.gt(b, a);
    goto check;
  }
  check: {
    var tmp_arg_8 : int := b;
    var tmp_c_9 : int := c;
    assert [callElimAssert_inc_pre_10]: int.ge(tmp_arg_8, 0);
    havoc c;
    assume [callElimPost_inc_post_11]: c == int.add(tmp_arg_8, 1);
    branch (int.gt(c, b)) goto up else goto down;
  }
  up: {
    return;
  }
  down: {
    return;
  }
};
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (callElimShown cfgCallsPgm)

/-- `p<a, b>(x : a, out y : b)`: `b` is fixed only by the type of the variable passed for `y`. -/
private def outTyP : Decl := mkProc "p" ["a", "b"] [("x", tv "a")] [("y", tv "b")]

/-- A CFG procedure calling `p(n, out r)` with `n : int` and `r : bool`, then branching on `r`. -/
private def cfgOutTyProg : Program :=
  let blk : Imperative.DetBlock String Command Expression :=
    { cmds := [.cmd (.init "r" (.forAll [] .bool) (.det (.boolConst Core.coreLoc true)) .empty),
               .call "p" none [.inArg (v "n" .int), .outArg "r"] .empty],
      transfer := .condGoto (v "r" .bool) "up" "down" .empty }
  let fin : Imperative.DetBlock String Command Expression :=
    { cmds := [], transfer := .finish .empty }
  { decls := [outTyP,
    .proc { header := { name := ⟨"Caller", ()⟩, typeArgs := [], inputs := [("n", .int)],
                        outputs := [] },
            spec := { preconditions := [], postconditions := [] },
            body := .cfg { entry := "entry",
                           blocks := [("entry", blk), ("up", fin), ("down", fin)] } false } .empty]
                           }

/--
info: program Core;

procedure p<a, b> (x : a, out y : b)
{
  
};
procedure Caller (n : int)
cfg entry {
  entry: {
    var r : bool := true;
    var tmp_arg_0 : int := n;
    var tmp_r_1 : bool := r;
    havoc r;
    assume [$__callElimHavoc_call_2]: true;
    branch (r) goto up else goto down;
  }
  up: {
    return;
  }
  down: {
    return;
  }
};
-/
#guard_msgs in
#eval IO.println (toString (callElim cfgOutTyProg))
#guard (callElim cfgOutTyProg).allExprs LExpr.fullyAnnotated

end CallElimCFG

/-! ## Call-elimination pipeline phase obligation tests -/
section CallElimPhaseTests
open Strata.SMT
open Core.SMT (Result)

private def satResult : Result := .sat []
private def unknownResult : Result := .unknown (some [])

/-- Obligation with call-elimination labels in path conditions. -/
private def callElimObligation : Imperative.ProofObligation Core.Expression :=
  { label := "test_callElim", property := .assert,
    assumptions := [[.assumption "$__callElimAssume_post" (.true testLoc)]],
    obligation := .true testLoc, metadata := {} }

/-- Obligation with no abstraction labels — models are sound. -/
private def cleanObligation : Imperative.ProofObligation Core.Expression :=
  { label := "test_clean", property := .assert,
    assumptions := [[.assumption "precond_x_positive" (.true testLoc)]],
    obligation := .true testLoc, metadata := {} }

-- callElimPipelinePhase: rejects sat when obligation has call-elim labels
#guard (satResult.adjustForPhases [callElimPipelinePhase.phase] callElimObligation).1 == unknownResult

-- callElimPipelinePhase: preserves sat when obligation has no call-elim labels
#guard (satResult.adjustForPhases [callElimPipelinePhase.phase] cleanObligation).1 == satResult

end CallElimPhaseTests
end
