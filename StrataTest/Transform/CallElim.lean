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
  assume [callElimAssume_f_ensures_1_6]: (b == tmp_arg_2);
  assume [callElimAssume_f_ensures_2_7]: (b == j);
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
  assume [callElimAssume_f_ensures_1_9]: b == (tmp_arg_2 && old_j_7);
  assume [callElimAssume_f_ensures_2_10]: b == old_j_7;
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
  assume [callElimAssume_f_ensures_1_9]: b == (tmp_arg_2 && old_j_7);
  assume [callElimAssume_f_ensures_2_10]: b == old_j_7;
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
  assume [callElimAssume_f_ensures_2_6]: (b == tmp_arg_2);
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
private def pairP : Decl :=
  mkProc "pair" ["a", "b"] [("x", tv "a"), ("y", tv "b")] [("r", tv "a")]
    (post := [eqE (v "r" (tv "a")) (v "x" (tv "a"))])
/-- `q<a>()` requires `forall y : a :: y == y`. -/
private def qP : Decl := mkProc "q" ["a"] [] [] (pre := [reflAll (tv "a")])
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
  assume [callElimAssume_idp_ensures_0_2]: ai == tmp_arg_0;
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
  assume [callElimAssume_swap_ensures_0_5]: i == old_j_4;
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
  var w : (a);
  var tmp_arg_0 : a := z;
  var tmp_w_1 : a := w;
  havoc w;
  assume [callElimAssume_idp_ensures_0_2]: w == tmp_arg_0;
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
  var w : (b);
  var tmp_arg_0 : b := y;
  var tmp_arg_1 : a := x;
  var tmp_w_2 : b := w;
  havoc w;
  assume [callElimAssume_pair_ensures_0_3]: w == tmp_arg_0;
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
  requires [q_requires_0]: forall y : (a) :: y == y;
  } {
  
};
procedure Caller ()
{
  assert [callElimAssert_q_requires_0_1]: forall y : $__cety_0 :: y == y;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim (qProg qP)))
#guard (callElim (qProg qP)).allExprs LExpr.fullyAnnotated

/--
info: program Core;

type $__cety_0;
procedure r<a, b> (x : a)
spec {
  requires [r_requires_0]: x == x;
  requires [r_requires_1]: forall y : (b) :: y == y;
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

/--
info: program Core;

type $__cety_0;
type $__cety_1;
procedure r<a, b> (x : a)
spec {
  requires [r_requires_0]: x == x;
  requires [r_requires_1]: forall y : (b) :: y == y;
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
  assume [callElimAssume_idp_ensures_0_3]: bb == tmp_arg_1;
};
-/
#guard_msgs in
#eval IO.println (toString (callElim (conflictProg idpP)))
#guard (callElim (conflictProg idpP)).allExprs LExpr.fullyAnnotated

end CallInstanceTests

/-! ## The opaque types of a call avoid the program's type names

A program may declare a type named like the opaque type call elimination gives a callee type
parameter that the call does not determine. Here the axiom makes `$__cety_0` a singleton, under
which the precondition of `Q` holds, so the precondition must be checked at another type. -/
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
  requires [Q_requires_0]: forall x : (a) :: forall y : (a) :: x == y;
  } {
  
};
procedure P ()
{
  assert [callElimAssert_Q_requires_0_2]: forall x : $__cety_1 :: forall y : $__cety_1 :: x == y;
};
-/
#guard_msgs in
#eval match Core.typeCheck .quiet capturedCallTypePgm with
  | .ok p => IO.println (toString (callElim p).stripMetaData)
  | .error e => IO.println e.message

/--
info:
Obligation: callElimAssert_Q_requires_0_2
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval EIO.toIO (fun s => IO.userError s)
  (Core.verifyProgram capturedCallTypePgm { Core.VerifyOptions.default with verbose := .quiet })


/-- A type declared inside a procedure body is avoided as well. Here the assumption makes the
    local `$__cety_0` a singleton, so the precondition of `Q` must be checked at another type. -/
def capturedLocalCallTypePgm : Program :=
  capturedLocalTypeProg "$__cety_0" [singletonAll (tv "a")] []

/--
info:
Obligation: callElimAssert_Q_requires_0_2
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
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
  } {

};
procedure P (a : int, out b : int, out c : int)
cfg entry {
  entry: {
    b := a;
    var tmp_arg_0 : int := b;
    var tmp_c_1 : int := c;
    assert [callElimAssert_inc_pre_2]: int.ge(tmp_arg_0, 0);
    havoc c;
    assume [callElimAssume_inc_post_3]: c == int.add(tmp_arg_0, 1);
    var tmp_arg_4 : int := c;
    var tmp_b_5 : int := b;
    assert [callElimAssert_inc_pre_6]: int.ge(tmp_arg_4, 0);
    havoc b;
    assume [callElimAssume_inc_post_7]: b == int.add(tmp_arg_4, 1);
    assert [b_big]: int.gt(b, a);
    goto check;
  }
  check: {
    var tmp_arg_8 : int := b;
    var tmp_c_9 : int := c;
    assert [callElimAssert_inc_pre_10]: int.ge(tmp_arg_8, 0);
    havoc c;
    assume [callElimAssume_inc_post_11]: c == int.add(tmp_arg_8, 1);
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
               .call "p" [.inArg (v "n" .int), .outArg "r"] .empty],
      transfer := .condGoto (v "r" .bool) "up" "down" .empty }
  let fin : Imperative.DetBlock String Command Expression :=
    { cmds := [], transfer := .finish .empty }
  { decls := [outTyP,
    .proc { header := { name := ⟨"Caller", ()⟩, typeArgs := [], inputs := [("n", .int)],
                        outputs := [] },
            spec := { preconditions := [], postconditions := [] },
            body := .cfg { entry := "entry",
                           blocks := [("entry", blk), ("up", fin), ("down", fin)] } } .empty] }

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
    assumptions := [[.assumption "callElimAssume_post" (.true testLoc)]],
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
