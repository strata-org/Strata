/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format
import Strata.Languages.Boogie.Boogie
import Strata.Languages.Boogie.DDMTransform.Translate
import Strata.Languages.Boogie.ProgramType
import Strata.Languages.Boogie.ProgramWF
import Strata.Languages.Boogie.StatementSemantics
import Strata.Transform.BoogieTransform
import Strata.Transform.CallElim


open Boogie
open Boogie.Transform
open CallElim
open Strata

/-! ## Call Elimination Examples -/
section CallElimExamples

def CallElimTest1 :=
#strata
program Boogie;
var i : bool;
var j : bool;
var k : bool;
procedure f(x : bool) returns (y : bool)
spec {
  requires (i == !x);
  ensures (y == x);
  ensures (y == j);
  modifies j;
};
procedure h() returns () spec {
  modifies j;
} {
  var b : bool;
  call b := f(k);
};
#end

def CallElimTest1Ans :=
#strata
program Boogie;
var i : bool;
var j : bool;
var k : bool;
procedure f(x : bool) returns (y : bool)
spec {
  requires (i == !x);
  ensures (y == x);
  ensures (y == j);
  modifies j;
};
procedure h() returns () spec {
  modifies j;
} {
  var b : bool;
  var tmp_arg_0 : bool := k;
  var tmp_b_1 : bool := b;
  assert [assert_0]: i == !tmp_arg_0;
  havoc b;
  havoc j;
  assume [assume_0]: b == tmp_arg_0;
  assume [assume_1]: b == j;
};
#end

def CallElimTest2 :=
#strata
program Boogie;
var i : bool;
var j : bool;
var k : bool;
var l : bool;
procedure f(x : bool, y : bool) returns (z : bool)
spec {
  requires (i == !x);
  ensures (z == old(k && j));
  ensures (z == old(j));
  modifies j;
};
procedure h() returns () spec {
  modifies j;
} {
  var b : bool;
  call b := f(k, l);
};
#end

def CallElimTest2Ans :=
#strata
program Boogie;
var i : bool;
var j : bool;
var k : bool;
var l : bool;
procedure f(x : bool, y : bool) returns (z : bool)
spec {
  requires (i == !x);
  ensures (z == old(k && j));
  ensures (z == old(j));
  modifies j;
};
procedure h() returns () spec {
  modifies j;
} {
  var b : bool;
  var tmp_arg_0 : bool := k;
  var tmp_arg_1 : bool := l;
  var tmp_b_2 : bool := b;
  var old_k_3 : bool := k;
  var old_j_4 : bool := j;
  assert [assert_0]: i == !tmp_arg_0;
  havoc b;
  havoc j;
  assume [assume_0]: b == (old_k_3 && old_j_4);
  assume [assume_1]: b == old_j_4;
};
#end

def CallElimTest3 :=
#strata
program Boogie;
var i : bool;
var j : bool;
var k : bool;
var l : bool;
procedure f(x : bool, y : bool) returns (z : bool)
spec {
  requires (i == !x);
  ensures (z == old(k && j));
  ensures (z == old(j));
  modifies j;
};
procedure h() returns () spec {
  modifies j;
} {
  var b : bool;
  call b := f(k && i || j, l);
};
#end

def CallElimTest3Ans :=
#strata
program Boogie;
var i : bool;
var j : bool;
var k : bool;
var l : bool;
procedure f(x : bool, y : bool) returns (z : bool)
spec {
  requires (i == !x);
  ensures (z == old(k && j));
  ensures (z == old(j));
  modifies j;
};
procedure h() returns () spec {
  modifies j;
} {
  var b : bool;
  var tmp_arg_0 : bool := k && i || j;
  var tmp_arg_1 : bool := l;
  var tmp_b_2 : bool := b;
  var old_k_3 : bool := k;
  var old_j_4 : bool := j;
  assert [assert_0]: i == !tmp_arg_0;
  havoc b;
  havoc j;
  assume [assume_0]: b == (old_k_3 && old_j_4);
  assume [assume_1]: b == old_j_4;
};
#end

def translate (t : Strata.Program) : Boogie.Program := (TransM.run Inhabited.default (translateProgram t)).fst

def env := (Lambda.LContext.default.addFactoryFunctions Boogie.Factory)

def translateWF (t : Strata.Program) : WF.WFProgram :=
  let p := translate t
  match H: Program.typeCheck env Lambda.TEnv.default p with
  | .error e => panic! "Well, " ++ Std.format e |> toString
  | .ok res => { self := p, prop := by exact WF.Program.typeCheckWF H }

def tests : List (Boogie.Program × Boogie.Program) := [
  (CallElimTest1, CallElimTest1Ans),
  (CallElimTest2, CallElimTest2Ans),
  (CallElimTest3, CallElimTest3Ans),
].map (Prod.map translate translate)

def callElim (p : Boogie.Program)
  : Boogie.Program :=
  match (run p callElim') with
  | .ok res => res
  | .error e => panic! e

/--
info: true
-/
#guard_msgs in
#eval tests.all (λ (test, ans) ↦ (toString (callElim test).eraseTypes) == (toString ans.eraseTypes))

--#eval callElim tests[1].fst
--#eval tests[1].snd

end CallElimExamples
