/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.CallElim
import Strata.Languages.Boogie.ProgramType
import Strata.Languages.Boogie.ProgramWF
import Strata.DL.Lambda.IntBoolFactory
open Boogie
open CallElim
open Strata

section test

def test1 : Environment :=
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

def test1Ans : Environment :=
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
  assert i == !tmp_arg_0;
  havoc b;
  havoc j;
  assume b == tmp_arg_0;
  assume b == j;
};
#end

def test2 : Environment :=
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

def test2Ans : Environment :=
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
  assert i == !tmp_arg_0;
  havoc b;
  havoc j;
  assume b == (old_k_3 && old_j_4);
  assume b == old_j_4;
};
#end

def test3 : Environment :=
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

def test3Ans : Environment :=
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
  assert i == !tmp_arg_0;
  havoc b;
  havoc j;
  assume b == (old_k_3 && old_j_4);
  assume b == old_j_4;
};
#end

def translate (t : Environment) : Program := (TransM.run (translateProgram t.commands)).fst

def env := (Lambda.TEnv.default.addFactoryFunctions Boogie.Factory)

def translateWF (t : Environment) : WF.WFProgram :=
  let p := translate t
  match H: Program.typeCheck env p with
  | .error e => panic! "Well, " ++ Std.format e |> toString
  | .ok res => { self := p, prop := by exact WF.Program.typeCheckWF H }

def tests : List (Program × Program) := [
  (test1, test1Ans),
  (test2, test2Ans),
  (test3, test3Ans),
].map (Prod.map translate translate)

/--
info: true
-/
#guard_msgs in
#eval tests.all (λ (test, ans) ↦ (toString (callElim test)) == (toString ans))

-- #eval callElim tests[1].fst
-- #eval tests[1].snd

end test
