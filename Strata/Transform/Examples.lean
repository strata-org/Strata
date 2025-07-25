/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
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
  havoc b;
  havoc j;
  assert i == !k;
  assume b == k;
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
  var old_k_0 : bool := k;
  var old_j_1 : bool := j;
  havoc b;
  havoc j;
  assert i == !k;
  assume b == (old_k_0 && old_j_1);
  assume b == old_j_1;
};
#end

def translate (t : Environment) : Program := (TransM.run (translateProgram t.commands)).fst

def env := (Lambda.TEnv.default.addFactoryFunctions Boogie.Factory)

def translateWF (t : Environment) : WF.WFProgram :=
  let p := translate t
  match H: Program.typeCheck env p with
  | .error e => panic! "Well, " ++ Std.format e |> toString
  | .ok res => { self := p, prop := by exact WF.Program.typeCheckWF H }

def runTest (test : Environment) (ans : Environment) : Bool :=
  toString (callElim (translateWF test)) == toString (translateWF ans).self

#guard runTest test1 test1Ans
#guard runTest test2 test2Ans

-- #eval callElim tests[0].fst
-- #eval tests[0].snd.self

end test
