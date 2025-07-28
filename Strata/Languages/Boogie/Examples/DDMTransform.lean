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

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def msEnv : Environment :=
#strata
program Boogie;
// Running example from Mutual Summaries paper
//
// int g;
// void Foo1(int x) {
//     if (x < 100) {
//         g := g + x;
//         Foo1(x + 1);
//     }
// }
//
// void Foo2(int x) {
//     if (x < 100) {
//         g := g + 2*x;
//         Foo2(x + 1);
//     }
// }
//
//

// Template: MS(inputs1, inputs2, globals1, globals2, globals1', globals2', returns, returns')
function MS(x1: int, x2: int, g1: int, g2: int, g1': int, g2': int, r1: int, r2: int) : bool
{
    ((x1 == x2) && (x1 >= 0) && (g1 <= g2)) ==> g1' <= g2'
}

// Template: <f>.token(inputs, globals, globals', returns);
function Foo1_token(x1: int, g1: int, g1': int, r1: int) : bool;
function Foo2_token(x2: int, g2: int, g2': int, r2: int) : bool;

var g: int;

procedure Foo1(x1: int) returns (r1: int)
  spec {

    modifies g;
    // Template: <f>.token(inputs, old(globals), globals, returns);
    free ensures Foo1_token(x1,old(g),g,r1);
  };

procedure Foo2(x2: int) returns (r2: int)
  spec {
    modifies g;
    free ensures Foo2_token(x2,old(g),g,r2);
  };

procedure MS_check (x1: int, x2: int) returns (r1: int, r2: int)
  spec {

  // mutual summary axiom
  requires (forall x1: int, x2: int, g1: int, g2: int, g1': int, g2': int, r1: int, r2: int ::
    {Foo1_token(x1,g1,g1',r1), Foo2_token(x2,g2,g2',r2)}
    Foo1_token(x1, g1, g1', r1) && Foo2_token(x2, g2, g2', r2) ==>
      MS(x1, x2, g1, g2, g1', g2', r1, r2));

  modifies g;
  }
{
  var g1: int; var g1': int; var g2: int; var g2': int;

  g1 := g;

  // inline Foo1:
  if (x1 < 100) {
    g := g + x1;
    call r1 := Foo1(x1 + 1);
  }
  g1' := g;

  havoc g;
  g2 := g;

  // inline Foo2:
  if (x2 < 100) {
    g := g + 2 * x2;
    call r2 := Foo2(x2 + 1);
  }
  g2' := g;

  // mutual summary assertion
  assert MS(x1, x2, g1, g2, g1', g2', r1, r2);
};
#end

-- #eval IO.println test.format.render
-- #eval test.commands
-- #eval TransM.run (translateProgram (test.commands)) |>.snd |>.isEmpty


end Strata
---------------------------------------------------------------------
