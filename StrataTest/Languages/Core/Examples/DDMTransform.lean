/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def msPgm : Program :=
#strata
program Core;
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

procedure Foo1(x1: int, g: int, out r1: int, out g': int)
  spec {
    // Template: <f>.token(inputs, old globals, globals, returns);
    free ensures Foo1_token(x1,g,g',r1);
  };

procedure Foo2(x2: int, g: int, out r2: int, out g': int)
  spec {
    free ensures Foo2_token(x2,g,g',r2);
  };

procedure MS_check (x1: int, x2: int, g: int, out r1: int, out r2: int, out g': int)
  spec {

  // mutual summary axiom
  requires (forall x1: int, x2: int, g1: int, g2: int, g1': int, g2': int, r1: int, r2: int ::
    {Foo1_token(x1,g1,g1',r1), Foo2_token(x2,g2,g2',r2)}
    Foo1_token(x1, g1, g1', r1) && Foo2_token(x2, g2, g2', r2) ==>
      MS(x1, x2, g1, g2, g1', g2', r1, r2));

  }
{
  var g1: int; var g1': int; var g2: int; var g2': int;
  var g_cur: int;

  g_cur := g;
  g1 := g_cur;

  // inline Foo1:
  if (x1 < 100) {
    g_cur := g_cur + x1;
    call Foo1(x1 + 1, g_cur, out r1, out g_cur);
  }
  g1' := g_cur;

  havoc g_cur;
  g2 := g_cur;

  // inline Foo2:
  if (x2 < 100) {
    g_cur := g_cur + 2 * x2;
    call Foo2(x2 + 1, g_cur, out r2, out g_cur);
  }
  g2' := g_cur;

  g' := g_cur;

  // mutual summary assertion
  assert MS(x1, x2, g1, g2, g1', g2', r1, r2);
};
#end

-- #eval IO.println test
-- #eval test.commands
-- #eval TransM.run (translateProgram (test.commands)) |>.snd |>.isEmpty


end Strata
---------------------------------------------------------------------
