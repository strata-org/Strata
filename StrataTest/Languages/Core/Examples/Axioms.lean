/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Core.Verifier
import Strata.Languages.Core.CallGraph

---------------------------------------------------------------------
namespace Strata

def axiomPgm1 :=
#strata
program Core;

const x : int;
axiom [a1]: x == 5;

const y : int;
axiom [a2]: y == 2;

function f(x: int): int;
axiom [f1]: (forall y : int :: f(y) > y);

procedure P() returns (ret : int)
  spec {
    ensures [use_f1]: ret > 7;
  }
{
  assert [use_a1_a2]: x > y;
  ret := f(x + y);
};

procedure P2() returns ()
{
  assert [use_a1_again]: y == 2;
  assert [use_a2_again]: f(y) > y;
};

#end

/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval verify "cvc5" axiomPgm1

---------------------------------------------------------------------

def axiomPgm2 :=
#strata
program Core;

function f(x : int) : int;
function g(x : int) : int;

axiom [f_g_ax]: (forall x : int :: { f(x) } f(x) == g(x) + 1);
// NOTE the trigger `f(x)` in `g_ax` below, which causes the
// dependency analysis to include this axiom in all goals involving `f(x)`.
axiom [g_ax]:   (forall x : int :: { g(x), f(x) } g(x) == x * 2);

procedure main (x : int) returns () {

assert [axiomPgm2_main_assert]: (x >= 0 ==> f(x) > x);
};
#end

/-- info: [] -/
#guard_msgs in
#eval let (program, _) := Core.getProgram axiomPgm2
      Std.format (Core.Program.getIrrelevantAxioms program ["f"])

/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval verify "z3" axiomPgm2

---------------------------------------------------------------------
