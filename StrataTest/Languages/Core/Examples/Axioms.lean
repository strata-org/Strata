/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.CallGraph
import StrataDDM.Integration.Lean.HashCommands

meta section
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
axiom [f1]: (forall y : int :: int.gt(f(y), y));

procedure P(out ret : int)
  spec {
    ensures [use_f1]: int.gt(ret, 7);
  }
{
  assert [use_a1_a2]: int.gt(x, y);
  ret := f(int.add(x, y));
};

procedure P2()
{
  assert [use_a1_again]: y == 2;
  assert [use_a2_again]: int.gt(f(y), y);
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: use_a1_a2
Property: assert
Assumptions:
a1: x == 5
a2: y == 2
f1: forall y : int :: int.gt(f(y), y)
Obligation:
int.gt(x, y)

Label: use_f1
Property: assert
Assumptions:
a1: x == 5
a2: y == 2
f1: forall y : int :: int.gt(f(y), y)
Obligation:
int.gt(f(int.add(x, y)), 7)

Label: use_a1_again
Property: assert
Assumptions:
a1: x == 5
a2: y == 2
f1: forall y : int :: int.gt(f(y), y)
Obligation:
y == 2

Label: use_a2_again
Property: assert
Assumptions:
a1: x == 5
a2: y == 2
f1: forall y : int :: int.gt(f(y), y)
Obligation:
int.gt(f(y), y)

---
info:
Obligation: use_a1_a2
Property: assert
Result: ✅ pass

Obligation: use_f1
Property: assert
Result: ✅ pass

Obligation: use_a1_again
Property: assert
Result: ✅ pass

Obligation: use_a2_again
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify axiomPgm1

---------------------------------------------------------------------

def axiomPgm2 :=
#strata
program Core;

function f(x : int) : int;
function g(x : int) : int;

axiom [f_g_ax]: (forall x : int :: { f(x) } f(x) == int.add(g(x), 1));
// NOTE the trigger `f(x)` in `g_ax` below, which causes the
// dependency analysis to include this axiom in all goals involving `f(x)`.
axiom [g_ax]:   (forall x : int :: { g(x), f(x) } g(x) == int.mul(x, 2));

procedure main (x : int) {

assert [axiomPgm2_main_assert]: (int.ge(x, 0) ==> int.gt(f(x), x));
};
#end

/--
info: []
-/
#guard_msgs in
#eval let (program, _) := Core.getProgram axiomPgm2
      let cache := Core.IrrelevantAxioms.Cache.build program
      Std.format (Core.IrrelevantAxioms.getIrrelevantAxioms program cache ["f"])

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: axiomPgm2_main_assert
Property: assert
Assumptions:
f_g_ax: forall x : int ::  { f(x) }
  f(x) == int.add(g(x), 1)
g_ax: forall x : int ::  { g(x), f(x) }
  g(x) == int.mul(x, 2)
Obligation:
int.ge(x@1, 0) ==> int.gt(f(x@1), x@1)

---
info:
Obligation: axiomPgm2_main_assert
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify axiomPgm2

end Strata
end
---------------------------------------------------------------------
