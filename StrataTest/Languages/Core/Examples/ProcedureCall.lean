/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core.CallGraph

---------------------------------------------------------------------
namespace Strata

def globalCounterPgm : Program :=
#strata
program Core;

inline function Add(x : int, y : int) : int { x + y }

procedure Inc(inout counter : int, a : int, out ret : int)
spec {
  requires [counter_ge_zero]: (counter >= 0);
  requires [a_positive]:      (a > 0);
  ensures  [new_g_value]:     (counter == old counter + a);
  ensures  [old_g_property]:  (ret - a == old counter);
}
{
  counter := Add(counter, a);
  ret := counter;
};

procedure P(inout counter : int, out b : int)
spec {
  requires [counter_ge_zero]: (counter >= 0);
  ensures [return_value_lemma]: (b == old counter + 16);
}
{
  call Inc(inout counter, 8, out b);
  call Inc(inout counter, 8, out b);
};

procedure Q1() {
  assert true;
};

procedure Q2() {
  call Q1();
};
#end

/--
info: CallGraph(callees: [("Inc", []),
("P", [("Inc", 2)]),
("Q1", []),
("Q2", [("Q1", 1)])],
         callers: [("Inc", [("P", 2)]),
("P", []),
("Q1", [("Q2", 1)]),
("Q2", [])])
-/
#guard_msgs in
#eval let (program, _) := Core.getProgram globalCounterPgm
      Core.Program.toProcedureCG program

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: new_g_value
Property: assert
Assumptions:
counter_ge_zero: counter@1 >= 0
a_positive: a@1 > 0
Obligation:
true

Label: old_g_property
Property: assert
Assumptions:
counter_ge_zero: counter@1 >= 0
a_positive: a@1 > 0
Obligation:
counter@1 + a@1 - a@1 == counter@1

Label: callElimAssert_counter_ge_zero_14
Property: assert
Assumptions:
counter_ge_zero: counter@3 >= 0
Obligation:
counter@3 >= 0

Label: callElimAssert_a_positive_15
Property: assert
Assumptions:
counter_ge_zero: counter@3 >= 0
Obligation:
true

Label: callElimAssert_counter_ge_zero_5
Property: assert
Assumptions:
counter_ge_zero: counter@3 >= 0
callElimAssume_new_g_value_16: counter@5 == counter@3 + 8
callElimAssume_old_g_property_17: b@2 - 8 == counter@3
Obligation:
counter@5 >= 0

Label: callElimAssert_a_positive_6
Property: assert
Assumptions:
counter_ge_zero: counter@3 >= 0
callElimAssume_new_g_value_16: counter@5 == counter@3 + 8
callElimAssume_old_g_property_17: b@2 - 8 == counter@3
Obligation:
true

Label: return_value_lemma
Property: assert
Assumptions:
counter_ge_zero: counter@3 >= 0
callElimAssume_new_g_value_16: counter@5 == counter@3 + 8
callElimAssume_old_g_property_17: b@2 - 8 == counter@3
callElimAssume_new_g_value_7: counter@6 == counter@5 + 8
callElimAssume_old_g_property_8: b@3 - 8 == counter@5
Obligation:
b@3 == counter@3 + 16

Label: assert_0
Property: assert
Obligation:
true

---
info:
Obligation: new_g_value
Property: assert
Result: ✅ pass

Obligation: old_g_property
Property: assert
Result: ✅ pass

Obligation: callElimAssert_counter_ge_zero_14
Property: assert
Result: ✅ pass

Obligation: callElimAssert_a_positive_15
Property: assert
Result: ✅ pass

Obligation: callElimAssert_counter_ge_zero_5
Property: assert
Result: ✅ pass

Obligation: callElimAssert_a_positive_6
Property: assert
Result: ✅ pass

Obligation: return_value_lemma
Property: assert
Result: ✅ pass

Obligation: assert_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify globalCounterPgm

---------------------------------------------------------------------

/-
-- DDM AST
#eval globalCounterEnv.commands

-- Translation from DDM AST to Strata Core AST
#eval TransM.run (translateProgram (globalCounterEnv.commands))
-/

---------------------------------------------------------------------
