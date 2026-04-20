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

var counter : int;

inline function Add(x : int, y : int) : int { x + y }

procedure Inc(a : int) returns (ret : int)
spec {
  modifies counter;
  requires [counter_ge_zero]: (counter >= 0);
  requires [a_positive]:      (a > 0);
  ensures  [new_g_value]:     (counter == old counter + a);
  ensures  [old_g_property]:  (ret - a == old counter);
}
{
  counter := Add(counter, a);
  ret := counter;
};

procedure P() returns (b : int)
spec {
  modifies counter;
  requires [counter_ge_zero]: (counter >= 0);
  ensures [return_value_lemma]: (b == old counter + 16);
}
{
  call b := Inc(8);
  call b := Inc(8);
};

procedure Q1() returns () {
  assert true;
};

procedure Q2() returns () {
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
counter_ge_zero: $__counter1 >= 0
a_positive: $__a2 > 0
Obligation:
true

Label: old_g_property
Property: assert
Assumptions:
counter_ge_zero: $__counter1 >= 0
a_positive: $__a2 > 0
Obligation:
$__counter1 + $__a2 - $__a2 == $__counter1

Label: callElimAssert_counter_ge_zero_10
Property: assert
Assumptions:
counter_ge_zero: $__counter4 >= 0
Obligation:
$__counter4 >= 0

Label: callElimAssert_a_positive_11
Property: assert
Assumptions:
counter_ge_zero: $__counter4 >= 0
Obligation:
true

Label: callElimAssert_counter_ge_zero_3
Property: assert
Assumptions:
counter_ge_zero: $__counter4 >= 0
callElimAssume_new_g_value_12: $__counter7 == $__counter4 + 8
callElimAssume_old_g_property_13: $__b6 - 8 == $__counter4
Obligation:
$__counter7 >= 0

Label: callElimAssert_a_positive_4
Property: assert
Assumptions:
counter_ge_zero: $__counter4 >= 0
callElimAssume_new_g_value_12: $__counter7 == $__counter4 + 8
callElimAssume_old_g_property_13: $__b6 - 8 == $__counter4
Obligation:
true

Label: return_value_lemma
Property: assert
Assumptions:
counter_ge_zero: $__counter4 >= 0
callElimAssume_new_g_value_12: $__counter7 == $__counter4 + 8
callElimAssume_old_g_property_13: $__b6 - 8 == $__counter4
callElimAssume_new_g_value_5: $__counter9 == $__counter7 + 8
callElimAssume_old_g_property_6: $__b8 - 8 == $__counter7
Obligation:
$__b8 == $__counter4 + 16

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

Obligation: callElimAssert_counter_ge_zero_10
Property: assert
Result: ✅ pass

Obligation: callElimAssert_a_positive_11
Property: assert
Result: ✅ pass

Obligation: callElimAssert_counter_ge_zero_3
Property: assert
Result: ✅ pass

Obligation: callElimAssert_a_positive_4
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
