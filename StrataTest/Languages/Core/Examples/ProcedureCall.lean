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
  ensures  [new_g_value]:     (counter == old(counter) + a);
  ensures  [old_g_property]:  (ret - a == old(counter));
}
{
  counter := Add(counter, a);
  ret := counter;
};

procedure P() returns (b : int)
spec {
  modifies counter;
  requires [counter_ge_zero]: (counter >= 0);
  ensures [return_value_lemma]: (b == old(counter) + 16);
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
info: { callees := Std.HashMap.ofList [("Inc", Std.HashMap.ofList []),
              ("Q2", Std.HashMap.ofList [("Q1", 1)]),
              ("P", Std.HashMap.ofList [("Inc", 2)]),
              ("Q1", Std.HashMap.ofList [])],
  callers := Std.HashMap.ofList [("Inc", Std.HashMap.ofList [("P", 2)]), ("Q1", Std.HashMap.ofList [("Q2", 1)])] }
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
(counter_ge_zero, (~Int.Ge $__counter0 #0))
(a_positive, (~Int.Gt $__a1 #0))

Proof Obligation:
#true

Label: old_g_property
Property: assert
Assumptions:
(counter_ge_zero, (~Int.Ge $__counter0 #0))
(a_positive, (~Int.Gt $__a1 #0))

Proof Obligation:
((~Int.Sub (~Int.Add $__counter0 $__a1) $__a1) == $__counter0)

Label: (Origin_Inc_Requires)counter_ge_zero
Property: assert
Assumptions:
(counter_ge_zero, (~Int.Ge $__counter3 #0))

Proof Obligation:
(~Int.Ge $__counter3 #0)

Label: (Origin_Inc_Requires)a_positive
Property: assert
Assumptions:
(counter_ge_zero, (~Int.Ge $__counter3 #0))

Proof Obligation:
#true

Label: (Origin_Inc_Requires)counter_ge_zero
Property: assert
Assumptions:
(counter_ge_zero, (~Int.Ge $__counter3 #0))
((Origin_Inc_Ensures)new_g_value, ($__counter6 == (~Int.Add
  $__counter3
  #8))) ((Origin_Inc_Ensures)old_g_property, ((~Int.Sub $__b5 #8) == $__counter3))

Proof Obligation:
(~Int.Ge $__counter6 #0)

Label: (Origin_Inc_Requires)a_positive
Property: assert
Assumptions:
(counter_ge_zero, (~Int.Ge $__counter3 #0))
((Origin_Inc_Ensures)new_g_value, ($__counter6 == (~Int.Add
  $__counter3
  #8))) ((Origin_Inc_Ensures)old_g_property, ((~Int.Sub $__b5 #8) == $__counter3))

Proof Obligation:
#true

Label: return_value_lemma
Property: assert
Assumptions:
(counter_ge_zero, (~Int.Ge $__counter3 #0))
((Origin_Inc_Ensures)new_g_value, ($__counter6 == (~Int.Add
  $__counter3
  #8))) ((Origin_Inc_Ensures)old_g_property, ((~Int.Sub
  $__b5
  #8) == $__counter3)) ((Origin_Inc_Ensures)new_g_value, ($__counter8 == (~Int.Add
  $__counter6
  #8))) ((Origin_Inc_Ensures)old_g_property, ((~Int.Sub $__b7 #8) == $__counter6))

Proof Obligation:
($__b7 == (~Int.Add $__counter3 #16))

Label: assert_0
Property: assert
Assumptions:


Proof Obligation:
#true

---
info:
Obligation: new_g_value
Property: assert
Result: ✅ pass

Obligation: old_g_property
Property: assert
Result: ✅ pass

Obligation: (Origin_Inc_Requires)counter_ge_zero
Property: assert
Result: ✅ pass

Obligation: (Origin_Inc_Requires)a_positive
Property: assert
Result: ✅ pass

Obligation: (Origin_Inc_Requires)counter_ge_zero
Property: assert
Result: ✅ pass

Obligation: (Origin_Inc_Requires)a_positive
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
