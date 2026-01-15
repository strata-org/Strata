/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier
import Strata.Languages.Boogie.CallGraph

---------------------------------------------------------------------
namespace Strata

def globalCounterPgm : Program :=
#strata
program Boogie;

var counter : int;

inline function Add(x : int, y : int) : int { x + y }

procedure Inc(a : int) returns (ret : int)
spec {
  modifies counter;
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
info: { callees := Std.HashMap.ofList [("Inc", []), ("Q2", ["Q1"]), ("P", ["Inc"]), ("Q1", [])],
  callers := Std.HashMap.ofList [("Inc", ["P"]), ("Q1", ["Q2"])] }
-/
#guard_msgs in
#eval let (program, _) := Boogie.getProgram globalCounterPgm
      Boogie.Program.toProcedureCG program

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: new_g_value
Property: assert
Assumptions:
(a_positive, ((~Int.Gt $__a1) #0))

Proof Obligation:
#true

Label: old_g_property
Property: assert
Assumptions:
(a_positive, ((~Int.Gt $__a1) #0))

Proof Obligation:
(((~Int.Sub ((~Int.Add $__counter0) $__a1)) $__a1) == $__counter0)

Label: (Origin_Inc_Requires)a_positive
Property: assert
Assumptions:


Proof Obligation:
#true

Label: (Origin_Inc_Requires)a_positive
Property: assert
Assumptions:
((Origin_Inc_Ensures)new_g_value, ($__counter6 == ((~Int.Add $__counter3) #8)))
((Origin_Inc_Ensures)old_g_property, (((~Int.Sub $__b5) #8) == $__counter3))

Proof Obligation:
#true

Label: return_value_lemma
Property: assert
Assumptions:
((Origin_Inc_Ensures)new_g_value, ($__counter6 == ((~Int.Add $__counter3) #8)))
((Origin_Inc_Ensures)old_g_property, (((~Int.Sub $__b5) #8) == $__counter3)) ((Origin_Inc_Ensures)new_g_value, ($__counter8 == ((~Int.Add $__counter6) #8))) ((Origin_Inc_Ensures)old_g_property, (((~Int.Sub $__b7) #8) == $__counter6))

Proof Obligation:
($__b7 == ((~Int.Add $__counter3) #16))

Label: assert_0
Property: assert
Assumptions:


Proof Obligation:
#true

Wrote problem to vcs/old_g_property.smt2.
Wrote problem to vcs/return_value_lemma.smt2.
---
info:
Obligation: new_g_value
Property: assert
Result: ✅ pass

Obligation: old_g_property
Property: assert
Result: ✅ pass

Obligation: (Origin_Inc_Requires)a_positive
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
#eval verify "cvc5" globalCounterPgm

---------------------------------------------------------------------

/-
-- DDM AST
#eval globalCounterEnv.commands

-- Translation from DDM AST to Boogie/Strata AST
#eval TransM.run (translateProgram (globalCounterEnv.commands))
-/

---------------------------------------------------------------------
