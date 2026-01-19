/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def freeReqEnsPgm : Program :=
#strata
program Core;
var g : int;
procedure Proc() returns ()
spec {
  modifies g;
  free requires [g_eq_15]: g == 15;
  // `g_lt_10` is not checked by this procedure.
  free ensures [g_lt_10]: g < 10;
}
{
  assert [g_gt_10_internal]: (g > 10);
  g := g + 1;
};

procedure ProcCaller () returns (x : int) {
  call := Proc();
  // Fails; `g_eq_15` requires of Proc ignored here.
  assert [g_eq_15_internal]: (g == 15);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


Obligation (Origin_Proc_Requires)g_eq_15 is free!


VCs:
Label: g_gt_10_internal
Property: assert
Assumptions:
(g_eq_15, ($__g0 == #15))

Proof Obligation:
((~Int.Gt $__g0) #10)

Label: g_lt_10
Property: assert
Assumptions:
(g_eq_15, ($__g0 == #15))

Proof Obligation:
#true

Label: g_eq_15_internal
Property: assert
Assumptions:
((Origin_Proc_Ensures)g_lt_10, ((~Int.Lt $__g2) #10))

Proof Obligation:
($__g2 == #15)



Result: Obligation: g_eq_15_internal
Property: assert
Result: ❌ fail
Model:
($__g2, 0)


Evaluated program:
var (g : int) := init_g_0
(procedure Proc :  () → ())
modifies: [g]
preconditions: (g_eq_15, ((g : int) == #15) (Attribute: Core.Procedure.CheckAttr.Free))
postconditions: (g_lt_10, (((~Int.Lt : (arrow int (arrow int bool))) (g : int)) #10) (Attribute: Core.Procedure.CheckAttr.Free))
body: assume [g_eq_15] ($__g0 == #15)
assert [g_gt_10_internal] ((~Int.Gt $__g0) #10)
g := ((~Int.Add $__g0) #1)
assert [g_lt_10] #true

(procedure ProcCaller :  () → ((x : int)))
modifies: []
preconditions: ⏎
postconditions: ⏎
body: call Proc([])
assert [g_eq_15_internal] ($__g2 == #15)

---
info:
Obligation: g_gt_10_internal
Property: assert
Result: ✅ pass

Obligation: g_lt_10
Property: assert
Result: ✅ pass

Obligation: g_eq_15_internal
Property: assert
Result: ❌ fail
Model:
($__g2, 0)
-/
#guard_msgs in
#eval verify "cvc5" freeReqEnsPgm

---------------------------------------------------------------------
