/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def freeReqEnsPgm : Program :=
#strata
program Boogie;
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
info: [Strata.Boogie] Type checking succeeded.


Obligation <Origin:Proc_Requires>g_eq_15 is free!


VCs:
Label: g_gt_10_internal
Assumptions:
(g_eq_15, ($__g0 == #15))
Proof Obligation:
((~Int.Gt $__g0) #10)

Label: g_lt_10
Assumptions:
(g_eq_15, ($__g0 == #15))
Proof Obligation:
#true

Label: g_eq_15_internal
Assumptions:
(<Origin:Proc_Ensures>g_lt_10, ((~Int.Lt $__g2) #10))
Proof Obligation:
($__g2 == #15)

Wrote problem to vcs/g_gt_10_internal.smt2.
Wrote problem to vcs/g_lt_10.smt2.
Wrote problem to vcs/g_eq_15_internal.smt2.


Obligation g_eq_15_internal: could not be proved!

Result: failed
CEx: ($__g2, 0)

Evaluated program:
var (g : int) := init_g_0
(procedure Proc :  () → ())
modifies: [g]
preconditions: (g_eq_15, ((g : int) == (#15 : int)) (Attribute: Boogie.Procedure.CheckAttr.Free))
postconditions: (g_lt_10, (((~Int.Lt : (arrow int (arrow int bool))) (g : int)) (#10 : int)) (Attribute: Boogie.Procedure.CheckAttr.Free))
body: assume [g_eq_15] ($__g0 == #15)
assert [g_gt_10_internal] ((~Int.Gt $__g0) #10)
g := ((~Int.Add $__g0) #1)
#[<[g_lt_10]: (((~Int.Lt : (arrow int (arrow int bool))) (g : int)) (#10 : int))>,
 <[g_lt_10]: FreePostCondition>] assert [g_lt_10] #true

(procedure ProcCaller :  () → ((x : int)))
modifies: []
preconditions: ⏎
postconditions: ⏎
body: #[<var g: ($__g2 : int)>] call Proc([])
assert [g_eq_15_internal] ($__g2 == #15)

---
info:
Obligation: g_gt_10_internal
Result: verified

Obligation: g_lt_10
Result: verified

Obligation: g_eq_15_internal
Result: failed
CEx: ($__g2, 0)
-/
#guard_msgs in
#eval verify "cvc5" freeReqEnsPgm

---------------------------------------------------------------------
