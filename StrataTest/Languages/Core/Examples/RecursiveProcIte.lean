/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def procIfPgm : Program :=
#strata
program Core;

procedure F(n : int) returns (r : int)
spec {
  ensures [n_gt_100_postcond]: 100 < n ==> r == n - 10;
  ensures [n_le_100_postcond]: n <= 100 ==> r == 91;
}
{
   if (100 < n)
   {
       r := n - 10;
   }
   else
   {
       call r := F(n + 11);
       call r := F(r);
   }
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: n_gt_100_postcond
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt #100 n)>: 100 < $__n0
Obligation:
100 < $__n0 ==> true

Label: n_le_100_postcond
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt #100 n)>: 100 < $__n0
Obligation:
$__n0 <= 100 ==> $__n0 - 10 == 91

---
info:
Obligation: n_gt_100_postcond
Property: assert
Result: ✅ pass

Obligation: n_le_100_postcond
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify procIfPgm

/-
<PCs>
if (cond) {
  <PCs ++ [cond]>
  tb
  assume (PCt)
  <PCs ++ ([cond, PCt])>
} else {
  <PCs ++ [!cond]>
  eb
  assume (PCf)
  <PCs ++ ([!cond, PCf]>
}
<PCs ++ [cond => cond, cond => PCt, !cond => !cond, !cond => PCf]>
-/
