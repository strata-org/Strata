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

procedure F(n : int, out r : int)
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
       call F(n + 11, out r);
       call F(r, out r);
   }
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: n_gt_100_postcond
Property: assert
Assumptions:
<label_ite_cond_true: 100 < n>: if 100 < n@1 then 100 < n@1 else true
<label_ite_cond_false: !(100 < n)>: if if 100 < n@1 then false else true then if 100 < n@1 then false else true else true
callElimAssume_n_gt_100_postcond_6: if if 100 < n@1 then false else true then 100 < n@1 + 11 ==> r@2 == n@1 + 11 - 10 else true
callElimAssume_n_le_100_postcond_7: if if 100 < n@1 then false else true then n@1 + 11 <= 100 ==> r@2 == 91 else true
callElimAssume_n_gt_100_postcond_2: if if 100 < n@1 then false else true then 100 < r@2 ==> r@3 == r@2 - 10 else true
callElimAssume_n_le_100_postcond_3: if if 100 < n@1 then false else true then r@2 <= 100 ==> r@3 == 91 else true
Obligation:
100 < n@1 ==> if 100 < n@1 then n@1 - 10 else r@3 == n@1 - 10

Label: n_le_100_postcond
Property: assert
Assumptions:
<label_ite_cond_true: 100 < n>: if 100 < n@1 then 100 < n@1 else true
<label_ite_cond_false: !(100 < n)>: if if 100 < n@1 then false else true then if 100 < n@1 then false else true else true
callElimAssume_n_gt_100_postcond_6: if if 100 < n@1 then false else true then 100 < n@1 + 11 ==> r@2 == n@1 + 11 - 10 else true
callElimAssume_n_le_100_postcond_7: if if 100 < n@1 then false else true then n@1 + 11 <= 100 ==> r@2 == 91 else true
callElimAssume_n_gt_100_postcond_2: if if 100 < n@1 then false else true then 100 < r@2 ==> r@3 == r@2 - 10 else true
callElimAssume_n_le_100_postcond_3: if if 100 < n@1 then false else true then r@2 <= 100 ==> r@3 == 91 else true
Obligation:
n@1 <= 100 ==> if 100 < n@1 then n@1 - 10 else r@3 == 91

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
