/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.MetaVerifier

open StrataDDM (Program)
---------------------------------------------------------------------
namespace Strata

def procIfPgm : Program :=
#strata
program Core;

procedure F(n : int, out r : int)
spec {
  ensures [n_gt_100_postcond]: int.lt(100, n) ==> r == int.sub(n, 10);
  ensures [n_le_100_postcond]: int.le(n, 100) ==> r == 91;
}
{
   if (int.lt(100, n))
   {
       r := int.sub(n, 10);
   }
   else
   {
       call F(int.add(n, 11), out r);
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
<label_ite_cond_true: int.lt(100, n)>: if int.lt(100, n@1) then int.lt(100, n@1) else true
<label_ite_cond_false: !(int.lt(100, n))>: if if int.lt(100, n@1) then false else true then if int.lt(100, n@1) then false else true else true
callElimAssume_n_gt_100_postcond_2: if if int.lt(100, n@1) then false else true then int.lt(100, int.add(n@1, 11)) ==> r@2 == int.sub(int.add(n@1, 11), 10) else true
callElimAssume_n_le_100_postcond_3: if if int.lt(100, n@1) then false else true then int.le(int.add(n@1, 11), 100) ==> r@2 == 91 else true
callElimAssume_n_gt_100_postcond_6: if if int.lt(100, n@1) then false else true then int.lt(100, r@2) ==> r@3 == int.sub(r@2, 10) else true
callElimAssume_n_le_100_postcond_7: if if int.lt(100, n@1) then false else true then int.le(r@2, 100) ==> r@3 == 91 else true
Obligation:
int.lt(100, n@1) ==> (if int.lt(100, n@1) then int.sub(n@1, 10) else r@3) == int.sub(n@1, 10)

Label: n_le_100_postcond
Property: assert
Assumptions:
<label_ite_cond_true: int.lt(100, n)>: if int.lt(100, n@1) then int.lt(100, n@1) else true
<label_ite_cond_false: !(int.lt(100, n))>: if if int.lt(100, n@1) then false else true then if int.lt(100, n@1) then false else true else true
callElimAssume_n_gt_100_postcond_2: if if int.lt(100, n@1) then false else true then int.lt(100, int.add(n@1, 11)) ==> r@2 == int.sub(int.add(n@1, 11), 10) else true
callElimAssume_n_le_100_postcond_3: if if int.lt(100, n@1) then false else true then int.le(int.add(n@1, 11), 100) ==> r@2 == 91 else true
callElimAssume_n_gt_100_postcond_6: if if int.lt(100, n@1) then false else true then int.lt(100, r@2) ==> r@3 == int.sub(r@2, 10) else true
callElimAssume_n_le_100_postcond_7: if if int.lt(100, n@1) then false else true then int.le(r@2, 100) ==> r@3 == 91 else true
Obligation:
int.le(n@1, 100) ==> (if int.lt(100, n@1) then int.sub(n@1, 10) else r@3) == 91

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
#eval Core.verify procIfPgm

theorem procIfPgm_correct : smtVCsCorrect procIfPgm := by
  gen_smt_vcs
  all_goals (try grind)

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

end Strata
