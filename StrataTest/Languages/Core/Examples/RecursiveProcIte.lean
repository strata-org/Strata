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
(<label_ite_cond_true: ((~Int.Lt #100) n)>, (if ((~Int.Lt #100) $__n0) then ((~Int.Lt #100) $__n0) else #true))
(<label_ite_cond_false: !((~Int.Lt #100) n)>, (if (if ((~Int.Lt #100) $__n0) then #false else #true) then (if ((~Int.Lt #100) $__n0) then #false else #true) else #true)) ((Origin_F_Ensures)n_gt_100_postcond, (if (if ((~Int.Lt #100) $__n0) then #false else #true) then ((~Bool.Implies ((~Int.Lt #100) ((~Int.Add $__n0) #11))) ($__r2 == ((~Int.Sub ((~Int.Add $__n0) #11)) #10))) else #true)) ((Origin_F_Ensures)n_le_100_postcond, (if (if ((~Int.Lt #100) $__n0) then #false else #true) then ((~Bool.Implies ((~Int.Le ((~Int.Add $__n0) #11)) #100)) ($__r2 == #91)) else #true)) ((Origin_F_Ensures)n_gt_100_postcond, (if (if ((~Int.Lt #100) $__n0) then #false else #true) then ((~Bool.Implies ((~Int.Lt #100) $__r2)) ($__r3 == ((~Int.Sub $__r2) #10))) else #true)) ((Origin_F_Ensures)n_le_100_postcond, (if (if ((~Int.Lt #100) $__n0) then #false else #true) then ((~Bool.Implies ((~Int.Le $__r2) #100)) ($__r3 == #91)) else #true))

Proof Obligation:
((~Bool.Implies ((~Int.Lt #100) $__n0)) ((if ((~Int.Lt #100) $__n0) then ((~Int.Sub $__n0) #10) else $__r3) == ((~Int.Sub $__n0) #10)))

Label: n_le_100_postcond
Property: assert
Assumptions:
(<label_ite_cond_true: ((~Int.Lt #100) n)>, (if ((~Int.Lt #100) $__n0) then ((~Int.Lt #100) $__n0) else #true))
(<label_ite_cond_false: !((~Int.Lt #100) n)>, (if (if ((~Int.Lt #100) $__n0) then #false else #true) then (if ((~Int.Lt #100) $__n0) then #false else #true) else #true)) ((Origin_F_Ensures)n_gt_100_postcond, (if (if ((~Int.Lt #100) $__n0) then #false else #true) then ((~Bool.Implies ((~Int.Lt #100) ((~Int.Add $__n0) #11))) ($__r2 == ((~Int.Sub ((~Int.Add $__n0) #11)) #10))) else #true)) ((Origin_F_Ensures)n_le_100_postcond, (if (if ((~Int.Lt #100) $__n0) then #false else #true) then ((~Bool.Implies ((~Int.Le ((~Int.Add $__n0) #11)) #100)) ($__r2 == #91)) else #true)) ((Origin_F_Ensures)n_gt_100_postcond, (if (if ((~Int.Lt #100) $__n0) then #false else #true) then ((~Bool.Implies ((~Int.Lt #100) $__r2)) ($__r3 == ((~Int.Sub $__r2) #10))) else #true)) ((Origin_F_Ensures)n_le_100_postcond, (if (if ((~Int.Lt #100) $__n0) then #false else #true) then ((~Bool.Implies ((~Int.Le $__r2) #100)) ($__r3 == #91)) else #true))

Proof Obligation:
((~Bool.Implies ((~Int.Le $__n0) #100)) ((if ((~Int.Lt #100) $__n0) then ((~Int.Sub $__n0) #10) else $__r3) == #91))

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
#eval verify "cvc5" procIfPgm

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
