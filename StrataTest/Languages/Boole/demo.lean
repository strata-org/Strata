/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

def loopSimple : Strata.Program :=
#strata
program Boole;

procedure loopSimple (n: int) returns (r: int)
spec {
  requires (n >= 0);
}
{
  var sum : int;
  var i : int;

  sum := 0;
  i := 0;
  while(i < n)
    invariant (i <= n && ((i * (i-1)) div 2 == sum))
  {
    sum := sum + i;
    i := i + 1;
  }
  assert [sum_assert]: ((n * (n-1)) div 2 == sum);
  assert [neg_cond]: (i == n);
  r := sum;
};
#end

open Strata.SMT

theorem loopSimple_smtVCsCorrect : smtVCsCorrect loopSimple := by
  gen_smt_vcs
  all_goals (try grind)

/-- info: 'loopSimple_smtVCsCorrect' depends on axioms: [propext,
 Classical.choice,
 ExprSourceLoc.eq_trivial,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝,
 Core.bv16SafeAddFunc._native.native_decide.ax_1✝,
 Core.bv16SafeMulFunc._native.native_decide.ax_1✝,
 Core.bv16SafeNegFunc._native.native_decide.ax_1✝,
 Core.bv16SafeSDivFunc._native.native_decide.ax_1✝,
 Core.bv16SafeSDivFunc._native.native_decide.ax_2✝,
 Core.bv16SafeSubFunc._native.native_decide.ax_1✝,
 Core.bv16SafeUAddFunc._native.native_decide.ax_1✝,
 Core.bv16SafeUMulFunc._native.native_decide.ax_1✝,
 Core.bv16SafeUNegFunc._native.native_decide.ax_1✝,
 Core.bv16SafeUSubFunc._native.native_decide.ax_1✝,
 Core.bv1SafeAddFunc._native.native_decide.ax_1✝,
 Core.bv1SafeMulFunc._native.native_decide.ax_1✝,
 Core.bv1SafeNegFunc._native.native_decide.ax_1✝,
 Core.bv1SafeSDivFunc._native.native_decide.ax_4✝,
 Core.bv1SafeSDivFunc._native.native_decide.ax_5✝,
 Core.bv1SafeSubFunc._native.native_decide.ax_1✝,
 Core.bv1SafeUAddFunc._native.native_decide.ax_1✝,
 Core.bv1SafeUMulFunc._native.native_decide.ax_1✝,
 Core.bv1SafeUNegFunc._native.native_decide.ax_1✝,
 Core.bv1SafeUSubFunc._native.native_decide.ax_1✝,
 Core.bv32SafeAddFunc._native.native_decide.ax_1✝,
 Core.bv32SafeMulFunc._native.native_decide.ax_1✝,
 Core.bv32SafeNegFunc._native.native_decide.ax_1✝,
 Core.bv32SafeSDivFunc._native.native_decide.ax_1✝,
 Core.bv32SafeSDivFunc._native.native_decide.ax_2✝,
 Core.bv32SafeSubFunc._native.native_decide.ax_1✝,
 Core.bv32SafeUAddFunc._native.native_decide.ax_1✝,
 Core.bv32SafeUMulFunc._native.native_decide.ax_1✝,
 Core.bv32SafeUNegFunc._native.native_decide.ax_1✝,
 Core.bv32SafeUSubFunc._native.native_decide.ax_1✝,
 Core.bv64SafeAddFunc._native.native_decide.ax_1✝,
 Core.bv64SafeMulFunc._native.native_decide.ax_1✝,
 Core.bv64SafeNegFunc._native.native_decide.ax_1✝,
 Core.bv64SafeSDivFunc._native.native_decide.ax_1✝,
 Core.bv64SafeSDivFunc._native.native_decide.ax_2✝,
 Core.bv64SafeSubFunc._native.native_decide.ax_1✝,
 Core.bv64SafeUAddFunc._native.native_decide.ax_1✝,
 Core.bv64SafeUMulFunc._native.native_decide.ax_1✝,
 Core.bv64SafeUNegFunc._native.native_decide.ax_1✝,
 Core.bv64SafeUSubFunc._native.native_decide.ax_1✝,
 Core.bv8SafeAddFunc._native.native_decide.ax_1✝,
 Core.bv8SafeMulFunc._native.native_decide.ax_1✝,
 Core.bv8SafeNegFunc._native.native_decide.ax_1✝,
 Core.bv8SafeSDivFunc._native.native_decide.ax_1✝,
 Core.bv8SafeSDivFunc._native.native_decide.ax_2✝,
 Core.bv8SafeSubFunc._native.native_decide.ax_1✝,
 Core.bv8SafeUAddFunc._native.native_decide.ax_1✝,
 Core.bv8SafeUMulFunc._native.native_decide.ax_1✝,
 Core.bv8SafeUNegFunc._native.native_decide.ax_1✝,
 Core.bv8SafeUSubFunc._native.native_decide.ax_1✝]-/
#guard_msgs in
#print axioms loopSimple_smtVCsCorrect
