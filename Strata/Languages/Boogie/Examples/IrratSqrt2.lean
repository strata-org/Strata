/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Boogie
import Strata.Languages.Boogie.Verifier
import Strata.Languages.Boogie.LeanDenote
import Mathlib.Data.Real.Irrational

---------------------------------------------------------------------
namespace Strata

def sqrt2IrrationalEnv : Environment :=
#strata
program Boogie;
procedure Test(p : int, q : int) returns ()
{

  assert [int_add_commutes]: (p + q == q + p);

  assume [q_gt_0]: (q > 0);
  assert [sqrt_2_is_irrational]: ((p * p) != (2 * q * q));

};
#end


private theorem sqrt_2_is_irrational_helper :
  ∀ (p q : Int), (decide (q > 0) ==> !p * p == 2 * q * q) = true := by
  intro p q
  simp [Lambda.Bool.implies, -decide_implies]
  intro h_q_pos
  have h_main := irrational_sqrt_two
  have h_not_isSq := @irrational_sqrt_ratCast_iff_of_nonneg 2 (by simp)
  simp_all [IsSquare]
  have h_not_isSq_alt := @h_not_isSq (p / q)
  ring_nf at h_not_isSq_alt
  have := @mul_inv_eq_iff_eq_mul₀  _ _
          ((p : Rat) ^ 2) ((q : Rat) ^ 2) 2 (by simp_all; omega)
  ring_nf at this
  norm_cast at this
  ring_nf; simp_all
  have _ : ¬((p : Rat) ^ 2 * ((q : Rat) ^ 2)⁻¹ = 2) := by
    exact fun a => h_not_isSq_alt (id (Eq.symm a))
  simp_all

theorem sqrt_2_is_irrational : ∀ (__p0 __q1 : ℤ),
  (decide (__q1 > 0) ==>
          !__p0 * __p0 == 2 * __q1 * __q1) = true := by
  apply sqrt_2_is_irrational_helper

/--
info: SMT Results:

Obligation: int_add_commutes
Result: verified

Obligation: sqrt_2_is_irrational
Result: err ⏎
---
info:
✅️ Theorem sqrt_2_is_irrational is already in the environment!
-/
#guard_msgs in
#verify sqrt2IrrationalEnv (timeout := 1) (verbose := false)

end Strata
