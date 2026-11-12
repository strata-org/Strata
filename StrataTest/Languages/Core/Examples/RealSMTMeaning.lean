/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import Strata.Languages.Core.Logic.FactoryInterp
import Strata.Util.RealProps
import StrataDDM.Integration.Lean.HashCommands

/-! The real operations of the models of `Core.Factory` that satisfy `Core.RealsAsReal` and
the SMT-LIB theory of reals the solver uses agree on the edge cases below: division by zero
is unconstrained in both, and is still a function of its arguments. -/

/-! ### In the model -/

open Strata.Util in
/-- In a model satisfying `RealsAsReal`, `Real.Div` is division at a nonzero divisor. -/
example {tc : Lambda.TyConstrInterp} {op : Lambda.OpInterp tc} (h : Core.RealsAsReal op) :
    (op "Real.Div" (Core.realBinSort .real) : Real → Real → Real) (Real.ofRat 1) (Real.ofRat (-2)) =
      Real.ofRat 1 / Real.ofRat (-2) :=
  h.div _ _ fun h0 =>
    absurd (Real.ofRat_inj.mp (h0 : Real.ofRat (-2) = Real.ofRat 0)) (by decide)

open Strata.Util Classical in
/-- The comparisons are the order on `Real` in every model satisfying `RealsAsReal`. -/
example {tc : Lambda.TyConstrInterp} {op : Lambda.OpInterp tc} (h : Core.RealsAsReal op) :
    (op "Real.Lt" (Core.realBinSort .bool) : Real → Real → Bool) (Real.ofRat (-1)) (Real.ofRat 0) =
      true ∧
    (op "Real.Ge" (Core.realBinSort .bool) : Real → Real → Bool) (Real.ofRat 0) (Real.ofRat 0) =
      true := by
  rw [h.lt, h.ge]
  exact ⟨decide_eq_true (Real.ofRat_lt_ofRat.mpr (by decide)),
    decide_eq_true (Real.ofRat_le_ofRat.mpr (by decide))⟩

/-! ### In the solver -/

meta section
open StrataDDM (Program)

namespace Strata

/-- Edge cases of the real operations in the solver. Division by zero is a function of its
    arguments (`div_zero_functional`) whose value neither SMT-LIB nor `RealsAsReal` fixes, so
    neither `div_zero_unconstrained` nor `div_zero_unconstrained_one` verifies.

    What the expected output pins: for the two `div_zero_unconstrained` cases, the verdict
    fail is the point, and the model value is solver-chosen; `div_mul_cancel` is nonlinear
    and passes on the cvc5 that CI pins. -/
def realEdgePgm : Program :=
#strata
program Core;

procedure P(x : real, y : real)
{
  assert [div_zero_functional]: real.div(x, 0.0) == real.div(x, 0.0);
  assert [div_zero_unconstrained]: real.div(x, 0.0) == 0.0;
  assert [div_zero_unconstrained_one]: real.div(x, 0.0) == 1.0;
  assert [div_nonzero]: real.div(1.0, 4.0) == 0.25;
  assert [div_mul_cancel]: !(y == 0.0) ==> real.mul(real.div(x, y), y) == x;
  assert [neg_sub]: real.neg(real.sub(x, y)) == real.sub(y, x);
  assert [lt_irrefl]: !real.lt(x, x);
  assert [le_total]: real.le(x, y) || real.ge(x, y);
  assert [gt_lt]: real.gt(x, y) == real.lt(y, x);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: div_zero_functional
Property: assert
Obligation:
true

Label: div_zero_unconstrained
Property: assert
Obligation:
real.div(x@1, 0.0) == 0.0

Label: div_zero_unconstrained_one
Property: assert
Obligation:
real.div(x@1, 0.0) == 1.0

Label: div_nonzero
Property: assert
Obligation:
real.div(1.0, 4.0) == 0.25

Label: div_mul_cancel
Property: assert
Obligation:
!(y@1 == 0.0) ==> real.mul(real.div(x@1, y@1), y@1) == x@1

Label: neg_sub
Property: assert
Obligation:
real.neg(real.sub(x@1, y@1)) == real.sub(y@1, x@1)

Label: lt_irrefl
Property: assert
Obligation:
!(real.lt(x@1, x@1))

Label: le_total
Property: assert
Obligation:
real.le(x@1, y@1) || real.ge(x@1, y@1)

Label: gt_lt
Property: assert
Obligation:
real.gt(x@1, y@1) == real.lt(y@1, x@1)

---
info:
Obligation: div_zero_functional
Property: assert
Result: ✅ pass

Obligation: div_zero_unconstrained
Property: assert
Result: ❌ fail
Model:
(x@1, 0.0)

Obligation: div_zero_unconstrained_one
Property: assert
Result: ❌ fail
Model:
(x@1, 0.0)

Obligation: div_nonzero
Property: assert
Result: ✅ pass

Obligation: div_mul_cancel
Property: assert
Result: ✅ pass

Obligation: neg_sub
Property: assert
Result: ✅ pass

Obligation: lt_irrefl
Property: assert
Result: ✅ pass

Obligation: le_total
Property: assert
Result: ✅ pass

Obligation: gt_lt
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify realEdgePgm

end Strata

end
