/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.DDMTransform.Translate

/-! ## Tests for SMT DDM Translate -/

namespace Strata.SMTDDM

/-- info: Except.ok "(+ 10 20)" -/
#guard_msgs in #eval (toString
    (.app SMT.Op.add [(.prim (.int 10)), (.prim (.int 20))] .int))

/-- info: Except.ok "(+ 10 -20)" -/
#guard_msgs in #eval (toString
    (.app SMT.Op.add [(.prim (.int 10)), (.prim (.int (-20)))] .int))

/-- info: Except.ok "(+ 0.1 0.2)" -/
#guard_msgs in #eval (toString
    (.app SMT.Op.add [(.prim (.real (Decimal.mk 1 (-1)))),
                      (.prim (.real (Decimal.mk 2 (-2))))] .int))

/-- info: Except.ok "(_ bv1 32)" -/
#guard_msgs in #eval (toString
    (.prim (.bitvec (BitVec.ofNat 32/-width-/ 1/-value-/))))

end Strata.SMTDDM
