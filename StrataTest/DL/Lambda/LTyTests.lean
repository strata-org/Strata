/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LTy

/-! ## Tests for LTy -/

namespace Lambda

open LTy.Syntax

/--
info: [Lambda.LMonoTy.tcons "arrow" [Lambda.LMonoTy.ftvar "_dummy0", Lambda.LMonoTy.ftvar "_dummy1"],
 Lambda.LMonoTy.tcons "bool" [],
 Lambda.LMonoTy.tcons "foo" [Lambda.LMonoTy.ftvar "_dummy0"],
 Lambda.LMonoTy.tcons "a" [Lambda.LMonoTy.ftvar "_dummy0", Lambda.LMonoTy.ftvar "_dummy1"]]
-/
#guard_msgs in
#eval LMonoTy.getTyConstructors
        ((.tcons "arrow" [.tcons "bool" [], .tcons "foo" [.tcons "a" [.ftvar "b", .tcons "bool" []]]]))

/-- info: 3 -/
#guard_msgs in
#eval LTy.inputArity t[int → (int → (int → int))]
/-- info: 2 -/
#guard_msgs in
#eval LTy.inputArity t[int → (int → int)]
/-- info: 1 -/
#guard_msgs in
#eval LTy.inputArity t[∀a. (%a → int) → int]
/-- info: 0 -/
#guard_msgs in
#eval LTy.inputArity t[∀a. pair %a bool]

/-- info: [int, int, int] -/
#guard_msgs in
#eval format $ LMonoTy.inputTypes mty[int → (int → (int → int))]
/-- info: [int, bool] -/
#guard_msgs in
#eval format $ LMonoTy.inputTypes mty[int → (bool → int)]
/-- info: [int, bool, bit] -/
#guard_msgs in
#eval format $ LMonoTy.inputTypes mty[int → (bool → (bit → nat))]
/-- info: [(arrow int int)] -/
#guard_msgs in
#eval format $ LMonoTy.inputTypes mty[(int → int) → nat]
/-- info: [] -/
#guard_msgs in
#eval LMonoTy.inputTypes mty[pair int bool]

end Lambda
