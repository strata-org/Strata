/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
import all Strata.Languages.Core.Factory

/-! ## Tests for Factory -/

namespace Core

/--
info: [("Neg", "unaryOp"), ("Add", "binaryOp"), ("Sub", "binaryOp"), ("Mul", "binaryOp"), ("UDiv", "binaryOp"),
  ("UMod", "binaryOp"), ("SDiv", "binaryOp"), ("SMod", "binaryOp"), ("Not", "unaryOp"), ("And", "binaryOp"),
  ("Or", "binaryOp"), ("Xor", "binaryOp"), ("Shl", "binaryOp"), ("UShr", "binaryOp"), ("SShr", "binaryOp"),
  ("ULt", "binaryPredicate"), ("ULe", "binaryPredicate"), ("UGt", "binaryPredicate"), ("UGe", "binaryPredicate"),
  ("SLt", "binaryPredicate"), ("SLe", "binaryPredicate"), ("SGt", "binaryPredicate"), ("SGe", "binaryPredicate")]
-/
#guard_msgs in
#eval List.zip BVOpNames BVOpAritys

end Core
