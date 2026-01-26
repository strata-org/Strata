/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Factory

/-! ## Tests for Factory -/

namespace Core

private def BVOpNames :=
  ["Neg", "Add", "Sub", "Mul", "UDiv", "UMod", "SDiv", "SMod",
   "Not", "And", "Or", "Xor", "Shl", "UShr", "SShr",
   "ULt", "ULe", "UGt", "UGe",
   "SLt", "SLe", "SGt", "SGe"]

private def BVOpAritys :=
  ["unaryOp", "binaryOp", "binaryOp", "binaryOp", "binaryOp", "binaryOp", "binaryOp", "binaryOp",
   "unaryOp", "binaryOp", "binaryOp", "binaryOp", "binaryOp", "binaryOp", "binaryOp",
   "binaryPredicate", "binaryPredicate", "binaryPredicate", "binaryPredicate",
   "binaryPredicate", "binaryPredicate", "binaryPredicate", "binaryPredicate" ]

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
