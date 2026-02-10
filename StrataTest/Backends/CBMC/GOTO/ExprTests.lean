/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.Expr

namespace CProverGOTO.Tests

open Std (format)
open CProverGOTO

private def s_expr : Expr :=
  {
    id := .nullary $ .symbol "s",
    type := Ty.UnsignedBV 32
  }

private def one_expr : Expr :=
  {
    id := .nullary $ .constant "1",
    type := Ty.UnsignedBV 32
  }

/-- Constructs `s + 1  (bv32)`. -/
private def add_expr : Expr :=
  {
    id := .multiary .Plus,
    type := Ty.UnsignedBV 32,
    operands := [s_expr, one_expr]
  }

/-- info: (((s : unsignedbv[32]) + (1 : unsignedbv[32])) : unsignedbv[32]) -/
#guard_msgs in
#eval format add_expr

end CProverGOTO.Tests
