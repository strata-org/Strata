/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.Deduplication

namespace Core.Deduplication.Tests

open Lambda Imperative Core.Deduplication

/-! ## Unit tests for expression deduplication -/

private def mkFvar (name : String) : Expression.Expr :=
  .fvar () ⟨name, ()⟩ none

private def mkOp (name : String) : Expression.Expr :=
  .op () ⟨name, ()⟩ none

private def mkApp1 (fn arg : Expression.Expr) : Expression.Expr :=
  .app () fn arg

private def mkApp2 (fn arg1 arg2 : Expression.Expr) : Expression.Expr :=
  .app () (.app () fn arg1) arg2

private def mkInt (i : Int) : Expression.Expr :=
  .intConst () i

/-! ### Program-level deduplication tests -/

-- Test: deduplicateBody introduces var declarations for duplicated expressions
/--
info: true
-/
#guard_msgs in
#eval do
  let fx := mkApp1 (mkOp "F") (mkFvar "x")
  let body : Statements := [
    Statement.assume "a1" (mkApp2 (mkOp "Int.Ge") fx (mkInt 5)) .empty,
    Statement.assert "check" (.eq () (mkApp2 (mkOp "Int.Add") fx fx)
                                     (mkApp2 (mkOp "Int.Mul") (mkInt 2) fx)) .empty
  ]
  let (body', _) := deduplicateBody body 0
  -- The deduplicated body should have more statements (var declarations prepended)
  return decide (body'.length > body.length)

-- Test: deduplicateBody does not modify body with no duplicates
/--
info: true
-/
#guard_msgs in
#eval do
  let body : Statements := [
    Statement.assume "a1" (mkApp2 (mkOp "Int.Ge") (mkFvar "x") (mkInt 5)) .empty,
    Statement.assert "check" (mkApp2 (mkOp "Int.Le") (mkFvar "y") (mkInt 10)) .empty
  ]
  let (body', _) := deduplicateBody body 0
  return decide (body'.length == body.length)

end Core.Deduplication.Tests
