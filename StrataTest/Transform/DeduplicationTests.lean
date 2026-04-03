/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.Deduplication

namespace Core.Deduplication.Tests

open Lambda Imperative Core.Deduplication

/-! ## Unit tests for expression deduplication -/

private def mkObligation (label : String) (assumptions : PathConditions Expression)
    (obligation : Expression.Expr) : ProofObligation Expression :=
  { label, property := .assert, assumptions, obligation, metadata := .empty }

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

private def countDedupAssumptions (ob : ProofObligation Expression) : Nat :=
  let all := ob.assumptions.flatMap id
  all.filter (fun (l, _) => "$__dedup".isPrefixOf l) |>.length

/-! ### Obligation-level deduplication tests -/

-- Test: no deduplication when no duplicates exist
/--
info: 0
-/
#guard_msgs in
#eval do
  let ob := mkObligation "no_dups"
    [[("a1", mkApp2 (mkOp "Int.Add") (mkInt 1) (mkInt 2))]]
    (mkApp2 (mkOp "Int.Le") (mkInt 3) (mkInt 4))
  let (ob', _) := deduplicateObligation ob 0
  return countDedupAssumptions ob'

-- Test: deduplication when the same expression appears in assumptions and obligation
/--
info: 1
-/
#guard_msgs in
#eval do
  -- F(x) appears in both an assumption and the obligation
  let fx := mkApp1 (mkOp "F") (mkFvar "x")
  let ob := mkObligation "with_dups"
    [[("a1", mkApp2 (mkOp "Int.Ge") fx (mkInt 5))]]
    (.eq () (mkApp2 (mkOp "Int.Add") fx fx)
            (mkApp2 (mkOp "Int.Mul") (mkInt 2) fx))
  let (ob', _) := deduplicateObligation ob 0
  return countDedupAssumptions ob'

-- Test: trivial expressions (constants, variables) are not deduplicated
/--
info: 0
-/
#guard_msgs in
#eval do
  let x := mkFvar "x"
  let ob := mkObligation "trivial"
    [[("a1", mkApp2 (mkOp "Int.Ge") x (mkInt 5))]]
    (mkApp2 (mkOp "Int.Le") x (mkInt 5))
  let (ob', _) := deduplicateObligation ob 0
  return countDedupAssumptions ob'

-- Test: expressions with bound variables are not deduplicated
/--
info: 0
-/
#guard_msgs in
#eval do
  let withBvar := mkApp1 (mkOp "F") (.bvar () 0)
  let ob := mkObligation "bvar"
    [[("a1", .eq () withBvar (mkInt 5))]]
    (.eq () withBvar (mkInt 5))
  let (ob', _) := deduplicateObligation ob 0
  return countDedupAssumptions ob'

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
