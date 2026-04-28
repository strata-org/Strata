/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.ASTtoCST

/-! Tests for the generic call fallback in ASTtoCST.

When an unknown operation name reaches the `handleUnaryOps`,
`handleBinaryOps` / `handleBitvecBinaryOps`, or `handleTernaryOps`
fallback, the printer should render it as a generic function call
`name(arg1, arg2, …)` rather than silently defaulting to an unrelated
Core construct (e.g. `.bvand`, `.not`, `.map_set`).

We construct Core AST terms directly using Lambda `LExpr` so that
the operation names are not in the known-builtin tables, and then
format them via `Core.formatStatement`. -/

namespace Strata.Test.GenericCallFallback

open Strata Core Lambda

private def mkOp (name : String) : Core.Expression.Expr :=
  LExpr.op Strata.SourceRange.none ⟨name, ()⟩ none

private def mkFvar (name : String) : Core.Expression.Expr :=
  LExpr.fvar Strata.SourceRange.none ⟨name, ()⟩ none

private def mkApp (fn arg : Core.Expression.Expr) : Core.Expression.Expr :=
  LExpr.app Strata.SourceRange.none fn arg

private def mkStrConst (s : String) : Core.Expression.Expr :=
  LExpr.const Strata.SourceRange.none (.strConst s)

private def mkCall1 (opName : String) (a : Core.Expression.Expr) : Core.Expression.Expr :=
  mkApp (mkOp opName) a

private def mkCall2 (opName : String) (a b : Core.Expression.Expr) : Core.Expression.Expr :=
  mkApp (mkApp (mkOp opName) a) b

private def mkCall3 (opName : String) (a b c : Core.Expression.Expr) : Core.Expression.Expr :=
  mkApp (mkApp (mkApp (mkOp opName) a) b) c

private def mkCall4 (opName : String) (a b c d : Core.Expression.Expr) : Core.Expression.Expr :=
  mkApp (mkApp (mkApp (mkApp (mkOp opName) a) b) c) d

private def mkAssert (label : String) (e : Core.Expression.Expr) : Core.Statement :=
  Core.Statement.assert label e #[]

private def fmtStmt (s : Core.Statement) (fvs : Array String := #[]) : String :=
  (Core.formatStatement s (extraFreeVars := fvs)).pretty

-- -----------------------------------------------------------------------
-- Test: unknown unary operation renders as `unknownUnary(x)`, not `!x`
-- -----------------------------------------------------------------------

/--
info: "assert [u1]: unknownUnary(x);\n\n-- Errors encountered during conversion:\nUnsupported construct in handleUnaryOps: unknown operation, rendering as generic call: unknownUnary\nContext: Global scope:\n  freeVars: [x]"
-/
#guard_msgs in
#eval do
  let e := mkCall1 "unknownUnary" (mkFvar "x")
  IO.println (repr (fmtStmt (mkAssert "u1" e) #["x"]))

-- -----------------------------------------------------------------------
-- Test: unknown binary operation renders as `re_search_bool(pat, s)`,
-- not `pat & s` (the original bug from issue #797)
-- -----------------------------------------------------------------------

/--
info: "assert [b1]: re_search_bool(\"^[0-9]+$\", s);\n\n-- Errors encountered during conversion:\nUnsupported construct in handleBitvecBinaryOps: unknown operation, rendering as generic call: re_search_bool\nContext: Global scope:\n  freeVars: [s]"
-/
#guard_msgs in
#eval do
  let e := mkCall2 "re_search_bool" (mkStrConst "^[0-9]+$") (mkFvar "s")
  IO.println (repr (fmtStmt (mkAssert "b1" e) #["s"]))

-- -----------------------------------------------------------------------
-- Test: another unknown binary op
-- -----------------------------------------------------------------------

/--
info: "assert [b2]: customBinOp(x, y);\n\n-- Errors encountered during conversion:\nUnsupported construct in handleBitvecBinaryOps: unknown operation, rendering as generic call: customBinOp\nContext: Global scope:\n  freeVars: [x, y]"
-/
#guard_msgs in
#eval do
  let e := mkCall2 "customBinOp" (mkFvar "x") (mkFvar "y")
  IO.println (repr (fmtStmt (mkAssert "b2" e) #["x", "y"]))

-- -----------------------------------------------------------------------
-- Test: unknown ternary operation renders as `ternaryFoo(x, y, z)`,
-- not `x[y := z]` (the old map_set fallback)
-- -----------------------------------------------------------------------

/--
info: "assert [t1]: ternaryFoo(x, y, z);\n\n-- Errors encountered during conversion:\nUnsupported construct in handleTernaryOps: unknown operation, rendering as generic call: ternaryFoo\nContext: Global scope:\n  freeVars: [x, y, z]"
-/
#guard_msgs in
#eval do
  let e := mkCall3 "ternaryFoo" (mkFvar "x") (mkFvar "y") (mkFvar "z")
  IO.println (repr (fmtStmt (mkAssert "t1" e) #["x", "y", "z"]))

-- -----------------------------------------------------------------------
-- Test: unknown 4-ary operation renders as generic call
-- -----------------------------------------------------------------------

/--
info: "assert [q1]: fourArgFn(a, b, c, d);\n\n-- Errors encountered during conversion:\nUnsupported construct in lopToExpr: unknown operation, rendering as generic call: fourArgFn\nContext: Global scope:\n  freeVars: [a, b, c, d]"
-/
#guard_msgs in
#eval do
  let e := mkCall4 "fourArgFn" (mkFvar "a") (mkFvar "b") (mkFvar "c") (mkFvar "d")
  IO.println (repr (fmtStmt (mkAssert "q1" e) #["a", "b", "c", "d"]))

-- -----------------------------------------------------------------------
-- Test: known operations still render correctly (regression check)
-- -----------------------------------------------------------------------

/--
info: "assert [known_add]: x + y;"
-/
#guard_msgs in
#eval do
  let e := mkCall2 "Int.Add" (mkFvar "x") (mkFvar "y")
  IO.println (repr (fmtStmt (mkAssert "known_add" e) #["x", "y"]))

/--
info: "assert [known_not]: !x;"
-/
#guard_msgs in
#eval do
  let e := mkCall1 "Bool.Not" (mkFvar "x")
  IO.println (repr (fmtStmt (mkAssert "known_not" e) #["x"]))

end Strata.Test.GenericCallFallback
