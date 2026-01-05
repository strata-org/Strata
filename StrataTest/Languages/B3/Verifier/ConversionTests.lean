/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.Conversion
import Strata.Languages.B3.DDMTransform.DefinitionAST

/-!
# B3 to SMT Conversion Tests

Tests for the B3 AST to SMT term conversion, including error handling.
-/

namespace StrataTest.B3.Verifier.Conversion

open Strata
open Strata.B3AST
open Strata.B3.Verifier
open Strata.SMT

---------------------------------------------------------------------
-- Test Helpers
---------------------------------------------------------------------

def testExpr (expr : Expression SourceRange) : Except ConversionError Term :=
  expressionToSMT ConversionContext.empty expr

def testExprWithCtx (ctx : ConversionContext) (expr : Expression SourceRange) : Except ConversionError Term :=
  expressionToSMT ctx expr

---------------------------------------------------------------------
-- Literal Conversion Tests
---------------------------------------------------------------------

/--
info: ✓ Integer literal conversion
-/
#guard_msgs in
#eval
  let expr := Expression.literal default (Literal.intLit default 42)
  match testExpr expr with
  | .ok _ => IO.println "✓ Integer literal conversion"
  | .error err => IO.println s!"✗ Conversion failed: {err}"

/--
info: ✓ Boolean literal conversion
-/
#guard_msgs in
#eval
  let expr := Expression.literal default (Literal.boolLit default true)
  match testExpr expr with
  | .ok _ => IO.println "✓ Boolean literal conversion"
  | .error err => IO.println s!"✗ Conversion failed: {err}"

---------------------------------------------------------------------
-- Variable Conversion Tests
---------------------------------------------------------------------

/--
info: ✓ Unbound variable error
-/
#guard_msgs in
#eval
  let expr := Expression.id default 0
  match testExpr expr with
  | .error (ConversionError.unboundVariable 0) => IO.println "✓ Unbound variable error"
  | .error other => IO.println s!"✗ Expected unboundVariable error, got {other}"
  | .ok _ => IO.println "✗ Expected error, got success"

/--
info: ✓ Bound variable conversion
-/
#guard_msgs in
#eval
  let ctx := ConversionContext.empty.push "x"
  let expr := Expression.id default 0
  match testExprWithCtx ctx expr with
  | .ok _ => IO.println "✓ Bound variable conversion"
  | .error err => IO.println s!"✗ Conversion failed: {err}"

---------------------------------------------------------------------
-- Binary Operation Tests
---------------------------------------------------------------------

/--
info: ✓ Addition conversion
-/
#guard_msgs in
#eval
  let lhs := Expression.literal default (Literal.intLit default 1)
  let rhs := Expression.literal default (Literal.intLit default 2)
  let expr := Expression.binaryOp default (BinaryOp.add default) lhs rhs
  match testExpr expr with
  | .ok _ => IO.println "✓ Addition conversion"
  | .error err => IO.println s!"✗ Conversion failed: {err}"

/--
info: ✓ Equality conversion
-/
#guard_msgs in
#eval
  let lhs := Expression.literal default (Literal.intLit default 5)
  let rhs := Expression.literal default (Literal.intLit default 5)
  let expr := Expression.binaryOp default (BinaryOp.eq default) lhs rhs
  match testExpr expr with
  | .ok _ => IO.println "✓ Equality conversion"
  | .error err => IO.println s!"✗ Conversion failed: {err}"

/--
info: ✓ Binary op error propagation
-/
#guard_msgs in
#eval
  let lhs := Expression.id default 0  -- Unbound
  let rhs := Expression.literal default (Literal.intLit default 2)
  let expr := Expression.binaryOp default (BinaryOp.add default) lhs rhs
  match testExpr expr with
  | .error (ConversionError.unboundVariable 0) => IO.println "✓ Binary op error propagation"
  | .error other => IO.println s!"✗ Expected unboundVariable error, got {other}"
  | .ok _ => IO.println "✗ Expected error, got success"

---------------------------------------------------------------------
-- Unary Operation Tests
---------------------------------------------------------------------

/--
info: ✓ Negation conversion
-/
#guard_msgs in
#eval
  let arg := Expression.literal default (Literal.intLit default 5)
  let expr := Expression.unaryOp default (UnaryOp.neg default) arg
  match testExpr expr with
  | .ok _ => IO.println "✓ Negation conversion"
  | .error err => IO.println s!"✗ Conversion failed: {err}"

/--
info: ✓ Logical not conversion
-/
#guard_msgs in
#eval
  let arg := Expression.literal default (Literal.boolLit default true)
  let expr := Expression.unaryOp default (UnaryOp.not default) arg
  match testExpr expr with
  | .ok _ => IO.println "✓ Logical not conversion"
  | .error err => IO.println s!"✗ Conversion failed: {err}"

---------------------------------------------------------------------
-- Conditional (ITE) Tests
---------------------------------------------------------------------

/--
info: ✓ If-then-else conversion
-/
#guard_msgs in
#eval
  let cond := Expression.literal default (Literal.boolLit default true)
  let thn := Expression.literal default (Literal.intLit default 1)
  let els := Expression.literal default (Literal.intLit default 2)
  let expr := Expression.ite default cond thn els
  match testExpr expr with
  | .ok _ => IO.println "✓ If-then-else conversion"
  | .error err => IO.println s!"✗ Conversion failed: {err}"

---------------------------------------------------------------------
-- Function Call Tests
---------------------------------------------------------------------

/--
info: ✓ Function call (no args)
-/
#guard_msgs in
#eval
  let fnName : Ann String SourceRange := ⟨default, "f"⟩
  let args : Ann (Array (Expression SourceRange)) SourceRange := ⟨default, #[]⟩
  let expr := Expression.functionCall default fnName args
  match testExpr expr with
  | .ok _ => IO.println "✓ Function call (no args)"
  | .error err => IO.println s!"✗ Conversion failed: {err}"

/--
info: ✓ Function call (with args)
-/
#guard_msgs in
#eval
  let fnName : Ann String SourceRange := ⟨default, "f"⟩
  let arg1 := Expression.literal default (Literal.intLit default 1)
  let arg2 := Expression.literal default (Literal.intLit default 2)
  let args : Ann (Array (Expression SourceRange)) SourceRange := ⟨default, #[arg1, arg2]⟩
  let expr := Expression.functionCall default fnName args
  match testExpr expr with
  | .ok _ => IO.println "✓ Function call (with args)"
  | .error err => IO.println s!"✗ Conversion failed: {err}"

---------------------------------------------------------------------
-- Quantifier Tests
---------------------------------------------------------------------

/--
info: ✓ Forall quantifier conversion
-/
#guard_msgs in
#eval
  let varName : Ann String SourceRange := ⟨default, "x"⟩
  let tyName : Ann String SourceRange := ⟨default, "int"⟩
  let patterns : Ann (Array (Pattern SourceRange)) SourceRange := ⟨default, #[]⟩
  let body := Expression.literal default (Literal.boolLit default true)
  let expr := Expression.quantifierExpr default
    (QuantifierKind.forall default) varName tyName patterns body
  match testExpr expr with
  | .ok _ => IO.println "✓ Forall quantifier conversion"
  | .error err => IO.println s!"✗ Conversion failed: {err}"

---------------------------------------------------------------------
-- Error Propagation Tests
---------------------------------------------------------------------

/--
info: ✓ Nested error propagation
-/
#guard_msgs in
#eval
  let unboundVar := Expression.id default 99
  let validLit := Expression.literal default (Literal.intLit default 1)
  let innerAdd := Expression.binaryOp default (BinaryOp.add default) unboundVar validLit
  let outerMul := Expression.binaryOp default (BinaryOp.mul default) innerAdd validLit
  match testExpr outerMul with
  | .error (ConversionError.unboundVariable 99) =>
      IO.println "✓ Nested error propagation"
  | .error other => IO.println s!"✗ Expected unboundVariable 99, got {other}"
  | .ok _ => IO.println "✗ Expected error, got success"

end StrataTest.B3.Verifier.Conversion
