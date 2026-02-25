/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.DefinitionAST
import Strata.Languages.Core.Expressions
import Strata.DDM.Util.SourceRange

/-!
# Core to B3 Expression Conversion

Converts Core expressions back to B3 expressions for display and diagnosis.
This is the inverse of the B3→Core translation in ToCore.lean.
-/

namespace Strata.B3.FromCore

open Strata.B3AST
open Core
open Lambda

/-- Conversion errors -/
inductive ConversionError where
  | unsupportedCoreExpr (expr : String)
  | typeMismatch (expected : String) (got : String)
  deriving Repr

instance : ToString ConversionError where
  toString e := match e with
    | .unsupportedCoreExpr expr => s!"Unsupported Core expression: {expr}"
    | .typeMismatch exp got => s!"Type mismatch: expected {exp}, got {got}"

/-- Helper to convert constants -/
def convertConst (sr : SourceRange) (c : Lambda.LConst) : Except ConversionError (B3AST.Expression SourceRange) :=
  match c with
  | Lambda.LConst.boolConst b => Except.ok (.literal sr (.boolLit sr b))
  | Lambda.LConst.intConst i => 
    if i >= 0 then
      Except.ok (.literal sr (.intLit sr i.natAbs))
    else
      Except.ok (.unaryOp sr (.neg sr) (.literal sr (.intLit sr i.natAbs)))
  | _ => Except.error (.unsupportedCoreExpr "unsupported constant")

mutual

/-- Helper to convert application expressions -/
partial def convertApp (sr : SourceRange) (fn arg : Core.Expression.Expr) : Except ConversionError (B3AST.Expression SourceRange) :=
  match fn with
  | Lambda.LExpr.app _ (Lambda.LExpr.op _ name _) lhs =>
    -- Binary operator
    (exprFromCore lhs).bind fun lhsB3 =>
    (exprFromCore arg).bind fun rhsB3 =>
    let opName := name.name
    if opName == "Int.Add" then Except.ok (.binaryOp sr (.add sr) lhsB3 rhsB3)
    else if opName == "Int.Sub" then Except.ok (.binaryOp sr (.sub sr) lhsB3 rhsB3)
    else if opName == "Int.Mul" then Except.ok (.binaryOp sr (.mul sr) lhsB3 rhsB3)
    else if opName == "Int.Div" then Except.ok (.binaryOp sr (.div sr) lhsB3 rhsB3)
    else if opName == "Int.Mod" then Except.ok (.binaryOp sr (.mod sr) lhsB3 rhsB3)
    else if opName == "Int.Lt" then Except.ok (.binaryOp sr (.lt sr) lhsB3 rhsB3)
    else if opName == "Int.Le" then Except.ok (.binaryOp sr (.le sr) lhsB3 rhsB3)
    else if opName == "Int.Gt" then Except.ok (.binaryOp sr (.gt sr) lhsB3 rhsB3)
    else if opName == "Int.Ge" then Except.ok (.binaryOp sr (.ge sr) lhsB3 rhsB3)
    else if opName == "Bool.And" then Except.ok (.binaryOp sr (.and sr) lhsB3 rhsB3)
    else if opName == "Bool.Or" then Except.ok (.binaryOp sr (.or sr) lhsB3 rhsB3)
    else if opName == "Bool.Implies" then Except.ok (.binaryOp sr (.implies sr) lhsB3 rhsB3)
    else if opName == "Eq" then Except.ok (.binaryOp sr (.eq sr) lhsB3 rhsB3)
    else if opName == "Neq" then Except.ok (.binaryOp sr (.neq sr) lhsB3 rhsB3)
    else Except.error (.unsupportedCoreExpr s!"binary operator {opName}")
  | Lambda.LExpr.op _ name _ =>
    -- Unary operator
    (exprFromCore arg).bind fun argB3 =>
    let opName := name.name
    if opName == "Bool.Not" then Except.ok (.unaryOp sr (.not sr) argB3)
    else if opName == "Int.Neg" then Except.ok (.unaryOp sr (.neg sr) argB3)
    else Except.error (.unsupportedCoreExpr s!"unary operator {opName}")
  | _ => Except.error (.unsupportedCoreExpr "unsupported function application")

/-- Convert Core expression to B3 expression, preserving source locations from Core metadata -/
partial def exprFromCore (e : Core.Expression.Expr) : Except ConversionError (B3AST.Expression SourceRange) :=
  let sr := match e with
    | Lambda.LExpr.const m _ => m
    | Lambda.LExpr.bvar m _ => m
    | Lambda.LExpr.app m _ _ => m
    | Lambda.LExpr.ite m _ _ _ => m
    | Lambda.LExpr.op m _ _ => m
    | Lambda.LExpr.fvar m _ _ => m
    | Lambda.LExpr.abs m _ _ => m
    | Lambda.LExpr.quant m _ _ _ _ => m
    | Lambda.LExpr.eq m _ _ => m
  match e with
  | Lambda.LExpr.const _ c => convertConst sr c
  | Lambda.LExpr.bvar _ idx => Except.ok (.id sr idx)
  | Lambda.LExpr.app _ fn arg => convertApp sr fn arg
  | Lambda.LExpr.ite _ cond thn els =>
    (exprFromCore cond).bind fun condB3 =>
    (exprFromCore thn).bind fun thnB3 =>
    (exprFromCore els).bind fun elsB3 =>
    Except.ok (.ite sr condB3 thnB3 elsB3)
  | _ => Except.error (.unsupportedCoreExpr "unsupported expression")

end

end Strata.B3.FromCore
