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

/-- Convert Core type to B3 type string -/
private def coreTypeToB3Type : LMonoTy → String
  | .tcons "int" _ => "int"
  | .tcons "bool" _ => "bool"
  | .tcons "string" _ => "string"
  | .tcons name _ => name
  | _ => "int"

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

private def binaryOpMap : Std.HashMap String (SourceRange → B3AST.BinaryOp SourceRange) :=
  Std.HashMap.ofList [
    ("Int.Add",      .add), ("Int.Sub",     .sub),
    ("Int.Mul",      .mul), ("Int.Div",     .div),
    ("Int.Mod",      .mod), ("Int.Lt",      .lt),
    ("Int.Le",       .le),  ("Int.Gt",      .gt),
    ("Int.Ge",       .ge),  ("Bool.And",    .and),
    ("Bool.Or",      .or),  ("Bool.Implies",.implies),
    ("Eq",           .eq),  ("Neq",         .neq)
  ]

private def unaryOpMap : Std.HashMap String (SourceRange → B3AST.UnaryOp SourceRange) :=
  Std.HashMap.ofList [("Bool.Not", .not), ("Int.Neg", .neg)]

mutual

/-- Helper to convert application expressions -/
partial def convertApp (sr : SourceRange) (fn arg : Core.Expression.Expr) : Except ConversionError (B3AST.Expression SourceRange) :=
  match fn with
  | Lambda.LExpr.app _ (Lambda.LExpr.op _ name _) lhs =>
    -- Binary operator
    (exprFromCore lhs).bind fun lhsB3 =>
    (exprFromCore arg).bind fun rhsB3 =>
    match binaryOpMap.get? name.name with
    | some mkOp => Except.ok (.binaryOp sr (mkOp sr) lhsB3 rhsB3)
    | none      => Except.error (.unsupportedCoreExpr s!"binary operator {name.name}")
  | Lambda.LExpr.op _ name _ =>
    -- Unary operator
    (exprFromCore arg).bind fun argB3 =>
    match unaryOpMap.get? name.name with
    | some mkOp => Except.ok (.unaryOp sr (mkOp sr) argB3)
    | none      => Except.error (.unsupportedCoreExpr s!"unary operator {name.name}")
  | Lambda.LExpr.fvar _ name _ =>
    -- Function call: f(arg)
    (exprFromCore arg).bind fun argB3 =>
    Except.ok (.functionCall sr ⟨sr, name.name⟩ ⟨sr, #[argB3]⟩)
  | Lambda.LExpr.app _ (Lambda.LExpr.fvar _ name _) firstArg =>
    -- Multi-arg function call: f(arg1, arg2, ...)
    (exprFromCore firstArg).bind fun firstB3 =>
    (exprFromCore arg).bind fun argB3 =>
    Except.ok (.functionCall sr ⟨sr, name.name⟩ ⟨sr, #[firstB3, argB3]⟩)
  | _ => Except.error (.unsupportedCoreExpr "unsupported function application")

/-- Convert Core expression to B3 expression, preserving source locations from Core metadata -/
partial def exprFromCore (e : Core.Expression.Expr) : Except ConversionError (B3AST.Expression SourceRange) :=
  match e with
  | Lambda.LExpr.const m c => convertConst m c
  | Lambda.LExpr.bvar m idx => Except.ok (.id m idx)
  | Lambda.LExpr.app m fn arg => convertApp m fn arg
  | Lambda.LExpr.ite m cond thn els =>
    (exprFromCore cond).bind fun condB3 =>
    (exprFromCore thn).bind fun thnB3 =>
    (exprFromCore els).bind fun elsB3 =>
    Except.ok (.ite m condB3 thnB3 elsB3)
  | Lambda.LExpr.fvar m name _ =>
    -- Free variable reference - represent as 0-arg function call
    Except.ok (.functionCall m ⟨m, name.name⟩ ⟨m, #[]⟩)
  | Lambda.LExpr.eq m lhs rhs =>
    (exprFromCore lhs).bind fun lhsB3 =>
    (exprFromCore rhs).bind fun rhsB3 =>
    Except.ok (.binaryOp m (.eq m) lhsB3 rhsB3)
  | Lambda.LExpr.quant m kind name tyOpt trigger body =>
    let qk := match kind with
      | .all => B3AST.QuantifierKind.forall m
      | .exist => B3AST.QuantifierKind.exists m
    -- Collect all nested quantifiers of the same kind into a var list
    let rec collectVars (e : Core.Expression.Expr) (idx : Nat) (acc : List (B3AST.VarDecl SourceRange)) :
        List (B3AST.VarDecl SourceRange) × Core.Expression.Expr :=
      match e with
      | Lambda.LExpr.quant (innerM : SourceRange) k innerName innerTyOpt _ innerBody =>
        if k == kind then
          let tyStr := match innerTyOpt with
            | some ty => coreTypeToB3Type ty
            | none => "int"
          let varName := if innerName.isEmpty then s!"x{idx}" else innerName
          let varDecl := B3AST.VarDecl.quantVarDecl innerM ⟨innerM, varName⟩ ⟨innerM, tyStr⟩
          collectVars innerBody (idx + 1) (acc ++ [varDecl])
        else (acc, e)
      | _ => (acc, e)
    let tyStr := match tyOpt with
      | some ty => coreTypeToB3Type ty
      | none => "int"
    let outerVarName := if name.isEmpty then "x0" else name
    let outerVar := B3AST.VarDecl.quantVarDecl m ⟨m, outerVarName⟩ ⟨m, tyStr⟩
    let (allVars, innerBody) := collectVars body 1 [outerVar]
    -- Convert trigger to patterns
    let patterns := match trigger with
      | Lambda.LExpr.boolConst _ true => #[]
      | _ =>
        match exprFromCore trigger with
        | .ok trigB3 => #[B3AST.Pattern.pattern m ⟨m, #[trigB3]⟩]
        | .error _ => #[]
    (exprFromCore innerBody).bind fun bodyB3 =>
    Except.ok (.quantifierExpr m qk ⟨m, allVars.toArray⟩ ⟨m, patterns⟩ bodyB3)
  | _ => Except.error (.unsupportedCoreExpr "unsupported expression")

end

end Strata.B3.FromCore
