/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.Conversion
import Strata.Languages.Core.Statement
import Strata.Languages.Core.Expressions

---------------------------------------------------------------------

namespace Strata

---------------------------------------------------------------------

/- Integration between CoreAST/CoreCST and Core.Statement -/

-- Error types for Core integration
inductive CoreIntegrationError
  | unsupportedExpression (msg : String)
  | unsupportedStatement (msg : String)
  | unsupportedType (msg : String)
  | conversionError (msg : String)
  deriving Repr, BEq

-- Conversion from CoreAST to Core.Statement
def convertASTToCore : CoreASTDDM.Statement → Except CoreIntegrationError Core.Statement
  | .assert_stmt e => do
    -- For now, create a simple assert with placeholder expression
    let coreExpr : Core.Expression.Expr := .intConst () 0  -- placeholder
    return Core.Statement.assert "assert" coreExpr
  | .assume_stmt e => do
    let coreExpr : Core.Expression.Expr := .intConst () 0  -- placeholder
    return Core.Statement.assume "assume" coreExpr
  | .var_decl tp => do
    -- Create a variable declaration - need to generate identifier and type
    throw (.unsupportedStatement "variable declarations need more context")
  | .assign_stmt idx e => do
    -- Create assignment - need to resolve index to identifier
    throw (.unsupportedStatement "assignments need variable context")
  | .havoc_stmt idx => do
    -- Create havoc - need to resolve index to identifier
    throw (.unsupportedStatement "havoc needs variable context")
  | _ => throw (.unsupportedStatement "statement not yet supported")

-- Conversion from Core.Statement to CoreAST
def convertCoreToAST : Core.Statement → Except CoreIntegrationError CoreASTDDM.Statement
  | .assert label expr _ => do
    -- Convert Core expression to AST expression (placeholder)
    let astExpr : CoreASTDDM.Expression := .bool_true  -- placeholder
    return .assert_stmt astExpr
  | .assume label expr _ => do
    let astExpr : CoreASTDDM.Expression := .bool_true  -- placeholder
    return .assume_stmt astExpr
  | .init name ty expr _ => do
    -- Convert to variable declaration with initialization
    let astTy : Type := .builtin "int"  -- placeholder
    let astExpr : CoreASTDDM.Expression := .nat_lit 0  -- placeholder
    return .var_decl_init astTy astExpr
  | .set name expr _ => do
    -- Convert to assignment - need variable context to get index
    let astExpr : CoreASTDDM.Expression := .nat_lit 0  -- placeholder
    return .assign_stmt 0 astExpr  -- placeholder index
  | .havoc name _ => do
    return .havoc_stmt 0  -- placeholder index
  | _ => throw (.unsupportedStatement "Core statement not yet supported")

-- High-level conversion functions with context
structure CoreConversionContext where
  variables : List String  -- Variable names in scope
  nextVarIndex : Nat       -- Next available variable index

def CoreConversionContext.empty : CoreConversionContext :=
  { variables := [], nextVarIndex := 0 }

def CoreConversionContext.addVariable (ctx : CoreConversionContext) (name : String) : CoreConversionContext :=
  { ctx with variables := name :: ctx.variables, nextVarIndex := ctx.nextVarIndex + 1 }

def CoreConversionContext.lookupVariable (ctx : CoreConversionContext) (name : String) : Option Nat :=
  ctx.variables.findIdx? (· == name)

-- Convert CoreCST to Core.Statement via AST
def convertCSTToCore (cst : CoreCSTDDM.Statement) : Except String Core.Statement := do
  let ast ← cstToAST cst |>.mapError toString
  let core ← convertASTToCore ast |>.mapError toString
  return core

-- Convert Core.Statement to CoreCST via AST  
def convertCoreToCST (core : Core.Statement) : Except String CoreCSTDDM.Statement := do
  let ast ← convertCoreToAST core |>.mapError toString
  let cst ← astToCST ast |>.mapError toString
  return cst

-- Round-trip test: Core → CST → Core
def roundTripCore (core : Core.Statement) : Except String Core.Statement := do
  let cst ← convertCoreToCST core
  let core' ← convertCSTToCore cst
  return core'

---------------------------------------------------------------------

end Strata
