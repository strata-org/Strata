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

instance : ToString CoreIntegrationError where
  toString
  | .unsupportedExpression msg => s!"Unsupported expression: {msg}"
  | .unsupportedStatement msg => s!"Unsupported statement: {msg}"
  | .unsupportedType msg => s!"Unsupported type: {msg}"
  | .conversionError msg => s!"Conversion error: {msg}"

-- Conversion from CoreAST to Core.Statement
def convertASTToCore : CoreASTDDM.Statement Unit → Except CoreIntegrationError Core.Statement
  | _ => throw (.unsupportedStatement "conversion not implemented")

-- Conversion from Core.Statement to CoreAST
def convertCoreToAST : Core.Statement → Except CoreIntegrationError (CoreASTDDM.Statement Unit)
  | _ => throw (.unsupportedStatement "conversion not implemented")

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
def convertCSTToCore (cst : CoreCSTDDM.Statement Unit) : Except String Core.Statement := do
  let ast ← cstToAST cst |>.mapError toString
  let core ← convertASTToCore ast |>.mapError toString
  return core

-- Convert Core.Statement to CoreCST via AST  
def convertCoreToCST (core : Core.Statement) : Except String (CoreCSTDDM.Statement Unit) := do
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
