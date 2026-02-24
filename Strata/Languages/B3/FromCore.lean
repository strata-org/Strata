/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.DefinitionAST
import Strata.Languages.Core.Expressions

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

/-- Convert Core expression to B3 expression, preserving metadata -/
partial def exprFromCore (e : Core.Expression.Expr) : Except ConversionError (B3AST.Expression SourceRange) :=
  .error (.unsupportedCoreExpr "not implemented")

end Strata.B3.FromCore
