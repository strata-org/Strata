/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.Conversion
import Strata.Languages.B3.DDMTransform.DefinitionAST

/-!
# B3 Formatting Utilities

Helper functions for formatting B3 AST nodes to strings using DDM.
-/

namespace B3

open Strata

/-- Get metadata from B3 expression -/
def getExpressionMetadata (expr : B3AST.Expression SourceRange) : SourceRange :=
  match expr with
  | .literal m _ => m
  | .id m _ => m
  | .ite m _ _ _ => m
  | .binaryOp m _ _ _ => m
  | .unaryOp m _ _ => m
  | .functionCall m _ _ => m
  | .labeledExpr m _ _ => m
  | .letExpr m _ _ _ => m
  | .quantifierExpr m _ _ _ _ => m

/-- Format a DDM operation AST node to string -/
private def formatOp (prog : Program) (op : Operation) : String :=
  let fmtCtx := FormatContext.ofDialects prog.dialects prog.globalContext {}
  let fmtState : FormatState := { openDialects := prog.dialects.toList.foldl (init := {}) fun a (dialect : Dialect) => a.insert dialect.name }
  (mformat (ArgF.op op) fmtCtx fmtState).format.pretty.trimAscii.toString

/-- Format B3 statement to string -/
def formatStatement (prog : Program) (stmt : B3AST.Statement SourceRange) (ctx : ToCSTContext) : String :=
  let (cstStmt, _) := B3.stmtToCST ctx stmt
  formatOp prog cstStmt.toAst

/-- Format B3 expression to string -/
def formatExpression (prog : Program) (expr : B3AST.Expression SourceRange) (ctx : ToCSTContext) : String :=
  let (cstExpr, _) := B3.expressionToCST ctx expr
  formatOp prog cstExpr.toAst

end B3
