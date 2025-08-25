import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.LState
import Strata.DL.Imperative.Stmt
import Strata.DL.DataFlow
import Strata.DL.Generic.TranslationContext

---------------------------------------------------------------------

namespace HigherOrder

/-! ## Higher-Order Function Dialect

A higher-order function dialect for Strata that extends the Lambda dialect with:
- Function values that can be passed as arguments
- Function application with higher-order functions
- Arithmetic operations on basic values
- Integration with the Imperative dialect for statements and commands
-/

-- Higher-order function expressions extending Lambda dialect
inductive HOExpr where
  -- Include all Lambda expressions
  | lambda (e : Lambda.LExpr String)

  -- Higher-order specific operations
  | app : HOExpr → HOExpr → HOExpr                  -- Function application: f(arg)
  | arith : String → HOExpr → HOExpr → HOExpr       -- Arithmetic: x + y, x * y, etc.
  | ite : HOExpr → HOExpr → HOExpr → HOExpr         -- if-then-else: if c then t else e

  deriving Repr, DecidableEq, Nonempty

-- Helper functions for DataFlow interface
namespace HOExpr

-- Helper constructors for common Lambda expressions
def var (name : String) : HOExpr := .lambda (Lambda.LExpr.fvar name none)
def const (value : String) : HOExpr := .lambda (Lambda.LExpr.const value none)

-- Extract variable name from HOExpr
def extractVariableName (expr : HOExpr) : Option String :=
  match expr with
  | .lambda (Lambda.LExpr.fvar name _) => some name
  | _ => none

-- Extract data location from HOExpr for DataFlow
def extractDataLocation (expr : HOExpr) : DataFlow.DataLocation :=
  match expr with
  | .lambda (Lambda.LExpr.fvar name _) => DataFlow.DataLocation.variable name
  | .lambda (Lambda.LExpr.const value _) => DataFlow.DataLocation.literal value
  | .lambda (Lambda.LExpr.abs _ _) => DataFlow.DataLocation.variable "lambda_function"
  | .lambda _ => DataFlow.DataLocation.variable "lambda_expr"
  | .app _ _ => DataFlow.DataLocation.variable "app_result"
  | .arith op _ _ => DataFlow.DataLocation.variable s!"arith_{op}_result"
  | .ite _ _ _ => DataFlow.DataLocation.variable "ite_result"

end HOExpr

-- Define our expression system using HigherOrder dialect
abbrev HigherOrderStrataExpression : Imperative.PureExpr := {
  Ident := String,                    -- Simple string identifiers
  Expr := HOExpr,                     -- Higher-order expressions
  Ty := Lambda.LMonoTy,               -- Lambda types
  TyEnv := Std.HashMap String Lambda.LMonoTy,  -- Type environment
  EvalEnv := Lambda.LState String,    -- State for evaluation
  EqIdent := inferInstance            -- DecidableEq for String
}

-- Statements and commands parameterized by our higher-order expressions
abbrev HigherOrderStrataStatement := Imperative.Stmt HigherOrderStrataExpression (Imperative.Cmd HigherOrderStrataExpression)
abbrev HigherOrderStrataStatements := List HigherOrderStrataStatement
abbrev HigherOrderStrataCommand := Imperative.Cmd HigherOrderStrataExpression

-- Function definitions in the higher-order dialect
abbrev HigherOrderStrataFunction := Generic.StrataFunction HigherOrderStrataStatement Lambda.LMonoTy

-- Translation context for higher-order functions
abbrev HigherOrderTranslationContext := Generic.TranslationContext HigherOrderStrataStatement Lambda.LMonoTy

end HigherOrder
