/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.Conversion

/-!
# B3 Conversion Error Tests

Tests for error handling in CST↔AST conversion.
-/

namespace StrataTest.B3.ConversionErrors

open Strata
open Strata.B3CST
open Strata.B3AST

/-- Convert CST expression to AST and return formatted error messages -/
def checkCSTToASTErrors (expr : B3CST.Expression Nat) : IO Unit := do
  let ctx := B3.FromCSTContext.empty
  let (_ast, errors) := B3.expressionFromCST ctx expr

  if errors.isEmpty then
    IO.println "No errors"
  else
    for err in errors do
      match err with
      | .unresolvedIdentifier name _metadata =>
          IO.println s!"Unresolved identifier '{name}'"

/-- Create a ToCSTContext from a list of variable names (in declaration order) -/
def mkContext (vars : List String) (inProcedure : Bool := false) : B3.ToCSTContext :=
  { vars := vars.reverse, inProcedure := inProcedure }

/-- Convert AST expression to CST and return formatted error messages -/
def checkASTToCSTErrors (ctx : B3.ToCSTContext) (expr : B3AST.Expression Nat) : IO Unit := do
  let (_cst, errors) := B3.expressionToCST ctx expr

  if errors.isEmpty then
    IO.println "No errors"
  else
    for err in errors do
      match err with
      | .variableOutOfBounds idx size _metadata =>
          IO.println s!"Variable @{idx} out of bounds (context size: {size})"
      | .unsupportedVariableReference idx _metadata =>
          IO.println s!"Variable @{idx} not supported in concrete syntax"

/--
info: Unresolved identifier 'undefinedVar'
-/
#guard_msgs in
#eval checkCSTToASTErrors (.id 42 "undefinedVar")

/--
info: Unresolved identifier 'foo'
Unresolved identifier 'bar'
-/
#guard_msgs in
#eval checkCSTToASTErrors (.add 5 (.id 10 "foo") (.id 20 "bar"))

/--
info: Unresolved identifier 'x'
Unresolved identifier 'y'
Unresolved identifier 'z'
-/
#guard_msgs in
#eval checkCSTToASTErrors (.add 0 (.mul 0 (.id 1 "x") (.id 2 "y")) (.id 3 "z"))

/--
info: No errors
-/
#guard_msgs in
#eval checkCSTToASTErrors (.natLit 100 42)

/--
info: No errors
-/
#guard_msgs in
#eval checkASTToCSTErrors (mkContext ["x", "y", "z"]) (.id 100 2)

/--
info: Variable @1 not supported in concrete syntax
-/
#guard_msgs in
#eval checkASTToCSTErrors (mkContext ["x", "x"]) (.id 120 1)

/--
info: No errors
-/
#guard_msgs in
#eval checkASTToCSTErrors (mkContext ["x", "x"] (inProcedure := true)) (.id 125 1)

/--
info: Variable @1 not supported in concrete syntax
-/
#guard_msgs in
#eval checkASTToCSTErrors (mkContext ["x", "x", "x"]) (.id 130 1)

/--
info: Variable @5 out of bounds (context size: 3)
-/
#guard_msgs in
#eval checkASTToCSTErrors (mkContext ["x", "y", "z"]) (.id 200 5)

/--
info: Variable @1 not supported in concrete syntax
Variable @1 not supported in concrete syntax
-/
#guard_msgs in
#eval checkASTToCSTErrors (mkContext ["x", "x", "x"])
  (.binaryOp 0 (.add 0) (.id 10 1) (.id 20 1))

end StrataTest.B3.ConversionErrors
