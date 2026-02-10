/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-!
# Datatype Support for DDM

This module provides datatype-related types and functions for the DDM, including
function templates and name pattern expansion.
This module is imported by `Strata.DDM.AST` and its types are re-exported there.
Most users should import `Strata.DDM.AST` rather than this module directly.

## Function Template System

Function templates specify patterns for generating auxiliary functions from datatype
declarations. Each template has:
- An iteration scope (perConstructor or perField)
- A name pattern for generating function names
- Parameter and return type specifications
-/

set_option autoImplicit false

public section
namespace Strata

/-! ## Function Template Types -/

/--
Iteration scope for function template expansion.
-/
inductive FunctionIterScope where
  /-- One function per constructor -/
  | perConstructor
  /-- One function per field (across all constructors) -/
  | perField
  deriving BEq, Repr, DecidableEq, Inhabited

/--
Type reference in a function specification, used to specify parameter and
 return types in function templates.
-/
inductive TypeRef where
  /-- The datatype being declared -/
  | datatype
  /-- The type of the current field -/
  | fieldType
  /-- A built-in type like "bool", "int" -/
  | builtin (name : String)
  deriving BEq, Repr, DecidableEq, Inhabited

/--
A part of a name pattern - either a literal string or a placeholder.
-/
inductive NamePatternPart where
  /-- A literal string to include verbatim in the generated name -/
  | literal (s : String)
  /-- Placeholder for the datatype name -/
  | datatype
  /-- Placeholder for the constructor name -/
  | constructor
  /-- Placeholder for the field name -/
  | field
  deriving BEq, Repr, DecidableEq, Inhabited

/--
A function template specification.
Describes how to generate additional functions based on datatype structure.
-/
structure FunctionTemplate where
  /-- Iteration scope -/
  scope : FunctionIterScope
  /-- Name pattern as structured parts -/
  namePattern : Array NamePatternPart
  /-- Parameter types (list of type references) -/
  paramTypes : Array TypeRef
  /-- Return type reference -/
  returnType : TypeRef
  deriving BEq, Repr, DecidableEq, Inhabited

/-! ## Name Pattern Functions -/

/--
Expand a name pattern with concrete values.
Each part is expanded based on its type:
- `literal s` → the literal string s
- `datatype` → the datatype name
- `constructor` → the constructor name (or empty string if not provided)
- `field` → the field name (or empty string if not provided)
-/
def expandNamePattern (pattern : Array NamePatternPart)
    (datatypeName : String)
    (constructorName : Option String := none)
    (fieldName : Option String := none) : String :=
  pattern.foldl (init := "") fun acc part =>
    acc ++ match part with
    | .literal s => s
    | .datatype => datatypeName
    | .constructor => constructorName.getD ""
    | .field => fieldName.getD ""

/--
Validate a name pattern for scope compatibility.
Returns `none` if valid, or `some errorMessage` if invalid.
- `perConstructor` scope cannot use `.field` placeholder
- `perField` scope cannot use `.constructor` placeholder
-/
def validateNamePattern (pattern : Array NamePatternPart) (scope : FunctionIterScope)
    : Option String :=
  match scope with
  | .perConstructor =>
    if pattern.any (· == .field) then
      some "Placeholder 'field' is not available in perConstructor scope"
    else
      none
  | .perField =>
    if pattern.any (· == .constructor) then
      some "Placeholder 'constructor' is not available in perField scope"
    else
      none

end Strata
end
