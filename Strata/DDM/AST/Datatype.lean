/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-!
# Datatype Support for DDM

This module provides datatype-related types and functions for the Dialect Definition
Mechanism (DDM). It includes:

- **Function Templates**: A system for generating auxiliary functions (testers, accessors)
  from datatype declarations
- **Name Pattern Expansion**: Utilities for generating function names from patterns

## Function Template System

Function templates specify patterns for generating auxiliary functions from datatype
declarations. Each template has:
- An iteration scope (perConstructor, perField, or perConstructorField)
- A name pattern for generating function names
- Parameter and return type specifications

## Usage

This module is imported by `Strata.DDM.AST` and its types are re-exported there.
Most users should import `Strata.DDM.AST` rather than this module directly.

## Design Notes

The types in this module are intentionally kept dependency-free to allow them to be
defined separately from the main AST types. Functions that depend on `TypeExpr`,
`Arg`, `GlobalContext`, etc. remain in `AST.lean`.
-/

set_option autoImplicit false

public section
namespace Strata

/-! ## Function Template Types -/

/--
Iteration scope for function template expansion.
Determines how many functions are generated from a template.
-/
inductive FunctionIterScope where
  /-- One function per constructor -/
  | perConstructor
  /-- One function per field (across all constructors) -/
  | perField
  /-- One function per (constructor, field) pair -/
  | perConstructorField
  deriving BEq, Repr, DecidableEq, Inhabited

/--
Type reference in a function specification.
Used to specify parameter and return types in function templates.
-/
inductive TypeRef where
  /-- The datatype being declared -/
  | datatype
  /-- The type of the current field (only valid in perField/perConstructorField scope) -/
  | fieldType
  /-- A built-in type like "bool", "int" -/
  | builtin (name : String)
  deriving BEq, Repr, DecidableEq, Inhabited

/--
A part of a name pattern - either a literal string or a placeholder.
Used to construct function names from datatype/constructor/field information.
-/
inductive NamePatternPart where
  /-- A literal string to include verbatim in the generated name -/
  | literal (s : String)
  /-- Placeholder for the datatype name -/
  | datatype
  /-- Placeholder for the constructor name (only valid in perConstructor/perConstructorField) -/
  | constructor
  /-- Placeholder for the field name (only valid in perField/perConstructorField) -/
  | field
  /-- Placeholder for the field index (only valid in perField/perConstructorField) -/
  | fieldIndex
  deriving BEq, Repr, DecidableEq, Inhabited

/--
A function template specification.
Describes how to generate additional functions based on datatype structure.
-/
structure FunctionTemplate where
  /-- Iteration scope -/
  scope : FunctionIterScope
  /-- Name pattern as structured parts (type-safe, no string parsing needed) -/
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
- `fieldIndex` → the field index as a string (or empty string if not provided)
-/
def expandNamePattern (pattern : Array NamePatternPart)
    (datatypeName : String)
    (constructorName : Option String := none)
    (fieldName : Option String := none)
    (fieldIdx : Option Nat := none) : String :=
  pattern.foldl (init := "") fun acc part =>
    acc ++ match part with
    | .literal s => s
    | .datatype => datatypeName
    | .constructor => constructorName.getD ""
    | .field => fieldName.getD ""
    | .fieldIndex => fieldIdx.map toString |>.getD ""

/--
Validate a name pattern for scope compatibility.
Returns `none` if valid, or `some errorMessage` if invalid.
- `perConstructor` scope cannot use `.field` or `.fieldIndex` placeholders
- `perField` scope cannot use `.constructor` placeholder
- `perConstructorField` scope can use all placeholders
-/
def validateNamePattern (pattern : Array NamePatternPart) (scope : FunctionIterScope)
    : Option String :=
  match scope with
  | .perConstructor =>
    if pattern.any (· == .field) then
      some "Placeholder 'field' is not available in perConstructor scope"
    else if pattern.any (· == .fieldIndex) then
      some "Placeholder 'fieldIndex' is not available in perConstructor scope"
    else
      none
  | .perField =>
    if pattern.any (· == .constructor) then
      some "Placeholder 'constructor' is not available in perField scope"
    else
      none
  | .perConstructorField =>
    none

end Strata
end
