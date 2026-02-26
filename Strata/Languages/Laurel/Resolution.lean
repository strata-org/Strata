/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Util.Tactics

/-!
# Name Resolution Pass

Assigns a unique numeric ID to every definition and reference node in a
Laurel program, then resolves references to their definitions.

## Design

IDs are added directly to the AST nodes that represent definitions or
references. Specifically:

### Definition nodes (introduce a name into scope)
- `StmtExpr.LocalVariable` — local variable declaration
- `StmtExpr.Forall` / `StmtExpr.Exists` — quantifier-bound variable
- `Parameter` — procedure parameter
- `Procedure` — procedure definition
- `Field` — field on a composite type
- `CompositeType` / `ConstrainedType` / `DatatypeDefinition` — type definitions
- `DatatypeConstructor` — datatype constructor
- `Constant` — named constant

### Reference nodes (use a name)
- `StmtExpr.Identifier` — variable reference
- `StmtExpr.StaticCall` — static procedure call
- `StmtExpr.InstanceCall` — instance method call
- `StmtExpr.FieldSelect` — field access
- `StmtExpr.New` — object creation (references a type)
- `StmtExpr.Exit` — exit a labelled block
- `HighType.UserDefined` — type reference

Each of these nodes carries an `id : Nat` field (defaulting to `0`).
The ID assignment pass fills in unique values. The resolution pass then
builds a map from reference IDs to `AstNode` values describing the
definition each reference resolves to.
-/

namespace Strata.Laurel

/-! ## AstNode — the target of a resolved reference -/

/-- A definition-site AST node that a reference can resolve to. -/
inductive AstNode where
  /-- A local variable declaration. -/
  | localVariable (name : Identifier) (type : HighTypeMd)
  /-- A procedure parameter. -/
  | parameter (param : Parameter)
  /-- A static procedure. -/
  | staticProcedure (proc : Procedure)
  /-- An instance procedure (method) on a composite type. -/
  | instanceProcedure (typeName : Identifier) (proc : Procedure)
  /-- A field on a composite type. -/
  | field (typeName : Identifier) (fld : Field)
  /-- A composite type definition. -/
  | compositeType (ty : CompositeType)
  /-- A constrained type definition. -/
  | constrainedType (ty : ConstrainedType)
  /-- A datatype definition. -/
  | datatypeDefinition (ty : DatatypeDefinition)
  /-- A datatype constructor. -/
  | datatypeConstructor (typeName : Identifier) (ctor : DatatypeConstructor)
  /-- A constant. -/
  | constant (c : Constant)
  /-- A quantifier-bound variable. -/
  | quantifierVar (name : Identifier) (type : HighTypeMd)

/-! ## Resolution result -/

/-- The output of the resolution pass. -/
structure ResolutionResult where
  /-- The program with unique IDs on all definition and reference nodes. -/
  program : Program
  /-- Map from reference node ID to the definition it resolves to. -/
  refToDef : Std.HashMap Nat AstNode

/-! ## ID assignment -/

abbrev IdM := StateM Nat

/-- Allocate a fresh unique ID. -/
def freshId : IdM Nat := do
  let id ← get
  set (id + 1)
  return id
