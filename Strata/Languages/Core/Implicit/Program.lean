/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Implicit.Procedure
public import Strata.Languages.Core.Program

/-!
# Core-implicit programs

A Core-implicit program mirrors Core's `Program` structure but uses
`Core.Implicit.Procedure` for its procedure declarations. Non-procedure
declarations (types, axioms, functions) are shared with Core-explicit
since they don't involve heap operations.
-/

namespace Core.Implicit

public section

open Core

/-- The schema of a composite (object) type: its declared fields (with Core
types) and the names of the types it extends. This carries the type information
that the explicit encoding reifies into `Field`/`TypeTag`/`ancestorsPerType`
datatypes — here it is kept as plain structured data a backend reads directly.
It describes the *object* a `Composite` reference points to; `Composite` itself
stays an opaque reference type (its fields are NOT projected onto the value). -/
structure ObjectType where
  /-- The composite type's name (e.g. `"Node"`). -/
  name : String
  /-- Declared fields, each with its Core type. -/
  fields : List (String × Expression.Ty)
  /-- Names of the types this composite extends (the subtype hierarchy). -/
  extending : List String
  deriving Inhabited

/-- A declaration in a Core-implicit program. Mirrors `Core.Decl` but
uses `Core.Implicit.Procedure` for procedure declarations, and adds an
`objectType` schema declaration for composite types (which the explicit path
erases into heap-encoding datatypes). -/
inductive Decl where
  | type (t : TypeDecl) (md : Imperative.MetaData Core.Expression)
  | ax (a : Axiom) (md : Imperative.MetaData Core.Expression)
  | distinct (name : Expression.Ident) (es : List Expression.Expr)
             (md : Imperative.MetaData Core.Expression)
  | proc (d : Procedure) (md : Imperative.MetaData Core.Expression)
  | func (f : Function) (md : Imperative.MetaData Core.Expression)
  | recFuncBlock (fs : List Function) (md : Imperative.MetaData Core.Expression)
  | objectType (t : ObjectType) (md : Imperative.MetaData Core.Expression)
  deriving Inhabited

/-- A Core-implicit program. -/
structure Program where
  /-- The ordered list of declarations. -/
  decls : List Decl
  /-- Core-explicit declarations preserved verbatim for the inverse transform
      (e.g., the `heapNew` procedure). These are not transformed to implicit
      representation; `toExplicit` emits them as-is. -/
  prelude : List Core.Decl := []
  deriving Inhabited

end

end Core.Implicit
