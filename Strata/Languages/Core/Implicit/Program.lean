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

/-- A declaration in a Core-implicit program. Mirrors `Core.Decl` but
uses `Core.Implicit.Procedure` for procedure declarations. -/
inductive Decl where
  | type (t : TypeDecl) (md : Imperative.MetaData Core.Expression)
  | ax (a : Axiom) (md : Imperative.MetaData Core.Expression)
  | distinct (name : Expression.Ident) (es : List Expression.Expr)
             (md : Imperative.MetaData Core.Expression)
  | proc (d : Procedure) (md : Imperative.MetaData Core.Expression)
  | func (f : Function) (md : Imperative.MetaData Core.Expression)
  | recFuncBlock (fs : List Function) (md : Imperative.MetaData Core.Expression)
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
