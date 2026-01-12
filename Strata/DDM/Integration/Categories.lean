/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST

namespace Strata.DDM.Integration

open Strata

/-- Init categories that map to primitive types (no interface/inductive needed) -/
def primitiveCategories : Std.HashSet QualifiedIdent := Std.HashSet.ofList [
  q`Init.Ident,
  q`Init.Num,
  q`Init.Decimal,
  q`Init.Str,
  q`Init.ByteArray,
  q`Init.Bool
]

/-- Init categories that are internal machinery (should error if used by dialects) -/
def forbiddenCategories : Std.HashSet QualifiedIdent := Std.HashSet.ofList [
  q`Init.TypeExpr,
  q`Init.BindingType,
  q`StrataDDL.Binding
]

/-- Init categories that are abstract extension points (dialects provide implementations) -/
def abstractCategories : Std.HashSet QualifiedIdent := Std.HashSet.ofList [
  q`Init.Expr,
  q`Init.Type,
  q`Init.TypeP
]

end Strata.DDM.Integration
