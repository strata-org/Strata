/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Imperative.Cmd

namespace Imperative
open Std (ToFormat Format format)

---------------------------------------------------------------------

class TypeContext (P : PureExpr) (T : Type) where
  isBoolType   : P.Ty → Bool
  freeVars     : P.Expr → List P.Ident
  preprocess   : T → P.Ty → Except Format (P.Ty × T)
  postprocess  : T → P.Ty → Except Format (P.Ty × T)
  update       : T → P.Ident → P.Ty → T
  lookup       : T → P.Ident → Option P.Ty
  inferType    : T → Cmd P → P.Expr → Except Format (P.Expr × P.Ty × T)
  unifyTypes   : T → List (P.Ty × P.Ty) → Except Format T

---------------------------------------------------------------------
end Imperative
