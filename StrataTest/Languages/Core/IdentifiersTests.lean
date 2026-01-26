/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Identifiers
import Strata.DL.Lambda.LExpr

namespace Core.Identifiers.Tests

open Core.Syntax
open Lambda.LTy.Syntax
open Lambda.LExpr.SyntaxMono

elab "eb[" e:lexprmono "]" : term => elabLExprMono (T:=⟨CoreExprMetadata, Visibility⟩) e

/--
info: Lambda.LExpr.op () (CoreIdent.unres "old")
  none : Lambda.LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
-/
#guard_msgs in
#check eb[~old]

/--
info: Lambda.LExpr.app () (Lambda.LExpr.op () (CoreIdent.unres "old") none)
  (Lambda.LExpr.fvar () (CoreIdent.unres "a")
    none) : Lambda.LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
-/
#guard_msgs in
#check eb[(~old a)]

/--
info: Lambda.LExpr.fvar () (CoreIdent.unres "x")
  (some (Lambda.LMonoTy.tcons "bool" [])) : Lambda.LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
-/
#guard_msgs in
#check eb[(x : bool)]

end Core.Identifiers.Tests
