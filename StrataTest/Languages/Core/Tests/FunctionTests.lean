/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Function

/-! ## Tests for Core Function -/

namespace Core
open Std (ToFormat Format format)
open Lambda
open LTy.Syntax LExpr.SyntaxMono

/-- info: ok: ∀[a, b]. (arrow int (arrow a (arrow b (arrow a a)))) -/
#guard_msgs in
#eval do let type ← LFunc.type (T:=CoreLParams)
                     ({ name := ⟨"Foo", ()⟩,
                        typeArgs := ["a", "b"],
                        inputs := [(⟨"w", ()⟩, mty[int]), (⟨"x", ()⟩, mty[%a]), (⟨"y", ()⟩, mty[%b]), (⟨"z", ()⟩, mty[%a])],
                        output := mty[%a],
                        body := some (LExpr.fvar () (⟨"x", ()⟩) none) } : Function)
         return format type

end Core
