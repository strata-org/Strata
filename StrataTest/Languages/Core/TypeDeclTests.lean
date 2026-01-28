/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.TypeDecl

/-! ## Tests for TypeDecl -/

namespace Core
open Std (ToFormat Format format)
open Lambda.LTy.Syntax

/-- info: ∀[_ty0, _ty1, _ty2]. (Foo _ty0 _ty1 _ty2) -/
#guard_msgs in
#eval format $ TypeConstructor.toType { name := "Foo", numargs := 3 }

end Core
