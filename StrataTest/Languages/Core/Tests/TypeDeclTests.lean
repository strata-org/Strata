/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.TypeDecl

/-! ## Tests for TypeDecl -/

namespace Core
open Std (ToFormat Format format)
open Lambda.LTy.Syntax

/-- info: ∀[a, b, c]. (Foo a b c) -/
#guard_msgs in
#eval format $ TypeConstructor.toType { name := "Foo", params := ["a", "b", "c"] }

end Core
