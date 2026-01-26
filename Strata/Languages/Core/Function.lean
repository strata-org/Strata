/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Core.Statement

---------------------------------------------------------------------

namespace Core

open Std (ToFormat Format format)
open Lambda

/-! # Strata Core Functions -/

abbrev Function := Lambda.LFunc CoreLParams

-- Type class instances to enable type class resolution for CoreLParams.Identifier
instance : DecidableEq CoreLParams.IDMeta :=
  show DecidableEq Visibility from inferInstance

instance : ToFormat CoreLParams.IDMeta :=
  show ToFormat Visibility from inferInstance

---------------------------------------------------------------------

end Core
