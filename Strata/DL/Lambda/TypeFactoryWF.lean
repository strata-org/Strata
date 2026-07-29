/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.TypeFactory

/-!
## Well-formedness of TypeFactory

A `TypeFactory` is well-formed when datatype names are unique across all
mutual blocks. Additional conditions will be added as needed.
-/

namespace Lambda

open Strata.DL.Util (TyIdentifier)

public section

/-- Well-formedness properties for a `TypeFactory`. -/
structure TypeFactoryWF {IDMeta : Type} (tf : @TypeFactory IDMeta) where
  /-- Datatype names are unique across all mutual blocks. -/
  name_nodup : (tf.allDatatypes.map (·.name)).Nodup

end -- public section
end Lambda
