/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

namespace GotoIR
open Std (ToFormat Format format)

-------------------------------------------------------------------------------

-- (TODO) Implement Ty.toIRep.

namespace Ty
/-
Ref.:
cbmc/src/util/std_types.h
cbmc/src/util/mathematical_types.h
-/

inductive BitVec where
  | SignedBV (size : Nat)
  | UnsignedBV (size : Nat)
  deriving Repr, Inhabited, DecidableEq

end Ty

inductive Ty where
  | Boolean
  | Integer
  | String
  | BitVector (bv : Ty.BitVec)
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Ty where
  format t := match t with
    | .Boolean => "bool"
    | .Integer => "int"
    | .String => "string"
    | .BitVector (.SignedBV n) => f!"signedbv[{n}]"
    | .BitVector (.UnsignedBV n) => f!"unsignedbv[{n}]"

-------------------------------------------------------------------------------

end GotoIR
