/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

namespace Vector

@[inline]
def modify! (v : Vector α n) (i : Nat) (f : α → α) : Vector α n where
  toArray := v.toArray.modify i f
  size_toArray := Eq.trans Array.size_modify v.size_toArray

@[inline]
def modify (v : Vector α n) (i : Fin n) (f : α → α) : Vector α n := v.modify! i.val f

end Vector
