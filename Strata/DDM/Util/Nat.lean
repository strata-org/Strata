/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public section
namespace Nat

/--
A fold over natural numbers similar to `Nat.fold` but with an optional starting argument.
-/
@[inline] def foldlM {α : Type u} {m : Type u → Type v} [Monad m] (n : Nat) (f : (i : Nat) → i < n → α → m α) (init : α) (start : Nat := 0) : m α :=
  if p : start < n then
    f start p init >>= n.foldlM f (start := start + 1)
  else
    pure init

end Nat
end
