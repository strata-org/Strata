/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
Extra declarations in Fin namespace.

These are private so we do not extend Lean's namespaces.
-/
namespace Fin

instance {n} : Min (Fin n) where
  min x y := ⟨min x.val y.val, by omega⟩

/--
A range of natural numbers from 0 to n-1, used with `ForIn` to iterate over all
values of `Fin n`. Enables syntax like `for i in Fin.range 10 do ...`
-/
inductive Range (n : Nat) where
| mk : Range n

namespace Range

instance {m n} [Monad m] : ForIn m (Range n) (Fin n) where
  forIn _ b f := private loop f b 0
    where loop {m} [Monad m] {β} (f : Fin n → β → m (ForInStep β)) (b : β) (i : Nat) : m β :=
            if p : i < n then do
              match ← f ⟨i, p⟩ b with
              | .done b => pure b
              | .yield b => loop f b (i+1)
            else
              pure b

end Range

def range (n : Nat) : Range n := .mk

end Fin

public section
namespace Strata.Fin
export _root_.Fin(Range range)
end Strata.Fin

end
