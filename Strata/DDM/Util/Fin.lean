/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Extra declarations in Fin namespace
-/

namespace Fin

instance : Min (Fin n) where
  min x y := ⟨min x.val y.val, by omega⟩

inductive Range (n : Nat) where
| mk : Range n

namespace Range

instance : ForIn m (Range n) (Fin n) where
  forIn _ b f := loop f b 0
    where loop {m} [Monad m] {β} (f : Fin n → β → m (ForInStep β)) (b : β) (i : Nat) : m β :=
            if p : i < n then do
              match ← f ⟨i, p⟩ b with
              | .done b => pure b
              | .yield b => loop f b (i+1)
            else
              pure b

end Range

def range (n : Nat) : Range n := .mk
