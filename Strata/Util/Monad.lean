/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init

/-! # Successful completion of monadic computations

`MonadIsSuccess m` says which values a computation in `m` can complete
normally with. It lets a property of results be stated for a computation that
can fail, diverge or perform effects, such as an analyzer that calls an
external solver in `EIO`: the property constrains only the results the
computation returns.
-/

public section

/-- Computations in `m` that can complete normally, and the value they complete
    with. -/
class MonadIsSuccess (m : Type → Type) where
  /-- `x` can complete normally with `a`. -/
  IsSuccess {α : Type} : m α → α → Prop

/-- An `Except` computation completes normally with `a` when it is `.ok a`. -/
instance {ε : Type} : MonadIsSuccess (Except ε) where
  IsSuccess x a := x = .ok a

/-- An `EIO` computation completes normally with `a` when some run of it from
    some world returns `a`. -/
instance {ε : Type} : MonadIsSuccess (EIO ε) where
  IsSuccess x a := ∃ w w', (show EST ε IO.RealWorld _ from x) w = .ok a w'

end -- public section
