/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.PtrCache

/-!
## Properties of the pointer-address caches

Key results:

- `run'_output_eq` / `run1'_output_eq` — the caches are transparent
  optimizations: running a cached computation from any starting cache yields
  exactly `f x`, guaranteed by the `Result.h` proof every entry carries.
-/

namespace Strata.PtrCache

public section

/-- **The pointer cache is a transparent optimization.** Running any
    `PtrCacheM f x` computation from any starting cache yields a value equal to
    `f x`, on the nose. The cache's (unobservable, squashed) contents cannot
    affect the result — this is guaranteed for free by the `Result.h` proof that
    every entry carries, so no separate correctness test is ever needed for a
    cache built on this interface. -/
theorem run'_output_eq {α β : Type} {f : α → β} {x : α}
    (m : PtrCacheM f x) (c : PtrCache f) : (m.run' c).output = f x :=
  (m.run' c).h

/-- The single-slot cache is a transparent optimization: running any
    `PtrCache1M f x` computation from any starting cache yields a value equal
    to `f x`. -/
theorem run1'_output_eq {α β : Type} {f : α → β} {x : α}
    (m : PtrCache1M f x) (c : PtrCache1 f) : (m.run' c).output = f x :=
  (m.run' c).h

end

end Strata.PtrCache
