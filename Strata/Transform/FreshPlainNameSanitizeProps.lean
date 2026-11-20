/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.FreshPlainNameSanitize

/-! # Properties of `FreshPlainName.sanitize`

- `sanitize_noHash`: the result of `sanitize` has no `#`. The base of a name generated through
  it is therefore `#`-free; that the emitted name, the base with a freshness suffix, has no `#`
  is checked by tests, not proved here.
-/

public section

namespace Core.FreshPlainName

/-- **`sanitize` leaves no `#`.** -/
theorem sanitize_noHash (n : String) : '#' ∉ (sanitize n).toList := by
  unfold sanitize
  simp only [String.toList_map, List.mem_map, not_exists, not_and]
  intro c _ h
  split at h
  · cases h
  · rename_i hc; exact hc (by simpa using h)

end Core.FreshPlainName

end
