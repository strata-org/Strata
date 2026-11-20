/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Util.NameProofs

/-! # The fresh-name lemmas are usable from other modules

`Strata.Util.NameProofs` exports its lemmas, so a proof in another module can cite them
instead of carrying its own copies. -/

example (taken : Std.HashSet String) (base : String) :
    Strata.Name.freshName taken base ∉ taken :=
  Strata.Name.freshName_not_mem taken base

example (taken : String → Bool) (fuel : Nat) (base : String) (names : List String)
    (hall : ∀ n, taken n = true → n ∈ names) (hnames : names.length ≤ fuel) :
    taken (Strata.Name.freshNameBy taken fuel base) = false :=
  Strata.Name.freshNameBy_not_taken taken fuel base names hall hnames
