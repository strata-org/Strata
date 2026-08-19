/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Pipeline.FactSet

/-! # Properties of canonical fact lists

Theorems about the default representation `FactSet.lean` defines:

* `nodup_canonFacts` — canonicalizing yields a duplicate-free list, because it
  filters the vocabulary's enumeration and that is duplicate-free.
* `CanonicalFactList.nodup` — hence every set built either way is
  duplicate-free.

Two lemmas about `canonFacts` stay with the definitions instead, because the
default `FactAlgebra` instance is built from them; the note there says so. -/

namespace Strata.Pipeline

public section

variable {F : Type} [FactVocabulary F]

/-- Canonicalizing a list yields a duplicate-free one, because it filters an
    enumeration that is duplicate-free. -/
theorem nodup_canonFacts (l : List F) : (canonFacts l).Nodup :=
  (FactVocabulary.all_nodup (F := F)).filter _

/-- The default representation is duplicate-free, whichever constructor built it. -/
theorem CanonicalFactList.nodup (σ : CanonicalFactList F) : σ.facts.Nodup := by
  have h : canonFacts σ.facts = σ.facts := σ.canonical
  rw [← h]
  exact nodup_canonFacts _

end -- public section

end Strata.Pipeline
