/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.PureExpr

public section

namespace Strata.Transform.GenSuffix

open Imperative

/-- `NoGenSuffix Q xs` says every ident in `xs` was supplied by user source —
i.e. is `HasIdent.ident s` only for strings `s` that do *not* satisfy the
label-kind predicate `Q` (the kind of label this pass mints). Instantiating
`Q := HasUnderscoreDigitSuffix` recovers the blanket "no statement writes a
gen-shaped variable" condition; a per-kind `Q` lets a composition partner
satisfy the obligation by minting under a disjoint prefix.

Lives in a low base module so multiple correctness passes can reuse it without
pulling in any heavy transform closure. -/
abbrev NoGenSuffix {P : PureExpr} [HasIdent P]
    (Q : String → Prop)
    (xs : List P.Ident) : Prop :=
  ∀ x ∈ xs, ∀ s : String,
    x = HasIdent.ident (P := P) s → ¬ Q s

end Strata.Transform.GenSuffix
