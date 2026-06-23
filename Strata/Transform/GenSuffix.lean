/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.PureExpr

public section

namespace Strata.Transform.GenSuffix

open Imperative

/-- `NoGenSuffix Q xs` says no name `xs` carries is the image of a `Q`-kind
string — equivalently, every ident in `xs` was supplied by user source.  Stated
*kind-first*: for every string `s` satisfying the label-kind predicate `Q` (the
kind of label this pass mints), `HasIdent.ident s` is absent from `xs`.
Instantiating `Q := HasUnderscoreDigitSuffix` recovers the blanket "no statement
writes a gen-shaped variable" condition; a per-kind `Q` lets a composition
partner satisfy the obligation by minting under a disjoint prefix.

The kind-first shape matches the leaf of `exprsShapeFree` and the consumer
freshness obligations downstream, so the threaded facts feed those consumers by
definitional unfolding.

Lives in a low base module so multiple correctness passes can reuse it without
pulling in any heavy transform closure. -/
abbrev NoGenSuffix {P : PureExpr} [HasIdent P]
    (Q : String → Prop)
    (xs : List P.Ident) : Prop :=
  ∀ s : String, Q s → HasIdent.ident (P := P) s ∉ xs

/-- Bridge to the membership-first reading: `NoGenSuffix Q xs` is equivalent to
"every ident in `xs` is `HasIdent.ident s` only for non-`Q` strings `s`".  The
two directions just reorder the binders and contrapose the final implication.
Provided for any site that prefers to build the predicate membership-first. -/
theorem noGenSuffix_iff_membFirst {P : PureExpr} [HasIdent P]
    (Q : String → Prop) (xs : List P.Ident) :
    NoGenSuffix (P := P) Q xs ↔
      ∀ x ∈ xs, ∀ s : String, x = HasIdent.ident (P := P) s → ¬ Q s := by
  constructor
  · intro h x hx s heq hQ
    exact h s hQ (heq ▸ hx)
  · intro h s hQ hmem
    exact h _ hmem s rfl hQ

end Strata.Transform.GenSuffix
