/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.DL.Lambda.Factory

/-! # A call whose instance is compared up to renaming of type variables

`opPair<a, b>(x : a, y : b) : bool` has no body, so a call to it stays and
shows its type annotation. `wrapPair` is an inline function whose body calls
`opPair`, with its type parameters named as given. -/

meta section

public section

namespace Lambda.RenamingFixtures

/-- Expressions with metadata type `M` and plain identifiers, as Core uses. -/
abbrev Params (M : Type) : LExprParams := ⟨M, Unit⟩

/-- `opPair(x, y)` with `opPair : a → b → bool`, `x : a` and `y : b`, every node
carrying metadata `m`. -/
def opPairCall {M : Type} (m : M) (a b : LMonoTy) : LExpr (Params M).mono :=
  .app m (.app m (.op m ⟨"opPair", ()⟩ (some (.arrow a (.arrow b .bool))))
    (.fvar m ⟨"x", ()⟩ (some a))) (.fvar m ⟨"y", ()⟩ (some b))

/-- `opPair<a, b>(x : a, y : b) : bool`, without a body. -/
def opPair {M : Type} : LFunc (Params M) :=
  LFunc.mk (name := ⟨"opPair", ()⟩) (typeArgs := ["a", "b"])
    (inputs := [(⟨"x", ()⟩, .ftvar "a"), (⟨"y", ()⟩, .ftvar "b")]) (output := .bool)

/-- The inline function `name<a, b>(x : a, y : b) : bool { opPair(x, y) }`. -/
def wrapPair {M : Type} (m : M) (name : String := "wrapPair") (a : TyIdentifier := "a")
    (b : TyIdentifier := "b") : LFunc (Params M) :=
  LFunc.mk (name := ⟨name, ()⟩) (typeArgs := [a, b])
    (inputs := [(⟨"x", ()⟩, .ftvar a), (⟨"y", ()⟩, .ftvar b)]) (output := .bool)
    (attr := #[.inline]) (body := some (opPairCall m (.ftvar a) (.ftvar b)))

end Lambda.RenamingFixtures

end -- public section
end
