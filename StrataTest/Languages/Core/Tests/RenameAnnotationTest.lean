/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Expressions
meta import Strata.Languages.Core.ExpressionsProps
meta import Strata.DL.Imperative.Cmd

meta section

/-!
# Core identifier-rename annotation-preservation tests

The generic rename machinery (`substFvarManyExpr`) renames a free variable by
NAME, so on `Core.Expression` it must keep the variable's type annotation: a
type-annotated `x : int` renamed to `y` becomes `y : int`, not a bare `y`.
(Replacing the node with a freshly built `mkFvar` free variable would drop the
annotation, since `Core`'s `mkFvar` is `.fvar () · none`.) -/

namespace CoreRenameAnnotationTest
open Imperative Lambda

/-- A `Core.Expression` free variable `x` annotated with type `int`. -/
def xInt : Core.Expression.Expr := .fvar () ⟨"x", ()⟩ (some .int)

/-- The same variable renamed to `y`, still annotated with `int`. -/
def yInt : Core.Expression.Expr := .fvar () ⟨"y", ()⟩ (some .int)

-- Renaming `x ↦ y` on `x : int` yields `y : int`: the annotation is preserved,
-- NOT dropped to a bare `y`.
#guard substFvarManyExpr (P := Core.Expression) [(⟨"x", ()⟩, ⟨"y", ()⟩)] xInt == yInt

-- Complementary check: the result differs from the bare, unannotated `y`.
#guard (substFvarManyExpr (P := Core.Expression) [(⟨"x", ()⟩, ⟨"y", ()⟩)] xInt
          == (.fvar () ⟨"y", ()⟩ none : Core.Expression.Expr)) == false

-- An unrelated annotated variable is left untouched (name and annotation both).
#guard substFvarManyExpr (P := Core.Expression) [(⟨"x", ()⟩, ⟨"y", ()⟩)]
         (.fvar () ⟨"w", ()⟩ (some .int)) == (.fvar () ⟨"w", ()⟩ (some .int) : Core.Expression.Expr)

/-! ## Multi-pair renames on the real `Core.Expression` instance

The `#guard`s above and the single-pair cases exercise `Core.Expression` but
only with one rename pair. The two design choices of the rename list —
*simultaneous (non-cascading)* and *first-match* — are only observable with a
multi-pair list, so pin them directly on `Core.Expression` (not on the
`RenameTest` fixture's own `substAll`). -/

/-- `x : int`, `y : int`, `z : int` and an equality node `x == y` over `Core.Expression`. -/
def xI : Core.Expression.Expr := .fvar () ⟨"x", ()⟩ (some .int)
def yI : Core.Expression.Expr := .fvar () ⟨"y", ()⟩ (some .int)
def zI : Core.Expression.Expr := .fvar () ⟨"z", ()⟩ (some .int)

-- Simultaneous, non-cascading: renaming `[(x, y), (y, z)]` in `x == y` gives
-- `y == z`, NOT `z == z` — the `y` introduced by the first pair is not itself
-- re-renamed by the second. Annotations are carried through on both subterms.
#guard substFvarManyExpr (P := Core.Expression) [(⟨"x", ()⟩, ⟨"y", ()⟩), (⟨"y", ()⟩, ⟨"z", ()⟩)]
         (.eq () xI yI) == (.eq () yI zI : Core.Expression.Expr)

-- First-match: a duplicated source resolves through the FIRST matching pair, so
-- `[(x, y), (x, z)]` renames `x` to `y` (not `z`).
#guard substFvarManyExpr (P := Core.Expression) [(⟨"x", ()⟩, ⟨"y", ()⟩), (⟨"x", ()⟩, ⟨"z", ()⟩)]
         xI == (yI : Core.Expression.Expr)

/-! ## `Cmd.substIdentMany` — what the rewrite produces, per command kind

The binder-name lemmas in `CmdProps` pin which identifiers `substIdentMany`
exposes, but nothing pins the rewritten *value* positions. Pin them directly on
`Core.Expression` so a bug that skipped rewriting an `init`/`set` right-hand side
or an `assert` body would be caught: the renamed fvars inside each command must
follow the rename list (with annotations preserved), the `set` binder target
follows `renameLookup`, and the `init` binder is left unchanged. -/

open Imperative (Cmd ExprOrNondet)

-- `init w := (x == y)` under `[x ↦ x', y ↦ y']` rewrites the RHS fvars to `x' == y'`
-- while leaving the `init` binder `w` unchanged. The binder is deliberately NOT a
-- rename source — per `Cmd.substIdentMany`'s contract, the caller renames the
-- declaring occurrence, so the binder must not appear as a rename source here.
#guard Cmd.substIdentMany (P := Core.Expression)
         [(⟨"x", ()⟩, ⟨"x'", ()⟩), (⟨"y", ()⟩, ⟨"y'", ()⟩)]
         (.init ⟨"w", ()⟩ (.forAll [] .int) (.det (.eq () xI yI)) #[])
       == (Cmd.init ⟨"w", ()⟩ (.forAll [] .int)
             (.det (.eq () (.fvar () ⟨"x'", ()⟩ (some .int)) (.fvar () ⟨"y'", ()⟩ (some .int)))) #[]
            : Cmd Core.Expression)

-- `set x := y` under `[x ↦ x', y ↦ y']` rewrites BOTH the `set` binder target
-- (via `renameLookup`) and the RHS fvar to `set x' := y'`.
#guard Cmd.substIdentMany (P := Core.Expression)
         [(⟨"x", ()⟩, ⟨"x'", ()⟩), (⟨"y", ()⟩, ⟨"y'", ()⟩)]
         (.set ⟨"x", ()⟩ (.det yI) #[])
       == (Cmd.set ⟨"x'", ()⟩ (.det (.fvar () ⟨"y'", ()⟩ (some .int))) #[]
            : Cmd Core.Expression)

-- `assert "l" (x == y)` under `[x ↦ x', y ↦ y']` rewrites the asserted body's
-- fvars, keeping the label and annotations.
#guard Cmd.substIdentMany (P := Core.Expression)
         [(⟨"x", ()⟩, ⟨"x'", ()⟩), (⟨"y", ()⟩, ⟨"y'", ()⟩)]
         (.assert "l" (.eq () xI yI) #[])
       == (Cmd.assert "l"
             (.eq () (.fvar () ⟨"x'", ()⟩ (some .int)) (.fvar () ⟨"y'", ()⟩ (some .int))) #[]
            : Cmd Core.Expression)

/-! ## Nested terms: the rename descends through every compound constructor

A single term that nests `.quant` (trigger and body), `.abs`, `.ite`, `.app` and
`.eq`, with annotated free variables at depth. Under `[x ↦ x', y ↦ y']` every
occurrence of `x`/`y` is renamed with its `int` annotation kept, the off-source
`z` and the bound variables are untouched, and every binder name, binder type and
quantifier kind is carried through unchanged. -/

/-- `x' : int` and `y' : int`, the renamed counterparts of `xI` and `yI`. -/
def xI' : Core.Expression.Expr := .fvar () ⟨"x'", ()⟩ (some .int)
def yI' : Core.Expression.Expr := .fvar () ⟨"y'", ()⟩ (some .int)

/-- `∀ q : int {x}. (λ f : int. if (#0 x) then y else (x == z))`, built from the
fvars `x`, `y`, `z`. -/
def nestedTerm (x y z : Core.Expression.Expr) : Core.Expression.Expr :=
  .quant () .all "q" (some .int) x
    (.abs () "f" (some .int)
      (.ite () (.app () (.bvar () 0) x) y (.eq () x z)))

#guard substFvarManyExpr (P := Core.Expression)
         [(⟨"x", ()⟩, ⟨"x'", ()⟩), (⟨"y", ()⟩, ⟨"y'", ()⟩)]
         (nestedTerm xI yI zI)
       == nestedTerm xI' yI' zI

-- The rename really happened at depth: the result differs from the input.
#guard (substFvarManyExpr (P := Core.Expression)
          [(⟨"x", ()⟩, ⟨"x'", ()⟩), (⟨"y", ()⟩, ⟨"y'", ()⟩)]
          (nestedTerm xI yI zI)
        == nestedTerm xI yI zI) == false

/-! ## All constructors: a free-variable name rewrite that keeps annotations

Annotation preservation and structural recursion across every constructor hold
*by construction*: `Expression.renameFvars e subst` is defined as
`Expression.mapFvarNames (renameLookup subst) e`, and `mapFvarNames` rewrites
only each `.fvar m x ty`'s name (to `.fvar m (g x) ty`) while reconstructing
every other node unchanged — so each occurrence's metadata and type annotation
are carried through and every subterm is visited.  The `#guard`s above are
concrete illustrations; the definition is the coverage.  The two are
definitionally equal, so this holds by `rfl`. -/

example (e : Core.Expression.Expr) (s : List (Core.CoreIdent × Core.CoreIdent)) :
    Core.Expression.renameFvars e s
      = Core.Expression.mapFvarNames (renameLookup (P := Core.Expression) s) e :=
  rfl

end CoreRenameAnnotationTest

end
