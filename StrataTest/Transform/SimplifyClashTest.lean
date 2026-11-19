/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Transform.Simplify.Precondition

/-! # The clash `Laws` cannot rule out

`Laws` asks `StepWF` only at typings that agree with the formals of the factory's functions
with a body. A body with a variable named like such a formal at another type is outside what
the Simplify theorem covers, and `Block.clashesWithFormals` decides it. Lifting the
restriction needs `BodyAnnotated` to leave a function's own formals alone, since
substitution replaces them before any lookup. -/

meta section

namespace Core.Simplify.ClashTest

open Lambda Imperative

/-- `inc (n : int) : int := Int.Add(n, 1)`, and `Int.Add` without a body. -/
def factory : Lambda.Factory CoreLParams :=
  Factory.ofArray #[
    { name := ⟨"inc", ()⟩, inputs := [(⟨"n", ()⟩, .int)], output := .int,
      body := some (.app default (.app default (.op default ⟨"Int.Add", ()⟩ none)
        (.fvar default ⟨"n", ()⟩ (some .int))) (.intConst default 1)) },
    { name := ⟨"Int.Add", ()⟩, inputs := [(⟨"x", ()⟩, .int), (⟨"y", ()⟩, .int)],
      output := .int }]

/-- The entry typing: `m` is an `int`. -/
def Γ : VarTyping Expression := fun x =>
  if x = ⟨"m", ()⟩ then some (.forAll [] .int) else none

/-- `var x : ty;`, without a value. -/
def declare (x : String) (ty : LMonoTy) : Statement :=
  Statement.init ⟨x, ()⟩ (.forAll [] ty) .nondet .empty

/-- An assertion that reads `x`. -/
def assertOn (x : String) : Statement :=
  Statement.assert "a"
    (.eq default (.fvar default ⟨x, ()⟩ none) (.fvar default ⟨x, ()⟩ none)) .empty

-- No clash: `m` and `a` are not named like `inc`'s formal.
#guard !Block.clashesWithFormals factory Γ [declare "a" .int, assertOn "m"]

-- A local `n : bool` clashes with `inc`'s formal `n : int`.
#guard Block.clashesWithFormals factory Γ [declare "n" .bool, assertOn "n"]

-- At the formal's own type there is no clash.
#guard !Block.clashesWithFormals factory Γ [declare "n" .int, assertOn "n"]

-- A bodiless function's formal never clashes: `x : bool` against `Int.Add`'s `x : int`.
#guard !Block.clashesWithFormals factory Γ [declare "x" .bool, assertOn "x"]

-- A local in a nested scope is checked too.
#guard Block.clashesWithFormals factory Γ [.block "l" [declare "n" .bool] .empty]

end Core.Simplify.ClashTest

end
