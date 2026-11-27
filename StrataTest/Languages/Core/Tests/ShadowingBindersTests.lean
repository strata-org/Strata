/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.ShadowingBinders
import Plausible

/-! # Fresh names for variables named like a function

`ShadowingBinders.freshRenaming` picks for `x` the first `x@k` such that neither it nor its
`old` form is taken. Here `x@1` to `x@3` are taken, and so are the `old` forms of `x@4` to
`x@6`: the six taken names refuse six candidates, and `x@7` is the first free one. -/

namespace Core.ShadowingBindersTests

private def taken : List String :=
  ["x@1", "x@2", "x@3", "old x@4", "old x@5", "old x@6"]

/-- info: [("x", "x@7"), ("old x", "old x@7")] -/
#guard_msgs in
#eval Core.ShadowingBinders.freshRenaming (taken.contains ·) taken.length ["x"]

/-! A variable named `x` and one literally named `old x` (as `|old x|` can be written), both
renamed together. `old x` is also the `old` form of `x`, one name in the program, so it has
one pair, `old x@1`, the `old` form of `x@1`, and every use of `old x` is renamed to it. -/

/-- info: [("x", "x@1"), ("old x", "old x@1")] -/
#guard_msgs in
#eval Core.ShadowingBinders.freshRenaming (fun _ => false) 0 ["x", "old x"]

/-- info: ["x@1", "old x@1", "old x@1", "y"] -/
#guard_msgs in
#eval (["x", "old x", "old x", "y"].map fun n =>
    (Core.ShadowingBinders.renameIdent
      (Core.ShadowingBinders.freshRenaming (fun _ => false) 0 ["x", "old x"])
      ⟨n, ()⟩).name)

/-! ## Property: fresh names are distinct and avoid every taken name

For random taken sets and binder lists drawn from names that collide on purpose (a name, its
`old` form, its `@k` forms and the `old` forms of those), the pairs `freshRenaming` returns
have distinct sources and distinct targets, and no target is taken. So the renaming is
injective and its new names, with their `old` forms, clash with nothing. -/

/-- Names that collide with each other on purpose. -/
private def pool : List String :=
  ["x", "y", "old x", "old y", "old old x", "x@1", "x@2", "x@3", "old x@1", "old x@2", "y@1",
    "old y@1", "x@1@1", "old x@1@1"]

/-- A random case: the taken names and the binders to rename. -/
private structure RCase where
  taken : List String
  xs : List String
  deriving Repr

open Plausible in
instance : Arbitrary RCase where
  arbitrary := do
    let pick : Gen String := do
      let i := (← Gen.choose Nat 0 (pool.length - 1) (by decide)).1
      pure (pool.getD i "x")
    let nt := (← Gen.choose Nat 0 8 (by omega)).1
    let nx := (← Gen.choose Nat 0 4 (by omega)).1
    pure ⟨← (List.range nt).mapM fun _ => pick, ← (List.range nx).mapM fun _ => pick⟩

open Plausible in
instance : Shrinkable RCase := ⟨fun _ => []⟩

/-- The property, on one case, with the binders deduplicated and not themselves taken, as the
    callers pass them. -/
private def freshOk (c : RCase) : Bool :=
  let xs := (c.xs.filter (!c.taken.contains ·)).eraseDups
  let ren := ShadowingBinders.freshRenaming (c.taken.contains ·) c.taken.length xs
  (ren.map (·.1)).Nodup && (ren.map (·.2)).Nodup && ren.all (!c.taken.contains ·.2)

/-- info: Unable to find a counter-example -/
#guard_msgs in
#eval Plausible.Testable.check (∀ c : RCase, freshOk c = true)
  { numInst := 2000, randomSeed := some 11 }

end Core.ShadowingBindersTests
