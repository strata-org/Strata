/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Std

/-! # List duplicate detection

Generic utility for finding duplicate elements in a list using `BEq` and
`Hashable` instances for O(n) detection.
-/

/-- Find elements that appear more than once in a list. Uses a HashMap
    for O(1) lookup per element. -/
public def List.findDuplicates [BEq α] [Hashable α] (xs : List α) : List α :=
  let map := xs.foldl (fun (m : Std.HashMap α (α × Nat)) x =>
    match m[x]? with
    | some (orig, n) => m.insert x (orig, n + 1)
    | none => m.insert x (x, 1)
  ) {}
  let revDups := map.fold (fun acc _ (orig, count) =>
    if count > 1 then orig :: acc else acc
  ) ([] : List α)
  revDups.reverse
