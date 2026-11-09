/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Lambda.LState

/-! ## Tests for `NameSupply.fresh` -/

meta section
namespace Lambda

/-- The names `fresh` generates, in order, for the base names `xs`, starting from `s`. -/
private def freshAll (xs : List String) (s : NameSupply := {}) : List String :=
  (xs.foldl (fun (acc, s) x => let (n, s) := s.fresh x; (n :: acc, s)) ([], s)).1.reverse

#guard freshAll ["x", "x", "x"] == ["x", "x@1", "x@2"]
#guard freshAll ["x", "y", "x", "y"] == ["x", "y", "x@1", "y@1"]

-- A used name is skipped.
#guard freshAll ["x", "x"] { usedNames := Std.HashSet.ofList ["x@1"] } == ["x", "x@2"]

-- After `x@4`, the next name with base `x` starts the search at suffix 4.
#guard freshAll ["x@4", "x"] == ["x@4", "x@5"]

end Lambda
end
