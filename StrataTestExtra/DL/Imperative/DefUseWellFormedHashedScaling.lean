/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.Statement
meta import Strata.Languages.Core.Statement
meta import StrataTest.Util.Scaling

/-! # Scaling of the hashed def-use check

`Block.defUseWellFormedHashed` must stay linear in the length of a block. The test checks
a chain of `n` initializations, each reading the variable the previous one defined, at
`n = 1000` and `n = 8000`, keeping the fastest of five runs of each, and asserts the larger
takes under 32 times as long as the smaller, the bound `SimplifyScaling` uses. A linear check
gives a ratio near 8, quadratic cost near 64, so the bound leaves a factor of four for a
loaded host and rejects quadratic cost. The specification `Block.defUseWellFormed` nests one
closure per statement and is quadratic (101 times slower from 100 to 1000 statements), and
so is keeping the defined names in a list (75 times). The test reads the clock, so it runs
under `lake test` rather than `lake build`, where host load could fail the build. -/

namespace Strata.DefUseWellFormedHashedTest
open Core Lambda Imperative

private def var (i : Nat) : Expression.Expr := .fvar default ⟨s!"x{i}", ()⟩ (some .int)

/-- `var x1 := x0 + 1; var x2 := x1 + 1; …; var xn := x(n-1) + 1`. -/
private def chain (n : Nat) : List Statement :=
  (List.range n).map fun i =>
    Statement.init ⟨s!"x{i+1}", ()⟩ (.forAll [] .int)
      (.det (.app default (.app default (.op default ⟨"Int.Add", ()⟩ none) (var i))
        (.intConst default 1)))
      .empty

/-- The hashed check on a body whose only entry variable is `x0`. -/
private def check (ss : List Statement) : Bool :=
  Block.defUseWellFormedHashed (P := Expression) (C := Command) {}
    (fun x => x.name == "x0") (fun _ => true) ss

/-- info: true -/
#guard_msgs in
#eval StrataTest.Scaling.scalesUnder 32 check (chain 1000) (chain 8000)

end Strata.DefUseWellFormedHashedTest
