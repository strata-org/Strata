/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkChainReplay
import all Strata.Languages.Core.Counterexample.BackLinkChainReplay

/-! # Properties of chain replay

Key theorems:
- `isTopLevelAt_of_isTopLevelAtB`: the executable check `isTopLevelAtB` accepting a
  counterexample's configuration means the counterexample starts at the top of the
  statements.
- `not_isTopLevelAt_of_isTopLevelAtB_false`: `isTopLevelAtB` rejecting it means it does
  not.
-/

namespace Core

open Imperative

public section

/-- A counterexample whose configuration the executable check `isTopLevelAtB` rejects
    does not start at the top of `stmts` (`isTopLevelAt`). -/
theorem not_isTopLevelAt_of_isTopLevelAtB_false
    {stmts : List (Stmt Expression Command)} {cex : CexA Expression Command}
    (h : isTopLevelAtB stmts cex.cfg = false) : ¬ isTopLevelAt stmts cex := by
  cases hcfg : cex.cfg <;> simp_all [isTopLevelAt, isTopLevelAtB]

/-- A counterexample whose configuration the executable check `isTopLevelAtB` accepts
    starts at the top of `stmts` (`isTopLevelAt`). -/
theorem isTopLevelAt_of_isTopLevelAtB
    {stmts : List (Stmt Expression Command)} {cex : CexA Expression Command}
    (h : isTopLevelAtB stmts cex.cfg = true) : isTopLevelAt stmts cex := by
  cases hcfg : cex.cfg <;> simp_all [isTopLevelAt, isTopLevelAtB]

end -- public section

end Core
