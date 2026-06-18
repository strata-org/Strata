/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.Cmd
public import Strata.Transform.LoopInitHoist

import all Strata.DL.Imperative.Cmd
import all Strata.DL.Imperative.Stmt
import all Strata.Transform.LoopInitHoist

public section

namespace Imperative

variable {P : PureExpr}

/-! # `containsFuncDecl` preservation through the hoisting pass

The hoisting pass `Block.hoistLoopPrefixInits` threads the "no funcDecl
anywhere" structural invariant through its recursion, gating the merged
correctness proof's `loop_preserves_struct`.  The predicate is SHAPE-ONLY (it
inspects the statement tree, not variable names), so the fresh-name
substitution introduced by the monadic pass leaves it invariant.  The
monadic-pass postcondition is proven in `LoopInitHoist.lean`
(`hoistLoopPrefixInits_containsFuncDecl_eq`); here we package the `= false`
preservation corollary consumed downstream.
-/

/-- `Block.hoistLoopPrefixInits` preserves the "no funcDecl anywhere"
invariant. -/
theorem Block.hoistLoopPrefixInits_preserves_containsFuncDecl
    [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (body : List (Stmt P (Cmd P)))
    (h : Block.containsFuncDecl body = false) :
    Block.containsFuncDecl (Block.hoistLoopPrefixInits body) = false := by
  rw [Block.hoistLoopPrefixInits_containsFuncDecl_eq]; exact h

end Imperative
