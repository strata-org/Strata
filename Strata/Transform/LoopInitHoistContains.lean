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

/-! ## `noExit`: the structural "no `.exit` constructor anywhere" Bool walker.

This is a shape-only predicate (like `containsNondetLoop` / `containsFuncDecl`)
asserting a statement / block contains no `.exit` constructor. It scopes the
loop-init hoisting correctness statement to exit-free loop bodies: the body
correspondence the proof transports through is terminal-only, so a body that
can exit is out of scope. Defined here, upstream of both the correctness proof
and the Step-C producer, so both consume the same constant. -/
mutual
@[expose] def Stmt.noExit (s : Stmt P (Cmd P)) : Bool :=
  match s with
  | .cmd _ => true
  | .block _ bss _ => Block.noExit bss
  | .ite _ tss ess _ => Block.noExit tss && Block.noExit ess
  | .loop _ _ _ body _ => Block.noExit body
  | .exit _ _ => false
  | .funcDecl _ _ => true
  | .typeDecl _ _ => true
  termination_by sizeOf s

@[expose] def Block.noExit (ss : List (Stmt P (Cmd P))) : Bool :=
  match ss with
  | [] => true
  | s :: rest => Stmt.noExit s && Block.noExit rest
  termination_by sizeOf ss
end

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
