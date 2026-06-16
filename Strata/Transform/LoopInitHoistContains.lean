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

/-! ## `noExit` is preserved by the hoisting pass.

`noExit` is the residual fact `transportShape` needs beyond the four genuine
§E `.loop` arm Bool preconditions.  The §E arm carries `Block.noExit [.loop g m
inv body md] = true`, so `Block.noExit body = true`; to feed
`Block.transportShape_of_arm_preconds` on the POST-ORDER-PROCESSED body
`body₁ = (Block.hoistLoopPrefixInitsM body σ).1` we need
`Block.noExit (Block.hoistLoopPrefixInitsM body σ).1 = true`.

`noExit` is an `&&`-shaped structural Bool walker that descends `.block`/`.ite`
sub-blocks and a `.loop`'s body — exactly the shape of `loopMeasureNone`.  The
proof therefore mirrors the `loopMeasureNone` machinery in `LoopInitHoist`
exactly: distribute over `++`, exploit that a `.cmd`-only prelude has no exits,
and observe that `substIdent`/`applyRenames` leave the exit structure unchanged
(only identifiers are renamed; `.exit` labels are strings, untouched). -/

/-- `Block.noExit` distributes over `++`. -/
private theorem Block.noExit_append (xs ys : List (Stmt P (Cmd P))) :
    Block.noExit (xs ++ ys) = (Block.noExit xs && Block.noExit ys) := by
  induction xs with
  | nil => simp [Block.noExit]
  | cons x rest ih => simp [Block.noExit, ih, Bool.and_assoc]

/-- A list of `.cmd`s trivially has `noExit = true`. -/
private theorem Block.noExit_map_cmd (cs : List (Cmd P)) :
    Block.noExit (cs.map Stmt.cmd : List (Stmt P (Cmd P))) = true := by
  induction cs with
  | nil => simp [Block.noExit]
  | cons c rest ih =>
    simp [List.map_cons, Block.noExit, Stmt.noExit, ih]

/-! ### `substIdent` / `applyRenames` preserve `noExit`. -/

mutual
/-- `Stmt.substIdent` preserves `noExit` (renaming an identifier leaves the
`.exit` structure unchanged). -/
theorem Stmt.substIdent_noExit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (y y' : P.Ident) (s : Stmt P (Cmd P)) :
    Stmt.noExit (Stmt.substIdent y y' s) = Stmt.noExit s := by
  match s with
  | .cmd c => cases c <;> simp [Cmd.substIdent, Stmt.noExit]
  | .block lbl bss md =>
      simp only [Stmt.substIdent_block, Stmt.noExit]
      exact Block.substIdent_noExit y y' bss
  | .ite g tss ess md =>
      simp only [Stmt.substIdent_ite, Stmt.noExit]
      rw [Block.substIdent_noExit y y' tss,
          Block.substIdent_noExit y y' ess]
  | .loop g m inv bss md =>
      simp only [Stmt.substIdent_loop, Stmt.noExit]
      exact Block.substIdent_noExit y y' bss
  | .exit lbl md => simp [Stmt.noExit]
  | .funcDecl d md => simp [Stmt.noExit]
  | .typeDecl t md => simp [Stmt.noExit]
  termination_by sizeOf s

theorem Block.substIdent_noExit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (y y' : P.Ident) (ss : List (Stmt P (Cmd P))) :
    Block.noExit (Block.substIdent y y' ss) = Block.noExit ss := by
  match ss with
  | [] => simp [Block.noExit]
  | s :: rest =>
      simp only [Block.substIdent, Block.noExit]
      rw [Stmt.substIdent_noExit y y' s,
          Block.substIdent_noExit y y' rest]
  termination_by sizeOf ss
end

/-- `Block.applyRenames` preserves `noExit`. -/
theorem Block.applyRenames_noExit [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (renames : List (P.Ident × P.Ident)) (ss : List (Stmt P (Cmd P))) :
    Block.noExit (Block.applyRenames renames ss) = Block.noExit ss := by
  unfold Block.applyRenames
  induction renames generalizing ss with
  | nil => simp
  | cons p rest ih =>
      simp only [List.foldl_cons]
      rw [ih (Block.substIdent p.1 p.2 ss), Block.substIdent_noExit]

/-! ### The monadic pass preserves `noExit`.

The lift's residual is built from per-statement residuals; the `.cmd .init`
residual is a `.set` (no exit), `.block`/`.ite`/`.loop` keep their shape, and
no arm introduces an `.exit`.  The hoist `.loop` arm prepends a `.cmd`-only
havoc prelude and `applyRenames`s the lift residual; both preserve `noExit`. -/

mutual
private theorem Stmt.liftInitsInLoopBodyM_snd_noExit
    [HasIdent P] (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.noExit (Stmt.liftInitsInLoopBodyM s σ).1.2.2 =
      Stmt.noExit s := by
  match s with
  | .cmd c =>
      cases c <;>
        simp [Stmt.liftInitsInLoopBodyM, Block.noExit, Stmt.noExit]
  | .block lbl bss md =>
      rw [Stmt.liftInitsInLoopBodyM_block_residual]
      simp only [Block.noExit, Stmt.noExit, Bool.and_true]
      exact Block.liftInitsInLoopBodyM_snd_noExit bss σ
  | .ite g tss ess md =>
      rw [Stmt.liftInitsInLoopBodyM_ite_residual]
      simp only [Block.noExit, Stmt.noExit, Bool.and_true,
                 Block.liftInitsInLoopBodyM_snd_noExit tss σ,
                 Block.liftInitsInLoopBodyM_snd_noExit ess _]
  | .loop g m inv body md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.noExit, Stmt.noExit]
  | .exit lbl md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.noExit, Stmt.noExit]
  | .funcDecl d md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.noExit, Stmt.noExit]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBodyM, Block.noExit, Stmt.noExit]
  termination_by sizeOf s

private theorem Block.liftInitsInLoopBodyM_snd_noExit
    [HasIdent P] (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.noExit (Block.liftInitsInLoopBodyM ss σ).1.2.2 =
      Block.noExit ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBodyM, Block.noExit]
  | s :: rest =>
      rw [Block.liftInitsInLoopBodyM_cons_residual, Block.noExit_append,
          Stmt.liftInitsInLoopBodyM_snd_noExit s σ,
          Block.liftInitsInLoopBodyM_snd_noExit rest _, Block.noExit]
  termination_by sizeOf ss
end

mutual
private theorem Stmt.hoistLoopPrefixInitsM_noExit
    [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.noExit (Stmt.hoistLoopPrefixInitsM s σ).1 =
      Stmt.noExit s := by
  match s with
  | .cmd c =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.noExit, Stmt.noExit]
  | .block lbl bss md =>
      rw [Stmt.hoistLoopPrefixInitsM_block_out]
      simp only [Block.noExit, Stmt.noExit, Bool.and_true]
      exact Block.hoistLoopPrefixInitsM_noExit bss σ
  | .ite g tss ess md =>
      rw [Stmt.hoistLoopPrefixInitsM_ite_out]
      simp only [Block.noExit, Stmt.noExit, Bool.and_true,
                 Block.hoistLoopPrefixInitsM_noExit tss σ,
                 Block.hoistLoopPrefixInitsM_noExit ess _]
  | .loop g m inv body md =>
      rw [Stmt.hoistLoopPrefixInitsM_loop_out]
      have h_body :
          Block.noExit (Block.hoistLoopPrefixInitsM body σ).1 =
            Block.noExit body :=
        Block.hoistLoopPrefixInitsM_noExit body σ
      have h_lift :
          Block.noExit
            (Block.liftInitsInLoopBodyM (Block.hoistLoopPrefixInitsM body σ).1
              (Block.hoistLoopPrefixInitsM body σ).2).1.2.2 =
            Block.noExit body := by
        rw [Block.liftInitsInLoopBodyM_snd_noExit]; exact h_body
      rw [Block.noExit_append]
      simp only [Block.noExit_map_cmd, Block.noExit, Stmt.noExit,
                 Bool.true_and, Bool.and_true]
      rw [Block.applyRenames_noExit, h_lift]
  | .exit lbl md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.noExit, Stmt.noExit]
  | .funcDecl d md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.noExit, Stmt.noExit]
  | .typeDecl t md =>
      simp [Stmt.hoistLoopPrefixInitsM, Block.noExit, Stmt.noExit]
  termination_by sizeOf s

private theorem Block.hoistLoopPrefixInitsM_noExit
    [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.noExit (Block.hoistLoopPrefixInitsM ss σ).1 =
      Block.noExit ss := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInitsM, Block.noExit]
  | s :: rest =>
      rw [Block.hoistLoopPrefixInitsM_cons_out, Block.noExit_append,
          Stmt.hoistLoopPrefixInitsM_noExit s σ,
          Block.hoistLoopPrefixInitsM_noExit rest _, Block.noExit]
  termination_by sizeOf ss
end

end Imperative
