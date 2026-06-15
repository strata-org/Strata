/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.NondetElimCorrect
public import Strata.Transform.LoopInitHoistCorrect
public import Strata.Transform.StructuredToUnstructuredCorrect

public section

namespace Imperative

/-! # Pipeline preservation bridges

This module proves the structural preservation lemmas that let the three
structured-to-unstructured passes chain end-to-end:

  `nondetElim` ▸ `hoistLoopPrefixInits` ▸ `stmtsToCFG`

The three soundness theorems are:
  * `nondetElim_sound` (`NondetElimCorrect`),
  * `hoistLoopPrefixInits_preserves` (`LoopInitHoistCorrect`, the §F theorem),
  * `structuredToUnstructured_sound` (`StructuredToUnstructuredCorrect`).

To compose them via `StoreAgreement.trans`, the OUTPUT of each pass must
satisfy the INPUT preconditions of the next.  This file establishes those
bridge facts as `Bool`-predicate / shape postconditions on the pass outputs.

## Direction A — `nondetElim` output ⊨ hoist §F preconditions

`nondetElim` only ever adds `init`/`ite (.det _)`/`loop (.det _)`/`havoc`
statements; it never adds invariants, measures, exits, or function
declarations, and (by its `simpleShape` postcondition) it removes every
nondeterministic loop.  Hence the structural §F preconditions are preserved
or established.

## Direction B — hoist output ⊨ simple-S2U preconditions

`hoistLoopPrefixInits` lifts loop-body inits and renames the lifted names; it
preserves the simple shape, the no-invariant / no-measure restrictions, and
establishes `loopBodyNoInits` (its raison d'être).
-/

---------------------------------------------------------------------
/-! ## Section 0 — `loopMeasureNone` ↔ `noMeasureLoops` reconciliation

The hoist §F precondition speaks of `Block.loopMeasureNone`
(`LoopInitHoist.lean`) while the simple-S2U precondition speaks of
`Block.noMeasureLoops` (`Stmt.lean`).  The two predicates have identical
recursion (`m.isNone && recurse`), so they are pointwise equal.  We prove
the equality once and use it to translate between the two namespaces. -/

mutual
/-- `Stmt.loopMeasureNone` and `Stmt.noMeasureLoops` are the same predicate. -/
theorem Stmt.loopMeasureNone_eq_noMeasureLoops {P : PureExpr}
    (s : Stmt P (Cmd P)) :
    Stmt.loopMeasureNone s = Stmt.noMeasureLoops s := by
  match s with
  | .cmd c => simp [Stmt.loopMeasureNone, Stmt.noMeasureLoops]
  | .block lbl bss md =>
      rw [Stmt.loopMeasureNone, Stmt.noMeasureLoops]
      exact Block.loopMeasureNone_eq_noMeasureLoops bss
  | .ite g tss ess md =>
      rw [Stmt.loopMeasureNone, Stmt.noMeasureLoops,
        Block.loopMeasureNone_eq_noMeasureLoops tss,
        Block.loopMeasureNone_eq_noMeasureLoops ess]
  | .loop g m inv body md =>
      rw [Stmt.loopMeasureNone, Stmt.noMeasureLoops,
        Block.loopMeasureNone_eq_noMeasureLoops body]
  | .exit lbl md => simp [Stmt.loopMeasureNone, Stmt.noMeasureLoops]
  | .funcDecl d md => simp [Stmt.loopMeasureNone, Stmt.noMeasureLoops]
  | .typeDecl t md => simp [Stmt.loopMeasureNone, Stmt.noMeasureLoops]
  termination_by sizeOf s

/-- `Block.loopMeasureNone` and `Block.noMeasureLoops` are the same predicate. -/
theorem Block.loopMeasureNone_eq_noMeasureLoops {P : PureExpr}
    (ss : List (Stmt P (Cmd P))) :
    Block.loopMeasureNone ss = Block.noMeasureLoops ss := by
  match ss with
  | [] => simp [Block.loopMeasureNone, Block.noMeasureLoops]
  | s :: rest =>
      rw [Block.loopMeasureNone, Block.noMeasureLoops,
        Stmt.loopMeasureNone_eq_noMeasureLoops s,
        Block.loopMeasureNone_eq_noMeasureLoops rest]
  termination_by sizeOf ss
end

---------------------------------------------------------------------
/-! ## Section 1 — `noFuncDecl` ↔ `containsFuncDecl` duality

`nondetElim` preserves `noFuncDecl` (proven in `NondetElim.lean`), while the
hoist §F precondition speaks of `containsFuncDecl = false`.  The two are exact
negations; we prove the direction we need: `noFuncDecl = true` implies
`containsFuncDecl = false`. -/

mutual
/-- `Stmt.noFuncDecl s = true` implies `Stmt.containsFuncDecl s = false`. -/
theorem Stmt.not_containsFuncDecl_of_noFuncDecl {P : PureExpr}
    (s : Stmt P (Cmd P)) (h : Stmt.noFuncDecl s = true) :
    Stmt.containsFuncDecl s = false := by
  match s with
  | .cmd c => rw [Stmt.containsFuncDecl]
  | .block lbl bss md =>
      rw [Stmt.containsFuncDecl]
      rw [Stmt.noFuncDecl] at h
      exact Block.not_containsFuncDecl_of_noFuncDecl bss h
  | .ite g tss ess md =>
      rw [Stmt.containsFuncDecl, Bool.or_eq_false_iff]
      rw [Stmt.noFuncDecl, Bool.and_eq_true] at h
      exact ⟨Block.not_containsFuncDecl_of_noFuncDecl tss h.1,
             Block.not_containsFuncDecl_of_noFuncDecl ess h.2⟩
  | .loop g m inv body md =>
      rw [Stmt.containsFuncDecl]
      rw [Stmt.noFuncDecl] at h
      exact Block.not_containsFuncDecl_of_noFuncDecl body h
  | .exit lbl md => rw [Stmt.containsFuncDecl]
  | .funcDecl d md => rw [Stmt.noFuncDecl] at h; exact absurd h (by simp)
  | .typeDecl t md => rw [Stmt.containsFuncDecl]
  termination_by sizeOf s

/-- `Block.noFuncDecl ss = true` implies `Block.containsFuncDecl ss = false`. -/
theorem Block.not_containsFuncDecl_of_noFuncDecl {P : PureExpr}
    (ss : List (Stmt P (Cmd P))) (h : Block.noFuncDecl ss = true) :
    Block.containsFuncDecl ss = false := by
  match ss with
  | [] => rw [Block.containsFuncDecl]
  | s :: rest =>
      rw [Block.containsFuncDecl, Bool.or_eq_false_iff]
      rw [Block.noFuncDecl, Bool.and_eq_true] at h
      exact ⟨Stmt.not_containsFuncDecl_of_noFuncDecl s h.1,
             Block.not_containsFuncDecl_of_noFuncDecl rest h.2⟩
  termination_by sizeOf ss
end

---------------------------------------------------------------------
/-! ## Section 2 — `simpleShape` excludes nondeterministic loops

`Block.simpleShape` admits a `.loop` only with a deterministic guard, so any
block satisfying `simpleShape` has `containsNondetLoop = false`.  Combined with
`nondetElim_simpleShape`, this discharges the hoist §F precondition
`containsNondetLoop (nondetElim ss) = false`. -/

mutual
/-- A simple-shape statement contains no nondeterministic loop. -/
theorem Stmt.not_containsNondetLoop_of_simpleShape {P : PureExpr}
    (s : Stmt P (Cmd P)) (h : Stmt.simpleShape s = true) :
    Stmt.containsNondetLoop s = false := by
  match s with
  | .cmd c => rw [Stmt.containsNondetLoop]
  | .block lbl bss md =>
      rw [Stmt.containsNondetLoop]
      rw [Stmt.simpleShape] at h
      exact Block.not_containsNondetLoop_of_simpleShape bss h
  | .ite (.det e) tss ess md =>
      rw [Stmt.containsNondetLoop, Bool.or_eq_false_iff]
      rw [Stmt.simpleShape, Bool.and_eq_true] at h
      exact ⟨Block.not_containsNondetLoop_of_simpleShape tss h.1,
             Block.not_containsNondetLoop_of_simpleShape ess h.2⟩
  | .ite .nondet tss ess md => rw [Stmt.simpleShape] at h; exact absurd h (by simp)
  | .loop (.det e) m inv body md =>
      rw [Stmt.containsNondetLoop]
      rw [Stmt.simpleShape, Bool.and_eq_true] at h
      exact Block.not_containsNondetLoop_of_simpleShape body h.2
  | .loop .nondet m inv body md =>
      rw [Stmt.simpleShape] at h; exact absurd h (by simp)
  | .exit lbl md => rw [Stmt.containsNondetLoop]
  | .funcDecl d md => rw [Stmt.containsNondetLoop]
  | .typeDecl t md => rw [Stmt.containsNondetLoop]
  termination_by sizeOf s

/-- A simple-shape block contains no nondeterministic loop. -/
theorem Block.not_containsNondetLoop_of_simpleShape {P : PureExpr}
    (ss : List (Stmt P (Cmd P))) (h : Block.simpleShape ss = true) :
    Block.containsNondetLoop ss = false := by
  match ss with
  | [] => rw [Block.containsNondetLoop]
  | s :: rest =>
      rw [Block.containsNondetLoop, Bool.or_eq_false_iff]
      rw [Block.simpleShape, Bool.and_eq_true] at h
      exact ⟨Stmt.not_containsNondetLoop_of_simpleShape s h.1,
             Block.not_containsNondetLoop_of_simpleShape rest h.2⟩
  termination_by sizeOf ss
end

---------------------------------------------------------------------
/-! ## Section 3 — Direction A: structural §F preconditions on `nondetElim`

The hoist §F theorem `hoistLoopPrefixInits_preserves` takes the `nondetElim`
output as its input program.  The structural (shape-only) §F preconditions are
discharged here from the corresponding facts on the source `ss`:

  * `containsNondetLoop = false`  — established (nondetElim removes nondet loops),
  * `containsFuncDecl = false`    — preserved (from `noFuncDecl`),
  * `loopHasNoInvariants = true`  — preserved,
  * `loopMeasureNone = true`      — preserved (via `noMeasureLoops`),
  * `noExit = true`               — preserved.

The `loopMeasureNone` and `noExit` preservations are net-new here; the other
three reuse the `nondetElim_*` postconditions from `NondetElim.lean`. -/

/-- nondetElim establishes the hoist §F `containsNondetLoop = false` precond. -/
theorem nondetElim_containsNondetLoop {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) :
    Block.containsNondetLoop (Block.nondetElim ss) = false :=
  Block.not_containsNondetLoop_of_simpleShape _ (nondetElim_simpleShape ss)

/-- nondetElim preserves `containsFuncDecl = false` (via `noFuncDecl`). -/
theorem nondetElim_containsFuncDecl {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (h : Block.noFuncDecl ss = true) :
    Block.containsFuncDecl (Block.nondetElim ss) = false :=
  Block.not_containsFuncDecl_of_noFuncDecl _ (nondetElim_noFuncDecl ss h)

/-! ### `noExit` preservation through the pass

`nondetElim` never introduces an `.exit`; it adds only `init`/`ite`/`loop`/
`havoc` statements.  We prove preservation by induction mirroring
`nondetElim_loopHasNoInvariants`. -/

/-- `Block.noExit` distributes over `++`. -/
theorem Block.noExit_append {P : PureExpr} (xs ys : List (Stmt P (Cmd P))) :
    Block.noExit (xs ++ ys) =
      (Block.noExit xs && Block.noExit ys) := by
  induction xs with
  | nil => simp [Block.noExit]
  | cons x rest ih => simp [Block.noExit, ih, Bool.and_assoc]

mutual
/-- `Stmt.nondetElimM` preserves `noExit`: the rewrite never emits an
`.exit` and passes through the body's exit structure unchanged (the only
new tail statement is a `havoc`, which is exit-free). -/
theorem Stmt.nondetElimM_noExit {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (h : Stmt.noExit s = true) :
    Block.noExit (Stmt.nondetElimM s σ).1 = true := by
  match s with
  | .cmd c => simp [Stmt.nondetElimM, Block.noExit, Stmt.noExit]
  | .block lbl bss md =>
      rw [Stmt.nondetElimM_block_out]
      simp only [Block.noExit, Stmt.noExit, Bool.and_true]
      rw [Stmt.noExit] at h
      exact Block.nondetElimM_noExit bss σ h
  | .ite (.det e) tss ess md =>
      rw [Stmt.nondetElimM_ite_det_out]
      rw [Stmt.noExit, Bool.and_eq_true] at h
      simp only [Block.noExit, Stmt.noExit, Bool.and_true,
                 Block.nondetElimM_noExit tss σ h.1,
                 Block.nondetElimM_noExit ess _ h.2]
  | .ite .nondet tss ess md =>
      rw [Stmt.nondetElimM_ite_nondet_out]
      rw [Stmt.noExit, Bool.and_eq_true] at h
      simp only [Block.noExit, Stmt.noExit, Bool.and_true,
                 Block.nondetElimM_noExit tss _ h.1,
                 Block.nondetElimM_noExit ess _ h.2]
  | .loop (.det e) m inv body md =>
      rw [Stmt.nondetElimM_loop_det_out]
      simp only [Block.noExit, Stmt.noExit, Bool.and_true]
      rw [Stmt.noExit] at h
      exact Block.nondetElimM_noExit body σ h
  | .loop .nondet m inv body md =>
      rw [Stmt.nondetElimM_loop_nondet_out]
      rw [Stmt.noExit] at h
      simp only [Block.noExit_append, Block.noExit, Stmt.noExit, Bool.and_true,
                 Block.nondetElimM_noExit body _ h]
  | .exit lbl md => exact absurd h (by simp [Stmt.noExit])
  | .funcDecl d md => simp [Stmt.nondetElimM, Block.noExit, Stmt.noExit]
  | .typeDecl t md => simp [Stmt.nondetElimM, Block.noExit, Stmt.noExit]
  termination_by sizeOf s

theorem Block.nondetElimM_noExit {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h : Block.noExit ss = true) :
    Block.noExit (Block.nondetElimM ss σ).1 = true := by
  match ss with
  | [] => simp [Block.nondetElimM, Block.noExit]
  | s :: rest =>
      rw [Block.noExit, Bool.and_eq_true] at h
      rw [Block.nondetElimM_cons_out, Block.noExit_append]
      simp only [Stmt.nondetElimM_noExit s σ h.1,
                 Block.nondetElimM_noExit rest _ h.2, Bool.and_true]
  termination_by sizeOf ss
end

/-- Top-level: `nondetElim` preserves `noExit`. -/
theorem nondetElim_noExit {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (h : Block.noExit ss = true) :
    Block.noExit (Block.nondetElim ss) = true :=
  Block.nondetElimM_noExit ss StringGenState.emp h

/-! ### `loopMeasureNone` preservation through the pass

The §F precond speaks of `loopMeasureNone`.  `nondetElim` already proves
`noMeasureLoops` preservation; we translate via Section 0's equality. -/

/-- Top-level: `nondetElim` preserves `loopMeasureNone` (via `noMeasureLoops`). -/
theorem nondetElim_loopMeasureNone {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (h : Block.loopMeasureNone ss = true) :
    Block.loopMeasureNone (Block.nondetElim ss) = true := by
  rw [Block.loopMeasureNone_eq_noMeasureLoops] at h ⊢
  exact nondetElim_noMeasureLoops ss h

end Imperative
