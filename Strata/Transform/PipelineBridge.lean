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

mutual
/-- `Stmt.containsFuncDecl s = false` implies `Stmt.noFuncDecl s = true`. -/
theorem Stmt.noFuncDecl_of_not_containsFuncDecl {P : PureExpr}
    (s : Stmt P (Cmd P)) (h : Stmt.containsFuncDecl s = false) :
    Stmt.noFuncDecl s = true := by
  match s with
  | .cmd c => rw [Stmt.noFuncDecl]
  | .block lbl bss md =>
      rw [Stmt.noFuncDecl]; rw [Stmt.containsFuncDecl] at h
      exact Block.noFuncDecl_of_not_containsFuncDecl bss h
  | .ite g tss ess md =>
      rw [Stmt.noFuncDecl, Bool.and_eq_true]
      rw [Stmt.containsFuncDecl, Bool.or_eq_false_iff] at h
      exact ⟨Block.noFuncDecl_of_not_containsFuncDecl tss h.1,
             Block.noFuncDecl_of_not_containsFuncDecl ess h.2⟩
  | .loop g m inv body md =>
      rw [Stmt.noFuncDecl]; rw [Stmt.containsFuncDecl] at h
      exact Block.noFuncDecl_of_not_containsFuncDecl body h
  | .exit lbl md => rw [Stmt.noFuncDecl]
  | .funcDecl d md => rw [Stmt.containsFuncDecl] at h; exact absurd h (by simp)
  | .typeDecl t md => rw [Stmt.noFuncDecl]
  termination_by sizeOf s

/-- `Block.containsFuncDecl ss = false` implies `Block.noFuncDecl ss = true`. -/
theorem Block.noFuncDecl_of_not_containsFuncDecl {P : PureExpr}
    (ss : List (Stmt P (Cmd P))) (h : Block.containsFuncDecl ss = false) :
    Block.noFuncDecl ss = true := by
  match ss with
  | [] => rw [Block.noFuncDecl]
  | s :: rest =>
      rw [Block.noFuncDecl, Bool.and_eq_true]
      rw [Block.containsFuncDecl, Bool.or_eq_false_iff] at h
      exact ⟨Stmt.noFuncDecl_of_not_containsFuncDecl s h.1,
             Block.noFuncDecl_of_not_containsFuncDecl rest h.2⟩
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

---------------------------------------------------------------------
/-! ## Section 4 — Direction B: structural simple-S2U preconditions on `hoist`

The simple-S2U theorem `structuredToUnstructured_sound` takes the hoist output
as its input program.  Its structural (shape-only) preconditions are discharged
here from hoist's preservation/postcondition lemmas:

  * `noFuncDecl = true`        — preserved (via `containsFuncDecl`),
  * `simpleShape = true`       — preserved (net-new chain in `LoopInitHoist`),
  * `loopBodyNoInits = true`   — established (hoist's raison d'être),
  * `loopHasNoInvariants = true` — preserved,
  * `noMeasureLoops = true`    — preserved (via `loopMeasureNone`).

The remaining simple-S2U preconditions (`uniqueInits`, `fresh_inits`,
`store_clean`, `NoGenSuffix`, `userLabelsDisjoint`) are NAME-level conditions
on the hoist output's `initVars`/`modVars`; see Section 5 for the obstruction
those raise for the composed pipeline. -/

variable {P : PureExpr}

/-- Direction B: hoist preserves `noFuncDecl` (via `containsFuncDecl`). -/
theorem hoist_noFuncDecl [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P))) (h : Block.noFuncDecl ss = true) :
    Block.noFuncDecl (Block.hoistLoopPrefixInits ss) = true :=
  Block.noFuncDecl_of_not_containsFuncDecl _
    (Block.hoistLoopPrefixInits_preserves_containsFuncDecl ss
      (Block.not_containsFuncDecl_of_noFuncDecl ss h))

/-- Direction B: hoist preserves `simpleShape`. -/
theorem hoist_simpleShape [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P))) (h : Block.simpleShape ss = true) :
    Block.simpleShape (Block.hoistLoopPrefixInits ss) = true :=
  Block.hoistLoopPrefixInits_preserves_simpleShape ss h

/-- Direction B: hoist establishes `loopBodyNoInits` (its raison d'être). -/
theorem hoist_loopBodyNoInits [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P))) :
    Block.loopBodyNoInits (Block.hoistLoopPrefixInits ss) = true :=
  Block.hoistLoopPrefixInits_preserves_loopBodyNoInits ss

/-- Direction B: hoist preserves `loopHasNoInvariants`. -/
theorem hoist_loopHasNoInvariants [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P))) (h : Block.loopHasNoInvariants ss = true) :
    Block.loopHasNoInvariants (Block.hoistLoopPrefixInits ss) = true :=
  Block.hoistLoopPrefixInits_preserves_loopHasNoInvariants ss h

/-- Direction B: hoist preserves `noMeasureLoops` (via `loopMeasureNone`). -/
theorem hoist_noMeasureLoops [HasIdent P] [HasSubstFvar P] [HasFvar P] [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P))) (h : Block.noMeasureLoops ss = true) :
    Block.noMeasureLoops (Block.hoistLoopPrefixInits ss) = true := by
  rw [← Block.loopMeasureNone_eq_noMeasureLoops] at h ⊢
  exact Block.hoistLoopPrefixInits_preserves_loopMeasureNone ss h

---------------------------------------------------------------------
/-! ## Section 5 — Store-condition bridges (from a clean initial store)

The three passes all run from the SAME initial environment `ρ₀`.  When `ρ₀`'s
store is everywhere `none` (the simple-S2U `store_clean` hypothesis), every
store-shaped precondition of the downstream passes is discharged uniformly:

  * nondetElim's `h_no_gen_suffix` (`ρ₀` undef on suffix-shaped names),
  * hoist §F's `h_hoist_undef` (`ρ₀` undef on the input's `initVars`),
  * hoist §F's `h_src_store_shapefree` (`ρ₀` undef on suffix-shaped names),
  * simple-S2U's `fresh_inits` (`ρ₀` undef on the input's `initVars`).

These are recorded as named helpers so the eventual end-to-end composition can
discharge them by a single appeal to `store_clean`. -/

/-- From a clean store, `ρ₀` is undefined on every suffix-shaped name — the
nondetElim `h_no_gen_suffix` / hoist `h_src_store_shapefree` shape. -/
theorem store_clean_no_gen_suffix [HasIdent P] {ρ₀ : Env P}
    (h_clean : ∀ ident : P.Ident, ρ₀.store ident = none) :
    ∀ s, String.HasUnderscoreDigitSuffix s →
      ρ₀.store (HasIdent.ident (P := P) s) = none :=
  fun _ _ => h_clean _

/-- From a clean store, `ρ₀` is undefined on every name in any list — the hoist
`h_hoist_undef` / simple-S2U `fresh_inits` shape. -/
theorem store_clean_undef_on [HasIdent P] {ρ₀ : Env P}
    (h_clean : ∀ ident : P.Ident, ρ₀.store ident = none)
    (xs : List P.Ident) :
    ∀ y ∈ xs, ρ₀.store y = none :=
  fun y _ => h_clean y

---------------------------------------------------------------------
/-! ## Section 6 — Composition obstruction: the shared `_<digits>` namespace

The structural bridges above (Sections 1–4) discharge every SHAPE-only
precondition of the chain.  The remaining preconditions are NAME-SHAPE
conditions, and they expose a genuine architectural obstruction that prevents
the three `_sound` theorems from composing as currently stated.

**Root cause.** All three passes mint fresh names with `StringGenState.gen`,
which produces strings of the form `pf ++ "_" ++ toString n` — every generated
name satisfies `String.HasUnderscoreDigitSuffix` (`gen_hasUnderscoreDigitSuffix`).
The passes use DISTINCT prefixes (`$__ndelim_ite$` / `$__ndelim_loop$` for
nondetElim, `_hoist` for hoist, `$__nondet_ite$` / `loop_entry$` / … for the
str2unstr translator), so the generated namespaces are PREFIX-disjoint.

But each pass's correctness theorem certifies that its own fresh names cannot
collide with the input by requiring the input to contain NO `_<digits>`-suffixed
name AT ALL — a SUFFIX-shape exclusion, not a prefix-disjointness one:

  * `nondetElim → hoist` (direction A) needs
      `Block.exprsShapeFree (Block.nondetElim ss)` and
      `Block.hoistedNamesFreshInRhsAndGuards (Block.nondetElim ss) = true`.
    Both are FALSE: nondetElim emits `.ite (.det (fvar g))` / `.loop (.det
    (fvar g))` guards whose read-var `g = $__ndelim_*$_n` is suffix-shaped, and
    `g` is simultaneously a top-level `init`-var.  `exprsShapeFree`'s `.loop`/
    `.ite` guard conjunct (`∀ suffix-shaped str, ident str ∉ getVars g`) and
    `hoistedNamesFreshInRhsAndGuards`'s `namesFreshInExprs (initVars _) _`
    conjunct each require `g ∉ getVars (fvar g) = [g]` for the suffix-shaped
    `g` — a contradiction.  (The guard conjunct of `exprsShapeFree` is
    load-bearing: the hoist §F `.loop` arm consumes it to prove the hoist
    targets are fresh in the loop guard.)

  * `hoist → str2unstr` (direction B) needs
      `NoGenSuffix (Block.initVars (Block.hoistLoopPrefixInits …))` and
      `NoGenSuffix (transformBlockModVars (Block.hoistLoopPrefixInits …))`.
    Both are FALSE: hoist lifts loop-body inits to top level under FRESH
    `_hoist_n` names, so the output's `initVars`/`modVars` contain
    `_hoist`-prefixed names that ARE `_<digits>`-suffixed — exactly what
    `NoGenSuffix` forbids.

**Why this is not a bridge lemma.** Discharging these would require the
downstream proof to certify collision-freedom via PREFIX-disjointness (its own
prefix vs. the upstream pass's prefix) instead of via the blanket SUFFIX-shape
exclusion currently baked into `exprsShapeFree` / `hoistedNamesFreshInRhsAndGuards`
/ `NoGenSuffix`.  That is a cross-cutting relaxation of the precondition
predicates threaded through all three large `_sound` proofs (the hoist §F
`.loop` arm and the str2unstr core simulation), i.e. a precondition redesign,
not an additive preservation lemma.  It is recorded here rather than papered
over with a false (vacuous-on-the-interesting-inputs) hypothesis. -/

---------------------------------------------------------------------
/-! ## Section 7 — Cross-pass foreignness of minted names

The kind-generalized soundness theorems (`nondetElim_sound_kind`,
`hoistLoopPrefixInits_preserves_kind`, `structuredToUnstructured_sound_kind`)
replace the blanket `HasUnderscoreDigitSuffix` exclusion of Section 6 with
per-kind reasoning, so the cross-pass name-shape preconditions become
*vacuous on foreign names*: each leaf has the form `∀ str, Q str → …`, and an
upstream-minted name `str` satisfies `¬ Q str` for the downstream kind `Q`,
discharging the implication trivially.

The two lemmas below supply that foreignness. Each refutes the downstream
`Kind` predicate on an upstream mint by showing the generator prefixes disagree
at character `0`: every disjunct of the downstream kind carries some literal
`HasGenPrefix pfᵢ` clause, but the upstream mint begins with a different literal
character, so `(pfᵢ ++ "_").toList.isPrefixOf _` is `false`. This mirrors the
template `hoist_name_not_ndelimKind` (which establishes the *other* direction of
this disjointness, hoist mint ∉ ndelimKind). -/

/-- A name minted by `nondetElim` (under `ndelimItePrefix` or `ndelimLoopPrefix`,
both beginning with `$`) is *not* a `hoistKind` label (`hoistFreshPrefix` begins
with `_`). This is the Direction-A foreignness fact: every read-var / init-var /
modified-var that `nondetElim` introduces is `ndelimKind`, hence `¬ hoistKind`,
so the hoist pass's `exprsShapeFree`/`*_shapefree` leaves are vacuous on the
`nondetElim` output. -/
theorem ndelim_name_not_hoistKind (sg : StringGenState) :
    ¬ hoistKind (StringGenState.gen ndelimItePrefix sg).1
  ∧ ¬ hoistKind (StringGenState.gen ndelimLoopPrefix sg).1 := by
  refine ⟨?_, ?_⟩ <;>
    · rw [StringGenState.gen_eq]
      rintro ⟨_, hpref, _⟩
      simp only [String.HasGenPrefix, hoistFreshPrefix, ndelimItePrefix,
        ndelimLoopPrefix, String.toList_append] at hpref
      simp [List.isPrefixOf] at hpref

/-- A name minted by `hoistLoopPrefixInits` (under `hoistFreshPrefix`, beginning
with `_`) is *not* an `s2uKind` label. Each of the thirteen `s2uKind` disjuncts
carries a literal generator prefix beginning with one of `i`, `$`, `l`, `m`,
`e`, `b` — and the parametric `block${l}$` disjunct always begins with `b` for
*every* `l` — none of which is `_`, so the hoist mint disagrees with each at
character `0`. This is the Direction-B foreignness fact: every `initVars` /
`transformBlockModVars` name the hoist pass freshly introduces is `hoistKind`,
hence `¬ s2uKind`, so the S2U pass's `NoGenSuffix` leaves are vacuous on the
hoist output's fresh names. -/
theorem hoist_name_not_s2uKind (sg : StringGenState) :
    ¬ StructuredToUnstructuredCorrect.s2uKind
        (StringGenState.gen hoistFreshPrefix sg).1 := by
  rw [StringGenState.gen_eq]
  -- Each disjunct yields `hpref : HasGenPrefix pfᵢ (hoistFreshPrefix ++ "_" ++ …)`.
  -- Unfold to a `List.isPrefixOf` over `toList`, then read off the prefix's head:
  -- for the twelve fixed prefixes `pfᵢ.toList` reduces to a literal `c :: …`, and
  -- for the parametric `block$⟨l⟩$` disjunct the head `toString "block$"` still
  -- reduces to `'b' :: …` even though `l` blocks full reduction.  In every case
  -- the head is `≠ '_'`, the head of the `hoistFreshPrefix` (`"_hoist"`) name, so
  -- the prefix relation is refuted by a head clash.
  rintro (⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ |
          ⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ |
          ⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ |
          ⟨l, _, hpref, _⟩) <;>
    simp only [String.HasGenPrefix, hoistFreshPrefix, String.toList_append] at hpref <;>
    · rw [List.isPrefixOf_iff_prefix] at hpref
      obtain ⟨t, ht⟩ := hpref
      simp only [String.toList, show (toString "block$") = "block$" from rfl] at ht
      exact absurd (List.cons.inj ht).1 (by decide)

end Imperative
