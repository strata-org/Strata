/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.NondetElimCorrect
public import Strata.Transform.LoopInitHoistCorrect
public import Strata.Transform.StructuredToUnstructuredCorrect

-- `import all` to reach the (module-private) name-classification helpers from the
-- loop-init-hoist WF family and the `Block.initVars`/`modVars` distribution
-- lemmas they rely on; these discharge the Direction-B cross-pass leaves.
import all Strata.Transform.NondetElim
import all Strata.Transform.LoopInitHoistLoopArmWF

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

/-- A name minted by `nondetElim` (under `ndelimItePrefix`/`ndelimLoopPrefix`,
both beginning `$__ndelim_`) is *not* an `s2uKind` label.  Eleven of the thirteen
`s2uKind` prefixes disagree with `$` at character `0`; the two `$`-leading S2U
prefixes (`$__nondet_ite$`, `$__nondet_loop$`) agree through `$__n` but diverge at
character `4` (`o` vs. the ndelim `d`), so the prefix relation is still refuted by
a (deeper) head clash.  This is the Direction-B foreignness fact for the *ndelim*
names that survive into the hoist output's `initVars`/`modVars`: they are not
`s2uKind`, so the S2U `NoGenSuffix` leaves are vacuous on them. -/
theorem ndelim_name_not_s2uKind (sg : StringGenState) :
    ¬ StructuredToUnstructuredCorrect.s2uKind (StringGenState.gen ndelimItePrefix sg).1
  ∧ ¬ StructuredToUnstructuredCorrect.s2uKind (StringGenState.gen ndelimLoopPrefix sg).1 := by
  refine ⟨?_, ?_⟩ <;>
  · rw [StringGenState.gen_eq]
    rintro (⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ |
            ⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ |
            ⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ | ⟨_, hpref, _⟩ |
            ⟨_, _, hpref, _⟩) <;>
      simp only [String.HasGenPrefix, ndelimItePrefix, ndelimLoopPrefix,
        String.toList_append] at hpref <;>
      · rw [List.isPrefixOf_iff_prefix] at hpref
        obtain ⟨t, ht⟩ := hpref
        simp only [String.toList, show (toString "block$") = "block$" from rfl] at ht
        -- character 0 clash for the eleven non-`$` prefixes; character 4 clash
        -- (`o`/`n` vs. ndelim `d`) for the two `$`-leading nondet prefixes.
        first
          | exact absurd (List.cons.inj ht).1 (by decide)
          | exact absurd
              (List.cons.inj (List.cons.inj (List.cons.inj
                (List.cons.inj (List.cons.inj ht).2).2).2).2).1 (by decide)

---------------------------------------------------------------------
/-! ## Section 8 — Direction A: `nondetElim` output name classification

The hoist §F preconditions at `Q := hoistKind` (`exprsShapeFree`, the
`*_shapefree` `initVars`/`modVars` leaves) reach into the *whole* `nondetElim`
output, not just its source-inherited names.  Their leaves all have the shape
`∀ str, Q str → ident str ∉ …`, and to make them vacuous on the `nondetElim`
output we classify every name the pass can introduce:

  * every `initVars` / `modVars` name of the output is either a *source* name
    (inherited verbatim) or a freshly-minted `ndelimKind` guard ident, and
  * every read-var the output mentions is either a source read-var or, in the
    two `.nondet` arms, the freshly-minted guard `mkFvar (ndelim ident)` —
    which is `ndelimKind`, foreign to `hoistKind`.

The classification (`*_classified`) drives the `*_shapefree` leaves; the
`exprsShapeFree` preservation (`*_exprsShapeFree`) drives the guard leaf.  Both
are parametric in the downstream kind `Q` *and* a foreignness witness
(`¬ Q ndelim-name`), so instantiating `Q := hoistKind` with
`ndelim_name_not_hoistKind` discharges Direction A. -/

variable [HasIdent P] [HasFvar P] [HasBool P]

/-- `Block.initVars` distributes over list append. -/
theorem Block.initVars_append (xs ys : List (Stmt P (Cmd P))) :
    Block.initVars (xs ++ ys) = Block.initVars xs ++ Block.initVars ys := by
  induction xs with
  | nil => simp [Block.initVars]
  | cons x rest ih =>
      simp only [List.cons_append, Block.initVars_cons, ih, List.append_assoc]

/-- `Block.modifiedVars` distributes over list append. -/
theorem Block.modifiedVars_append (xs ys : List (Stmt P (Cmd P))) :
    Block.modifiedVars (xs ++ ys) = Block.modifiedVars xs ++ Block.modifiedVars ys := by
  induction xs with
  | nil => simp [Block.modifiedVars]
  | cons x rest ih =>
      simp only [List.cons_append, Block.modifiedVars, ih, List.append_assoc]

/-- An `init` command modifies nothing (it *defines*, not modifies). -/
private theorem init_modVars (x : P.Ident) (ty : P.Ty) (e : ExprOrNondet P)
    (md : MetaData P) :
    HasVarsImp.modifiedVars (HasInit.init (CmdT := Cmd P) x ty e md) =
      ([] : List P.Ident) := by
  with_unfolding_all rfl

/-- A `havoc x` command modifies exactly `[x]`. -/
private theorem havoc_modVars (x : P.Ident) (md : MetaData P) :
    HasVarsImp.modifiedVars (HasHavoc.havoc (CmdT := Cmd P) x md) = [x] := by
  with_unfolding_all rfl

mutual
/-- Every `initVars` element of the `nondetElim` output of a statement is either
an original source `initVars` element or a freshly-minted `ndelimKind` guard. -/
theorem Stmt.nondetElimM_initVars_classified
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    ∀ x ∈ Block.initVars (P := P) (Stmt.nondetElimM s σ).1,
      x ∈ Stmt.initVars s ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ ndelimKind str) := by
  match s with
  | .cmd c =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars, List.append_nil] at hx
      exact Or.inl hx
  | .block lbl bss md =>
      intro x hx
      rw [Stmt.nondetElimM_block_out] at hx
      simp only [Block.initVars_cons, Stmt.initVars_block, Block.initVars,
        List.append_nil] at hx ⊢
      exact Block.nondetElimM_initVars_classified bss σ x hx
  | .ite (.det e) tss ess md =>
      intro x hx
      rw [Stmt.nondetElimM_ite_det_out] at hx
      simp only [Block.initVars_cons, Stmt.initVars_ite, Block.initVars,
        List.append_nil, List.mem_append] at hx ⊢
      rcases hx with h | h
      · rcases Block.nondetElimM_initVars_classified tss σ x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_initVars_classified ess _ x h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .ite .nondet tss ess md =>
      intro x hx
      rw [Stmt.nondetElimM_ite_nondet_out] at hx
      rw [Block.initVars_cons] at hx
      rw [show Stmt.initVars (P := P)
            (Stmt.cmd (HasInit.init (HasIdent.ident (P := P) (StringGenState.gen ndelimItePrefix σ).1)
              HasBool.boolTy ExprOrNondet.nondet md)) =
            [HasIdent.ident (P := P) (StringGenState.gen ndelimItePrefix σ).1]
          from by with_unfolding_all rfl] at hx
      simp only [Stmt.initVars_ite, Block.initVars_cons, Block.initVars, List.append_nil,
        List.singleton_append, List.mem_cons, List.mem_append] at hx ⊢
      rcases hx with h_g | h_t | h_e
      · exact Or.inr ⟨(StringGenState.gen ndelimItePrefix σ).1, h_g, ndelimKind_gen.1 σ⟩
      · rcases Block.nondetElimM_initVars_classified tss _ x h_t with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_initVars_classified ess _ x h_e with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .loop (.det e) m inv body md =>
      intro x hx
      rw [Stmt.nondetElimM_loop_det_out] at hx
      simp only [Block.initVars_cons, Stmt.initVars_loop, Block.initVars,
        List.append_nil] at hx ⊢
      exact Block.nondetElimM_initVars_classified body σ x hx
  | .loop .nondet m inv body md =>
      intro x hx
      rw [Stmt.nondetElimM_loop_nondet_out] at hx
      rw [Block.initVars_cons] at hx
      rw [show Stmt.initVars (P := P)
            (Stmt.cmd (HasInit.init (HasIdent.ident (P := P) (StringGenState.gen ndelimLoopPrefix σ).1)
              HasBool.boolTy ExprOrNondet.nondet md)) =
            [HasIdent.ident (P := P) (StringGenState.gen ndelimLoopPrefix σ).1]
          from by with_unfolding_all rfl] at hx
      have h_havoc : Block.initVars (P := P)
          [Stmt.cmd (HasHavoc.havoc (HasIdent.ident (P := P) (StringGenState.gen ndelimLoopPrefix σ).1) md)] = [] := by
        with_unfolding_all rfl
      simp only [Stmt.initVars_loop, Block.initVars_cons, Block.initVars, List.append_nil,
        List.singleton_append, List.mem_cons] at hx ⊢
      rcases hx with h_g | h_body
      · exact Or.inr ⟨(StringGenState.gen ndelimLoopPrefix σ).1, h_g, ndelimKind_gen.2 σ⟩
      · rw [Block.initVars_append, h_havoc, List.append_nil] at h_body
        rcases Block.nondetElimM_initVars_classified body _ x h_body with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
  | .exit lbl md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars, Stmt.initVars,
        List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  | .funcDecl d md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars, Stmt.initVars,
        List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  | .typeDecl t md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars, Stmt.initVars,
        List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  termination_by sizeOf s

/-- Block-level `initVars` classification of the `nondetElim` output. -/
theorem Block.nondetElimM_initVars_classified
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ∀ x ∈ Block.initVars (P := P) (Block.nondetElimM ss σ).1,
      x ∈ Block.initVars ss ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ ndelimKind str) := by
  match ss with
  | [] =>
      intro x hx
      simp only [Block.nondetElimM, Block.initVars] at hx
      exact absurd hx List.not_mem_nil
  | s :: rest =>
      intro x hx
      rw [Block.nondetElimM_cons_out, Block.initVars_append] at hx
      simp only [List.mem_append] at hx
      rw [Block.initVars_cons, List.mem_append]
      rcases hx with h | h
      · rcases Stmt.nondetElimM_initVars_classified s σ x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_initVars_classified rest _ x h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  termination_by sizeOf ss
end

mutual
/-- Every `modifiedVars` element of the `nondetElim` output of a statement is
either an original source `modifiedVars` element or a freshly-minted
`ndelimKind` guard (the loop re-havoc target). -/
theorem Stmt.nondetElimM_modVars_classified
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    ∀ x ∈ Block.modifiedVars (P := P) (Stmt.nondetElimM s σ).1,
      x ∈ Stmt.modifiedVars s ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ ndelimKind str) := by
  match s with
  | .cmd c =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.modifiedVars, List.append_nil] at hx
      exact Or.inl hx
  | .block lbl bss md =>
      intro x hx
      rw [Stmt.nondetElimM_block_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx ⊢
      exact Block.nondetElimM_modVars_classified bss σ x hx
  | .ite (.det e) tss ess md =>
      intro x hx
      rw [Stmt.nondetElimM_ite_det_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil, List.mem_append] at hx ⊢
      rcases hx with h | h
      · rcases Block.nondetElimM_modVars_classified tss σ x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_modVars_classified ess _ x h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .ite .nondet tss ess md =>
      intro x hx
      rw [Stmt.nondetElimM_ite_nondet_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, init_modVars, List.nil_append,
        List.append_nil, List.mem_append] at hx ⊢
      rcases hx with h | h
      · rcases Block.nondetElimM_modVars_classified tss _ x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_modVars_classified ess _ x h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .loop (.det e) m inv body md =>
      intro x hx
      rw [Stmt.nondetElimM_loop_det_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx ⊢
      exact Block.nondetElimM_modVars_classified body σ x hx
  | .loop .nondet m inv body md =>
      intro x hx
      rw [Stmt.nondetElimM_loop_nondet_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, init_modVars, List.nil_append,
        List.append_nil] at hx ⊢
      rw [Block.modifiedVars_append] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, havoc_modVars, List.append_nil,
        List.mem_append, List.mem_singleton] at hx ⊢
      rcases hx with h | h_g
      · rcases Block.nondetElimM_modVars_classified body _ x h with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
      · exact Or.inr ⟨(StringGenState.gen ndelimLoopPrefix σ).1, h_g, ndelimKind_gen.2 σ⟩
  | .exit lbl md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  | .funcDecl d md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  | .typeDecl t md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  termination_by sizeOf s

/-- Block-level `modifiedVars` classification of the `nondetElim` output. -/
theorem Block.nondetElimM_modVars_classified
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ∀ x ∈ Block.modifiedVars (P := P) (Block.nondetElimM ss σ).1,
      x ∈ Block.modifiedVars ss ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ ndelimKind str) := by
  match ss with
  | [] =>
      intro x hx
      simp only [Block.nondetElimM, Block.modifiedVars] at hx
      exact absurd hx List.not_mem_nil
  | s :: rest =>
      intro x hx
      rw [Block.nondetElimM_cons_out, Block.modifiedVars_append] at hx
      simp only [List.mem_append] at hx
      simp only [Block.modifiedVars, List.mem_append]
      rcases hx with h | h
      · rcases Stmt.nondetElimM_modVars_classified s σ x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_modVars_classified rest _ x h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  termination_by sizeOf ss
end

variable [HasVarsPure P P.Expr] [LawfulHasFvar P] [LawfulHasIdent P]

/-- `Block.exprsShapeFree Q` distributes over list append. -/
theorem Block.exprsShapeFree_append {Q : String → Prop}
    (xs ys : List (Stmt P (Cmd P)))
    (h : Block.exprsShapeFree (P := P) Q xs ∧ Block.exprsShapeFree (P := P) Q ys) :
    Block.exprsShapeFree (P := P) Q (xs ++ ys) := by
  induction xs with
  | nil => simpa only [List.nil_append] using h.2
  | cons x rest ih =>
      rw [List.cons_append, Block.exprsShapeFree]
      rw [Block.exprsShapeFree] at h
      exact ⟨h.1.1, ih ⟨h.1.2, h.2⟩⟩

/-- A `.cmd (init _ _ .nondet _)` reads nothing, so it is `exprsShapeFree`. -/
private theorem init_nondet_sf {Q : String → Prop} (ident : P.Ident) (ty : P.Ty)
    (md : MetaData P) :
    Stmt.exprsShapeFree (P := P) Q (Stmt.cmd (HasInit.init ident ty ExprOrNondet.nondet md)) := by
  show Stmt.exprsShapeFree (P := P) Q (Stmt.cmd (Cmd.init ident ty ExprOrNondet.nondet md))
  simp only [Stmt.exprsShapeFree, ExprOrNondet.getVars]
  exact fun str _ hmem => absurd hmem List.not_mem_nil

/-- A `.cmd (havoc _)` reads nothing, so it is `exprsShapeFree`. -/
private theorem havoc_sf {Q : String → Prop} (ident : P.Ident) (md : MetaData P) :
    Stmt.exprsShapeFree (P := P) Q (Stmt.cmd (HasHavoc.havoc ident md)) := by
  show Stmt.exprsShapeFree (P := P) Q (Stmt.cmd (Cmd.set ident ExprOrNondet.nondet md))
  simp only [Stmt.exprsShapeFree, ExprOrNondet.getVars]
  exact fun str _ hmem => absurd hmem List.not_mem_nil

/-- The freshly minted ndelim guard ident is `∉ getVars` of any `Q`-foreign
read-var slot: the only read is `mkFvar ident` whose vars ⊆ `[ident]` and `ident`
carries the ndelim kind, foreign to `Q`. -/
private theorem ndelim_guard_fresh {Q : String → Prop}
    (pf : String) (σ : StringGenState)
    (hforeign : ¬ Q (StringGenState.gen pf σ).1) :
    ∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉
        HasVarsPure.getVars (P := P)
          (HasFvar.mkFvar (HasIdent.ident (P := P) (StringGenState.gen pf σ).1)) := by
  intro str hQ hmem
  have hin : HasIdent.ident (P := P) str ∈
      [HasIdent.ident (P := P) (StringGenState.gen pf σ).1] :=
    LawfulHasFvar.mkFvar_getVars (P := P) _ hmem
  rw [List.mem_singleton] at hin
  exact hforeign (LawfulHasIdent.ident_inj hin ▸ hQ)

/-- Transport `exprsShapeFree` across a `.loop` whose guard/body are replaced but
whose measure/invariants are unchanged: the measure/invariant freshness conjuncts
carry over verbatim from the source loop. -/
private theorem loop_sf_transport {Q : String → Prop} (g₀ g₁ : ExprOrNondet P)
    (m : Option P.Expr) (inv : List (String × P.Expr))
    (body₀ body₁ : List (Stmt P (Cmd P))) (md : MetaData P)
    (h : Stmt.exprsShapeFree (P := P) Q (.loop g₀ m inv body₀ md))
    (hg : ∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉ ExprOrNondet.getVars (P := P) g₁)
    (hb : Block.exprsShapeFree (P := P) Q body₁) :
    Stmt.exprsShapeFree (P := P) Q (.loop g₁ m inv body₁ md) := by
  rw [Stmt.exprsShapeFree.eq_def] at h ⊢
  exact ⟨hg, h.2.1, h.2.2.1, hb⟩

mutual
/-- `nondetElim` preserves `exprsShapeFree Q`, provided the labels it mints (the
two ndelim guard prefixes) are foreign to `Q`: source read-vars stay `Q`-free,
and the only new read-var is the freshly-minted guard ident, which is `¬ Q` by
foreignness. -/
theorem Stmt.nondetElimM_exprsShapeFree {Q : String → Prop}
    (hfi : ∀ sg, ¬ Q (StringGenState.gen ndelimItePrefix sg).1)
    (hfl : ∀ sg, ¬ Q (StringGenState.gen ndelimLoopPrefix sg).1)
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (h : Stmt.exprsShapeFree (P := P) Q s) :
    Block.exprsShapeFree (P := P) Q (Stmt.nondetElimM s σ).1 := by
  match s with
  | .cmd c =>
      simp only [Stmt.nondetElimM, Block.exprsShapeFree]
      exact ⟨h, trivial⟩
  | .block lbl bss md =>
      rw [Stmt.nondetElimM_block_out]
      simp only [Stmt.exprsShapeFree] at h
      simp only [Block.exprsShapeFree, Stmt.exprsShapeFree, and_true]
      exact Block.nondetElimM_exprsShapeFree hfi hfl bss σ h
  | .ite (.det e) tss ess md =>
      rw [Stmt.nondetElimM_ite_det_out]
      simp only [Stmt.exprsShapeFree] at h
      simp only [Block.exprsShapeFree, Stmt.exprsShapeFree, and_true]
      exact ⟨h.1, Block.nondetElimM_exprsShapeFree hfi hfl tss σ h.2.1,
             Block.nondetElimM_exprsShapeFree hfi hfl ess _ h.2.2⟩
  | .ite .nondet tss ess md =>
      rw [Stmt.nondetElimM_ite_nondet_out]
      simp only [Stmt.exprsShapeFree] at h
      simp only [Block.exprsShapeFree, and_true]
      refine ⟨init_nondet_sf _ _ _, ?_⟩
      simp only [Stmt.exprsShapeFree]
      refine ⟨ndelim_guard_fresh ndelimItePrefix σ (hfi σ),
              Block.nondetElimM_exprsShapeFree hfi hfl tss _ h.2.1,
              Block.nondetElimM_exprsShapeFree hfi hfl ess _ h.2.2⟩
  | .loop (.det e) m inv body md =>
      rw [Stmt.nondetElimM_loop_det_out]
      have hg : ∀ str : String, Q str →
          HasIdent.ident (P := P) str ∉ ExprOrNondet.getVars (P := P) (.det e) := by
        rw [Stmt.exprsShapeFree.eq_def] at h; exact h.1
      have hbody : Block.exprsShapeFree (P := P) Q body := by
        rw [Stmt.exprsShapeFree.eq_def] at h; exact h.2.2.2
      simp only [Block.exprsShapeFree, and_true]
      exact loop_sf_transport (.det e) (.det e) m inv body _ md h hg
        (Block.nondetElimM_exprsShapeFree hfi hfl body σ hbody)
  | .loop .nondet m inv body md =>
      rw [Stmt.nondetElimM_loop_nondet_out]
      have hbody : Block.exprsShapeFree (P := P) Q body := by
        rw [Stmt.exprsShapeFree.eq_def] at h; exact h.2.2.2
      simp only [Block.exprsShapeFree, and_true]
      refine ⟨init_nondet_sf _ _ _, ?_⟩
      refine loop_sf_transport .nondet
        (.det (HasFvar.mkFvar (HasIdent.ident (P := P) (StringGenState.gen ndelimLoopPrefix σ).1)))
        m inv body _ md h
        (ndelim_guard_fresh ndelimLoopPrefix σ (hfl σ)) ?_
      refine Block.exprsShapeFree_append _ _
        ⟨Block.nondetElimM_exprsShapeFree hfi hfl body _ hbody, ?_⟩
      simp only [Block.exprsShapeFree, and_true]
      exact havoc_sf _ _
  | .exit lbl md =>
      simp only [Stmt.nondetElimM, Block.exprsShapeFree, Stmt.exprsShapeFree, and_true]
  | .funcDecl d md =>
      simp only [Stmt.nondetElimM, Block.exprsShapeFree, Stmt.exprsShapeFree, and_true]
  | .typeDecl t md =>
      simp only [Stmt.nondetElimM, Block.exprsShapeFree, Stmt.exprsShapeFree, and_true]
  termination_by sizeOf s

/-- Block-level `exprsShapeFree Q` preservation through `nondetElim`. -/
theorem Block.nondetElimM_exprsShapeFree {Q : String → Prop}
    (hfi : ∀ sg, ¬ Q (StringGenState.gen ndelimItePrefix sg).1)
    (hfl : ∀ sg, ¬ Q (StringGenState.gen ndelimLoopPrefix sg).1)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h : Block.exprsShapeFree (P := P) Q ss) :
    Block.exprsShapeFree (P := P) Q (Block.nondetElimM ss σ).1 := by
  match ss with
  | [] =>
      simp only [Block.nondetElimM, Block.exprsShapeFree]
  | s :: rest =>
      rw [Block.nondetElimM_cons_out]
      simp only [Block.exprsShapeFree] at h
      exact Block.exprsShapeFree_append _ _
        ⟨Stmt.nondetElimM_exprsShapeFree hfi hfl s σ h.1,
         Block.nondetElimM_exprsShapeFree hfi hfl rest _ h.2⟩
  termination_by sizeOf ss
end

end Imperative
