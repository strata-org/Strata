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
  * `structuredToUnstructured_sound_kind` (`StructuredToUnstructuredCorrect`).

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
  * `loopMeasureNone = true`      — preserved (via `noMeasureLoops`).

The hoist soundness theorem no longer requires the source to be exit-free, so no
`noExit` precondition is discharged here.  The `loopMeasureNone` preservation is
net-new here; the other two reuse the `nondetElim_*` postconditions from
`NondetElim.lean`. -/

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

-- No `noExit` bridge for `nondetElim`: a loop-body `.exit` in the user source is
-- admitted and faithfully simulated, so the composition need not carry `noExit`.

---------------------------------------------------------------------
/-! ## Section 4 — Direction B: structural simple-S2U preconditions on `hoist`

The simple-S2U theorem `structuredToUnstructured_sound_kind` takes the hoist output
as its input program.  Its structural (shape-only) preconditions are discharged
here from hoist's preservation/postcondition lemmas:

  * `noFuncDecl = true`        — preserved (via `containsFuncDecl`),
  * `simpleShape = true`       — preserved (net-new chain in `LoopInitHoist`),
  * `loopBodyNoInits = true`   — established (hoist's raison d'être),
  * `loopHasNoInvariants = true` — preserved,
  * `noMeasureLoops = true`    — preserved (via `loopMeasureNone`).

The remaining simple-S2U preconditions (`uniqueInits`, `fresh_inits`,
`store_gens`, `NoGenSuffix`, `userLabelsShapeNodup`) are NAME-level conditions
on the hoist output's `initVars`/`modVars`, discharged by the composition in
the sections that follow. -/

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
/-! ## Section 6 — Composition: from blanket suffix-shape to per-kind reasoning

The structural bridges above (Sections 1–4) discharge every SHAPE-only
precondition of the chain.  The remaining preconditions are NAME-SHAPE
conditions.  Under the original *blanket* statements they could not be
discharged, because each pass's correctness theorem certified collision-freedom
by requiring the input to contain NO `_<digits>`-suffixed name AT ALL — a
suffix-shape exclusion rather than a prefix-disjointness one:

  * `nondetElim → hoist` (direction A) needed
    `exprsShapeFree (Block.nondetElim ss)` and
    `hoistedNamesFreshInRhsAndGuards (Block.nondetElim ss)`.  Both are FALSE
    under the blanket reading: `nondetElim` emits `.ite (.det (fvar g))` /
    `.loop (.det (fvar g))` guards whose read-var `g = $__ndelim_*$_n` is
    suffix-shaped *and* is a top-level `init`-var, so the suffix-shape guard
    conjuncts demand `g ∉ getVars (fvar g) = [g]` — a contradiction.

  * `hoist → str2unstr` (direction B) needed
    `NoGenSuffix (initVars (hoist …))` and
    `NoGenSuffix (transformBlockModVars (hoist …))`, both FALSE because hoist
    lifts loop-body inits under fresh `_hoist_n` names, which are suffix-shaped.

**Resolution.**  The obstruction is dissolved on two axes, and the
chain is closed in `pipeline_sound` (Section 11):

  1. *Per-kind generalization.*  The three `_sound_kind` theorems replace the
     blanket `HasUnderscoreDigitSuffix` exclusion with a `Kind` predicate `Q`
     (`ndelimKind` / `hoistKind` / `s2uKind`).  The generated namespaces are
     prefix-disjoint (Section 7's foreignness lemmas: `ndelimKind`/`hoistKind`/
     `s2uKind` are pairwise non-overlapping), so each cross-pass name-shape leaf
     `∀ str, Q str → ident str ∉ …` is *vacuous on a foreign upstream name*
     (Sections 8–10's output classifications: every output read-var, init-var
     and mod-var is upstream-kind-or-source, hence `¬ Q`).

  2. *RHS-only freshness.*  The remaining obligation the per-kind axis does NOT
     cover — `hoistedNamesFreshInRhsAndGuards`, the `initVars`-freshness whose
     `.ite`/`.loop` *guard*-read clause is the false one above — is relaxed to
     `namesFreshInRhsExprs`, which checks only command-RHS read positions (the
     guard-read clauses were already dead in every consumption site of the hoist
     proof; guard agreement for a loop's body inits comes from their
     undefinedness at the loop head, discharged inside the loop driver).
     `nondetElim` then *preserves* this RHS-only freshness
     (`nondetElim_hoistedNamesFreshInRhsAndGuards`, Section 10), because it reads
     its fresh guard only in a guard, never in a command RHS.

No precondition is papered over with a false or vacuous-on-the-interesting-input
hypothesis: every `pipeline_sound` precondition is satisfiable by a clean
initial store and a shape-restricted, kind-free user program. -/

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
character, so `(pfᵢ ++ "_").toList.isPrefixOf _` is `false`. The reverse
disjointness (hoist mint ∉ ndelimKind) follows by the same head-clash argument
with the two prefixes swapped. -/

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

/-- Kind-level form of the Direction-A foreignness: any `ndelimKind` string is
not a `hoistKind` string.  (Unpacks the `ndelimKind` witness to a `gen` output
and applies `ndelim_name_not_hoistKind`.) -/
theorem ndelimKind_not_hoistKind {s : String} (h : ndelimKind s) : ¬ hoistKind s := by
  rcases h with ⟨sg, _, he⟩ | ⟨sg, _, he⟩
  · exact he ▸ (ndelim_name_not_hoistKind sg).1
  · exact he ▸ (ndelim_name_not_hoistKind sg).2

/-- Kind-level form: any `ndelimKind` string is not an `s2uKind` string. -/
theorem ndelimKind_not_s2uKind {s : String} (h : ndelimKind s) :
    ¬ StructuredToUnstructuredCorrect.s2uKind s := by
  rcases h with ⟨sg, _, he⟩ | ⟨sg, _, he⟩
  · exact he ▸ (ndelim_name_not_s2uKind sg).1
  · exact he ▸ (ndelim_name_not_s2uKind sg).2

/-- Kind-level form: any `hoistKind` string is not an `s2uKind` string. -/
theorem hoistKind_not_s2uKind {s : String} (h : hoistKind s) :
    ¬ StructuredToUnstructuredCorrect.s2uKind s := by
  obtain ⟨sg, _, he⟩ := h
  exact he ▸ hoist_name_not_s2uKind sg

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
theorem Stmt.nondetElimM_initVars_classified [HasIdent P] [HasFvar P] [HasBool P]
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
theorem Block.nondetElimM_initVars_classified [HasIdent P] [HasFvar P] [HasBool P]
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
theorem Stmt.nondetElimM_modVars_classified [HasIdent P] [HasFvar P] [HasBool P]
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
theorem Block.nondetElimM_modVars_classified [HasIdent P] [HasFvar P] [HasBool P]
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

/-- `Block.exprsShapeFree Q` distributes over list append. -/
theorem Block.exprsShapeFree_append [HasIdent P] [HasVarsPure P P.Expr] {Q : String → Prop}
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
private theorem init_nondet_sf [HasIdent P] [HasVarsPure P P.Expr] {Q : String → Prop} (ident : P.Ident) (ty : P.Ty)
    (md : MetaData P) :
    Stmt.exprsShapeFree (P := P) Q (Stmt.cmd (HasInit.init ident ty ExprOrNondet.nondet md)) := by
  show Stmt.exprsShapeFree (P := P) Q (Stmt.cmd (Cmd.init ident ty ExprOrNondet.nondet md))
  simp only [Stmt.exprsShapeFree, ExprOrNondet.getVars]
  exact fun str _ hmem => absurd hmem List.not_mem_nil

/-- A `.cmd (havoc _)` reads nothing, so it is `exprsShapeFree`. -/
private theorem havoc_sf [HasIdent P] [HasVarsPure P P.Expr] {Q : String → Prop} (ident : P.Ident) (md : MetaData P) :
    Stmt.exprsShapeFree (P := P) Q (Stmt.cmd (HasHavoc.havoc ident md)) := by
  show Stmt.exprsShapeFree (P := P) Q (Stmt.cmd (Cmd.set ident ExprOrNondet.nondet md))
  simp only [Stmt.exprsShapeFree, ExprOrNondet.getVars]
  exact fun str _ hmem => absurd hmem List.not_mem_nil

/-- The freshly minted ndelim guard ident is `∉ getVars` of any `Q`-foreign
read-var slot: the only read is `mkFvar ident` whose vars ⊆ `[ident]` and `ident`
carries the ndelim kind, foreign to `Q`. -/
private theorem ndelim_guard_fresh [HasIdent P] [HasFvar P] [HasVarsPure P P.Expr]
    [LawfulHasFvar P] [LawfulHasIdent P] {Q : String → Prop}
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
private theorem loop_sf_transport [HasIdent P] [HasVarsPure P P.Expr] {Q : String → Prop} (g₀ g₁ : ExprOrNondet P)
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
theorem Stmt.nondetElimM_exprsShapeFree [HasIdent P] [HasFvar P] [HasBool P] [HasVarsPure P P.Expr]
    [LawfulHasFvar P] [LawfulHasIdent P] {Q : String → Prop}
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
theorem Block.nondetElimM_exprsShapeFree [HasIdent P] [HasFvar P] [HasBool P] [HasVarsPure P P.Expr]
    [LawfulHasFvar P] [LawfulHasIdent P] {Q : String → Prop}
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

---------------------------------------------------------------------
/-\! ## Section 9 — Direction A: `nondetElim` output `uniqueInits`

The hoist §F precondition `Block.uniqueInits (nondetElim ss)` (= `Nodup` of the
output `initVars`) is established by a window-tracked classification that
mirrors the loop-init-hoist `_initVars_classified`: every output init name is
either an original source init (a member of `Block.initVars ss`) or a
freshly-minted `ndelimKind` guard captured in a `gen`-step window disjoint from
its neighbours.  Distinctness across the source/source, source/fresh, and
fresh/fresh classes is exactly `hoistInitClass_disjoint` (pass-agnostic in `Q`
and the carrier), reused here at `Q := ndelimKind`.  The source-side
`h_sf` hypothesis (no ndelim-kind name is a source init) is discharged at the
top level from a kind-free front-end source. -/

section NondetElimUniqueInits
variable {P : PureExpr}

local notation "HoistInitClass" => LoopInitHoistLoopArmWF.HoistInitClass
local notation "hoistInitClass_disjoint" => @LoopInitHoistLoopArmWF.hoistInitClass_disjoint
local notation "GenStep" => StringGenState.GenStep

theorem Stmt.nondetElimM_block_state [HasIdent P] [HasFvar P] [HasBool P] (lbl : String) (bss : List (Stmt P (Cmd P)))
    (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.block lbl bss md) σ).2 = (Block.nondetElimM bss σ).2 := by
  rw [Stmt.nondetElimM]; rcases h : Block.nondetElimM bss σ with ⟨bss', σ'⟩; simp only [h]

theorem Stmt.nondetElimM_ite_det_state [HasIdent P] [HasFvar P] [HasBool P] (e : P.Expr) (tss ess : List (Stmt P (Cmd P)))
    (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.ite (.det e) tss ess md) σ).2 =
      (Block.nondetElimM ess (Block.nondetElimM tss σ).2).2 := by
  rw [Stmt.nondetElimM]
  rcases h₁ : Block.nondetElimM tss σ with ⟨tss', σ₁⟩
  rcases h₂ : Block.nondetElimM ess σ₁ with ⟨ess', σ₂⟩
  simp only [h₁, h₂]

theorem Stmt.nondetElimM_ite_nondet_state [HasIdent P] [HasFvar P] [HasBool P] (tss ess : List (Stmt P (Cmd P)))
    (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2 =
      (Block.nondetElimM ess (Block.nondetElimM tss (StringGenState.gen ndelimItePrefix σ).2).2).2 := by
  rw [Stmt.nondetElimM]
  rcases hg : StringGenState.gen ndelimItePrefix σ with ⟨g, σ₁⟩
  rcases h₁ : Block.nondetElimM tss σ₁ with ⟨tss', σ₂⟩
  rcases h₂ : Block.nondetElimM ess σ₂ with ⟨ess', σ₃⟩
  simp only [hg, h₁, h₂]

theorem Stmt.nondetElimM_loop_det_state [HasIdent P] [HasFvar P] [HasBool P] (e : P.Expr) (m : Option P.Expr)
    (inv : List (String × P.Expr)) (body : List (Stmt P (Cmd P)))
    (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.loop (.det e) m inv body md) σ).2 = (Block.nondetElimM body σ).2 := by
  rw [Stmt.nondetElimM]; rcases h : Block.nondetElimM body σ with ⟨body', σ'⟩; simp only [h]

theorem Stmt.nondetElimM_loop_nondet_state [HasIdent P] [HasFvar P] [HasBool P] (m : Option P.Expr) (inv : List (String × P.Expr))
    (body : List (Stmt P (Cmd P))) (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2 =
      (Block.nondetElimM body (StringGenState.gen ndelimLoopPrefix σ).2).2 := by
  rw [Stmt.nondetElimM]
  rcases hg : StringGenState.gen ndelimLoopPrefix σ with ⟨g, σ₁⟩
  rcases h : Block.nondetElimM body σ₁ with ⟨body', σ₂⟩
  simp only [hg, h]

theorem Block.nondetElimM_cons_state [HasIdent P] [HasFvar P] [HasBool P] (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P)))
    (σ : StringGenState) :
    (Block.nondetElimM (s :: rest) σ).2 = (Block.nondetElimM rest (Stmt.nondetElimM s σ).2).2 := by
  rw [Block.nondetElimM]
  rcases h₁ : Stmt.nondetElimM s σ with ⟨ss_s, σ₁⟩
  rcases h₂ : Block.nondetElimM rest σ₁ with ⟨ss_r, σ₂⟩
  simp only [h₁, h₂]

/-- The freshly minted ndelim guard satisfies the `HoistInitClass` fresh
disjunct at `ndelimKind` over a one-`gen`-step window. -/
private theorem ndelim_fresh_class [HasIdent P] (pf : String) (σ : StringGenState)
    (h_wf : StringGenState.WF σ)
    (hpf : ndelimKind (StringGenState.gen pf σ).1) :
    ∃ str : String, HasIdent.ident (P := P) (StringGenState.gen pf σ).1 = HasIdent.ident str
      ∧ str ∈ StringGenState.stringGens (StringGenState.gen pf σ).2
      ∧ str ∉ StringGenState.stringGens σ
      ∧ ndelimKind str :=
  ⟨(StringGenState.gen pf σ).1, rfl,
    by rw [StringGenState.stringGens_gen]; exact List.mem_cons.mpr (Or.inl rfl),
    StringGenState.stringGens_gen_not_in pf σ h_wf, hpf⟩

mutual
/-- Strengthened nondetElim `initVars` classification: window-tracked
`HoistInitClass` at `ndelimKind`, plus `Nodup`.  Mirrors the hoist
`_initVars_classified`. -/
theorem Stmt.nondetElimM_initVars_nodup [HasIdent P] [LawfulHasIdent P] [HasFvar P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) (h_wf : StringGenState.WF σ)
    (h_unique : (Stmt.initVars s).Nodup)
    (h_sf : ∀ str : String, ndelimKind str → HasIdent.ident (P := P) str ∉ Stmt.initVars s) :
    (∀ x ∈ Block.initVars (P := P) (Stmt.nondetElimM s σ).1,
        HoistInitClass ndelimKind (Stmt.initVars s) σ (Stmt.nondetElimM s σ).2 x)
      ∧ (Block.initVars (P := P) (Stmt.nondetElimM s σ).1).Nodup := by
  match s with
  | .cmd c =>
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars, List.append_nil] at hx ⊢
        exact Or.inl hx
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars, List.append_nil]
        exact h_unique
  | .block lbl bss md =>
      rw [Stmt.nondetElimM_block_out, Stmt.nondetElimM_block_state]
      have h_unique' : (Block.initVars bss).Nodup := by
        simpa only [Stmt.initVars_block] using h_unique
      have h_sf' : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars bss := by
        intro str hsuf; simpa only [Stmt.initVars_block] using h_sf str hsuf
      have ih := Block.nondetElimM_initVars_nodup bss σ h_wf h_unique' h_sf'
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Block.initVars_cons, Stmt.initVars_block, Block.initVars,
          List.append_nil] at hx ⊢
        simpa only [Stmt.initVars_block] using ih.1 x hx
      · simp only [Block.initVars_cons, Stmt.initVars_block, Block.initVars, List.append_nil]
        exact ih.2
  | .ite (.det e) tss ess md =>
      rw [Stmt.nondetElimM_ite_det_out, Stmt.nondetElimM_ite_det_state]
      have h_uni : (Block.initVars tss ++ Block.initVars ess).Nodup := by
        simpa only [Stmt.initVars_ite] using h_unique
      have h_uni_t : (Block.initVars tss).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_e : (Block.initVars ess).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_disj_te : ∀ a ∈ Block.initVars tss, ∀ b ∈ Block.initVars ess, a ≠ b :=
        (List.nodup_append.mp h_uni).2.2
      have h_sf_t : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars tss := by
        intro str hsuf hmem; exact h_sf str hsuf (by
          rw [Stmt.initVars_ite, List.mem_append]; exact Or.inl hmem)
      have h_sf_e : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars ess := by
        intro str hsuf hmem; exact h_sf str hsuf (by
          rw [Stmt.initVars_ite, List.mem_append]; exact Or.inr hmem)
      have ih_t := Block.nondetElimM_initVars_nodup tss σ h_wf h_uni_t h_sf_t
      have h_wf_t : StringGenState.WF (Block.nondetElimM tss σ).2 :=
        (Block.nondetElimM_genStep tss σ).wf_mono h_wf
      have ih_e := Block.nondetElimM_initVars_nodup ess (Block.nondetElimM tss σ).2 h_wf_t h_uni_e h_sf_e
      have h_step_t : GenStep σ (Block.nondetElimM tss σ).2 := Block.nondetElimM_genStep tss σ
      have h_step_e : GenStep (Block.nondetElimM tss σ).2
          (Block.nondetElimM ess (Block.nondetElimM tss σ).2).2 := Block.nondetElimM_genStep ess _
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Block.initVars_cons, Stmt.initVars_ite, Block.initVars, List.append_nil] at hx ⊢
        rw [List.mem_append] at hx
        rcases hx with h | h
        · rcases ih_t.1 x h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [List.mem_append]; exact Or.inl h_o)
          · exact Or.inr ⟨str, he, h_step_e.subset hin, hnot, hQ⟩
        · rcases ih_e.1 x h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [List.mem_append]; exact Or.inr h_o)
          · exact Or.inr ⟨str, he, hin, fun h_in_σ => hnot (h_step_t.subset h_in_σ), hQ⟩
      · simp only [Block.initVars_cons, Stmt.initVars_ite, Block.initVars, List.append_nil]
        rw [List.nodup_append]
        exact ⟨ih_t.2, ih_e.2, hoistInitClass_disjoint (Block.initVars tss) (Block.initVars ess)
          σ (Block.nondetElimM tss σ).2 _ h_wf h_step_t h_step_e
          h_disj_te h_sf_t h_sf_e _ _ ih_t.1 ih_e.1⟩
  | .ite .nondet tss ess md =>
      rw [Stmt.nondetElimM_ite_nondet_out, Stmt.nondetElimM_ite_nondet_state]
      have h_wf₀ : StringGenState.WF (StringGenState.gen ndelimItePrefix σ).2 := (StringGenState.GenStep.of_gen ndelimItePrefix σ).wf_mono h_wf
      have h_step_g : GenStep σ (StringGenState.gen ndelimItePrefix σ).2 := StringGenState.GenStep.of_gen ndelimItePrefix σ
      -- the source `.ite .nondet` initVars are the branches'.
      have h_uni : (Block.initVars tss ++ Block.initVars ess).Nodup := by
        simpa only [Stmt.initVars] using h_unique
      have h_uni_t : (Block.initVars tss).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_e : (Block.initVars ess).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_disj_te : ∀ a ∈ Block.initVars tss, ∀ b ∈ Block.initVars ess, a ≠ b :=
        (List.nodup_append.mp h_uni).2.2
      have h_sf_src : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars tss ++ Block.initVars ess := by
        intro str hsuf; simpa only [Stmt.initVars] using h_sf str hsuf
      have h_sf_t : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars tss :=
        fun str hsuf hmem => h_sf_src str hsuf (List.mem_append.mpr (Or.inl hmem))
      have h_sf_e : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars ess :=
        fun str hsuf hmem => h_sf_src str hsuf (List.mem_append.mpr (Or.inr hmem))
      have ih_t := Block.nondetElimM_initVars_nodup tss (StringGenState.gen ndelimItePrefix σ).2 h_wf₀ h_uni_t h_sf_t
      have h_wf_t : StringGenState.WF (Block.nondetElimM tss (StringGenState.gen ndelimItePrefix σ).2).2 :=
        (Block.nondetElimM_genStep tss (StringGenState.gen ndelimItePrefix σ).2).wf_mono h_wf₀
      have ih_e := Block.nondetElimM_initVars_nodup ess (Block.nondetElimM tss (StringGenState.gen ndelimItePrefix σ).2).2 h_wf_t h_uni_e h_sf_e
      have h_step_t : GenStep (StringGenState.gen ndelimItePrefix σ).2 (Block.nondetElimM tss (StringGenState.gen ndelimItePrefix σ).2).2 := Block.nondetElimM_genStep tss (StringGenState.gen ndelimItePrefix σ).2
      have h_step_e : GenStep (Block.nondetElimM tss (StringGenState.gen ndelimItePrefix σ).2).2
          (Block.nondetElimM ess (Block.nondetElimM tss (StringGenState.gen ndelimItePrefix σ).2).2).2 := Block.nondetElimM_genStep ess _
      -- the freshly minted guard, classified over the `σ → (StringGenState.gen ndelimItePrefix σ).2` gen window.
      have h_guard_iv : Stmt.initVars (P := P)
          (Stmt.cmd (HasInit.init (HasIdent.ident (P := P) (StringGenState.gen ndelimItePrefix σ).1)
            HasBool.boolTy ExprOrNondet.nondet md)) =
          [HasIdent.ident (P := P) (StringGenState.gen ndelimItePrefix σ).1] := by
        with_unfolding_all rfl
      -- branch inits classified together over the post-gen window `(StringGenState.gen ndelimItePrefix σ).2 → σ₂`.
      have h_branchClass : ∀ y ∈ Block.initVars (Block.nondetElimM tss (StringGenState.gen ndelimItePrefix σ).2).1 ++
            Block.initVars (Block.nondetElimM ess (Block.nondetElimM tss (StringGenState.gen ndelimItePrefix σ).2).2).1,
          HoistInitClass ndelimKind (Block.initVars tss ++ Block.initVars ess) (StringGenState.gen ndelimItePrefix σ).2
            (Block.nondetElimM ess (Block.nondetElimM tss (StringGenState.gen ndelimItePrefix σ).2).2).2 y := by
        intro y hy
        rw [List.mem_append] at hy
        rcases hy with h | h
        · rcases ih_t.1 y h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (List.mem_append.mpr (Or.inl h_o))
          · exact Or.inr ⟨str, he, h_step_e.subset hin, hnot, hQ⟩
        · rcases ih_e.1 y h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (List.mem_append.mpr (Or.inr h_o))
          · exact Or.inr ⟨str, he, hin, fun hσ => hnot (h_step_t.subset hσ), hQ⟩
      have h_branchNodup : (Block.initVars (Block.nondetElimM tss (StringGenState.gen ndelimItePrefix σ).2).1 ++
            Block.initVars (Block.nondetElimM ess (Block.nondetElimM tss (StringGenState.gen ndelimItePrefix σ).2).2).1).Nodup := by
        rw [List.nodup_append]
        exact ⟨ih_t.2, ih_e.2, hoistInitClass_disjoint (Block.initVars tss) (Block.initVars ess)
          (StringGenState.gen ndelimItePrefix σ).2 (Block.nondetElimM tss (StringGenState.gen ndelimItePrefix σ).2).2 _ h_wf₀ h_step_t h_step_e
          h_disj_te h_sf_t h_sf_e _ _ ih_t.1 ih_e.1⟩
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Block.initVars_cons, Stmt.initVars_ite, Block.initVars, List.append_nil,
          h_guard_iv, List.singleton_append, List.mem_cons, List.mem_append] at hx
        rcases hx with h_g | h_t | h_e
        · obtain ⟨str, he, hin, hnot, hQ⟩ := ndelim_fresh_class (P := P) ndelimItePrefix σ h_wf (ndelimKind_gen.1 σ)
          exact Or.inr ⟨str, h_g.trans he, h_step_e.subset (h_step_t.subset hin), hnot, hQ⟩
        · rcases ih_t.1 x h_t with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [Stmt.initVars_ite, List.mem_append]; exact Or.inl h_o)
          · exact Or.inr ⟨str, he, h_step_e.subset hin,
              fun hσ => hnot (h_step_g.subset hσ), hQ⟩
        · rcases ih_e.1 x h_e with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [Stmt.initVars_ite, List.mem_append]; exact Or.inr h_o)
          · exact Or.inr ⟨str, he, hin,
              fun hσ => hnot (h_step_t.subset (h_step_g.subset hσ)), hQ⟩
      · simp only [Block.initVars_cons, Stmt.initVars_ite, Block.initVars, List.append_nil,
          h_guard_iv, List.singleton_append]
        rw [List.nodup_cons]
        refine ⟨?_, h_branchNodup⟩
        -- guard ∉ branchInits: a guard ident is `∈ stringGens (StringGenState.gen ndelimItePrefix σ).2 \ σ`; classify each
        -- branch member and refute each cross-class collision.
        intro hmem
        have h_guard_fresh := ndelim_fresh_class (P := P) ndelimItePrefix σ h_wf (ndelimKind_gen.1 σ)
        obtain ⟨gstr, geq, gin, gnot, gQ⟩ := h_guard_fresh
        rcases h_branchClass _ hmem with h_o | ⟨str, he, hin, hnot, hQ⟩
        · exact h_sf_src gstr gQ (geq ▸ h_o)
        · have : gstr = str := LawfulHasIdent.ident_inj (geq.symm.trans he)
          exact hnot (this ▸ gin)
  | .loop (.det e) m inv body md =>
      rw [Stmt.nondetElimM_loop_det_out, Stmt.nondetElimM_loop_det_state]
      have h_unique' : (Block.initVars body).Nodup := by
        simpa only [Stmt.initVars_loop] using h_unique
      have h_sf' : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars body := by
        intro str hsuf; simpa only [Stmt.initVars_loop] using h_sf str hsuf
      have ih := Block.nondetElimM_initVars_nodup body σ h_wf h_unique' h_sf'
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Block.initVars_cons, Stmt.initVars_loop, Block.initVars,
          List.append_nil] at hx ⊢
        simpa only [Stmt.initVars_loop] using ih.1 x hx
      · simp only [Block.initVars_cons, Stmt.initVars_loop, Block.initVars, List.append_nil]
        exact ih.2
  | .loop .nondet m inv body md =>
      rw [Stmt.nondetElimM_loop_nondet_out, Stmt.nondetElimM_loop_nondet_state]
      have h_wf₀ : StringGenState.WF (StringGenState.gen ndelimLoopPrefix σ).2 :=
        (StringGenState.GenStep.of_gen ndelimLoopPrefix σ).wf_mono h_wf
      have h_step_g : GenStep σ (StringGenState.gen ndelimLoopPrefix σ).2 :=
        StringGenState.GenStep.of_gen ndelimLoopPrefix σ
      have h_unique' : (Block.initVars body).Nodup := by
        simpa only [Stmt.initVars] using h_unique
      have h_sf' : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars body := by
        intro str hsuf; simpa only [Stmt.initVars] using h_sf str hsuf
      have ih := Block.nondetElimM_initVars_nodup body (StringGenState.gen ndelimLoopPrefix σ).2 h_wf₀ h_unique' h_sf'
      have h_step_body : GenStep (StringGenState.gen ndelimLoopPrefix σ).2
          (Block.nondetElimM body (StringGenState.gen ndelimLoopPrefix σ).2).2 :=
        Block.nondetElimM_genStep body _
      -- the new loop body is `body' ++ [havoc guard]`; havoc has no inits.
      have h_havoc_init : Block.initVars (P := P)
          [Stmt.cmd (HasHavoc.havoc (HasIdent.ident (P := P) (StringGenState.gen ndelimLoopPrefix σ).1) md)] = [] := by
        with_unfolding_all rfl
      have h_guard_iv : Stmt.initVars (P := P)
          (Stmt.cmd (HasInit.init (HasIdent.ident (P := P) (StringGenState.gen ndelimLoopPrefix σ).1)
            HasBool.boolTy ExprOrNondet.nondet md)) =
          [HasIdent.ident (P := P) (StringGenState.gen ndelimLoopPrefix σ).1] := by
        with_unfolding_all rfl
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Block.initVars_cons, Stmt.initVars_loop, Block.initVars, List.append_nil,
          h_guard_iv, List.singleton_append, List.mem_cons] at hx
        rw [Block.initVars_append, h_havoc_init, List.append_nil] at hx
        simp only [Stmt.initVars_loop]
        rcases hx with h_g | h_body
        · obtain ⟨str, he, hin, hnot, hQ⟩ := ndelim_fresh_class (P := P) ndelimLoopPrefix σ h_wf (ndelimKind_gen.2 σ)
          exact Or.inr ⟨str, h_g.trans he, h_step_body.subset hin, hnot, hQ⟩
        · rcases ih.1 x h_body with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl h_o
          · exact Or.inr ⟨str, he, hin, fun hσ => hnot (h_step_g.subset hσ), hQ⟩
      · simp only [Block.initVars_cons, Stmt.initVars_loop, Block.initVars, List.append_nil,
          h_guard_iv, List.singleton_append]
        rw [Block.initVars_append, h_havoc_init, List.append_nil, List.nodup_cons]
        refine ⟨?_, ih.2⟩
        intro hmem
        obtain ⟨gstr, geq, gin, gnot, gQ⟩ := ndelim_fresh_class (P := P) ndelimLoopPrefix σ h_wf (ndelimKind_gen.2 σ)
        rcases ih.1 _ hmem with h_o | ⟨str, he, hin, hnot, hQ⟩
        · exact h_sf' gstr gQ (geq ▸ h_o)
        · have : gstr = str := LawfulHasIdent.ident_inj (geq.symm.trans he)
          exact hnot (this ▸ gin)
  | .exit lbl md =>
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars, Stmt.initVars,
          List.append_nil] at hx; exact (List.not_mem_nil hx).elim
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars, Stmt.initVars,
          List.append_nil]; exact List.nodup_nil
  | .funcDecl d md =>
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars, Stmt.initVars,
          List.append_nil] at hx; exact (List.not_mem_nil hx).elim
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars, Stmt.initVars,
          List.append_nil]; exact List.nodup_nil
  | .typeDecl t md =>
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars, Stmt.initVars,
          List.append_nil] at hx; exact (List.not_mem_nil hx).elim
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars, Stmt.initVars,
          List.append_nil]; exact List.nodup_nil
  termination_by sizeOf s

theorem Block.nondetElimM_initVars_nodup [HasIdent P] [LawfulHasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) (h_wf : StringGenState.WF σ)
    (h_unique : (Block.initVars ss).Nodup)
    (h_sf : ∀ str : String, ndelimKind str → HasIdent.ident (P := P) str ∉ Block.initVars ss) :
    (∀ x ∈ Block.initVars (P := P) (Block.nondetElimM ss σ).1,
        HoistInitClass ndelimKind (Block.initVars ss) σ (Block.nondetElimM ss σ).2 x)
      ∧ (Block.initVars (P := P) (Block.nondetElimM ss σ).1).Nodup := by
  match ss with
  | [] =>
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [Block.nondetElimM, Block.initVars] at hx; exact (List.not_mem_nil hx).elim
      · simp only [Block.nondetElimM, Block.initVars]; exact List.nodup_nil
  | s :: rest =>
      rw [Block.nondetElimM_cons_out, Block.nondetElimM_cons_state]
      have h_uni : (Stmt.initVars s ++ Block.initVars rest).Nodup := by
        simpa only [Block.initVars_cons] using h_unique
      have h_uni_s : (Stmt.initVars s).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_r : (Block.initVars rest).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_disj_sr : ∀ a ∈ Stmt.initVars s, ∀ b ∈ Block.initVars rest, a ≠ b :=
        (List.nodup_append.mp h_uni).2.2
      have h_sf_s : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Stmt.initVars s := by
        intro str hsuf hmem; exact h_sf str hsuf (by
          rw [Block.initVars_cons, List.mem_append]; exact Or.inl hmem)
      have h_sf_r : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars rest := by
        intro str hsuf hmem; exact h_sf str hsuf (by
          rw [Block.initVars_cons, List.mem_append]; exact Or.inr hmem)
      have ih_s := Stmt.nondetElimM_initVars_nodup s σ h_wf h_uni_s h_sf_s
      have h_wf_s : StringGenState.WF (Stmt.nondetElimM s σ).2 :=
        (Stmt.nondetElimM_genStep s σ).wf_mono h_wf
      have ih_r := Block.nondetElimM_initVars_nodup rest (Stmt.nondetElimM s σ).2 h_wf_s h_uni_r h_sf_r
      have h_step_s : GenStep σ (Stmt.nondetElimM s σ).2 := Stmt.nondetElimM_genStep s σ
      have h_step_r : GenStep (Stmt.nondetElimM s σ).2
          (Block.nondetElimM rest (Stmt.nondetElimM s σ).2).2 := Block.nondetElimM_genStep rest _
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Block.initVars_append] at hx
        rw [Block.initVars_cons]
        rw [List.mem_append] at hx
        rcases hx with h | h
        · rcases ih_s.1 x h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [List.mem_append]; exact Or.inl h_o)
          · exact Or.inr ⟨str, he, h_step_r.subset hin, hnot, hQ⟩
        · rcases ih_r.1 x h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [List.mem_append]; exact Or.inr h_o)
          · exact Or.inr ⟨str, he, hin, fun h_in_σ => hnot (h_step_s.subset h_in_σ), hQ⟩
      · rw [Block.initVars_append, List.nodup_append]
        exact ⟨ih_s.2, ih_r.2, hoistInitClass_disjoint (Stmt.initVars s) (Block.initVars rest)
          σ (Stmt.nondetElimM s σ).2 _ h_wf h_step_s h_step_r
          h_disj_sr h_sf_s h_sf_r _ _ ih_s.1 ih_r.1⟩
  termination_by sizeOf ss
end
end NondetElimUniqueInits

---------------------------------------------------------------------
/-! ## Section 10 — Direction A: `hoistedNamesFreshInRhsAndGuards` on `nondetElim`

The hoist §F precondition `hoistedNamesFreshInRhsAndGuards (nondetElim ss)` is
the last cross-pass obligation.  The predicate is the RHS-only `initVars`
freshness `namesFreshInRhsExprs (initVars _) _`:

  `nondetElim` only ever introduces command RHS positions that read nothing
  (`init _ .nondet` / `havoc`); it reads its fresh guard *only* in a
  `.ite`/`.loop` *guard*, never in a command RHS.  So the RHS-only freshness is
  preserved verbatim for any fixed name list
  (`Block.nondetElimM_namesFreshInRhsExprs`), and the per-name coverage of the
  output's own `initVars` is supplied by the Section-8/9 classification (source
  inits inherit the source hypothesis; fresh `ndelimKind` guards are RHS-fresh
  by source kind-freedom).

Guard freshness for a loop's body inits is no longer demanded: at every loop
head a body-init name is undefined, so an evaluating guard cannot read it, and
the loop driver discharges the guard agreement from that undefinedness
invariant directly. -/

section NondetElimFresh
variable {P : PureExpr}

/-- A `.cmd (init _ _ .nondet _)` has an empty-vars RHS, so any names list is
RHS-fresh in it. -/
private theorem init_nondet_rhsfree [HasVarsPure P P.Expr] (names : List P.Ident) (ident : P.Ident)
    (ty : P.Ty) (md : MetaData P) :
    Stmt.namesFreshInRhsExprs (P := P) names
      (Stmt.cmd (HasInit.init ident ty ExprOrNondet.nondet md)) = true := by
  show Stmt.namesFreshInRhsExprs (P := P) names
    (Stmt.cmd (Cmd.init ident ty ExprOrNondet.nondet md)) = true
  simp only [Stmt.namesFreshInRhsExprs, ExprOrNondet.getVars]
  rw [List.all_eq_true]; intro z _; rfl

/-- A `.cmd (havoc _)` has an empty-vars RHS, so any names list is RHS-fresh in
it. -/
private theorem havoc_rhsfree [HasVarsPure P P.Expr] (names : List P.Ident) (ident : P.Ident)
    (md : MetaData P) :
    Stmt.namesFreshInRhsExprs (P := P) names
      (Stmt.cmd (HasHavoc.havoc ident md)) = true := by
  show Stmt.namesFreshInRhsExprs (P := P) names
    (Stmt.cmd (Cmd.set ident ExprOrNondet.nondet md)) = true
  simp only [Stmt.namesFreshInRhsExprs, ExprOrNondet.getVars]
  rw [List.all_eq_true]; intro z _; rfl

mutual
/-- `nondetElim` preserves `namesFreshInRhsExprs names` for a fixed name list:
all introduced command RHS positions read nothing, and source RHS positions are
unchanged. -/
theorem Stmt.nondetElimM_namesFreshInRhsExprs [HasIdent P] [HasFvar P] [HasBool P] [HasVarsPure P P.Expr] (names : List P.Ident)
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (h : Stmt.namesFreshInRhsExprs (P := P) names s = true) :
    Block.namesFreshInRhsExprs (P := P) names (Stmt.nondetElimM s σ).1 = true := by
  match s with
  | .cmd c =>
      simp only [Stmt.nondetElimM, Block.namesFreshInRhsExprs, Bool.and_true]
      exact h
  | .block lbl bss md =>
      rw [Stmt.nondetElimM_block_out]
      simp only [Stmt.namesFreshInRhsExprs] at h
      simp only [Block.namesFreshInRhsExprs, Stmt.namesFreshInRhsExprs, Bool.and_true]
      exact Block.nondetElimM_namesFreshInRhsExprs names bss σ h
  | .ite (.det e) tss ess md =>
      rw [Stmt.nondetElimM_ite_det_out]
      simp only [Stmt.namesFreshInRhsExprs, Bool.and_eq_true] at h
      simp only [Block.namesFreshInRhsExprs, Stmt.namesFreshInRhsExprs, Bool.and_true,
        Bool.and_eq_true]
      exact ⟨Block.nondetElimM_namesFreshInRhsExprs names tss σ h.1,
             Block.nondetElimM_namesFreshInRhsExprs names ess _ h.2⟩
  | .ite .nondet tss ess md =>
      rw [Stmt.nondetElimM_ite_nondet_out]
      simp only [Stmt.namesFreshInRhsExprs, Bool.and_eq_true] at h
      simp only [Block.namesFreshInRhsExprs, Bool.and_true, Bool.and_eq_true]
      refine ⟨init_nondet_rhsfree _ _ _ _, ?_⟩
      simp only [Stmt.namesFreshInRhsExprs, Bool.and_eq_true]
      exact ⟨Block.nondetElimM_namesFreshInRhsExprs names tss _ h.1,
             Block.nondetElimM_namesFreshInRhsExprs names ess _ h.2⟩
  | .loop (.det e) m inv body md =>
      rw [Stmt.nondetElimM_loop_det_out]
      simp only [Stmt.namesFreshInRhsExprs] at h
      simp only [Block.namesFreshInRhsExprs, Stmt.namesFreshInRhsExprs, Bool.and_true]
      exact Block.nondetElimM_namesFreshInRhsExprs names body σ h
  | .loop .nondet m inv body md =>
      rw [Stmt.nondetElimM_loop_nondet_out]
      simp only [Stmt.namesFreshInRhsExprs] at h
      simp only [Block.namesFreshInRhsExprs, Stmt.namesFreshInRhsExprs, Bool.and_true,
        Bool.and_eq_true]
      have h_havoc : Block.namesFreshInRhsExprs (P := P) names
          [Stmt.cmd (HasHavoc.havoc (HasIdent.ident (P := P) (StringGenState.gen ndelimLoopPrefix σ).1) md)] = true := by
        simp only [Block.namesFreshInRhsExprs, Bool.and_true]
        exact havoc_rhsfree _ _ _
      refine ⟨init_nondet_rhsfree _ _ _ _, ?_⟩
      exact Block.namesFreshInRhsExprs_append _ _
        (Block.nondetElimM_namesFreshInRhsExprs names body _ h) h_havoc
  | .exit lbl md =>
      simp only [Stmt.nondetElimM, Block.namesFreshInRhsExprs, Stmt.namesFreshInRhsExprs,
        Bool.and_true]
  | .funcDecl d md =>
      simp only [Stmt.nondetElimM, Block.namesFreshInRhsExprs, Stmt.namesFreshInRhsExprs,
        Bool.and_true]
  | .typeDecl t md =>
      simp only [Stmt.nondetElimM, Block.namesFreshInRhsExprs, Stmt.namesFreshInRhsExprs,
        Bool.and_true]
  termination_by sizeOf s

theorem Block.nondetElimM_namesFreshInRhsExprs [HasIdent P] [HasFvar P] [HasBool P] [HasVarsPure P P.Expr] (names : List P.Ident)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h : Block.namesFreshInRhsExprs (P := P) names ss = true) :
    Block.namesFreshInRhsExprs (P := P) names (Block.nondetElimM ss σ).1 = true := by
  match ss with
  | [] => simp only [Block.nondetElimM, Block.namesFreshInRhsExprs]
  | s :: rest =>
      rw [Block.nondetElimM_cons_out]
      simp only [Block.namesFreshInRhsExprs, Bool.and_eq_true] at h
      exact Block.namesFreshInRhsExprs_append _ _
        (Stmt.nondetElimM_namesFreshInRhsExprs names s σ h.1)
        (Block.nondetElimM_namesFreshInRhsExprs names rest _ h.2)
  termination_by sizeOf ss
end

/-- An `ndelimKind` guard ident is RHS-fresh in the kind-free source: it is the
identifier of an `ndelimKind` label, and the source reads no `ndelimKind` ident
in any expression (`exprsShapeFree ndelimKind`), so a fortiori not in any RHS. -/
private theorem ndelim_guard_namesFreshInRhsExprs_src [HasIdent P] [HasVarsPure P P.Expr]
    {str : String} (h_kind : ndelimKind str) (ss : List (Stmt P (Cmd P)))
    (h_sf : Block.exprsShapeFree (P := P) ndelimKind ss) :
    Block.namesFreshInRhsExprs (P := P) [HasIdent.ident (P := P) str] ss = true :=
  Block.namesFreshInRhsExprs_of_namesFreshInExprs _ ss
    (Block.namesFreshInExprs_of_exprsShapeFree' (Q := ndelimKind)
      (fun z hz => by
        rw [List.mem_singleton] at hz; exact ⟨str, hz, h_kind⟩)
      ss h_sf)

/-- Every name in `initVars (nondetElim ss)` is RHS-fresh in the source `ss`:
source inits inherit the source RHS-freshness; freshly minted `ndelimKind`
guards are RHS-fresh by source kind-freedom. -/
theorem nondetElim_initVars_namesFreshInRhsExprs_src [HasIdent P] [HasFvar P] [HasBool P] [HasVarsPure P P.Expr]
    (ss : List (Stmt P (Cmd P)))
    (h_src_rhs : Block.namesFreshInRhsExprs (P := P) (Block.initVars ss) ss = true)
    (h_sf : Block.exprsShapeFree (P := P) ndelimKind ss) :
    Block.namesFreshInRhsExprs (P := P)
      (Block.initVars (Block.nondetElim ss)) ss = true := by
  refine Block.namesFreshInRhsExprs_of_forall_mem _ ss (fun z hz => ?_)
  rcases Block.nondetElimM_initVars_classified ss StringGenState.emp z hz with
    h_src | ⟨str, h_eq, h_kind⟩
  · exact Block.namesFreshInRhsExprs_subset
      (fun w hw => by rw [List.mem_singleton] at hw; exact hw ▸ h_src) ss h_src_rhs
  · exact h_eq ▸ ndelim_guard_namesFreshInRhsExprs_src h_kind ss h_sf

/-- The `namesFreshInRhsExprs (initVars …) …` conjunct of
`hoistedNamesFreshInRhsAndGuards` holds on the `nondetElim` output: the source
fact (every output init RHS-fresh in the source) is transported through the pass
(which only adds variable-free command RHS positions). -/
theorem nondetElim_namesFreshInRhsExprs [HasIdent P] [HasFvar P] [HasBool P] [HasVarsPure P P.Expr]
    (ss : List (Stmt P (Cmd P)))
    (h_src_rhs : Block.namesFreshInRhsExprs (P := P) (Block.initVars ss) ss = true)
    (h_sf : Block.exprsShapeFree (P := P) ndelimKind ss) :
    Block.namesFreshInRhsExprs (P := P)
      (Block.initVars (Block.nondetElim ss)) (Block.nondetElim ss) = true :=
  Block.nondetElimM_namesFreshInRhsExprs _ ss StringGenState.emp
    (nondetElim_initVars_namesFreshInRhsExprs_src ss h_src_rhs h_sf)

end NondetElimFresh

section NondetElimFreshAssembly
variable {P : PureExpr}

/-- Top-level Direction-A bridge: `nondetElim` establishes the
`hoistedNamesFreshInRhsAndGuards` postcondition on its output, given the
front-end source facts (its own `hoistedNamesFreshInRhsAndGuards` and its
`ndelimKind`-freedom). This discharges the hoist §F `h_fresh` precondition at
the `nondetElim` output: the predicate is the RHS-only `initVars` freshness,
preserved verbatim because `nondetElim` only ever adds variable-free command
RHS positions (its fresh guard is read only in a `.ite`/`.loop` guard). -/
theorem nondetElim_hoistedNamesFreshInRhsAndGuards [HasIdent P] [LawfulHasIdent P] [HasFvar P] [HasBool P] [HasVarsPure P P.Expr] [LawfulHasFvar P]
    (ss : List (Stmt P (Cmd P)))
    (h_fresh_src : Block.hoistedNamesFreshInRhsAndGuards (P := P) ss = true)
    (h_sf : Block.exprsShapeFree (P := P) ndelimKind ss) :
    Block.hoistedNamesFreshInRhsAndGuards (P := P) (Block.nondetElim ss) = true := by
  unfold Block.hoistedNamesFreshInRhsAndGuards at h_fresh_src ⊢
  exact nondetElim_namesFreshInRhsExprs ss h_fresh_src h_sf

end NondetElimFreshAssembly

---------------------------------------------------------------------
/-! ## Section 10b — `transformBlockModVars` ≡ `Block.modifiedVars`

The S2U `NoGenSuffix` precondition speaks of the translator's local
`transformBlockModVars`, whose recursion is identical to `Block.modifiedVars`
(`.cmd c ↦ Cmd.modifiedVars c`, branch/body recursion).  They are pointwise
equal; we prove it once so the modVars `NoGenSuffix s2uKind` leaf can be
discharged from the (kind-classified) `Block.modifiedVars` of the hoist output. -/

mutual
theorem transformStmtModVars_eq_modifiedVars {P : PureExpr} (s : Stmt P (Cmd P)) :
    StructuredToUnstructuredCorrect.transformStmtModVars (P := P) s = Stmt.modifiedVars s := by
  match s with
  | .cmd c => rfl
  | .block lbl bss md =>
      show StructuredToUnstructuredCorrect.transformBlockModVars bss = Block.modifiedVars bss
      exact transformBlockModVars_eq_modifiedVars bss
  | .ite g tss ess md =>
      show StructuredToUnstructuredCorrect.transformBlockModVars tss ++
        StructuredToUnstructuredCorrect.transformBlockModVars ess =
          Block.modifiedVars tss ++ Block.modifiedVars ess
      rw [transformBlockModVars_eq_modifiedVars tss, transformBlockModVars_eq_modifiedVars ess]
  | .loop g m inv body md =>
      show StructuredToUnstructuredCorrect.transformBlockModVars body = Block.modifiedVars body
      exact transformBlockModVars_eq_modifiedVars body
  | .exit lbl md => rfl
  | .funcDecl d md => rfl
  | .typeDecl t md => rfl
  termination_by sizeOf s

theorem transformBlockModVars_eq_modifiedVars {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    StructuredToUnstructuredCorrect.transformBlockModVars (P := P) ss = Block.modifiedVars ss := by
  match ss with
  | [] => rfl
  | s :: rest =>
      show StructuredToUnstructuredCorrect.transformStmtModVars s ++
        StructuredToUnstructuredCorrect.transformBlockModVars rest =
          Stmt.modifiedVars s ++ Block.modifiedVars rest
      rw [transformStmtModVars_eq_modifiedVars s, transformBlockModVars_eq_modifiedVars rest]
  termination_by sizeOf ss
end

---------------------------------------------------------------------
/-! ## Section 11 — The composed pipeline soundness theorem

`pipeline ss := stmtsToCFG (hoist (nondetElim ss))`.  The three kind-generalized
soundness theorems chain via `StoreAgreement.trans`: each pass runs its input
program from the same clean initial environment `ρ₀`, and the cross-pass
name-shape preconditions are discharged by per-kind foreignness (Sections 7–10)
rather than the blanket suffix-shape exclusion that obstructed the original
composition.

The front-end hypotheses on the user source `ss` are all satisfiable by a real
program: `ss` is shape-restricted (no func decls, no loop invariants/measures)
and *kind-free* — it mentions none of the
`$__ndelim_*$` / `_hoist` / S2U construct prefixes that the three passes mint
(the `*_kindfree` hypotheses), and never writes or reads such a name.  `ρ₀`'s
store need only leave the source inits (`h_store_inits`) and the three passes'
minted names (`h_store_mints`) undefined — not the entire store. -/

section PipelineSound
variable {P : PureExpr}

/-- The composed structured-to-unstructured pipeline. -/
@[expose] def pipeline [HasIdent P] [HasFvar P] [HasBool P] [HasSubstFvar P] [DecidableEq P.Ident]
    [HasNot P] [HasIntOrder P]
    (ss : List (Stmt P (Cmd P))) :
    CFG String (DetBlock String (Cmd P) P) :=
  (stmtsToCFG ∘ Block.hoistLoopPrefixInits ∘ Block.nondetElim) ss

/-- **Pipeline soundness.** Every terminating source run of `ss` from a clean
initial store `ρ₀` is matched by a terminating run of the unstructured CFG
`pipeline ss` whose final store agrees with the source's (source on the left).

A real composition of the three `_sound_kind` theorems via `StoreAgreement.trans`:
no hypothesis is vacuous or false — each precondition is satisfiable by a clean
initial store and a shape-restricted, kind-free user program. -/
theorem pipeline_sound [HasFvar P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P]
    [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasFvar P]
    [LawfulHasBool P] [LawfulHasIdent P] [LawfulHasIntOrder P] [LawfulHasNot P]
    [HasSubstFvar P] [LawfulHasSubstFvar P]
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwfvar' : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval)
    (hwfcongr' : ∀ ρ : Env P, WellFormedSemanticEvalExprCongr ρ.eval)
    (hwfsubst' : ∀ ρ : Env P, WellFormedSemanticEvalSubstFvar ρ.eval)
    (hwfdef' : ∀ ρ : Env P, WellFormedSemanticEvalDef ρ.eval)
    -- `ρ₀` need only leave the source inits and the three passes' minted
    -- (gen-kind) names undefined — not the entire store.  Source inits are the
    -- runtime-shape precondition the hoist's `prelude_execution` consumes; the
    -- minted names (`ndelimKind`/`hoistKind`/`s2uKind`) are foreign to the source
    -- vars and their undefinedness is irreducibly required (a fresh guard or a
    -- fresh CFG-relevant binder collides with a populated store).  `modVars` need
    -- NOT be undefined.
    (h_store_inits : ∀ x ∈ Block.initVars ss, ρ₀.store x = none)
    (h_store_mints : ∀ s : String,
      (ndelimKind s ∨ hoistKind s ∨ StructuredToUnstructuredCorrect.s2uKind s) →
      ρ₀.store (HasIdent.ident (P := P) s) = none)
    -- source shape restrictions (front-end well-formedness):
    (h_nofd : Block.noFuncDecl ss = true)
    (h_lhni : Block.loopHasNoInvariants ss = true)
    (h_nml : Block.noMeasureLoops ss = true)
    (h_unique : Block.uniqueInits ss)
    (h_fresh : Block.hoistedNamesFreshInRhsAndGuards (P := P) ss = true)
    (h_disj : StructuredToUnstructuredCorrect.Block.userLabelsShapeNodup
      (Block.hoistLoopPrefixInits (Block.nondetElim ss)))
    -- source kind-freedom (user names never collide with any minted prefix):
    (h_ndelim_writes : SrcNoGenWrites (P := P) ndelimKind ss)
    (h_ndelim_exprs : Block.exprsShapeFree (P := P) ndelimKind ss)
    (h_hoist_exprs : Block.exprsShapeFree (P := P) hoistKind ss)
    -- The three passes' minted-name kinds avoid the source `initVars` (one merged
    -- disjunction over the three pass kinds, replacing the per-kind triple):
    (h_disj_initVars : ∀ str : String,
      (ndelimKind str ∨ hoistKind str ∨ StructuredToUnstructuredCorrect.s2uKind str) →
      HasIdent.ident (P := P) str ∉ Block.initVars ss)
    -- The hoist/S2U minted-name kinds avoid the source `modifiedVars` (one merged
    -- disjunction; `ndelimKind` modVars-freedom is folded into `h_ndelim_writes`):
    (h_disj_modVars : ∀ str : String,
      (hoistKind str ∨ StructuredToUnstructuredCorrect.s2uKind str) →
      HasIdent.ident (P := P) str ∉ Block.modifiedVars ss)
    (h_term : StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) (.terminal ρ')) :
    ∃ σ_cfg, StructuredToUnstructuredCorrect.StepDetCFGStar extendEval (pipeline ss)
        (.atBlock (pipeline ss).entry ρ₀.store ρ₀.hasFailure)
        (.terminal σ_cfg ρ'.hasFailure)
      ∧ StoreAgreement ρ'.store σ_cfg := by
  -- === STEP 1: nondetElim ===  StoreAgreement ρ'.store ρ_out.store.
  obtain ⟨ρ_out, h_run1, h_agree1, h_hf1⟩ :=
    nondetElim_sound_kind extendEval ss ρ₀ ρ'
      hwfb hwfv (hwfdef' ρ₀) (hwfcongr' ρ₀) (hwfvar' ρ₀)
      (fun s hk => h_store_mints s (Or.inl hk)) h_ndelim_writes h_nofd h_lhni h_term
  -- Direction-A hoist §F preconds on the `nondetElim` output, at `Q := hoistKind`.
  have h_out_unique : Block.uniqueInits (Block.nondetElim ss) :=
    (Block.nondetElimM_initVars_nodup ss StringGenState.emp StringGenState.wf_emp
      h_unique (fun str hk => h_disj_initVars str (Or.inl hk))).2
  have h_out_iv_sf : ∀ str : String, hoistKind str →
      HasIdent.ident (P := P) str ∉ Block.initVars (Block.nondetElim ss) := by
    intro str hk hmem
    rcases Block.nondetElimM_initVars_classified ss StringGenState.emp _ hmem with
      h_src | ⟨str', h_eq, h_nd⟩
    · exact h_disj_initVars str (Or.inr (Or.inl hk)) h_src
    · exact ndelimKind_not_hoistKind h_nd (LawfulHasIdent.ident_inj h_eq ▸ hk)
  have h_out_mv_sf : ∀ str : String, hoistKind str →
      HasIdent.ident (P := P) str ∉ Block.modifiedVars (Block.nondetElim ss) := by
    intro str hk hmem
    rcases Block.nondetElimM_modVars_classified ss StringGenState.emp _ hmem with
      h_src | ⟨str', h_eq, h_nd⟩
    · exact h_disj_modVars str (Or.inl hk) h_src
    · exact ndelimKind_not_hoistKind h_nd (LawfulHasIdent.ident_inj h_eq ▸ hk)
  have h_out_exprs_sf : Block.exprsShapeFree (P := P) hoistKind (Block.nondetElim ss) :=
    Block.nondetElimM_exprsShapeFree
      (fun sg => (ndelim_name_not_hoistKind sg).1)
      (fun sg => (ndelim_name_not_hoistKind sg).2)
      ss StringGenState.emp h_hoist_exprs
  have h_out_fresh : Block.hoistedNamesFreshInRhsAndGuards (P := P) (Block.nondetElim ss) = true :=
    nondetElim_hoistedNamesFreshInRhsAndGuards ss h_fresh h_ndelim_exprs
  -- Each init of the `nondetElim` output is undefined in `ρ₀`: by the output
  -- init classification it is either a genuine source init (`h_store_inits`) or a
  -- freshly-minted `ndelimKind` guard (`h_store_mints ∘ Or.inl`).
  have h_out_undef : ∀ y ∈ Block.initVars (Block.nondetElim ss), ρ₀.store y = none := by
    intro y hy
    rcases Block.nondetElimM_initVars_classified ss StringGenState.emp y hy with
      h_src | ⟨str, h_eq, h_nd⟩
    · exact h_store_inits y h_src
    · rw [h_eq]; exact h_store_mints str (Or.inl h_nd)
  -- === STEP 2: hoist (input `nondetElim ss`, source run = Step 1's) ===
  -- StoreAgreement ρ_out.store ρ_h'.store.
  obtain ⟨ρ_h', h_run2, h_agree2, h_hf2⟩ :=
    hoistLoopPrefixInits_preserves_kind (Q := hoistKind) hoistKind_gen
      (extendEval := extendEval) (Block.nondetElim ss)
      (nondetElim_containsNondetLoop ss)
      (nondetElim_containsFuncDecl ss h_nofd)
      (nondetElim_loopHasNoInvariants ss h_lhni)
      (by rw [Block.loopMeasureNone_eq_noMeasureLoops]; exact nondetElim_noMeasureLoops ss h_nml)
      h_out_exprs_sf h_out_unique h_out_fresh
      (fun x hmem s heq hq => h_out_iv_sf s hq (heq ▸ hmem))
      (fun x hmem s heq hq => h_out_mv_sf s hq (heq ▸ hmem))
      h_out_undef
      (fun str hk => h_store_mints str (Or.inr (Or.inl hk)))
      h_run1
      hwfvar' hwfcongr' hwfsubst' hwfdef'
  -- === Direction-B S2U preconds on the hoist output, at `Q := s2uKind` ===
  -- The hoist-output init classification at `Q := hoistKind`: each output init is
  -- a `nondetElim`-output init or a fresh `hoistKind` name; plus `Nodup`.
  have h_hoist_iv_cls :=
    LoopInitHoistLoopArmWF.Block.hoistLoopPrefixInitsM_initVars_classified (Q := hoistKind) hoistKind_gen
      (Block.nondetElim ss) StringGenState.emp StringGenState.wf_emp h_out_unique h_out_iv_sf
  have h_step3_unique : Block.uniqueInits (Block.hoistLoopPrefixInits (Block.nondetElim ss)) :=
    h_hoist_iv_cls.2
  -- Each init of the hoist output is undefined in `ρ₀`: by the output init
  -- classification it is either a `nondetElim`-output init (`h_out_undef`) or a
  -- freshly-minted `hoistKind` name (`h_store_mints ∘ Or.inr ∘ Or.inl`).
  have h_step3_undef : ∀ x ∈ Block.initVars (Block.hoistLoopPrefixInits (Block.nondetElim ss)),
      ρ₀.store x = none := by
    intro x hx
    rcases h_hoist_iv_cls.1 x hx with h_src | ⟨str, h_eq, _, _, h_hoistk⟩
    · exact h_out_undef x h_src
    · rw [h_eq]; exact h_store_mints str (Or.inr (Or.inl h_hoistk))
  -- `NoGenSuffix s2uKind` on the hoist-output `initVars`: each init is foreign to
  -- `s2uKind` — a fresh `hoistKind`, or (further classified) a fresh `ndelimKind`
  -- or a genuine source init (`s2uKind`-free by hypothesis).
  have h_step3_iv : NoGenSuffix (P := P) StructuredToUnstructuredCorrect.s2uKind
      (Block.initVars (Block.hoistLoopPrefixInits (Block.nondetElim ss))) := by
    intro x hx s hxs hk
    rcases h_hoist_iv_cls.1 x hx with h_src | ⟨str, h_eq, _, _, h_hoistk⟩
    · rcases Block.nondetElimM_initVars_classified ss StringGenState.emp x h_src with
        h_src2 | ⟨str2, h_eq2, h_nd⟩
      · exact h_disj_initVars s (Or.inr (Or.inr hk)) (hxs ▸ h_src2)
      · exact ndelimKind_not_s2uKind h_nd (LawfulHasIdent.ident_inj (hxs ▸ h_eq2) ▸ hk)
    · exact hoistKind_not_s2uKind h_hoistk (LawfulHasIdent.ident_inj (hxs ▸ h_eq) ▸ hk)
  -- `NoGenSuffix s2uKind` on `transformBlockModVars` (≡ `Block.modifiedVars`):
  -- each output modVar is foreign to `s2uKind` similarly.
  have h_step3_mv : NoGenSuffix (P := P) StructuredToUnstructuredCorrect.s2uKind
      (StructuredToUnstructuredCorrect.transformBlockModVars
        (Block.hoistLoopPrefixInits (Block.nondetElim ss))) := by
    rw [transformBlockModVars_eq_modifiedVars]
    intro x hx s hxs hk
    rcases LoopInitHoistLoopArmWF.Block.hoistLoopPrefixInitsM_modVars_classified (Q := hoistKind) hoistKind_gen
        (Block.nondetElim ss) StringGenState.emp StringGenState.wf_emp h_out_unique h_out_iv_sf x hx with
      h_src | ⟨str, h_eq, _, _, h_hoistk⟩
    · rw [List.mem_append] at h_src
      rcases h_src with h_mv | h_iv
      · rcases Block.nondetElimM_modVars_classified ss StringGenState.emp x h_mv with
          h_src2 | ⟨str2, h_eq2, h_nd⟩
        · exact h_disj_modVars s (Or.inr hk) (hxs ▸ h_src2)
        · exact ndelimKind_not_s2uKind h_nd (LawfulHasIdent.ident_inj (hxs ▸ h_eq2) ▸ hk)
      · rcases Block.nondetElimM_initVars_classified ss StringGenState.emp x h_iv with
          h_src2 | ⟨str2, h_eq2, h_nd⟩
        · exact h_disj_initVars s (Or.inr (Or.inr hk)) (hxs ▸ h_src2)
        · exact ndelimKind_not_s2uKind h_nd (LawfulHasIdent.ident_inj (hxs ▸ h_eq2) ▸ hk)
    · exact hoistKind_not_s2uKind h_hoistk (LawfulHasIdent.ident_inj (hxs ▸ h_eq) ▸ hk)
  -- === STEP 3: stmtsToCFG (input `hoist (nondetElim ss)`, source run = Step 2's) ===
  -- StoreAgreement ρ_h'.store σ_cfg.
  obtain ⟨σ_cfg, h_run3, h_agree3⟩ :=
    StructuredToUnstructuredCorrect.structuredToUnstructured_sound_kind
      (Q := StructuredToUnstructuredCorrect.s2uKind)
      StructuredToUnstructuredCorrect.s2uKind_gen
      extendEval (Block.hoistLoopPrefixInits (Block.nondetElim ss)) ρ₀ ρ_h'
      hwfb hwfv (hwfdef' ρ₀) (hwfcongr' ρ₀) (hwfvar' ρ₀)
      (hoist_noFuncDecl _ (nondetElim_noFuncDecl ss h_nofd))
      (hoist_simpleShape _ (nondetElim_simpleShape ss))
      h_step3_unique
      (hoist_loopBodyNoInits _)
      (hoist_loopHasNoInvariants _ (nondetElim_loopHasNoInvariants ss h_lhni))
      (hoist_noMeasureLoops _ (nondetElim_noMeasureLoops ss h_nml))
      h_step3_undef
      h_disj
      (fun x hx => h_store_mints x (Or.inr (Or.inr hx)))
      h_step3_iv h_step3_mv
      h_run2
  -- === CHAIN via StoreAgreement.trans (source on the left) ===
  -- the CFG run's failure flag `ρ_h'.hasFailure` equals the source's `ρ'.hasFailure`
  -- (Step 2 preserves it relative to `ρ_out`, Step 1 relative to `ρ'`).
  have h_hf : ρ_h'.hasFailure = ρ'.hasFailure := h_hf2.trans h_hf1
  rw [h_hf] at h_run3
  exact ⟨σ_cfg, h_run3, StoreAgreement.trans h_agree1 (StoreAgreement.trans h_agree2 h_agree3)⟩

end PipelineSound

end Imperative
