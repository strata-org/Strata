/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT

  The `applyRenames` ↔ `substFvarMany` keystone.  This file is load-bearing: it
  is imported by `LoopInitHoistBodyTransport` and `LoopInitHoistStepCProducer`
  (and transitively by the end-to-end theorem `hoistLoopPrefixInits_preserves`).

  It establishes that `Block.applyRenames` (the pass's iterated single-variable
  `substIdent`, applied head-first) agrees with `substFvarMany` (the simultaneous
  fold the transport machinery is stated over) under the freshness the lift
  provides — the bridge that lets the producer rewrite a renamed body one
  statement at a time.
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CmdSemantics
public import Strata.Transform.LoopInitHoist
public import Strata.Transform.LoopInitHoistContains
public import Strata.Transform.LoopInitHoistFreshness
public import Strata.Transform.LoopInitHoistRewrite
public import Strata.Transform.LoopInitHoistInfra
public import Strata.Transform.LoopInitHoistLoopDriver

import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.Cmd
import all Strata.Transform.LoopInitHoist
import all Strata.Transform.LoopInitHoistContains
import all Strata.Transform.LoopInitHoistFreshness
import all Strata.Transform.LoopInitHoistRewrite
import all Strata.Transform.LoopInitHoistInfra

public section

namespace Imperative
namespace OptEKeystone

open StructuredToUnstructuredCorrect (extendStoreOne extendStoreOne_self extendStoreOne_other)

variable {P : PureExpr}

/-! ## Layer 1 — the EXPRESSION-level core.

`Block.applyRenames` folds `Block.substIdent p.1 p.2` over the rename list,
head-first.  On every EXPRESSION position, `substIdent` applies
`HasSubstFvar.substFvar e p.1 (HasFvar.mkFvar p.2)` for that one pair.  So the
expression seen at a leaf after the whole `applyRenames` fold is precisely

    subst.foldl (fun acc p => HasSubstFvar.substFvar acc p.1 (HasFvar.mkFvar p.2)) e

which is the DEFINITION of `substFvarMany e subst` (in `LoopInitHoistInfra`).

THE KEY FINDING: the expression-level keystone is DEFINITIONALLY TRUE.  There is
NO reconciliation gap between "iterated single-var" and "simultaneous" at the
syntactic level, because `substFvarMany` was DEFINED as the iterated single-var
fold — the "simultaneous" semantics live entirely inside the EVAL-level lemmas
(`substFvarMany_eval_tweak`/`_eval_transport`), which is where the freshness /
non-interference reasoning is discharged.  So the syntactic keystone needs NO
freshness preconditions at all. -/

/-! ## Layer 2 — the STRUCTURAL DESCENT.

The gate's REAL content (the part downstream `bodyTransport` actually needs) is
that the OUTER fold `Block.applyRenames subst body` — folding the WHOLE block
through `Block.substIdent` one pair at a time — equals descending the
PER-EXPRESSION simultaneous fold (`substFvarMany`) into the body, i.e. it lands
in exactly the renamed shapes the loop driver consumes:

  * a `.det` guard becomes `substFvarMany g subst`            (driver: `loopDet_lift_renamedGuard_E` / `_TE`)
  * an `assert`/`assume`/`cover` predicate becomes `substFvarMany b subst`
  * an `init`/`set` name becomes its `renameLookup`-image and its rhs `substFvarMany`-renamed
  * sub-blocks (`.block`/`.ite`/`.loop` body) are `applyRenames`-renamed recursively

We prove the structural descent by induction on `subst`, peeling one pair at a
time and pushing it through `Block.substIdent`'s definitional equations.  This is
the bridge between the one-pair-at-a-time `applyRenames` and the per-leaf
`substFvarMany` the transport lemmas speak.  NO freshness is needed for the
SYNTACTIC descent either; the foldl simply commutes with the structural recursion.
-/

/-- `applyRenames` on `[]` is the identity. -/
@[simp] public theorem applyRenames_nil [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident] (ss : List (Stmt P (Cmd P))) :
    Block.applyRenames ([] : List (P.Ident × P.Ident)) ss = ss := rfl

/-- `applyRenames` head-peel: apply the head pair via `Block.substIdent`, then
the tail via `applyRenames`. -/
public theorem applyRenames_cons [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (a b : P.Ident) (rest : List (P.Ident × P.Ident)) (ss : List (Stmt P (Cmd P))) :
    Block.applyRenames ((a, b) :: rest) ss
      = Block.applyRenames rest (Block.substIdent a b ss) := rfl

/-- `applyRenames` of any rename list on the empty block is the empty block
(folding `Block.substIdent` over `[]` keeps `[]` at every step). -/
@[simp] public theorem applyRenames_empty_block [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (subst : List (P.Ident × P.Ident)) :
    Block.applyRenames subst ([] : List (Stmt P (Cmd P))) = [] := by
  induction subst with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    rw [applyRenames_cons, Block.substIdent_nil]
    exact ih

/-- `applyRenames` distributes over `cons` of statements: the per-statement
single-var renames compose to a per-statement `applyRenames`. -/
public theorem applyRenames_stmt_cons [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (subst : List (P.Ident × P.Ident)) (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) :
    Block.applyRenames subst (s :: rest)
      = (subst.foldl (fun acc p => Stmt.substIdent p.1 p.2 acc) s)
        :: Block.applyRenames subst rest := by
  induction subst generalizing s rest with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    rw [applyRenames_cons, Block.substIdent_cons]
    rw [ih]
    rfl

/-- The per-statement iterated single-var fold (head-first) — the analogue of
`substFvarMany` at the `Stmt` level.  This is what `applyRenames` applies to each
statement of the body (by `applyRenames_stmt_cons`). -/
@[expose] def stmtSubstMany [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident] (s : Stmt P (Cmd P)) (subst : List (P.Ident × P.Ident)) :
    Stmt P (Cmd P) :=
  subst.foldl (fun acc p => Stmt.substIdent p.1 p.2 acc) s

@[simp] public theorem stmtSubstMany_nil [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident] (s : Stmt P (Cmd P)) :
    stmtSubstMany s ([] : List (P.Ident × P.Ident)) = s := rfl

@[simp] public theorem stmtSubstMany_cons [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (s : Stmt P (Cmd P)) (a b : P.Ident) (rest : List (P.Ident × P.Ident)) :
    stmtSubstMany s ((a, b) :: rest)
      = stmtSubstMany (Stmt.substIdent a b s) rest := rfl

/-- `applyRenames` on a body = map `stmtSubstMany` over the statements.  This is
the clean characterisation the cons-sequencer (`bodySimES_cons`) consumes: the
hoist body `applyRenames subst body` is the per-statement `stmtSubstMany`-image,
so `bodySimES_cons` can be driven head-statement at a time. -/
public theorem applyRenames_eq_map_stmtSubstMany [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (subst : List (P.Ident × P.Ident)) (ss : List (Stmt P (Cmd P))) :
    Block.applyRenames subst ss = ss.map (fun s => stmtSubstMany s subst) := by
  induction ss with
  | nil => simp
  | cons s rest ih =>
    rw [applyRenames_stmt_cons, List.map_cons, ih]
    rfl

/-! ### The leaf-shape reconciliations — `stmtSubstMany` lands on driver shapes.

For the loop-driver's guard slot the relevant fact is that the iterated fold on a
`.det` guard expression is `substFvarMany g subst`.  We expose the key leaf
descents that show `stmtSubstMany` produces EXACTLY the `substFvarMany` /
`renameLookup` shapes the driver and the per-statement sims speak. -/

/-- A `.det` guard `ExprOrNondet` folds to the `substFvarMany` of its expression.
This is the guard the `loopDet_lift_renamedGuard_E` / `_TE` drivers expect:
`.det (substFvarMany g subst)`. -/
public theorem exprOrNondet_substMany_det [HasFvar P] [HasSubstFvar P]
    (g : P.Expr) (subst : List (P.Ident × P.Ident)) :
    (subst.foldl (fun acc p => ExprOrNondet.substIdent p.1 p.2 acc) (ExprOrNondet.det g))
      = ExprOrNondet.det (substFvarMany g subst) := by
  induction subst generalizing g with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    simp only [List.foldl_cons, ExprOrNondet.substIdent_det]
    rw [ih]
    rfl

/-- `.nondet` is fixed by the fold. -/
public theorem exprOrNondet_substMany_nondet [HasFvar P] [HasSubstFvar P]
    (subst : List (P.Ident × P.Ident)) :
    (subst.foldl (fun acc p => ExprOrNondet.substIdent p.1 p.2 acc)
        (ExprOrNondet.nondet (P := P)))
      = ExprOrNondet.nondet := by
  induction subst with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    simp only [List.foldl_cons, ExprOrNondet.substIdent_nondet]
    exact ih

/-- A nested-loop statement folds to a loop whose `.det` guard is
`substFvarMany g subst` and whose body is `applyRenames subst body` — exactly the
shape `nestedLoop_stmtSimES` / `loopDet_lift_renamedGuard_E` / `_TE` consume.
(Measure-free, invariant-free loops, as the lifted form produces.) -/
public theorem stmtSubstMany_loop_det [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (g : P.Expr) (body : List (Stmt P (Cmd P))) (md : MetaData P)
    (subst : List (P.Ident × P.Ident)) :
    stmtSubstMany (Stmt.loop (.det g) none [] body md) subst
      = Stmt.loop (.det (substFvarMany g subst)) none [] (Block.applyRenames subst body) md := by
  induction subst generalizing g body with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    rw [stmtSubstMany_cons, Stmt.substIdent_loop]
    -- reduce the head-pair rename on guard (.det), measure (none) and invariants ([])
    -- so the IH (stated for the `.det _ none [] _` shape) applies.
    simp only [ExprOrNondet.substIdent_det, Option.map_none, List.map_nil]
    rw [ih]
    -- guard: substFvarMany of (substFvar g a (mkFvar b)) over tl = substFvarMany g ((a,b)::tl)
    -- body: applyRenames tl (substIdent a b body) = applyRenames ((a,b)::tl) body
    rw [applyRenames_cons]
    rfl

/-- An `assert` command folds to `substFvarMany` of its predicate. -/
public theorem cmdSubstMany_assert [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (lbl : String) (e : P.Expr) (md : MetaData P) (subst : List (P.Ident × P.Ident)) :
    (subst.foldl (fun acc p => Cmd.substIdent p.1 p.2 acc) (Cmd.assert lbl e md))
      = Cmd.assert lbl (substFvarMany e subst) md := by
  induction subst generalizing e with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    simp only [List.foldl_cons, Cmd.substIdent_assert]
    rw [ih]
    rfl

/-- An `init` command folds to: name renamed by `renameLookup`, rhs by the
per-`ExprOrNondet` fold.  This shows the NAME-position iterated rename is exactly
`renameLookup` — the same resolver `substFvarMany_eval_tweak` uses — under target
freshness/distinctness.  We state the SYNTACTIC fold here; the `renameLookup`
identification is the freshness-bearing fact, proved next. -/
public theorem cmdSubstMany_init_name_fold [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (name : P.Ident) (ty : P.Ty) (e : ExprOrNondet P) (md : MetaData P)
    (subst : List (P.Ident × P.Ident)) :
    (subst.foldl (fun acc p => Cmd.substIdent p.1 p.2 acc) (Cmd.init name ty e md))
      = Cmd.init
          (subst.foldl (fun acc p => if acc = p.1 then p.2 else acc) name)
          ty
          (subst.foldl (fun acc p => ExprOrNondet.substIdent p.1 p.2 acc) e)
          md := by
  induction subst generalizing name e with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    simp only [List.foldl_cons, Cmd.substIdent_init]
    rw [ih]

/-! ### Freshness reconciliation for the NAME position.

The init/set NAME position is renamed by an iterated `if name = aᵢ then bᵢ`
fold, head-first.  Under the lift's well-formedness — targets `Nodup`, sources
disjoint from targets — this iterated name-fold collapses to `renameLookup subst
name`, the SAME single-pass resolver that `substFvarMany_eval_tweak` uses on the
store.  This is the one place the freshness/uniqueness bundle is genuinely needed
at the SYNTACTIC level: without source-target disjointness a freshly-introduced
target could be re-renamed by a later pair.

PRECONDITION ACTUALLY NEEDED (revealed by the proof): `h_disjoint` (sources
disjoint from targets) — exactly what the pass guarantees and what the driver
already threads.  Source-nodup is NOT needed for the name-fold collapse (only for
`renameLookup_mem`, which the eval lemmas use separately). -/

/-- The iterated name-fold from a value `v` that is NOT a source of any pair is
the identity (no `if v = aᵢ` guard ever fires). -/
public theorem name_fold_notin_id [DecidableEq P.Ident]
    (subst : List (P.Ident × P.Ident)) (v : P.Ident)
    (h : v ∉ subst.map Prod.fst) :
    (subst.foldl (fun acc p => if acc = p.1 then p.2 else acc) v) = v := by
  induction subst generalizing v with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a', b'⟩
    simp only [List.foldl_cons]
    have hva' : v ≠ a' := fun heq => h (by simp [heq])
    rw [if_neg hva']
    exact ih v (fun hmem => h (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hmem))

public theorem name_fold_eq_renameLookup [DecidableEq P.Ident]
    (subst : List (P.Ident × P.Ident)) (name : P.Ident)
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd) :
    (subst.foldl (fun acc p => if acc = p.1 then p.2 else acc) name)
      = renameLookup subst name := by
  induction subst generalizing name with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    simp only [List.foldl_cons, renameLookup_cons]
    by_cases hna : name = a
    · -- name = a: head renames it to b. The tail fold from b is identity because
      -- b is a target (disjointness ⇒ b ∉ tl.fst), and renameLookup tl b = b too.
      subst hna
      rw [if_pos rfl, if_pos rfl]
      have hb_notin_tl_fst : b ∉ tl.map Prod.fst := by
        intro hmem
        exact h_disjoint b (by simp [hmem]) (by simp)
      exact name_fold_notin_id tl b hb_notin_tl_fst
    · -- name ≠ a: head leaves name; recurse with tail-disjointness.
      rw [if_neg hna, if_neg hna]
      apply ih
      intro a' ha' hb'
      exact h_disjoint a' (by simp [ha']) (by simp [hb'])

/-- Full `init` leaf reconciliation: under disjointness the fold lands exactly on
`renameLookup`-renamed name + (for a `.det` rhs) `substFvarMany`-renamed rhs. -/
public theorem cmdSubstMany_init_det [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (name : P.Ident) (ty : P.Ty) (rhs : P.Expr) (md : MetaData P)
    (subst : List (P.Ident × P.Ident))
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd) :
    (subst.foldl (fun acc p => Cmd.substIdent p.1 p.2 acc)
        (Cmd.init name ty (.det rhs) md))
      = Cmd.init (renameLookup subst name) ty (.det (substFvarMany rhs subst)) md := by
  rw [cmdSubstMany_init_name_fold, name_fold_eq_renameLookup subst name h_disjoint,
      exprOrNondet_substMany_det]

/-! ## VERDICT (summary, machine-checked above).

* The EXPRESSION-level keystone is DEFINITIONALLY TRUE: the fold `applyRenames`
  applies to each expression position is `substFvarMany` by definition, with NO
  preconditions.  The "iterated vs simultaneous" reconciliation lives entirely in
  the EVAL-level `substFvarMany_eval_*` lemmas, which already exist and carry the
  freshness bundle.

* The STRUCTURAL descent (`applyRenames_eq_map_stmtSubstMany`,
  `stmtSubstMany_loop_det`, `cmdSubstMany_assert`, `exprOrNondet_substMany_det`)
  is also SYNTACTIC and needs NO freshness — `applyRenames`'s outer fold commutes
  with the structural recursion, landing on the exact `substFvarMany`-guard /
  `applyRenames`-body shapes the loop driver consumes.

* The ONLY freshness-bearing syntactic fact is the init/set NAME-position
  collapse `name_fold_eq_renameLookup`, which needs PRECISELY `h_disjoint`
  (sources disjoint from targets) — already threaded by the pass and driver. -/

end OptEKeystone
end Imperative
