/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
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
public import Strata.Transform.LoopInitHoistKeystone
public import Strata.Transform.LoopInitHoistBodyTransport

import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.Cmd
import all Strata.Transform.LoopInitHoist
import all Strata.Transform.LoopInitHoistContains
import all Strata.Transform.LoopInitHoistFreshness
import all Strata.Transform.LoopInitHoistRewrite
import all Strata.Transform.LoopInitHoistInfra

public section

namespace Imperative
namespace LoopInitHoistStepCProducer

/-!
# Step-C producer: the loop-init hoist pass output inhabits `BodyTransport`.

The loop-init hoist pass processes a `.loop`'s post-order body `body₁` (already
init-free in every nested loop) by harvesting its prefix inits into fresh-name
havocs and rewriting each lifted `init y ty rhs md` to `set y rhs md`, recording
`(y, y')` renames.  The renamed-lifted body is
`body₃ = Block.applyRenames (substOf' (Block.entriesOf body₁ σ))
           (Block.liftInitsInLoopBodyM body₁ σ).1.2.2`.

This module proves that `body₁` and `body₃` are related by the per-statement
`BodyTransport` correspondence relation, at the global carriers harvested from
the lift (`sourcesOf'`/`targetsOf'`/`substOf'` of the entries).  This is the
producer the `.loop` arm of the hoist correctness proof consumes (together with
`Block.bodyTransport`, which turns a `BodyTransport` derivation into the
eval-carrying body simulation the loop driver wants).

The proof is a structural mutual induction over `body₁` MIRRORING the recursion
of `Block.entriesOf`/`Stmt.entriesOf`: `Block.entriesOf_cons` /
`Stmt.entriesOf_block` / `Stmt.entriesOf_ite` peel the entries, the keystone
`applyRenames_eq_map_stmtSubstMany` aligns `body₃` statement-by-statement, and
the per-init `init_site_applyRenames` lands the renamed `set`.

Carriers `A B subst` are fixed at the GLOBAL harvest of the enclosing loop body,
so `body₃`'s every statement is `stmtSubstMany · subst`; the recursion threads a
membership invariant `EntriesIn` (every harvested entry's source/target/pair lies
in `A`/`B`/`subst`), which is monotone across the sub-block recursion, plus the
monotone `Block.namesFreshInExprs` freshness facts over `A` and `B`.
-/

open LoopInitHoistLoopDriver (Entry havocStmts' substOf' targetsOf' sourcesOf'
  Stmt.entriesOf Block.entriesOf Block.entriesOf_cons Stmt.entriesOf_block Stmt.entriesOf_ite)
open LoopInitHoistBodyTransport (BodyTransport)
open OptEKeystone (applyRenames_eq_map_stmtSubstMany applyRenames_cons applyRenames_stmt_cons
  applyRenames_empty_block stmtSubstMany stmtSubstMany_nil stmtSubstMany_cons
  stmtSubstMany_loop_det cmdSubstMany_assert cmdSubstMany_init_det exprOrNondet_substMany_det
  exprOrNondet_substMany_nondet name_fold_eq_renameLookup)

variable {P : PureExpr}

/-! ## Ported leaf helpers from the Step-C scratch.

These align ONE lifted-init site of `body₂` with the `BodyTransport.init_set`
hoist shape under the GLOBAL `subst`.  They are syntactic (no eval), proved from
the keystone fold lemmas; reproduced here so the producer is self-contained. -/

/-- A `.cmd` folds to `.cmd` of the per-`Cmd` fold. -/
theorem stmtSubstMany_cmd [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident] (c : Cmd P) (subst : List (P.Ident × P.Ident)) :
    stmtSubstMany (.cmd c) subst
      = .cmd (subst.foldl (fun acc p => Cmd.substIdent p.1 p.2 acc) c) := by
  induction subst generalizing c with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    rw [stmtSubstMany_cons, Stmt.substIdent_cmd]
    exact ih _

/-- The `set` name-fold (no freshness needed). -/
theorem cmdSubstMany_set_name_fold [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (name : P.Ident) (e : ExprOrNondet P) (md : MetaData P)
    (subst : List (P.Ident × P.Ident)) :
    (subst.foldl (fun acc p => Cmd.substIdent p.1 p.2 acc) (Cmd.set name e md))
      = Cmd.set
          (subst.foldl (fun acc p => if acc = p.1 then p.2 else acc) name)
          (subst.foldl (fun acc p => ExprOrNondet.substIdent p.1 p.2 acc) e)
          md := by
  induction subst generalizing name e with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    simp only [List.foldl_cons, Cmd.substIdent_set]
    exact ih _ _

/-- A `set` command folds: name renamed by `renameLookup`, rhs by `substFvarMany`. -/
theorem cmdSubstMany_set_det [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (name : P.Ident) (rhs : P.Expr) (md : MetaData P)
    (subst : List (P.Ident × P.Ident))
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd) :
    stmtSubstMany (.cmd (.set name (.det rhs) md)) subst
      = .cmd (.set (renameLookup subst name) (.det (substFvarMany rhs subst)) md) := by
  rw [stmtSubstMany_cmd, cmdSubstMany_set_name_fold,
      name_fold_eq_renameLookup subst name h_disjoint, exprOrNondet_substMany_det]

/-- The cmd-only init site of `body₂` becomes, after `applyRenames`
(= `stmtSubstMany` global subst), exactly the `BodyTransport.init_set` hoist
shape. -/
theorem init_site_applyRenames [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (a b : P.Ident) (rhs : P.Expr) (md : MetaData P)
    (subst : List (P.Ident × P.Ident))
    (h_pair : (a, b) ∈ subst)
    (h_src_nodup : (subst.map Prod.fst).Nodup)
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd) :
    stmtSubstMany (.cmd (.set a (.det rhs) md)) subst
      = .cmd (.set b (.det (substFvarMany rhs subst)) md) := by
  rw [cmdSubstMany_set_det a rhs md subst h_disjoint,
      renameLookup_mem subst h_src_nodup h_pair]

/-- A nondet-rhs `set` command folds: name renamed by `renameLookup`, `.nondet`
rhs fixed. -/
theorem cmdSubstMany_set_nondet [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (name : P.Ident) (md : MetaData P)
    (subst : List (P.Ident × P.Ident))
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd) :
    stmtSubstMany (.cmd (.set name .nondet md)) subst
      = .cmd (.set (renameLookup subst name) .nondet md) := by
  rw [stmtSubstMany_cmd, cmdSubstMany_set_name_fold,
      name_fold_eq_renameLookup subst name h_disjoint, exprOrNondet_substMany_nondet]

/-- The nondet-init site of `body₂` (lifted to `set a .nondet`) becomes, after
`applyRenames`, the `BodyTransport.init_nondet` hoist shape `set b .nondet`. -/
theorem init_nondet_site_applyRenames [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (a b : P.Ident) (md : MetaData P)
    (subst : List (P.Ident × P.Ident))
    (h_pair : (a, b) ∈ subst)
    (h_src_nodup : (subst.map Prod.fst).Nodup)
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd) :
    stmtSubstMany (.cmd (.set a .nondet md)) subst
      = .cmd (.set b .nondet md) := by
  rw [cmdSubstMany_set_nondet a md subst h_disjoint,
      renameLookup_mem subst h_src_nodup h_pair]

/-- A genuine (non-lifted) `.set name (.det rhs)`'s name is UNCHANGED by the
rename (its `name ∉ subst sources`), and its rhs is `substFvarMany`-renamed. -/
theorem set_site_applyRenames [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (name : P.Ident) (rhs : P.Expr) (md : MetaData P)
    (subst : List (P.Ident × P.Ident))
    (h_name_notin_src : name ∉ subst.map Prod.fst)
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd) :
    stmtSubstMany (.cmd (.set name (.det rhs) md)) subst
      = .cmd (.set name (.det (substFvarMany rhs subst)) md) := by
  rw [cmdSubstMany_set_det name rhs md subst h_disjoint,
      renameLookup_notin subst name h_name_notin_src]

/-- A genuine (non-lifted) `.set name .nondet`'s name is UNCHANGED by the rename. -/
theorem set_nondet_site_applyRenames [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (name : P.Ident) (md : MetaData P)
    (subst : List (P.Ident × P.Ident))
    (h_name_notin_src : name ∉ subst.map Prod.fst)
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd) :
    stmtSubstMany (.cmd (.set name .nondet md)) subst
      = .cmd (.set name .nondet md) := by
  rw [cmdSubstMany_set_nondet name md subst h_disjoint,
      renameLookup_notin subst name h_name_notin_src]

/-! ## `assert`/`assume`/`cover` fold to renamed predicates. -/

theorem stmtSubstMany_cmd_assert [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (lbl : String) (e : P.Expr) (md : MetaData P) (subst : List (P.Ident × P.Ident)) :
    stmtSubstMany (.cmd (.assert lbl e md)) subst
      = .cmd (.assert lbl (substFvarMany e subst) md) := by
  rw [stmtSubstMany_cmd, cmdSubstMany_assert]

theorem stmtSubstMany_cmd_assume [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (lbl : String) (e : P.Expr) (md : MetaData P) (subst : List (P.Ident × P.Ident)) :
    stmtSubstMany (.cmd (.assume lbl e md)) subst
      = .cmd (.assume lbl (substFvarMany e subst) md) := by
  rw [stmtSubstMany_cmd]
  congr 1
  induction subst generalizing e with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨x, y⟩
    simp only [List.foldl_cons, Cmd.substIdent_assume]
    rw [ih]; rfl

theorem stmtSubstMany_cmd_cover [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (lbl : String) (e : P.Expr) (md : MetaData P) (subst : List (P.Ident × P.Ident)) :
    stmtSubstMany (.cmd (.cover lbl e md)) subst
      = .cmd (.cover lbl (substFvarMany e subst) md) := by
  rw [stmtSubstMany_cmd]
  congr 1
  induction subst generalizing e with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨x, y⟩
    simp only [List.foldl_cons, Cmd.substIdent_cover]
    rw [ih]; rfl

/-! ## `.block` / `.ite` fold to renamed sub-blocks. -/

theorem stmtSubstMany_block [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (lbl : String) (bss : List (Stmt P (Cmd P))) (md : MetaData P)
    (subst : List (P.Ident × P.Ident)) :
    stmtSubstMany (.block lbl bss md) subst
      = .block lbl (Block.applyRenames subst bss) md := by
  induction subst generalizing bss with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨x, y⟩
    rw [stmtSubstMany_cons, Stmt.substIdent_block, ih, applyRenames_cons]

theorem stmtSubstMany_ite [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (g : P.Expr) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (subst : List (P.Ident × P.Ident)) :
    stmtSubstMany (.ite (.det g) tss ess md) subst
      = .ite (.det (substFvarMany g subst))
          (Block.applyRenames subst tss) (Block.applyRenames subst ess) md := by
  induction subst generalizing g tss ess with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨x, y⟩
    rw [stmtSubstMany_cons, Stmt.substIdent_ite]
    simp only [ExprOrNondet.substIdent_det]
    rw [ih, applyRenames_cons, applyRenames_cons]
    rfl

theorem stmtSubstMany_ite_nondet [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (subst : List (P.Ident × P.Ident)) :
    stmtSubstMany (.ite .nondet tss ess md) subst
      = .ite .nondet
          (Block.applyRenames subst tss) (Block.applyRenames subst ess) md := by
  induction subst generalizing tss ess with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨x, y⟩
    rw [stmtSubstMany_cons, Stmt.substIdent_ite]
    simp only [ExprOrNondet.substIdent_nondet]
    rw [ih, applyRenames_cons, applyRenames_cons]

theorem stmtSubstMany_typeDecl [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (tc : TypeConstructor) (md : MetaData P) (subst : List (P.Ident × P.Ident)) :
    stmtSubstMany (.typeDecl tc md) subst = (.typeDecl tc md : Stmt P (Cmd P)) := by
  induction subst with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨x, y⟩
    rw [stmtSubstMany_cons, Stmt.substIdent_typeDecl]; exact ih

/-- An `.exit` is left literally unchanged by the rename fold (`substIdent_exit`). -/
theorem stmtSubstMany_exit [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (lbl : String) (md : MetaData P) (subst : List (P.Ident × P.Ident)) :
    stmtSubstMany (.exit lbl md) subst = (.exit lbl md : Stmt P (Cmd P)) := by
  induction subst with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨x, y⟩
    rw [stmtSubstMany_cons, Stmt.substIdent_exit]; exact ih

/-! ## The membership invariant carried through the recursion. -/

/-- Every entry harvested from `body₁` at `σ` has its source ident in `A`, its
target ident in `B`, and its `(source, target)` pair in `subst`.  This is the
positional connection between each `init`/expr in `body₁` and its entry, kept at
the GLOBAL carriers; monotone across the sub-block recursion. -/
def EntriesIn [HasIdent P] (A B : List P.Ident) (subst : List (P.Ident × P.Ident))
    (body₁ : List (Stmt P (Cmd P))) (σ : StringGenState) : Prop :=
  ∀ e ∈ Block.entriesOf body₁ σ, e.1 ∈ A ∧ e.2.1 ∈ B ∧ (e.1, e.2.1) ∈ subst

theorem EntriesIn.cons_head [HasIdent P]
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))} {σ : StringGenState}
    (h : EntriesIn A B subst (s :: rest) σ) :
    ∀ e ∈ Stmt.entriesOf s σ, e.1 ∈ A ∧ e.2.1 ∈ B ∧ (e.1, e.2.1) ∈ subst := by
  intro e he
  refine h e ?_
  rw [Block.entriesOf_cons]
  exact List.mem_append.mpr (Or.inl he)

theorem EntriesIn.cons_tail [HasIdent P]
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))} {σ : StringGenState}
    (h : EntriesIn A B subst (s :: rest) σ) :
    EntriesIn A B subst rest (Stmt.liftInitsInLoopBodyM s σ).2 := by
  intro e he
  refine h e ?_
  rw [Block.entriesOf_cons]
  exact List.mem_append.mpr (Or.inr he)

theorem EntriesIn.block [HasIdent P]
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {lbl : String} {bss : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))} {σ : StringGenState}
    (h : EntriesIn A B subst (.block lbl bss md :: rest) σ) :
    EntriesIn A B subst bss σ := by
  intro e he
  apply EntriesIn.cons_head h e
  rw [Stmt.entriesOf_block]
  exact he

theorem EntriesIn.ite_then [HasIdent P]
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))} {σ : StringGenState}
    (h : EntriesIn A B subst (.ite g tss ess md :: rest) σ) :
    EntriesIn A B subst tss σ := by
  intro e he
  apply EntriesIn.cons_head h e
  rw [Stmt.entriesOf_ite]
  exact List.mem_append.mpr (Or.inl he)

theorem EntriesIn.ite_else [HasIdent P]
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))} {σ : StringGenState}
    (h : EntriesIn A B subst (.ite g tss ess md :: rest) σ) :
    EntriesIn A B subst ess (Block.liftInitsInLoopBodyM tss σ).2 := by
  intro e he
  apply EntriesIn.cons_head h e
  rw [Stmt.entriesOf_ite]
  exact List.mem_append.mpr (Or.inr he)

/-- The head init's entry pair, at the head of the entries list. -/
theorem entriesOf_init_head_mem [HasIdent P]
    (a : P.Ident) (τ : P.Ty) (rhs : ExprOrNondet P) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ((a, HasIdent.ident (P := P) (StringGenState.gen hoistFreshPrefix σ).1, τ, md) : Entry P)
      ∈ Block.entriesOf (.cmd (.init a τ rhs md) :: rest) σ := by
  rw [Block.entriesOf_cons, Stmt.entriesOf]
  exact List.mem_append.mpr (Or.inl (by simp))

/-! ## Per-statement freshness extraction from `namesFreshInExprs`. -/

theorem namesFresh_cmd_init [HasVarsPure P P.Expr]
    {names : List P.Ident} {a : P.Ident} {τ : P.Ty} {rhs : P.Expr} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))}
    (h : Block.namesFreshInExprs names (.cmd (.init a τ (.det rhs) md) :: rest) = true) :
    (∀ x ∈ names, x ∉ HasVarsPure.getVars rhs) ∧
      Block.namesFreshInExprs names rest = true := by
  simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_eq_true] at h
  refine ⟨?_, h.2⟩
  intro x hx
  have := (List.all_eq_true.mp h.1) x hx
  exact freshFromIdents_not_mem (by simpa [ExprOrNondet.getVars] using this)

theorem namesFresh_cmd_set_det [HasVarsPure P P.Expr]
    {names : List P.Ident} {name : P.Ident} {rhs : P.Expr} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))}
    (h : Block.namesFreshInExprs names (.cmd (.set name (.det rhs) md) :: rest) = true) :
    (∀ x ∈ names, x ∉ HasVarsPure.getVars rhs) ∧
      Block.namesFreshInExprs names rest = true := by
  simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_eq_true] at h
  refine ⟨?_, h.2⟩
  intro x hx
  have := (List.all_eq_true.mp h.1) x hx
  exact freshFromIdents_not_mem (by simpa [ExprOrNondet.getVars] using this)

theorem namesFresh_cmd_assert [HasVarsPure P P.Expr]
    {names : List P.Ident} {lbl : String} {e : P.Expr} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))}
    (h : Block.namesFreshInExprs names (.cmd (.assert lbl e md) :: rest) = true) :
    (∀ x ∈ names, x ∉ HasVarsPure.getVars e) ∧
      Block.namesFreshInExprs names rest = true := by
  simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_eq_true] at h
  refine ⟨?_, h.2⟩
  intro x hx
  exact freshFromIdents_not_mem ((List.all_eq_true.mp h.1) x hx)

theorem namesFresh_cmd_assume [HasVarsPure P P.Expr]
    {names : List P.Ident} {lbl : String} {e : P.Expr} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))}
    (h : Block.namesFreshInExprs names (.cmd (.assume lbl e md) :: rest) = true) :
    (∀ x ∈ names, x ∉ HasVarsPure.getVars e) ∧
      Block.namesFreshInExprs names rest = true := by
  simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_eq_true] at h
  refine ⟨?_, h.2⟩
  intro x hx
  exact freshFromIdents_not_mem ((List.all_eq_true.mp h.1) x hx)

theorem namesFresh_block [HasVarsPure P P.Expr]
    {names : List P.Ident} {lbl : String} {bss : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))}
    (h : Block.namesFreshInExprs names (.block lbl bss md :: rest) = true) :
    Block.namesFreshInExprs names bss = true ∧
      Block.namesFreshInExprs names rest = true := by
  simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_eq_true] at h
  exact h

theorem namesFresh_ite [HasVarsPure P P.Expr]
    {names : List P.Ident} {g : P.Expr} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))}
    (h : Block.namesFreshInExprs names (.ite (.det g) tss ess md :: rest) = true) :
    (∀ x ∈ names, x ∉ HasVarsPure.getVars g) ∧
      Block.namesFreshInExprs names tss = true ∧
      Block.namesFreshInExprs names ess = true ∧
      Block.namesFreshInExprs names rest = true := by
  simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h_g, h_tss⟩, h_ess⟩, h_rest⟩ := h
  refine ⟨?_, h_tss, h_ess, h_rest⟩
  intro x hx
  exact freshFromIdents_not_mem (by simpa [ExprOrNondet.getVars] using ((List.all_eq_true.mp h_g) x hx))

theorem namesFresh_ite_nondet [HasVarsPure P P.Expr]
    {names : List P.Ident} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))}
    (h : Block.namesFreshInExprs names (.ite .nondet tss ess md :: rest) = true) :
    Block.namesFreshInExprs names tss = true ∧
      Block.namesFreshInExprs names ess = true := by
  simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, h_tss⟩, h_ess⟩, _⟩ := h
  exact ⟨h_tss, h_ess⟩

theorem namesFresh_loop [HasVarsPure P P.Expr]
    {names : List P.Ident} {g : P.Expr} {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))}
    (h : Block.namesFreshInExprs names (.loop (.det g) none [] body md :: rest) = true) :
    (∀ x ∈ names, x ∉ HasVarsPure.getVars g) ∧
      Block.namesFreshInExprs names body = true ∧
      Block.namesFreshInExprs names rest = true := by
  simp only [Block.namesFreshInExprs, Stmt.namesFreshInExprs, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at h
  obtain ⟨⟨h_g, h_body⟩, h_rest⟩ := h
  refine ⟨?_, h_body, h_rest⟩
  intro x hx
  exact freshFromIdents_not_mem (by simpa [ExprOrNondet.getVars] using ((List.all_eq_true.mp h_g) x hx))

/-! ## `modifiedVars` peel helpers (for the `.set` name-disjointness side-conditions). -/

/-- The head `.set name`'s name is in the body's `modifiedVars`. -/
theorem set_name_mem_modifiedVars
    (name : P.Ident) (rhs : ExprOrNondet P) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) :
    name ∈ Block.modifiedVars (.cmd (.set name rhs md) :: rest) := by
  simp [Block.modifiedVars, Stmt.modifiedVars, HasVarsImp.modifiedVars, Cmd.modifiedVars]

theorem modifiedVars_cons_tail
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))} {x : P.Ident}
    (hx : x ∈ Block.modifiedVars rest) :
    x ∈ Block.modifiedVars (s :: rest) := by
  simp only [Block.modifiedVars, List.mem_append]
  exact Or.inr hx

theorem modifiedVars_block_subset
    {lbl : String} {bss : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))} {x : P.Ident}
    (hx : x ∈ Block.modifiedVars bss) :
    x ∈ Block.modifiedVars (.block lbl bss md :: rest) := by
  simp only [Block.modifiedVars, Stmt.modifiedVars, List.mem_append]
  exact Or.inl hx

theorem modifiedVars_ite_then_subset
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))} {x : P.Ident}
    (hx : x ∈ Block.modifiedVars tss) :
    x ∈ Block.modifiedVars (.ite g tss ess md :: rest) := by
  simp only [Block.modifiedVars, Stmt.modifiedVars, List.mem_append]
  exact Or.inl (Or.inl hx)

theorem modifiedVars_ite_else_subset
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))} {x : P.Ident}
    (hx : x ∈ Block.modifiedVars ess) :
    x ∈ Block.modifiedVars (.ite g tss ess md :: rest) := by
  simp only [Block.modifiedVars, Stmt.modifiedVars, List.mem_append]
  exact Or.inl (Or.inr hx)

theorem modifiedVars_loop_subset
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {lbody : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))} {x : P.Ident}
    (hx : x ∈ Block.modifiedVars lbody) :
    x ∈ Block.modifiedVars (.loop g m inv lbody md :: rest) := by
  simp only [Block.modifiedVars, Stmt.modifiedVars, List.mem_append]
  exact Or.inl hx

/-! ## `allLoopBodiesInitFree` peel helpers. -/

theorem initfree_cons
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))}
    (h : Block.allLoopBodiesInitFree (s :: rest) = true) :
    Stmt.allLoopBodiesInitFree s = true ∧ Block.allLoopBodiesInitFree rest = true := by
  simp only [Block.allLoopBodiesInitFree, Bool.and_eq_true] at h
  exact h

theorem initfree_block
    {lbl : String} {bss : List (Stmt P (Cmd P))} {md : MetaData P}
    (h : Stmt.allLoopBodiesInitFree (.block lbl bss md) = true) :
    Block.allLoopBodiesInitFree bss = true := by
  simpa [Stmt.allLoopBodiesInitFree] using h

theorem initfree_ite
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    (h : Stmt.allLoopBodiesInitFree (.ite g tss ess md) = true) :
    Block.allLoopBodiesInitFree tss = true ∧ Block.allLoopBodiesInitFree ess = true := by
  simp only [Stmt.allLoopBodiesInitFree, Bool.and_eq_true] at h
  exact h

theorem initfree_loop_noinits
    {g : ExprOrNondet P} {body : List (Stmt P (Cmd P))} {md : MetaData P}
    (h : Stmt.allLoopBodiesInitFree (.loop g none [] body md) = true) :
    Block.noInitsAnywhere body = true ∧ Block.allLoopBodiesInitFree body = true := by
  simp only [Stmt.allLoopBodiesInitFree, Bool.and_eq_true] at h
  exact h

mutual
/-- A `noInitsAnywhere` statement has empty `Stmt.entriesOf` (no `.init` to
harvest, and loops are passed through). -/
theorem Stmt.entriesOf_noInits [HasIdent P]
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (h : Stmt.noInitsAnywhere s = true) :
    Stmt.entriesOf s σ = [] := by
  match s with
  | .cmd c =>
      cases c with
      | init _ _ _ _ => exact absurd h (by simp [Stmt.noInitsAnywhere])
      | _ => simp [Stmt.entriesOf]
  | .block lbl bss md =>
      rw [Stmt.entriesOf_block]
      exact Block.entriesOf_noInits bss σ (by simpa [Stmt.noInitsAnywhere] using h)
  | .ite g tss ess md =>
      rw [Stmt.entriesOf_ite]
      simp only [Stmt.noInitsAnywhere, Bool.and_eq_true] at h
      rw [Block.entriesOf_noInits tss σ h.1,
          Block.entriesOf_noInits ess _ h.2, List.append_nil]
  | .loop g m inv body md => rw [Stmt.entriesOf]
  | .exit lbl md => rw [Stmt.entriesOf]
  | .funcDecl d md => rw [Stmt.entriesOf]
  | .typeDecl t md => rw [Stmt.entriesOf]
  termination_by sizeOf s

/-- A `noInitsAnywhere` body has empty `entriesOf` (no `.init` to harvest, and
loops are passed through). -/
theorem Block.entriesOf_noInits [HasIdent P]
    (body : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h : Block.noInitsAnywhere body = true) :
    Block.entriesOf body σ = [] := by
  match body with
  | [] => rw [Block.entriesOf]
  | s :: rest =>
      rw [Block.entriesOf_cons]
      simp only [Block.noInitsAnywhere, Bool.and_eq_true] at h
      rw [Stmt.entriesOf_noInits s σ h.1,
          Block.entriesOf_noInits rest _ h.2, List.append_nil]
  termination_by sizeOf body
end

/-! ## `applyRenames` distributes over `++`. -/

theorem applyRenames_append [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (subst : List (P.Ident × P.Ident)) (xs ys : List (Stmt P (Cmd P))) :
    Block.applyRenames subst (xs ++ ys)
      = Block.applyRenames subst xs ++ Block.applyRenames subst ys := by
  rw [applyRenames_eq_map_stmtSubstMany, applyRenames_eq_map_stmtSubstMany,
      applyRenames_eq_map_stmtSubstMany, List.map_append]

/-- `applyRenames` of a singleton statement is the singleton `stmtSubstMany`. -/
theorem applyRenames_singleton [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (subst : List (P.Ident × P.Ident)) (s : Stmt P (Cmd P)) :
    Block.applyRenames subst [s] = [stmtSubstMany s subst] := by
  rw [applyRenames_eq_map_stmtSubstMany, List.map_cons, List.map_nil]

/-- The per-pair source-functional uniqueness the `init_set` constructor wants:
distinct sources, so a source resolves to a unique target. -/
theorem unique_of_src_nodup [DecidableEq P.Ident]
    {subst : List (P.Ident × P.Ident)} {a b : P.Ident}
    (h_src_nodup : (subst.map Prod.fst).Nodup) (h_pair : (a, b) ∈ subst) :
    ∀ a' b', (a', b') ∈ subst → a' = a → b' = b := by
  intro a' b' h_mem h_eq
  subst h_eq
  have e1 : renameLookup subst a' = b' := renameLookup_mem subst h_src_nodup h_mem
  have e2 : renameLookup subst a' = b := renameLookup_mem subst h_src_nodup h_pair
  rw [e1] at e2; exact e2

/-- Target-side analog: distinct targets, so a target resolves to a unique
source.  Proved by induction on `subst` mirroring `renameLookup`. -/
theorem unique_of_tgt_nodup
    {subst : List (P.Ident × P.Ident)} {a b : P.Ident}
    (h_tgt_nodup : (subst.map Prod.snd).Nodup) (h_pair : (a, b) ∈ subst) :
    ∀ a' b', (a', b') ∈ subst → b' = b → a' = a := by
  intro a' b' h_mem h_eq
  subst h_eq
  induction subst with
  | nil => simp at h_pair
  | cons hd tl ih =>
    rcases hd with ⟨x, y⟩
    simp only [List.map_cons, List.nodup_cons] at h_tgt_nodup
    rcases List.mem_cons.mp h_pair with h_eq1 | h_in1 <;>
      rcases List.mem_cons.mp h_mem with h_eq2 | h_in2
    · simp only [Prod.mk.injEq] at h_eq1 h_eq2
      rw [h_eq1.1, h_eq2.1]
    · -- (a,b') = (x,y) so b'=y; (a',b')∈tl so b'∈ tl.snd; tgt nodup ⊥
      simp only [Prod.mk.injEq] at h_eq1
      exact absurd (List.mem_map.mpr ⟨(a', b'), h_in2, by rw [h_eq1.2]⟩) h_tgt_nodup.1
    · simp only [Prod.mk.injEq] at h_eq2
      exact absurd (List.mem_map.mpr ⟨(a, b'), h_in1, by rw [h_eq2.2]⟩) h_tgt_nodup.1
    · exact ih h_tgt_nodup.2 h_in2 h_in1

/-! ## The BodyTransport-expressible structural fragment.

`BodyTransport` (read its constructors) covers: `.det`-rhs `init`, `.nondet`-rhs
`init`, `.det`-rhs `set`, `.nondet`-rhs `set`, `assert`/`assume`/`cover`,
`.block`, `.det`-guard `.ite`, `.nondet`-guard `.ite`, `.typeDecl`, an `.exit`,
and a measure-free, invariant-free, `.det`-guard nested `.loop`.  It carries NO
constructor for a measured / invariant-bearing / `.nondet`-guard `.loop` or a
`.funcDecl`.

`transportShape` is the Bool walker that asserts a body lies in this expressible
fragment.  Via `transportShape_of_arm_preconds` below it FOLLOWS FROM the genuine
§E `.loop` arm Bool preconditions ALONE (`containsNondetLoop = false`,
`containsFuncDecl = false`, `loopHasNoInvariants = true`, `loopMeasureNone =
true`).  An `.exit` is now admitted: `BodyTransport` carries an `.exit`
constructor and `Block.bodyTransport` produces a SUM-TYPED `BodySimES`, so a
`.block` whose inner body breaks (and the loop early-exit pattern) is handled by
the banked `block_stmtSimES` / `exit_stmtSimES` arms — no `noExit` residual is
needed. -/

mutual
@[expose] def Stmt.transportShape (s : Stmt P (Cmd P)) : Bool :=
  match s with
  | .cmd (.init _ _ (.det _) _) => true
  | .cmd (.init _ _ .nondet _) => true
  | .cmd (.set _ (.det _) _) => true
  | .cmd (.set _ .nondet _) => true
  | .cmd (.assert _ _ _) => true
  | .cmd (.assume _ _ _) => true
  | .cmd (.cover _ _ _) => true
  | .block _ bss _ => Block.transportShape bss
  | .ite (.det _) tss ess _ => Block.transportShape tss && Block.transportShape ess
  | .ite .nondet tss ess _ => Block.transportShape tss && Block.transportShape ess
  | .loop (.det _) none [] lbody _ => Block.transportShape lbody
  | .loop _ _ _ _ _ => false
  | .exit _ _ => true
  | .funcDecl _ _ => false
  | .typeDecl _ _ => true
  termination_by sizeOf s

@[expose] def Block.transportShape (ss : List (Stmt P (Cmd P))) : Bool :=
  match ss with
  | [] => true
  | s :: rest => Stmt.transportShape s && Block.transportShape rest
  termination_by sizeOf ss
end

/-! ## `transportShape` from the §E `.loop` arm Bool preconditions.

With `BodyTransport` now carrying an `.exit` constructor (and `Block.bodyTransport`
producing a SUM-TYPED `BodySimES`, so an inner body that breaks is handled), the
expressible fragment ADMITS `.exit` anywhere — `transportShape (.exit _ _) = true`.
The residual `noExit` requirement is therefore GONE.

`transportShape` FOLLOWS FROM the genuine §E `.loop` arm Bool preconditions ALONE
(`containsNondetLoop = false`, `containsFuncDecl = false`, `loopHasNoInvariants =
true`, `loopMeasureNone = true`).  Proved by mutual structural induction; each
statement constructor reduces to its sub-blocks under the corresponding Bool-walker
reductions (the `.exit` arm is now a trivial `true`). -/
mutual
theorem Stmt.transportShape_of_arm_preconds
    (s : Stmt P (Cmd P))
    (h_nd : Stmt.containsNondetLoop s = false)
    (h_fd : Stmt.containsFuncDecl s = false)
    (h_inv : Stmt.loopHasNoInvariants s = true)
    (h_measure : Stmt.loopMeasureNone s = true) :
    Stmt.transportShape s = true := by
  match s with
  | .cmd c =>
      cases c with
      | init _ _ rhs _ => cases rhs <;> simp only [Stmt.transportShape]
      | set _ rhs _ => cases rhs <;> simp only [Stmt.transportShape]
      | assert _ _ _ => simp only [Stmt.transportShape]
      | assume _ _ _ => simp only [Stmt.transportShape]
      | cover _ _ _ => simp only [Stmt.transportShape]
  | .block lbl bss md =>
      simp only [Stmt.transportShape]
      exact Block.transportShape_of_arm_preconds bss
        (by simpa only [Stmt.containsNondetLoop] using h_nd)
        (by simpa only [Stmt.containsFuncDecl] using h_fd)
        (by simpa only [Stmt.loopHasNoInvariants] using h_inv)
        (by simpa only [Stmt.loopMeasureNone] using h_measure)
  | .ite g tss ess md =>
      simp only [Stmt.containsNondetLoop, Bool.or_eq_false_iff] at h_nd
      simp only [Stmt.containsFuncDecl, Bool.or_eq_false_iff] at h_fd
      simp only [Stmt.loopHasNoInvariants, Bool.and_eq_true] at h_inv
      simp only [Stmt.loopMeasureNone, Bool.and_eq_true] at h_measure
      have h_t := Block.transportShape_of_arm_preconds tss h_nd.1 h_fd.1 h_inv.1 h_measure.1
      have h_e := Block.transportShape_of_arm_preconds ess h_nd.2 h_fd.2 h_inv.2 h_measure.2
      cases g <;>
        simp only [Stmt.transportShape, Bool.and_eq_true] <;> exact ⟨h_t, h_e⟩
  | .loop g m inv body md =>
      -- `containsNondetLoop` forces a `.det` guard; `loopMeasureNone` forces `m = none`;
      -- `loopHasNoInvariants` forces `inv = []`.  Then recurse on the body.
      cases g with
      | nondet => exact absurd h_nd (by simp [Stmt.containsNondetLoop])
      | det g' =>
        have h_m : m = none := by
          rw [Stmt.loopMeasureNone, Bool.and_eq_true] at h_measure
          exact Option.isNone_iff_eq_none.mp h_measure.1
        have h_inv_nil : inv = [] := by
          rw [Stmt.loopHasNoInvariants, Bool.and_eq_true] at h_inv
          exact List.isEmpty_iff.mp h_inv.1
        subst h_m; subst h_inv_nil
        simp only [Stmt.transportShape]
        exact Block.transportShape_of_arm_preconds body
          (by simpa only [Stmt.containsNondetLoop] using h_nd)
          (by simpa only [Stmt.containsFuncDecl] using h_fd)
          (by rw [Stmt.loopHasNoInvariants, Bool.and_eq_true] at h_inv; exact h_inv.2)
          (by rw [Stmt.loopMeasureNone, Bool.and_eq_true] at h_measure; exact h_measure.2)
  | .exit lbl md => simp only [Stmt.transportShape]
  | .funcDecl d md => exact absurd h_fd (by simp [Stmt.containsFuncDecl])
  | .typeDecl t md => simp only [Stmt.transportShape]
  termination_by sizeOf s

theorem Block.transportShape_of_arm_preconds
    (ss : List (Stmt P (Cmd P)))
    (h_nd : Block.containsNondetLoop ss = false)
    (h_fd : Block.containsFuncDecl ss = false)
    (h_inv : Block.loopHasNoInvariants ss = true)
    (h_measure : Block.loopMeasureNone ss = true) :
    Block.transportShape ss = true := by
  match ss with
  | [] => simp only [Block.transportShape]
  | s :: rest =>
      simp only [Block.containsNondetLoop, Bool.or_eq_false_iff] at h_nd
      simp only [Block.containsFuncDecl, Bool.or_eq_false_iff] at h_fd
      simp only [Block.loopHasNoInvariants, Bool.and_eq_true] at h_inv
      simp only [Block.loopMeasureNone, Bool.and_eq_true] at h_measure
      simp only [Block.transportShape, Bool.and_eq_true]
      exact ⟨Stmt.transportShape_of_arm_preconds s h_nd.1 h_fd.1 h_inv.1 h_measure.1,
             Block.transportShape_of_arm_preconds rest h_nd.2 h_fd.2 h_inv.2 h_measure.2⟩
  termination_by sizeOf ss
end

/-! ## The producer.

Structural induction over `body₁`, mirroring `Block.entriesOf`'s recursion.  The
hoist body is `body₃ = applyRenames subst (lift residual)`.  Carriers `A B subst`
are the GLOBAL harvest of the enclosing loop body, so each statement of `body₃`
is `stmtSubstMany · subst`; the recursion threads the `EntriesIn` membership
invariant (monotone across sub-blocks) and the monotone `namesFreshInExprs`
freshness facts over `A` and `B`. -/

theorem Block.bodyTransport_of_lift [HasFvar P] [HasIdent P] [HasSubstFvar P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    (body₁ : List (Stmt P (Cmd P))) (σ : StringGenState)
    (A B : List P.Ident) (subst : List (P.Ident × P.Ident))
    (h_initfree : Block.allLoopBodiesInitFree body₁ = true)
    (h_entries : EntriesIn A B subst body₁ σ)
    (h_B_fresh : Block.namesFreshInExprs B body₁ = true)
    (h_mod_disjoint_B : ∀ x ∈ Block.modifiedVars body₁, x ∉ B)
    (h_subst_wf : ∀ a b, (a, b) ∈ subst → a ∈ A ∧ b ∈ B)
    (h_A_subst_fst : ∀ a ∈ A, a ∈ subst.map Prod.fst)
    (h_src_nodup : (subst.map Prod.fst).Nodup)
    (h_tgt_nodup : (subst.map Prod.snd).Nodup)
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd)
    (h_shape : Block.transportShape body₁ = true) :
    BodyTransport A B subst
      body₁
      (Block.applyRenames subst (Block.liftInitsInLoopBodyM body₁ σ).1.2.2) := by
  match body₁ with
  | [] =>
      -- residual of [] is [], applyRenames _ [] = [].
      have h_res : (Block.liftInitsInLoopBodyM ([] : List (Stmt P (Cmd P))) σ).1.2.2 = [] := by
        rw [Block.liftInitsInLoopBodyM]
      rw [h_res, applyRenames_empty_block]
      exact BodyTransport.nil
  | s :: rest =>
      -- Peel the residual and applyRenames over the cons append.
      rw [Block.liftInitsInLoopBodyM_cons_residual, applyRenames_append]
      -- structural facts for the tail.
      obtain ⟨h_if_s, h_if_rest⟩ := initfree_cons h_initfree
      obtain ⟨h_shape_s, h_shape_rest⟩ : Stmt.transportShape s = true ∧ Block.transportShape rest = true := by
        simpa only [Block.transportShape, Bool.and_eq_true] using h_shape
      have h_entries_tail : EntriesIn A B subst rest (Stmt.liftInitsInLoopBodyM s σ).2 :=
        EntriesIn.cons_tail h_entries
      have h_tail :
          BodyTransport A B subst rest
            (Block.applyRenames subst
              (Block.liftInitsInLoopBodyM rest (Stmt.liftInitsInLoopBodyM s σ).2).1.2.2) := by
        refine Block.bodyTransport_of_lift rest (Stmt.liftInitsInLoopBodyM s σ).2 A B subst
          h_if_rest h_entries_tail ?_ ?_ h_subst_wf h_A_subst_fst
          h_src_nodup h_tgt_nodup h_disjoint h_shape_rest
        · simp only [Block.namesFreshInExprs, Bool.and_eq_true] at h_B_fresh; exact h_B_fresh.2
        · exact fun x hx => h_mod_disjoint_B x (modifiedVars_cons_tail hx)
      -- Now case on the head statement.  `s` is restricted to the
      -- BodyTransport-expressible fragment by `h_shape` (see `transportShape`).
      match s, h_if_s, h_entries, h_B_fresh, h_mod_disjoint_B, h_shape_s with
      | .cmd (.init a τ (.det rhs0) md), _, h_entries, h_B_fresh, _, _ =>
          -- residual of a .det init = [.cmd (.set a (.det rhs0) md)].
          have h_sres : (Stmt.liftInitsInLoopBodyM (.cmd (.init a τ (.det rhs0) md)) σ).1.2.2
              = [.cmd (.set a (.det rhs0) md)] := by
            rw [Stmt.liftInitsInLoopBodyM]
          rw [h_sres, applyRenames_singleton]
          -- the head entry pair (a, b) with b the generated fresh ident.
          have h_pair_mem : (a, HasIdent.ident (P := P) (StringGenState.gen hoistFreshPrefix σ).1) ∈ subst := by
            have := h_entries _ (entriesOf_init_head_mem a τ (.det rhs0) md rest σ)
            exact this.2.2
          have h_a_in_A : a ∈ A := by
            have := h_entries _ (entriesOf_init_head_mem a τ (.det rhs0) md rest σ)
            exact this.1
          have h_b_in_B : HasIdent.ident (P := P) (StringGenState.gen hoistFreshPrefix σ).1 ∈ B := by
            have := h_entries _ (entriesOf_init_head_mem a τ (.det rhs0) md rest σ)
            exact this.2.1
          -- the renamed set equals the BodyTransport.init_set hoist shape.
          rw [init_site_applyRenames a _ rhs0 md subst h_pair_mem h_src_nodup h_disjoint]
          -- freshness of rhs0 (TARGET side only; sources need no freshness).
          obtain ⟨h_B_rhs, _⟩ := namesFresh_cmd_init h_B_fresh
          exact BodyTransport.init_set h_pair_mem h_a_in_A h_b_in_B
            (fun a' b' hm he => unique_of_src_nodup h_src_nodup h_pair_mem a' b' hm he)
            (fun a' b' hm he => unique_of_tgt_nodup h_tgt_nodup h_pair_mem a' b' hm he)
            h_B_rhs h_tail
      | .cmd (.init a τ ExprOrNondet.nondet md), _, h_entries, _, _, _ =>
          -- A nondet-rhs init is lifted like a det one: residual `[.cmd (.set a .nondet md)]`,
          -- entry/rename `(a, b)`; `applyRenames` renames it to `.set b .nondet`.
          have h_sres : (Stmt.liftInitsInLoopBodyM (.cmd (.init a τ ExprOrNondet.nondet md)) σ).1.2.2
              = [.cmd (.set a .nondet md)] := by
            rw [Stmt.liftInitsInLoopBodyM]
          rw [h_sres, applyRenames_singleton]
          have h_pair_mem : (a, HasIdent.ident (P := P) (StringGenState.gen hoistFreshPrefix σ).1) ∈ subst := by
            have := h_entries _ (entriesOf_init_head_mem a τ ExprOrNondet.nondet md rest σ)
            exact this.2.2
          have h_a_in_A : a ∈ A := by
            have := h_entries _ (entriesOf_init_head_mem a τ ExprOrNondet.nondet md rest σ)
            exact this.1
          have h_b_in_B : HasIdent.ident (P := P) (StringGenState.gen hoistFreshPrefix σ).1 ∈ B := by
            have := h_entries _ (entriesOf_init_head_mem a τ ExprOrNondet.nondet md rest σ)
            exact this.2.1
          rw [init_nondet_site_applyRenames a _ md subst h_pair_mem h_src_nodup h_disjoint]
          exact BodyTransport.init_nondet h_pair_mem h_a_in_A h_b_in_B
            (fun a' b' hm he => unique_of_src_nodup h_src_nodup h_pair_mem a' b' hm he)
            (fun a' b' hm he => unique_of_tgt_nodup h_tgt_nodup h_pair_mem a' b' hm he)
            h_tail
      | .cmd (.set name (.det rhs) md), _, _, h_B_fresh, h_mdB, _ =>
          -- A `.set name` is the residual verbatim; DISPATCH on whether `name` is a
          -- rename SOURCE.  If `name ∈ subst sources` (= `A`), the var was ALSO declared
          -- (`init name`) in this body: the lift hoists the declaration and `applyRenames`
          -- renames this later `.set name → .set b` (the same rename it applies at the
          -- `.init` site), giving `set_renamed`.  Otherwise `name ∉ A` and the name is
          -- UNCHANGED by the rename, giving the plain `set`.
          have h_sres : (Stmt.liftInitsInLoopBodyM (.cmd (.set name (.det rhs) md)) σ).1.2.2
              = [.cmd (.set name (.det rhs) md)] := by
            simp [Stmt.liftInitsInLoopBodyM]
          rw [h_sres, applyRenames_singleton]
          obtain ⟨h_B_rhs, _⟩ := namesFresh_cmd_set_det h_B_fresh
          have h_name_notin_B : name ∉ B :=
            h_mdB name (set_name_mem_modifiedVars name (.det rhs) md rest)
          by_cases h_src : name ∈ subst.map Prod.fst
          · -- rename source: `name = a`, target `b := renameLookup subst name`.
            obtain ⟨p, hp, hp1⟩ := List.mem_map.mp h_src
            have h_pair_mem : (name, p.2) ∈ subst := by cases p; cases hp1; exact hp
            obtain ⟨h_a_in_A, h_b_in_B⟩ := h_subst_wf name p.2 h_pair_mem
            have h_b_eq : renameLookup subst name = p.2 :=
              renameLookup_mem subst h_src_nodup h_pair_mem
            rw [init_site_applyRenames name (renameLookup subst name) rhs md subst
              (h_b_eq ▸ h_pair_mem) h_src_nodup h_disjoint]
            refine BodyTransport.set_renamed (h_b_eq ▸ h_pair_mem) h_a_in_A (h_b_eq ▸ h_b_in_B)
              (fun a' b' hm he => unique_of_src_nodup h_src_nodup (h_b_eq ▸ h_pair_mem) a' b' hm he)
              (fun a' b' hm he => unique_of_tgt_nodup h_tgt_nodup (h_b_eq ▸ h_pair_mem) a' b' hm he)
              h_B_rhs h_tail
          · -- not a rename source: `name ∉ A` (since `A ⊆ sources`), name UNCHANGED.
            have h_name_notin_A : name ∉ A := fun ha => h_src (h_A_subst_fst name ha)
            rw [set_site_applyRenames name rhs md subst h_src h_disjoint]
            exact BodyTransport.set h_name_notin_A h_name_notin_B h_B_rhs h_tail
      | .cmd (.set name ExprOrNondet.nondet md), _, _, _, h_mdB, _ =>
          have h_sres : (Stmt.liftInitsInLoopBodyM (.cmd (.set name ExprOrNondet.nondet md)) σ).1.2.2
              = [.cmd (.set name .nondet md)] := by
            simp [Stmt.liftInitsInLoopBodyM]
          rw [h_sres, applyRenames_singleton]
          have h_name_notin_B : name ∉ B :=
            h_mdB name (set_name_mem_modifiedVars name .nondet md rest)
          by_cases h_src : name ∈ subst.map Prod.fst
          · obtain ⟨p, hp, hp1⟩ := List.mem_map.mp h_src
            have h_pair_mem : (name, p.2) ∈ subst := by cases p; cases hp1; exact hp
            obtain ⟨h_a_in_A, h_b_in_B⟩ := h_subst_wf name p.2 h_pair_mem
            have h_b_eq : renameLookup subst name = p.2 :=
              renameLookup_mem subst h_src_nodup h_pair_mem
            rw [init_nondet_site_applyRenames name (renameLookup subst name) md subst
              (h_b_eq ▸ h_pair_mem) h_src_nodup h_disjoint]
            exact BodyTransport.set_renamed_nondet (h_b_eq ▸ h_pair_mem) h_a_in_A (h_b_eq ▸ h_b_in_B)
              (fun a' b' hm he => unique_of_src_nodup h_src_nodup (h_b_eq ▸ h_pair_mem) a' b' hm he)
              (fun a' b' hm he => unique_of_tgt_nodup h_tgt_nodup (h_b_eq ▸ h_pair_mem) a' b' hm he)
              h_tail
          · have h_name_notin_A : name ∉ A := fun ha => h_src (h_A_subst_fst name ha)
            rw [set_nondet_site_applyRenames name md subst h_src h_disjoint]
            exact BodyTransport.set_nondet h_name_notin_A h_name_notin_B h_tail
      | .cmd (.assert lbl e md), _, h_entries, h_B_fresh, _, _ =>
          have h_sres : (Stmt.liftInitsInLoopBodyM (.cmd (.assert lbl e md)) σ).1.2.2
              = [.cmd (.assert lbl e md)] := by
            simp [Stmt.liftInitsInLoopBodyM]
          rw [h_sres, applyRenames_singleton,
              stmtSubstMany_cmd_assert]
          obtain ⟨h_B_e, _⟩ := namesFresh_cmd_assert h_B_fresh
          exact BodyTransport.assert h_B_e h_tail
      | .cmd (.assume lbl e md), _, h_entries, h_B_fresh, _, _ =>
          have h_sres : (Stmt.liftInitsInLoopBodyM (.cmd (.assume lbl e md)) σ).1.2.2
              = [.cmd (.assume lbl e md)] := by
            simp [Stmt.liftInitsInLoopBodyM]
          rw [h_sres, applyRenames_singleton,
              stmtSubstMany_cmd_assume]
          obtain ⟨h_B_e, _⟩ := namesFresh_cmd_assume h_B_fresh
          exact BodyTransport.assume h_B_e h_tail
      | .cmd (.cover lbl e md), _, h_entries, h_B_fresh, _, _ =>
          have h_sres : (Stmt.liftInitsInLoopBodyM (.cmd (.cover lbl e md)) σ).1.2.2
              = [.cmd (.cover lbl e md)] := by
            simp [Stmt.liftInitsInLoopBodyM]
          rw [h_sres, applyRenames_singleton,
              stmtSubstMany_cmd_cover]
          exact BodyTransport.cover h_tail
      | .typeDecl tc md, _, _, _, _, _ =>
          -- residual of a `.typeDecl` is the typeDecl verbatim; `applyRenames`/
          -- `substIdent` leave it unchanged.
          have h_sres : (Stmt.liftInitsInLoopBodyM (.typeDecl tc md) σ).1.2.2
              = [.typeDecl tc md] := by
            simp [Stmt.liftInitsInLoopBodyM]
          rw [h_sres, applyRenames_singleton, stmtSubstMany_typeDecl]
          exact BodyTransport.typeDecl h_tail
      | .exit lbl md, _, _, _, _, _ =>
          -- residual of an `.exit` is the exit verbatim; `applyRenames`/`substIdent`
          -- leave it unchanged.
          have h_sres : (Stmt.liftInitsInLoopBodyM (.exit lbl md) σ).1.2.2
              = [.exit lbl md] := by
            simp [Stmt.liftInitsInLoopBodyM]
          rw [h_sres, applyRenames_singleton, stmtSubstMany_exit]
          exact BodyTransport.exit h_tail
      | .block lbl bss md, h_if_s, h_entries, h_B_fresh, h_mdB, h_shape_s =>
          -- residual of a .block = [.block lbl bss_res md].
          rw [Stmt.liftInitsInLoopBodyM_block_residual, applyRenames_singleton, stmtSubstMany_block]
          -- recurse on bss at σ.
          have h_if_bss := initfree_block h_if_s
          have h_entries_bss : EntriesIn A B subst bss σ := EntriesIn.block h_entries
          obtain ⟨h_B_bss, _⟩ := namesFresh_block h_B_fresh
          have h_shape_bss : Block.transportShape bss = true := by
            simpa only [Stmt.transportShape] using h_shape_s
          have h_inner :=
            Block.bodyTransport_of_lift bss σ A B subst h_if_bss h_entries_bss h_B_bss
              (fun x hx => h_mdB x (modifiedVars_block_subset hx)) h_subst_wf h_A_subst_fst
              h_src_nodup h_tgt_nodup h_disjoint h_shape_bss
          exact BodyTransport.block h_inner h_tail
      | .ite (.det g) tss ess md, h_if_s, h_entries, h_B_fresh, h_mdB, h_shape_s =>
          rw [Stmt.liftInitsInLoopBodyM_ite_residual, applyRenames_singleton, stmtSubstMany_ite]
          have ⟨h_if_tss, h_if_ess⟩ := initfree_ite h_if_s
          have h_entries_tss : EntriesIn A B subst tss σ := EntriesIn.ite_then h_entries
          have h_entries_ess : EntriesIn A B subst ess (Block.liftInitsInLoopBodyM tss σ).2 :=
            EntriesIn.ite_else h_entries
          obtain ⟨h_B_g, h_B_tss, h_B_ess, _⟩ := namesFresh_ite h_B_fresh
          have h_shape_tss : Block.transportShape tss = true ∧ Block.transportShape ess = true := by
            simpa only [Stmt.transportShape, Bool.and_eq_true] using h_shape_s
          have h_then :=
            Block.bodyTransport_of_lift tss σ A B subst h_if_tss h_entries_tss h_B_tss
              (fun x hx => h_mdB x (modifiedVars_ite_then_subset hx)) h_subst_wf h_A_subst_fst
              h_src_nodup h_tgt_nodup h_disjoint h_shape_tss.1
          have h_else :=
            Block.bodyTransport_of_lift ess (Block.liftInitsInLoopBodyM tss σ).2 A B subst
              h_if_ess h_entries_ess h_B_ess
              (fun x hx => h_mdB x (modifiedVars_ite_else_subset hx)) h_subst_wf h_A_subst_fst
              h_src_nodup h_tgt_nodup h_disjoint h_shape_tss.2
          exact BodyTransport.ite h_B_g h_then h_else h_tail
      | .ite ExprOrNondet.nondet tss ess md, h_if_s, h_entries, h_B_fresh, h_mdB, h_shape_s =>
          rw [Stmt.liftInitsInLoopBodyM_ite_residual, applyRenames_singleton, stmtSubstMany_ite_nondet]
          have ⟨h_if_tss, h_if_ess⟩ := initfree_ite h_if_s
          have h_entries_tss : EntriesIn A B subst tss σ := EntriesIn.ite_then h_entries
          have h_entries_ess : EntriesIn A B subst ess (Block.liftInitsInLoopBodyM tss σ).2 :=
            EntriesIn.ite_else h_entries
          obtain ⟨h_B_tss, h_B_ess⟩ := namesFresh_ite_nondet h_B_fresh
          have h_shape_tss : Block.transportShape tss = true ∧ Block.transportShape ess = true := by
            simpa only [Stmt.transportShape, Bool.and_eq_true] using h_shape_s
          have h_then :=
            Block.bodyTransport_of_lift tss σ A B subst h_if_tss h_entries_tss h_B_tss
              (fun x hx => h_mdB x (modifiedVars_ite_then_subset hx)) h_subst_wf h_A_subst_fst
              h_src_nodup h_tgt_nodup h_disjoint h_shape_tss.1
          have h_else :=
            Block.bodyTransport_of_lift ess (Block.liftInitsInLoopBodyM tss σ).2 A B subst
              h_if_ess h_entries_ess h_B_ess
              (fun x hx => h_mdB x (modifiedVars_ite_else_subset hx)) h_subst_wf h_A_subst_fst
              h_src_nodup h_tgt_nodup h_disjoint h_shape_tss.2
          exact BodyTransport.ite_nondet h_then h_else h_tail
      | .loop (.det g) none [] lbody md, h_if_s, h_entries, h_B_fresh, h_mdB, h_shape_s =>
          -- residual of a nested .loop is the loop verbatim.
          have h_sres : (Stmt.liftInitsInLoopBodyM (.loop (.det g) none [] lbody md) σ).1.2.2
              = [.loop (.det g) none [] lbody md] := by
            simp [Stmt.liftInitsInLoopBodyM]
          rw [h_sres, applyRenames_singleton, stmtSubstMany_loop_det]
          -- the loop body is init-free, so its entries are [].
          obtain ⟨h_noinits, h_if_lbody⟩ := initfree_loop_noinits h_if_s
          have h_lbody_iv : Block.initVars lbody = [] :=
            Block.initVars_eq_nil_of_noInitsAnywhere lbody h_noinits
          -- recurse on lbody at σ; its entries are empty so EntriesIn holds vacuously.
          have h_entries_lbody : EntriesIn A B subst lbody σ := by
            intro e he
            rw [Block.entriesOf_noInits lbody σ h_noinits] at he
            simp at he
          obtain ⟨h_B_g, h_B_lbody, _⟩ := namesFresh_loop h_B_fresh
          have h_shape_lbody : Block.transportShape lbody = true := by
            simpa only [Stmt.transportShape] using h_shape_s
          have h_lbody :=
            Block.bodyTransport_of_lift lbody σ A B subst h_if_lbody h_entries_lbody
              h_B_lbody
              (fun x hx => h_mdB x (modifiedVars_loop_subset hx)) h_subst_wf h_A_subst_fst
              h_src_nodup h_tgt_nodup h_disjoint h_shape_lbody
          -- the lift residual of an init-free body is the body verbatim.
          rw [Block.liftInitsInLoopBodyM_snd_no_inits lbody σ h_lbody_iv] at h_lbody
          exact BodyTransport.loop h_B_g h_lbody h_tail
      -- The remaining head shapes are excluded by `transportShape` (a measured /
      -- invariant-bearing / nondet-guard loop, or a `.funcDecl`).
      | .loop (.det g) (some me) inv lbody md, _, _, _, _, h_shape =>
          exact absurd h_shape (by simp [Stmt.transportShape])
      | .loop (.det g) none (i :: inv) lbody md, _, _, _, _, h_shape =>
          exact absurd h_shape (by simp [Stmt.transportShape])
      | .loop ExprOrNondet.nondet m inv lbody md, _, _, _, _, h_shape =>
          exact absurd h_shape (by simp [Stmt.transportShape])
      | .funcDecl d md, _, _, _, _, h_shape =>
          exact absurd h_shape (by simp [Stmt.transportShape])
  termination_by sizeOf body₁

/-! ## Step B builder: the producer's `BodyTransport` becomes the driver's
sum-typed `BodySimSum`.

`Block.bodyTransport_of_lift` produces a `BodyTransport` derivation;
`LoopInitHoistBodyTransport.Block.bodyTransport` turns it into the eval-carrying,
SUM-TYPED `BodySimES`; `OptEStepBProvider.bodySimES_to_bodySimSum` forgets the eval
conjunct to land in the driver's `BodySimSum` slot (terminal-OR-exiting).  This
packages Step B for the §E `.loop` arm at the harvest carriers `A B subst` and
admits a loop body that breaks (`.exit`). -/
theorem Block.stepB_bodySim_of_lift [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    (body₁ : List (Stmt P (Cmd P))) (σ : StringGenState)
    (A B : List P.Ident) (subst : List (P.Ident × P.Ident))
    (h_initfree : Block.allLoopBodiesInitFree body₁ = true)
    (h_entries : EntriesIn A B subst body₁ σ)
    (h_B_fresh : Block.namesFreshInExprs B body₁ = true)
    (h_mod_disjoint_B : ∀ x ∈ Block.modifiedVars body₁, x ∉ B)
    (h_subst_wf : ∀ a b, (a, b) ∈ subst → a ∈ A ∧ b ∈ B)
    (h_src_nodup : (subst.map Prod.fst).Nodup)
    (h_tgt_nodup : (subst.map Prod.snd).Nodup)
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd)
    (h_shape : Block.transportShape body₁ = true)
    (h_subst_fst_A : ∀ a ∈ subst.map Prod.fst, a ∈ A)
    (h_A_subst_fst : ∀ a ∈ A, a ∈ subst.map Prod.fst)
    (h_subst_snd_B : ∀ b ∈ subst.map Prod.snd, b ∈ B)
    (h_wfvar   : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval)
    (h_wfcongr : ∀ ρ : Env P, WellFormedSemanticEvalExprCongr ρ.eval)
    (h_wfsubst : ∀ ρ : Env P, WellFormedSemanticEvalSubstFvar ρ.eval)
    (h_wfdef   : ∀ ρ : Env P, WellFormedSemanticEvalDef ρ.eval) :
    LoopInitHoistLoopDriver.BodySimSum (extendEval := extendEval) A B subst
      body₁
      (Block.applyRenames subst (Block.liftInitsInLoopBodyM body₁ σ).1.2.2) := by
  -- `BodySimES` (eval-carrying, sum-typed, `@[expose]`) drives into
  -- `LoopInitHoistLoopDriver.BodySimSum` via `bodySimES_to_bodySimSum`, dropping the
  -- eval conjunct from each (terminal and exiting) output.
  have hBES : OptEStepBProvider.BodySimES (extendEval := extendEval) A B subst body₁
      (Block.applyRenames subst (Block.liftInitsInLoopBodyM body₁ σ).1.2.2) :=
    LoopInitHoistBodyTransport.Block.bodyTransport (extendEval := extendEval)
      (Block.bodyTransport_of_lift body₁ σ A B subst h_initfree h_entries h_B_fresh
        h_mod_disjoint_B h_subst_wf h_A_subst_fst h_src_nodup h_tgt_nodup h_disjoint h_shape)
      h_subst_fst_A h_A_subst_fst h_subst_snd_B h_src_nodup h_disjoint h_tgt_nodup
      h_wfvar h_wfcongr h_wfsubst h_wfdef
  exact OptEStepBProvider.bodySimES_to_bodySimSum hBES

/-- The FAILING-config sibling of `Block.stepB_bodySim_of_lift`: the same lift's
`BodyTransport` derivation, fed to `Block.bodyTransport_to_fail`, yields a
`BodySimFail` for the rewritten loop body (a failing source-body run is matched by a
failing renamed-lifted-body run). -/
theorem Block.stepB_bodySim_of_lift_fail [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    (body₁ : List (Stmt P (Cmd P))) (σ : StringGenState)
    (A B : List P.Ident) (subst : List (P.Ident × P.Ident))
    (h_initfree : Block.allLoopBodiesInitFree body₁ = true)
    (h_entries : EntriesIn A B subst body₁ σ)
    (h_B_fresh : Block.namesFreshInExprs B body₁ = true)
    (h_mod_disjoint_B : ∀ x ∈ Block.modifiedVars body₁, x ∉ B)
    (h_subst_wf : ∀ a b, (a, b) ∈ subst → a ∈ A ∧ b ∈ B)
    (h_src_nodup : (subst.map Prod.fst).Nodup)
    (h_tgt_nodup : (subst.map Prod.snd).Nodup)
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd)
    (h_shape : Block.transportShape body₁ = true)
    (h_subst_fst_A : ∀ a ∈ subst.map Prod.fst, a ∈ A)
    (h_A_subst_fst : ∀ a ∈ A, a ∈ subst.map Prod.fst)
    (h_subst_snd_B : ∀ b ∈ subst.map Prod.snd, b ∈ B)
    (h_wfvar   : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval)
    (h_wfcongr : ∀ ρ : Env P, WellFormedSemanticEvalExprCongr ρ.eval)
    (h_wfsubst : ∀ ρ : Env P, WellFormedSemanticEvalSubstFvar ρ.eval)
    (h_wfdef   : ∀ ρ : Env P, WellFormedSemanticEvalDef ρ.eval) :
    OptEStepBProvider.BodySimFail (extendEval := extendEval) A B subst
      body₁
      (Block.applyRenames subst (Block.liftInitsInLoopBodyM body₁ σ).1.2.2) :=
  LoopInitHoistBodyTransport.Block.bodyTransport_to_fail (extendEval := extendEval)
    (Block.bodyTransport_of_lift body₁ σ A B subst h_initfree h_entries h_B_fresh
      h_mod_disjoint_B h_subst_wf h_A_subst_fst h_src_nodup h_tgt_nodup h_disjoint h_shape)
    h_subst_fst_A h_A_subst_fst h_subst_snd_B h_src_nodup h_disjoint h_tgt_nodup
    h_wfvar h_wfcongr h_wfsubst h_wfdef

end LoopInitHoistStepCProducer
end Imperative

end -- public section
