/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.Cmd
public import Strata.Transform.LoopInitHoist
public import Strata.Transform.LoopInitHoistRewrite

import all Strata.DL.Imperative.Cmd
import all Strata.DL.Imperative.Stmt
import all Strata.Transform.LoopInitHoist
import all Strata.Transform.LoopInitHoistRewrite

public section

namespace Imperative

variable {P : PureExpr}

/-! # Phase 7.5 redesign sub-step C: `hoistedNamesFreshInRhsAndGuards`
preservation through the `liftInitsInLoopBody` residual

The strengthened freshness predicate
`Block.hoistedNamesFreshInRhsAndGuards` is preserved by the residual
(`.snd`) of the `liftInitsInLoopBody` pass.

This file proves the surviving shape-only preservation lemma
(ported in Phase 8 Option E onto the monadic pass):
* `Block.liftInitsInLoopBody_snd_preserves_hoistedNamesFreshInRhsAndGuards`

The pass residual only:
* converts `.cmd (.init y ty rhs md)` → `.cmd (.set y rhs md)` (rhs unchanged),
* recurses into `.block` / `.ite` substructures.

The proof structure: a sequence of mutual structural inductions that mirror
the pass residual's recursion arms, factoring out three reusable helpers:
1. `namesFreshInExprs names` is preserved (without name-list change),
2. `hoistedNamesFreshInGuards` is preserved (per-loop check is local),
3. `Block.initVars (output)` is a subset of `Block.initVars (input)`,
   used together with `Block.namesFreshInExprs_subset` (already proven in
   `LoopInitHoistRewrite.lean`).
-/

/-! ## List-append distributivity helpers (used inside mutual blocks below). -/

/-- `Block.namesFreshInExprs` distributes over `++`. -/
private theorem Block.namesFreshInExprs_append
    [HasVarsPure P P.Expr] (names : List P.Ident)
    (xs ys : List (Stmt P (Cmd P)))
    (hx : Block.namesFreshInExprs names xs = true)
    (hy : Block.namesFreshInExprs names ys = true) :
    Block.namesFreshInExprs names (xs ++ ys) = true := by
  induction xs with
  | nil => simpa using hy
  | cons x rest ih =>
    simp only [Block.namesFreshInExprs, Bool.and_eq_true] at hx
    simp only [List.cons_append, Block.namesFreshInExprs, Bool.and_eq_true]
    refine ⟨hx.1, ?_⟩
    exact ih hx.2

/-- `Block.hoistedNamesFreshInGuards` distributes over `++`. -/
private theorem Block.hoistedNamesFreshInGuards_append
    [HasVarsPure P P.Expr]
    (xs ys : List (Stmt P (Cmd P)))
    (hx : Block.hoistedNamesFreshInGuards xs = true)
    (hy : Block.hoistedNamesFreshInGuards ys = true) :
    Block.hoistedNamesFreshInGuards (xs ++ ys) = true := by
  induction xs with
  | nil => simpa using hy
  | cons x rest ih =>
    simp only [Block.hoistedNamesFreshInGuards, Bool.and_eq_true] at hx
    simp only [List.cons_append, Block.hoistedNamesFreshInGuards,
               Bool.and_eq_true]
    refine ⟨hx.1, ?_⟩
    exact ih hx.2

/-! ## Helper 1: `liftInitsInLoopBody.snd` preserves `namesFreshInExprs`
(no name-list change)

`liftInitsInLoopBody` only rewrites `.cmd .init y ty rhs md` →
`.cmd .set y rhs md` (rhs unchanged). Both `init` and `set` arms of
`namesFreshInExprs` check `freshFromIdents z (ExprOrNondet.getVars rhs)`,
so the rewrite preserves the freshness check verbatim. Loops pass through
unchanged. -/

mutual

private theorem Stmt.liftInitsInLoopBody_snd_namesFreshInExprs
    [HasIdent P] [HasVarsPure P P.Expr] (names : List P.Ident)
    (s : Stmt P (Cmd P))
    (h : Stmt.namesFreshInExprs names s = true) :
    Block.namesFreshInExprs names (Stmt.liftInitsInLoopBody s).snd = true := by
  cases s with
  | cmd c =>
    cases c with
    | init x ty rhs md =>
      -- Residual: [.cmd (.set x rhs md)]; both init and set arms of
      -- `namesFreshInExprs` check freshFromIdents z (ExprOrNondet.getVars rhs),
      -- so the freshness premise transfers verbatim (name-preserving rewrite).
      simp only [Stmt.liftInitsInLoopBody_snd_cmd_init, Block.namesFreshInExprs,
                 Stmt.namesFreshInExprs, Bool.and_true]
      simp only [Stmt.namesFreshInExprs] at h
      exact h
    | set _ _ _ | assert _ _ _ | assume _ _ _ | cover _ _ _ =>
      simp only [Stmt.liftInitsInLoopBody_snd_cmd_set,
                 Stmt.liftInitsInLoopBody_snd_cmd_assert,
                 Stmt.liftInitsInLoopBody_snd_cmd_assume,
                 Stmt.liftInitsInLoopBody_snd_cmd_cover, Block.namesFreshInExprs,
                 Stmt.namesFreshInExprs, Bool.and_true]
      simp only [Stmt.namesFreshInExprs] at h
      exact h
  | block lbl bss md =>
    simp only [Stmt.liftInitsInLoopBody_snd_block, Block.namesFreshInExprs,
               Stmt.namesFreshInExprs, Bool.and_true]
    have h_bss : Block.namesFreshInExprs names bss = true := by
      simp only [Stmt.namesFreshInExprs] at h; exact h
    exact Block.liftInitsInLoopBody_snd_namesFreshInExprs names bss h_bss
  | ite g tss ess md =>
    have h_parts :
        names.all (fun z => freshFromIdents z (ExprOrNondet.getVars g)) = true ∧
        Block.namesFreshInExprs names tss = true ∧
        Block.namesFreshInExprs names ess = true := by
      simp only [Stmt.namesFreshInExprs, Bool.and_eq_true] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
    have ih_t :=
      Block.liftInitsInLoopBody_snd_namesFreshInExprs names tss h_parts.2.1
    have ih_e :=
      Block.liftInitsInLoopBody_snd_namesFreshInExprs names ess h_parts.2.2
    simp only [Stmt.liftInitsInLoopBody_snd_ite, Block.namesFreshInExprs,
               Stmt.namesFreshInExprs, Bool.and_true]
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨h_parts.1, ih_t⟩, ih_e⟩
  | loop g m inv body md =>
    -- liftInitsInLoopBody passes loops through unchanged.
    simp only [Stmt.liftInitsInLoopBody_snd_loop, Block.namesFreshInExprs,
               Bool.and_true]
    exact h
  | exit lbl md =>
    simp only [Stmt.liftInitsInLoopBody_snd_exit, Block.namesFreshInExprs,
               Stmt.namesFreshInExprs, Bool.and_self]
  | funcDecl d md =>
    simp only [Stmt.liftInitsInLoopBody_snd_funcDecl, Block.namesFreshInExprs,
               Stmt.namesFreshInExprs, Bool.and_self]
  | typeDecl t md =>
    simp only [Stmt.liftInitsInLoopBody_snd_typeDecl, Block.namesFreshInExprs,
               Stmt.namesFreshInExprs, Bool.and_self]
  termination_by sizeOf s

private theorem Block.liftInitsInLoopBody_snd_namesFreshInExprs
    [HasIdent P] [HasVarsPure P P.Expr] (names : List P.Ident)
    (ss : List (Stmt P (Cmd P)))
    (h : Block.namesFreshInExprs names ss = true) :
    Block.namesFreshInExprs names (Block.liftInitsInLoopBody ss).snd = true := by
  match ss with
  | [] =>
    simp only [Block.liftInitsInLoopBody_snd_nil, Block.namesFreshInExprs]
  | s :: rest =>
    have h_s : Stmt.namesFreshInExprs names s = true := by
      simp only [Block.namesFreshInExprs, Bool.and_eq_true] at h; exact h.1
    have h_rest : Block.namesFreshInExprs names rest = true := by
      simp only [Block.namesFreshInExprs, Bool.and_eq_true] at h; exact h.2
    have ih_s := Stmt.liftInitsInLoopBody_snd_namesFreshInExprs names s h_s
    have ih_rest :=
      Block.liftInitsInLoopBody_snd_namesFreshInExprs names rest h_rest
    simp only [Block.liftInitsInLoopBody_snd_cons]
    exact Block.namesFreshInExprs_append names _ _ ih_s ih_rest
  termination_by sizeOf ss

end

/-! ## Helper 2: `liftInitsInLoopBody.snd` preserves `hoistedNamesFreshInGuards`

Loops are pass-through under `liftInitsInLoopBody`, so the per-loop check
(which depends on `Block.initVars` of the loop body) is preserved verbatim.
The other arms recurse structurally with no per-loop check at the current
level. -/

mutual

private theorem Stmt.liftInitsInLoopBody_snd_hoistedNamesFreshInGuards
    [HasIdent P] [HasVarsPure P P.Expr]
    (s : Stmt P (Cmd P))
    (h : Stmt.hoistedNamesFreshInGuards s = true) :
    Block.hoistedNamesFreshInGuards (Stmt.liftInitsInLoopBody s).snd = true := by
  cases s with
  | cmd c =>
    cases c with
    | init x ty rhs md =>
      simp only [Stmt.liftInitsInLoopBody_snd_cmd_init,
                 Block.hoistedNamesFreshInGuards,
                 Stmt.hoistedNamesFreshInGuards, Bool.and_self]
    | set _ _ _ | assert _ _ _ | assume _ _ _ | cover _ _ _ =>
      simp only [Stmt.liftInitsInLoopBody_snd_cmd_set,
                 Stmt.liftInitsInLoopBody_snd_cmd_assert,
                 Stmt.liftInitsInLoopBody_snd_cmd_assume,
                 Stmt.liftInitsInLoopBody_snd_cmd_cover,
                 Block.hoistedNamesFreshInGuards,
                 Stmt.hoistedNamesFreshInGuards, Bool.and_self]
  | block lbl bss md =>
    have h_bss : Block.hoistedNamesFreshInGuards bss = true := by
      simp only [Stmt.hoistedNamesFreshInGuards] at h; exact h
    simp only [Stmt.liftInitsInLoopBody_snd_block, Block.hoistedNamesFreshInGuards,
               Stmt.hoistedNamesFreshInGuards, Bool.and_true]
    exact Block.liftInitsInLoopBody_snd_hoistedNamesFreshInGuards bss h_bss
  | ite g tss ess md =>
    have h_branches :
        Block.hoistedNamesFreshInGuards tss = true ∧
        Block.hoistedNamesFreshInGuards ess = true := by
      simp only [Stmt.hoistedNamesFreshInGuards, Bool.and_eq_true] at h; exact h
    simp only [Stmt.liftInitsInLoopBody_snd_ite, Block.hoistedNamesFreshInGuards,
               Stmt.hoistedNamesFreshInGuards, Bool.and_true]
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · exact Block.liftInitsInLoopBody_snd_hoistedNamesFreshInGuards tss
        h_branches.1
    · exact Block.liftInitsInLoopBody_snd_hoistedNamesFreshInGuards ess
        h_branches.2
  | loop g m inv body md =>
    -- Pass-through; structural equality.
    simp only [Stmt.liftInitsInLoopBody_snd_loop, Block.hoistedNamesFreshInGuards,
               Bool.and_true]
    exact h
  | exit lbl md =>
    simp only [Stmt.liftInitsInLoopBody_snd_exit, Block.hoistedNamesFreshInGuards,
               Stmt.hoistedNamesFreshInGuards, Bool.and_self]
  | funcDecl d md =>
    simp only [Stmt.liftInitsInLoopBody_snd_funcDecl,
               Block.hoistedNamesFreshInGuards,
               Stmt.hoistedNamesFreshInGuards, Bool.and_self]
  | typeDecl t md =>
    simp only [Stmt.liftInitsInLoopBody_snd_typeDecl,
               Block.hoistedNamesFreshInGuards,
               Stmt.hoistedNamesFreshInGuards, Bool.and_self]
  termination_by sizeOf s

private theorem Block.liftInitsInLoopBody_snd_hoistedNamesFreshInGuards
    [HasIdent P] [HasVarsPure P P.Expr]
    (ss : List (Stmt P (Cmd P)))
    (h : Block.hoistedNamesFreshInGuards ss = true) :
    Block.hoistedNamesFreshInGuards (Block.liftInitsInLoopBody ss).snd = true := by
  match ss with
  | [] =>
    simp only [Block.liftInitsInLoopBody_snd_nil, Block.hoistedNamesFreshInGuards]
  | s :: rest =>
    have h_s : Stmt.hoistedNamesFreshInGuards s = true := by
      simp only [Block.hoistedNamesFreshInGuards, Bool.and_eq_true] at h
      exact h.1
    have h_rest : Block.hoistedNamesFreshInGuards rest = true := by
      simp only [Block.hoistedNamesFreshInGuards, Bool.and_eq_true] at h
      exact h.2
    have ih_s :=
      Stmt.liftInitsInLoopBody_snd_hoistedNamesFreshInGuards s h_s
    have ih_rest :=
      Block.liftInitsInLoopBody_snd_hoistedNamesFreshInGuards rest h_rest
    simp only [Block.liftInitsInLoopBody_snd_cons]
    exact Block.hoistedNamesFreshInGuards_append _ _ ih_s ih_rest
  termination_by sizeOf ss

end

/-! ## Helper 3: `Block.initVars` of `liftInitsInLoopBody.snd` is a subset of
input's `Block.initVars`.

The pass converts `.cmd .init` to `.cmd .set` (drops the var from initVars),
recurses into `.block` / `.ite` (preserves subset relation by IH), and
passes `.loop` through (initVars unchanged for that subtree). -/

mutual

private theorem Stmt.liftInitsInLoopBody_snd_initVars_subset
    [HasIdent P] (s : Stmt P (Cmd P)) :
    Block.initVars (Stmt.liftInitsInLoopBody s).snd ⊆ Stmt.initVars s := by
  cases s with
  | cmd c =>
    cases c with
    | init x ty rhs md =>
      -- Residual: [.cmd (.set x rhs md)]; initVars = []; ⊆ [x].
      simp only [Stmt.liftInitsInLoopBody_snd_cmd_init, Block.initVars,
                 Stmt.initVars]
      intro y hy
      cases hy
    | set _ _ _ | assert _ _ _ | assume _ _ _ | cover _ _ _ =>
      simp only [Stmt.liftInitsInLoopBody_snd_cmd_set,
                 Stmt.liftInitsInLoopBody_snd_cmd_assert,
                 Stmt.liftInitsInLoopBody_snd_cmd_assume,
                 Stmt.liftInitsInLoopBody_snd_cmd_cover, Block.initVars,
                 Stmt.initVars, List.append_nil]
      intro y hy; exact hy
  | block lbl bss md =>
    simp only [Stmt.liftInitsInLoopBody_snd_block, Block.initVars, Stmt.initVars,
               List.append_nil]
    exact Block.liftInitsInLoopBody_snd_initVars_subset bss
  | ite g tss ess md =>
    simp only [Stmt.liftInitsInLoopBody_snd_ite, Block.initVars, Stmt.initVars,
               List.append_nil]
    intro y hy
    rw [List.mem_append] at hy ⊢
    rcases hy with hy | hy
    · exact Or.inl (Block.liftInitsInLoopBody_snd_initVars_subset tss hy)
    · exact Or.inr (Block.liftInitsInLoopBody_snd_initVars_subset ess hy)
  | loop g m inv body md =>
    -- Pass-through; residual = [.loop g m inv body md]; initVars same.
    simp only [Stmt.liftInitsInLoopBody_snd_loop, Block.initVars, Stmt.initVars,
               List.append_nil]
    intro y hy; exact hy
  | exit lbl md =>
    simp only [Stmt.liftInitsInLoopBody_snd_exit, Block.initVars, Stmt.initVars]
    intro y hy; exact hy
  | funcDecl d md =>
    simp only [Stmt.liftInitsInLoopBody_snd_funcDecl, Block.initVars,
               Stmt.initVars]
    intro y hy; exact hy
  | typeDecl t md =>
    simp only [Stmt.liftInitsInLoopBody_snd_typeDecl, Block.initVars,
               Stmt.initVars]
    intro y hy; exact hy
  termination_by sizeOf s

private theorem Block.liftInitsInLoopBody_snd_initVars_subset
    [HasIdent P] (ss : List (Stmt P (Cmd P))) :
    Block.initVars (Block.liftInitsInLoopBody ss).snd ⊆ Block.initVars ss := by
  match ss with
  | [] =>
    simp only [Block.liftInitsInLoopBody_snd_nil, Block.initVars]
    intro y hy; exact hy
  | s :: rest =>
    simp only [Block.liftInitsInLoopBody_snd_cons, Block.initVars]
    rw [Block.initVars_append]
    intro y hy
    rw [List.mem_append] at hy ⊢
    rcases hy with hy | hy
    · exact Or.inl (Stmt.liftInitsInLoopBody_snd_initVars_subset s hy)
    · exact Or.inr (Block.liftInitsInLoopBody_snd_initVars_subset rest hy)
  termination_by sizeOf ss

end

/-! ## Lemma 1: `Block.liftInitsInLoopBody.snd` preserves
`hoistedNamesFreshInRhsAndGuards`. -/

theorem Block.liftInitsInLoopBody_snd_preserves_hoistedNamesFreshInRhsAndGuards
    [HasIdent P] [HasVarsPure P P.Expr]
    (body : List (Stmt P (Cmd P)))
    (h : Block.hoistedNamesFreshInRhsAndGuards body = true) :
    Block.hoistedNamesFreshInRhsAndGuards
      (Block.liftInitsInLoopBody body).snd = true := by
  unfold Block.hoistedNamesFreshInRhsAndGuards at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  obtain ⟨h_guards, h_fresh⟩ := h
  refine ⟨?_, ?_⟩
  · -- hoistedNamesFreshInGuards preservation.
    exact Block.liftInitsInLoopBody_snd_hoistedNamesFreshInGuards body h_guards
  · -- namesFreshInExprs (initVars body') body' preservation.
    -- Step 1: namesFreshInExprs (initVars body) body' = true (preservation
    --         under same names list).
    have h_step1 :
        Block.namesFreshInExprs (Block.initVars body)
          (Block.liftInitsInLoopBody body).snd = true :=
      Block.liftInitsInLoopBody_snd_namesFreshInExprs _ body h_fresh
    -- Step 2: initVars body' ⊆ initVars body, so namesFreshInExprs is
    --         monotone (smaller name list → still fresh).
    have h_sub :
        Block.initVars (Block.liftInitsInLoopBody body).snd
          ⊆ Block.initVars body :=
      Block.liftInitsInLoopBody_snd_initVars_subset body
    exact Block.namesFreshInExprs_subset h_sub
      (Block.liftInitsInLoopBody body).snd h_step1

end Imperative
