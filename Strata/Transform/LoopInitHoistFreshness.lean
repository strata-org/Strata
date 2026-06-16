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

/-! # `namesFreshInExprs` preservation through the `liftInitsInLoopBody` residual

The residual (`.snd`) of the `liftInitsInLoopBody` pass preserves the
shape-only freshness predicate `Block.namesFreshInExprs names` without any
name-list change.

The pass residual only:
* converts `.cmd (.init y ty rhs md)` → `.cmd (.set y rhs md)` (rhs unchanged),
* recurses into `.block` / `.ite` substructures.

Both the `.init` and `.set` arms of `namesFreshInExprs` check
`freshFromIdents z (ExprOrNondet.getVars rhs)`, so the rewrite preserves the
freshness check verbatim.  The proof is a mutual structural induction mirroring
the residual's recursion arms; `Block.namesFreshInExprs_append` factors out the
`++` distribution the `.loop` arm needs.
-/

/-! ## List-append distributivity helper (used inside the mutual block below). -/

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
end Imperative
