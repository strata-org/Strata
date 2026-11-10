/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.Program
public import Strata.Transform.Passive.SimulationProps
public import Strata.DL.Imperative.CmdCallFormals

/-! # Syntactic facts for the initial-environment gate of guarded programs
Tree-form lists (`Block.treeForm`) touch and mention only their free variables (`Block.freeVars`)
and the names they declare (`touched_sub_fv_defs`, `idents_sub_fv_defs`), and are def-use well
formed when their free variables are defined, their declarations are distinct and undefined, and
their operators are declared (`defUse_of_treeForm`). For source lists: a list well scoped from `S`
declares no name of `S` (`wfl_defs_not_mem`), the free variables of a list are among the variables
it touches (`Block.freeVars_sub_touched`), and a def-use well-formed list declares every
operator it references (`block_defUse_ops`).

Key theorems: `idents_sub_fv_defs`, `touched_sub_fv_defs`, `defUse_of_treeForm`,
`wfl_defs_not_mem`, `Block.freeVars_sub_touched`, `block_defUse_ops`. -/

namespace Imperative
namespace WP

open BigStep

public section

/-! ## Tree-form lists -/

/-- Every identifier of a tree-form list is a free variable of it or a name it declares. -/
theorem idents_sub_fv_defs {P : PureExpr} [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident]
    [HasFvar P] [HasFvars P] {L : PStmts P} (h : Block.treeForm L = true) :
    ∀ x ∈ Block.idents L, x ∈ Block.freeVars L ++ Block.definedVars L false := by
  induction L using Block.treeForm.induct with
  | case8 => rw [Block.treeForm] at h <;> grind
  | case7 t e md rest iht ihe =>
    simp only [Block.treeForm, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨⟨rfl, ht⟩, he⟩ := h
    have hT := iht ht
    have hE := ihe he
    simp only [Block.idents, Stmt.idents, Block.freeVars, Stmt.freeVars,
      Block.definedVars, Stmt.definedVars,
      ExprOrNondet.getVars] at *
    grind
  | _ =>
    (try cases ‹ExprOrNondet P›) <;> simp only [Block.treeForm] at h <;>
    simp_all only [Block.idents, Block.freeVars, Block.definedVars, List.mem_append, Stmt.idents,
      List.mem_cons, Stmt.definedVars, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars,
      mem_exprFV, Stmt.freeVars] <;> grind

/-- Every variable a tree-form list touches is a free variable of it or a name it declares. -/
theorem touched_sub_fv_defs {P : PureExpr} [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident]
    [HasFvar P] [HasFvars P] {L : PStmts P} (h : Block.treeForm L = true) :
    ∀ x ∈ Block.touchedVars L, x ∈ Block.freeVars L ++ Block.definedVars L false := by
  induction L using Block.treeForm.induct with
  | case8 => rw [Block.treeForm] at h <;> grind
  | case7 t e md rest iht ihe =>
    simp only [Block.treeForm, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨⟨rfl, ht⟩, he⟩ := h
    have hT := iht ht
    have hE := ihe he
    simp_all only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append,
      Block.modifiedVars, Stmt.modifiedVars, Block.definedVars, Stmt.definedVars, Block.getVars,
      Stmt.getVars, ExprOrNondet.getVars, Block.freeVars, Stmt.freeVars]
    grind
  | _ =>
    (try cases ‹ExprOrNondet P›) <;> simp only [Block.treeForm] at h <;>
    simp_all only [Block.touchedVars, Block.modifiedOrDefinedVars, Block.modifiedVars,
      Block.definedVars, Block.getVars, Block.freeVars, List.mem_append, Stmt.modifiedVars,
      HasVarsImp.modifiedVars, CmdExt.modifiedVars, Cmd.modifiedVars, Stmt.definedVars,
      HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars, Stmt.getVars,
      HasVarsImp.readVars, CmdExt.readVars, Cmd.getVars, ExprOrNondet.getVars, List.mem_cons,
      mem_exprFV, Stmt.freeVars] <;> grind

/-- A tree-form list is def-use well formed from the defined names `D` and the declared
    operators `decl` when its free variables are defined, the names it declares are distinct and
    undefined, and its operators are declared. -/
theorem defUse_of_treeForm {P : PureExpr} [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [Hashable P.Ident] [HasFvar P] [HasFvars P] [HasOps P] {L : PStmts P}
    (h : Block.treeForm L = true)
    {D decl : P.Ident → Bool} (hfv : ∀ x ∈ Block.freeVars L, D x = true)
    (hnd : (Block.definedVars L false).Nodup)
    (hnew : ∀ x ∈ Block.definedVars L false, D x = false)
    (hops : ∀ o ∈ Block.getOps L, decl o = true) :
    Block.defUseWellFormed D decl L = true := by
  induction L using Block.treeForm.induct generalizing D with
  | case1 => rfl
  | case8 => rw [Block.treeForm] at h <;> grind
  | case7 t e md rest iht ihe =>
    simp only [Block.treeForm, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨⟨rfl, ht⟩, he⟩ := h
    simp_all [Block.defUseWellFormed, Stmt.defUseWellFormed, Block.getOps, Stmt.getOps,
      Block.freeVars, Stmt.freeVars, Block.definedVars, Stmt.definedVars, ExprOrNondet.getVars,
      ExprOrNondet.getOps, List.nodup_append]
  | _ =>
    rename_i ih
    simp only [Block.treeForm] at h
    simp only [Block.defUseWellFormed, Bool.and_eq_true]
    refine ⟨?_, ih h ?_ ?_ ?_ ?_⟩ <;> (try cases ‹ExprOrNondet P›) <;>
    simp_all only [Block.freeVars, List.mem_append, mem_exprFV, Block.definedVars, Stmt.definedVars,
      HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars, List.mem_cons, Block.getOps,
      Stmt.getOps, Stmt.defUseWellFormed, HasVarsImp.readVars, CmdExt.readVars, Cmd.getVars,
      ExprOrNondet.getVars, HasVarsImp.modifiedVars, CmdExt.modifiedVars, Cmd.modifiedVars,
      Stmt.freeVars] <;> grind

/-! ## Source lists -/

/-- A list well scoped from `S` (`Block.WellScoped`) declares no name of `S`, at any depth. -/
theorem wfl_defs_not_mem {P : PureExpr} [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident]
    [HasFvar P] [HasFvars P] {Lc S : List P.Ident} {ss : PStmts P} (h : Block.WellScoped Lc S ss) :
    ∀ x ∈ Block.definedVars ss false, x ∉ S := by
  have hsub : ∀ x ∈ Block.definedVars ss false, x ∈ stmtsInits ss := by
    clear h
    induction ss using stmtsInits.induct with
    | case6 s rest h1 h2 h3 h4 ih =>
      rcases s with ((_ | _ | _ | _ | _) | _) | _ | _ | _ | _ | _
      case ite => exact (h2 _ _ _ _ rfl).elim
      case loop => exact (h4 _ _ _ _ _ rfl).elim
      all_goals simp_all [stmtsInits, Block.definedVars, HasVarsImp.definedVars,
        CmdExt.definedVars, Cmd.definedVars]
    | _ =>
      simp_all only [Block.definedVars, stmtsInits, Stmt.definedVars, HasVarsImp.definedVars,
        CmdExt.definedVars, Cmd.definedVars] <;> grind
  exact fun x hx hS => wfl_inits_disjoint S ss h x hS (hsub x hx)

/-- The free variables of a statement list are among the variables it touches. -/
theorem Block.freeVars_sub_touched {P : PureExpr} [BEq P.Ident] [LawfulBEq P.Ident]
    [Hashable P.Ident]
    [HasFvar P] [HasFvars P] {ss : PStmts P} :
    ∀ x ∈ Block.freeVars ss, x ∈ Block.touchedVars ss := by
  have hsub : ∀ x ∈ Block.freeVars ss, x ∈ Block.modifiedVars ss ∨ x ∈ Block.getVars ss := by
    induction ss using stmtsInits.induct with
    | case6 s rest h1 h2 h3 h4 ih =>
      rcases s with ((_ | _ | _ | _ | _) | _) | _ | _ | _ | _ | _
      case ite => exact (h2 _ _ _ _ rfl).elim
      case loop => exact (h4 _ _ _ _ _ rfl).elim
      all_goals (try cases ‹ExprOrNondet P›) <;>
        simp_all only [Block.freeVars, List.mem_append, mem_exprFV, Block.modifiedVars,
          Stmt.modifiedVars,
          HasVarsImp.modifiedVars, CmdExt.modifiedVars, Cmd.modifiedVars, Block.getVars,
          Stmt.getVars, HasVarsImp.readVars, CmdExt.readVars, Cmd.getVars, ExprOrNondet.getVars,
          Stmt.freeVars, List.mem_cons] <;> grind
    | _ =>
      (try cases ‹ExprOrNondet P›) <;>
      simp_all only [Block.freeVars, Block.modifiedVars, Block.getVars, List.mem_append, mem_exprFV,
        Stmt.modifiedVars, Stmt.getVars, HasVarsImp.readVars, CmdExt.readVars, Cmd.getVars,
        ExprOrNondet.getVars, Stmt.freeVars] <;> grind
  intro x hx
  rcases hsub x hx with h | h <;> simp [Block.touchedVars, Block.modifiedOrDefinedVars, h]

mutual
/-- A def-use well-formed statement declares every operator it references. -/
private theorem stmt_defUse_ops {P : PureExpr} {C : Type} [HasVarsImp P C] [HasFvars P]
    [HasOps P] [HasOpsImp P C] [DecidableEq P.Ident] {decl : P.Ident → Bool} :
    ∀ {D : P.Ident → Bool} (s : Stmt P C), Stmt.defUseWellFormed D decl s = true →
      ∀ o ∈ Stmt.getOps s, decl o = true
  | _, .cmd _, h => by simp_all [Stmt.defUseWellFormed, Stmt.getOps]
  | _, .block _ b _, h => block_defUse_ops b (by simpa [Stmt.defUseWellFormed] using h)
  | _, .ite _ t e _, h => by
    simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at h
    have ht := block_defUse_ops t h.1.2
    have he := block_defUse_ops e h.2
    simp only [Stmt.getOps, List.mem_append]
    grind
  | _, .loop _ _ _ b _, h => by
    simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at h
    have hb := block_defUse_ops b h.2
    simp only [Stmt.getOps, List.mem_append, List.mem_flatMap]
    grind
  | _, .exit _ _, _ | _, .typeDecl _ _, _ => by simp [Stmt.getOps]
/-- A def-use well-formed statement list declares every operator it references. -/
theorem block_defUse_ops {P : PureExpr} {C : Type} [HasVarsImp P C] [HasFvars P]
    [HasOps P] [HasOpsImp P C] [DecidableEq P.Ident] {decl : P.Ident → Bool} :
    ∀ {D : P.Ident → Bool} (ss : Block P C), Block.defUseWellFormed D decl ss = true →
      ∀ o ∈ Block.getOps ss, decl o = true
  | _, [], _ => by simp [Block.getOps]
  | _, s :: rest, h => by
    simp only [Block.defUseWellFormed, Bool.and_eq_true] at h
    have hs := stmt_defUse_ops s h.1
    have hr := block_defUse_ops rest h.2
    simp only [Block.getOps, List.mem_append]
    grind
end

end -- public section

end WP
end Imperative
