/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt

namespace Imperative

public section

variable {P : PureExpr} {C : Type}

/-! ### Disjointness of funcDeclNames from definedVars

The strengthened `defUseWellFormed.funcDecl` case requires that each
`funcDecl decl _` AST node satisfies `!definedVars decl.name` at its
position.  This lets us derive: every name in `funcDeclNames s` is NOT
in the initial `definedVars` predicate.  Used by simulation proofs
when combined with `block_preserves_eval_on_disjoint`.
-/

mutual

theorem Stmt.funcDeclNames_disjoint_of_defUseOk [HasVarsImp P C]
    [HasFvars P] [HasOps P] [HasOpsImp P C] [HasVarsPure P C] [DecidableEq P.Ident]
    (defined : P.Ident → Bool) (declared : P.Ident → Bool) (s : Stmt P C)
    (hwf : Stmt.defUseWellFormed defined declared s = true) :
    ∀ n ∈ Stmt.funcDeclNames s false, defined n = false := by
  match s with
  | .cmd _ => intro n hn; simp [Stmt.funcDeclNames] at hn
  | .exit _ _ => intro n hn; simp [Stmt.funcDeclNames] at hn
  | .typeDecl _ _ => intro n hn; simp [Stmt.funcDeclNames] at hn
  | .funcDecl decl _ =>
    intro n hn
    simp [Stmt.funcDeclNames] at hn
    subst hn
    simp [Stmt.defUseWellFormed, Bool.and_eq_true] at hwf
    exact Bool.not_eq_true _ |>.mp (by simpa using hwf.1.1.2)
  | .block _ bss _ =>
    intro n hn
    simp [Stmt.funcDeclNames] at hn
    simp [Stmt.defUseWellFormed] at hwf
    exact Block.funcDeclNames_disjoint_of_defUseOk defined declared bss hwf n hn
  | .ite _ tss ess _ =>
    intro n hn
    simp [Stmt.funcDeclNames, List.mem_append] at hn
    simp [Stmt.defUseWellFormed, Bool.and_eq_true] at hwf
    rcases hn with hn | hn
    · exact Block.funcDeclNames_disjoint_of_defUseOk defined declared tss hwf.1.2 n hn
    · exact Block.funcDeclNames_disjoint_of_defUseOk defined declared ess hwf.2 n hn
  | .loop _ _ _ body _ =>
    intro n hn
    simp [Stmt.funcDeclNames] at hn
    simp [Stmt.defUseWellFormed, Bool.and_eq_true] at hwf
    exact Block.funcDeclNames_disjoint_of_defUseOk defined declared body hwf.2 n hn

theorem Block.funcDeclNames_disjoint_of_defUseOk [HasVarsImp P C]
    [HasFvars P] [HasOps P] [HasOpsImp P C] [HasVarsPure P C] [DecidableEq P.Ident]
    (defined : P.Ident → Bool) (declared : P.Ident → Bool) (bss : Block P C)
    (hwf : Block.defUseWellFormed defined declared bss = true) :
    ∀ n ∈ Block.funcDeclNames bss false, defined n = false := by
  match bss with
  | [] => intro n hn; simp [Block.funcDeclNames] at hn
  | s :: rest =>
    intro n hn
    simp [Block.funcDeclNames, List.mem_append] at hn
    simp [Block.defUseWellFormed, Bool.and_eq_true] at hwf
    rcases hn with hn | hn
    · exact Stmt.funcDeclNames_disjoint_of_defUseOk defined declared s hwf.1 n hn
    · -- The tail's predicate is `definedVars ∪ definedVars(s)`; if `n` is in
      -- `funcDeclNames rest`, then it's not in the larger predicate, hence
      -- not in `definedVars` either.
      have ih := Block.funcDeclNames_disjoint_of_defUseOk
        (fun m => defined m || decide (m ∈ Stmt.definedVars s true))
        (fun m => declared m || decide (m ∈ Stmt.funcDeclNames s true)) rest hwf.2 n hn
      simp [Bool.or_eq_false_iff] at ih
      exact ih.1

end

mutual

/-- All `funcDeclNames` of `s` are *not* in the initial `declared` predicate,
    given `Stmt.defUseWellFormed defined declared s = true`.  This is the
    operator-level analog of `Stmt.funcDeclNames_disjoint_of_defUseOk`. -/
theorem Stmt.funcDeclNames_disjoint_of_declared [HasVarsImp P C]
    [HasFvars P] [HasOps P] [HasOpsImp P C] [HasVarsPure P C] [DecidableEq P.Ident]
    (defined : P.Ident → Bool) (declared : P.Ident → Bool) (s : Stmt P C)
    (hwf : Stmt.defUseWellFormed defined declared s = true) :
    ∀ n ∈ Stmt.funcDeclNames s false, declared n = false := by
  match s with
  | .cmd _ => intro n hn; simp [Stmt.funcDeclNames] at hn
  | .exit _ _ => intro n hn; simp [Stmt.funcDeclNames] at hn
  | .typeDecl _ _ => intro n hn; simp [Stmt.funcDeclNames] at hn
  | .funcDecl decl _ =>
    intro n hn
    simp [Stmt.funcDeclNames] at hn
    subst hn
    simp [Stmt.defUseWellFormed, Bool.and_eq_true] at hwf
    exact Bool.not_eq_true _ |>.mp (by simpa using hwf.2)
  | .block _ bss _ =>
    intro n hn
    simp [Stmt.funcDeclNames] at hn
    simp [Stmt.defUseWellFormed] at hwf
    exact Block.funcDeclNames_disjoint_of_declared defined declared bss hwf n hn
  | .ite _ tss ess _ =>
    intro n hn
    simp [Stmt.funcDeclNames, List.mem_append] at hn
    simp [Stmt.defUseWellFormed, Bool.and_eq_true] at hwf
    rcases hn with hn | hn
    · exact Block.funcDeclNames_disjoint_of_declared defined declared tss hwf.1.2 n hn
    · exact Block.funcDeclNames_disjoint_of_declared defined declared ess hwf.2 n hn
  | .loop _ _ _ body _ =>
    intro n hn
    simp [Stmt.funcDeclNames] at hn
    simp [Stmt.defUseWellFormed, Bool.and_eq_true] at hwf
    exact Block.funcDeclNames_disjoint_of_declared defined declared body hwf.2 n hn

theorem Block.funcDeclNames_disjoint_of_declared [HasVarsImp P C]
    [HasFvars P] [HasOps P] [HasOpsImp P C] [HasVarsPure P C] [DecidableEq P.Ident]
    (defined : P.Ident → Bool) (declared : P.Ident → Bool) (bss : Block P C)
    (hwf : Block.defUseWellFormed defined declared bss = true) :
    ∀ n ∈ Block.funcDeclNames bss false, declared n = false := by
  match bss with
  | [] => intro n hn; simp [Block.funcDeclNames] at hn
  | s :: rest =>
    intro n hn
    simp [Block.funcDeclNames, List.mem_append] at hn
    simp [Block.defUseWellFormed, Bool.and_eq_true] at hwf
    rcases hn with hn | hn
    · exact Stmt.funcDeclNames_disjoint_of_declared defined declared s hwf.1 n hn
    · have ih := Block.funcDeclNames_disjoint_of_declared
        (fun m => defined m || decide (m ∈ Stmt.definedVars s true))
        (fun m => declared m || decide (m ∈ Stmt.funcDeclNames s true)) rest hwf.2 n hn
      simp [Bool.or_eq_false_iff] at ih
      exact ih.1

end

mutual

/-- If a statement contains no function declarations, then `funcDeclNames` is
    empty (for either choice of `excludeScoped`). -/
theorem Stmt.funcDeclNames_eq_nil_of_noFuncDecl
    (s : Stmt P C) (excludeScoped : Bool) (h : Stmt.noFuncDecl s = true) :
    Stmt.funcDeclNames s excludeScoped = [] := by
  match s with
  | .cmd _ => simp [Stmt.funcDeclNames]
  | .exit _ _ => simp [Stmt.funcDeclNames]
  | .typeDecl _ _ => simp [Stmt.funcDeclNames]
  | .funcDecl _ _ => simp [Stmt.noFuncDecl] at h
  | .block _ bss _ =>
    simp [Stmt.noFuncDecl] at h
    cases excludeScoped <;> simp [Stmt.funcDeclNames]
    exact Block.funcDeclNames_eq_nil_of_noFuncDecl bss false h
  | .ite _ tss ess _ =>
    simp [Stmt.noFuncDecl, Bool.and_eq_true] at h
    cases excludeScoped <;> simp [Stmt.funcDeclNames]
    refine ⟨?_, ?_⟩
    · exact Block.funcDeclNames_eq_nil_of_noFuncDecl tss false h.1
    · exact Block.funcDeclNames_eq_nil_of_noFuncDecl ess false h.2
  | .loop _ _ _ body _ =>
    simp [Stmt.noFuncDecl] at h
    cases excludeScoped <;> simp [Stmt.funcDeclNames]
    exact Block.funcDeclNames_eq_nil_of_noFuncDecl body false h

/-- If a block contains no function declarations, then `funcDeclNames` is empty. -/
theorem Block.funcDeclNames_eq_nil_of_noFuncDecl
    (ss : Block P C) (excludeScoped : Bool) (h : Block.noFuncDecl ss = true) :
    Block.funcDeclNames ss excludeScoped = [] := by
  match ss with
  | [] => simp [Block.funcDeclNames]
  | s :: rest =>
    simp [Block.noFuncDecl, Bool.and_eq_true] at h
    simp [Block.funcDeclNames]
    refine ⟨?_, ?_⟩
    · exact Stmt.funcDeclNames_eq_nil_of_noFuncDecl s excludeScoped h.1
    · exact Block.funcDeclNames_eq_nil_of_noFuncDecl rest excludeScoped h.2

end

end -- public section

end Imperative
