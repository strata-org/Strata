/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt

namespace Imperative

public section

variable {P : PureExpr} {C : Type}

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
