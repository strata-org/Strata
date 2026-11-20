/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Simplify.StmtShape
public import Strata.Transform.Simplify.DeadDefsShape
public import Strata.Languages.Core.Logic.LangDef
public import Strata.Transform.Simplify.Precondition
public import Strata.Transform.Simplify.Entry
import Strata.Util.ListUtilsProps
import all Strata.Transform.Simplify.Precondition
import all Strata.Transform.Simplify.StmtShape
import all Strata.Transform.Simplify.DeadDefsShape
import all Strata.Transform.Simplify
import all Strata.Transform.Simplify.Expr
import all Strata.Transform.Simplify.SimpWF
import Strata.DL.Imperative.StmtProps
import Strata.DL.Imperative.CmdProps

/-! # The simplified body's entry gate

Simplify declares no variable and no init-type the body does not: the simplification pass
keeps every `init` with its variable and type (`simpStmts_definedVars`,
`simpStmts_initTypes`), and the sweep only drops statements (`dropDeadDefs_definedVars`,
`dropDeadDefs_initTypes`). So the gate of the simplified body follows from the body's gate,
the def-use well-formedness of the simplified body and the agreement of its annotations with a
typing of the entry store (`sweptBody_blockInitEnvWF`), which are the parts of it Simplify's
rewriting can change.

Both of those hold (`sweptBody_wf`): the simplification pass keeps them (`simpStmts_wf`), and
so does the sweep (`sweep_wf`), since a definition it drops declares a variable nothing after
it mentions (`mem_dropDeadDefsAux_live`). When the phase's check passes, it also makes the
simplified body's entry environment well-formed, over any factory (`gateOK_blockInitEnvWF`).
Simplify also adds no procedure call (`checkedBody_noCalls`).
-/

namespace Core.Simplify

open Imperative

public section

/-- Simplifying a command keeps its init-types. -/
private theorem simpCmd_initTypes (ctx : Ctx) (c : Imperative.Cmd Expression) :
    Stmt.initTypes (P := Expression) (C := Command) (.cmd (.cmd (simpCmd ctx c).1)) =
      Stmt.initTypes (P := Expression) (C := Command) (.cmd (.cmd c)) := by
  cases c with
  | init x ty e md => cases e <;> rfl
  | set x e md => cases e <;> rfl
  | _ => rfl

mutual
/-- Simplifying a statement keeps what it declares. -/
private theorem simpStmt_definedVars (ctx : Ctx) (s : Statement) :
    Block.definedVars (P := Expression) (C := Command) (simpStmt ctx s).1 false =
      Stmt.definedVars (P := Expression) (C := Command) s false := by
  match s with
  | .cmd (.cmd c) =>
    rw [simpStmt_cmd]; simp only [Block.definedVars, List.append_nil]
    exact simpCmd_definedVars ctx c false
  | .cmd (.call pname tyArgs args md) => rw [simpStmt_call]; rfl
  | .block l ss md =>
    rw [simpStmt_block_eq]
    simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ↓reduceIte,
      List.append_nil]
    exact simpStmts_definedVars ctx ss
  | .ite (.det c) ts es md =>
    rw [simpStmt_ite_det_eq]
    simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ↓reduceIte,
      List.append_nil]
    rw [simpStmts_definedVars ctx ts, simpStmts_definedVars ctx es]
  | .ite .nondet ts es md =>
    rw [simpStmt_ite_nondet_eq]
    simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ↓reduceIte,
      List.append_nil]
    rw [simpStmts_definedVars ctx ts, simpStmts_definedVars ctx es]
  | .loop g m invs body md =>
    rw [simpStmt_loop]
    simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ↓reduceIte,
      List.append_nil]
    exact simpStmts_definedVars _ body
  | .exit l md => rw [simpStmt_exit]; rfl
  | .typeDecl tc md => rw [simpStmt_typeDecl]; rfl
  termination_by sizeOf s
/-- Simplifying a list keeps what it declares. -/
private theorem simpStmts_definedVars (ctx : Ctx) (ss : List Statement) :
    Block.definedVars (P := Expression) (C := Command) (simpStmts ctx ss).1 false =
      Block.definedVars (P := Expression) (C := Command) ss false := by
  match ss with
  | [] => rw [simpStmts_nil]
  | s :: rest =>
    rw [simpStmts_cons, Block.definedVars_append, simpStmt_definedVars,
      simpStmts_definedVars _ rest]
    rfl
  termination_by sizeOf ss
end

mutual
/-- Simplifying a statement keeps its init-types. -/
private theorem simpStmt_initTypes (ctx : Ctx) (s : Statement) :
    Block.initTypes (P := Expression) (C := Command) (simpStmt ctx s).1 =
      Stmt.initTypes (P := Expression) (C := Command) s := by
  match s with
  | .cmd (.cmd c) =>
    rw [simpStmt_cmd]; simp only [Block.initTypes, List.append_nil]
    exact simpCmd_initTypes ctx c
  | .cmd (.call pname tyArgs args md) => rw [simpStmt_call]; rfl
  | .block l ss md =>
    rw [simpStmt_block_eq]
    simp only [Block.initTypes, Stmt.initTypes, List.append_nil]
    exact simpStmts_initTypes ctx ss
  | .ite (.det c) ts es md =>
    rw [simpStmt_ite_det_eq]
    simp only [Block.initTypes, Stmt.initTypes, List.append_nil]
    rw [simpStmts_initTypes ctx ts, simpStmts_initTypes ctx es]
  | .ite .nondet ts es md =>
    rw [simpStmt_ite_nondet_eq]
    simp only [Block.initTypes, Stmt.initTypes, List.append_nil]
    rw [simpStmts_initTypes ctx ts, simpStmts_initTypes ctx es]
  | .loop g m invs body md =>
    rw [simpStmt_loop]
    simp only [Block.initTypes, Stmt.initTypes, List.append_nil]
    exact simpStmts_initTypes _ body
  | .exit l md => rw [simpStmt_exit]; rfl
  | .typeDecl tc md => rw [simpStmt_typeDecl]; rfl
  termination_by sizeOf s
/-- Simplifying a list keeps its init-types. -/
private theorem simpStmts_initTypes (ctx : Ctx) (ss : List Statement) :
    Block.initTypes (P := Expression) (C := Command) (simpStmts ctx ss).1 =
      Block.initTypes (P := Expression) (C := Command) ss := by
  match ss with
  | [] => rw [simpStmts_nil]
  | s :: rest =>
    rw [simpStmts_cons, Block.initTypes_append, simpStmt_initTypes,
      simpStmts_initTypes _ rest]
    rfl
  termination_by sizeOf ss
end

mutual
/-- Simplifying a loop-free statement gives loop-free statements. -/
private theorem simpStmt_noLoops (ctx : Ctx) (s : Statement) (h : Stmt.noLoops s = true) :
    Block.noLoops (simpStmt ctx s).1 = true := by
  match s with
  | .cmd (.cmd c) =>
    rw [simpStmt_cmd]; simp [Block.noLoops_cons, Block.noLoops_nil, Stmt.noLoops_cmd]
  | .cmd (.call pname tyArgs args md) =>
    rw [simpStmt_call]; simp [Block.noLoops_cons, Block.noLoops_nil, Stmt.noLoops_cmd]
  | .block l ss md =>
    rw [Stmt.noLoops_block] at h
    rw [simpStmt_block_eq]
    simp only [Block.noLoops_cons, Block.noLoops_nil, Stmt.noLoops_block,
      simpStmts_noLoops ctx ss h, Bool.and_self]
  | .ite (.det c) ts es md =>
    rw [Stmt.noLoops_ite, Bool.and_eq_true] at h
    rw [simpStmt_ite_det_eq]
    simp only [Block.noLoops_cons, Block.noLoops_nil, Stmt.noLoops_ite,
      simpStmts_noLoops ctx ts h.1, simpStmts_noLoops ctx es h.2, Bool.and_self]
  | .ite .nondet ts es md =>
    rw [Stmt.noLoops_ite, Bool.and_eq_true] at h
    rw [simpStmt_ite_nondet_eq]
    simp only [Block.noLoops_cons, Block.noLoops_nil, Stmt.noLoops_ite,
      simpStmts_noLoops ctx ts h.1, simpStmts_noLoops ctx es h.2, Bool.and_self]
  | .loop g m invs body md => rw [Stmt.noLoops_loop] at h; cases h
  | .exit l md =>
    rw [simpStmt_exit]; simp [Block.noLoops_cons, Block.noLoops_nil, Stmt.noLoops_exit]
  | .typeDecl tc md =>
    rw [simpStmt_typeDecl]; simp [Block.noLoops_cons, Block.noLoops_nil, Stmt.noLoops_typeDecl]
  termination_by sizeOf s
/-- Simplifying a loop-free list gives a loop-free list. -/
theorem simpStmts_noLoops (ctx : Ctx) (ss : List Statement) (h : Block.noLoops ss = true) :
    Block.noLoops (simpStmts ctx ss).1 = true := by
  match ss with
  | [] => rw [simpStmts_nil]; exact Block.noLoops_nil
  | s :: rest =>
    rw [Block.noLoops_cons, Bool.and_eq_true] at h
    rw [simpStmts_cons, Block.noLoops_append, simpStmt_noLoops ctx s h.1,
      simpStmts_noLoops _ rest h.2]
    rfl
  termination_by sizeOf ss
end

/-- A statement of a base command makes no call. -/
private theorem noCalls_cmd (c : Imperative.Cmd Expression) :
    Statement.noCalls (.cmd (.cmd c)) = true := by
  rw [Statement.noCalls, Stmt.allSubstmts_cmd]; rfl

/-- The statements of two lists without calls make none. -/
private theorem noCalls_append {xs ys : List Statement} (hx : Statements.noCalls xs = true)
    (hy : Statements.noCalls ys = true) : Statements.noCalls (xs ++ ys) = true := by
  rw [Statements.noCalls, Block.allSubstmts_append]
  exact Bool.and_eq_true_iff.2 ⟨hx, hy⟩

mutual
/-- Simplifying a statement without calls gives statements without calls. -/
private theorem simpStmt_noCalls (ctx : Ctx) (s : Statement) (h : Statement.noCalls s = true) :
    Statements.noCalls (simpStmt ctx s).1 = true := by
  match s with
  | .cmd (.cmd c) => rw [simpStmt_cmd]; exact noCalls_singleton (noCalls_cmd _)
  | .cmd (.call pname tyArgs args md) =>
    rw [Statement.noCalls, Stmt.allSubstmts_cmd] at h; cases h
  | .block l ss md =>
    rw [simpStmt_block_eq]
    have ih := simpStmts_noCalls ctx ss (noCalls_block h)
    exact noCalls_singleton (by rw [noCalls_eq_block]; exact ih)
  | .ite (.det c) ts es md =>
    rw [simpStmt_ite_det_eq]
    exact noCalls_singleton (by
      rw [noCalls_eq_ite, Bool.and_eq_true]
      exact ⟨simpStmts_noCalls ctx ts (noCalls_ite h).1,
        simpStmts_noCalls ctx es (noCalls_ite h).2⟩)
  | .ite .nondet ts es md =>
    rw [simpStmt_ite_nondet_eq]
    exact noCalls_singleton (by
      rw [noCalls_eq_ite, Bool.and_eq_true]
      exact ⟨simpStmts_noCalls ctx ts (noCalls_ite h).1,
        simpStmts_noCalls ctx es (noCalls_ite h).2⟩)
  | .loop g m invs body md =>
    rw [simpStmt_loop]
    have ih := simpStmts_noCalls (forgetAssigned ctx body) body (noCalls_loop h)
    exact noCalls_singleton (by rw [noCalls_eq_loop]; exact ih)
  | .exit l md =>
    rw [simpStmt_exit]; exact noCalls_singleton h
  | .typeDecl tc md =>
    rw [simpStmt_typeDecl]; exact noCalls_singleton h
  termination_by sizeOf s
/-- Simplifying a list without calls gives a list without calls. -/
private theorem simpStmts_noCalls (ctx : Ctx) (ss : List Statement)
    (h : Statements.noCalls ss = true) : Statements.noCalls (simpStmts ctx ss).1 = true := by
  match ss with
  | [] => rw [simpStmts_nil]; exact noCalls_nil
  | s :: rest =>
    rw [simpStmts_cons]
    exact noCalls_append (simpStmt_noCalls ctx s (noCalls_cons h).1)
      (simpStmts_noCalls _ rest (noCalls_cons h).2)
  termination_by sizeOf ss
end

mutual
/-- Simplifying a statement keeps its `exit` targets. -/
private theorem simpStmt_labels (ctx : Ctx) (s : Statement) :
    Block.labels (simpStmt ctx s).1 = Stmt.labels s := by
  match s with
  | .cmd (.cmd c) => rw [simpStmt_cmd]; rfl
  | .cmd (.call pname tyArgs args md) => rw [simpStmt_call]; rfl
  | .block l ss md =>
    rw [simpStmt_block_eq]
    simp only [Block.labels, Stmt.labels, List.append_nil]
    exact simpStmts_labels ctx ss
  | .ite (.det c) ts es md =>
    rw [simpStmt_ite_det_eq]
    simp only [Block.labels, Stmt.labels, List.append_nil]
    rw [simpStmts_labels ctx ts, simpStmts_labels ctx es]
  | .ite .nondet ts es md =>
    rw [simpStmt_ite_nondet_eq]
    simp only [Block.labels, Stmt.labels, List.append_nil]
    rw [simpStmts_labels ctx ts, simpStmts_labels ctx es]
  | .loop g m invs body md =>
    rw [simpStmt_loop]
    simp only [Block.labels, Stmt.labels, List.append_nil]
    exact simpStmts_labels _ body
  | .exit l md => rw [simpStmt_exit]; rfl
  | .typeDecl tc md => rw [simpStmt_typeDecl]; rfl
  termination_by sizeOf s
/-- Simplifying a list keeps its `exit` targets. -/
private theorem simpStmts_labels (ctx : Ctx) (ss : List Statement) :
    Block.labels (simpStmts ctx ss).1 = Block.labels ss := by
  match ss with
  | [] => rw [simpStmts_nil]
  | s :: rest =>
    rw [simpStmts_cons, Block.labels_append, simpStmt_labels, simpStmts_labels _ rest]
    rfl
  termination_by sizeOf ss
end


section Sweep
variable {Fl : Lambda.Factory CoreLParams}

/-- What a statement or list declares, and its init-types. -/
private def Decls (ss : List Statement) : List CoreIdent × List Expression.Ty :=
  (Block.definedVars (P := Expression) (C := Command) ss false,
    Block.initTypes (P := Expression) (C := Command) ss)

/-- What `a` declares and its init-types are among `b`'s. -/
private def Sub (a b : List Statement) : Prop :=
  (∀ n ∈ (Decls a).1, n ∈ (Decls b).1) ∧ (∀ t ∈ (Decls a).2, t ∈ (Decls b).2)

/-- `Sub` is preserved by putting a statement in front of each list. -/
private theorem Sub.cons {s s' : Statement} {r r' : List Statement} (h₁ : Sub [s'] [s])
    (h₂ : Sub r' r) : Sub (s' :: r') (s :: r) := by
  simp only [Sub, Decls, Block.definedVars, Block.initTypes, List.mem_append,
    List.append_nil] at h₁ h₂ ⊢
  exact ⟨fun n hn => hn.elim (fun h => .inl (h₁.1 n h)) (fun h => .inr (h₂.1 n h)),
    fun t ht => ht.elim (fun h => .inl (h₁.2 t h)) (fun h => .inr (h₂.2 t h))⟩

/-- `Sub` is preserved by putting a statement in front of the larger list. -/
private theorem Sub.tail {s : Statement} {r r' : List Statement} (h : Sub r' r) :
    Sub r' (s :: r) := by
  simp only [Sub, Decls, Block.definedVars, Block.initTypes, List.mem_append] at h ⊢
  exact ⟨fun n hn => .inr (h.1 n hn), fun t ht => .inr (h.2 t ht)⟩

mutual
/-- Sweeping a statement declares nothing it does not. -/
private theorem sweepStmt_sub (D : Defined) (L : Std.HashSet String) (added : List String)
    (s : Statement) : Sub [(dropDeadDefsStmt Fl D L added s).1] [s] := by
  match s with
  | .cmd c => rw [dropDeadDefsStmt_cmd]; exact ⟨fun _ h => h, fun _ h => h⟩
  | .exit l md => rw [dropDeadDefsStmt_exit]; exact ⟨fun _ h => h, fun _ h => h⟩
  | .typeDecl tc md => rw [dropDeadDefsStmt_typeDecl]; exact ⟨fun _ h => h, fun _ h => h⟩
  | .block l ss md =>
    rw [dropDeadDefsStmt_block]
    have ih := sweep_sub D L added ss
    simp only [Sub, Decls, Block.definedVars, Block.initTypes, Stmt.definedVars,
      Stmt.initTypes, Bool.false_eq_true, ↓reduceIte, List.append_nil] at ih ⊢
    exact ih
  | .loop g m invs body md =>
    rw [dropDeadDefsStmt_loop]
    have ih := sweep_sub D L added body
    simp only [Sub, Decls, Block.definedVars, Block.initTypes, Stmt.definedVars,
      Stmt.initTypes, Bool.false_eq_true, ↓reduceIte, List.append_nil] at ih ⊢
    exact ih
  | .ite c ts es md =>
    rw [dropDeadDefsStmt_ite_arms]
    have iht := sweep_sub D L [] ts
    have ihe := sweep_sub D L [] es
    simp only [Sub, Decls, Block.definedVars, Block.initTypes, Stmt.definedVars,
      Stmt.initTypes, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.mem_append]
      at iht ihe ⊢
    exact ⟨fun n hn => hn.elim (fun h => .inl (iht.1 n h)) (fun h => .inr (ihe.1 n h)),
      fun t ht => ht.elim (fun h => .inl (iht.2 t h)) (fun h => .inr (ihe.2 t h))⟩
  termination_by sizeOf s
/-- Sweeping a list declares nothing it does not. -/
private theorem sweep_sub (D : Defined) (L : Std.HashSet String) (added : List String)
    (ss : List Statement) : Sub (dropDeadDefsAux Fl D L added ss).1 ss := by
  match ss with
  | [] => rw [dropDeadDefsAux_nil]; exact ⟨fun _ h => h, fun _ h => h⟩
  | s :: rest =>
    by_cases hdead : ∃ y, definedBy Fl D s = some y ∧
        (dropDeadDefsAux Fl (D.after s) L added rest).2.1.contains y.name = false
    · obtain ⟨y, hdef, hfalse⟩ := hdead
      rw [dropDeadDefsAux_cons_dead hdef hfalse]
      exact (sweep_sub (D.after s) L added rest).tail
    · rw [dropDeadDefsAux_cons_keep (keep_of_not_dead hdead)]
      exact Sub.cons (sweepStmt_sub D _ _ s) (sweep_sub (D.after s) L added rest)
  termination_by sizeOf ss
end

mutual
/-- Sweeping a statement adds no `exit` target. -/
private theorem sweepStmt_labels (D : Defined) (L : Std.HashSet String) (added : List String)
    (s : Statement) : ∀ l ∈ Stmt.labels (dropDeadDefsStmt Fl D L added s).1, l ∈ Stmt.labels s := by
  match s with
  | .cmd c => rw [dropDeadDefsStmt_cmd]; exact fun _ h => h
  | .exit l md => rw [dropDeadDefsStmt_exit]; exact fun _ h => h
  | .typeDecl tc md => rw [dropDeadDefsStmt_typeDecl]; exact fun _ h => h
  | .block l ss md =>
    rw [dropDeadDefsStmt_block]
    simpa only [Stmt.labels] using sweep_labels D L added ss
  | .loop g m invs body md =>
    rw [dropDeadDefsStmt_loop]
    simpa only [Stmt.labels] using sweep_labels D L added body
  | .ite c ts es md =>
    rw [dropDeadDefsStmt_ite_arms]
    simp only [Stmt.labels, List.mem_append]
    exact fun l hl => hl.elim (fun h => .inl (sweep_labels D L [] ts l h))
      (fun h => .inr (sweep_labels D L [] es l h))
  termination_by sizeOf s
/-- Sweeping a list adds no `exit` target. -/
private theorem sweep_labels (D : Defined) (L : Std.HashSet String) (added : List String)
    (ss : List Statement) :
    ∀ l ∈ Block.labels (dropDeadDefsAux Fl D L added ss).1, l ∈ Block.labels ss := by
  match ss with
  | [] => rw [dropDeadDefsAux_nil]; exact fun _ h => h
  | s :: rest =>
    by_cases hdead : ∃ y, definedBy Fl D s = some y ∧
        (dropDeadDefsAux Fl (D.after s) L added rest).2.1.contains y.name = false
    · obtain ⟨y, hdef, hfalse⟩ := hdead
      rw [dropDeadDefsAux_cons_dead hdef hfalse]
      intro l hl
      simp only [Block.labels, List.mem_append]
      exact .inr (sweep_labels (D.after s) L added rest l hl)
    · rw [dropDeadDefsAux_cons_keep (keep_of_not_dead hdead)]
      intro l hl
      simp only [Block.labels, List.mem_append] at hl ⊢
      exact hl.elim (fun h => .inl (sweepStmt_labels D _ _ s l h))
        (fun h => .inr (sweep_labels (D.after s) L added rest l h))
  termination_by sizeOf ss
end

mutual
/-- Sweeping a loop-free statement gives a loop-free statement. -/
private theorem sweepStmt_noLoops (D : Defined) (L : Std.HashSet String) (added : List String)
    (s : Statement) (h : Stmt.noLoops s = true) :
    Stmt.noLoops (dropDeadDefsStmt Fl D L added s).1 = true := by
  match s with
  | .cmd c => rw [dropDeadDefsStmt_cmd]; exact Stmt.noLoops_cmd _
  | .exit l md => rw [dropDeadDefsStmt_exit]; exact Stmt.noLoops_exit _ _
  | .typeDecl tc md => rw [dropDeadDefsStmt_typeDecl]; exact Stmt.noLoops_typeDecl _ _
  | .block l ss md =>
    rw [Stmt.noLoops_block] at h
    rw [dropDeadDefsStmt_block, Stmt.noLoops_block]
    exact sweep_noLoops D L added ss h
  | .loop g m invs body md => rw [Stmt.noLoops_loop] at h; cases h
  | .ite c ts es md =>
    rw [Stmt.noLoops_ite, Bool.and_eq_true] at h
    rw [dropDeadDefsStmt_ite_arms, Stmt.noLoops_ite, sweep_noLoops D L [] ts h.1,
      sweep_noLoops D L [] es h.2]
    rfl
  termination_by sizeOf s
/-- Sweeping a loop-free list gives a loop-free list. -/
private theorem sweep_noLoops (D : Defined) (L : Std.HashSet String) (added : List String)
    (ss : List Statement) (h : Block.noLoops ss = true) :
    Block.noLoops (dropDeadDefsAux Fl D L added ss).1 = true := by
  match ss with
  | [] => rw [dropDeadDefsAux_nil]; exact Block.noLoops_nil
  | s :: rest =>
    rw [Block.noLoops_cons, Bool.and_eq_true] at h
    by_cases hdead : ∃ y, definedBy Fl D s = some y ∧
        (dropDeadDefsAux Fl (D.after s) L added rest).2.1.contains y.name = false
    · obtain ⟨y, hdef, hfalse⟩ := hdead
      rw [dropDeadDefsAux_cons_dead hdef hfalse]
      exact sweep_noLoops (D.after s) L added rest h.2
    · rw [dropDeadDefsAux_cons_keep (keep_of_not_dead hdead), Block.noLoops_cons,
        sweepStmt_noLoops D _ _ s h.1, sweep_noLoops (D.after s) L added rest h.2]
      rfl
  termination_by sizeOf ss
end

/-- The sweep of a loop-free list is loop-free. -/
private theorem dropDeadDefs_noLoops (D : Defined) (L : Std.HashSet String)
    {ss : List Statement} (h : Block.noLoops ss = true) :
    Block.noLoops (dropDeadDefs Fl D L ss) = true :=
  sweep_noLoops D L [] ss h

mutual
/-- Sweeping a statement without calls gives a statement without calls. -/
private theorem sweepStmt_noCalls (D : Defined) (L : Std.HashSet String) (added : List String)
    (s : Statement) (h : Statement.noCalls s = true) :
    Statement.noCalls (dropDeadDefsStmt Fl D L added s).1 = true := by
  match s with
  | .cmd c => rw [dropDeadDefsStmt_cmd]; exact h
  | .exit l md => rw [dropDeadDefsStmt_exit]; exact h
  | .typeDecl tc md => rw [dropDeadDefsStmt_typeDecl]; exact h
  | .block l ss md =>
    rw [dropDeadDefsStmt_block, noCalls_eq_block]
    exact sweep_noCalls D L added ss (noCalls_block h)
  | .loop g m invs body md =>
    rw [dropDeadDefsStmt_loop]
    simp only
    rw [noCalls_eq_loop]
    exact sweep_noCalls D L added body (noCalls_loop h)
  | .ite c ts es md =>
    rw [dropDeadDefsStmt_ite_arms, noCalls_eq_ite, Bool.and_eq_true]
    exact ⟨sweep_noCalls D L [] ts (noCalls_ite h).1, sweep_noCalls D L [] es (noCalls_ite h).2⟩
  termination_by sizeOf s
/-- Sweeping a list without calls gives a list without calls. -/
private theorem sweep_noCalls (D : Defined) (L : Std.HashSet String) (added : List String)
    (ss : List Statement) (h : Statements.noCalls ss = true) :
    Statements.noCalls (dropDeadDefsAux Fl D L added ss).1 = true := by
  match ss with
  | [] => rw [dropDeadDefsAux_nil]; exact noCalls_nil
  | s :: rest =>
    by_cases hdead : ∃ y, definedBy Fl D s = some y ∧
        (dropDeadDefsAux Fl (D.after s) L added rest).2.1.contains y.name = false
    · obtain ⟨y, hdef, hfalse⟩ := hdead
      rw [dropDeadDefsAux_cons_dead hdef hfalse]
      exact sweep_noCalls (D.after s) L added rest (noCalls_cons h).2
    · rw [dropDeadDefsAux_cons_keep (keep_of_not_dead hdead), noCalls_eq_cons,
        sweepStmt_noCalls D _ _ s (noCalls_cons h).1,
        sweep_noCalls (D.after s) L added rest (noCalls_cons h).2]
      rfl
  termination_by sizeOf ss
end

/-- `n` is read or written by the statement `s`. -/
private def Mentions (s : Statement) (n : CoreIdent) : Prop :=
  n ∈ Stmt.getVars s ∨ n ∈ Stmt.modifiedOrDefinedVars (P := Expression) (C := Command) s false

/-- `n` is read or written by a statement of `ss`. -/
private def BMentions (ss : List Statement) (n : CoreIdent) : Prop :=
  n ∈ Block.getVars ss ∨ n ∈ Block.modifiedOrDefinedVars (P := Expression) (C := Command) ss false

/-- What the head of a list mentions, the list mentions. -/
private theorem BMentions.head {s : Statement} {rest : List Statement} {n : CoreIdent}
    (h : Mentions s n) : BMentions (s :: rest) n := by
  rcases h with h | h
  · exact .inl (by simp [Block.getVars, h])
  · simp only [Stmt.modifiedOrDefinedVars, List.mem_append] at h
    right; rcases h with h | h <;> simp [h]

/-- What the rest of a list mentions, the list mentions. -/
private theorem BMentions.tail {s : Statement} {rest : List Statement} {n : CoreIdent}
    (h : BMentions rest n) : BMentions (s :: rest) n := by
  rcases h with h | h
  · exact .inl (by simp [Block.getVars, h])
  · simp only [Block.modifiedOrDefinedVars, List.mem_append] at h
    right; rcases h with h | h <;> simp [h]

/-- Sweeping a statement keeps what it declares in its own scope, and its typed definitions. -/
private theorem sweepStmt_decls (D : Defined) (L : Std.HashSet String) (added : List String)
    (s : Statement) :
    Stmt.definedVars (P := Expression) (C := Command) (dropDeadDefsStmt Fl D L added s).1 true =
        Stmt.definedVars (P := Expression) (C := Command) s true ∧
      Stmt.typedDefinedVars (P := Expression) (C := Command) (dropDeadDefsStmt Fl D L added s).1 =
        Stmt.typedDefinedVars (P := Expression) (C := Command) s := by
  match s with
  | .cmd c => rw [dropDeadDefsStmt_cmd]; exact ⟨rfl, rfl⟩
  | .exit l md => rw [dropDeadDefsStmt_exit]; exact ⟨rfl, rfl⟩
  | .typeDecl tc md => rw [dropDeadDefsStmt_typeDecl]; exact ⟨rfl, rfl⟩
  | .block l ss md => rw [dropDeadDefsStmt_block]; exact ⟨rfl, rfl⟩
  | .loop g m invs body md => rw [dropDeadDefsStmt_loop]; exact ⟨rfl, rfl⟩
  | .ite c ts es md => rw [dropDeadDefsStmt_ite_arms]; exact ⟨rfl, rfl⟩

mutual
/-- **Sweeping a statement keeps it well-formed.** A statement without loops or calls,
    def-use well-formed from `D` and well annotated for `Γ`, sweeps to one def-use
    well-formed from any `D'` within `D` that has every name of `D` the swept statement
    mentions, and well annotated for any `Γ'` that agrees with `Γ` on those names. -/
private theorem sweepStmt_wf (fs : CoreIdent → Bool) (Dd : Defined) (L : Std.HashSet String)
    (added : List String) (s : Statement) (D D' : CoreIdent → Bool)
    (Γ Γ' : VarTyping Expression) (hnl : Stmt.noLoops s = true)
    (hnc : Statement.noCalls s = true)
    (hdu : Stmt.defUseWellFormed (P := Expression) (C := Command) D fs s = true)
    (hann : Stmt.fvarTypesWellAnnotated (P := Expression) (C := Command) Γ s)
    (hD : ∀ n, D' n = true → D n = true)
    (hD' : ∀ n, D n = true → Mentions (dropDeadDefsStmt Fl Dd L added s).1 n → D' n = true)
    (hΓ : ∀ n, Mentions (dropDeadDefsStmt Fl Dd L added s).1 n → Γ' n = Γ n) :
    Stmt.defUseWellFormed (P := Expression) (C := Command) D' fs
        (dropDeadDefsStmt Fl Dd L added s).1 = true ∧
      Stmt.fvarTypesWellAnnotated (P := Expression) (C := Command) Γ'
        (dropDeadDefsStmt Fl Dd L added s).1 := by
  match s with
  | .cmd (.cmd c) =>
    rw [dropDeadDefsStmt_cmd] at hD' hΓ ⊢
    rw [cmd_defUse_iff] at hdu ⊢
    rw [cmd_annot_iff] at hann ⊢
    obtain ⟨hr, hm, hdf, ho⟩ := hdu
    have hread : ∀ x ∈ Cmd.getVars c, Mentions (.cmd (.cmd c)) x := fun x hx =>
      .inl (by simpa [Stmt.getVars, HasVarsImp.readVars, CmdExt.readVars] using hx)
    refine ⟨⟨fun x hx => hD' x (hr x hx) (hread x hx),
      fun x hx => hD' x (hm x hx) (.inr (by
        simp [Stmt.modifiedVars, HasVarsImp.modifiedVars, CmdExt.modifiedVars, hx])),
      fun x hx => ?_, ho⟩,
      VarTyping.annotates_congr hann fun x _ hx => hΓ x (hread x
        (Cmd.mem_getVars_of_typed c hx))⟩
    cases h : D' x
    · rfl
    · have := hD x h; rw [hdf x hx] at this; cases this
  | .cmd (.call pname tyArgs args md) =>
    obtain ⟨c', hc'⟩ := exists_baseCmd_of_noCalls hnc
    cases hc'
  | .block l ss md =>
    rw [dropDeadDefsStmt_block] at hD' hΓ ⊢
    rw [Stmt.noLoops_block] at hnl
    simp only [Stmt.defUseWellFormed] at hdu ⊢
    simp only [Stmt.fvarTypesWellAnnotated] at hann ⊢
    have hmen : ∀ n, BMentions (dropDeadDefsAux Fl Dd L added ss).1 n →
        Mentions (.block l (dropDeadDefsAux Fl Dd L added ss).1 md) n := fun n h =>
      h.imp mem_getVars_block mem_modOrDef_block
    exact sweep_wf fs Dd L added ss D D' Γ Γ' hnl (noCalls_block hnc) hdu hann hD
      (fun n hn hm => hD' n hn (hmen n hm)) (fun n hm => hΓ n (hmen n hm))
  | .ite c ts es md =>
    rw [dropDeadDefsStmt_ite_arms] at hD' hΓ ⊢
    rw [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    simp only [Stmt.defUseWellFormed, Bool.and_eq_true, List.all_eq_true] at hdu ⊢
    simp only [Stmt.fvarTypesWellAnnotated] at hann ⊢
    obtain ⟨⟨⟨hcv, hco⟩, hdt⟩, hde⟩ := hdu
    have hcm : ∀ n ∈ c.getVars, Mentions (.ite c (dropDeadDefsAux Fl Dd L [] ts).1
        (dropDeadDefsAux Fl Dd L [] es).1 md) n := fun n hn =>
      .inl (by simp [Stmt.getVars, hn])
    have hmt : ∀ n, BMentions (dropDeadDefsAux Fl Dd L [] ts).1 n →
        Mentions (.ite c (dropDeadDefsAux Fl Dd L [] ts).1
          (dropDeadDefsAux Fl Dd L [] es).1 md) n := fun n h =>
      h.imp mem_getVars_iteThen mem_modOrDef_iteThen
    have hme : ∀ n, BMentions (dropDeadDefsAux Fl Dd L [] es).1 n →
        Mentions (.ite c (dropDeadDefsAux Fl Dd L [] ts).1
          (dropDeadDefsAux Fl Dd L [] es).1 md) n := fun n h =>
      h.imp mem_getVars_iteElse mem_modOrDef_iteElse
    have ht := sweep_wf fs Dd L [] ts D D' Γ Γ' hnl.1 (noCalls_ite hnc).1 hdt hann.2.1 hD
      (fun n hn hm => hD' n hn (hmt n hm)) (fun n hm => hΓ n (hmt n hm))
    have he := sweep_wf fs Dd L [] es D D' Γ Γ' hnl.2 (noCalls_ite hnc).2 hde hann.2.2 hD
      (fun n hn hm => hD' n hn (hme n hm)) (fun n hm => hΓ n (hme n hm))
    exact ⟨⟨⟨⟨fun n hn => hD' n (hcv n hn) (hcm n hn), hco⟩, ht.1⟩, he.1⟩,
      VarTyping.annotates_congr hann.1 fun x _ hx =>
        hΓ x (hcm x (ExprOrNondet.mem_getVars_of_typed c hx)), ht.2, he.2⟩
  | .loop g m invs body md => rw [Stmt.noLoops_loop] at hnl; cases hnl
  | .exit l md =>
    rw [dropDeadDefsStmt_exit]
    exact ⟨rfl, trivial⟩
  | .typeDecl tc md =>
    rw [dropDeadDefsStmt_typeDecl]
    exact ⟨rfl, trivial⟩
  termination_by sizeOf s

/-- **Sweeping a list keeps it well-formed.** A list without loops or calls, def-use
    well-formed from `D` and well annotated for `Γ`, sweeps to one def-use well-formed from any
    `D'` within `D` that has every name of `D` the swept list mentions, and well annotated for
    any `Γ'` that agrees with `Γ` on those names: a dropped `init` declares a variable nothing
    after it mentions. -/
private theorem sweep_wf (fs : CoreIdent → Bool) (Dd : Defined) (L : Std.HashSet String)
    (added : List String) (ss : List Statement) (D D' : CoreIdent → Bool)
    (Γ Γ' : VarTyping Expression) (hnl : Block.noLoops ss = true)
    (hnc : Statements.noCalls ss = true)
    (hdu : Block.defUseWellFormed (P := Expression) (C := Command) D fs ss = true)
    (hann : Block.fvarTypesWellAnnotated (P := Expression) (C := Command) Γ ss)
    (hD : ∀ n, D' n = true → D n = true)
    (hD' : ∀ n, D n = true → BMentions (dropDeadDefsAux Fl Dd L added ss).1 n → D' n = true)
    (hΓ : ∀ n, BMentions (dropDeadDefsAux Fl Dd L added ss).1 n → Γ' n = Γ n) :
    Block.defUseWellFormed (P := Expression) (C := Command) D' fs
        (dropDeadDefsAux Fl Dd L added ss).1 = true ∧
      Block.fvarTypesWellAnnotated (P := Expression) (C := Command) Γ'
        (dropDeadDefsAux Fl Dd L added ss).1 := by
  match ss with
  | [] => rw [dropDeadDefsAux_nil]; exact ⟨rfl, trivial⟩
  | s :: rest =>
    rw [Block.noLoops_cons, Bool.and_eq_true] at hnl
    simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
    simp only [Block.fvarTypesWellAnnotated] at hann
    by_cases hdead : ∃ y, definedBy Fl Dd s = some y ∧
        (dropDeadDefsAux Fl (Dd.after s) L added rest).2.1.contains y.name = false
    · obtain ⟨y, hdef, hfalse⟩ := hdead
      rw [dropDeadDefsAux_cons_dead hdef hfalse] at hD' hΓ ⊢
      obtain ⟨ty, e, md, rfl, -⟩ := init_of_definedBy hdef
      have hne : ∀ n, BMentions (dropDeadDefsAux Fl (Dd.after (.init y ty (.det e) md)) L added
          rest).1 n → n ≠ y := by
        intro n hn hny
        subst hny
        have hlive := (mem_dropDeadDefsAux_live (Dd.after _) L added rest n.name).mpr
          (.inr (hn.imp (fun h => List.mem_map.mpr ⟨_, h, rfl⟩)
            (fun h => List.mem_map.mpr ⟨_, h, rfl⟩)))
        rw [Std.HashSet.mem_iff_contains, hfalse] at hlive
        cases hlive
      refine sweep_wf fs _ L added rest _ D' _ Γ' hnl.2 (noCalls_cons hnc).2 hdu.2 hann.2
        (fun n h => by simp [hD n h]) (fun n hn hm => hD' n ?_ hm) (fun n hm => ?_)
      · have hny := hne n hm
        simpa [Stmt.definedVars, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars,
          hny] using hn
      · rw [hΓ n hm]
        simp only [Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars,
          CmdExt.typedDefinedVars, Cmd.typedDefinedVars]
        exact (VarTyping.extend_of_not_mem (d := [(y, ty)]) (by simpa using hne n hm)).symm
    · rw [dropDeadDefsAux_cons_keep (keep_of_not_dead hdead)] at hD' hΓ ⊢
      simp only at hD' hΓ ⊢
      obtain ⟨hdv, htd⟩ := sweepStmt_decls (Fl := Fl) Dd
        (dropDeadDefsAux Fl (Dd.after s) L added rest).2.1
        (dropDeadDefsAux Fl (Dd.after s) L added rest).2.2 s
      have h1 := sweepStmt_wf fs Dd _ _ s D D' Γ Γ' hnl.1 (noCalls_cons hnc).1 hdu.1 hann.1 hD
        (fun n hn hm => hD' n hn (BMentions.head hm)) (fun n hm => hΓ n (BMentions.head hm))
      have h2 := sweep_wf fs (Dd.after s) L added rest _
        (fun n => D' n || decide (n ∈ Stmt.definedVars (P := Expression) (C := Command) s true))
        _ (Γ'.extend (Stmt.typedDefinedVars (P := Expression) (C := Command) s)) hnl.2
        (noCalls_cons hnc).2 hdu.2 hann.2
        (fun n h => by
          rcases Bool.or_eq_true_iff.mp h with h | h
          · simp [hD n h]
          · simp [h])
        (fun n hn hm => by
          rcases Bool.or_eq_true_iff.mp hn with h | h
          · simp [hD' n h hm.tail]
          · simp [h])
        (fun n hm => VarTyping.extend_congr _ (hΓ n hm.tail))
      simp only [Block.defUseWellFormed, Bool.and_eq_true, Block.fvarTypesWellAnnotated]
      rw [hdv, htd]
      exact ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩
  termination_by sizeOf ss
end

/-- The sweep adds no `exit` target. -/
private theorem dropDeadDefs_labels (D : Defined) (L : Std.HashSet String)
    (ss : List Statement) :
    ∀ l ∈ Block.labels (dropDeadDefs Fl D L ss), l ∈ Block.labels ss :=
  sweep_labels D L [] ss

/-- The sweep declares nothing the list does not. -/
private theorem dropDeadDefs_definedVars (D : Defined) (L : Std.HashSet String)
    (ss : List Statement) :
    ∀ n ∈ Block.definedVars (P := Expression) (C := Command) (dropDeadDefs Fl D L ss) false,
      n ∈ Block.definedVars (P := Expression) (C := Command) ss false :=
  (sweep_sub D L [] ss).1

/-- The sweep has no init-type the list does not. -/
private theorem dropDeadDefs_initTypes (D : Defined) (L : Std.HashSet String)
    (ss : List Statement) :
    ∀ t ∈ Block.initTypes (P := Expression) (C := Command) (dropDeadDefs Fl D L ss),
      t ∈ Block.initTypes (P := Expression) (C := Command) ss :=
  (sweep_sub D L [] ss).2

end Sweep

/-- Simplify declares no variable the body does not. -/
private theorem sweptBody_definedVars (base : Ctx) (proc : Procedure) (ss : List Statement) :
    ∀ n ∈ Block.definedVars (P := Expression) (C := Command) (sweptBody base proc ss) false,
      n ∈ Block.definedVars (P := Expression) (C := Command) ss false := fun n hn => by
  have := dropDeadDefs_definedVars _ _ _ n hn
  rwa [simpStmts_definedVars] at this

/-- **The simplified body's gate.** It follows from the body's gate, the def-use
    well-formedness of the simplified body and a typing of the entry store its annotations
    agree with, since Simplify declares no variable and no init-type the body does not. -/
theorem sweptBody_blockInitEnvWF {params : Core.Logic.InitEnvWFParams}
    {ss : List Statement} {ρ : Imperative.Env Expression} {base : Ctx} {proc : Procedure}
    (h : Core.Logic.BlockInitEnvWF params ss ρ)
    (hdu : Block.defUseWellFormed (fun x => (ρ.store x).isSome) params.declaredFuncs
      (sweptBody base proc ss) = true)
    (hfv : ∃ Γ, StoreHasTyping ρ.factory ρ.store Γ ∧
      Block.fvarTypesWellAnnotated (P := Expression) (C := Command) Γ (sweptBody base proc ss))
    (hss : Block.noLoops ss = true) :
    Core.Logic.BlockInitEnvWF params (sweptBody base proc ss) ρ := by
  have hdv := sweptBody_definedVars base proc ss
  have hit : ∀ t ∈ Block.initTypes (P := Expression) (C := Command) (sweptBody base proc ss),
      t ∈ Block.initTypes (P := Expression) (C := Command) ss := fun t ht => by
    have := dropDeadDefs_initTypes _ _ _ t ht
    rwa [simpStmts_initTypes] at this
  exact { h with
    readWritesDefined := fun _ hn hnd =>
      Block.defined_of_mem_touchedVars (fun _ _ h => h) hdu hn hnd
    defsUndefined := fun n hn => h.defsUndefined n (hdv n hn)
    measuresTyped := fun m hm => by
      rw [sweptBody, Block.measures_nil_of_noLoops _ (dropDeadDefs_noLoops _ _
        (simpStmts_noLoops _ _ hss))] at hm
      cases hm
    fvarTypesOk := hfv
    exitsNotReserved := fun l hl => h.exitsNotReserved l (by
      have := dropDeadDefs_labels _ _ _ l hl
      rwa [simpStmts_labels] at this)
    definedVarsNotReserved := fun n hn => h.definedVarsNotReserved n (hdv n hn)
    defUseOk := hdu
    initTypesInhabited := fun ty hty => h.initTypesInhabited ty (hit ty hty) }


/-- **The phase's check is sound.** If the body's entry environment is well-formed, over the
    context's factory, and the simplified body passes `gateOK`, the simplified body's entry
    environment is well-formed for the same parameters. The check declares the factory's
    functions, which the gate declares (`BlockInitEnvWF.runtimeFactoryDeclared`), and reads
    variables from the body's entry variables, which the entry store binds. This needs no
    condition on the factory: it covers factories whose inlined bodies call undeclared
    operators, for which the check fails and the phase keeps the body. -/
theorem gateOK_blockInitEnvWF {params : Core.Logic.InitEnvWFParams}
    {ss : List Statement} {ρ : Imperative.Env Expression} {base : Ctx} {proc : Procedure}
    (h : Core.Logic.BlockInitEnvWF params ss ρ) (hF : ρ.factory.factory = base.factory)
    (hg : gateOK base.factory ss (sweptBody base proc ss) = true)
    (hss : Block.noLoops ss = true) :
    Core.Logic.BlockInitEnvWF params (sweptBody base proc ss) ρ := by
  simp only [gateOK, Bool.and_eq_true] at hg
  rw [Block.defUseWellFormedHashed_empty (P := Expression) (C := Command),
    Block.annotsAgreeHashed_eq (P := Expression) (C := Command)] at hg
  have hD : (fun x => (Std.HashSet.ofList
      ((Block.touchedVars (P := Expression) (C := Command) ss).filter fun x => !(Std.HashSet.ofList
        (Block.definedVars (P := Expression) (C := Command) ss false)).contains x)).contains x) =
      fun x : CoreIdent => decide (x ∈ Block.entryVars ss) := by
    funext x
    simp [Std.HashSet.contains_ofList, Block.entryVars]
  rw [hD] at hg
  have hdu := Block.defUse_declared _ _ _ params.declaredFuncs
    (fun f hf => h.runtimeFactoryDeclared f (hF ▸ of_decide_eq_true hf)) hg.1
  refine sweptBody_blockInitEnvWF h (Block.defUse_grow _ _ _ _ ⟨?_, ?_⟩ hdu) ?_ hss
  · intro x hx
    have hx' : x ∈ Block.entryVars ss := of_decide_eq_true hx
    simp only [Block.entryVars, List.mem_filter, decide_eq_true_eq] at hx'
    exact h.readWritesDefined x hx'.1 hx'.2
  · intro x hx
    have hxs := sweptBody_definedVars base proc ss x hx
    have hnone : ρ.store x = none := Option.isNone_iff_eq_none.mp (h.defsUndefined x hxs)
    have hne : x ∉ Block.entryVars ss := by
      intro hm
      simp only [Block.entryVars, List.mem_filter, decide_eq_true_eq] at hm
      exact hm.2 hxs
    simp only [hnone, Option.isSome_none, hne, decide_false]
  · obtain ⟨Γ, hσ, hw⟩ := h.fvarTypesOk
    exact ⟨Γ, hσ, Block.annotsAgreeB_transport hw hg.2⟩

/-- **Simplify keeps a body well-formed.** A body without loops or calls, def-use well-formed
    from `D`, typed under a typing `Γ` of monotypes and whose init-types are monotypes,
    simplified from a context that records nothing and whose fold factory brings in only
    declared operators, becomes a body def-use well-formed from `D` and well annotated for `Γ`:
    the simplification pass keeps both (`simpStmts_wf`), and so does the sweep, which drops
    only definitions nothing after them mentions (`sweep_wf`). -/
private theorem sweptBody_wf {base : Ctx} {fs : CoreIdent → Bool} (hB : WFSetup base fs)
    (hempty : base.values.toList = []) (proc : Procedure) {ss : List Statement}
    {D : CoreIdent → Bool} {Γ : VarTyping Expression} (hmono : MonoTyping Γ)
    (hinit : ∀ ty ∈ Block.initTypes (P := Expression) (C := Command) ss, ∃ τ, ty = .forAll [] τ)
    (hnl : Block.noLoops ss = true) (hnc : Statements.noCalls ss = true)
    (hdu : Block.defUseWellFormed (P := Expression) (C := Command) D fs ss = true)
    (hok : Block.exprsOKIn base.factory Γ ss) :
    Block.defUseWellFormed (P := Expression) (C := Command) D fs (sweptBody base proc ss) = true ∧
      Block.fvarTypesWellAnnotated (P := Expression) (C := Command) Γ (sweptBody base proc ss) := by
  have hV : ValuesOK fs [] D Γ base := fun x r hm => by rw [hempty] at hm; cases hm
  obtain ⟨h1, h2, -, -⟩ := simpStmts_wf hB ss base D Γ (Ctx.Fixed.refl base) hV hmono hinit hnl
    hnc hdu hok
  exact sweep_wf fs _ _ [] _ D D Γ Γ (simpStmts_noLoops _ _ hnl) (simpStmts_noCalls _ _ hnc) h1 h2
    (fun _ h => h) (fun _ h _ => h) (fun _ _ => rfl)

/-- **Simplify adds no call.** The body the phase installs for a body without calls has
    none. -/
theorem checkedBody_noCalls (base : Ctx) (proc : Procedure) {ss : List Statement}
    (h : Statements.noCalls ss = true) : Statements.noCalls (checkedBody base proc ss) = true := by
  simp only [checkedBody]
  split
  · exact sweep_noCalls _ _ [] _ (simpStmts_noCalls base ss h)
  · exact h

end -- public section

end Core.Simplify
