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
import Strata.DL.Imperative.StmtProps

/-! # The simplified body's entry gate

Simplify declares no variable and no init-type the body does not: the simplification pass
keeps every `init` with its variable and type (`simpStmts_definedVars`,
`simpStmts_initTypes`), and the sweep only drops statements (`dropDeadDefsAux_definedVars`,
`dropDeadDefsAux_initTypes`). So the gate of the simplified body follows from the body's
gate and the def-use well-formedness of the simplified body (`simplifyBody_blockInitEnvWF`),
which is the one part of it Simplify's rewriting can change.

The key result is `targetWFB_sound`: when the body's entry environment is well-formed and
the decidable check `targetWFB` accepts the simplified body, the simplified body's entry
environment is well-formed.
-/

namespace Core.Simplify

open Imperative

public section

/-- Simplifying a command keeps what it declares. -/
private theorem simpCmd_definedVars (ctx : Ctx) (c : Imperative.Cmd Expression) (b : Bool) :
    Stmt.definedVars (P := Expression) (C := Command) (.cmd (.cmd (simpCmd ctx c).1)) b =
      Stmt.definedVars (P := Expression) (C := Command) (.cmd (.cmd c)) b := by
  cases c with
  | init x ty e md => cases e <;> rfl
  | set x e md => cases e <;> rfl
  | _ => rfl

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


/-- **The decidable target gate.** The simplified body `out` of `ss₀` is def-use
    well-formed from the body's entry variables, with the declared functions of `params`,
    and its free-variable annotations agree with those of `ss₀` (`Block.annotsAgreeB`).
    It is a computation on Simplify's output, so a caller with a concrete program
    discharges it by evaluation. -/
@[expose] def targetWFB (params : Core.Logic.InitEnvWFParams) (ss₀ out : List Statement) :
    Bool :=
  Block.defUseWellFormed (P := Expression) (C := Command)
    (fun x : CoreIdent => decide (x ∈ Block.entryVars ss₀)) params.declaredFuncs out &&
  Block.annotsAgreeB (P := Expression) (C := Command) ss₀ out

/-- The parameters whose declared functions are those of the factory `F`. -/
@[expose] def factoryParams (F : Lambda.Factory CoreLParams) : Core.Logic.InitEnvWFParams :=
  { prefixIdents := [], declaredFuncs := fun f => decide (f.name ∈ F) }

/-- The phase's check is `targetWFB` with the factory's functions declared. -/
theorem gateOK_eq_targetWFB (F : Lambda.Factory CoreLParams) (ss out : List Statement) :
    gateOK F ss out = targetWFB (factoryParams F) ss out := by
  simp only [gateOK, targetWFB, factoryParams]
  rw [Block.defUseWellFormedHashed_empty (P := Expression) (C := Command),
    Block.annotsAgreeHashed_eq (P := Expression) (C := Command)]
  have hD : (fun x => (Std.HashSet.ofList
      ((Block.touchedVars (P := Expression) (C := Command) ss).filter fun x => !(Std.HashSet.ofList
        (Block.definedVars (P := Expression) (C := Command) ss false)).contains x)).contains x) =
      fun x : CoreIdent => decide (x ∈ Block.entryVars ss) := by
    funext x
    simp [Std.HashSet.contains_ofList, Block.entryVars]
  rw [hD]

/-- `targetWFB` survives declaring more functions. -/
theorem targetWFB_mono {params params' : Core.Logic.InitEnvWFParams} {ss out : List Statement}
    (h : ∀ f, params.declaredFuncs f = true → params'.declaredFuncs f = true)
    (hB : targetWFB params ss out = true) : targetWFB params' ss out = true := by
  simp only [targetWFB, Bool.and_eq_true] at hB ⊢
  exact ⟨Block.defUse_declared out _ _ _ h hB.1, hB.2⟩

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
private theorem simplifyBody_definedVars {ss out : List Statement} {base : Ctx}
    {inputs : @Lambda.LMonoTySignature Unit} {live : Std.HashSet String}
    (hout : simplifyBody base inputs live ss = some out) :
    ∀ n ∈ Block.definedVars (P := Expression) (C := Command) out false,
      n ∈ Block.definedVars (P := Expression) (C := Command) ss false := fun n hn => by
  simp only [simplifyBody, Option.some.injEq] at hout
  subst hout
  have := dropDeadDefs_definedVars _ _ _ n hn
  rwa [simpStmts_definedVars] at this

/-- **The simplified body's gate.** It follows from the body's gate and the def-use
    well-formedness of the simplified body, since Simplify declares no variable and no
    init-type the body does not. -/
theorem simplifyBody_blockInitEnvWF {params : Core.Logic.InitEnvWFParams}
    {ss out : List Statement} {ρ : Imperative.Env Expression} {base : Ctx}
    {inputs : @Lambda.LMonoTySignature Unit} {live : Std.HashSet String}
    (h : Core.Logic.BlockInitEnvWF params ss ρ)
    (hout : simplifyBody base inputs live ss = some out)
    (hdu : Block.defUseWellFormed (fun x => (ρ.store x).isSome) params.declaredFuncs out =
      true)
    (hann : Block.annotsAgreeB (P := Expression) (C := Command) ss out = true)
    (hss : Block.noLoops ss = true) :
    Core.Logic.BlockInitEnvWF params out ρ := by
  simp only [simplifyBody, Option.some.injEq] at hout
  subst hout
  have hdv : ∀ n ∈ Block.definedVars (P := Expression) (C := Command)
      (dropDeadDefs base.factory (Defined.ofParams inputs (simpStmts base ss).1) live
        (simpStmts base ss).1) false,
      n ∈ Block.definedVars (P := Expression) (C := Command) ss false := fun n hn => by
    have := dropDeadDefs_definedVars _ _ _ n hn
    rwa [simpStmts_definedVars] at this
  have hit : ∀ t ∈ Block.initTypes (P := Expression) (C := Command)
      (dropDeadDefs base.factory (Defined.ofParams inputs (simpStmts base ss).1) live
        (simpStmts base ss).1),
      t ∈ Block.initTypes (P := Expression) (C := Command) ss := fun t ht => by
    have := dropDeadDefs_initTypes _ _ _ t ht
    rwa [simpStmts_initTypes] at this
  exact { h with
    readWritesDefined := fun _ hn hnd =>
      Block.defined_of_mem_touchedVars (fun _ _ h => h) hdu hn hnd
    defsUndefined := fun n hn => h.defsUndefined n (hdv n hn)
    measuresTyped := fun m hm => by
      rw [Block.measures_nil_of_noLoops _ (dropDeadDefs_noLoops _ _
        (simpStmts_noLoops _ _ hss))] at hm
      cases hm
    fvarTypesOk := by
      obtain ⟨Γ, hσ, hw⟩ := h.fvarTypesOk
      exact ⟨Γ, hσ, Block.annotsAgreeB_transport hw hann⟩
    exitsNotReserved := fun l hl => h.exitsNotReserved l (by
      have := dropDeadDefs_labels _ _ _ l hl
      rwa [simpStmts_labels] at this)
    definedVarsNotReserved := fun n hn => h.definedVarsNotReserved n (hdv n hn)
    defUseOk := hdu
    initTypesInhabited := fun ty hty => h.initTypesInhabited ty (hit ty hty) }


/-- **The decidable gate is sound.** If the body's entry environment is well-formed and the
    simplified body passes `targetWFB`, the simplified body's entry environment is
    well-formed for the same parameters. -/
theorem targetWFB_sound {params : Core.Logic.InitEnvWFParams}
    {ss out : List Statement} {ρ : Imperative.Env Expression} {base : Ctx}
    {inputs : @Lambda.LMonoTySignature Unit} {live : Std.HashSet String}
    (h : Core.Logic.BlockInitEnvWF params ss ρ)
    (hout : simplifyBody base inputs live ss = some out)
    (hB : targetWFB params ss out = true) (hss : Block.noLoops ss = true) :
    Core.Logic.BlockInitEnvWF params out ρ := by
  simp only [targetWFB, Bool.and_eq_true] at hB
  refine simplifyBody_blockInitEnvWF h hout (Block.defUse_grow out _ _ _ ⟨?_, ?_⟩ hB.1) hB.2 hss
  · intro x hx
    have hx' : x ∈ Block.entryVars ss := of_decide_eq_true hx
    simp only [Block.entryVars, List.mem_filter, decide_eq_true_eq] at hx'
    exact h.readWritesDefined x hx'.1 hx'.2
  · intro x hx
    have hxs := simplifyBody_definedVars hout x hx
    have hnone : ρ.store x = none := Option.isNone_iff_eq_none.mp (h.defsUndefined x hxs)
    have hne : x ∉ Block.entryVars ss := by
      intro hm
      simp only [Block.entryVars, List.mem_filter, decide_eq_true_eq] at hm
      exact hm.2 hxs
    simp only [hnone, Option.isSome_none, hne, decide_false]

end -- public section

end Core.Simplify
