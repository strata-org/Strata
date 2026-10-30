/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BigStep.Sem
public import Strata.DL.Imperative.Logic.TraceRelations
public import Strata.DL.Imperative.CmdProps

/-! # Properties of the big-step semantics of loop-free and obligation programs

Inversions of the command semantics `EvalE` for `init`, `set`, `assume`, `assert` and `cover`,
and the effect of a store update; sequencing of runs and reaches (`brun_append`,
`breach_append_run`, `breach_cmd_cons`) and failures as reaches whose events claim them
(`fails_iff_claim`); and the conditions of the events of a run, a reach or a failure read only
identifiers of the list (`brun_fv`, `breach_fv`, `fails_fv`).

Key theorems: `evalE_init_det_inv`, `evalE_init_nondet_inv`, `evalE_set_det_inv`,
`evalE_set_nondet_inv`, `evalE_assume_inv`, `evalE_assert_inv`, `evalE_cover_inv`,
`update_facts`, `evalInterp_stableUnder` (evaluation to `true` is stable under the shared
semantic event relation `EventArg.WithWF`), `brun_append`, `breach_append_run`,
`fails_iff_claim`, `brun_fv`, `breach_fv`, `fails_fv`. -/

namespace Imperative
namespace BigStep

public section

variable {P : PureExpr} [HasBool P] [HasFvar P]

section
variable [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
  [HasFvars P] [LawfulHasVal P]

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasFvars P] [LawfulHasVal P] in
/-- A deterministic `init x : ty := e` step evaluates `e` to a value `v` of type `ty`
    (`HasVal.valueOfTy F v ty`), defines the undefined `x` as `v`, leaves the other
    variables unchanged and emits no event. -/
theorem evalE_init_det_inv_typed {F : P.Factory} {σ σ1 : SemanticStore P}
    {x : P.Ident} {ty : P.Ty} {e : P.Expr} {md : MetaData P}
    {evs : List (Event P)} (h : EvalE F σ (.cmd (.init x ty (.det e) md)) σ1 evs) :
    ∃ v, P.eval F σ e = some v ∧ σ x = none ∧ σ1 x = some v ∧ (∀ y, x ≠ y → σ1 y = σ y) ∧
      evs = [] ∧ HasVal.valueOfTy F v ty :=
  match h with | .eval_init hev (.init h0 h1 hfr) hty _ => ⟨_, hev, h0, h1, hfr, rfl, hty⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasFvars P] [LawfulHasVal P] in
/-- A nondeterministic `init x : ty` step defines the undefined `x` as some value `v` of
    type `ty`, leaves the other variables unchanged and emits no event. -/
theorem evalE_init_nondet_inv_typed {F : P.Factory} {σ σ1 : SemanticStore P}
    {x : P.Ident} {ty : P.Ty} {md : MetaData P}
    {evs : List (Event P)} (h : EvalE F σ (.cmd (.init x ty .nondet md)) σ1 evs) :
    ∃ v, HasVal.valueOfTy F v ty ∧ σ x = none ∧ σ1 x = some v ∧
      (∀ y, x ≠ y → σ1 y = σ y) ∧ evs = [] :=
  match h with | .eval_init_unconstrained (.init h0 h1 hfr) hty _ => ⟨_, hty, h0, h1, hfr, rfl⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasFvars P] [LawfulHasVal P] in
/-- A deterministic `init x := e` step evaluates `e` to a value `v`, defines the
    undefined `x` as `v`, leaves the other variables unchanged and emits no event. -/
theorem evalE_init_det_inv {F : P.Factory} {σ σ1 : SemanticStore P}
    {x : P.Ident} {ty : P.Ty} {e : P.Expr} {md : MetaData P}
    {evs : List (Event P)} (h : EvalE F σ (.cmd (.init x ty (.det e) md)) σ1 evs) :
    ∃ v, P.eval F σ e = some v ∧ σ x = none ∧ σ1 x = some v ∧ (∀ y, x ≠ y → σ1 y = σ y) ∧
      evs = [] :=
  (evalE_init_det_inv_typed h).imp fun _ ⟨hev, h0, h1, hfr, he, _⟩ => ⟨hev, h0, h1, hfr, he⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    in
/-- A nondeterministic `init x` step defines the undefined `x` as some value `v`,
    leaves the other variables unchanged and emits no event. -/
theorem evalE_init_nondet_inv {F : P.Factory} {σ σ1 : SemanticStore P}
    {x : P.Ident} {ty : P.Ty} {md : MetaData P}
    {evs : List (Event P)} (h : EvalE F σ (.cmd (.init x ty .nondet md)) σ1 evs) :
    ∃ v, HasVal.value F v ∧ σ x = none ∧ σ1 x = some v ∧
      (∀ y, x ≠ y → σ1 y = σ y) ∧ evs = [] :=
  (evalE_init_nondet_inv_typed h).imp fun _ ⟨hty, hrest⟩ =>
    ⟨LawfulHasVal.valueOfTy_isVal _ _ _ hty, hrest⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasFvars P] [LawfulHasVal P] in
/-- Inversion of a deterministic `set`: its value and the updated store. -/
theorem evalE_set_det_inv {F : P.Factory} {σ σ1 : SemanticStore P}
    {x : P.Ident} {e : P.Expr} {md : MetaData P}
    {evs : List (Event P)} (h : EvalE F σ (.cmd (.set x (.det e) md)) σ1 evs) :
    ∃ v, P.eval F σ e = some v ∧ HasVal.valueOfStoredTy (P := P) F σ x v ∧ σ1 x = some v ∧
      (∀ y, x ≠ y → σ1 y = σ y) ∧ evs = [] :=
  match h with | .eval_set hev (.update _ h1 hfr) hty _ => ⟨_, hev, hty, h1, hfr, rfl⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasFvars P] [LawfulHasVal P] in
/-- Inversion of a nondeterministic `set`: its value and the updated store. -/
theorem evalE_set_nondet_inv {F : P.Factory} {σ σ1 : SemanticStore P}
    {x : P.Ident} {md : MetaData P}
    {evs : List (Event P)} (h : EvalE F σ (.cmd (.set x .nondet md)) σ1 evs) :
    ∃ v, HasVal.valueOfStoredTy (P := P) F σ x v ∧ σ1 x = some v ∧ (∀ y, x ≠ y → σ1 y = σ y) ∧
      evs = [] := match h with | .eval_set_nondet (.update _ h1 hfr) hty _ => ⟨_, hty, h1, hfr, rfl⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasFvars P] [LawfulHasVal P] in
/-- An `assume` step keeps the store and emits its assumption event. -/
theorem evalE_assume_inv {F : P.Factory} {σ σ1 : SemanticStore P}
    {l : String} {e : P.Expr} {md : MetaData P}
    {evs : List (Event P)} (h : EvalE F σ (.cmd (.assume l e md)) σ1 evs) :
    σ1 = σ ∧
      evs = [.assume { factory := F, store := σ, label := l, expr := e, metadata := md }] :=
  match h with | .eval_assume => ⟨rfl, rfl⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasFvars P] [LawfulHasVal P] in
/-- An `assert` step keeps the store and emits its assertion event. -/
theorem evalE_assert_inv {F : P.Factory} {σ σ1 : SemanticStore P}
    {l : String} {e : P.Expr} {md : MetaData P}
    {evs : List (Event P)} (h : EvalE F σ (.cmd (.assert l e md)) σ1 evs) :
    σ1 = σ ∧
      evs = [.assert { factory := F, store := σ, label := l, expr := e, metadata := md }] :=
  match h with | .eval_assert => ⟨rfl, rfl⟩

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasFvars P] [LawfulHasVal P] in
/-- A `cover` step keeps the store and emits its cover event. -/
theorem evalE_cover_inv {F : P.Factory} {σ σ1 : SemanticStore P}
    {l : String} {e : P.Expr} {md : MetaData P}
    {evs : List (Event P)} (h : EvalE F σ (.cmd (.cover l e md)) σ1 evs) :
    σ1 = σ ∧
      evs = [.cover { factory := F, store := σ, label := l, expr := e, metadata := md }] :=
  match h with | .eval_cover => ⟨rfl, rfl⟩

omit [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P] [HasFvar P]
    [HasFvars P] [LawfulHasVal P] in
/-- Updating `x` to `v` maps `x` to `v` and leaves the other variables unchanged. -/
theorem update_facts (σ : SemanticStore P) (x : P.Ident) (v : P.Expr) :
    Imperative.SemanticStore.update σ x v x = some v ∧
      (∀ y, x ≠ y → Imperative.SemanticStore.update σ x v y = σ y) :=
  ⟨by simp [SemanticStore.update], fun y hy => by simp [SemanticStore.update, Ne.symm hy]⟩

end

omit [HasFvar P] in
/-- Evaluation to `true` is stable under the shared semantic event relation:
related snapshots have the same factory and expression and agree on the
expression's free variables, so evaluator congruence transports the value. -/
theorem evalInterp_stableUnder {Extra : P.Ident → Prop} [HasFvars P] :
    ConditionInterp.StableUnder (P := P) (evalInterp : ConditionInterp P)
      (EventArg.WithWF (EventArg.ExtendsEnv Extra)) := by
  intro _ source target h
  obtain ⟨hfac, _, _, hexpr, _⟩ := h.rel
  have htargetWF : WellFormedStore target.store source.factory := by
    rw [hfac]
    exact h.targetStoreWF
  change P.eval source.factory source.store source.expr = some HasBool.tt ↔
    P.eval target.factory target.store target.expr = some HasBool.tt
  rw [← hfac, ← hexpr]
  rw [h.exprCongr source.expr source.store target.store
    h.sourceStoreWF htargetWF h.store_fv]

/-! ## Sequencing -/

section Sequencing
variable {F : P.Factory}

/-- A run of `a` ending normally followed by a run of `b` is a run of `a ++ b`. -/
theorem brun_append : ∀ {a b : PStmts P} {σ σ1 : SemanticStore P}
    {t1 t2 : List (Event P)} {o : Outcome P},
    BRun F a σ t1 (.normal σ1) → BRun F b σ1 t2 o → BRun F (a ++ b) σ (t1 ++ t2) o
  | [], _, _, _, _, _, _, .nil, h2 => h2
  | _ :: _, _, _, _, _, _, _, .cons_normal h1 h2, h3 =>
    List.append_assoc .. ▸ .cons_normal h1 (brun_append h2 h3)

/-- A run of `a` ending normally followed by a reach of `b` is a reach of `a ++ b`. -/
theorem breach_append_run :
    ∀ {a b : PStmts P} {σ σ1 : SemanticStore P} {t1 t2 : List (Event P)},
      BRun F a σ t1 (.normal σ1) → BReach F b σ1 t2 → BReach F (a ++ b) σ (t1 ++ t2)
  | [], _, _, _, _, _, .nil, h2 => h2
  | _ :: _, _, _, _, _, _, .cons_normal h1 h2, h3 =>
    List.append_assoc .. ▸ .later h1 (breach_append_run h2 h3)

/-- A command followed by `rest`, with no events of `rest` or a reach of `rest` after it, is
    reached with the command's events followed by those of `rest`. -/
theorem breach_cmd_cons {c : CmdExt P} {rest : PStmts P} {σ σ1 : SemanticStore P}
    {evs tr : List (Event P)} (hE : EvalE F σ c σ1 evs) (h : tr = [] ∨ BReach F rest σ1 tr) :
    BReach F (.cmd c :: rest) σ (evs ++ tr) :=
  h.elim (fun h => h ▸ (List.append_nil evs).symm ▸ .here (.cmd hE)) (.later (.cmd hE))

/-- A list fails the target `t` exactly when a reach of it emits events that claim a failure of
    `t`. -/
theorem fails_iff_claim {ss : PStmts P} {σ : SemanticStore P} {t : AssertId P} :
    Fails F ss σ t ↔ ∃ tr, BReach F ss σ tr ∧ Claim t tr :=
  ⟨fun ⟨evs, e, hb, hA, hf⟩ => ⟨_, hb, evs, e, rfl, hA, hf⟩,
    fun ⟨_, hb, evs, e, he, hA, hf⟩ => ⟨evs, e, he ▸ hb, hA, hf⟩⟩

end Sequencing

/-! ## The identifiers the events of a run read -/

section Idents
variable [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [HasFvars P] {F : P.Factory}

/-- The condition of every event of a command step reads only identifiers of the command. -/
private theorem evalE_fv {σ σ' : SemanticStore P} {c : Cmd P} {evs : List (Event P)}
    (h : EvalE F σ (.cmd c) σ' evs) :
    ∀ ev ∈ evs, ∀ y ∈ exprFV ev.condition.expr, y ∈ Stmt.idents (.cmd (.cmd c) : PStmt P) := by
  cases h <;> simp [Event.condition, Stmt.idents, getFvars_mem_exprFV]

mutual
/-- The condition of every event of a run reads only identifiers of the list. -/
theorem brun_fv : ∀ {ss : PStmts P} {σ : SemanticStore P}
    {evs : List (Event P)} {o : Outcome P}, BRun F ss σ evs o →
    ∀ ev ∈ evs, ∀ y ∈ exprFV ev.condition.expr, y ∈ Block.idents ss
  | _, _, _, _, .nil => nofun
  | _, _, _, _, .cons_normal h1 h2 => fun ev hev y hy =>
    (List.mem_append.1 hev).elim (fun hev => List.mem_append_left _ (brunS_fv h1 ev hev y hy))
      fun hev => List.mem_append_right _ (brun_fv h2 ev hev y hy)
  | _, _, _, _, .cons_exit h1 => fun ev hev y hy =>
    List.mem_append_left _ (brunS_fv h1 ev hev y hy)
/-- The condition of every event of a statement run reads only identifiers of the statement. -/
private theorem brunS_fv : ∀ {s : PStmt P} {σ : SemanticStore P}
    {evs : List (Event P)} {o : Outcome P}, BRunS F s σ evs o →
    ∀ ev ∈ evs, ∀ y ∈ exprFV ev.condition.expr, y ∈ Stmt.idents s
  | _, _, _, _, .cmd (c := .cmd _) h => evalE_fv h
  | _, _, _, _, .cmd (c := .call _ _ _) h => h.elim
  | _, _, _, _, .ite_true _ h | _, _, _, _, .ite_nondet_true h | _, _, _, _, .ite_false _ h
  | _, _, _, _, .ite_nondet_false h => fun ev hev y hy => by
    simp [Stmt.idents, brun_fv h ev hev y hy, ExprOrNondet.getVars_det,
      ExprOrNondet.getVars_nondet, getFvars_mem_exprFV]
  | _, _, _, _, .block h => brun_fv h
  | _, _, _, _, .exit | _, _, _, _, .typeDecl => nofun
end

mutual
/-- The condition of every event of a reach reads only identifiers of the list. -/
theorem breach_fv : ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)},
    BReach F ss σ evs → ∀ ev ∈ evs, ∀ y ∈ exprFV ev.condition.expr, y ∈ Block.idents ss
  | _, _, _, .here h => fun ev hev y hy => List.mem_append_left _ (breachS_fv h ev hev y hy)
  | _, _, _, .later h1 h2 => fun ev hev y hy =>
    (List.mem_append.1 hev).elim (fun hev => List.mem_append_left _ (brunS_fv h1 ev hev y hy))
      fun hev => List.mem_append_right _ (breach_fv h2 ev hev y hy)
/-- The condition of every event of a statement reach reads only identifiers of the
    statement. -/
private theorem breachS_fv : ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)},
    BReachS F s σ evs → ∀ ev ∈ evs, ∀ y ∈ exprFV ev.condition.expr, y ∈ Stmt.idents s
  | _, _, _, .cmd (c := .cmd _) h => evalE_fv h
  | _, _, _, .cmd (c := .call _ _ _) h => h.elim
  | _, _, _, .ite_true _ h | _, _, _, .ite_nondet_true h | _, _, _, .ite_false _ h
  | _, _, _, .ite_nondet_false h => fun ev hev y hy => by
    simp [Stmt.idents, breach_fv h ev hev y hy, ExprOrNondet.getVars_det,
      ExprOrNondet.getVars_nondet, getFvars_mem_exprFV]
  | _, _, _, .block h => breach_fv h
end

/-- The target a list fails reads only identifiers of the list. -/
theorem fails_fv {ss : PStmts P} {σ : SemanticStore P} {t : AssertId P}
    (h : Fails F ss σ t) : ∀ y ∈ exprFV t.expr, y ∈ Block.idents ss := by
  obtain ⟨evs, e, hb, -, hfe⟩ := h
  have he : e.condition.expr = t.expr := by
    cases e <;> simp only [FailsAt] at hfe <;> exact hfe.2.1
  exact he ▸ breach_fv hb e (List.mem_append_right _ (List.mem_singleton_self _))

end Idents

end -- public section

end BigStep
end Imperative
