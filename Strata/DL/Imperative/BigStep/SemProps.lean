/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BigStep.Sem
public import Strata.DL.Imperative.Logic.TraceRelations
public import Strata.DL.Imperative.CmdProps
import Strata.DL.Imperative.Logic.TraceInterpProps

/-! # Properties of the big-step semantics

The effect of a store update; sequencing of runs and reaches (`brun_append`,
`brun_append_exit`, `breach_append_left`, `breach_append_run`, `breach_cmd_cons`) and failures
as reaches whose events claim them (`fails_iff_claim`); claims of a failure along `++`
(`claim_prepend`, `claim_split`), on one event (`claim_single`), on no event (`Claim.not_nil`)
and after a command (`reach_cmd_claim`), and reaches after a run or a statement
(`reach_after_run`, `reach_after_stmt`); evaluation to
`true` (`evalInterp_holds_iff`) and a failing check carried over to a condition with the same
values (`failsAt_transfer`); and
the conditions of the events of a run, a reach or a failure read only identifiers of the list
(`brun_fv`, `breach_fv`, `fails_fv`). A run keeps the variables defined
at its start defined (`brun_dom`), defines only those and the list's (`brun_sub`), changes no
variable it does not modify (`brun_frame`), keeps
the store value-valued, its values typed in agreement with the start (`brun_typed`,
`brunS_typed`, `TypeAgree`), leaving a scope keeps it value-valued (`WellFormedStore.proj`), and a
statement ending normally defines exactly its start's variables and its top-level definitions
(`brunS_normal_isSome`); a list exits only to the labels of its `exit`s (`brun_exit_label`), and
only to labels of enclosing blocks when its blocks catch the others (`brun_exit_covered`).
Under evaluation to `true`, an assumption or a check is
the counterpart (`Event.WeakensAssume`) of one with the same label whose condition evaluates as
required (`Event.WeakensAssume.assume`, `Event.WeakensAssume.check`).

Inversions of single command steps are the `EvalCmdE.*_inv` lemmas of `CmdSemanticsProps`;
they apply to `EvalE` on a base command, which unfolds to `EvalCmdE`.

Key theorems: `update_facts`, `evalInterp_stableUnder` (evaluation to `true` is stable
under the shared semantic event relation `EventArg.WithWF`), `brun_append`, `brun_append_exit`,
`breach_append_left`, `breach_append_run`,
`fails_iff_claim`, `claim_prepend`, `claim_split`, `reach_cmd_claim`, `failsAt_transfer`,
`brun_fv`, `breach_fv`, `fails_fv`, `brun_dom`, `brun_sub`, `brun_frame`,
`brun_typed`, `brunS_normal_isSome`, `brun_exit_label`, `brun_exit_covered`,
`Event.WeakensAssume.assume`,
`Event.WeakensAssume.check`. -/

namespace Imperative
namespace BigStep

public section

variable {P : PureExpr} [HasBool P] [HasFvar P]

section
variable [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
  [HasFvars P] [LawfulHasVal P]

omit [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P] [HasFvar P]
    [HasFvars P] [LawfulHasVal P] in
/-- Updating `x` to `v` maps `x` to `v` and leaves the other variables unchanged. -/
theorem update_facts (σ : SemanticStore P) (x : P.Ident) (v : P.Val) :
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
  change P.eval source.factory source.store source.expr = some (HasBool.ttVal source.factory) ↔
    P.eval target.factory target.store target.expr = some (HasBool.ttVal target.factory)
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

/-- A run of `a` exiting is a run of `a ++ b`, which exits the same way. -/
theorem brun_append_exit : ∀ {a b : PStmts P} {σ σ1 : SemanticStore P}
    {t : List (Event P)} {l : String},
    BRun F a σ t (.exit l σ1) → BRun F (a ++ b) σ t (.exit l σ1)
  | _ :: _, _, _, _, _, _, .cons_normal h1 h2 => .cons_normal h1 (brun_append_exit h2)
  | _ :: _, _, _, _, _, _, .cons_exit h1 => .cons_exit h1

/-- A reach of `a` is a reach of `a ++ b`. -/
theorem breach_append_left : ∀ {a b : PStmts P} {σ : SemanticStore P} {t : List (Event P)},
    BReach F a σ t → BReach F (a ++ b) σ t
  | _ :: _, _, _, _, .here h => .here h
  | _ :: _, _, _, _, .later h1 h2 => .later h1 (breach_append_left h2)

/-- A run of `a` ending normally followed by a reach of `b` is a reach of `a ++ b`. -/
theorem breach_append_run :
    ∀ {a b : PStmts P} {σ σ1 : SemanticStore P} {t1 t2 : List (Event P)},
      BRun F a σ t1 (.normal σ1) → BReach F b σ1 t2 → BReach F (a ++ b) σ (t1 ++ t2)
  | [], _, _, _, _, _, .nil, h2 => h2
  | _ :: _, _, _, _, _, _, .cons_normal h1 h2, h3 =>
    List.append_assoc .. ▸ .later h1 (breach_append_run h2 h3)

/-- A command emitting events followed by `rest`, with no events of `rest` or a reach of `rest`
    after it, is reached with the command's events followed by those of `rest`. -/
theorem breach_cmd_cons {c : CmdExt P} {rest : PStmts P} {σ σ1 : SemanticStore P}
    {evs tr : List (Event P)} (hE : EvalE F σ c σ1 evs) (he : evs ≠ [])
    (h : tr = [] ∨ BReach F rest σ1 tr) :
    BReach F (.cmd c :: rest) σ (evs ++ tr) :=
  h.elim (fun h => h ▸ (List.append_nil evs).symm ▸ .here (.cmd hE he)) (.later (.cmd hE))

/-- A list fails the target `t` with the condition `e` exactly when a reach of it emits events
    that claim a failure of `t` with the condition `e`. -/
theorem fails_iff_claim {ss : PStmts P} {σ : SemanticStore P} {t : AssertId P} {e : P.Expr} :
    Fails F ss σ t e ↔ ∃ tr, BReach F ss σ tr ∧ Claim t e tr :=
  ⟨fun ⟨evs, ev, hb, hA, hf⟩ => ⟨_, hb, evs, ev, rfl, hA, hf⟩,
    fun ⟨_, hb, evs, ev, he, hA, hf⟩ => ⟨evs, ev, he ▸ hb, hA, hf⟩⟩

mutual
/-- A reach of a list emits events. -/
theorem breach_ne_nil {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)} :
    BReach F ss σ evs → evs ≠ []
  | .here h => breachS_ne_nil h
  | .later _ h => by simpa using fun _ => breach_ne_nil h

/-- A reach of a statement emits events. -/
theorem breachS_ne_nil {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)} :
    BReachS F s σ evs → evs ≠ []
  | .cmd _ h => h
  | .ite_true _ h | .ite_false _ h | .ite_nondet_true h | .ite_nondet_false h | .block h
  | .loop_here _ h => breach_ne_nil h
  | .loop_later _ _ h => by simpa using fun _ => breachS_ne_nil h
end

end Sequencing

/-! ## Claims of a failure -/

section Claims
variable {F : P.Factory}

omit [HasFvar P] in
/-- A feasible prefix keeps a trace claiming a failure of `t` with the condition `e` claiming
    it. -/
theorem claim_prepend {t : AssertId P} {tr1 tr2 : List (Event P)} {e : P.Expr}
    (h1 : Trace.AssumptionsHold P evalInterp () tr1)
    (h2 : Claim t e tr2) : Claim t e (tr1 ++ tr2) :=
  match h2 with
  | ⟨evs, ev, htr, hf, ht⟩ =>
    ⟨tr1 ++ evs, ev, by simp [htr], Trace.AssumptionsHold.append h1 hf, ht⟩

omit [HasFvar P] in
/-- If the events `a ++ b`, with `b` nonempty, claim a failure of `t` with the condition `e`,
    then `a` is feasible and `b` claims it. -/
theorem claim_split {e : P.Expr} {t : AssertId P} {a b : List (Event P)} (hb : b ≠ [])
    (h : Claim t e (a ++ b)) : Trace.AssumptionsHold P evalInterp () a ∧ Claim t e b := by
  obtain ⟨evs, ev, he, hA, hf⟩ := h
  obtain ⟨b, e', rfl⟩ := (List.eq_nil_or_concat b).resolve_left hb
  obtain ⟨rfl, ⟨⟩⟩ := List.append_inj' (by simpa using he : a ++ b ++ [e'] = evs ++ [ev]) rfl
  exact ⟨fun c hc => hA c (by simp [hc]), b, _, by simp, fun c hc => hA c (by simp [hc]), hf⟩

omit [HasFvar P] in
/-- A single event claiming a failure at an occurrence of condition `cond` is a failing
    occurrence of the target with the condition `cond`. -/
theorem claim_single {t : AssertId P} {cond : P.Expr} {e : Event P} (h : Claim t cond [e]) :
    FailsAt t cond e := by
  obtain ⟨evs, e', he, -, hf⟩ := h
  cases evs <;> simp_all

omit [HasFvar P] in
/-- No trace claims a failure without events. -/
theorem Claim.not_nil {t : AssertId P} {cond : P.Expr} : ¬ Claim t cond [] :=
  fun ⟨_, _, h, _⟩ => by simp at h

/-- A reach of a list from a store some statements lead to without events is a reach of the
    statements followed by the list. -/
theorem reach_after_run {σS σS1 : SemanticStore P} {out o : PStmts P} {tr : List (Event P)}
    (hrun : BRun F o σS [] (.normal σS1)) (h : BReach F out σS1 tr) :
    ∃ tr0, BReach F (o ++ out) σS (tr0 ++ tr) ∧ Trace.AssumptionsHold P evalInterp () tr0 :=
  ⟨[], breach_append_run hrun h, nofun⟩

/-- A reach of a list after a statement that runs, with feasible events, is a reach of the
    statement followed by the list. -/
theorem reach_after_stmt {σS σS1 : SemanticStore P} {out : PStmts P} {tr evs : List (Event P)}
    {c : PStmt P} (hc : BRunS F c σS evs (.normal σS1))
    (hf : Trace.AssumptionsHold P evalInterp () evs) (h : BReach F out σS1 tr) :
    ∃ tr0, BReach F (c :: out) σS (tr0 ++ tr) ∧ Trace.AssumptionsHold P evalInterp () tr0 :=
  ⟨evs, .later hc h, hf⟩

/-- A reach of a list headed by a command, claiming a failure at an occurrence of condition `cond`,
    runs the command, whose events claim it, or are feasible and followed by a reach of the rest
    claiming it. -/
theorem reach_cmd_claim {σ : SemanticStore P} {t : AssertId P} {tr : List (Event P)}
    {cond : P.Expr} {c : Cmd P} {rest : PStmts P} (h : BReach F (.cmd (.cmd c) :: rest) σ tr)
    (hC : Claim t cond tr) : ∃ σ1 evs, EvalE F σ (.cmd c) σ1 evs ∧ (Claim t cond evs ∨
      ∃ tr', BReach F rest σ1 tr' ∧ Trace.AssumptionsHold P evalInterp () evs ∧
        Claim t cond tr') := by
  rcases h with ⟨⟨hE, -⟩⟩ | @⟨_, _, _, _, _, tr', ⟨hE⟩, hR⟩
  · exact ⟨_, _, hE, .inl hC⟩
  · by_cases hb : tr' = []
    · exact ⟨_, _, hE, .inl (by simpa [hb] using hC)⟩
    · exact ⟨_, _, hE, .inr ⟨_, hR, claim_split hb hC⟩⟩

omit [HasFvar P] in
/-- A condition holds under evaluation to `true` exactly when it evaluates to `true`. -/
theorem evalInterp_holds_iff {w : (evalInterp (P := P)).World} {a : EventArg P} :
    evalInterp.holds w a ↔ EvalsTo a.factory a.store a.expr (HasBool.ttVal a.factory) := .rfl

omit [HasFvar P] in
/-- An assertion (a cover) in the store `σS` with the label and metadata of a failing
    occurrence of the target `t` with the condition `e` in the store `σL`, and a condition `e'`
    evaluating to the values of `e`, is a failing occurrence of `t` with the condition `e'`. -/
theorem failsAt_transfer {σS σL : SemanticStore P} {l : String} {md : MetaData P}
    {E : EventArg P → Event P} (hE : E = .assert ∨ E = .cover)
    {t : AssertId P} {e e' : P.Expr} (h : ∀ v, EvalsTo F σS e' v ↔ EvalsTo F σL e v)
    (hf : FailsAt t e (E { factory := F, store := σL, label := l, expr := e, metadata := md })) :
    FailsAt t e' (E { factory := F, store := σS, label := l, expr := e', metadata := md }) := by
  rcases hE with rfl | rfl <;> exact ⟨hf.1, hf.2.1, rfl, (h _).2 hf.2.2.2⟩

end Claims

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
  | _, _, _, _, .exit | _, _, _, _, .typeDecl | _, _, _, _, .loop_exit _ => nofun
  | _, _, _, _, .loop_iter _ h1 h2 => fun ev hev y hy =>
    (List.mem_append.1 hev).elim
      (fun hev => by simp [Stmt.idents, brun_fv h1 ev hev y hy])
      fun hev => brunS_fv h2 ev hev y hy
  | _, _, _, _, .loop_break _ h => fun ev hev y hy => by
    simp [Stmt.idents, brun_fv h ev hev y hy]
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
  | _, _, _, .cmd (c := .cmd _) h _ => evalE_fv h
  | _, _, _, .cmd (c := .call _ _ _) h _ => h.elim
  | _, _, _, .ite_true _ h | _, _, _, .ite_nondet_true h | _, _, _, .ite_false _ h
  | _, _, _, .ite_nondet_false h => fun ev hev y hy => by
    simp [Stmt.idents, breach_fv h ev hev y hy, ExprOrNondet.getVars_det,
      ExprOrNondet.getVars_nondet, getFvars_mem_exprFV]
  | _, _, _, .block h => breach_fv h
  | _, _, _, .loop_here _ h => fun ev hev y hy => by
    simp [Stmt.idents, breach_fv h ev hev y hy]
  | _, _, _, .loop_later _ h1 h2 => fun ev hev y hy =>
    (List.mem_append.1 hev).elim
      (fun hev => by simp [Stmt.idents, brun_fv h1 ev hev y hy])
      fun hev => breachS_fv h2 ev hev y hy
end

/-- The condition of a failing occurrence a list reaches reads only identifiers of the list. -/
theorem fails_fv {ss : PStmts P} {σ : SemanticStore P} {t : AssertId P} {e : P.Expr}
    (h : Fails F ss σ t e) : ∀ y ∈ exprFV e, y ∈ Block.idents ss := by
  obtain ⟨evs, ev, hb, -, hfe⟩ := h
  have he : ev.condition.expr = e := by
    cases ev <;> simp only [FailsAt] at hfe <;> exact hfe.2.2.1
  exact he ▸ breach_fv hb ev (List.mem_append_right _ (List.mem_singleton_self _))

end Idents

/-! ## The stores of a run

A run keeps every variable defined at its start defined (`brun_dom`), changes no variable it
does not modify (`brun_frame`), and keeps the values typed, each variable defined at its start
holding a value sharing a type with its initial one (`brun_typed`).  A statement ending normally
defines exactly the variables of its start and those it defines at top level
(`brunS_normal_isSome`).  A list exits only to labels it mentions (`brun_exit_label`). -/

section Stores
variable [HasFvars P] [LawfulHasVal P] {F : P.Factory}

/-- The variables of the store `σ'` share a type with their values in `σ`: every variable
    defined in both holds values of a common type. -/
@[expose] def TypeAgree (F : P.Factory) (σ σ' : SemanticStore P) : Prop :=
  ∀ x p v, σ x = some p → σ' x = some v → ∃ ty, HasVal.valueOfTy F p ty ∧ HasVal.valueOfTy F v ty

omit [HasFvar P] [HasFvars P] in
/-- A store of values agrees in type with itself. -/
theorem TypeAgree.refl {σ : SemanticStore P} (h : WellFormedStore σ F) : TypeAgree F σ σ := by
  intro x p v hp hv
  obtain ⟨ty, hty⟩ := LawfulHasVal.value_typed F p (h x p hp)
  exact ⟨ty, hty, by rw [hp] at hv; cases hv; exact hty⟩

omit [HasFvar P] [HasFvars P] in
/-- Type agreement composes through a store defining every variable of the first. -/
theorem TypeAgree.trans {σ₁ σ₂ σ₃ : SemanticStore P}
    (h₁ : TypeAgree F σ₁ σ₂) (h₂ : TypeAgree F σ₂ σ₃)
    (hdom : ∀ x, (σ₁ x).isSome → (σ₂ x).isSome) : TypeAgree F σ₁ σ₃ := by
  intro x p v hp hv
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (hdom x (by simp [hp]))
  obtain ⟨t₁, hp₁, hq₁⟩ := h₁ x p q hp hq
  obtain ⟨t₂, hq₂, hv₂⟩ := h₂ x q v hq hv
  exact ⟨t₁, hp₁, LawfulHasVal.valueOfTy_congr F q v t₁ t₂ hq₁ hq₂ hv₂⟩

omit [HasFvar P] [HasFvars P] [LawfulHasVal P] in
/-- Type agreement with a store carries over to its projection. -/
theorem TypeAgree.proj {σ σp σ' : SemanticStore P} (h : TypeAgree F σ σ') :
    TypeAgree F σ (projectStore σp σ') := by
  intro x p v hp hv
  simp only [projectStore] at hv
  split at hv
  · exact h x p v hp hv
  · cases hv

omit [HasFvar P] [HasFvars P] [LawfulHasVal P] in
/-- Leaving a scope keeps the store value-valued. -/
theorem WellFormedStore.proj {σp σ : SemanticStore P} (h : WellFormedStore σ F) :
    WellFormedStore (projectStore σp σ) F := by
  intro x v hv
  simp only [projectStore] at hv
  split at hv
  · exact h x v hv
  · cases hv

omit [HasBool P] [HasFvar P] [HasFvars P] in
/-- The store of a projected outcome is the projected store. -/
private theorem Outcome.proj_store (σp : SemanticStore P) (o : Outcome P) :
    (o.proj σp).store = projectStore σp o.store := by
  cases o <;> rfl

omit [HasBool P] [HasFvar P] [HasFvars P] in
/-- The store of the outcome of a block is the projected store. -/
private theorem Outcome.block_store (l : String) (σp : SemanticStore P) (o : Outcome P) :
    (o.block l σp).store = projectStore σp o.store := by
  cases o <;> simp only [Outcome.block] <;> (try split) <;> rfl

/-- What a run does to the store: it keeps the variables defined at its start defined, changes
    none of them outside `W`, defines no variable outside `D` that was not defined at its start,
    and keeps the store value-valued, its values typed in agreement with the start. -/
private structure RunStore (F : P.Factory) (W D : List P.Ident) (σ σ' : SemanticStore P) :
    Prop where
  dom : ∀ x, (σ x).isSome → (σ' x).isSome
  frame : ∀ x, (σ x).isSome → x ∉ W → σ' x = σ x
  sub : ∀ x, (σ' x).isSome → (σ x).isSome ∨ x ∈ D
  typed : WellFormedStore σ F → WellFormedStore σ' F ∧ TypeAgree F σ σ'

omit [HasFvar P] [HasFvars P] in
/-- A store runs to itself: `RunStore` is reflexive. -/
private theorem RunStore.refl (W D : List P.Ident) (σ : SemanticStore P) :
    RunStore F W D σ σ :=
  ⟨fun _ h => h, fun _ _ _ => rfl, fun _ h => .inl h, fun h => ⟨h, .refl h⟩⟩

omit [HasFvar P] [HasFvars P] [LawfulHasVal P] in
/-- `RunStore` holds for larger sets of written and defined variables. -/
private theorem RunStore.mono {W W' D D' : List P.Ident} {σ σ' : SemanticStore P}
    (h : RunStore F W D σ σ') (hW : ∀ x ∈ W, x ∈ W') (hD : ∀ x ∈ D, x ∈ D') :
    RunStore F W' D' σ σ' :=
  ⟨h.dom, fun x hx hn => h.frame x hx (fun hm => hn (hW x hm)),
    fun x hx => (h.sub x hx).imp_right (hD x), h.typed⟩

omit [HasFvar P] [HasFvars P] in
/-- `RunStore` composes over two consecutive runs. -/
private theorem RunStore.trans {W D : List P.Ident} {σ₁ σ₂ σ₃ : SemanticStore P}
    (h₁ : RunStore F W D σ₁ σ₂) (h₂ : RunStore F W D σ₂ σ₃) : RunStore F W D σ₁ σ₃ :=
  ⟨fun x hx => h₂.dom x (h₁.dom x hx),
    fun x hx hn => (h₂.frame x (h₁.dom x hx) hn).trans (h₁.frame x hx hn),
    fun x hx => (h₂.sub x hx).elim (h₁.sub x) .inr,
    fun h => ⟨(h₂.typed (h₁.typed h).1).1,
      (h₁.typed h).2.trans (h₂.typed (h₁.typed h).1).2 h₁.dom⟩⟩

omit [HasFvar P] [HasFvars P] [LawfulHasVal P] in
/-- Projecting the end store of a run on its start store keeps what the run did and defines
    nothing new. -/
private theorem RunStore.proj {W D : List P.Ident} {σ σ' : SemanticStore P}
    (h : RunStore F W D σ σ') : RunStore F W [] σ (projectStore σ σ') :=
  ⟨fun x hx => by simp [projectStore, hx, h.dom x hx],
    fun x hx hn => by simp [projectStore, hx, h.frame x hx hn],
    fun x hx => .inl (by simp only [projectStore] at hx; split at hx <;> simp_all),
    fun hT => ⟨WellFormedStore.proj (h.typed hT).1, (h.typed hT).2.proj⟩⟩

omit [HasFvar P] [HasFvars P] in
/-- Defining the undefined `x` as a typed value, changing no other variable, changes nothing
    (`RunStore` with no modified variables) and defines only `x`. -/
private theorem init_runStore {σ σ' : SemanticStore P} {x : P.Ident} {v : P.Val} {ty : P.Ty}
    (h0 : σ x = none) (h1 : σ' x = some v) (hfr : ∀ y, x ≠ y → σ' y = σ y)
    (hty : HasVal.valueOfTy F v ty) : RunStore F [] [x] σ σ' := by
  have hne : ∀ y, (σ y).isSome → x ≠ y := fun y hy hxy => by simp_all
  refine ⟨fun y hy => by rw [hfr y (hne y hy)]; exact hy, fun y hy _ => hfr y (hne y hy),
    fun y hy => ?_, fun hT => ⟨fun y w hw => ?_, fun y p w hp hw => ?_⟩⟩
  · by_cases hxy : x = y
    · exact .inr (by simp [hxy])
    · exact .inl (by rwa [hfr y hxy] at hy)
  · by_cases hxy : x = y
    · subst hxy; rw [h1] at hw; cases hw; exact LawfulHasVal.valueOfTy_isVal F _ ty hty
    · rw [hfr y hxy] at hw; exact hT y w hw
  · have hxy := hne y (by simp [hp])
    rw [hfr y hxy, hp] at hw
    cases hw
    obtain ⟨t, ht⟩ := LawfulHasVal.value_typed F p (hT y p hp)
    exact ⟨t, ht, ht⟩

omit [HasFvar P] [HasFvars P] in
/-- `RunStore` for updating the defined `x` to a value sharing a type with its old one. -/
private theorem update_runStore {σ σ' : SemanticStore P} {x : P.Ident} {v : P.Val}
    (hup : UpdateState P σ x v σ') (hst : HasVal.valueOfStoredTy (P := P) F σ x v) :
    RunStore F [x] [] σ σ' := by
  obtain ⟨h0, h1, hfr⟩ := hup
  obtain ⟨prev, ty, hprev, hpty, hvty⟩ := hst
  refine ⟨fun y hy => ?_, fun y _ hn => hfr y (fun h => hn (by simp [h])), fun y hy => ?_,
    fun hT => ⟨fun y w hw => ?_, fun y p w hp hw => ?_⟩⟩
  · by_cases hxy : x = y
    · subst hxy; simp [h1]
    · rw [hfr y hxy]; exact hy
  · by_cases hxy : x = y
    · subst hxy; exact .inl (by simp [h0])
    · exact .inl (by rwa [hfr y hxy] at hy)
  · by_cases hxy : x = y
    · subst hxy; rw [h1] at hw; cases hw; exact LawfulHasVal.valueOfTy_isVal F _ ty hvty
    · rw [hfr y hxy] at hw; exact hT y w hw
  · by_cases hxy : x = y
    · subst hxy; rw [h1] at hw; rw [hprev] at hp; cases hw; cases hp; exact ⟨ty, hpty, hvty⟩
    · rw [hfr y hxy, hp] at hw
      cases hw
      obtain ⟨t, ht⟩ := LawfulHasVal.value_typed F p (hT y p hp)
      exact ⟨t, ht, ht⟩

omit [HasFvars P] in
/-- A command step changes only the variables the command modifies and defines only those it
    defines (`RunStore`). -/
private theorem evalE_runStore {c : CmdExt P} {σ σ' : SemanticStore P} {evs : List (Event P)}
    (h : EvalE F σ c σ' evs) :
    RunStore F (CmdExt.modifiedVars c) (CmdExt.definedVars c) σ σ' := by
  cases c with
  | call => exact h.elim
  | cmd c =>
    change EvalCmdE P F σ c σ' evs at h
    cases h with
    | eval_assert | eval_assume | eval_cover => exact .refl _ _ _
    | eval_init _ hinit hty _ | eval_init_unconstrained hinit hty _ =>
      obtain ⟨h0, h1, hfr⟩ := hinit
      exact (init_runStore h0 h1 hfr hty).mono (by simp)
        (by simp [CmdExt.definedVars, Cmd.definedVars])
    | eval_set _ hup hst _ | eval_set_nondet hup hst _ =>
      exact (update_runStore hup hst).mono
        (by simp [CmdExt.modifiedVars, Cmd.modifiedVars]) (by simp)

omit [HasFvars P] [LawfulHasVal P] in
/-- A command step defines the variables it defines. -/
private theorem evalE_defined {c : CmdExt P} {σ σ' : SemanticStore P} {evs : List (Event P)}
    (h : EvalE F σ c σ' evs) : ∀ x ∈ CmdExt.definedVars c, (σ' x).isSome := by
  cases c with
  | call => exact h.elim
  | cmd c =>
    change EvalCmdE P F σ c σ' evs at h
    cases h with
    | eval_init _ hinit _ _ | eval_init_unconstrained hinit _ _ =>
      obtain ⟨_, h1, _⟩ := hinit
      intro x hx
      simp only [CmdExt.definedVars, Cmd.definedVars, List.mem_singleton] at hx
      simp [hx, h1]
    | _ => simp [CmdExt.definedVars, Cmd.definedVars]

mutual
/-- A run of a list changes only the variables the list modifies and defines only those it
    defines at any depth (`RunStore`). -/
private theorem brun_runStore : ∀ {ss : PStmts P} {σ : SemanticStore P}
    {evs : List (Event P)} {o : Outcome P}, BRun F ss σ evs o →
    RunStore F (Block.modifiedVars ss) (Block.definedVars ss true) σ o.store
  | _, _, _, _, .nil => .refl _ _ _
  | _, _, _, _, .cons_normal h1 h2 =>
    ((brunS_runStore h1).mono (fun _ hx => by simp [Block.modifiedVars, hx])
        (fun _ hx => by simp [Block.definedVars, hx])).trans
      ((brun_runStore h2).mono (fun _ hx => by simp [Block.modifiedVars, hx])
        (fun _ hx => by simp [Block.definedVars, hx]))
  | _, _, _, _, .cons_exit h1 =>
    (brunS_runStore h1).mono (fun _ hx => by simp [Block.modifiedVars, hx])
      (fun _ hx => by simp [Block.definedVars, hx])
/-- A run of a statement changes only the variables the statement modifies and defines only
    those it defines at any depth (`RunStore`). -/
private theorem brunS_runStore : ∀ {s : PStmt P} {σ : SemanticStore P}
    {evs : List (Event P)} {o : Outcome P}, BRunS F s σ evs o →
    RunStore F (Stmt.modifiedVars s) (Stmt.definedVars s true) σ o.store
  | _, _, _, _, .cmd h => evalE_runStore h
  | _, _, _, _, .ite_true _ h | _, _, _, _, .ite_nondet_true h => by
    rw [Outcome.proj_store]
    exact (brun_runStore h).proj.mono (fun _ hx => by simp [Stmt.modifiedVars, hx]) (by simp)
  | _, _, _, _, .ite_false _ h | _, _, _, _, .ite_nondet_false h => by
    rw [Outcome.proj_store]
    exact (brun_runStore h).proj.mono (fun _ hx => by simp [Stmt.modifiedVars, hx]) (by simp)
  | _, _, _, _, .block h => by
    rw [Outcome.block_store]
    exact (brun_runStore h).proj.mono (fun _ hx => by simp [Stmt.modifiedVars, hx]) (by simp)
  | _, _, _, _, .exit | _, _, _, _, .typeDecl | _, _, _, _, .loop_exit _ => .refl _ _ _
  | _, _, _, _, .loop_iter _ h1 h2 =>
    ((brun_runStore h1).proj.mono (fun _ hx => by simp [Stmt.modifiedVars, hx])
      (by simp)).trans (brunS_runStore h2)
  | _, _, _, _, .loop_break _ h =>
    (brun_runStore h).proj.mono (fun _ hx => by simp [Stmt.modifiedVars, hx]) (by simp)
end

/-- A run defines only the variables of its start and those the list defines at any depth. -/
theorem brun_sub {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P} (h : BRun F ss σ evs o) :
    ∀ x, (o.store x).isSome → (σ x).isSome ∨ x ∈ Block.definedVars ss true :=
  (brun_runStore h).sub

/-- A run keeps every variable defined at its start defined. -/
theorem brun_dom {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P} (h : BRun F ss σ evs o) : ∀ x, (σ x).isSome → (o.store x).isSome :=
  (brun_runStore h).dom

/-- A run changes no variable defined at its start that the list does not modify. -/
theorem brun_frame {ss : PStmts P} {σ : SemanticStore P}
    {evs : List (Event P)} {o : Outcome P} (h : BRun F ss σ evs o) :
    ∀ x, (σ x).isSome → x ∉ Block.modifiedVars ss → o.store x = σ x :=
  (brun_runStore h).frame

/-- A run from a value-valued store ends in one, each variable defined at the start holding a
    value sharing a type with its initial one. -/
theorem brun_typed {ss : PStmts P} {σ : SemanticStore P}
    {evs : List (Event P)} {o : Outcome P} (h : BRun F ss σ evs o) (hT : WellFormedStore σ F) :
    WellFormedStore o.store F ∧ TypeAgree F σ o.store :=
  (brun_runStore h).typed hT

/-- A statement run from a value-valued store ends in one, each variable defined at the start
    holding a value sharing a type with its initial one. -/
theorem brunS_typed {s : PStmt P} {σ : SemanticStore P}
    {evs : List (Event P)} {o : Outcome P} (h : BRunS F s σ evs o) (hT : WellFormedStore σ F) :
    WellFormedStore o.store F ∧ TypeAgree F σ o.store :=
  (brunS_runStore h).typed hT

/-- A statement ending normally defines exactly the variables of its start and those it defines
    at top level. -/
theorem brunS_normal_isSome {s : PStmt P} {σ σ' : SemanticStore P}
    {evs : List (Event P)} (h : BRunS F s σ evs (.normal σ')) :
    ∀ x, (σ' x).isSome = ((σ x).isSome || decide (x ∈ Stmt.definedVars s true)) := by
  have hR := brunS_runStore h
  intro x
  apply Bool.eq_iff_iff.2
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨hR.sub x, fun hx => hx.elim (hR.dom x) fun hd => ?_⟩
  cases s with
  | cmd c =>
    cases h with
    | cmd hE => exact evalE_defined hE x hd
  | _ => simp [Stmt.definedVars] at hd

omit [HasFvars P] [LawfulHasVal P] in
mutual
/-- A list exits only to a label one of its `exit`s targets. -/
theorem brun_exit_label : ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P}, BRun F ss σ evs o → ∀ l σ', o = .exit l σ' → l ∈ Block.labels ss
  | _, _, _, _, .nil, _, _, h => by cases h
  | _, _, _, _, .cons_normal _ h2, l, σ', h => by
    simp [Block.labels, brun_exit_label h2 l σ' h]
  | _, _, _, _, .cons_exit h1, l, σ', h => by
    simp [Block.labels, brunS_exit_label h1 l σ' h]
/-- A statement exits only to a label one of its `exit`s targets. -/
theorem brunS_exit_label : ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P}, BRunS F s σ evs o → ∀ l σ', o = .exit l σ' → l ∈ Stmt.labels s
  | _, _, _, _, .cmd _, _, _, h => by cases h
  | _, _, _, _, .ite_true (o := o') _ h, l, σ', ho
  | _, _, _, _, .ite_nondet_true (o := o') h, l, σ', ho => by
    have ih := brun_exit_label h
    cases o' with
    | normal => cases ho
    | exit l' σ'' =>
      simp only [Outcome.proj, Outcome.exit.injEq] at ho
      obtain ⟨rfl, -⟩ := ho
      exact List.mem_append_left _ (ih _ _ rfl)
  | _, _, _, _, .ite_false (o := o') _ h, l, σ', ho
  | _, _, _, _, .ite_nondet_false (o := o') h, l, σ', ho => by
    have ih := brun_exit_label h
    cases o' with
    | normal => cases ho
    | exit l' σ'' =>
      simp only [Outcome.proj, Outcome.exit.injEq] at ho
      obtain ⟨rfl, -⟩ := ho
      exact List.mem_append_right _ (ih _ _ rfl)
  | _, _, _, _, .block (o := o') h, l, σ', ho => by
    have ih := brun_exit_label h
    cases o' with
    | normal => cases ho
    | exit l' σ'' =>
      simp only [Outcome.block] at ho
      split at ho
      · cases ho
      · simp only [Outcome.exit.injEq] at ho
        obtain ⟨rfl, -⟩ := ho
        exact ih _ _ rfl
  | _, _, _, _, .exit, l, σ', h => by
    simp only [Outcome.exit.injEq] at h
    simp [Stmt.labels, h.1]
  | _, _, _, _, .typeDecl, _, _, h | _, _, _, _, .loop_exit _, _, _, h => by cases h
  | _, _, _, _, .loop_iter _ _ h2, l, σ', h => brunS_exit_label h2 l σ' h
  | _, _, _, _, .loop_break _ h, l, σ', ho => by
    have ih := brun_exit_label h
    simp only [Outcome.exit.injEq] at ho
    obtain ⟨rfl, -⟩ := ho
    exact ih _ _ rfl
end

omit [HasFvars P] [LawfulHasVal P] in
mutual
/-- A list whose `exit`s are caught by its blocks or by blocks labelled `labels` exits only to
    a label of `labels`. -/
theorem brun_exit_covered : ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P}, BRun F ss σ evs o → ∀ {labels : List String},
    Block.exitsCoveredByBlocks labels ss → ∀ l σ', o = .exit l σ' → l ∈ labels
  | _, _, _, _, .nil, _, _, _, _, h => by cases h
  | _, _, _, _, .cons_normal _ h2, _, hc, l, σ', h => brun_exit_covered h2 hc.2 l σ' h
  | _, _, _, _, .cons_exit h1, _, hc, l, σ', h => brunS_exit_covered h1 hc.1 l σ' h
/-- A statement whose `exit`s are caught by its blocks or by blocks labelled `labels` exits only
    to a label of `labels`. -/
theorem brunS_exit_covered : ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P}, BRunS F s σ evs o → ∀ {labels : List String},
    Stmt.exitsCoveredByBlocks labels s → ∀ l σ', o = .exit l σ' → l ∈ labels
  | _, _, _, _, .cmd _, _, _, _, _, h => by cases h
  | _, _, _, _, .ite_true (o := o') _ h, _, hc, l, σ', ho
  | _, _, _, _, .ite_nondet_true (o := o') h, _, hc, l, σ', ho => by
    have ih := brun_exit_covered h hc.1
    cases o' with
    | normal => cases ho
    | exit l' σ'' =>
      simp only [Outcome.proj, Outcome.exit.injEq] at ho
      obtain ⟨rfl, -⟩ := ho
      exact ih _ _ rfl
  | _, _, _, _, .ite_false (o := o') _ h, _, hc, l, σ', ho
  | _, _, _, _, .ite_nondet_false (o := o') h, _, hc, l, σ', ho => by
    have ih := brun_exit_covered h hc.2
    cases o' with
    | normal => cases ho
    | exit l' σ'' =>
      simp only [Outcome.proj, Outcome.exit.injEq] at ho
      obtain ⟨rfl, -⟩ := ho
      exact ih _ _ rfl
  | _, _, _, _, .block (l := lb) (o := o') h, _, hc, l, σ', ho => by
    have ih := brun_exit_covered h hc
    cases o' with
    | normal => cases ho
    | exit l' σ'' =>
      simp only [Outcome.block] at ho
      split at ho
      · cases ho
      · rename_i hne
        simp only [Outcome.exit.injEq] at ho
        obtain ⟨rfl, -⟩ := ho
        exact (List.mem_cons.1 (ih _ _ rfl)).resolve_left hne
  | _, _, _, _, .exit, _, hc, l, σ', h => by
    simp only [Outcome.exit.injEq] at h
    exact h.1 ▸ hc
  | _, _, _, _, .typeDecl, _, _, _, _, h | _, _, _, _, .loop_exit _, _, _, _, _, h => by cases h
  | _, _, _, _, .loop_iter _ _ h2, _, hc, l, σ', h => brunS_exit_covered h2 hc l σ' h
  | _, _, _, _, .loop_break _ h, _, hc, l, σ', ho => by
    have ih := brun_exit_covered h hc
    simp only [Outcome.exit.injEq] at ho
    obtain ⟨rfl, -⟩ := ho
    exact ih _ _ rfl
end

end Stores

end -- public section

end BigStep

/-! ## Counterparts under evaluation to `true` -/

public section

namespace Event.WeakensAssume

variable {P : PureExpr} [HasBool P] {F : P.Factory} {σS σL : SemanticStore P} {l : String}
  {md : MetaData P}

/-- An assumption in the store `σS` whose condition evaluates to `true` whenever the
    assumption's in the store `σL` does is its counterpart under evaluation to `true`. -/
theorem assume {a a' : P.Expr}
    (h : EvalsTo F σL a (HasBool.ttVal F) → EvalsTo F σS a' (HasBool.ttVal F)) :
    Event.WeakensAssume BigStep.evalInterp
      (.assume { factory := F, store := σL, label := l, expr := a, metadata := md })
      (.assume { factory := F, store := σS, label := l, expr := a', metadata := md }) :=
  ⟨rfl, rfl, fun _ => h⟩

/-- An assertion (a cover) in the store `σS` whose condition evaluates to the values of the
    one's in the store `σL` is its counterpart under evaluation to `true`. -/
theorem check {E : EventArg P → Event P} (hE : E = .assert ∨ E = .cover) {e e' : P.Expr}
    (h : ∀ v, EvalsTo F σS e' v ↔ EvalsTo F σL e v) :
    Event.WeakensAssume BigStep.evalInterp
      (E { factory := F, store := σL, label := l, expr := e, metadata := md })
      (E { factory := F, store := σS, label := l, expr := e', metadata := md }) := by
  rcases hE with rfl | rfl <;> exact ⟨rfl, rfl, fun _ => (h _).symm⟩

end Event.WeakensAssume

end -- public section

end Imperative
