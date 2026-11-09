/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BigStep.Sem
public import Strata.DL.Imperative.Logic.TraceRelations
public import Strata.DL.Imperative.CmdProps
import Strata.DL.Imperative.Logic.TraceInterpProps

/-! # Properties of the big-step semantics of loop-free and obligation programs

Inversions of the command semantics `EvalE` for `init`, `set`, `assume`, `assert` and `cover`,
and the effect of a store update; sequencing of runs and reaches (`brun_append`,
`breach_append_run`, `breach_cmd_cons`) and failures as reaches whose events claim them
(`fails_iff_claim`); claims of a failure along `++` (`claim_prepend`, `claim_split`), on one
event (`claim_single`), on no event (`Claim.not_nil`) and after a command (`reach_cmd_claim`),
and reaches after a run or a statement (`reach_after_run`, `reach_after_stmt`); evaluation to
`true` (`evalInterp_holds_iff`) and a failing check carried over to a condition with the same
values (`failsAt_transfer`); and
the conditions of the events of a run, a reach or a failure read only identifiers of the list
(`brun_fv`, `breach_fv`, `fails_fv`). Under evaluation to `true`, an assumption or a check is
the counterpart (`Event.WeakensAssume`) of one with the same label whose condition evaluates as
required (`Event.WeakensAssume.assume`, `Event.WeakensAssume.check`).

Key theorems: `evalE_init_det_inv`, `evalE_init_nondet_inv`, `evalE_set_det_inv`,
`evalE_set_nondet_inv`, `evalE_assume_inv`, `evalE_assert_inv`, `evalE_cover_inv`,
`update_facts`, `evalInterp_stableUnder` (evaluation to `true` is stable under the shared
semantic event relation `EventArg.WithWF`), `brun_append`, `breach_append_run`,
`fails_iff_claim`, `claim_prepend`, `claim_split`, `reach_cmd_claim`, `failsAt_transfer`,
`brun_fv`, `breach_fv`, `fails_fv`, `Event.WeakensAssume.assume`,
`Event.WeakensAssume.check`. -/

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

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvars P] in
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

/-- A list fails the target `t` with the condition `e` exactly when a reach of it emits events
    that claim a failure of `t` with the condition `e`. -/
theorem fails_iff_claim {ss : PStmts P} {σ : SemanticStore P} {t : AssertId P} {e : P.Expr} :
    Fails F ss σ t e ↔ ∃ tr, BReach F ss σ tr ∧ Claim t e tr :=
  ⟨fun ⟨evs, ev, hb, hA, hf⟩ => ⟨_, hb, evs, ev, rfl, hA, hf⟩,
    fun ⟨_, hb, evs, ev, he, hA, hf⟩ => ⟨evs, ev, he ▸ hb, hA, hf⟩⟩

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
  rcases h with ⟨⟨hE⟩⟩ | @⟨_, _, _, _, _, tr', ⟨hE⟩, hR⟩
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

/-- The condition of a failing occurrence a list reaches reads only identifiers of the list. -/
theorem fails_fv {ss : PStmts P} {σ : SemanticStore P} {t : AssertId P} {e : P.Expr}
    (h : Fails F ss σ t e) : ∀ y ∈ exprFV e, y ∈ Block.idents ss := by
  obtain ⟨evs, ev, hb, -, hfe⟩ := h
  have he : ev.condition.expr = e := by
    cases ev <;> simp only [FailsAt] at hfe <;> exact hfe.2.2.1
  exact he ▸ breach_fv hb ev (List.mem_append_right _ (List.mem_singleton_self _))

end Idents

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
