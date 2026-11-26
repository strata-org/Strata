/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.BetaReduceTyping
public import Strata.Transform.GuardFwdCoreCorrect
public import Strata.Transform.Passive.WellTyped
import all Strata.Transform.BetaReduce
import all Strata.Transform.BetaReduceProps
import all Strata.Transform.BetaReduceTyping
import all Strata.Transform.DefInlineCorrect
import Strata.DL.Lambda.LExprDenoteBeta
import Strata.DL.Imperative.CmdSemanticsProps
import Strata.Transform.DeadDefElimProps

/-! # Beta reduction over-approximates (Core)

Contracting the redexes of a Core expression keeps its value wherever it has one
(`reduceExpr_eval`, from `Lambda.LExpr.denoteEval_betaReduceRedexesWith`): the contraction keeps
the Lean denotation of every typed expression.  An expression without a value may get one (`(λ x
: int. 5) true` has none, `5` has one), so the assertions and covers whose conditions must keep
their values exactly are those whose conditions are typed Boolean expressions
(`Block.condsTyped Expression.Typed`), which have a value in every store that conforms to the
types their annotations give their free variables (`Core.eval_of_typed`).

On a list in passive form whose conditions are typed in this way, beta reduction is a trace
over-approximation in the general form `OverapproximatesTracesUptoWhen`
(`betaReduce_overapproximatesTraces`): equal initial environments, traces related by
`Trace.WeakensAssumes evalInterp` (each assertion and cover holds exactly when the source's does,
each assumption holds whenever the source's does), equal final environments, and the output
satisfies the gate wherever the input does.  A run of the input from a store conforming to a
typing its annotations agree with is replayed on the output (`betaReduce_run_rel`,
`betaReduce_reach_rel`), event by event (`Imperative.GuardFwd.GFEvRel`).  Beta reduction keeps
the passive form and the typing of the conditions (`betaReduceBlock_passive`,
`betaReduceBlock_condsTyped`).

Key theorems: `reduceExpr_eval`, `betaReduce_run_rel`, `betaReduce_reach_rel`,
`blockInitEnvWF_betaReduce`, `betaReduce_overapproximatesTraces`, `betaReduceBlock_passive`,
`betaReduceBlock_condsTyped`, `betaReduceBlock_initsTyped`. -/

namespace Core
namespace BetaReduce

open Imperative Imperative.BigStep Imperative.GuardFwd Imperative.Specification
  Imperative.Specification.Transform Core.Logic Lambda Core.DeadDefElim

public section

/-- **Contracting the redexes keeps the value of a Core expression** wherever it has one. -/
theorem reduceExpr_eval {F : Expression.Factory} {σ : SemanticStore Expression}
    {e : Expression.Expr} {v : Expression.Val} (h : Expression.eval F σ e = some v) :
    Expression.eval F σ (LExpr.betaReduceRedexesWith LExpr.mergeMetadataForSubst e) = some v :=
  LExpr.denoteEval_betaReduceRedexesWith _ h

/-- **A typed condition keeps its value exactly**: a condition typed Boolean
    (`Expression.Typed`) whose annotated free variables `Γ` types, in a store conforming to `Γ`,
    has a value, which its contraction keeps. -/
private theorem reduceExpr_eval_typed {F : Expression.Factory} {σ : SemanticStore Expression}
    {Γ : VarTyping Expression} {e : Expression.Expr} (hσ : StoreHasTyping F σ Γ)
    (ha : Γ.annotates (HasFvars.getTypedFvars (P := Expression) e))
    (he : Expression.Typed e HasBool.boolTy) :
    Expression.eval F σ (LExpr.betaReduceRedexesWith LExpr.mergeMetadataForSubst e) =
      Expression.eval F σ e := by
  obtain ⟨v, hv, -⟩ := eval_of_typed F σ he fun x τ hx =>
    hσ x _ (ha x _ (List.mem_filterMap.2 ⟨(x, some τ), hx, rfl⟩))
  rw [reduceExpr_eval hv, hv]

mutual
/-- **A run of a list, replayed on its beta reduction.**  A run of a list in passive form whose
    conditions are typed, from a store conforming to a typing `Γ` the annotations of the list
    agree with, has a run of `reduceBlock ss` from the same store with the same outcome and
    corresponding events. -/
private theorem br_run {F : Expression.Factory} :
    ∀ {ss : Statements} {σ : SemanticStore Expression} {evs : List (Event Expression)}
      {o : Outcome Expression}, BRun F ss σ evs o → ∀ {Γ : VarTyping Expression},
    Block.passiveForm ss = true → Block.condsTyped Expression.Typed ss →
    StoreHasTyping F σ Γ → Block.fvarTypesWellAnnotated Γ ss →
    ∃ evs', BRun F (reduceBlock ss) σ evs' o ∧ List.Rel₂ GFEvRel evs evs'
  | _, _, _, _, .nil, _, _, _, _, _ => ⟨[], by rw [reduceBlock]; exact .nil, .nil⟩
  | _, _, _, _, .cons_normal h1 h2, _, hp, hc, hΓ, hA => by
    obtain ⟨evs1, h1', hr1, hpost⟩ := br_runS h1 (passive_cons hp).1 hc.1 hΓ hA.1
    obtain ⟨evs2, h2', hr2⟩ := br_run h2 (passive_cons hp).2 hc.2 (hpost _ rfl) hA.2
    exact ⟨evs1 ++ evs2, by rw [reduceBlock]; exact .cons_normal h1' h2', hr1.append hr2⟩
  | _, _, _, _, .cons_exit h1, _, hp, hc, hΓ, hA => by
    obtain ⟨evs1, h1', hr1, -⟩ := br_runS h1 (passive_cons hp).1 hc.1 hΓ hA.1
    exact ⟨evs1, by rw [reduceBlock]; exact .cons_exit h1', hr1⟩
/-- **A run of a statement, replayed on its beta reduction**: `br_run` for one statement, and
    the store after it conforms to `Γ` extended by the statement's definitions. -/
private theorem br_runS {F : Expression.Factory} :
    ∀ {s : Statement} {σ : SemanticStore Expression} {evs : List (Event Expression)}
      {o : Outcome Expression}, BRunS F s σ evs o → ∀ {Γ : VarTyping Expression},
    Block.passiveForm [s] = true → Stmt.condsTyped Expression.Typed s →
    StoreHasTyping F σ Γ → Stmt.fvarTypesWellAnnotated Γ s →
    ∃ evs', BRunS F (reduceStmt s) σ evs' o ∧ List.Rel₂ GFEvRel evs evs' ∧
      ∀ σ', o = .normal σ' → StoreHasTyping F σ' (Γ.extend (Stmt.typedDefinedVars s))
  | _, _, _, _, .cmd (c := .cmd (.init x ty (.det e) md)) h, _, _, _, hΓ, _ => by
    obtain ⟨v, hev, h0, h1, hfr, rfl, hty⟩ := EvalCmdE.init_det_inv h
    simp only [reduceStmt, Command.mapExpr]
    refine ⟨[], .cmd (evalE_init_replay h ((reduceExpr_eval hev).trans hev.symm)), .nil,
      fun σ' ho => ?_⟩
    cases ho
    exact Imperative.DefInline.storeHasTyping_init hΓ h1 hfr hty
  | _, _, _, _, .cmd (c := .cmd (.init x ty .nondet md)) h, _, _, _, hΓ, _ => by
    obtain ⟨v, hty, h0, h1, hfr, rfl⟩ := EvalCmdE.init_nondet_inv h
    simp only [reduceStmt, Command.mapExpr]
    refine ⟨[], .cmd h, .nil, fun σ' ho => ?_⟩
    cases ho
    exact Imperative.DefInline.storeHasTyping_init hΓ h1 hfr hty
  | _, _, _, _, .cmd (c := .cmd (.set _ _ _)) _, _, hp, _, _, _ => by
    simp [Block.passiveForm] at hp
  | _, _, _, _, .cmd (c := .cmd (.assume l e md)) h, _, _, _, hΓ, _ => by
    obtain ⟨rfl, rfl⟩ := EvalCmdE.assume_inv h
    simp only [reduceStmt, Command.mapExpr]
    exact ⟨_, .cmd .eval_assume, .cons ⟨rfl, rfl, rfl, rfl, reduceExpr_eval⟩ .nil,
      fun σ' ho => by cases ho; exact hΓ⟩
  | _, _, _, _, .cmd (c := .cmd (.assert l e md)) h, _, _, hc, hΓ, hA => by
    obtain ⟨rfl, rfl⟩ := EvalCmdE.assert_inv h
    simp only [reduceStmt, Command.mapExpr]
    exact ⟨_, .cmd .eval_assert, .cons ⟨rfl, rfl, rfl, rfl, reduceExpr_eval_typed hΓ hA hc⟩ .nil,
      fun σ' ho => by cases ho; exact hΓ⟩
  | _, _, _, _, .cmd (c := .cmd (.cover l e md)) h, _, _, hc, hΓ, hA => by
    obtain ⟨rfl, rfl⟩ := EvalCmdE.cover_inv h
    simp only [reduceStmt, Command.mapExpr]
    exact ⟨_, .cmd .eval_cover, .cons ⟨rfl, rfl, rfl, rfl, reduceExpr_eval_typed hΓ hA hc⟩ .nil,
      fun σ' ho => by cases ho; exact hΓ⟩
  | _, _, _, _, .cmd (c := .call _ _ _ _) h, _, _, _, _, _ => h.elim
  | _, _, _, _, .ite_true _ _, _, hp, _, _, _
  | _, _, _, _, .ite_false _ _, _, hp, _, _, _ => by simp [Block.passiveForm] at hp
  | _, σ, _, _, .ite_nondet_true h, _, hp, hc, hΓ, hA => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨evs', h', hr⟩ := br_run h hp.1.1 hc.1 hΓ hA.2.1
    refine ⟨evs', by rw [reduceStmt]; exact .ite_nondet_true h', hr, fun σ' ho => ?_⟩
    obtain ⟨σ1, rfl, hk⟩ := passive_run h hp.1.1
    obtain rfl : σ' = σ := by
      cases ho
      exact funext fun x => by by_cases hx : (σ x).isSome <;> simp_all [projectStore]
    exact hΓ
  | _, σ, _, _, .ite_nondet_false h, _, hp, hc, hΓ, hA => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨evs', h', hr⟩ := br_run h hp.1.2 hc.2 hΓ hA.2.2
    refine ⟨evs', by rw [reduceStmt]; exact .ite_nondet_false h', hr, fun σ' ho => ?_⟩
    obtain ⟨σ1, rfl, hk⟩ := passive_run h hp.1.2
    obtain rfl : σ' = σ := by
      cases ho
      exact funext fun x => by by_cases hx : (σ x).isSome <;> simp_all [projectStore]
    exact hΓ
  | _, _, _, _, .block _, _, hp, _, _, _
  | _, _, _, _, .exit, _, hp, _, _, _
  | _, _, _, _, .typeDecl, _, hp, _, _, _
  | _, _, _, _, .loop_exit _, _, hp, _, _, _
  | _, _, _, _, .loop_iter _ _ _, _, hp, _, _, _
  | _, _, _, _, .loop_break _ _, _, hp, _, _, _ => by simp [Block.passiveForm] at hp
end


mutual
/-- **A reach of a list, replayed on its beta reduction**: a reach of a list in passive form
    whose conditions are typed, from a store conforming to a typing `Γ` the annotations of the
    list agree with, has a reach of `reduceBlock ss` from the same store with corresponding
    events. -/
private theorem br_reach {F : Expression.Factory} :
    ∀ {ss : Statements} {σ : SemanticStore Expression} {evs : List (Event Expression)},
    BReach F ss σ evs → ∀ {Γ : VarTyping Expression},
    Block.passiveForm ss = true → Block.condsTyped Expression.Typed ss →
    StoreHasTyping F σ Γ → Block.fvarTypesWellAnnotated Γ ss →
    ∃ evs', BReach F (reduceBlock ss) σ evs' ∧ List.Rel₂ GFEvRel evs evs'
  | _, _, _, .here h, _, hp, hc, hΓ, hA => by
    obtain ⟨evs', h', hr⟩ := br_reachS h (passive_cons hp).1 hc.1 hΓ hA.1
    exact ⟨evs', by rw [reduceBlock]; exact .here h', hr⟩
  | _, _, _, .later h1 h2, _, hp, hc, hΓ, hA => by
    obtain ⟨evs1, h1', hr1, hpost⟩ := br_runS h1 (passive_cons hp).1 hc.1 hΓ hA.1
    obtain ⟨evs2, h2', hr2⟩ := br_reach h2 (passive_cons hp).2 hc.2 (hpost _ rfl) hA.2
    exact ⟨evs1 ++ evs2, by rw [reduceBlock]; exact .later h1' h2', hr1.append hr2⟩
/-- **A reach of a statement, replayed on its beta reduction**: `br_reach` for one
    statement. -/
private theorem br_reachS {F : Expression.Factory} :
    ∀ {s : Statement} {σ : SemanticStore Expression} {evs : List (Event Expression)},
    BReachS F s σ evs → ∀ {Γ : VarTyping Expression},
    Block.passiveForm [s] = true → Stmt.condsTyped Expression.Typed s →
    StoreHasTyping F σ Γ → Stmt.fvarTypesWellAnnotated Γ s →
    ∃ evs', BReachS F (reduceStmt s) σ evs' ∧ List.Rel₂ GFEvRel evs evs'
  | _, _, _, .cmd (c := c) h hne, _, hp, hc, hΓ, hA => by
    obtain ⟨evs', h', hr, -⟩ := br_runS (.cmd h) hp hc hΓ hA
    have hne' : evs' ≠ [] := fun h0 => hne (by subst h0; cases hr; rfl)
    rw [reduceStmt] at h' ⊢
    cases h' with
    | cmd h' => exact ⟨evs', .cmd h' hne', hr⟩
  | _, _, _, .ite_true _ _, _, hp, _, _, _
  | _, _, _, .ite_false _ _, _, hp, _, _, _ => by simp [Block.passiveForm] at hp
  | _, _, _, .ite_nondet_true h, _, hp, hc, hΓ, hA => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨evs', h', hr⟩ := br_reach h hp.1.1 hc.1 hΓ hA.2.1
    exact ⟨evs', by rw [reduceStmt]; exact .ite_nondet_true h', hr⟩
  | _, _, _, .ite_nondet_false h, _, hp, hc, hΓ, hA => by
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    obtain ⟨evs', h', hr⟩ := br_reach h hp.1.2 hc.2 hΓ hA.2.2
    exact ⟨evs', by rw [reduceStmt]; exact .ite_nondet_false h', hr⟩
  | _, _, _, .block _, _, hp, _, _, _
  | _, _, _, .loop_here _ _, _, hp, _, _, _
  | _, _, _, .loop_later _ _ _, _, hp, _, _, _ => by simp [Block.passiveForm] at hp
end

/-- **A run of a list, and of its beta reduction.**  A run of a list in passive form whose
    conditions are typed Boolean expressions, from a store conforming to a typing `Γ` the
    annotations of the list agree with, has a run of `reduceBlock ss` from the same store with
    the same outcome and events corresponding one by one (`GFEvRel`). -/
theorem betaReduce_run_rel {F : Expression.Factory} {ss : Statements}
    {σ : SemanticStore Expression} {evs : List (Event Expression)} {o : Outcome Expression}
    {Γ : VarTyping Expression} (hp : Block.passiveForm ss = true)
    (hc : Block.condsTyped Expression.Typed ss) (hΓ : StoreHasTyping F σ Γ)
    (hA : Block.fvarTypesWellAnnotated Γ ss) (h : BRun F ss σ evs o) :
    ∃ evs', BRun F (betaReduceBlock ss) σ evs' o ∧ List.Rel₂ GFEvRel evs evs' :=
  br_run h hp hc hΓ hA

/-- **A reach of a list, and of its beta reduction**: `betaReduce_run_rel` for reaches. -/
theorem betaReduce_reach_rel {F : Expression.Factory} {ss : Statements}
    {σ : SemanticStore Expression} {evs : List (Event Expression)} {Γ : VarTyping Expression}
    (hp : Block.passiveForm ss = true) (hc : Block.condsTyped Expression.Typed ss)
    (hΓ : StoreHasTyping F σ Γ) (hA : Block.fvarTypesWellAnnotated Γ ss)
    (h : BReach F ss σ evs) :
    ∃ evs', BReach F (betaReduceBlock ss) σ evs' ∧ List.Rel₂ GFEvRel evs evs' :=
  br_reach h hp hc hΓ hA

/-- Beta reduction keeps the variables a list in passive form defines and the types its `init`s
    declare. -/
private theorem reduceBlock_shape (ss : Statements) (hp : Block.passiveForm ss = true) :
    (∀ b, Block.definedVars (reduceBlock ss) b = Block.definedVars ss b) ∧
      Block.initTypes (reduceBlock ss) = Block.initTypes ss := by
  induction ss using Block.passiveForm.induct <;> (try cases ‹ExprOrNondet Expression›) <;>
    simp_all [reduceBlock, reduceStmt, Command.mapExpr, Block.passiveForm, Block.initTypes,
      Stmt.initTypes, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars,
      HasInitTypesImp.initTypes, CmdExt.initTypes, Cmd.initTypes]

/-- **The output of beta reduction is well formed from every environment the input is**: on a
    list in passive form with typed `init`s, the gate `BlockInitEnvWF` of the input gives that of
    the output. -/
theorem blockInitEnvWF_betaReduce {params : InitEnvWFParams} {ss : Statements}
    {ρ : Imperative.Env Expression} (hp : Block.passiveForm ss = true)
    (hi : Block.initsTyped Expression.Typed ss) (h : BlockInitEnvWF params ss ρ) :
    BlockInitEnvWF params (betaReduceBlock ss) ρ := by
  obtain ⟨Γ, hσ, hw⟩ := h.fvarTypesOk
  obtain ⟨hdv, hit⟩ := reduceBlock_shape ss hp
  have hpo := reduceBlock_passive ss hp
  have hdu := reduceBlock_defUse _ _ ss h.defUseOk
  exact { h with
    exitsNotReserved := fun l hl => by simp [betaReduceBlock, Block.labels_of_passiveForm hpo] at hl
    measuresTyped := fun m hm => by simp [betaReduceBlock, Block.measures_of_passiveForm hpo] at hm
    readWritesDefined := fun n hn hnd =>
      Block.defined_of_mem_touchedVars (fun _ _ h => h) hdu hn hnd
    defsUndefined := fun n hn => h.defsUndefined n (hdv false ▸ hn)
    definedVarsNotReserved := fun n hn => h.definedVarsNotReserved n (hdv false ▸ hn)
    defUseOk := hdu
    initTypesInhabited := fun ty hty => h.initTypesInhabited ty (hit ▸ hty)
    fvarTypesOk := ⟨Γ, hσ, (reduceBlock_typed ss Γ hw hi).1⟩ }


/-- **Beta reduction keeps the passive form.** -/
theorem betaReduceBlock_passive {ss : Statements} (hp : Block.passiveForm ss = true) :
    Block.passiveForm (betaReduceBlock ss) = true :=
  reduceBlock_passive ss hp

/-- **Beta reduction keeps the `init`s typed** (`Core.Expression.Typed` at their declared types)
    of a list whose annotations agree with a typing. -/
theorem betaReduceBlock_initsTyped {ss : Statements} {Γ : VarTyping Expression}
    (hw : Block.fvarTypesWellAnnotated Γ ss) (hi : Block.initsTyped Expression.Typed ss) :
    Block.initsTyped Expression.Typed (betaReduceBlock ss) :=
  (reduceBlock_typed ss Γ hw hi).2

/-- **Beta reduction over-approximates the traces of a Core statement list.**  For a Core
    statement list `ss` in passive form (hence without loops and calls) whose `assume`, `assert`
    and `cover` conditions are typed Boolean expressions (`Block.condsTyped Expression.Typed`) and
    whose `init`s are typed (`Block.initsTyped Expression.Typed`), and every initial environment
    `ρ₀` satisfying `BlockInitEnvWF params ss`:
    * every finite trace of `ss` from `ρ₀` has a trace of `betaReduceBlock ss` from `ρ₀` whose
      assumptions are weakened (`Trace.WeakensAssumes evalInterp`: each assertion and cover
      keeps its label and metadata and holds exactly when the source's holds, each assumption
      keeps its label and metadata and holds whenever the source's holds);
    * every terminating or exiting run of `ss` from `ρ₀` has a run of `betaReduceBlock ss` from
      `ρ₀` ending in the same way, in the same final environment, with such a trace;
    * `betaReduceBlock ss` satisfies `BlockInitEnvWF params` at `ρ₀`. -/
theorem betaReduce_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) :
    OverapproximatesTracesUptoWhen (Trace.WeakensAssumes evalInterp) (· = ·) (· = ·)
      (EventLang.coreBlock π) (EventLang.coreBlock π) (fun ss => some (betaReduceBlock ss))
      (fun ss => Block.noLoops ss = true ∧ Statements.noCalls ss = true ∧
        Block.passiveForm ss = true ∧ Block.condsTyped Expression.Typed ss ∧
        Block.initsTyped Expression.Typed ss) params params := by
  intro ss st' hT ⟨hss, hnc, hp, hc, hi⟩ ρ₀ _ rfl hwf
  cases hT
  obtain ⟨σ₀, F⟩ := ρ₀
  have hWB := hwf.bool
  obtain ⟨Γ, hσ, hw⟩ := hwf.fvarTypesOk
  refine ⟨fun cfg trace h => ?_, fun ρ' trace h => ?_, fun l ρ' trace h => ?_,
    blockInitEnvWF_betaReduce hp hi hwf⟩
  all_goals have h' := star_evalE h hnc
  · rcases Classical.em (trace = []) with rfl | htr
    · exact ⟨_, [], .refl _, .nil⟩
    obtain ⟨evs', hb, hm⟩ := betaReduce_reach_rel hp hc hσ hw (star_breach h' htr)
    obtain ⟨cfg', hc⟩ := breach_star hWB hb
    exact ⟨cfg', evs', star_core π hc, GFEvRel.weakensAssumes hm⟩
  all_goals
    have hE := starE_preserves_factory h'
    obtain ⟨evs', hb, hm⟩ := betaReduce_run_rel hp hc hσ hw
      (by first | exact star_brun.1 h' | exact star_brun.2 h')
    exact ⟨_, evs', star_core π (brun_star hWB hb), hE ▸ rfl, GFEvRel.weakensAssumes hm⟩


/-- **Beta reduction keeps the conditions typed**: on a list in passive form whose `assume`,
    `assert` and `cover` conditions are typed Boolean expressions, so are those of its beta
    reduction. -/
theorem betaReduceBlock_condsTyped {ss : Statements} (hp : Block.passiveForm ss = true)
    (hc : Block.condsTyped Expression.Typed ss) :
    Block.condsTyped Expression.Typed (betaReduceBlock ss) := by
  unfold betaReduceBlock
  induction ss using Block.passiveForm.induct <;> (try cases ‹ExprOrNondet Expression›) <;>
    simp_all [reduceBlock, reduceStmt, Command.mapExpr, Block.passiveForm, Block.condsTyped,
      Stmt.condsTyped, CmdExt.condsTyped, reduceExpr, Expression.Typed_betaReduceRedexesWith]

end -- public section

end BetaReduce
end Core
