/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.GuardFwdCorrect
public import Strata.Transform.DeadDefElimCoreCorrect
public import Strata.Languages.Core.InstWellFormedSemanticsEval
public import Strata.Languages.Core.InstExprTyping
public import Strata.Transform.SSA.SSACoreCorrect
public import Strata.Transform.GuardFwdTyping
public import Strata.Transform.Passive.CoreTyped
import all Strata.Transform.GuardFwd
import all Strata.Languages.Core.PipelinePhase
import all Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.LExprDenoteEval

/-! # Guard forwarding over-approximates (Core)

The Core expression language satisfies the laws of guard forwarding (`coreGuardFwdLaws`), from
the denotational semantics of Core expressions (`Lambda.LExpr.denoteEval`): a conditional
evaluates when its condition evaluates to a Boolean and both arms to values of one sort
(`Lambda.LExpr.denoteEval_ite_iff`), and the sort of an expression's value depends on the free
variables only through the sorts of their values (`denoteEval_retype`).  Its syntax satisfies
the laws the initial-environment gate of the output needs (`coreGuardFwdSynLaws`), so the output
of guard forwarding on a list in passive form is well formed wherever its input is
(`blockInitEnvWF_guardFwd`).

Over Core's event language for statement lists (`EventLang.coreBlock`), guard forwarding on a
list in passive form is a trace over-approximation in the general form
`OverapproximatesTracesUptoWhen` (`guardFwd_overapproximatesTraces`): the initial environments
are equal; a source trace and its target trace correspond under evaluation to `true`
(`Trace.WeakensAssumes evalInterp`); final environments are equal; and the output satisfies the
gate wherever the input does.  The proof runs a Core trace as a trace over `EvalE`, turns it into
a big-step reach or run, replays it on the output (`guardFwd_reach_rel`, `guardFwd_run_rel`) and
turns the replay back into a Core trace.

The output of the SSA phase is in passive form (`WP.ssaEntry_passive`), and the output of guard
forwarding has no loops and calls (`guardFwd_noLoops_noCalls`), so the three phases compose:
guard forwarding then the erasure of unread definitions
(`guardFwd_deadDefElimH_overapproximatesTraces`, by `comp_trans_eq`), and the SSA phase before
them (`ssa_guardFwd_deadDefElimH_overapproximatesTraces`, by `comp_eq_right`).

A run of the pipeline phase `guardFwdPipelinePhase` runs `guardFwdProgram`
(`guardFwdPipelinePhase_ok`), which rewrites each procedure body (`guardFwdProgram_over`).

Key theorems: `coreGuardFwdLaws`, `coreGuardFwdSynLaws`, `blockInitEnvWF_guardFwd`,
`guardFwd_overapproximatesTraces`, `guardFwd_deadDefElimH_overapproximatesTraces`,
`ssa_guardFwd_deadDefElimH_overapproximatesTraces`, `guardFwdPipelinePhase_ok`. -/

namespace Core
namespace GuardFwd

open Imperative Imperative.BigStep Imperative.GuardFwd Imperative.Specification
  Imperative.Specification.Transform Core.Logic Strata.Logic Lambda Core.DeadDefElim
  Imperative.DeadDefElim

public section

/-- A monomorphic type scheme reads as its type. -/
private theorem toMonoType?_forAll (τ : LMonoTy) : (LTy.forAll [] τ).toMonoType? = some τ := by
  simp [LTy.toMonoType?]

/-- Two Core values have a common type exactly when both belong to the factory and have one
    sort. -/
private theorem sameTy_iff {F : Expression.Factory} {a b : Expression.Val} :
    SameTy F a b ↔ a.tc = F.model.tcInterp ∧ b.tc = F.model.tcInterp ∧ a.sort = b.sort := by
  refine ⟨fun ⟨ty, ⟨ha, hta⟩, ⟨hb, htb⟩⟩ => ⟨ha, hb, ?_⟩, fun ⟨ha, hb, hs⟩ =>
    ⟨.forAll [] a.sort.toMonoTy, ⟨ha, toMonoType?_forAll _⟩, ⟨hb, hs ▸ toMonoType?_forAll _⟩⟩⟩
  exact LSort.toMonoTy_injective (Option.some.inj (hta.symm.trans htb))

/-- **Retyping.**  Giving the free variables of a Core expression with a value values of the
    same sorts and of the factory keeps a value of the same sort. -/
private theorem denoteEval_retype {F : Expression.Factory} {σ σ' : SemanticStore Expression}
    {e : Expression.Expr} {v : Expression.Val} (hC' : WellFormedStore σ' F)
    (h : ∀ x ∈ HasFvars.getFvars e, SameTyO F (σ x) (σ' x))
    (hv : LExpr.denoteEval F σ e = some v) :
    ∃ v', LExpr.denoteEval F σ' e = some v' ∧ SameTy F v v' := by
  have hmem {x ty} (hx : (x, ty) ∈ e.freeVars) : x ∈ HasFvars.getFvars (P := Expression) e := by
    show x ∈ LExpr.LExpr.getVars e
    rw [getVars_eq_freeVars_idents]
    exact List.mem_map.2 ⟨_, hx, rfl⟩
  obtain ⟨hD, τ, hτ, hg, rfl⟩ := (LExpr.denoteEval_eq_some_iff (T := CoreLParams)).mp hv
  have hann : e.annotateFvars (ValStore.ann (T := CoreLParams) σ') =
      e.annotateFvars (ValStore.ann (T := CoreLParams) σ) :=
    LExpr.annotateFvars_congr e fun x ty hx => by
      rcases h x (hmem hx) with h | ⟨a, b, ha, hb, hab⟩
      · simp [ValStore.ann, h]
      · simp [ValStore.ann, ha, hb, (sameTy_iff.1 hab).2.2]
  have hτ' : (e.annotateFvars (ValStore.ann (T := CoreLParams) σ')).HasTypeA [] τ := hann ▸ hτ
  refine ⟨_, (LExpr.denoteEval_eq_some_iff (T := CoreLParams)).mpr
    ⟨fun x hx => ?_, τ, hτ', hg, rfl⟩,
    sameTy_iff.2 ⟨rfl, rfl, rfl⟩⟩
  rcases h x hx with h | ⟨a, b, -, hb, -⟩
  · exact h ▸ hD x hx
  · exact ⟨b, hb, hC' x b hb⟩

/-- A Core value of the Boolean type is `true` or `false`. -/
private theorem coreGuardFwdBool (F : Expression.Factory) {w : Expression.Val}
    (h : SameTy F w (HasBool.ttVal F)) : w = HasBool.ttVal F ∨ w = HasBool.ffVal F := by
  obtain ⟨hw, -, hs⟩ := sameTy_iff.1 h
  exact valueOfTy_bool F w ⟨hw, boolTy_toMonoType.trans (by rw [hs]; rfl)⟩

/-- **The laws of guard forwarding hold for Core.** -/
theorem coreGuardFwdLaws (F : Expression.Factory) : GuardFwdLaws (P := Expression) F where
  var := coreEvaluator_WellFormedSemanticEvalVar F
  congr := coreEvaluator_WellFormedSemanticEvalExprCongr F
  subst := WP.coreEvaluator_WellFormedSemanticEvalSubstExprs F
  typed h := ⟨.forAll [] _, LExpr.denoteEval_tc h, toMonoType?_forAll _⟩
  retype _ hC' h hv := denoteEval_retype hC' h hv
  bool_cases := coreGuardFwdBool F
  ite_parts {σ c t f v} h := by
    obtain ⟨b, vt, vf, hc, ht, hf, hs, rfl⟩ :=
      (LExpr.denoteEval_ite_iff (T := CoreLParams)).mp h
    refine ⟨_, vt, vf, hc, ht, hf, sameTy_iff.2 ⟨rfl, rfl, rfl⟩,
      sameTy_iff.2 ⟨LExpr.denoteEval_tc ht, LExpr.denoteEval_tc hf, hs⟩, fun hb => ?_,
      fun hb => ?_⟩ <;> cases SemValue.ofBool_injective hb <;> rfl
  val := coreEvaluator_WellFormedSemanticEvalVal F
  eq_refl {σ e a b x} he ha hb hC hx := by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hx
    have hav := (coreEvaluator_WellFormedSemanticEvalVar F a x σ hC ha).trans hv
    have hbv := (coreEvaluator_WellFormedSemanticEvalVar F b x σ hC hb).trans hv
    cases e <;> simp only [GuardOps.eqView?, eqView?, reduceCtorEq, Option.some.injEq,
      Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact LExpr.denoteEval_eq_true hav hbv
  ite_build {σ c t f wc wt wf} hc ht hf hb htf := by
    obtain ⟨-, -, hs⟩ := sameTy_iff.1 htf
    rcases (coreGuardFwdBool F hb) with rfl | rfl
    · exact ⟨wt, (LExpr.denoteEval_ite_iff (T := CoreLParams)).mpr ⟨true, wt, wf, hc, ht, hf, hs,
        rfl⟩, fun _ => rfl, fun h => absurd h (HasBool.ttVal_ne_ffVal F)⟩
    · exact ⟨wf, (LExpr.denoteEval_ite_iff (T := CoreLParams)).mpr ⟨false, wt, wf, hc, ht, hf, hs,
        rfl⟩, fun h => absurd h.symm (HasBool.ttVal_ne_ffVal F), fun _ => rfl⟩

/-- **The syntax laws of guard forwarding hold for Core.** -/
theorem coreGuardFwdSynLaws : GuardFwdSynLaws Expression where
  typed_ite c t f p := by
    change p ∈ Expression.typedFvars (LExpr.ite valueLoc c t f) ↔ _
    simp [HasFvars.getTypedFvars, Expression.typedFvars, LExpr.freeVars, List.filterMap_append]
  ops_ite c t f o := by
    change o ∈ LExpr.getOps (LExpr.ite valueLoc c t f) ↔ _
    simp [HasOps.getOps, LExpr.getOps]
  ops_iteView o hv := by
    rw [WP.iteView?_getOps hv]
    change _ ↔ o ∈ LExpr.getOps (LExpr.ite valueLoc _ _ _ : Expression.Expr)
    simp [HasOps.getOps, LExpr.getOps]
  ops_substFn e g hg o ho := LExpr.getOps_substFvarsBy hg e o ho
  ops_atomic r hr := by
    simp only [atomic, Bool.or_eq_true, Option.isSome_iff_exists] at hr
    rcases hr with (⟨x, hx⟩ | ⟨b, hb⟩) | hc
    · cases r <;> simp_all [HasFvar.getFvar] <;> rfl
    · exact WP.boolLit?_getOps hb
    · cases r <;> simp_all [WP.WPOps.lit?] <;> rfl
  typed_tt := rfl
  ops_tt := rfl

/-- **The output of guard forwarding is well formed from every environment the input is**: on a
    list in passive form, the gate `BlockInitEnvWF` of the input gives that of the output. -/
theorem blockInitEnvWF_guardFwd {params : InitEnvWFParams} {ss : Statements}
    {ρ : Imperative.Env Expression} (hp : Block.passiveForm ss = true)
    (h : BlockInitEnvWF params ss ρ) :
    BlockInitEnvWF params (guardFwd ss) ρ := by
  obtain ⟨Γ, hσ, hw⟩ := h.fvarTypesOk
  have hg := walk_gate coreGuardFwdSynLaws
    ⟨countB {} ss, Std.HashSet.ofList (Block.assignedVarsH ss), innerB {} ss⟩
    params.declaredFuncs ss hp {} _ Γ
    h.defUseOk hw fun _ _ h => by simp at h
  obtain ⟨hpo, hdv, hit, -⟩ := walk_shape
    ⟨countB {} ss, Std.HashSet.ofList (Block.assignedVarsH ss), innerB {} ss⟩
    ss hp {}
  exact { h with
    exitsNotReserved := fun l hl => by simp [guardFwd, Block.labels_of_passiveForm hpo] at hl
    measuresTyped := fun m hm => by simp [guardFwd, Block.measures_of_passiveForm hpo] at hm
    readWritesDefined := fun n hn hnd =>
      Block.defined_of_mem_touchedVars (fun _ _ h => h) hg.1 hn hnd
    defsUndefined := fun n hn => h.defsUndefined n (hdv false ▸ hn)
    definedVarsNotReserved := fun n hn => h.definedVarsNotReserved n (hdv false ▸ hn)
    defUseOk := hg.1
    initTypesInhabited := fun ty hty => h.initTypesInhabited ty (hit ▸ hty)
    fvarTypesOk := ⟨Γ, hσ, hg.2⟩ }

/-! ## The trace over-approximation -/

/-- **Guard forwarding over-approximates the traces of a Core statement list.**  For a Core
    statement list `ss` in passive form (`Block.passiveForm`: only `init`, `assume`, `assert`,
    `cover` and `ite *`, the shape of the SSA phase's output), hence without loops and calls, and
    every initial environment `ρ₀` satisfying `BlockInitEnvWF params ss`:
    * every finite trace of `ss` from `ρ₀` has a trace of `guardFwd ss` from `ρ₀` whose
      assumptions are weakened (`Trace.WeakensAssumes evalInterp`: each assertion and cover
      keeps its label and metadata and holds exactly when the source's holds, each assumption
      keeps its label and metadata and holds whenever the source's holds);
    * every terminating or exiting run of `ss` from `ρ₀` has a run of `guardFwd ss` from `ρ₀`
      ending in the same way, in the same final environment, with such a trace;
    * `guardFwd ss` satisfies `BlockInitEnvWF params` at `ρ₀`. -/
theorem guardFwd_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) :
    OverapproximatesTracesUptoWhen (Trace.WeakensAssumes evalInterp) (· = ·) (· = ·)
      (EventLang.coreBlock π) (EventLang.coreBlock π) (fun ss => some (guardFwd ss))
      (fun ss => Block.noLoops ss = true ∧ Statements.noCalls ss = true ∧
        Block.passiveForm ss = true) params params := by
  intro ss st' hT ⟨hss, hnc, hp⟩ ρ₀ _ rfl hwf
  cases hT
  obtain ⟨σ₀, F⟩ := ρ₀
  have hC : WellFormedStore σ₀ F := hwf.storeWellDefined
  have hWB := hwf.bool
  have hL := coreGuardFwdLaws F
  refine ⟨fun cfg trace h => ?_, fun ρ' trace h => ?_, fun l ρ' trace h => ?_,
    blockInitEnvWF_guardFwd hp hwf⟩
  all_goals have h' := star_evalE h hnc
  · rcases Classical.em (trace = []) with rfl | htr
    · exact ⟨_, [], .refl _, .nil⟩
    obtain ⟨evs', hb, hm⟩ := guardFwd_reach_rel hL hp hC (star_breach h' htr)
    obtain ⟨cfg', hc⟩ := breach_star hWB hb
    exact ⟨cfg', evs', star_core π hc, GFEvRel.weakensAssumes hm⟩
  all_goals
    have hE := starE_preserves_factory h'
    obtain ⟨evs', hb, hm⟩ := guardFwd_run_rel hL hp hC
      (by first | exact star_brun.1 h' | exact star_brun.2 h')
    exact ⟨_, evs', star_core π (brun_star hWB hb), hE ▸ rfl, GFEvRel.weakensAssumes hm⟩

/-! ## Composition with the SSA phase and the erasure of unread definitions -/

/-- **The output of guard forwarding has no loops and calls** (on a list in passive form). -/
theorem guardFwd_noLoops_noCalls {ss : Statements} (hp : Block.passiveForm ss = true) :
    Block.noLoops (guardFwd ss) = true ∧ Statements.noCalls (guardFwd ss) = true := by
  have hp' := (walk_shape
    ⟨countB {} ss, Std.HashSet.ofList (Block.assignedVarsH ss), innerB {} ss⟩ ss hp {}).1
  exact ⟨Block.passiveForm_allSubstmts (fun _ => rfl) (fun _ _ _ => rfl) hp',
    Block.passiveForm_allSubstmts (fun _ => rfl) (fun _ _ _ => rfl) hp'⟩

/-- **The output of guard forwarding is in passive form** (on a list in passive form). -/
theorem guardFwd_passive {ss : Statements} (hp : Block.passiveForm ss = true) :
    Block.passiveForm (guardFwd ss) = true :=
  (walk_shape
    ⟨countB {} ss, Std.HashSet.ofList (Block.assignedVarsH ss), innerB {} ss⟩ ss hp {}).1

/-- **Guard forwarding followed by the erasure of unread definitions over-approximates the
    traces of a Core statement list in passive form**, from equal initial environments: traces are
    related by the composition of `Trace.WeakensAssumes evalInterp` and `List.Rel₂ DDEventRel`,
    and final environments by `DDOut`. -/
theorem guardFwd_deadDefElimH_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) :
    OverapproximatesTracesUptoWhen
      (RComp (Trace.WeakensAssumes evalInterp) (List.Rel₂ DDEventRel)) (· = ·) DDOut
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss => some (guardFwd ss) >>= fun ss => some (Imperative.DeadDefElim.deadDefElimH [] ss))
      (fun ss => Block.noLoops ss = true ∧ Statements.noCalls ss = true ∧
        Block.passiveForm ss = true) params params := by
  exact OverapproximatesTracesUptoWhen.comp_trans_eq _ _ DDOut ddOut_trans
    (EventLang.coreBlock π) (EventLang.coreBlock π) (EventLang.coreBlock π)
    (fun ss => some (guardFwd ss)) (fun ss => some (deadDefElimH [] ss)) params params params
    (fun _ _ h hp => Option.some.inj h ▸ guardFwd_noLoops_noCalls hp.2.2)
    ((guardFwd_overapproximatesTraces π params).mono_out fun _ _ h =>
      by subst h; exact ⟨rfl, .refl _⟩)
    (deadDefElimH_overapproximatesTraces π params)

/-- **The SSA phase, guard forwarding and the erasure of unread definitions over-approximate the
    traces of a guarded statement list**, under the hypotheses and the precondition of
    `ssa_overapproximatesTraces`.  Initial environments are related by the
    entry renaming (`SSAEntryRel`); traces by the composition of the three trace relations; final
    environments by the composition of the factory equality of the SSA phase and `DDOut`. -/
theorem ssa_guardFwd_deadDefElimH_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) (hp : ∀ p ∈ params.prefixIdents, '@' ∉ p.toList)
    (fac : Lambda.Factory CoreLParams) (G : WP.IdSet Expression) (tys : WP.Tys Expression)
    (xs : List Expression.Ident)
    (al : List (Expression.Ident × Expression.Ident)) (hal : ∀ q ∈ al, q.2 ∈ xs)
    (ss₀ : Statements) :
    OverapproximatesTracesUptoWhen
      (RComp (Trace.WeakensAssumes evalInterp)
        (RComp (Trace.WeakensAssumes evalInterp) (List.Rel₂ DDEventRel)))
      (WP.SSAEntryRel fac G tys xs al ss₀) (RComp (fun ρ ρ' => ρ'.factory = ρ.factory) DDOut)
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss : Statements => (WP.ssaEntry fac G tys xs al ss).toOption.map (·.2.out) >>=
        fun ss : Statements => some (guardFwd ss) >>=
          fun ss : Statements => some (Imperative.DeadDefElim.deadDefElimH [] ss))
      (fun ss : Statements => ss = ss₀ ∧ Block.treeForm ss = true ∧ Block.armsHaveChecks ss = true ∧
        ∀ x ∈ Block.freeVars ss, x ∈ xs ∨ x ∈ al.map (·.1)) params params :=
  OverapproximatesTracesUptoWhen.comp_eq_right
    (fun _ _ h hpre => WP.ssaEntry_passive h hpre.2.1)
    (WP.ssa_overapproximatesTraces π params hp fac G tys xs al hal ss₀)
    (guardFwd_deadDefElimH_overapproximatesTraces π params)

/-! ## The pipeline phase -/

/-- A run of `guardFwdPipelinePhase` on `program` is a run of `guardFwdProgram`. -/
theorem guardFwdPipelinePhase_ok (program : Program) (s : Transform.CoreTransformState) :
    (guardFwdPipelinePhase.transform program).run s = (guardFwdProgram program).run s :=
  (rfl)

/-- **The guard-forwarding transform rewrites each procedure body.**  Let a run of
    `guardFwdProgram` on the program `prog` succeed with `out`, and let `q` be a procedure of
    `prog` with structured body `ss`.  Then `out` contains the procedure with body
    `guardFwd ss`, whose traces over-approximate those of `ss` when `ss` is in passive form
    (`guardFwd_overapproximatesTraces`). -/
theorem guardFwdProgram_over {prog out : Program} {s s' : Transform.CoreTransformState}
    {b : Bool} (h : (guardFwdProgram prog).run s = (.ok (b, out), s')) {q : Procedure}
    {md : Imperative.MetaData Expression} {ss : Statements} (hq : Decl.proc q md ∈ prog.decls)
    {opq : Bool} (hb : q.body = .structured ss opq) :
    Decl.proc { q with body := .structured (guardFwd ss) opq } md ∈ out.decls := by
  cases h
  exact Program.mapStructuredBodies_mem hq hb


/-- **Guard forwarding keeps the conditions of a Core statement list Boolean**: on a list in
    passive form that is def-use well formed, whose annotations agree with a typing `Γ` and whose
    `init`s are typed (`Core.Expression.Typed`), every `assume`, `assert` and `cover` of
    `guardFwd ss` has a Boolean condition when every one of `ss` has. -/
theorem coreGuardFwd_condsTyped {ss : Statements} (hp : Block.passiveForm ss = true)
    {dv df : Expression.Ident → Bool} {Γ : VarTyping Expression}
    (hd : Block.defUseWellFormed dv df ss = true) (hf : Block.fvarTypesWellAnnotated Γ ss)
    (hT : Block.initsTyped Expression.Typed ss) (hc : Block.condsTyped Expression.Typed ss) :
    Block.condsTyped Expression.Typed (guardFwd ss) :=
  Imperative.GuardFwd.guardFwd_condsTyped coreGuardFwdSynLaws
    (typedOpLaws Lambda.Factory.default) Expression.Typed_tt hp hd hf hT hc

end -- public section

end GuardFwd
end Core
