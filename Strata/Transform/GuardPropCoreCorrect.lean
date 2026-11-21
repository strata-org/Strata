/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.GuardPropCorrect
public import Strata.Transform.GuardPropProps
public import Strata.Transform.GuardFwdCoreCorrect
public import Strata.Transform.Passive.CoreTyped
public import Strata.Transform.GuardPropTyping
import all Strata.Transform.GuardProp
import all Strata.Transform.Passive.CoreLang
import all Strata.Languages.Core.PipelinePhase

/-! # Guard propagation over-approximates (Core)

Over Core's event language for statement lists (`EventLang.coreBlock`), guard propagation on a
list in passive form is a trace over-approximation in the general form
`OverapproximatesTracesUptoWhen` (`guardProp_overapproximatesTraces`): the initial environments
are equal; a source trace and its target trace correspond while the source's assumptions hold
(`Trace.KeepsWhileAssumed`: same kinds, labels and metadata, and conditions that hold exactly
when the source's hold, up to the first assumption of the source that does not hold); final
environments are equal; and the output satisfies the gate wherever the input does.  The proof
runs a Core trace as a trace over `EvalE`, turns it into a big-step reach or run, replays it on
the output (`guardProp_reach_rel`, `guardProp_run_rel`) and turns the replay back into a Core
trace.  The laws it uses for Core are those of guard forwarding (`coreGuardFwdLaws`,
`coreGuardFwdSynLaws`).

A run of the pipeline phase `guardPropPipelinePhase` runs `guardPropProgram`
(`guardPropPipelinePhase_ok`), which rewrites each procedure body (`guardPropProgram_over`).

Key theorems: `blockInitEnvWF_guardProp`, `guardProp_overapproximatesTraces`,
`guardPropPipelinePhase_ok`, `guardPropProgram_over`, `guardProp_initsTyped`,
`guardProp_condsTyped`. -/

namespace Core
namespace GuardProp

open Imperative Imperative.BigStep Imperative.GuardFwd Imperative.GuardProp
  Imperative.Specification Imperative.Specification.Transform Core.Logic Strata.Logic Lambda
  Core.GuardFwd Core.DeadDefElim Imperative.DeadDefElim

public section

/-- **The syntax laws of guard propagation hold for Core.** -/
theorem coreGuardPropSynLaws : GuardPropSynLaws Expression where
  ops_substFn_mem e g o ho := LExpr.getOps_substFvarsBy_mem e g o ho
  ops_ff := rfl

/-- **The output of guard propagation is well formed from every environment the input is**: on
    a list in passive form, the gate `BlockInitEnvWF` of the input gives that of the output. -/
theorem blockInitEnvWF_guardProp {params : InitEnvWFParams} {ss : Statements}
    {ρ : Imperative.Env Expression} (hp : Block.passiveForm ss = true)
    (h : BlockInitEnvWF params ss ρ) :
    BlockInitEnvWF params (guardProp ss) ρ := by
  obtain ⟨Γ, hσ, hw⟩ := h.fvarTypesOk
  have hg := walk_gate coreGuardFwdSynLaws coreGuardPropSynLaws
    (Std.HashSet.ofList (Block.assignedVarsH ss)) params.declaredFuncs ss hp {} _ Γ h.defUseOk hw
    fun _ _ h => by simp at h
  obtain ⟨hpo, hdv, hit, -⟩ := walk_shape (Std.HashSet.ofList (Block.assignedVarsH ss)) ss hp {}
  exact { h with
    exitsNotReserved := fun l hl => by simp [guardProp, Block.labels_of_passiveForm hpo] at hl
    readWritesDefined := fun n hn hnd =>
      Block.defined_of_mem_touchedVars (fun _ _ h => h) hg.1 hn hnd
    defsUndefined := fun n hn => h.defsUndefined n (hdv false ▸ hn)
    definedVarsNotReserved := fun n hn => h.definedVarsNotReserved n (hdv false ▸ hn)
    defUseOk := hg.1
    initTypesInhabited := fun ty hty => h.initTypesInhabited ty (hit ▸ hty)
    fvarTypesOk := ⟨Γ, hσ, hg.2⟩
    measuresTyped := fun m hm => by simp [guardProp, Block.measures_of_passiveForm hpo] at hm }

/-- The environment `ρ'` has the factory of `ρ` and holds, for every variable, the value of `ρ`
    or a value of its type (and nothing where `ρ` holds nothing). -/
@[expose] def EnvSameTypes (ρ ρ' : Imperative.Env Expression) : Prop :=
  ρ'.factory = ρ.factory ∧ ∀ x, SameTyO ρ.factory (ρ.store x) (ρ'.store x)

/-- **Guard propagation over-approximates the traces of a Core statement list.**  For a Core
    statement list `ss` in passive form (`Block.passiveForm`: only `init`, `assume`, `assert`,
    `cover` and `ite *`, the shape of the SSA phase's output), hence without loops and calls, and
    every initial environment `ρ₀` satisfying `BlockInitEnvWF params ss`:
    * every finite trace of `ss` from `ρ₀` has a trace of `guardProp ss` from `ρ₀` that
      corresponds to it while its assumptions hold (`Trace.KeepsWhileAssumed`: each event keeps
      its kind, label and metadata, and, up to the first assumption of the source that does not
      evaluate to `true`, each condition evaluates to `true` exactly when the source's does);
    * every terminating run of `ss` from `ρ₀` has a terminating run of `guardProp ss` from `ρ₀`
      with such a trace, in a final environment with the same factory that holds, for every
      variable, the value of the source's final environment or a value of its type
      (`EnvSameTypes`); a list in passive form has no exiting run;
    * `guardProp ss` satisfies `BlockInitEnvWF params` at `ρ₀`. -/
theorem guardProp_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) :
    OverapproximatesTracesUptoWhen Trace.KeepsWhileAssumed (· = ·) EnvSameTypes
      (EventLang.coreBlock π) (EventLang.coreBlock π) (fun ss => some (guardProp ss))
      (fun ss => Block.noLoops ss = true ∧ Statements.noCalls ss = true ∧
        Block.passiveForm ss = true) params params := by
  intro ss st' hT ⟨hss, hnc, hp⟩ ρ₀ _ rfl hwf
  cases hT
  obtain ⟨σ₀, F⟩ := ρ₀
  have hC : WellFormedStore σ₀ F := hwf.storeWellDefined
  have hWB := hwf.bool
  have hL := coreGuardFwdLaws F
  refine ⟨fun cfg trace h => ?_, fun ρ' trace h => ?_, fun l ρ' trace h => ?_,
    blockInitEnvWF_guardProp hp hwf⟩
  · have h' := star_evalE h hnc
    rcases Classical.em (trace = []) with rfl | htr
    · exact ⟨_, [], .refl _, .nil⟩
    obtain ⟨evs', hb, hm⟩ := guardProp_reach_rel hL hp hC (star_breach h' htr)
    obtain ⟨cfg', hc⟩ := breach_star hWB hb
    exact ⟨cfg', evs', star_core π hc, hm⟩
  · have h' := star_evalE h hnc
    have hE := starE_preserves_factory h'
    obtain ⟨evs', o', hb, hm, σ1, τ1, ⟨⟩, rfl, hD⟩ := guardProp_run_rel hL hp hC (star_brun.1 h')
    refine ⟨_, evs', star_core π (brun_star hWB hb), ?_, hm⟩
    exact ⟨hE, hE ▸ hD.same⟩
  · obtain ⟨-, o', -, -, σ1, τ1, ⟨⟩, -⟩ :=
      guardProp_run_rel hL hp hC (star_brun.2 (star_evalE h hnc))

/-- **The output of guard propagation is in passive form** (on a list in passive form). -/
theorem guardProp_passive {ss : Statements} (hp : Block.passiveForm ss = true) :
    Block.passiveForm (guardProp ss) = true :=
  (walk_shape (Std.HashSet.ofList (Block.assignedVarsH ss)) ss hp {}).1

/-! ## The pipeline phase -/

/-- A run of `guardPropPipelinePhase` on `program` is a run of `guardPropProgram`. -/
theorem guardPropPipelinePhase_ok (program : Program) (s : Transform.CoreTransformState) :
    (guardPropPipelinePhase.transform program).run s = (guardPropProgram program).run s :=
  (rfl)

/-- **The guard-propagation transform rewrites each procedure body.**  Let a run of
    `guardPropProgram` on the program `prog` succeed with `out`, and let `q` be a procedure of
    `prog` with structured body `ss`.  Then `out` contains the procedure with body
    `guardProp ss`, whose traces over-approximate those of `ss` when `ss` is in passive form
    (`guardProp_overapproximatesTraces`). -/
theorem guardPropProgram_over {prog out : Program} {s s' : Transform.CoreTransformState}
    {b : Bool} (h : (guardPropProgram prog).run s = (.ok (b, out), s')) {q : Procedure}
    {md : Imperative.MetaData Expression} {ss : Statements} (hq : Decl.proc q md ∈ prog.decls)
    {opq : Bool} (hb : q.body = .structured ss opq) :
    Decl.proc { q with body := .structured (guardProp ss) opq } md ∈ out.decls := by
  cases h
  exact Program.mapStructuredBodies_mem hq hb

/-- Guard propagation keeps every `init` as it is, so it keeps them typed. -/
private theorem walk_initsTyped (ini : Std.HashSet Expression.Ident) (ss : Statements)
    (hp : Block.passiveForm ss = true) :
    ∀ st, Block.initsTyped Core.Expression.Typed ss →
      Block.initsTyped Core.Expression.Typed (Imperative.GuardProp.walk ini st ss).1 := by
  induction ss using Block.passiveForm.induct <;> (try cases ‹ExprOrNondet Expression›) <;>
    simp_all [Imperative.GuardProp.walk, Imperative.GuardProp.walkS, Block.initsTyped,
      Stmt.initsTyped, CmdExt.initsTyped, Block.passiveForm]

/-- **Guard propagation keeps procedure bodies in passive form, typed and def-use well formed.**
    Every procedure `q'` of a run of `guardPropProgram` on `p` comes from a procedure `q` of `p`
    with the same header and metadata; when `q'` has a structured body, so has `q`, and when the
    body of `q` is in passive form, the body of `q'` is in passive form, is def-use well formed
    and passes the annotation check wherever the body of `q` does, and has typed `init`s when
    the body of `q` does. -/
theorem guardPropProgram_proc_kept {p out : Program} {s s' : Transform.CoreTransformState}
    {b : Bool} (h : (guardPropProgram p).run s = (.ok (b, out), s')) {q' : Procedure}
    {md : Imperative.MetaData Expression} (hq : Decl.proc q' md ∈ out.decls) :
    ∃ q, Decl.proc q md ∈ p.decls ∧ q'.header = q.header ∧
      ∀ ss' o, q'.body = .structured ss' o → ∃ ss, q.body = .structured ss o ∧
        (Block.passiveForm ss = true →
          Block.passiveForm ss' = true ∧
          (∀ D df Γ, Block.defUseWellFormed D df ss = true → Block.fvarTypesWellAnnotated Γ ss →
            Block.defUseWellFormed D df ss' = true ∧ Block.fvarTypesWellAnnotated Γ ss') ∧
          (∀ Γ, Block.fvarTypesWellAnnotated Γ ss → Block.initsTyped Core.Expression.Typed ss →
            Block.initsTyped Core.Expression.Typed ss')) := by
  cases h
  obtain ⟨q, hd, hh, hk⟩ := Program.mapStructuredBodies_proc hq
  refine ⟨q, hd, hh, fun ss' o hb' => ?_⟩
  obtain ⟨ss, hb, rfl⟩ := hk ss' o hb'
  refine ⟨ss, hb, fun hp => ⟨guardProp_passive hp, fun D df Γ hdu hw => ?_,
    fun Γ _ hT => walk_initsTyped _ ss hp {} hT⟩⟩
  exact walk_gate coreGuardFwdSynLaws coreGuardPropSynLaws
    (Std.HashSet.ofList (Block.assignedVarsH ss)) df ss hp {} D Γ hdu hw
    fun _ _ h => by simp at h


/-- **Guard propagation keeps the `init`s typed** (`Core.Expression.Typed` at their declared
    types) of a list in passive form: it keeps every `init` as it is. -/
theorem guardProp_initsTyped {ss : Statements} (hp : Block.passiveForm ss = true)
    (hi : Block.initsTyped Core.Expression.Typed ss) :
    Block.initsTyped Core.Expression.Typed (guardProp ss) :=
  walk_initsTyped _ ss hp {} hi

/-- **Guard propagation keeps the conditions typed** (`Core.Expression.Typed` at the Boolean
    type) of a Core statement list in passive form that is def-use well formed, whose
    annotations agree with a typing `Γ` and whose `init`s are typed. -/
theorem guardProp_condsTyped {ss : Statements} (hp : Block.passiveForm ss = true)
    {D df : Expression.Ident → Bool} {Γ : VarTyping Expression}
    (hd : Block.defUseWellFormed D df ss = true) (hw : Block.fvarTypesWellAnnotated Γ ss)
    (hi : Block.initsTyped Core.Expression.Typed ss)
    (hc : Block.condsTyped Core.Expression.Typed ss) :
    Block.condsTyped Core.Expression.Typed (guardProp ss) :=
  Imperative.GuardProp.guardProp_condsTyped coreGuardFwdSynLaws coreGuardPropSynLaws
    (typedOpLaws Lambda.Factory.default)
    (fun b => by
      cases b <;> exact ⟨.bool, rfl, rfl, fun _ _ h => by
        simp [Imperative.GuardProp.boolE, HasBool.tt, HasBool.ff, LExpr.freeVars] at h, .const rfl⟩)
    hp hd hw hi hc

end -- public section

end GuardProp
end Core
