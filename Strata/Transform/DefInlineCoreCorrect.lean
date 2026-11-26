/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.DefInlineCorrect
public import Strata.Transform.GuardFwdCoreCorrect
public import Strata.Transform.DefInlineTyping
public import Strata.Transform.Passive.CoreTyped
import all Strata.Transform.DefInline
import all Strata.Transform.GuardFwd
import all Strata.Languages.Core.PipelinePhase
import all Strata.DL.Lambda.LExpr
import Strata.Languages.Core.IntEvalProps
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.Factory

/-! # Inlining of single-use definitions over-approximates (Core)

The normalization of the Core phase, the folding of the constants of a sum (`addFold`), keeps values
under every factory that resolves `Int.Add` to Core's built-in addition (`addFold_normLaw`), adds no
free variable, annotated occurrence or operator (`addFold_synLaws`, after the substitution) and
keeps types (`addFold_typed`). Every factory of the pipeline resolves `Int.Add` so, since extending
`Core.Factory` refuses redefinitions (`addFactory_intAdd`).

The syntax of Core expressions satisfies the laws the initial-environment gate of the output needs,
for every substituting normalization that adds no free variable, annotated occurrence or operator to
the substituted expression (`coreDefInlineSynLaws`), so the output of `defInline` on a list in
passive form is well formed wherever its input is (`blockInitEnvWF_defInline`).

Over Core's event language for statement lists (`EventLang.coreBlock`), `defInline norm` on a
list in passive form is a trace over-approximation in the general form
`OverapproximatesTracesUptoWhen` (`defInline_overapproximatesTraces`), for initial environments
that are equal and satisfy a predicate `Q` under which `norm` keeps the value of the substituted
expression in the stores typing its annotated occurrences (`SubstNormLawT`): a source trace and
its target trace correspond under evaluation to `true` (`Trace.WeakensAssumes evalInterp`; each
condition of the target has the value of the source's); final environments are equal; and the
output satisfies the gate wherever the input does.

The phase runs after guard forwarding and before the erasure of unread definitions, which removes
the definitions it leaves unread.  The four phases from the SSA phase on compose
(`ssa_guardFwd_defInline_deadDefElimH_overapproximatesTraces`, by `comp_eqOn_right` and
`comp_eq_right`).

A run of the pipeline phase `defInlinePipelinePhase` runs `defInlineProgram`
(`defInlinePipelinePhase_ok`), which rewrites each procedure body (`defInlineProgram_over`).

Key theorems: `addFold_normLaw`, `addFold_normLawT`, `addFold_synLaws`, `addFold_typed`,
`addFactory_intAdd`,
`coreDefInlineSynLaws`, `blockInitEnvWF_defInline`,
`defInline_overapproximatesTraces`, `defInline_deadDefElimH_overapproximatesTraces`,
`guardFwd_defInline_deadDefElimH_overapproximatesTraces`,
`ssa_guardFwd_defInline_deadDefElimH_overapproximatesTraces`,
`defInlinePipelinePhase_ok`. -/

namespace Core
namespace DefInline

open Imperative Imperative.BigStep Imperative.GuardFwd Imperative.DefInline
  Imperative.Specification Imperative.Specification.Transform Core.Logic Strata.Logic Lambda
  Core.DeadDefElim Imperative.DeadDefElim Core.GuardFwd

public section

/-- **The syntax laws of the inlining hold for Core**, for every substituting normalization that
    adds no free-variable occurrence or operator to the substituted expression. -/
theorem coreDefInlineSynLaws {norm : SubstNorm Expression}
    (hv : ∀ g e p, p ∈ (norm g e).freeVars → p ∈ (e.substFvarsBy g).freeVars)
    (ho : ∀ g e o, o ∈ LExpr.getOps (norm g e) → o ∈ LExpr.getOps (e.substFvarsBy g)) :
    DefInlineSynLaws Expression norm where
  ops_substFn e _ o h := LExpr.getOps_substFvarsBy_mem e _ o h
  norm_fvars g e y hy := by
    simp only [HasFvars.getFvars, getVars_eq_freeVars_idents, List.mem_map] at hy ⊢
    exact hy.imp fun p ⟨hp, he⟩ => ⟨hv g e p hp, he⟩
  norm_typed g e p hp := by
    simp only [HasFvars.getTypedFvars, Expression.typedFvars, List.mem_filterMap] at hp ⊢
    exact hp.imp fun q ⟨hq, h⟩ => ⟨hv g e q hq, h⟩
  norm_ops := ho

/-! ## The folding of the constants of a sum -/

/-- The free-variable occurrences of `addFold e` are among those of `e`. -/
theorem addFold_freeVars (e : Expression.Expr) :
    ∀ p ∈ (addFold e).freeVars, p ∈ e.freeVars := by
  intro p hp
  unfold addFold at hp
  repeat' split at hp
  all_goals grind [LExpr.freeVars]

/-- The operators of `addFold e` are among those of `e`. -/
theorem addFold_ops (e : Expression.Expr) :
    ∀ o ∈ LExpr.getOps (addFold e), o ∈ LExpr.getOps e := by
  intro o ho
  unfold addFold at ho
  repeat' split at ho
  all_goals grind [LExpr.getOps]

/-- **The syntax laws of the inlining hold for the folding of the constants of a sum** after the
    substitution. -/
theorem addFold_synLaws : DefInlineSynLaws Expression (.after addFold) :=
  coreDefInlineSynLaws (fun _ _ => addFold_freeVars _) fun _ _ => addFold_ops _

/-- **The folding of the constants of a sum keeps types**: it folds an expression typed at `ty`
    (`Expression.Typed`) into one typed at `ty`. -/
theorem addFold_typed : NormTyped Expression.Typed addFold := by
  intro e ty ⟨τ, hτ, hg, hfv, hT⟩
  refine ⟨τ, hτ, hg, fun x τ? h => hfv x τ? (addFold_freeVars e _ h), ?_⟩
  unfold addFold
  repeat' split
  all_goals try exact hT
  rename_i hc
  obtain ⟨-, -, rfl, rfl⟩ := hc
  simp only [intAddTy] at hT ⊢
  obtain ⟨_, hf, -⟩ := HasTypeA.app_inv hT
  obtain ⟨_, ⟨⟩, hin⟩ := HasTypeA.app_inv hf
  obtain ⟨_, hf', -⟩ := HasTypeA.app_inv hin
  obtain ⟨_, ⟨⟩, ha⟩ := HasTypeA.app_inv hf'
  exact .app (.app .op ha) (.const rfl)

/-- An operator named `Int.Add` and annotated `int → int → int` applied to two integers evaluates
    to their sum when the factory resolves `Int.Add` to Core's built-in addition. -/
private theorem eval_add {F : Expression.Factory}
    (hF : F.factory["Int.Add"]? = some (intAddFunc (T := CoreLParams)).func) {σ : CoreStore}
    {m m' mo : ExpressionMetadata} {f : CoreIdent} (hf : f.name = "Int.Add")
    {x y : Expression.Expr} {a b : Int}
    (hx : Expression.eval F σ x = some (SemValue.ofInt F.model.tcInterp a))
    (hy : Expression.eval F σ y = some (SemValue.ofInt F.model.tcInterp b)) :
    Expression.eval F σ (.app m (.app m' (.op mo f intAddTy) x) y) =
      some (SemValue.ofInt F.model.tcInterp (a + b)) := by
  have h := LExpr.denoteEval_app2_op_int (m := m) (m' := m') (m'' := mo) (o := f) (c := .int)
    rfl hx hy
  rw [hf] at h
  exact h.trans (congrArg (fun n => some (SemValue.ofInt F.model.tcInterp n))
    (intAdd_opInterp_of_lookup F.model hF a b))

/-- **The folding of the constants of a sum keeps values** under a factory that resolves
    `Int.Add` to Core's built-in addition. -/
theorem addFold_normLaw {F : Expression.Factory}
    (hF : F.factory["Int.Add"]? = some (intAddFunc (T := CoreLParams)).func) :
    NormLaw (P := Expression) F addFold := by
  intro σ e _
  unfold addFold
  split
  split
  · rename_i m m' mo f ty m₁ m₁' mo' f' ty' a mc₁ c₁ mc c₂ hc
    obtain ⟨hf, hf', rfl, rfl⟩ := hc
    have hk (mk : ExpressionMetadata) (n : Int) : Expression.eval F σ (.const mk (.intConst n)) =
        some (SemValue.ofInt F.model.tcInterp n) := LExpr.denoteEval_intConst
    rcases Classical.em (∃ r, Expression.eval F σ a = some (SemValue.ofInt F.model.tcInterp r))
      with ⟨r, ha⟩ | ha
    · rw [eval_add hF hf ha (hk _ _), eval_add hF hf (eval_add hF hf' ha (hk _ _)) (hk _ _),
        Int.add_assoc]
    · have hn {x : Expression.Expr} {v : SemValue} {k : Int} {n n' n'' : ExpressionMetadata}
          {g : CoreIdent}
          (hx : ∀ p, Expression.eval F σ x = some (SemValue.ofInt F.model.tcInterp p) →
            ∃ r, Expression.eval F σ a = some (SemValue.ofInt F.model.tcInterp r))
          (hv : Expression.eval F σ (.app n (.app n' (.op n'' g intAddTy) x)
            (.const mc (.intConst k))) = some v) : False := by
        obtain ⟨p, -, hp, -⟩ := LExpr.denoteEval_app2_op_int_inv hv
        exact ha (hx _ hp)
      rw [Option.eq_none_iff_forall_ne_some.2 fun v hv => hn (fun _ h => ⟨_, h⟩) hv,
        Option.eq_none_iff_forall_ne_some.2 fun v hv => hn
          (x := .app m₁ (.app m₁' (.op mo' f' intAddTy) a) (.const mc₁ (.intConst c₁)))
          (fun _ h => (LExpr.denoteEval_app2_op_int_inv h).elim fun r h =>
            h.elim fun _ h => ⟨r, h.1⟩) hv]
  all_goals rfl

/-- **The folding of the constants of a sum keeps values in typed stores** (`NormLawT`) under a
    factory that resolves `Int.Add` to Core's built-in addition: it keeps them in every store. -/
theorem addFold_normLawT {F : Expression.Factory}
    (hF : F.factory["Int.Add"]? = some (intAddFunc (T := CoreLParams)).func) :
    NormLawT (P := Expression) F addFold :=
  NormLawT.of_forall (addFold_normLaw hF)

/-- **The factories of the pipeline resolve `Int.Add` to Core's built-in addition**: extending
    `Core.Factory` by `moreFns` keeps its functions, since an extension refuses redefinitions. -/
theorem addFactory_intAdd {moreFns fac : Lambda.Factory CoreLParams}
    (h : Core.Factory.addFactory moreFns = .ok fac) :
    fac["Int.Add"]? = some (intAddFunc (T := CoreLParams)).func :=
  addFactory_get h coreFactory_intAdd

/-! ## The inlining at a caller's choice of names

The same three results for `defInlineWith norm sel`, the inlining at a caller's choice of names.
None of them constrains `sel`: the walk's shape and gate lemmas (`walk_shape`, `walk_gate`) and
the run and reach relations (`defInlineWith_run_rel`, `defInlineWith_reach_rel`) hold for an
arbitrary context. -/

/-- **The output of the inlining at a caller's choice of names satisfies `BlockInitEnvWF`**:
    `blockInitEnvWF_defInline` for `defInlineWith norm sel`. -/
theorem blockInitEnvWF_defInlineWith {norm : SubstNorm Expression}
    (hS : DefInlineSynLaws Expression norm) {sel : Std.HashMap Expression.Ident Nat}
    {params : InitEnvWFParams} {ss : Statements} {ρ : Imperative.Env Expression}
    (hp : Block.passiveForm ss = true) (h : BlockInitEnvWF params ss ρ) :
    BlockInitEnvWF params (defInlineWith norm sel ss) ρ := by
  obtain ⟨Γ, hσ, hw⟩ := h.fvarTypesOk
  have hg := walk_gate hS ⟨sel, Std.HashSet.ofList (Block.assignedVarsH ss)⟩
    params.declaredFuncs ss hp {} _ Γ h.defUseOk hw fun _ _ h => by simp at h
  obtain ⟨hpo, hdv, hit, -⟩ := walk_shape norm
    ⟨sel, Std.HashSet.ofList (Block.assignedVarsH ss)⟩ ss hp {}
  exact { h with
    exitsNotReserved := fun l hl => by
      simp [defInlineWith, Block.labels_of_passiveForm hpo] at hl
    measuresTyped := fun m hm => by
      simp [defInlineWith, Block.measures_of_passiveForm hpo] at hm
    readWritesDefined := fun n hn hnd =>
      Block.defined_of_mem_touchedVars (fun _ _ h => h) hg.1 hn hnd
    defsUndefined := fun n hn => h.defsUndefined n (hdv false ▸ hn)
    definedVarsNotReserved := fun n hn => h.definedVarsNotReserved n (hdv false ▸ hn)
    defUseOk := hg.1
    initTypesInhabited := fun ty hty => h.initTypesInhabited ty (hit ▸ hty)
    fvarTypesOk := ⟨Γ, hσ, hg.2⟩ }

/-- **The output of the inlining at a caller's choice of names is in passive form, without loops
    and calls** (on a list in passive form). -/
theorem defInlineWith_passive {norm : SubstNorm Expression}
    {sel : Std.HashMap Expression.Ident Nat} {ss : Statements}
    (hp : Block.passiveForm ss = true) :
    Block.noLoops (defInlineWith norm sel ss) = true ∧
      Statements.noCalls (defInlineWith norm sel ss) = true ∧
      Block.passiveForm (defInlineWith norm sel ss) = true := by
  have hp' := (walk_shape norm
    ⟨sel, Std.HashSet.ofList (Block.assignedVarsH ss)⟩ ss hp {}).1
  exact ⟨Block.passiveForm_allSubstmts (fun _ => rfl) (fun _ _ _ => rfl) hp',
    Block.passiveForm_allSubstmts (fun _ => rfl) (fun _ _ _ => rfl) hp', hp'⟩

/-- **The inlining at a caller's choice of names over-approximates the traces of a Core statement
    list**: `defInline_overapproximatesTraces` for `defInlineWith norm (sel ss)`, under the same
    hypotheses on `norm` and for every choice `sel` of the names to substitute, which may depend
    on the list. -/
theorem defInlineWith_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) {norm : SubstNorm Expression}
    {sel : Statements → Std.HashMap Expression.Ident Nat}
    {Q : Imperative.Env Expression → Prop}
    (hN : ∀ ρ, Q ρ → SubstNormLawT (P := Expression) ρ.factory norm)
    (hS : DefInlineSynLaws Expression norm) :
    OverapproximatesTracesUptoWhen (Trace.WeakensAssumes evalInterp) (fun ρ ρ' => ρ = ρ' ∧ Q ρ)
      (· = ·) (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss => some (defInlineWith norm (sel ss) ss))
      (fun ss => Block.noLoops ss = true ∧ Statements.noCalls ss = true ∧
        Block.passiveForm ss = true) params params := by
  intro ss st' hT ⟨hss, hnc, hp⟩ ρ₀ _ ⟨rfl, hq⟩ hwf
  cases hT
  obtain ⟨σ₀, F⟩ := ρ₀
  have hC : WellFormedStore σ₀ F := hwf.storeWellDefined
  have hWB := hwf.bool
  have hL : DefInlineLaws F norm :=
    ⟨coreEvaluator_WellFormedSemanticEvalExprCongr F,
      WP.coreEvaluator_WellFormedSemanticEvalSubstExprs F, hS.norm_fvars, hS.norm_typed, hN _ hq⟩
  obtain ⟨Γ, hΓ, hA⟩ := hwf.fvarTypesOk
  refine ⟨fun cfg trace h => ?_, fun ρ' trace h => ?_, fun l ρ' trace h => ?_,
    blockInitEnvWF_defInlineWith hS hp hwf⟩
  all_goals have h' := star_evalE h hnc
  · rcases Classical.em (trace = []) with rfl | htr
    · exact ⟨_, [], .refl _, .nil⟩
    obtain ⟨evs', hb, hm⟩ := defInlineWith_reach_rel hL hp hC hΓ hA (star_breach h' htr)
    obtain ⟨cfg', hc⟩ := breach_star hWB hb
    exact ⟨cfg', evs', star_core π hc, GFEvRel.weakensAssumes hm⟩
  all_goals
    have hE := starE_preserves_factory h'
    obtain ⟨evs', hb, hm⟩ := defInlineWith_run_rel hL hp hC hΓ hA
      (by first | exact star_brun.1 h' | exact star_brun.2 h')
    refine ⟨_, evs', star_core π (brun_star hWB hb), ?_, GFEvRel.weakensAssumes hm⟩
    cases ρ'
    exact hE ▸ rfl

/-- **The inlining at a caller's choice of names followed by the erasure of unread definitions
    over-approximates the traces of a Core statement list in passive form**:
    `defInline_deadDefElimH_overapproximatesTraces` for `defInlineWith norm (sel ss)`. -/
theorem defInlineWith_deadDefElimH_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) {norm : SubstNorm Expression}
    {sel : Statements → Std.HashMap Expression.Ident Nat}
    {Q : Imperative.Env Expression → Prop}
    (hN : ∀ ρ, Q ρ → SubstNormLawT (P := Expression) ρ.factory norm)
    (hS : DefInlineSynLaws Expression norm) :
    OverapproximatesTracesUptoWhen
      (RComp (Trace.WeakensAssumes evalInterp) (List.Rel₂ DDEventRel))
      (fun ρ ρ' => ρ = ρ' ∧ Q ρ) (RComp (· = ·) DDOut)
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss => some (defInlineWith norm (sel ss) ss) >>=
        fun ss => some (Imperative.DeadDefElim.deadDefElimH [] ss))
      (fun ss => Block.noLoops ss = true ∧ Statements.noCalls ss = true ∧
        Block.passiveForm ss = true) params params :=
  OverapproximatesTracesUptoWhen.comp_eq_right
    (fun _ _ h hp => Option.some.inj h ▸ (defInlineWith_passive hp.2.2).imp_right (·.1))
    (defInlineWith_overapproximatesTraces π params hN hS)
    (deadDefElimH_overapproximatesTraces π params)

/-- **The output of the inlining is well formed from every environment the input is**: on a list
    in passive form, the gate `BlockInitEnvWF` of the input gives that of the output. -/
theorem blockInitEnvWF_defInline {norm : SubstNorm Expression}
    (hS : DefInlineSynLaws Expression norm) {params : InitEnvWFParams} {ss : Statements}
    {ρ : Imperative.Env Expression} (hp : Block.passiveForm ss = true)
    (h : BlockInitEnvWF params ss ρ) :
    BlockInitEnvWF params (defInline norm ss) ρ :=
  blockInitEnvWF_defInlineWith hS hp h

/-! ## The trace over-approximation -/

/-- **The inlining of single-use definitions over-approximates the traces of a Core statement
    list.**  Let the substituting normalization `norm` keep the value of the substituted
    expression in the stores typing its annotated occurrences (`SubstNormLawT`) under the factory
    of every environment satisfying `Q` (`hN`) and add no free variable, annotated occurrence or
    operator (`hS`).  For a Core statement list `ss` in passive form (`Block.passiveForm`: only
    `init`, `assume`, `assert`, `cover` and `ite *`, the shape of the SSA phase's output), and
    every initial environment `ρ₀` satisfying `Q` and `BlockInitEnvWF params ss`:
    * every finite trace of `ss` from `ρ₀` has a trace of `defInline norm ss` from `ρ₀` whose
      assumptions are weakened (`Trace.WeakensAssumes evalInterp`);
    * every terminating or exiting run of `ss` from `ρ₀` has a run of `defInline norm ss` from
      `ρ₀` ending in the same way, in the same final environment, with such a trace;
    * `defInline norm ss` satisfies `BlockInitEnvWF params` at `ρ₀`. -/
theorem defInline_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) {norm : SubstNorm Expression}
    {Q : Imperative.Env Expression → Prop}
    (hN : ∀ ρ, Q ρ → SubstNormLawT (P := Expression) ρ.factory norm)
    (hS : DefInlineSynLaws Expression norm) :
    OverapproximatesTracesUptoWhen (Trace.WeakensAssumes evalInterp) (fun ρ ρ' => ρ = ρ' ∧ Q ρ)
      (· = ·) (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss => some (defInline norm ss))
      (fun ss => Block.noLoops ss = true ∧ Statements.noCalls ss = true ∧
        Block.passiveForm ss = true) params params :=
  defInlineWith_overapproximatesTraces (sel := fun ss => countB {} ss) π params hN hS

/-! ## Composition with the SSA phase, guard forwarding and the erasure of unread definitions -/

/-- **The inlining followed by the erasure of unread definitions over-approximates the traces of a
    Core statement list in passive form**, under the hypotheses of
    `defInline_overapproximatesTraces`: traces are related by the composition of
    `Trace.WeakensAssumes evalInterp` and `List.Rel₂ DDEventRel`, and final environments by the
    composition of equality and `DDOut`. -/
theorem defInline_deadDefElimH_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) {norm : SubstNorm Expression}
    {Q : Imperative.Env Expression → Prop}
    (hN : ∀ ρ, Q ρ → SubstNormLawT (P := Expression) ρ.factory norm)
    (hS : DefInlineSynLaws Expression norm) :
    OverapproximatesTracesUptoWhen
      (RComp (Trace.WeakensAssumes evalInterp) (List.Rel₂ DDEventRel))
      (fun ρ ρ' => ρ = ρ' ∧ Q ρ) (RComp (· = ·) DDOut)
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss => some (defInline norm ss) >>=
        fun ss => some (Imperative.DeadDefElim.deadDefElimH [] ss))
      (fun ss => Block.noLoops ss = true ∧ Statements.noCalls ss = true ∧
        Block.passiveForm ss = true) params params :=
  defInlineWith_deadDefElimH_overapproximatesTraces (sel := fun ss => countB {} ss) π params hN hS

/-- **Guard forwarding, the inlining and the erasure of unread definitions over-approximate the
    traces of a Core statement list in passive form**, under the hypotheses of
    `defInline_overapproximatesTraces`, from equal initial environments satisfying `Q`: traces are
    related by the composition of the three trace relations, and final environments by the
    composition of two equalities and `DDOut`. -/
theorem guardFwd_defInline_deadDefElimH_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) {norm : SubstNorm Expression}
    {Q : Imperative.Env Expression → Prop}
    (hN : ∀ ρ, Q ρ → SubstNormLawT (P := Expression) ρ.factory norm)
    (hS : DefInlineSynLaws Expression norm) :
    OverapproximatesTracesUptoWhen
      (RComp (Trace.WeakensAssumes evalInterp)
        (RComp (Trace.WeakensAssumes evalInterp) (List.Rel₂ DDEventRel)))
      (fun ρ ρ' => ρ = ρ' ∧ Q ρ) (RComp (· = ·) (RComp (· = ·) DDOut))
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss => some (guardFwd ss) >>= fun ss => some (defInline norm ss) >>=
        fun ss => some (Imperative.DeadDefElim.deadDefElimH [] ss))
      (fun ss => Block.noLoops ss = true ∧ Statements.noCalls ss = true ∧
        Block.passiveForm ss = true) params params :=
  OverapproximatesTracesUptoWhen.comp_eqOn_right (fun _ _ h => h.1 ▸ h.2)
    (fun _ _ h hp => Option.some.inj h ▸
      (guardFwd_noLoops_noCalls hp.2.2).imp_right fun h => ⟨h, guardFwd_passive hp.2.2⟩)
    ((guardFwd_overapproximatesTraces π params).mono_in fun _ _ h => h.1)
    (defInline_deadDefElimH_overapproximatesTraces π params hN hS)

/-- **The SSA phase, guard forwarding, the inlining and the erasure of unread definitions
    over-approximate the traces of a guarded statement list**, under the hypotheses and the
    precondition of `ssa_overapproximatesTraces`, for a substituting
    normalization `norm` that keeps the value of the substituted expression in the stores typing its
    annotated occurrences (`SubstNormLawT`) under the factory of every environment satisfying `Q`
    and a `Q` that every target environment of the entry relation satisfies (`hQ`). Initial
    environments are related by the entry renaming (`SSAEntryRel`); traces by the composition of the
    four trace relations; final environments by the composition of the factory equality of the SSA
    phase, two equalities and `DDOut`. -/
theorem ssa_guardFwd_defInline_deadDefElimH_overapproximatesTraces
    (π : String → Option Procedure) (params : InitEnvWFParams)
    (hp : ∀ p ∈ params.prefixIdents, '@' ∉ p.toList) (fac : Lambda.Factory CoreLParams)
    (G : WP.IdSet Expression) (tys : WP.Tys Expression) (xs : List Expression.Ident)
    (al : List (Expression.Ident × Expression.Ident)) (hal : ∀ q ∈ al, q.2 ∈ xs)
    (ss₀ : Statements) {norm : SubstNorm Expression}
    {Q : Imperative.Env Expression → Prop}
    (hN : ∀ ρ, Q ρ → SubstNormLawT (P := Expression) ρ.factory norm)
    (hS : DefInlineSynLaws Expression norm)
    (hQ : ∀ ρ ρ', WP.SSAEntryRel fac G tys xs al ss₀ ρ ρ' → Q ρ') :
    OverapproximatesTracesUptoWhen
      (RComp (Trace.WeakensAssumes evalInterp) (RComp (Trace.WeakensAssumes evalInterp)
        (RComp (Trace.WeakensAssumes evalInterp) (List.Rel₂ DDEventRel))))
      (WP.SSAEntryRel fac G tys xs al ss₀)
      (RComp (fun ρ ρ' => ρ'.factory = ρ.factory) (RComp (· = ·) (RComp (· = ·) DDOut)))
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss : Statements => (WP.ssaEntry fac G tys xs al ss).toOption.map (·.2.out) >>=
        fun ss : Statements => some (guardFwd ss) >>=
          fun ss : Statements => some (defInline norm ss) >>=
            fun ss : Statements => some (Imperative.DeadDefElim.deadDefElimH [] ss))
      (fun ss : Statements => ss = ss₀ ∧ Block.treeForm ss = true ∧ Block.armsHaveChecks ss = true ∧
        ∀ x ∈ Block.freeVars ss, x ∈ xs ∨ x ∈ al.map (·.1)) params params :=
  OverapproximatesTracesUptoWhen.comp_eqOn_right hQ
    (fun _ _ h hpre => WP.ssaEntry_passive h hpre.2.1)
    (WP.ssa_overapproximatesTraces π params hp fac G tys xs al hal ss₀)
    (guardFwd_defInline_deadDefElimH_overapproximatesTraces π params hN hS)

/-! ## The pipeline phase -/

/-- A run of `defInlinePipelinePhase` on `program` is a run of
    `defInlineProgram (.after addFold)`. -/
theorem defInlinePipelinePhase_ok (program : Program) (s : Transform.CoreTransformState) :
    (defInlinePipelinePhase.transform program).run s =
      (defInlineProgram (.after addFold) program).run s :=
  (rfl)

/-- **The inlining transform rewrites each procedure body.**  Let a run of `defInlineProgram norm`
    on the program `prog` succeed with `out`, and let `q` be a procedure of `prog` with structured
    body `ss`.  Then `out` contains the procedure with body `defInline norm ss`, whose traces
    over-approximate those of `ss` when `ss` is in passive form
    (`defInline_overapproximatesTraces`). -/
theorem defInlineProgram_over {norm : SubstNorm Expression} {prog out : Program}
    {s s' : Transform.CoreTransformState} {b : Bool}
    (h : (defInlineProgram norm prog).run s = (.ok (b, out), s')) {q : Procedure}
    {md : Imperative.MetaData Expression} {ss : Statements} (hq : Decl.proc q md ∈ prog.decls)
    {opq : Bool} (hb : q.body = .structured ss opq) :
    Decl.proc { q with body := .structured (defInline norm ss) opq } md ∈ out.decls := by
  cases h
  exact Program.mapStructuredBodies_mem hq hb

end -- public section

end DefInline
end Core
