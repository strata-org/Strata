/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Simplify.FoldFactory
public import Strata.DL.Lambda.Denote.ReachesModMeta
import all Strata.Transform.Simplify.Expr
import all Strata.Transform.Simplify.FoldFactory
import all Strata.Transform.FunctionInlining
import all Strata.DL.Lambda.Denote.ReachesModMeta
import all Strata.DL.Lambda.Denote.Assumptions
import all Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import Strata.DL.Lambda.OperationalSemanticsProps
import Strata.DL.Lambda.LExprDenoteEval

/-! # Simplifying an expression preserves its meaning

Simplify's expression rewrites are steps of Lambda's reduction relation `Step` under the
factory it folds with: an expanded call is the right-hand side of `Step.expand_fn`, and
folding is `LExpr.eval`, which `eval_StepStar` turns into a sequence of steps. So the
denotation of an expression is preserved by `StepStar.denote_preserved`
(`ReachesModMeta.preserves`), under a model of the fold factory, which a model of the
procedure's factory gives (`Interp.withoutInline`).

* `simplifyExpr_preserves`: simplifying an expression in a sound context preserves its
  meaning.
* `simplifyExpr_denoteEval`: the same under Core's evaluator. In a store that binds every
  variable the context types, simplifying an annotated expression leaves its value
  unchanged. The statement-level proofs use this form.
* `simplifyExpr_inv`: a property of expressions that every reduction under the fold factory
  keeps, in an environment holding some of the recorded values, simplifying keeps.
* `simplifyExpr_namesIn`: simplifying introduces no free variable beyond those of the
  context's recorded values.
* `CtxSound`: what that assumes of a context. Its fold factory is the factory with the
  `inline` attribute weakened, it satisfies the assumptions of the denotational semantics,
  and every value the context has recorded is well-formed and denotes what its variable
  denotes.
-/

namespace Core.Simplify

open Lambda

/-- `stripInline` changes nothing `inlineCallBody` reads. -/
private theorem inlineCallBody_stripInline (c : List String) (fn : LFunc CoreLParams)
    (opExpr : Expression.Expr) (args : List Expression.Expr) :
    Strata.inlineCallBody (stripInline c fn) opExpr args =
      Strata.inlineCallBody fn opExpr args := by
  obtain ⟨_, h⟩ := stripInline_eq c fn
  rw [h]; rfl

/-- The fold factory of a context is its factory with `inline` weakened, and is
    well-formed. -/
def Ctx.FactoriesOK (ctx : Ctx) : Prop :=
  ctx.foldFactory = withoutInline ctx.carriers ctx.factory ∧ FactoryWF ctx.foldFactory

/-- Spending expansion budget keeps the factories as they were. -/
private theorem Ctx.FactoriesOK.spend {ctx : Ctx} (h : ctx.FactoriesOK) : ctx.spend.FactoriesOK := h

/-- Folding is a reduction under the fold factory. -/
private theorem fold_reaches {ctx : Ctx} (hok : ctx.FactoriesOK) (env : Lambda.Env CoreLParams)
    (n : Nat) (e : Expression.Expr) :
    ReachesModMeta ctx.foldFactory env e (LExpr.eval n ctx.foldFactory env e).fst :=
  ReachesModMeta.of_eval hok.2 n e

/-- An expansion `tryExpand` builds is a reduction of the call under the fold factory. -/
private theorem expansion_reaches {ctx : Ctx} (hok : ctx.FactoriesOK)
    {simp : Ctx → Expression.Expr → Expression.Expr}
    (hsimp : ∀ x, ReachesModMeta ctx.foldFactory Env.noValues x (simp ctx.spend x))
    {e opExpr : Expression.Expr} {args : List Expression.Expr} {fn : LFunc CoreLParams}
    (hc : ctx.factory.callOfLFunc e = some (opExpr, args, fn)) {r : Expression.Expr}
    (hr : (Strata.inlineCallBody fn opExpr args).map
      (fun x => fold ctx.foldFactory ctx.evalFuel (simp ctx.spend x)) = some r) :
    ReachesModMeta ctx.foldFactory Env.noValues e r := by
  have hc' : ctx.foldFactory.callOfLFunc e = some (opExpr, args, stripInline ctx.carriers fn) := by
    rw [hok.1, withoutInline_callOfLFunc, hc]; rfl
  rw [← inlineCallBody_stripInline ctx.carriers] at hr
  cases hx : Strata.inlineCallBody (stripInline ctx.carriers fn) opExpr args with
  | none => rw [hx] at hr; cases hr
  | some x =>
    rw [hx] at hr
    cases hr
    unfold Strata.inlineCallBody at hx
    split at hx
    · cases hx
    · rename_i body hb
      obtain ⟨ts, hts, rfl⟩ := (LFunc.instantiateBody?_eq_some (T := CoreLParams)).mp hx
      exact (ReachesModMeta.of_expand hc' hb hts).trans
        ((hsimp _).trans (fold_reaches hok Env.noValues _ _))

/-- `tryExpand` either leaves the expression alone or reduces it. -/
private theorem tryExpand_reaches {ctx : Ctx} (hok : ctx.FactoriesOK)
    {simp : Ctx → Expression.Expr → Expression.Expr}
    (hsimp : ctx.expandFuel ≠ 0 →
      ∀ x, ReachesModMeta ctx.foldFactory Env.noValues x (simp ctx.spend x))
    (e : Expression.Expr) :
    ReachesModMeta ctx.foldFactory Env.noValues e (tryExpand ctx simp e) := by
  unfold tryExpand
  split
  · exact .refl _
  · rename_i hfuel
    split
    · exact .refl _
    · rename_i opExpr args fn hc
      have hexp := fun r hr => expansion_reaches hok (hsimp hfuel) hc (r := r) hr
      simp only
      split
      · exact .refl _
      · split
        · cases h : (Strata.inlineCallBody fn opExpr args).map
            (fun x => fold ctx.foldFactory ctx.evalFuel (simp ctx.spend x)) with
          | none => simp only [Option.getD_none]; exact .refl _
          | some r => simp only [Option.getD_some]; exact hexp r h
        · split
          · split
            · rename_i r h
              split
              · exact hexp r h
              · exact .refl _
            · exact .refl _
          · exact .refl _

/-- `tryExpandRecursively` is a reduction under the fold factory.

Proof idea: induction on the expansion budget, then on the expression. Children are
rebuilt by reductions, and an expansion recurses only after spending budget. -/
private theorem tryExpandRecursively_reaches : ∀ (n : Nat) (ctx : Ctx), ctx.expandFuel = n →
    ctx.FactoriesOK →
    ∀ e, ReachesModMeta ctx.foldFactory Env.noValues e (tryExpandRecursively ctx e) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihn =>
  intro ctx hn hok e
  have hstep : ∀ r, ReachesModMeta ctx.foldFactory Env.noValues r (tryExpand ctx
      (fun c x => if _h : c.expandFuel < ctx.expandFuel then tryExpandRecursively c x else x)
      r) := by
    refine tryExpand_reaches hok (fun hfuel x => ?_)
    have hlt : ctx.spend.expandFuel < ctx.expandFuel := by
      simp only [Ctx.spend]; omega
    simp only [hlt, ↓reduceDIte]
    exact ihn _ (hn ▸ hlt) ctx.spend rfl hok.spend x
  induction e with
  | app m f a ihf iha =>
    rw [tryExpandRecursively]; exact (ReachesModMeta.app ihf iha).trans (hstep _)
  | eq m a b iha ihb =>
    rw [tryExpandRecursively]; exact (ReachesModMeta.eq iha ihb).trans (hstep _)
  | ite m c t f ihc iht ihf =>
    rw [tryExpandRecursively]; exact (ReachesModMeta.ite ihc iht ihf).trans (hstep _)
  | _ => rw [tryExpandRecursively]; exact hstep _

/-- The environment holding every value a context has recorded. -/
def valuesEnv (ctx : Ctx) : Lambda.Env CoreLParams := fun y => Map.find? ctx.values y

/-- What the expression lemmas assume of a context, for a fixed model (`tcInterp`,
`opInterp`) and a fixed valuation of the free variables (`fvarVal`): its factories are
related as the phase builds them, the fold factory satisfies the assumptions of the
denotational semantics, and every recorded value is well-formed and denotes the value
`fvarVal` gives its variable. -/
structure CtxSound (ctx : Ctx) (tf : @Lambda.TypeFactory CoreLParams.IDMeta)
    (tcInterp : Lambda.TyConstrInterp) (opInterp : Lambda.OpInterp tcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams tcInterp) (vt : Lambda.TyVarVal) where
  factories : ctx.FactoriesOK
  envWF : Lambda.Env.StepWF ctx.foldFactory (valuesEnv ctx)
  facWF : Lambda.Factory.WF ctx.foldFactory tf
  fWF : Lambda.Factory.StepWFOn ctx.foldFactory envWF.typed.tyMap
  fic : Lambda.Factory.InterpConsistent tcInterp opInterp ctx.foldFactory
  cic : Lambda.ConstrInterpConsistent tcInterp opInterp ctx.foldFactory
  envIC : Lambda.Env.InterpConsistentAt tcInterp opInterp fvarVal vt (valuesEnv ctx)
  /-- Every free variable of a recorded value has a type in the type map. -/
  cover : ∀ x r, valuesEnv ctx x = some r →
    r.NamesIn (fun y => (Map.find? envWF.typed.tyMap y).isSome)

section
variable {ctx : Ctx} {tf : @Lambda.TypeFactory CoreLParams.IDMeta}
  {tcInterp : Lambda.TyConstrInterp} {opInterp : Lambda.OpInterp tcInterp}
  {fvarVal : Lambda.FreeVarVal CoreLParams tcInterp} {vt : Lambda.TyVarVal}

/-- A reduction in an environment holding some of the recorded values preserves meaning. -/
private theorem CtxSound.preserves (h : CtxSound ctx tf tcInterp opInterp fvarVal vt)
    {env : Lambda.Env CoreLParams} (hsub : Env.Sub env (valuesEnv ctx))
    {e e' : Expression.Expr} (hr : ReachesModMeta ctx.foldFactory env e e') :
    Preserves ctx.foldFactory h.envWF.typed.tyMap tcInterp opInterp fvarVal vt e e' :=
  ReachesModMeta.preserves (h.envWF.restrict hsub) h.fWF h.facWF h.fic h.cic
    (h.envIC.restrict hsub) hr

/-- The empty environment holds a subset of the recorded values. -/
private theorem Env.noValues_sub : Env.Sub Env.noValues (valuesEnv ctx) := fun _ _ h => by cases h

/-- The environment of small recorded values holds a subset of the recorded values. -/
private theorem Env.smallValues_sub :
    Env.Sub (Env.smallValues ctx.foldFactory ctx.values) (valuesEnv ctx) := by
  intro x v h
  simp only [Env.smallValues, Lambda.Env.mk] at h
  split at h
  · rename_i w hw; split at h
    · cases h; exact hw
    · cases h
  · cases h

/-- The environment holding one recorded value holds a subset of the recorded values. -/
private theorem Env.oneValue_sub {x : CoreIdent} {v : Expression.Expr}
    (hx : Map.find? ctx.values x = some v) : Env.Sub (Env.oneValue x v) (valuesEnv ctx) := by
  intro y w h
  simp only [Env.oneValue, Lambda.Env.mk] at h
  split at h
  · rename_i hyx; cases h
    have hyx' : y = x := by simpa using hyx
    subst hyx'; exact hx
  · cases h

/-- **What every reduction keeps, `simplifyExpr` keeps.** A property of expressions that every
    reduction under the fold factory keeps, in an environment holding some of the recorded
    values, holds of the simplified expression when it holds of the expression: each stage of
    `simplifyExpr` is such a reduction. -/
theorem simplifyExpr_inv (hok : ctx.FactoriesOK) {Q : Expression.Expr → Prop}
    (hQ : ∀ {env : Lambda.Env CoreLParams} {e e' : Expression.Expr},
      Env.Sub env (valuesEnv ctx) → ReachesModMeta ctx.foldFactory env e e' → Q e → Q e')
    {e : Expression.Expr} (he : Q e) : Q (simplifyExpr ctx e) := by
  have hgo : ∀ d fuel tried todo next acc, Q acc →
      Q (trySubstWide.go ctx d fuel tried todo next acc) := by
    intro d fuel tried todo next acc
    fun_induction trySubstWide.go ctx d fuel tried todo next acc
    all_goals first
      | exact id
      | assumption
      | (intro hacc; rename_i ih
         simpa only [List.unattach_reverse, List.unattach_attach] using ih hacc)
      | (intro hacc; rename_i ih
         exact ih (hQ (Env.oneValue_sub (by assumption)) (fold_reaches hok _ _ _) hacc))
      | (intro hacc; rename_i ih; exact ih hacc)
  unfold simplifyExpr
  have hsimp := fun x => tryExpandRecursively_reaches _ ctx rfl hok x
  refine hQ Env.noValues_sub ((hsimp _).trans (fold_reaches hok _ _ _)) ?_
  unfold trySubstWide
  exact hgo _ _ _ _ _ _ (hQ Env.smallValues_sub (fold_reaches hok _ _ _)
    (hQ Env.noValues_sub (hsimp e) he))

/-- `trySubstWide` preserves meaning: each substitution it keeps is a reduction in the
environment holding the one value it substitutes. -/
private theorem trySubstWide_preserves (h : CtxSound ctx tf tcInterp opInterp fvarVal vt)
    (e : Expression.Expr) :
    Preserves ctx.foldFactory h.envWF.typed.tyMap tcInterp opInterp fvarVal vt e
      (trySubstWide ctx e) := by
  suffices hgo : ∀ d fuel tried todo next acc, Preserves ctx.foldFactory h.envWF.typed.tyMap
      tcInterp opInterp fvarVal vt acc (trySubstWide.go ctx d fuel tried todo next acc) by
    unfold trySubstWide; exact hgo _ _ _ _ _ _
  intro d fuel tried todo next acc
  fun_induction trySubstWide.go ctx d fuel tried todo next acc
  all_goals first
    | exact Preserves.refl _
    | assumption
    | (rename_i ih; simpa only [List.unattach_reverse, List.unattach_attach] using ih)
    | exact (h.preserves (Env.oneValue_sub (by assumption))
        (fold_reaches h.factories _ _ _)).trans (by assumption)

/-- The free variables a reduction in an environment holding some of the recorded values
    can reach are those of its source and of the recorded values. -/
private theorem CtxSound.namesIn (h : CtxSound ctx tf tcInterp opInterp fvarVal vt)
    {env : Lambda.Env CoreLParams} (hsub : Env.Sub env (valuesEnv ctx))
    {e e' : Expression.Expr} (hr : ReachesModMeta ctx.foldFactory env e e')
    (he : e.NamesIn (fun y => (Map.find? h.envWF.typed.tyMap y).isSome)) :
    e'.NamesIn (fun y => (Map.find? h.envWF.typed.tyMap y).isSome) :=
  hr.namesIn h.factories.2 (fun x r hx => h.cover x r (hsub x r hx)) he

/-- `simplifyExpr` introduces no free variable beyond those of the recorded values. -/
theorem simplifyExpr_namesIn (h : CtxSound ctx tf tcInterp opInterp fvarVal vt)
    {e : Expression.Expr} (he : e.NamesIn (fun y => (Map.find? h.envWF.typed.tyMap y).isSome)) :
    (simplifyExpr ctx e).NamesIn (fun y => (Map.find? h.envWF.typed.tyMap y).isSome) :=
  simplifyExpr_inv h.factories (fun hsub hr hq => h.namesIn hsub hr hq) he

/-- **Expression soundness.** Simplifying an expression in a sound context preserves its
meaning: the result is well-formed when the input is, has the input's types, and denotes
the same value, for every model and valuation the context is sound for.

Proof idea: each stage of `simplifyExpr` is a reduction under the fold factory, in an
environment holding some of the context's recorded values, and a sound context makes every
such reduction preserve meaning. -/
theorem simplifyExpr_preserves (h : CtxSound ctx tf tcInterp opInterp fvarVal vt)
    (e : Expression.Expr) :
    Preserves ctx.foldFactory h.envWF.typed.tyMap tcInterp opInterp fvarVal vt e
      (simplifyExpr ctx e) := by
  unfold simplifyExpr
  have hsimp := fun x => tryExpandRecursively_reaches _ ctx rfl h.factories x
  refine (h.preserves Env.noValues_sub (hsimp e)).trans
    ((h.preserves Env.smallValues_sub (fold_reaches h.factories _ _ _)).trans
    ((trySubstWide_preserves h _).trans
    (h.preserves Env.noValues_sub ((hsimp _).trans (fold_reaches h.factories _ _ _)))))
end

/-- **Expression soundness under Core's evaluator.** In a store that binds every variable
the context's type map records, at the recorded sort, simplifying an expression annotated
against that map, in a context sound for the valuation the store induces, leaves its value
unchanged. -/
theorem simplifyExpr_denoteEval {ctx : Ctx} {tf : @Lambda.TypeFactory CoreLParams.IDMeta}
    {M : Lambda.ModeledFactory CoreLParams} {σ : Lambda.ValStore CoreLParams}
    (h : CtxSound ctx tf M.model.tcInterp M.model.opInterp
      (@Lambda.ValStore.fvarVal CoreLParams M.model.tcInterp M.model.allInhabited σ)
      M.tyVarVal)
    (hmap : ∀ x τ, Map.find? h.envWF.typed.tyMap x = some τ →
      ∃ v, σ x = some v ∧ v.tc = M.model.tcInterp ∧ v.sort.toMonoTy = τ)
    {e : Expression.Expr} (hops : Lambda.OpsConsistent ctx.foldFactory e)
    (hann : Lambda.fvars_annotated_by h.envWF.typed.tyMap e)
    (hcov : e.NamesIn (fun y => (Map.find? h.envWF.typed.tyMap y).isSome))
    {v : Lambda.SemValue} (hv : e.denoteEval M σ = some v) :
    (simplifyExpr ctx e).denoteEval M σ = some v :=
  (simplifyExpr_preserves h e).denoteEval hops hann hmap hcov (simplifyExpr_namesIn h hcov) hv

end Core.Simplify
