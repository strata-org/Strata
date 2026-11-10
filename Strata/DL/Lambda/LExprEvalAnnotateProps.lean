/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprEvalFuelProps
import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.LState
import Strata.DL.Lambda.LExprEvalProps
import Strata.DL.Lambda.OperationalSemanticsProps

/-! # `LExpr.eval` does not read the type annotations of bound free variables

On a store that binds every free variable of `e` to an expression without free variables,
`LExpr.eval` returns the same result on `e` and on `e` with its free variables re-annotated
(`LExpr.annotateFvars`): it replaces every such variable by its binding before the annotation
could matter. The concrete evaluators of `shortCircuit` functions receive arguments
unevaluated, so they must commute with the re-annotation (`Factory.ShortCircuitAnnotates`).

Key definitions: `Factory.ShortCircuitAnnotates`. Key theorems: `eval_annotateFvars`.
-/

namespace Lambda
public section

variable {Tbase : LExprParams}

/-- The concrete evaluator of every `shortCircuit` function of `F`, which `LExpr.eval` applies to
    the arguments after the first unevaluated, commutes with re-annotating the free variables of
    those arguments. -/
@[expose] def Factory.ShortCircuitAnnotates [DecidableEq Tbase.IDMeta] (F : @Factory Tbase) :
    Prop :=
  ∀ (lf : LFunc Tbase), lf ∈ F.toArray →
    Strata.DL.Util.FuncAttr.hasShortCircuit lf.attr = true →
    ∀ ceval, lf.concreteEval = some ceval →
    ∀ (md : Tbase.Metadata) (a : LExpr Tbase.mono) (rest : List (LExpr Tbase.mono))
      (A : Identifier Tbase.IDMeta → Option LMonoTy),
      ceval md (a :: rest.map (LExpr.annotateFvars A)) =
        (ceval md (a :: rest)).map (LExpr.annotateFvars A)

/-- Re-annotating free variables keeps the free variables. -/
private theorem getVars_annotateFvars (A : Identifier Tbase.IDMeta → Option LMonoTy)
    (e : LExpr Tbase.mono) :
    LExpr.LExpr.getVars (e.annotateFvars A) = LExpr.LExpr.getVars e := by
  induction e <;> simp_all [LExpr.annotateFvars, LExpr.LExpr.getVars]

/-- Re-annotating an expression without free variables leaves it unchanged. -/
private theorem annotateFvars_of_getVars_nil (A : Identifier Tbase.IDMeta → Option LMonoTy)
    {e : LExpr Tbase.mono} (h : LExpr.LExpr.getVars e = []) : e.annotateFvars A = e := by
  induction e <;> simp_all [LExpr.annotateFvars, LExpr.LExpr.getVars]

/-- Re-annotating free variables keeps the top-level metadata. -/
private theorem metadata_annotateFvars (A : Identifier Tbase.IDMeta → Option LMonoTy)
    (e : LExpr Tbase.mono) : (e.annotateFvars A).metadata = e.metadata := by
  cases e <;> rfl

/-- Substituting a store that binds every free variable ignores their annotations. -/
private theorem substFvarsFromEnv_annotateFvars (env : Env Tbase)
    (A : Identifier Tbase.IDMeta → Option LMonoTy) (e : LExpr Tbase.mono)
    (hb : ∀ x ∈ LExpr.LExpr.getVars e, (env x).isSome = true) :
    LExpr.substFvarsFromEnv env (e.annotateFvars A) = LExpr.substFvarsFromEnv env e := by
  induction e with
  | fvar m x ty =>
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hb x (by simp [LExpr.LExpr.getVars]))
    simp [LExpr.annotateFvars, LExpr.substFvarsFromEnv, hv]
  | _ => simp_all [LExpr.annotateFvars, LExpr.substFvarsFromEnv, LExpr.LExpr.getVars]

/-- Splitting a re-annotated application spine gives the re-annotated head and arguments. -/
private theorem getLFuncCall_go_annotateFvars (A : Identifier Tbase.IDMeta → Option LMonoTy)
    (e : LExpr Tbase.mono) (acc : List (LExpr Tbase.mono)) :
    getLFuncCall.go (e.annotateFvars A) (acc.map (·.annotateFvars A)) =
      ((getLFuncCall.go e acc).1.annotateFvars A,
        (getLFuncCall.go e acc).2.map (·.annotateFvars A)) := by
  match e with
  | .app _ (.app _ e' a1) a2 =>
    have h := getLFuncCall_go_annotateFvars A e' ([a1, a2] ++ acc)
    simp only [List.map_append, List.map_cons, List.map_nil] at h
    simp only [LExpr.annotateFvars, getLFuncCall.go, h]
  | .app _ (.op _ _ _) _ => rfl
  | .app _ (.const _ _) _ | .app _ (.bvar _ _) _ | .app _ (.fvar _ _ _) _ => rfl
  | .app _ (.abs _ _ _ _) _ | .app _ (.quant _ _ _ _ _ _) _ => rfl
  | .app _ (.ite _ _ _ _) _ | .app _ (.eq _ _ _) _ => rfl
  | .const _ _ | .op _ _ _ | .bvar _ _ | .fvar _ _ _ | .abs _ _ _ _ => rfl
  | .quant _ _ _ _ _ _ | .ite _ _ _ _ | .eq _ _ _ => rfl

/-- A re-annotated expression is a call of the same function on the re-annotated arguments. -/
private theorem callOfLFunc_annotateFvars (F : @Factory Tbase)
    (A : Identifier Tbase.IDMeta → Option LMonoTy) (e : LExpr Tbase.mono) (b : Bool) :
    F.callOfLFunc (e.annotateFvars A) b =
      (F.callOfLFunc e b).map fun p => (p.1, p.2.1.map (·.annotateFvars A), p.2.2) := by
  have h := getLFuncCall_go_annotateFvars A e []
  simp only [List.map_nil] at h
  simp only [Factory.callOfLFunc, getLFuncCall, h]
  rcases getLFuncCall.go e [] with ⟨op, args⟩
  cases op
  case op m name ty =>
    simp only [LExpr.annotateFvars, List.length_map]
    split
    · rfl
    · split <;> rfl
  all_goals rfl

/-- Mapping the arguments of a short-circuit call maps its first and remaining arguments. -/
private theorem shortCircuitCall?_map (lf : LFunc Tbase)
    (g : LExpr Tbase.mono → LExpr Tbase.mono) (args : List (LExpr Tbase.mono)) :
    LExpr.shortCircuitCall? lf (args.map g) =
      (LExpr.shortCircuitCall? lf args).map fun p => (g p.1, p.2.1.map g, p.2.2) := by
  unfold LExpr.shortCircuitCall?
  split <;> cases args <;> cases lf.concreteEval <;> simp_all

/-- Re-annotation does not change whether an expression is a value. -/
private theorem isValue_annotateFvars (F : @Factory Tbase)
    (A : Identifier Tbase.IDMeta → Option LMonoTy) (e : LExpr Tbase.mono) :
    LExpr.isValue F (e.annotateFvars A) = LExpr.isValue F e := by
  by_cases h : LExpr.LExpr.getVars e = []
  · rw [annotateFvars_of_getVars_nil A h]
  · have h1 : LExpr.isValue F e = false :=
      Bool.eq_false_iff.2 fun hv => h (isValue_getVars_nil F e hv)
    have h2 : LExpr.isValue F (e.annotateFvars A) = false := Bool.eq_false_iff.2 fun hv =>
      h ((getVars_annotateFvars A e).symm.trans (isValue_getVars_nil F _ hv))
    rw [h1, h2]

section

variable [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta]
  [Traceable LExpr.EvalProvenance Tbase.Metadata]

/-- On a store of values without free variables that binds every free variable of `e`,
    the result of `eval` has no free variables. -/
private theorem eval_getVars_nil
    (hIdent : ∀ a b : Tbase.Identifier, a.name = b.name → a = b)
    (n : Nat) (F : @Factory Tbase) (env : Env Tbase) (hWF : FactoryWF F)
    (henv : ∀ x v, env x = some v → LExpr.LExpr.getVars v = []) (e : LExpr Tbase.mono)
    (hbound : ∀ x ∈ LExpr.LExpr.getVars e, (env x).isSome = true) :
    LExpr.LExpr.getVars (LExpr.eval n F env e).fst = [] := by
  refine List.eq_nil_iff_forall_not_mem.2 fun y hy => ?_
  rcases eval_getVars_origin hIdent F env n e hWF (Env.idempotent_of_getVars_nil henv) y hy with
    ⟨hy, hnone⟩ | ⟨x, v, -, hv, hyv⟩
  · exact absurd (hbound y hy) (by simp [hnone])
  · rw [henv x v hv] at hyv
    cases hyv

/-- `evalShortCircuit` ignores the annotations of bound free variables of the call, given that
    `eval` at the same fuel ignores those of every expression whose free variables are bound. -/
private theorem evalShortCircuit_annotateFvars
    (hIdent : ∀ a b : Tbase.Identifier, a.name = b.name → a = b)
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase) (hWF : FactoryWF F)
    (hSC : Factory.ShortCircuitAnnotates F)
    (henv : ∀ x v, env x = some v → LExpr.LExpr.getVars v = [])
    (A : Identifier Tbase.IDMeta → Option LMonoTy) (e op a : LExpr Tbase.mono)
    (rest : List (LExpr Tbase.mono)) (lf : LFunc Tbase) (hmem : lf ∈ F.toArray)
    (hsc : Strata.DL.Util.FuncAttr.hasShortCircuit lf.attr = true)
    (ceval : Tbase.Metadata → List (LExpr Tbase.mono) → Option (LExpr Tbase.mono))
    (hce : lf.concreteEval = some ceval)
    (hb : ∀ x ∈ a :: rest, ∀ y ∈ LExpr.LExpr.getVars x, (env y).isSome = true)
    (ih : ∀ e', (∀ x ∈ LExpr.LExpr.getVars e', (env x).isSome = true) →
      LExpr.eval n' F env (e'.annotateFvars A) = LExpr.eval n' F env e') :
    LExpr.evalShortCircuit n' F env (e.annotateFvars A) op (a.annotateFvars A)
        (rest.map (·.annotateFvars A)) ceval =
      LExpr.evalShortCircuit n' F env e op a rest ceval := by
  have ha := ih a (hb a List.mem_cons_self)
  have hrest : (rest.map (·.annotateFvars A)).map (fun x => (LExpr.eval n' F env x).fst) =
      rest.map (fun x => (LExpr.eval n' F env x).fst) := by
    simp only [List.map_map]
    exact List.map_congr_left fun x hx =>
      congrArg Prod.fst (ih x (hb x (List.mem_cons_of_mem _ hx)))
  simp only [LExpr.evalShortCircuit, metadata_annotateFvars, ha, hSC lf hmem hsc ceval hce, hrest]
  cases hv : LExpr.isValue F (LExpr.eval n' F env a).fst
  · rfl
  · cases hc : ceval e.metadata ((LExpr.eval n' F env a).fst :: rest) with
    | none => rfl
    | some e' =>
      have hb' : ∀ z ∈ LExpr.LExpr.getVars e', (env z).isSome = true := fun z hz => by
        obtain ⟨x, hx, hzx⟩ :=
          (hWF.lfuncs_wf lf hmem).concreteEval_freeVars ceval hce _ _ e' hc z hz
        rcases List.mem_cons.1 hx with rfl | hx
        · rw [eval_getVars_nil hIdent n' F env hWF henv a (hb a List.mem_cons_self)] at hzx
          cases hzx
        · exact hb x (List.mem_cons_of_mem _ hx) z hzx
      simp only [Option.map_some, ↓reduceIte, ih e' hb']

/-- `evalCore` ignores the annotations of the bound free variables of an expression with free
    variables, given that `eval` at the same fuel ignores those of every expression whose free
    variables are bound. -/
private theorem evalCore_annotateFvars
    (hIdent : ∀ a b : Tbase.Identifier, a.name = b.name → a = b)
    (n' : Nat) (F : @Factory Tbase) (env : Env Tbase) (hWF : FactoryWF F)
    (henv : ∀ x v, env x = some v → LExpr.LExpr.getVars v = [])
    (A : Identifier Tbase.IDMeta → Option LMonoTy) (e : LExpr Tbase.mono)
    (hbound : ∀ x ∈ LExpr.LExpr.getVars e, (env x).isSome = true)
    (h0 : LExpr.LExpr.getVars e ≠ [])
    (ih : ∀ e', (∀ x ∈ LExpr.LExpr.getVars e', (env x).isSome = true) →
      LExpr.eval n' F env (e'.annotateFvars A) = LExpr.eval n' F env e') :
    LExpr.evalCore n' F env (e.annotateFvars A) = LExpr.evalCore n' F env e := by
  have hsub : ∀ e', (∀ x ∈ LExpr.LExpr.getVars e', x ∈ LExpr.LExpr.getVars e) →
      LExpr.eval n' F env (e'.annotateFvars A) = LExpr.eval n' F env e' :=
    fun e' h => ih e' fun x hx => hbound x (h x hx)
  have hnil : ∀ e', (∀ x ∈ LExpr.LExpr.getVars e', x ∈ LExpr.LExpr.getVars e) →
      LExpr.LExpr.getVars (LExpr.eval n' F env e').fst = [] :=
    fun e' h => eval_getVars_nil hIdent n' F env hWF henv e' fun x hx => hbound x (h x hx)
  have h0' : LExpr.LExpr.getVars (e.annotateFvars A) ≠ [] := (getVars_annotateFvars A e).symm ▸ h0
  have hne : ∀ X Y : LExpr Tbase.mono, LExpr.LExpr.getVars X ≠ [] →
      LExpr.LExpr.getVars Y = [] → LExpr.eqModuloMeta X Y = false :=
    fun X Y hX hY => Bool.eq_false_iff.2 fun h => hX ((gv_eq_of_eqModuloMeta X Y h).trans hY)
  have hsubst := substFvarsFromEnv_annotateFvars env A e hbound
  cases e with
  | const _ _ | op _ _ _ | bvar _ _ => exact absurd rfl h0
  | fvar m x ty =>
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hbound x (by simp [LExpr.LExpr.getVars]))
    simp only [LExpr.annotateFvars, LExpr.evalCore, hv]
  | abs m nm ty body =>
    simp only [LExpr.annotateFvars] at hsubst
    simp only [LExpr.annotateFvars, LExpr.evalCore, hsubst]
  | quant m qk nm ty tr body =>
    simp only [LExpr.annotateFvars] at hsubst
    simp only [LExpr.annotateFvars, LExpr.evalCore, hsubst]
  | app m e1 e2 =>
    simp only [LExpr.annotateFvars] at h0'
    have h1 := hsub e1 fun x hx => by simp [LExpr.LExpr.getVars, hx]
    have h2 := hsub e2 fun x hx => by simp [LExpr.LExpr.getVars, hx]
    have hn1 := hnil e1 fun x hx => by simp [LExpr.LExpr.getVars, hx]
    have hn2 := hnil e2 fun x hx => by simp [LExpr.LExpr.getVars, hx]
    simp only [LExpr.annotateFvars, LExpr.evalCore, LExpr.evalApp, h1, h2]
    split
    · rename_i mAbs nm ty body heq
      rw [heq] at hn1
      have hY : ∀ s : Tbase.Metadata → LExpr Tbase.mono,
          (∀ md, LExpr.LExpr.getVars (s md) = []) → LExpr.LExpr.getVars (LExpr.subst s body) = [] :=
        fun s hs => List.eq_nil_iff_forall_not_mem.2 fun y hy => by
          rcases getVars_substK_mem 0 s body y hy with hb | ⟨md, hmd⟩
          · exact absurd hb ((show LExpr.LExpr.getVars body = [] from hn1) ▸ List.not_mem_nil)
          · exact absurd hmd ((hs md) ▸ List.not_mem_nil)
      rw [hne _ _ h0' (hY _ ?_), hne _ _ h0 (hY _ ?_)]
      · rfl
      all_goals exact fun _ => (getVars_replaceMetadata1 _ _).trans hn2
    · rw [hne _ _ h0' ?_, hne _ _ h0 ?_]
      · rfl
      all_goals simp only [LExpr.LExpr.getVars, hn1, hn2, List.append_nil]
  | eq m e1 e2 =>
    have h1 := hsub e1 fun x hx => by simp [LExpr.LExpr.getVars, hx]
    have h2 := hsub e2 fun x hx => by simp [LExpr.LExpr.getVars, hx]
    simp only [LExpr.annotateFvars, LExpr.evalCore, LExpr.evalEq, h1, h2]
  | ite m c t f =>
    have h1 := hsub c fun x hx => by simp [LExpr.LExpr.getVars, hx]
    have h2 := hsub t fun x hx => by simp [LExpr.LExpr.getVars, hx]
    have h3 := hsub f fun x hx => by simp [LExpr.LExpr.getVars, hx]
    simp only [LExpr.annotateFvars, LExpr.evalCore, LExpr.evalIte, h1, h2, h3]

end

variable [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta]
  [Traceable LExpr.EvalProvenance Tbase.Metadata]

/-- **`eval` ignores the annotations of bound free variables.** On a well-formed factory whose
    short-circuit evaluators commute with re-annotation, and a store whose values have no free
    variables and that binds every free variable of `e`, evaluating `e` with its free variables
    re-annotated by `A` gives the result of evaluating `e`. -/
theorem eval_annotateFvars
    (hIdent : ∀ a b : Tbase.Identifier, a.name = b.name → a = b)
    (n : Nat) (F : @Factory Tbase) (env : Env Tbase) (hWF : FactoryWF F)
    (hSC : Factory.ShortCircuitAnnotates F)
    (henv : ∀ x v, env x = some v → LExpr.LExpr.getVars v = [])
    (A : Identifier Tbase.IDMeta → Option LMonoTy) (e : LExpr Tbase.mono)
    (hbound : ∀ x ∈ LExpr.LExpr.getVars e, (env x).isSome = true) :
    LExpr.eval n F env (e.annotateFvars A) = LExpr.eval n F env e := by
  induction n generalizing e with
  | zero =>
    simp only [LExpr.eval, isValue_annotateFvars, substFvarsFromEnv_annotateFvars env A e hbound]
    split
    · rename_i hv
      rw [annotateFvars_of_getVars_nil A (isValue_getVars_nil F e hv)]
    · rfl
  | succ n' ih =>
    by_cases h0 : LExpr.LExpr.getVars e = []
    · rw [annotateFvars_of_getVars_nil A h0]
    have hve : LExpr.isValue F e = false :=
      Bool.eq_false_iff.2 fun hv => h0 (isValue_getVars_nil F e hv)
    simp only [LExpr.eval, isValue_annotateFvars, hve, callOfLFunc_annotateFvars,
      metadata_annotateFvars, Bool.false_eq_true, ↓reduceIte]
    cases hc : F.callOfLFunc e with
    | none => exact evalCore_annotateFvars hIdent n' F env hWF henv A e hbound h0 ih
    | some p =>
      obtain ⟨op, args, lf⟩ := p
      have hargs : ∀ x ∈ args, ∀ y ∈ LExpr.LExpr.getVars x, (env y).isSome = true :=
        fun x hx y hy => hbound y (callOfLFunc_getVars_args F e op args lf hc x hx y hy)
      have hmap : (args.map (·.annotateFvars A)).map (LExpr.eval n' F env) =
          args.map (LExpr.eval n' F env) := by
        simp only [List.map_map]
        exact List.map_congr_left fun x hx => ih x (hargs x hx)
      simp only [Option.map_some, shortCircuitCall?_map]
      cases hs : LExpr.shortCircuitCall? lf args with
      | none => simp only [Option.map_none, hmap]
      | some q =>
        obtain ⟨a, rest, ceval⟩ := q
        have hsc : Strata.DL.Util.FuncAttr.hasShortCircuit lf.attr = true := by
          unfold LExpr.shortCircuitCall? at hs
          split at hs
          · assumption
          · cases hs
        obtain ⟨rfl, hce⟩ := LExpr.shortCircuitCall?_some hs
        exact evalShortCircuit_annotateFvars hIdent n' F env hWF hSC henv A e op a rest lf
          (callOfLFunc_func_mem F e op _ lf false hc) hsc ceval hce hargs ih

end -- public section
end Lambda
