/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Simplify.Precondition
public import Strata.Transform.Simplify.StmtShape
import all Strata.Transform.Simplify.Precondition
import all Strata.Transform.Simplify.SimpRun
import all Strata.Transform.Simplify.ExprCorrect
import all Strata.Transform.Simplify.Expr
import all Strata.Transform.Simplify
import all Strata.Transform.Simplify.StmtShape
import all Strata.DL.Lambda.Denote.ReachesModMeta
import all Strata.DL.Lambda.Denote.Assumptions
import Strata.DL.Lambda.OperationalSemanticsProps
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.DL.Lambda.LExprWFProps
import Strata.Util.ListMapProps
import all Strata.Util.ListMap
import Strata.DL.Imperative.StmtProps
import Strata.DL.Imperative.CmdProps

/-! # The simplification pass keeps a body well-formed

Simplify rewrites a body's expressions and records variables' values to substitute later. Its
output is def-use well-formed, and its free-variable annotations agree with the typing in scope,
when the body's are and the factory brings in only its own operators (`Factory.OpsClosed`):

* a rewrite of an expression is a reduction under the fold factory, in an environment holding
  some of the recorded values, and a reduction mentions only operators of the expression, of the
  values and of the factory (`ReachesModMeta.opsIn`), and only free variables of the expression
  and of the values, with their annotations (`ReachesModMeta.namesIn`,
  `ReachesModMeta.annotated`), so `simplifyExpr` keeps an expression's free variables defined
  and annotated, and its operators declared, when the recorded values are
  (`simplifyExpr_outExprOK`);
* a recorded value mentions only variables in scope where it is recorded, and leaves the
  recorded values when one of its variables leaves scope: a block forgets the values that
  mention what it declares, and a branch keeps only the values that mention nothing its arms
  declare (`simpStmts_wf`).
-/

namespace Core.Simplify

open Lambda Imperative

/-! ## Expressions -/

/-- `e` passes the output check from the defined names `D`, the declared functions `fs` and the
    typing `Γ`: its operators are declared, and each of its free-variable occurrences names a
    defined variable and carries the monotype `Γ` gives it. -/
def OutExprOK (fs D : CoreIdent → Bool) (Γ : VarTyping Expression) (e : Expression.Expr) :
    Prop :=
  e.OpsIn (fun o => fs o = true) ∧
    ∀ y a, (y, a) ∈ LExpr.freeVars e → D y = true ∧ ∃ t, a = some t ∧ Γ y = some (.forAll [] t)

/-- Every type `Γ` gives is a monotype. -/
def MonoTyping (Γ : VarTyping Expression) : Prop :=
  ∀ y t, Γ y = some t → ∃ τ, t = .forAll [] τ

/-- The type map giving each name of `N` the monotype `Γ` gives it, if any. -/
def monoTyMap (Γ : VarTyping Expression) (N : List CoreIdent) : Map CoreIdent LMonoTy :=
  N.filterMap fun y => ((Γ y).bind LTy.toMonoType?).map fun τ => (y, τ)

/-- The type map of `N` gives each name of `N` the monotype `Γ` gives it. -/
private theorem find?_monoTyMap (Γ : VarTyping Expression) :
    ∀ (N : List CoreIdent) (y : CoreIdent),
      Map.find? (monoTyMap Γ N) y = if y ∈ N then (Γ y).bind LTy.toMonoType? else none := by
  intro N
  induction N with
  | nil => intro y; rfl
  | cons z N ih =>
    intro y
    unfold monoTyMap at ih ⊢
    rw [List.filterMap_cons]
    cases hz : (Γ z).bind LTy.toMonoType? with
    | none =>
      simp only [Option.map_none]
      rw [ih y]
      by_cases hyz : y = z
      · subst hyz; simp [hz]
      · simp [hyz]
    | some w =>
      simp only [Option.map_some, Map.find?]
      split
      · rename_i hzy; subst hzy; simp [hz]
      · rename_i hzy
        rw [ih y]
        have : y ≠ z := fun h => hzy h.symm
        simp [this]

/-- A type whose monotype is `τ` is the scheme of `τ`. -/
private theorem eq_forAll_of_bind {t? : Option Expression.Ty} {τ : LMonoTy}
    (h : t?.bind LTy.toMonoType? = some τ) : t? = some (.forAll [] τ) := by
  rcases t? with _ | ⟨vs, τ'⟩
  · cases h
  · cases vs with
    | nil => simp only [Option.bind_some, LTy.toMonoType?, Option.some.injEq] at h; rw [h]
    | cons => simp [LTy.toMonoType?] at h

/-- The names of the free variables of a context's recorded values. -/
private def valueVarNames (ctx : Ctx) : List CoreIdent :=
  ctx.values.toList.flatMap fun p => (LExpr.freeVars p.2).map Prod.fst

/-- A reduction under the fold factory, in an environment holding some of the recorded values,
    keeps an expression passing the output check when the recorded values pass it. -/
private theorem reach_outExprOK {ctx : Ctx} (hok : ctx.FactoriesOK)
    (hcl : ctx.foldFactory.OpsClosed) (hstep : ∀ tyMap, Factory.StepWFOn ctx.foldFactory tyMap)
    {fs D : CoreIdent → Bool} {Γ : VarTyping Expression}
    (hfs : ∀ o : CoreIdent, o.name ∈ ctx.foldFactory → fs o = true)
    (hV : ∀ x r, (x, r) ∈ ctx.values.toList → OutExprOK fs D Γ r)
    {env : Lambda.Env CoreLParams} (hsub : Env.Sub env (valuesEnv ctx))
    {e e' : Expression.Expr} (hr : ReachesModMeta ctx.foldFactory env e e')
    (he : OutExprOK fs D Γ e) : OutExprOK fs D Γ e' := by
  have hV' : ∀ x r, env x = some r → (x, r) ∈ ctx.values.toList := fun x r hx =>
    Map.find?_mem _ _ _ (hsub x r hx)
  refine ⟨ReachesModMeta.opsIn hcl hfs (fun x r hx => (hV x r (hV' x r hx)).1) hr he.1, ?_⟩
  let N := (LExpr.freeVars e).map Prod.fst ++ valueVarNames ctx
  have hin : ∀ r : Expression.Expr, OutExprOK fs D Γ r →
      (∀ y a, (y, a) ∈ LExpr.freeVars r → y ∈ N) →
      r.NamesIn (fun y => D y = true ∧ (Map.find? (monoTyMap Γ N) y).isSome) ∧
        fvars_annotated_by (monoTyMap Γ N) r := by
    intro r hr hN
    have key : ∀ y a, (y, a) ∈ LExpr.freeVars r →
        ∃ t, a = some t ∧ Map.find? (monoTyMap Γ N) y = some t := by
      intro y a hy
      obtain ⟨-, t, rfl, ht⟩ := hr.2 y a hy
      exact ⟨t, rfl, by simp [find?_monoTyMap, hN y _ hy, ht, LTy.toMonoType?]⟩
    refine ⟨fun y a hy => ⟨(hr.2 y a hy).1, ?_⟩, fvars_annotated_by_of_annotated fun y a hy => ?_⟩
    · obtain ⟨t, -, ht⟩ := key y a hy; simp [ht]
    · obtain ⟨t, rfl, ht⟩ := key y a hy
      exact ⟨t, rfl, fun t' ht' => by rw [ht] at ht'; exact Option.some.inj ht'⟩
  have henv : ∀ x r, env x = some r →
      r.NamesIn (fun y => D y = true ∧ (Map.find? (monoTyMap Γ N) y).isSome) ∧
        fvars_annotated_by (monoTyMap Γ N) r := fun x r hx =>
    hin r (hV x r (hV' x r hx)) fun y a hy => List.mem_append_right _
      (List.mem_flatMap.mpr ⟨(x, r), hV' x r hx, List.mem_map.mpr ⟨(y, a), hy, rfl⟩⟩)
  have he' := hin e he fun y a hy => List.mem_append_left _ (List.mem_map.mpr ⟨(y, a), hy, rfl⟩)
  have hnames := hr.namesIn hok.2 (fun x r hx => (henv x r hx).1) he'.1
  have hann := hr.annotated (fun x r hx => (henv x r hx).2) (hstep _).bodyAnnot
    (hstep _).evalAnnot he'.2
  intro y a hy
  obtain ⟨hD, hsome⟩ := hnames y a hy
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨t, rfl, ht⟩ := fvars_annotated_by_annotated hann y a hy
  have htt := ht t' ht'
  subst htt
  rw [find?_monoTyMap] at ht'
  split at ht'
  · exact ⟨hD, t, rfl, eq_forAll_of_bind ht'⟩
  · cases ht'

/-- **Simplifying an expression keeps it passing the output check**, when the recorded values
    pass it, the fold factory brings in only its own operators and those are declared. -/
theorem simplifyExpr_outExprOK {ctx : Ctx} (hok : ctx.FactoriesOK)
    (hcl : ctx.foldFactory.OpsClosed) (hstep : ∀ tyMap, Factory.StepWFOn ctx.foldFactory tyMap)
    {fs D : CoreIdent → Bool} {Γ : VarTyping Expression}
    (hfs : ∀ o : CoreIdent, o.name ∈ ctx.foldFactory → fs o = true)
    (hV : ∀ x r, (x, r) ∈ ctx.values.toList → OutExprOK fs D Γ r)
    {e : Expression.Expr} (he : OutExprOK fs D Γ e) : OutExprOK fs D Γ (simplifyExpr ctx e) :=
  simplifyExpr_inv hok (fun hsub hr hq => reach_outExprOK hok hcl hstep hfs hV hsub hr hq) he

/-- An expression of the body, typed under a typing of monotypes, whose variables are defined
    and whose operators are declared, passes the output check. -/
private theorem outExprOK_of_exprOK {F : Lambda.Factory CoreLParams} {Γ : VarTyping Expression}
    {fs D : CoreIdent → Bool} {e : Expression.Expr} {ty : Expression.Ty}
    (hok : ExprOK F Γ e ty) (hmono : MonoTyping Γ)
    (hD : ∀ y ∈ LExpr.LExpr.getVars e, D y = true) (hfs : ∀ o ∈ LExpr.getOps e, fs o = true) :
    OutExprOK fs D Γ e := by
  refine ⟨hfs, fun y a hy => ?_⟩
  have hyv : y ∈ LExpr.LExpr.getVars e := by
    rw [getVars_eq_freeVars_idents]; exact List.mem_map.mpr ⟨_, hy, rfl⟩
  obtain ⟨⟨τ, -, -, hdef, -⟩, -, hann⟩ := hok
  obtain ⟨t0, ht0⟩ := Option.isSome_iff_exists.mp (hdef y hyv)
  obtain ⟨τ', rfl⟩ := hmono y t0 ht0
  refine ⟨hD y hyv, τ', ?_, ht0⟩
  rcases LExpr.annotateFvars_eq_self_freeVars hann y a hy with h | h <;>
    simp only [ht0, Option.bind_some, LTy.toMonoType?] at h
  · cases h
  · exact h.symm

/-- The free variables of an expression passing the output check are defined. -/
private theorem OutExprOK.vars {fs D : CoreIdent → Bool} {Γ : VarTyping Expression} {e : Expression.Expr}
    (h : OutExprOK fs D Γ e) : ∀ y ∈ HasFvars.getFvars (P := Expression) e, D y = true := by
  intro y hy
  have hy' : y ∈ LExpr.LExpr.getVars e := hy
  rw [getVars_eq_freeVars_idents] at hy'
  obtain ⟨⟨_, a⟩, hm, rfl⟩ := List.mem_map.mp hy'
  exact (h.2 _ a hm).1

/-- The annotations of an expression passing the output check agree with the typing. -/
private theorem OutExprOK.annotates {fs D : CoreIdent → Bool} {Γ : VarTyping Expression}
    {e : Expression.Expr} (h : OutExprOK fs D Γ e) :
    Γ.annotates (HasFvars.getTypedFvars (P := Expression) e) := by
  intro x ty hx
  simp only [HasFvars.getTypedFvars, Expression.typedFvars, List.mem_filterMap] at hx
  obtain ⟨⟨y, a⟩, hm, ha⟩ := hx
  obtain ⟨-, t, rfl, ht⟩ := h.2 y a hm
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  exact ht

/-! ## Statements -/

/-- What the statement lemmas assume of the context a body is simplified from: its factories
    are related as the phase builds them, and its fold factory meets the step conditions at every
    type map, brings in only its own operators, all of which are declared. -/
structure WFSetup (base : Ctx) (fs : CoreIdent → Bool) : Prop where
  factories : base.FactoriesOK
  closed : base.foldFactory.OpsClosed
  step : ∀ tyMap, Factory.StepWFOn base.foldFactory tyMap
  declared : ∀ o : CoreIdent, o.name ∈ base.foldFactory → fs o = true

/-- Every value `ctx` records has declared operators, and each of its free-variable occurrences
    outside `N` names a variable `D` counts as defined and carries the monotype `Γ` gives it. -/
def ValuesOK (fs : CoreIdent → Bool) (N : List CoreIdent) (D : CoreIdent → Bool)
    (Γ : VarTyping Expression) (ctx : Ctx) : Prop :=
  ∀ x r, (x, r) ∈ ctx.values.toList → r.OpsIn (fun o => fs o = true) ∧
    ∀ y a, (y, a) ∈ LExpr.freeVars r → y ∉ N →
      D y = true ∧ ∃ t, a = some t ∧ Γ y = some (.forAll [] t)

section Stmts

variable {base : Ctx} {fs : CoreIdent → Bool}

/-- A value of a context whose values pass the output check everywhere passes it. -/
private theorem ValuesOK.out {D : CoreIdent → Bool}
    {Γ : VarTyping Expression} {ctx : Ctx} (h : ValuesOK fs [] D Γ ctx) {x : CoreIdent}
    {r : Expression.Expr} (hm : (x, r) ∈ ctx.values.toList) : OutExprOK fs D Γ r :=
  ⟨(h x r hm).1, fun y a hy => (h x r hm).2 y a hy List.not_mem_nil⟩

/-- The output check of recorded values survives defining more names, under a typing that
    agrees on the names defined before. -/
private theorem ValuesOK.mono {N : List CoreIdent} {D D' : CoreIdent → Bool}
    {Γ Γ' : VarTyping Expression} {ctx : Ctx} (h : ValuesOK fs N D Γ ctx)
    (hD : ∀ y, D y = true → D' y = true ∧ Γ' y = Γ y) : ValuesOK fs N D' Γ' ctx :=
  fun x r hm => ⟨(h x r hm).1, fun y a hy hN => by
    obtain ⟨hd, t, ha, ht⟩ := (h x r hm).2 y a hy hN
    exact ⟨(hD y hd).1, t, ha, (hD y hd).2.trans ht⟩⟩

/-- Simplifying an expression in a context of the run keeps it passing the output check. -/
private theorem WFSetup.simp (hB : WFSetup base fs) {ctx : Ctx} (hfix : ctx.Fixed base)
    {D : CoreIdent → Bool} {Γ : VarTyping Expression} (hV : ValuesOK fs [] D Γ ctx)
    {e : Expression.Expr} (he : OutExprOK fs D Γ e) : OutExprOK fs D Γ (simplifyExpr ctx e) := by
  obtain ⟨h1, h2, h3⟩ := hfix
  have hok : ctx.FactoriesOK := ⟨by rw [h1, h2, h3]; exact hB.factories.1, h2 ▸ hB.factories.2⟩
  exact simplifyExpr_outExprOK hok (h2 ▸ hB.closed) (h2 ▸ hB.step) (h2 ▸ hB.declared)
    (fun _ _ hm => hV.out hm) he

/-- A command passes the def-use check exactly when its reads and writes are defined, what it
    defines is not, and its operators are declared. -/
private theorem cmd_defUse_iff {D : CoreIdent → Bool} (c : Imperative.Cmd Expression) :
    Stmt.defUseWellFormed (P := Expression) (C := Command) D fs (.cmd (.cmd c)) = true ↔
      (∀ x ∈ Cmd.getVars c, D x = true) ∧ (∀ x ∈ Cmd.modifiedVars c, D x = true) ∧
      (∀ x ∈ Cmd.definedVars c, D x = false) ∧ (∀ o ∈ Cmd.getOps c, fs o = true) := by
  simp [Stmt.defUseWellFormed, HasVarsImp.readVars, HasVarsImp.modifiedVars,
    HasVarsImp.definedVars, CmdExt.readVars, CmdExt.modifiedVars, CmdExt.definedVars,
    HasOpsImp.getOps, CmdExt.getOps, and_assoc]

/-- A command's annotation check reads its annotated reads. -/
private theorem cmd_annot_iff {Γ : VarTyping Expression} (c : Imperative.Cmd Expression) :
    Stmt.fvarTypesWellAnnotated (P := Expression) (C := Command) Γ (.cmd (.cmd c)) ↔
      Γ.annotates (Cmd.getTypedVars c) := Iff.rfl

/-- **One command.** The simplified command passes the def-use and annotation checks, and every
    value recorded after it passes the output check, when the command passes the def-use check,
    is typed under `Γ`, and the values recorded before it pass the output check. -/
private theorem simpCmd_wf (hB : WFSetup base fs) {ctx : Ctx} (hfix : ctx.Fixed base)
    {D : CoreIdent → Bool} {Γ : VarTyping Expression} (hV : ValuesOK fs [] D Γ ctx)
    (hmono : MonoTyping Γ) (c : Imperative.Cmd Expression)
    (hdu : Stmt.defUseWellFormed (P := Expression) (C := Command) D fs (.cmd (.cmd c)) = true)
    (hok : Stmt.exprsOKIn base.factory Γ (.cmd (.cmd c))) :
    Stmt.defUseWellFormed (P := Expression) (C := Command) D fs
        (.cmd (.cmd (simpCmd ctx c).1)) = true ∧
      Stmt.fvarTypesWellAnnotated (P := Expression) (C := Command) Γ
        (.cmd (.cmd (simpCmd ctx c).1)) ∧
      ∀ x r, (x, r) ∈ (simpCmd ctx c).2.values.toList → OutExprOK fs D Γ r := by
  rw [cmd_defUse_iff] at hdu
  rw [cmd_defUse_iff, cmd_annot_iff]
  match c with
  | .init x ty (.det e) md =>
    rw [simpCmd_init_det]
    simp only [Cmd.getVars, ExprOrNondet.getVars, Cmd.modifiedVars, Cmd.definedVars,
      Cmd.getOps, Cmd.getTypedVars, ExprOrNondet.getTypedVars] at hdu ⊢
    simp only [Stmt.exprsOKIn] at hok
    have he := hB.simp hfix hV (outExprOK_of_exprOK hok hmono hdu.1 hdu.2.2.2)
    refine ⟨⟨he.vars, hdu.2.1, hdu.2.2.1, he.1⟩, he.annotates, fun x' r hr => ?_⟩
    rcases mem_record hr with ⟨-, rfl⟩ | ⟨hm, -⟩
    · exact he
    · exact hV.out hm
  | .init x ty .nondet md =>
    rw [simpCmd_init_nondet]
    exact ⟨hdu, by simp [Cmd.getTypedVars, ExprOrNondet.getTypedVars, VarTyping.annotates],
      fun _ _ hr => hV.out (mem_invalidateVar hr).1⟩
  | .set x (.det e) md =>
    rw [simpCmd_set_det]
    simp only [Cmd.getVars, ExprOrNondet.getVars, Cmd.modifiedVars, Cmd.definedVars,
      Cmd.getOps, Cmd.getTypedVars, ExprOrNondet.getTypedVars] at hdu ⊢
    simp only [Stmt.exprsOKIn] at hok
    obtain ⟨ty, -, hok⟩ := hok
    have he := hB.simp hfix hV (outExprOK_of_exprOK hok hmono hdu.1 hdu.2.2.2)
    refine ⟨⟨he.vars, hdu.2.1, hdu.2.2.1, he.1⟩, he.annotates, fun x' r hr => ?_⟩
    rcases mem_record hr with ⟨-, rfl⟩ | ⟨hm, -⟩
    · exact he
    · exact hV.out hm
  | .set x .nondet md =>
    rw [simpCmd_set_nondet]
    exact ⟨hdu, by simp [Cmd.getTypedVars, ExprOrNondet.getTypedVars, VarTyping.annotates],
      fun _ _ hr => hV.out (mem_invalidateVar hr).1⟩
  | .assert l e md | .assume l e md | .cover l e md =>
    first | rw [simpCmd_assert] | rw [simpCmd_assume] | rw [simpCmd_cover]
    simp only [Cmd.getVars, Cmd.modifiedVars, Cmd.definedVars, Cmd.getOps,
      Cmd.getTypedVars] at hdu ⊢
    simp only [Stmt.exprsOKIn] at hok
    have he := hB.simp hfix hV (outExprOK_of_exprOK hok hmono hdu.1 hdu.2.2.2)
    exact ⟨⟨he.vars, hdu.2.1, hdu.2.2.1, he.1⟩, he.annotates, fun _ _ hr => hV.out hr⟩

/-- Simplifying a command keeps what it declares. -/
theorem simpCmd_definedVars (ctx : Ctx) (c : Imperative.Cmd Expression) (b : Bool) :
    Stmt.definedVars (P := Expression) (C := Command) (.cmd (.cmd (simpCmd ctx c).1)) b =
      Stmt.definedVars (P := Expression) (C := Command) (.cmd (.cmd c)) b := by
  cases c with
  | init x ty e md => cases e <;> rfl
  | set x e md => cases e <;> rfl
  | _ => rfl

/-- Simplifying a command keeps its typed definitions. -/
private theorem simpCmd_typedDefinedVars (ctx : Ctx) (c : Imperative.Cmd Expression) :
    Stmt.typedDefinedVars (P := Expression) (C := Command) (.cmd (.cmd (simpCmd ctx c).1)) =
      Stmt.typedDefinedVars (P := Expression) (C := Command) (.cmd (.cmd c)) := by
  cases c with
  | init x ty e md => cases e <;> rfl
  | set x e md => cases e <;> rfl
  | _ => rfl

/-- Simplifying a command keeps the fixed fields of the context. -/
private theorem simpCmd_fixed {ctx : Ctx} (hfix : ctx.Fixed base) (c : Imperative.Cmd Expression) :
    (simpCmd ctx c).2.Fixed base := by
  cases c with
  | init x ty e md => cases e with
    | det e => exact hfix.record _ _
    | nondet => exact hfix.invalidateVar _
  | set x e md => cases e with
    | det e => exact hfix.record _ _
    | nondet => exact hfix.invalidateVar _
  | _ => exact hfix

/-- A variable a statement declares in its own scope is one it declares anywhere. -/
private theorem definedVars_true_sub (s : Statement) :
    ∀ y ∈ Stmt.definedVars (P := Expression) (C := Command) s true,
      y ∈ Stmt.definedVars (P := Expression) (C := Command) s false := by
  intro y hy
  cases s <;> simp_all [Stmt.definedVars, HasVarsImp.definedVars]

/-- A typed definition of a statement names a variable it declares in its own scope, at one of
    its init-types. -/
private theorem typedDefinedVars_spec (s : Statement) :
    ∀ p ∈ Stmt.typedDefinedVars (P := Expression) (C := Command) s,
      p.1 ∈ Stmt.definedVars (P := Expression) (C := Command) s true ∧
        p.2 ∈ Stmt.initTypes (P := Expression) (C := Command) s := by
  intro p hp
  rcases s with ((x | _ | _ | _ | _) | _) | _ | _ | _ | _ | _ <;>
    simp_all [Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars, CmdExt.typedDefinedVars,
      Cmd.typedDefinedVars, Stmt.definedVars, HasVarsImp.definedVars, CmdExt.definedVars,
      Cmd.definedVars, Stmt.initTypes, HasInitTypesImp.initTypes, CmdExt.initTypes,
      Cmd.initTypes]

/-- A free variable of an expression is among its variables. -/
private theorem mem_getFvars_of_freeVars {e : Expression.Expr} {y : CoreIdent}
    {a : Option LMonoTy} (h : (y, a) ∈ LExpr.freeVars e) :
    y ∈ HasFvars.getFvars (P := Expression) e := by
  show y ∈ LExpr.LExpr.getVars e
  rw [getVars_eq_freeVars_idents]; exact List.mem_map.mpr ⟨_, h, rfl⟩

/-- A definition `agreedDefs` records is one a live context records. -/
private theorem mem_agreedDefs_live {live : List Ctx} {a sc : Std.HashSet String}
    {x : CoreIdent} {v : Expression.Expr} (h : (x, v) ∈ agreedDefs live a sc) :
    ∃ c ∈ live, (x, v) ∈ c.values.toList := by
  match live with
  | [] => simp [agreedDefs] at h
  | first :: rest =>
    refine ⟨first, List.mem_cons_self, ?_⟩
    simp only [agreedDefs] at h
    split at h
    · obtain ⟨n, -, hsome⟩ := List.mem_filterMap.mp h
      split at hsome
      · rename_i w hfind
        split at hsome
        · simp only [Option.some.injEq, Prod.mk.injEq] at hsome
          obtain ⟨rfl, rfl⟩ := hsome
          exact Map.find?_mem _ _ _ hfind
        · cases hsome
      · cases hsome
    · exact (List.mem_filter.mp h).1

/-- An entry after a join is an entry of the base, or one a live context records whose value
    mentions no scoped name. -/
private theorem mem_join_live {b : Ctx} {live : List Ctx} {a sc : Std.HashSet String}
    {y : CoreIdent} {v : Expression.Expr} (h : (y, v) ∈ (b.join live a sc).values.toList) :
    (y, v) ∈ b.values.toList ∨ ((∃ c ∈ live, (y, v) ∈ c.values.toList) ∧
      ∀ f ∈ HasFvars.getFvars (P := Core.Expression) v, f.name ∉ sc) := by
  unfold Ctx.join at h
  split at h
  · exact .inl h
  · rcases mem_recordAgreed _ h with hag | hb
    · exact .inr ⟨mem_agreedDefs_live hag, (mem_agreedDefs hag).2.2.2⟩
    · exact .inl (mem_invalidate hb).1

/-- An arm that can run is one of the two arms. -/
private theorem mem_liveArms_pair {α : Type} {cond : ExprOrNondet Expression} {a b c : α}
    (h : c ∈ liveArms cond [a, b]) : c = a ∨ c = b := by
  cases cond <;> simp only [liveArms] at h
  · split at h
    · simp only [List.mem_singleton] at h; exact .inl h
    · split at h
      · simp only [List.mem_singleton] at h; exact .inr h
      · simpa using h
  · simpa using h

/-- The values a branch records afterwards pass the output check, when the values before it and
    those each arm records, outside what the arm declares, do. -/
private theorem join_valuesOK {ctx : Ctx} {D : CoreIdent → Bool} {Γ : VarTyping Expression}
    {cond : ExprOrNondet Expression} {ts es : List Statement}
    (hV : ValuesOK fs [] D Γ ctx)
    (hVt : ValuesOK fs (Block.definedVars ts false) D Γ (simpStmts ctx ts).2.1)
    (hVe : ValuesOK fs (Block.definedVars es false) D Γ (simpStmts ctx es).2.1) :
    ValuesOK fs [] D Γ (ctx.join (liveArms cond [(simpStmts ctx ts).2.1, (simpStmts ctx es).2.1])
      ((simpStmts ctx ts).2.2.union (simpStmts ctx es).2.2).vars
      ((simpStmts ctx ts).2.2.union (simpStmts ctx es).2.2).defined) := by
  intro x r hm
  rcases mem_join_live hm with hb | ⟨⟨c, hc, hmc⟩, hf⟩
  · exact hV x r hb
  · have hw := (simpStmts_writes ctx ts).union (simpStmts_writes ctx es)
    have hnd : ∀ y a, (y, a) ∈ LExpr.freeVars r →
        y ∉ Block.definedVars (P := Expression) (C := Command) ts false ∧
          y ∉ Block.definedVars (P := Expression) (C := Command) es false := by
      intro y a hy
      have hn := hf y (mem_getFvars_of_freeVars hy)
      rw [hw.defined_iff] at hn
      simp only [List.map_append, List.mem_append, not_or] at hn
      exact ⟨fun h => hn.1 (List.mem_map.mpr ⟨y, h, rfl⟩),
        fun h => hn.2 (List.mem_map.mpr ⟨y, h, rfl⟩)⟩
    rcases mem_liveArms_pair hc with rfl | rfl
    · exact ⟨(hVt x r hmc).1, fun y a hy _ => (hVt x r hmc).2 y a hy (hnd y a hy).1⟩
    · exact ⟨(hVe x r hmc).1, fun y a hy _ => (hVe x r hmc).2 y a hy (hnd y a hy).2⟩

mutual
/-- **One statement.** A statement without loops or calls, def-use well-formed from `D` and
    typed under a typing `Γ` of monotypes, simplifies to one statement declaring what it does,
    def-use well-formed from `D` and well annotated for `Γ`, when the values recorded before it
    pass the output check. The values recorded after it pass the output check against the names
    and typing in scope after it. -/
private theorem simpStmt_wf (hB : WFSetup base fs) (s : Statement) (ctx : Ctx)
    (D : CoreIdent → Bool) (Γ : VarTyping Expression) (hfix : ctx.Fixed base)
    (hV : ValuesOK fs [] D Γ ctx) (hmono : MonoTyping Γ)
    (hinit : ∀ ty ∈ Stmt.initTypes (P := Expression) (C := Command) s, ∃ τ, ty = .forAll [] τ)
    (hnl : Stmt.noLoops s = true) (hnc : Statement.noCalls s = true)
    (hdu : Stmt.defUseWellFormed (P := Expression) (C := Command) D fs s = true)
    (hok : Stmt.exprsOKIn base.factory Γ s) :
    ∃ s', (simpStmt ctx s).1 = [s'] ∧
      Stmt.definedVars (P := Expression) (C := Command) s' true =
        Stmt.definedVars (P := Expression) (C := Command) s true ∧
      Stmt.typedDefinedVars (P := Expression) (C := Command) s' =
        Stmt.typedDefinedVars (P := Expression) (C := Command) s ∧
      Stmt.defUseWellFormed (P := Expression) (C := Command) D fs s' = true ∧
      Stmt.fvarTypesWellAnnotated (P := Expression) (C := Command) Γ s' ∧
      (simpStmt ctx s).2.1.Fixed base ∧
      ValuesOK fs [] (fun n => D n || decide (n ∈ Stmt.definedVars (P := Expression)
        (C := Command) s true)) (Γ.extend (Stmt.typedDefinedVars (P := Expression) s))
        (simpStmt ctx s).2.1 := by
  match s with
  | .cmd (.cmd c) =>
    rw [simpStmt_cmd]
    obtain ⟨h1, h2, h3⟩ := simpCmd_wf hB hfix hV hmono c hdu hok
    have hnd := ((cmd_defUse_iff c).mp hdu).2.2.1
    refine ⟨_, rfl, simpCmd_definedVars ctx c true, simpCmd_typedDefinedVars ctx c, h1, h2,
      simpCmd_fixed hfix c, fun x r hm => ⟨(h3 x r hm).1, fun y a hy _ => ?_⟩⟩
    obtain ⟨hd, t, ha, ht⟩ := (h3 x r hm).2 y a hy
    refine ⟨by simp [hd], t, ha, ?_⟩
    rw [VarTyping.extend_of_not_mem]
    · exact ht
    · intro hy'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy'
      have := hnd _ (by simpa [Stmt.definedVars, HasVarsImp.definedVars, CmdExt.definedVars]
        using (typedDefinedVars_spec _ p hp).1)
      rw [hd] at this; cases this
  | .cmd (.call pname tyArgs args md) =>
    obtain ⟨c', hc'⟩ := exists_baseCmd_of_noCalls hnc
    cases hc'
  | .block l ss md =>
    rw [simpStmt_block_eq]
    simp only [Stmt.initTypes] at hinit
    rw [Stmt.noLoops_block] at hnl
    simp only [Stmt.defUseWellFormed] at hdu
    simp only [Stmt.exprsOKIn] at hok
    obtain ⟨hdu', hann', -, hV'⟩ :=
      simpStmts_wf hB ss ctx D Γ hfix hV hmono hinit hnl (noCalls_block hnc) hdu hok
    refine ⟨_, rfl, rfl, rfl, hdu', hann', (hfix.values _).invalidate _, fun x r hm => ?_⟩
    obtain ⟨hm, -, hf⟩ := mem_invalidate hm
    refine ⟨(hV' x r hm).1, fun y a hy _ => ?_⟩
    have hyn : y ∉ Block.definedVars (P := Expression) (C := Command) ss false := fun hd =>
      hf y (mem_getFvars_of_freeVars hy) (((simpStmts_writes ctx ss).vars_iff _).mpr
        (List.mem_map.mpr ⟨y, by simp [hd], rfl⟩))
    obtain ⟨hd, t, ha, ht⟩ := (hV' x r hm).2 y a hy hyn
    exact ⟨by simp [hd], t, ha, ht⟩
  | .ite (.det c) ts es md =>
    rw [simpStmt_ite_det_eq]
    simp only [Stmt.initTypes, List.mem_append] at hinit
    rw [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    simp only [Stmt.defUseWellFormed, ExprOrNondet.getVars, Bool.and_eq_true,
      List.all_eq_true] at hdu
    simp only [Stmt.exprsOKIn] at hok
    obtain ⟨⟨⟨hcv, hco⟩, hdt⟩, hde⟩ := hdu
    have hc := hB.simp hfix hV (outExprOK_of_exprOK hok.1 hmono hcv hco)
    obtain ⟨hdt', hat', -, hVt⟩ := simpStmts_wf hB ts ctx D Γ hfix hV hmono
      (fun ty h => hinit ty (.inl h)) hnl.1 (noCalls_ite hnc).1 hdt hok.2.1
    obtain ⟨hde', hae', -, hVe⟩ := simpStmts_wf hB es ctx D Γ hfix hV hmono
      (fun ty h => hinit ty (.inr h)) hnl.2 (noCalls_ite hnc).2 hde hok.2.2
    refine ⟨_, rfl, rfl, rfl, ?_, ⟨hc.annotates, hat', hae'⟩, hfix.join _ _ _,
      (join_valuesOK hV hVt hVe).mono fun y hy => ⟨by simp [hy], rfl⟩⟩
    simp only [Stmt.defUseWellFormed, ExprOrNondet.getVars, Bool.and_eq_true, List.all_eq_true]
    exact ⟨⟨⟨hc.vars, hc.1⟩, hdt'⟩, hde'⟩
  | .ite .nondet ts es md =>
    rw [simpStmt_ite_nondet_eq]
    simp only [Stmt.initTypes, List.mem_append] at hinit
    rw [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
    simp only [Stmt.exprsOKIn] at hok
    obtain ⟨hdt', hat', -, hVt⟩ := simpStmts_wf hB ts ctx D Γ hfix hV hmono
      (fun ty h => hinit ty (.inl h)) hnl.1 (noCalls_ite hnc).1 hdu.1.2 hok.1
    obtain ⟨hde', hae', -, hVe⟩ := simpStmts_wf hB es ctx D Γ hfix hV hmono
      (fun ty h => hinit ty (.inr h)) hnl.2 (noCalls_ite hnc).2 hdu.2 hok.2
    refine ⟨_, rfl, rfl, rfl, ?_, ⟨by simp [ExprOrNondet.getTypedVars, VarTyping.annotates],
      hat', hae'⟩, hfix.join _ _ _,
      (join_valuesOK hV hVt hVe).mono fun y hy => ⟨by simp [hy], rfl⟩⟩
    simp only [Stmt.defUseWellFormed, Bool.and_eq_true]
    exact ⟨⟨hdu.1.1, hdt'⟩, hde'⟩
  | .loop g m invs body md => rw [Stmt.noLoops_loop] at hnl; cases hnl
  | .exit l md =>
    rw [simpStmt_exit]
    exact ⟨_, rfl, rfl, rfl, hdu, trivial, hfix, hV.mono fun y hy => ⟨by simp [hy], rfl⟩⟩
  | .typeDecl tc md =>
    rw [simpStmt_typeDecl]
    exact ⟨_, rfl, rfl, rfl, hdu, trivial, hfix, hV.mono fun y hy => ⟨by simp [hy], rfl⟩⟩
  termination_by sizeOf s

/-- **A statement list.** A list without loops or calls, def-use well-formed from `D` and typed
    under a typing `Γ` of monotypes, whose init-types are monotypes, simplifies to a list
    def-use well-formed from `D` and well annotated for `Γ`, when the values recorded before it
    pass the output check. The values recorded after it pass the output check outside the
    names the list declares. -/
private theorem simpStmts_wf (hB : WFSetup base fs) (ss : List Statement) (ctx : Ctx)
    (D : CoreIdent → Bool) (Γ : VarTyping Expression) (hfix : ctx.Fixed base)
    (hV : ValuesOK fs [] D Γ ctx) (hmono : MonoTyping Γ)
    (hinit : ∀ ty ∈ Block.initTypes (P := Expression) (C := Command) ss, ∃ τ, ty = .forAll [] τ)
    (hnl : Block.noLoops ss = true) (hnc : Statements.noCalls ss = true)
    (hdu : Block.defUseWellFormed (P := Expression) (C := Command) D fs ss = true)
    (hok : Block.exprsOKIn base.factory Γ ss) :
    Block.defUseWellFormed (P := Expression) (C := Command) D fs (simpStmts ctx ss).1 = true ∧
      Block.fvarTypesWellAnnotated (P := Expression) (C := Command) Γ (simpStmts ctx ss).1 ∧
      (simpStmts ctx ss).2.1.Fixed base ∧
      ValuesOK fs (Block.definedVars (P := Expression) (C := Command) ss false) D Γ
        (simpStmts ctx ss).2.1 := by
  match ss with
  | [] =>
    rw [simpStmts_nil]
    exact ⟨by simp [Block.defUseWellFormed], trivial, hfix,
      fun x r hm => ⟨(hV x r hm).1, fun y a hy _ => (hV x r hm).2 y a hy List.not_mem_nil⟩⟩
  | s :: rest =>
    rw [simpStmts_cons]
    simp only [Block.initTypes, List.mem_append] at hinit
    rw [Block.noLoops_cons, Bool.and_eq_true] at hnl
    simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
    simp only [Block.exprsOKIn] at hok
    obtain ⟨s', hs', hdv, htd, hdu', hann', hfix', hV'⟩ := simpStmt_wf hB s ctx D Γ hfix hV
      hmono (fun ty h => hinit ty (.inl h)) hnl.1 (noCalls_cons hnc).1 hdu.1 hok.1
    have hmono' : MonoTyping (Γ.extend (Stmt.typedDefinedVars (P := Expression) s)) := by
      intro y t hy
      simp only [VarTyping.extend] at hy
      split at hy
      · rename_i p hp
        cases hy
        exact hinit _ (.inl (typedDefinedVars_spec s p (List.mem_of_find?_eq_some hp)).2)
      · exact hmono y t hy
    obtain ⟨hdu'', hann'', hfix'', hV''⟩ := simpStmts_wf hB rest _ _ _ hfix' hV' hmono'
      (fun ty h => hinit ty (.inr h)) hnl.2 (noCalls_cons hnc).2 hdu.2 hok.2
    rw [hs']
    refine ⟨?_, ?_, hfix'', fun x r hm => ⟨(hV'' x r hm).1, fun y a hy hN => ?_⟩⟩
    · simp only [List.singleton_append, Block.defUseWellFormed, Bool.and_eq_true]
      rw [hdv]; exact ⟨hdu', hdu''⟩
    · simp only [List.singleton_append, Block.fvarTypesWellAnnotated]
      rw [htd]; exact ⟨hann', hann''⟩
    · simp only [Block.definedVars, List.mem_append, not_or] at hN
      obtain ⟨hd, t, ha, ht⟩ := (hV'' x r hm).2 y a hy hN.2
      have hns : y ∉ Stmt.definedVars (P := Expression) (C := Command) s true := fun h =>
        hN.1 (definedVars_true_sub s y h)
      refine ⟨by simpa [hns] using hd, t, ha, ?_⟩
      rwa [VarTyping.extend_of_not_mem fun h => hns (by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        exact (typedDefinedVars_spec s p hp).1)] at ht
  termination_by sizeOf ss
end

end Stmts

end Core.Simplify
