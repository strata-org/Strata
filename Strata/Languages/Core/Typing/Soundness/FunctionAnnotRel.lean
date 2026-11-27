/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Soundness.Function
public import Strata.Languages.Core.Typing.Soundness.RecFuncBlock
public import Strata.Languages.Core.Typing.Props.ExprEraseProps
import all Strata.Languages.Core.Typing.Soundness.Function
import all Strata.Languages.Core.Typing.Soundness.RecFuncBlock
import all Strata.Languages.Core.Typing.Soundness.RecFuncBlockInversion
import all Strata.Languages.Core.Typing.Props.ExprEraseProps
import all Strata.Languages.Core.FunctionType
import all Strata.Languages.Core.RecFuncBlockType
import all Strata.Languages.Core.Function
import all Strata.Languages.Core.TypeSkolem
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.LExprType
import all Strata.DL.Lambda.LExprTEraseProps
import all Strata.DL.Lambda.LExprTypeEnv
import Strata.Util.Tactics

/-! # Annotations of checked functions

The function checker returns each function with its reserved type parameters renamed, its
signature types alias-resolved, and its expressions elaborated. `Function.typeCheck_annotRel`
shows that the result differs from the input only in those annotations: both erase to the same
function, and each signature type is the written type renamed and alias-resolved. -/

namespace Core

open Lambda Imperative

public section

/-- The alias resolution of a type against a list of aliases. -/
abbrev resolveTy (aliases : List TypeAlias) (ty : LMonoTy) : LMonoTy :=
  TContext.resolveTy ({ aliases := aliases } : TContext Unit) ty

/-- A type with its type variables renamed by `ren`; a variable `ren` does not list keeps its
    name. -/
abbrev renamedTy (ren : List (String × String)) (ty : LMonoTy) : LMonoTy :=
  LMonoTy.subst (Subst.ofRenaming ren) ty

/-- `ty'` is the written signature type `ty` with its type variables renamed by `ren` and its
    aliases resolved. -/
def SigTyRel (aliases : List TypeAlias) (ren : List (String × String)) (ty ty' : LMonoTy) :
    Prop :=
  ty' = resolveTy aliases (renamedTy ren ty)

/-- `ren` renames distinct type parameters among `typeArgs`, all of them reserved (the ones the
    checker may change), to pairwise distinct names outside `mentioned`, the type variables the
    declaration mentions. So no renamed parameter captures another type variable of the
    declaration. -/
def ReservedRenaming (typeArgs mentioned : List String) (ren : List (String × String)) : Prop :=
  TypeSpec.TyArgRenamingCore typeArgs mentioned ren ∧ ∀ p ∈ ren, isAllowedName p.1 = false

/-- The renaming of reserved type parameters that the checker picks is a `ReservedRenaming`,
    when the type parameters are distinct and every type variable the declaration mentions is
    avoided. -/
theorem reservedTypeArgsRenaming_reservedRenaming (typeArgs mentioned : List String)
    (avoid : Unit → List String) (hnd : typeArgs.Nodup) (hsub : ∀ v ∈ mentioned, v ∈ avoid ()) :
    ReservedRenaming typeArgs mentioned (reservedTypeArgsRenaming typeArgs avoid) := by
  obtain ⟨hfst, hsnd, hfresh⟩ := reservedTypeArgsRenaming_spec typeArgs avoid
  have hfstnd : ((reservedTypeArgsRenaming typeArgs avoid).map Prod.fst).Nodup :=
    hfst ▸ hnd.sublist List.filter_sublist
  have hmem : ∀ p ∈ reservedTypeArgsRenaming typeArgs avoid,
      p.1 ∈ typeArgs ∧ isAllowedName p.1 = false := by
    intro p hp
    have hfilter : p.1 ∈ typeArgs.filter (!isAllowedName ·) := hfst ▸ List.mem_map_of_mem hp
    obtain ⟨hin, hreserved⟩ := List.mem_filter.mp hfilter
    have hfalse : isAllowedName p.1 = false := by
      simpa only [Bool.not_eq_true'] using hreserved
    exact ⟨hin, hfalse⟩
  refine ⟨⟨hfstnd, hsnd, fun p hp => ⟨(hmem p hp).1, fun hin => (hfresh p hp).1 (hsub _ hin)⟩⟩,
    fun p hp => (hmem p hp).2⟩

/-- A renaming that the declarative typing spec allows for a declaration's type parameters
    is a `ReservedRenaming`: it renames distinct reserved type parameters to pairwise distinct
    names the declaration does not mention. -/
private theorem TypeSpec.TyArgRenaming.reservedRenaming {C : LContext CoreLParams}
    {Γ : TContext Unit} {typeArgs mentioned : List String} {ren : List (String × String)}
    (h : TypeSpec.TyArgRenaming C Γ typeArgs mentioned ren) :
    ReservedRenaming typeArgs mentioned ren :=
  ⟨h.1, fun p hp => (h.2 p hp).1⟩

/-- `f'` is the checked form of the written function `f`: both erase to the same function, and
    for one renaming `ren` of reserved type parameters, the type parameters of `f'` are those of
    `f` renamed and every signature type of `f'` is the written one renamed and
    alias-resolved. -/
def FuncAnnotRel (aliases : List TypeAlias) (f f' : Function) : Prop :=
  f'.eraseAnnots = f.eraseAnnots ∧
  ∃ ren : List (String × String),
    ReservedRenaming f.typeArgs f.mentionedTyVars ren ∧
    f'.typeArgs = renameTyArgList ren f.typeArgs ∧
    SigTyRel aliases ren f.output f'.output ∧
    List.Rel₂ (SigTyRel aliases ren) f.inputs.values f'.inputs.values

/-- The erasure of the pair list `keys.zip tys` keeps the keys when `tys` matches in length. -/
theorem zip_keys_map_erased {γ : Type} (l : List (CoreIdent × LMonoTy)) (tys : List γ)
    (hlen : (l.map Prod.fst).length = tys.length) :
    ((l.map Prod.fst).zip tys).map (fun p => (p.1, LMonoTy.erased))
      = l.map (fun p => (p.1, LMonoTy.erased)) := by
  induction l generalizing tys with
  | nil => simp only [List.map_nil, List.zip_nil_left]
  | cons p l ih =>
    cases tys with
    | nil => simp only [List.map_cons, List.length_cons, List.length_nil] at hlen; omega
    | cons t ts =>
      simp only [List.map_cons, List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.map_cons, List.zip_cons_cons, ih ts hlen]

/-- Renaming the type parameters of a function leaves its erasure unchanged. -/
private theorem Function.eraseAnnots_renameTypeArgs (f : Function) (ren : List (String × String)) :
    Function.eraseAnnots (f.renameTypeArgs ren) = f.eraseAnnots := by
  have hin : (f.inputs.map (fun (id, mty) => (id, LMonoTy.subst (Subst.ofRenaming ren) mty))).map
      (fun (x, _) => (x, LMonoTy.erased)) = f.inputs.map (fun (x, _) => (x, LMonoTy.erased)) := by
    exact (List.map_map (l := (f.inputs : List (CoreIdent × LMonoTy)))).trans rfl
  unfold Function.eraseAnnots LFuncDefined.eraseTypes LFuncDefined.renameTypeArgs
    LFuncDefined.applyTypeSubst renameTyArgList
  simp only [Option.map_map, List.map_map, Function.comp_def, LExpr.eraseTypes_applyTypeSubst]
  rw [hin]

/-- A position run on a skolemized expression stores an expression with the erasure of the
    written one. -/
private theorem PositionRun.stored_eraseTypes
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {σ : RigidNames}
    {sig : @LMonoTySignature Unit} {s : Option String} {e : Expression.Expr} {mty : LMonoTy}
    {et : LExprT CoreLParams.mono}
    (h : PositionRun C Env σ sig (skolemizeBody s σ e) mty et Env') (S : Subst) :
    (finishDeskolemized σ S et).eraseTypes = e.eraseTypes := by
  obtain ⟨EnvR, hres, -⟩ := h
  rw [eraseTypes_finishDeskolemized,
    SourceExpr.resolveWithType_unresolved_eraseTypes _ _ _ _ _ _ hres, eraseTypes_skolemizeBody]

/-- Every stored precondition of a successful precondition walk keeps its metadata and erases
    like the written one. -/
private theorem checkPreconditions_erase
    {C : Expression.TyContext} {name : String} {σ : RigidNames}
    {sig : @LMonoTySignature Unit} (S : Subst) :
    ∀ (ps : List (Strata.DL.Util.FuncPrecondition Expression.Expr Expression.ExprMetadata))
      (Env Env' : Expression.TyEnv)
      (pts : List (Expression.ExprMetadata × LExprT CoreLParams.mono)),
      Function.checkPreconditions C Env name σ sig ps = .ok (pts, Env') →
      pts.map (fun q => (q.1, (finishDeskolemized σ S q.2).eraseTypes))
        = ps.map (fun p => (p.md, p.expr.eraseTypes))
  | [], E, E', pts, h => by
    simp only [Function.checkPreconditions, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | p :: ps, E, E', pts, h => by
    obtain ⟨pT, Emid, psT, hrun, -, hrest, rfl⟩ := checkPreconditions_cons_inv h
    simp only [List.map_cons, hrun.stored_eraseTypes S,
      checkPreconditions_erase S ps _ _ psT hrest]

/-- Every stored axiom of a successful axiom walk erases like the written one. -/
private theorem checkAxioms_erase
    {C : Expression.TyContext} {name : String} {σ : RigidNames}
    {sig : @LMonoTySignature Unit} (S : Subst) :
    ∀ (axs : List Expression.Expr) (Env Env' : Expression.TyEnv)
      (ats : List (LExprT CoreLParams.mono)),
      Function.checkAxioms C Env name σ sig axs = .ok (ats, Env') →
      ats.map (fun et => (finishDeskolemized σ S et).eraseTypes) = axs.map LExpr.eraseTypes
  | [], E, E', ats, h => by
    simp only [Function.checkAxioms, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | ax :: axs, E, E', ats, h => by
    obtain ⟨axT, Emid, axsT, hrun, hrest, rfl⟩ := checkAxioms_cons_inv h
    simp only [List.map_cons, hrun.stored_eraseTypes S, checkAxioms_erase S axs _ _ axsT hrest]

/-- Each expression position of a successful position walk, once stored, erases to the
    corresponding written expression, and the precondition metadata is kept. -/
private theorem checkPositions_erase {self : Option String}
    {C : Expression.TyContext} {Env : Expression.TyEnv} {func : Function}
    {outR : LMonoTy} {insR : LMonoTys} {σ : RigidNames}
    {positions : Function.CheckedPositions}
    (h : Function.checkPositions self C Env func outR insR σ = .ok positions) (S : Subst) :
    positions.body.map (fun et => (finishDeskolemized σ S et).eraseTypes)
        = func.body.map LExpr.eraseTypes
    ∧ positions.measure.map (fun et => (finishDeskolemized σ S et).eraseTypes)
        = func.measure.map LExpr.eraseTypes
    ∧ positions.preconditions.map (fun q => (q.1, (finishDeskolemized σ S q.2).eraseTypes))
        = func.preconditions.map (fun p => (p.md, p.expr.eraseTypes))
    ∧ positions.axioms.map (fun et => (finishDeskolemized σ S et).eraseTypes)
        = func.axioms.map LExpr.eraseTypes := by
  obtain ⟨Ebody, Emeasure, Epre, hbody, hmeasure, hpre, hax⟩ := checkPositions_inv h
  refine ⟨?_, ?_, checkPreconditions_erase S _ _ _ _ hpre, checkAxioms_erase S _ _ _ _ hax⟩
  · rcases checkBody_inv hbody with ⟨hb, hnone, -⟩ | ⟨body, et, hb, hbt, hrun, -⟩
    · rw [hnone, hb]
      rfl
    · rw [hbt, hb]
      simp only [Option.map_some, hrun.stored_eraseTypes S]
  · rcases checkMeasure_inv hmeasure with ⟨hm, hnone, -⟩ | ⟨m, et, hm, hmt, hrun, -⟩
    · rw [hnone, hm]
      rfl
    · rw [hmt, hm]
      simp only [Option.map_some, hrun.stored_eraseTypes S]

/-- A checked function erases like the function it was checked from. -/
private theorem Function.CoreRun.eraseAnnots_eq
    {C : Expression.TyContext} {Env EnvCore : Expression.TyEnv}
    {func func' : Function} {outR : LMonoTy} {insR : LMonoTys}
    {positions : Function.CheckedPositions}
    (run : Function.CoreRun sc tn C Env EnvCore func func' outR insR positions) :
    func'.eraseAnnots = func.eraseAnnots := by
  obtain ⟨hbody, hmeas, hpre, hax⟩ :=
    checkPositions_erase run.positionsOk.choose_spec EnvCore.stateSubstInfo.subst
  have hlen : func.inputs.keys.length = insR.length := by
    have hl := List.Rel₂.length_eq run.insResolveEach
    have h1 := ListMap.keys.length (ls := func.inputs)
    have h2 := ListMap.values_length func.inputs
    omega
  have hin : (func.inputs.keys.zip insR).map (fun p => (p.1, LMonoTy.erased))
      = func.inputs.map (fun p => (p.1, LMonoTy.erased)) := by
    rw [ListMap.keys_eq_map_fst]
    refine zip_keys_map_erased (func.inputs : List (CoreIdent × LMonoTy)) insR ?_
    rw [← ListMap.keys_eq_map_fst]
    exact hlen
  rw [run.stored]
  generalize Function.rigidNames sc C func tn = σ at *
  generalize EnvCore.stateSubstInfo.subst = S at *
  have hbody' : (positions.body.map (finishDeskolemized σ S)).map LExpr.eraseTypes
      = func.body.map LExpr.eraseTypes := by
    rw [Option.map_map]
    exact hbody
  have hmeas' : (positions.measure.map (finishDeskolemized σ S)).map LExpr.eraseTypes
      = func.measure.map LExpr.eraseTypes := by
    rw [Option.map_map]
    exact hmeas
  have hax' : (positions.axioms.map (finishDeskolemized σ S)).map LExpr.eraseTypes
      = func.axioms.map LExpr.eraseTypes := by
    rw [List.map_map]
    exact hax
  have hpre' : (positions.preconditions.map fun (md, eT) =>
        ({ expr := finishDeskolemized σ S eT, md := md } :
          Strata.DL.Util.FuncPrecondition Expression.Expr Expression.ExprMetadata)).map
        (fun p => { p with expr := p.expr.eraseTypes })
      = func.preconditions.map (fun p => { p with expr := p.expr.eraseTypes }) := by
    have h1 := congrArg (List.map fun q =>
      ({ expr := q.2, md := q.1 } :
        Strata.DL.Util.FuncPrecondition Expression.Expr Expression.ExprMetadata)) hpre
    simp only [List.map_map] at h1
    simp only [List.map_map]
    exact h1
  unfold Function.eraseAnnots LFuncDefined.eraseTypes
  dsimp only
  congr 1 <;> first | exact hin | exact hbody' | exact hax' | exact hpre' | exact hmeas'

/-- Alias resolution against `Env.context` is `resolveTy` at its aliases. -/
private theorem resolveTy_context (Env : Expression.TyEnv) :
    Env.context.resolveTy = resolveTy Env.context.aliases :=
  TContext.resolveTy_congr (T := CoreLParams) rfl

/-- The input types of a function with its type parameters renamed are the renamed input types. -/
private theorem renameTypeArgs_inputs_values (f : Function) (ren : List (String × String)) :
    (f.renameTypeArgs ren).inputs.values = f.inputs.values.map (renamedTy ren) := by
  have hmap : ∀ l : List (CoreIdent × LMonoTy),
      (l.map (fun (id, mty) => (id, LMonoTy.subst (Subst.ofRenaming ren) mty))).map Prod.snd
        = (l.map Prod.snd).map (renamedTy ren) := by
    intro l
    rw [List.map_map, List.map_map]
    rfl
  rw [ListMap.values_eq_map_snd, ListMap.values_eq_map_snd]
  exact hmap f.inputs

/-- The checked function of `Function.typeCheckIn` is the written function with its type
    parameters renamed, its signature types renamed and alias-resolved, and its expressions
    elaborated. -/
theorem Function.typeCheckIn_annotRel {scope : Thunk (Std.HashSet String)}
    {C : Expression.TyContext} {Env : Expression.TyEnv} {func renamed func' : Function}
    (h : Function.typeCheckIn scope C Env func = .ok (renamed, func')) :
    FuncAnnotRel Env.context.aliases func func' := by
  obtain ⟨ren, hspec, hren⟩ := Function.typeCheckIn_alphaVariant h
  obtain ⟨-, EnvCore, hc⟩ := Function.typeCheckIn_checked h
  obtain ⟨outR, insR, positions, run⟩ := hc.run
  subst hren
  have hvals : func'.inputs.values = insR := by
    rw [run.stored]
    exact run.resolvedSig.2.1
  refine ⟨?_, ren, hspec.reservedRenaming, ?_, ?_, ?_⟩
  · rw [run.eraseAnnots_eq, Function.eraseAnnots_renameTypeArgs]
  · rw [run.stored]
    rfl
  · have hout : func'.output = outR := by rw [run.stored]
    rw [hout, TContext.resolveTy_of_resolveAliases (T := CoreLParams) run.outResolved]
    exact congrFun (resolveTy_context Env) _
  · rw [hvals]
    have hrel : List.Rel₂ (fun ty ty' => ty' = Env.context.resolveTy ty)
        (func.renameTypeArgs ren).inputs.values insR :=
      run.insResolveEach.imp fun _ _ hr =>
        TContext.resolveTy_of_resolveAliases (T := CoreLParams) hr
    rw [renameTypeArgs_inputs_values] at hrel
    refine (List.Rel₂.of_map_left (renamedTy ren) _ _ hrel).imp ?_
    intro ty ty' hty
    rw [resolveTy_context] at hty
    exact hty

/-- The function `Function.typeCheck` returns is the written function with its type parameters
    renamed, its signature types renamed and alias-resolved, and its expressions
    elaborated. -/
theorem Function.typeCheck_annotRel {C : Expression.TyContext} {Env Env' : Expression.TyEnv}
    {func func' : Function} (h : Function.typeCheck C Env func = .ok (func', Env')) :
    FuncAnnotRel Env.context.aliases func func' :=
  Function.typeCheckIn_annotRel (Function.typeCheck_in h)

/-- Every function of an accepted recursive block is the checked form of the written one. -/
theorem RecFuncBlock.typeCheck_annotRel {S S' : Std.HashSet String}
    {C C' : Expression.TyContext} {Env Env' : Expression.TyEnv} {funcs funcs' : List Function}
    (h : RecFuncBlock.typeCheckIn S C Env funcs = .ok (funcs', C', Env', S')) :
    List.Rel₂ (FuncAnnotRel Env.context.aliases) funcs funcs' := by
  obtain ⟨sigs, hsigRel, -, hdefRel, -, -⟩ :=
    RecFuncBlock.typeCheckIn_decompose S S' C C' Env Env' funcs funcs' h
  obtain ⟨-, hrel⟩ := RecFuncBlock.members_of_sigs hsigRel hdefRel
  exact hrel.imp fun _ _ ⟨_, hf⟩ => Function.typeCheckIn_annotRel hf

end

end Core
