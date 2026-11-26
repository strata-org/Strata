/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.TypeSkolem
public import Strata.Languages.Core.Typing.Spec.CmdTypeSpec
public import Strata.Languages.Core.Typing.Soundness.TypingAssumptions
public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.LExprTypeSpecProps
public import Strata.DL.Lambda.Denote.LExprAnnotated
public import Strata.DL.Lambda.Denote.LExprAnnotatedProps
public import Strata.DL.Lambda.Denote.LExprResolveAnnotated
public import Strata.DL.Lambda.FactoryWF
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.LExprTProps
public import Strata.DL.Lambda.TypeFactoryProps
public import Strata.Util.StringProps
public import Strata.Util.ListUtilsProps
public import Strata.Util.HMapsProps
import Strata.Util.NameProofs
import Strata.DL.Imperative.CmdProps
public import Strata.Languages.Core.WF
import Strata.Languages.Core.StatementProps
import Strata.Languages.Core.ProcedureProps
public import Strata.Languages.Core.Typing.Props.CmdTypeSpecProps
import all Strata.Languages.Core.Typing.Props.CmdTypeSpecProps
import Strata.Languages.Core.CallWFProps
import Strata.Languages.Core.IdentifiersProps
import Strata.DL.Lambda.LTyWFCheckSound
import Strata.DL.Lambda.LTyWF
import all Strata.Languages.Core.TypeSkolem
import all Strata.Languages.Core.Typing.Spec.TypeSpecShared
import all Strata.Languages.Core.Typing.Soundness.TypingAssumptions
import Strata.DL.Lambda.LExprAliasFree
import Strata.DL.Lambda.LExprAnnotRel
import Strata.DL.Lambda.LExprWFProps
import all Strata.Languages.Core.Statement
import all Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.Stmt
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.LTyProps
import Strata.DL.Lambda.Factory
import Strata.DL.Lambda.LTyWFProps
import Strata.DL.Lambda.NamePrefixesProps
import all Strata.Languages.Core.Procedure
import Strata.DL.Imperative.MetaDataProps

/-! # Rigid type parameters: names, renaming and skolemizer equations

Rigid-name conditions, type-parameter renaming, and equations for skolemization and
deskolemization on types, expressions and statements.

Key theorems:
* `rigidNamesAvoiding_spec`: the rigid constants are distinct and avoid the given names.
* `reservedTypeArgsRenaming_tyArgRenaming`: the renaming of reserved type parameters is
  injective and captures nothing. -/

public section

namespace Core

open Lambda Imperative

/-! ## Conditions and measures on rigid names -/

/-- The type constructor names in the type annotations of `e` and in the types of its
    literals. -/
def exprTyNames (e : Expression.Expr) : List String :=
  (exprAnnotTys e).flatMap getTypeRefs ++ exprLitTyNames e

/-- The type annotations of an optional expression. -/
def exprOrNondetAnnotTys (e : ExprOrNondet Expression) : List LMonoTy :=
  e.toList.flatMap exprAnnotTys

/-- The type constructor names in the types of the literals of a statement. -/
def stmtLitTyNames (s : Statement) : List String :=
  stmtCollect exprLitTyNames (fun _ => []) s

/-- The type constructor names in the types of the literals of a statement list. -/
def stmtsLitTyNames (ss : List Statement) : List String :=
  stmtsCollect exprLitTyNames (fun _ => []) ss

/-- `nm` is none of the constants of `σ`. -/
def notRigidConst (σ : RigidNames) (nm : String) : Bool :=
  σ.all fun p => p.2 != nm

/-- Every type `Csk` registers under a name that is not a constant of `σ`, `Crig` registers at
    the same arity. -/
def KnownTypesTransfer {T : LExprParams} (σ : RigidNames) (Csk Crig : LContext T) :
    Prop :=
  ∀ name n, σ.find? (fun p => p.2 == name) = none →
    Csk.knownTypes.contains { name := name, metadata := n } = true →
    Crig.knownTypes.contains { name := name, metadata := n } = true

mutual
/-- Size of a monotype, counting one for each constructor node. -/
def tySize (mty : LMonoTy) : Nat :=
  match mty with
  | .ftvar _ => 1
  | .bitvec _ => 1
  | .tcons _ args => 1 + tysSize args
/-- Size of a list of monotypes, counting one for each list cell plus the size of each
    member. -/
def tysSize (mtys : LMonoTys) : Nat :=
  match mtys with
  | [] => 0
  | mty :: rest => 1 + tySize mty + tysSize rest
end

/-- Deskolemizing `t` by `σ` keeps every type variable of `t`. -/
def deskolKeeps (σ : RigidNames) (t : LMonoTy) : Bool :=
  (LMonoTy.freeVars t).all fun v => (LMonoTy.freeVars (deskolemizeTy σ t)).contains v

/-- `Fsk` and `Frig` have the same names, and each `Frig` signature is the deskolemized `Fsk`
    signature. -/
def FactorySigDeskolemizes (σ : RigidNames)
    (Fsk Frig : Lambda.Factory CoreLParams) : Prop :=
  ∀ nm : String, (Fsk[nm]?).isSome = (Frig[nm]?).isSome ∧
    ∀ f ty, Fsk[nm]? = some f → f.type = .ok ty →
      ∃ f', Frig[nm]? = some f' ∧
        f'.type = .ok (mapLTyTys (deskolemizeTy σ) ty)

/-- Every factory signature either is fixed by deskolemization or binds no rigid parameter name. -/
def FactorySigDeskolSafe (σ : RigidNames) (F : Lambda.Factory CoreLParams) : Prop :=
  ∀ (nm : String) (f : LFunc CoreLParams) (ty : LTy),
    F[nm]? = some f → f.type = .ok ty →
      mapLTyTys (deskolemizeTy σ) ty = ty ∨
        List.Disj ty.boundVars (σ.map Prod.fst)

/-- Each lookup in `Γp` is the `Γsk` lookup substituted by `S` and deskolemized. -/
def ScopeCorr (σ : RigidNames) (S : Subst) (Γsk Γp : TContext CoreLParams.IDMeta) : Prop :=
  ∀ k : CoreIdent, Γp.types.find? k
    = (Γsk.types.find? k).map (mapLTyTys (fun m => deskolemizeTy σ (LMonoTy.subst S m)))

/-- Prefixing `ρ` to `S` changes `S` only on `vars`. -/
def BinderOnly (ρ S : Subst) (vars : List TyIdentifier) : Prop :=
  ∀ k, k ∉ vars →
    LMonoTy.subst (ρ ++ S) (.ftvar k) = LMonoTy.subst S (.ftvar k)

/-- A step that only draws fresh type variables: the context and substitution are unchanged and
    the type-variable generator does not go backwards. -/
structure SourceExpr.GenOnly (Env Env' : Expression.TyEnv) : Prop where
  context : Env'.context = Env.context
  subst : Env'.stateSubstInfo = Env.stateSubstInfo
  tyGen : Env.genEnv.genState.tyGen ≤ Env'.genEnv.genState.tyGen

/-- Holds when no parameter `σ` renames is both a member of `l` and the parameter whose rigid
    constant heads a subterm of `mty`. -/
def annotNoRigidClashIn (σ : RigidNames) (l : List TyIdentifier)
    (mty : LMonoTy) : Bool :=
  mtyAllTyConsNames (fun nm => σ.all (fun p => !(p.2 == nm) || !(l.contains p.1))) mty

/-- Holds when no parameter `σ` renames is both free in `mty` and the parameter whose rigid
    constant heads a subterm of `mty`. -/
def annotNoRigidClash (σ : RigidNames) (mty : LMonoTy) : Bool :=
  annotNoRigidClashIn σ (LMonoTy.freeVars mty) mty

/-- An elaborated expression with `S` applied and each rigid constant of `σ` written back as the
    type variable it stands for. -/
abbrev finishDeskolemized (σ : RigidNames) (S : Subst) (eT : LExprT CoreLParams.mono) :
    Core.Expression.Expr :=
  LExpr.replaceUserProvidedType (LExpr.unresolved (LExpr.applySubstT eT S)) (deskolemizeTy σ)

/-- Registering the rigid constants keeps the function table. -/
theorem addSkolemTypes_functions (C : Core.Expression.TyContext) (σ : RigidNames) :
    (addSkolemTypes C σ).functions = C.functions := by
  simp only [addSkolemTypes]

/-- Registering the rigid constants keeps the factory's function signatures well formed. -/
theorem FactorySigWF.addSkolemTypes (C : Core.Expression.TyContext) (σ : RigidNames)
    (h : FactorySigWF C.functions) : FactorySigWF (addSkolemTypes C σ).functions := by
  simpa only [addSkolemTypes_functions] using h

/-- Adding a renaming's constants appends its parameters to the rigid type variables. -/
theorem rigidTypeVars_addSkolemTypes (C : Core.Expression.TyContext) (σ : RigidNames) :
    (addSkolemTypes C σ).rigidTypeVars = C.rigidTypeVars ++ σ.map Prod.fst := by
  simp only [addSkolemTypes]

/-- Every parameter a renaming maps is rigid after adding the renaming's constants. -/
theorem rigid_mem_addSkolemTypes (C : Expression.TyContext) (σ : RigidNames) :
    ∀ q ∈ σ, q.1 ∈ (addSkolemTypes C σ).rigidTypeVars := by
  intro q hq
  rw [rigidTypeVars_addSkolemTypes, List.mem_append]
  exact Or.inr (List.mem_map.mpr ⟨q, hq, rfl⟩)

/-! ## Properties of skolemization and deskolemization -/

section Collect

variable {β : Type} (fe : Expression.Expr → List β) (ft : LMonoTy → List β)
  (f : LMonoTy → LMonoTy) (g : β → β)
  (hfe : ∀ e, fe (mapExprTys f e) = (fe e).map g) (hft : ∀ t, ft (f t) = (ft t).map g)

include hft in
/-- If applying `f` to a type maps `g` over what `ft` collects from it, then applying `f` to
    the body of every type scheme in a list maps `g` over what `ft` collects from the bodies. -/
private theorem flatMap_mapLTyTys (tys : List LTy) :
    (tys.map (mapLTyTys f)).flatMap (fun ty => ft ty.toMonoTypeUnsafe) =
      (tys.flatMap fun ty => ft ty.toMonoTypeUnsafe).map g := by
  induction tys with
  | nil => rfl
  | cons ty rest ih =>
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, List.map_append, ih]
    cases ty
    simp only [mapLTyTys, LTy.toMonoTypeUnsafe, hft]

include hfe hft in
/-- If applying `f` to every annotation of an expression maps `g` over what `fe` collects from
    it, and applying `f` to a type maps `g` over what `ft` collects from it, then applying `f`
    to every annotation of a command maps `g` over what `cmdCollect` lists. -/
private theorem cmdCollect_mapCmdTys (c : Command) :
    cmdCollect fe ft (mapCmdTys f c) = (cmdCollect fe ft c).map g := by
  cases c with
  | cmd cc =>
    cases cc with
    | init _ ty e _ =>
      cases ty
      cases e <;> simp only [mapCmdTys, mapCmdWith, mapLTyTys, ExprOrNondet.map, cmdCollect,
        CmdExt.initTypes, Cmd.initTypes, Statement.cmdTyArgs, Statement.cmdExprs, Cmd.readExprs,
        ExprOrNondet.toList, LTy.toMonoTypeUnsafe, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.map_append, hft, hfe]
    | set _ e _ =>
      cases e <;> simp only [mapCmdTys, mapCmdWith, ExprOrNondet.map, cmdCollect, CmdExt.initTypes,
        Cmd.initTypes, Statement.cmdTyArgs, Statement.cmdExprs, Cmd.readExprs,
        ExprOrNondet.toList, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.nil_append, List.map_nil, hfe]
    | assert _ _ _ | assume _ _ _ | cover _ _ _ =>
      simp only [mapCmdTys, mapCmdWith, cmdCollect, CmdExt.initTypes, Cmd.initTypes,
        Statement.cmdTyArgs, Statement.cmdExprs, Cmd.readExprs, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.nil_append, hfe]
  | call _ tyArgs args _ =>
    have htys : ((tyArgs.map (·.map (mapLTyTys f))).getD []).flatMap
          (fun ty => ft ty.toMonoTypeUnsafe) =
        ((tyArgs.getD []).flatMap fun ty => ft ty.toMonoTypeUnsafe).map g := by
      cases tyArgs with
      | none => rfl
      | some tys => exact flatMap_mapLTyTys ft f g hft tys
    have hargs : (CallArg.getInputExprs (args.map (CallArg.mapInput (mapExprTys f)))).flatMap fe =
        ((CallArg.getInputExprs args).flatMap fe).map g := by
      induction args with
      | nil => rfl
      | cons a rest ih =>
        cases a with
        | inArg e =>
          simp only [List.map_cons, CallArg.mapInput, CallArg.getInputExprs_cons_inArg,
            List.flatMap_cons, List.map_append, hfe]
          rw [ih]
        | inoutArg id =>
          have hfvar := hfe (LExpr.fvar Core.coreLoc id none)
          rw [mapExprTys, LExpr.replaceUserProvidedType, Option.map_none] at hfvar
          simp only [List.map_cons, CallArg.mapInput, CallArg.getInputExprs_cons_inoutArg,
            List.flatMap_cons, List.map_append, ih]
          rw [← hfvar]
        | outArg id =>
          simp only [List.map_cons, CallArg.mapInput, CallArg.getInputExprs_cons_outArg, ih]
    simp only [mapCmdTys, mapCmdWith, cmdCollect, CmdExt.initTypes, Statement.cmdTyArgs,
      Statement.cmdExprs, List.flatMap_nil, List.nil_append, List.map_append, htys, hargs]

include hfe hft in
/-- If applying `f` to every annotation of an expression maps `g` over what
    `fe` collects, and applying `f` to a type maps `g` over what `ft`
    collects, then applying `f` to every annotation of a statement list maps
    `g` over what `stmtsCollect` lists. -/
private theorem stmtsCollect_mapStmtsTys (ss : List Statement) :
    stmtsCollect fe ft (mapStmtsTys f ss) = (stmtsCollect fe ft ss).map g := by
  induction ss using Block.mapExpr.induct
    (motive1 := fun s => stmtCollect fe ft (mapStmtTys f s) = (stmtCollect fe ft s).map g) <;>
    simp_all [mapStmtTys_cmd, mapStmtTys_block, mapStmtTys_ite, mapStmtTys_loop,
      mapStmtTys_exit, mapStmtTys_typeDecl, mapStmtsTys_nil, mapStmtsTys_cons, ExprOrNondet.map,
      stmtCollect, stmtsCollect, stmtOwnCollect, ExprOrNondet.toList,
      Statement.loopExprs,
      cmdCollect_mapCmdTys fe ft f g hfe hft, List.map_flatMap, List.flatMap_map,
      Option.toList_map]

end Collect

/-- If applying the renaming `ren` to every annotation maps `g` over what `fe` collects from an
    expression and over what `ft` collects from a type, then renaming a procedure's type
    parameters maps `g` over what `procCollect` lists. -/
private theorem procCollect_renameTypeArgs {β : Type} (fe : Expression.Expr → List β)
    (ft : LMonoTy → List β) (g : β → β) (ren : List (String × String))
    (hfe : ∀ e, fe (mapExprTys (LMonoTy.subst (Subst.ofRenaming ren)) e) = (fe e).map g)
    (hft : ∀ t, ft (LMonoTy.subst (Subst.ofRenaming ren) t) = (ft t).map g)
    (proc : Procedure) :
    procCollect fe ft (proc.renameTypeArgs ren) = (procCollect fe ft proc).map g := by
  have hchk : ∀ cs : ListMap CoreLabel Procedure.Check,
      (ListMap.values (List.map (fun p => (p.1,
        (⟨mapExprTys (LMonoTy.subst (Subst.ofRenaming ren)) p.2.expr, p.2.attr, p.2.md⟩ :
          Procedure.Check))) cs)).flatMap (fun chk => fe chk.expr) =
        (cs.values.flatMap fun chk => fe chk.expr).map g := by
    intro cs
    rw [ListMap.values_map_snd cs fun c =>
      (⟨mapExprTys (LMonoTy.subst (Subst.ofRenaming ren)) c.expr, c.attr, c.md⟩ :
        Procedure.Check)]
    simp only [List.flatMap_map, List.map_flatMap, hfe]
  unfold procCollect bodyCollect Procedure.renameTypeArgs Procedure.mapTys
  simp only [hchk, List.map_append]
  cases proc.body with
  | structured ss =>
    simp only [stmtsCollect_mapStmtsTys fe ft _ g hfe hft]
  | abstract => simp
  | cfg c =>
    have hc := fun cmd => cmdCollect_mapCmdTys fe ft _ g hfe hft cmd
    simp only [DetCFG.mapCmdsGuards, List.flatMap_map, List.map_flatMap, List.map_append, hc]
    congr 2
    funext lb
    cases lb.2.transfer <;>
      simp only [hfe, List.map_nil, Imperative.MetaData.exprs_mapExprs, List.flatMap_map]

/-- Mapping over the type annotations of a statement list keeps the types it declares. -/
private theorem mapStmtsTys_localTypeDecls (f : LMonoTy → LMonoTy) (ss : List Statement) :
    Imperative.Block.localTypeDecls (mapStmtsTys f ss) = Imperative.Block.localTypeDecls ss := by
  induction ss using Block.mapExpr.induct
    (motive1 := fun s => Imperative.Stmt.localTypeDecls (mapStmtTys f s) =
      Imperative.Stmt.localTypeDecls s) <;>
    simp_all [mapStmtTys_cmd, mapStmtTys_block, mapStmtTys_ite, mapStmtTys_loop,
      mapStmtTys_exit, mapStmtTys_typeDecl, mapStmtsTys_nil, mapStmtsTys_cons, ExprOrNondet.map,
      Imperative.Stmt.localTypeDecls, Imperative.Block.localTypeDecls]

/-! ### `skolemizeTy` closes a type -/

/-- Skolemizing all of a type's free variables gives a closed type. -/
theorem LMonoTy.freeVars_skolemizeTy_eq_nil (σ : RigidNames) (mty : LMonoTy)
    (h : ∀ v ∈ LMonoTy.freeVars mty, v ∈ σ.map Prod.fst) :
    LMonoTy.freeVars (skolemizeTy σ mty) = [] := by
  unfold skolemizeTy
  refine LMonoTy.freeVars_subst_ground _ mty ?_
  intro a ha
  obtain ⟨q, hq, hqa⟩ := List.mem_map.mp (h a ha)
  cases hfind : σ.find? (fun p => p.1 == a) with
  | none =>
    have hne := List.find?_eq_none.mp hfind q hq
    simp only [hqa, beq_self_eq_true, not_true_eq_false] at hne
  | some p =>
    have hbound : Strata.Util.HMaps.find? (Subst.ofNullaryConsts σ) a
        = some (LMonoTy.tcons p.2 []) := by
      rw [Subst.find?_ofNullaryConsts, hfind, Option.map_some]
    rw [LMonoTy.subst_ftvar_of_some hbound]
    simp only [LMonoTy.freeVars, LMonoTys.freeVars]

/-! ### Properties of the rigid names `mintRigidNames` chooses

Each chosen constant has the rigid prefix and is new, so the renaming is injective. -/

/-- When `l` holds every taken name and `fuel` is at least its length, `mintRigidNames` names
    exactly `typeArgs`, in order, with distinct rigid-prefixed constants that are not taken. -/
private theorem mintRigidNames_spec (name : String) (taken : String → Bool) (fuel : Nat)
    (typeArgs : List String) (l : List String) (hl : ∀ n, taken n = true → n ∈ l)
    (hfuel : l.length ≤ fuel) :
    RigidNamesPrefixed (mintRigidNames name taken fuel typeArgs) ∧
      ((mintRigidNames name taken fuel typeArgs).map Prod.snd).Nodup ∧
      (mintRigidNames name taken fuel typeArgs).map Prod.fst = typeArgs ∧
      ∀ p ∈ mintRigidNames name taken fuel typeArgs, taken p.2 = false := by
  obtain ⟨hlen, hnd, hfresh, hpfx⟩ := Strata.Name.freshNamesBy_spec
    (typeArgs.map fun a => skolemName s!"{name}_{a}") taken fuel l hl hfuel
  rw [List.length_map] at hlen
  unfold mintRigidNames
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨b, hb, t, ht⟩ := hpfx p.2 (List.of_mem_zip hp).2
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hb
    exact ⟨s!"{name}_{a}" ++ t, by rw [ht, skolemName, String.append_assoc]⟩
  · rw [List.map_snd_zip (Nat.le_of_eq hlen)]
    exact hnd
  · exact List.map_fst_zip (Nat.le_of_eq hlen.symm)
  · intro p hp
    exact hfresh p.2 (List.of_mem_zip hp).2

/-- `rigidNamesAvoiding` pairs `typeArgs`, in order, with distinct rigid-prefixed constants that
    are neither registered types nor names of `scope`, `progSigs` or `own ()`. -/
theorem rigidNamesAvoiding_spec (C : Expression.TyContext)
    (scope progSigs : Thunk (Std.HashSet String)) (name : String) (own : Unit → List String)
    (typeArgs : List String) :
    RigidNamesPrefixed (rigidNamesAvoiding C scope progSigs name own typeArgs) ∧
      ((rigidNamesAvoiding C scope progSigs name own typeArgs).map Prod.snd).Nodup ∧
      RigidNamesFresh C.knownTypes (rigidNamesAvoiding C scope progSigs name own typeArgs) ∧
      (rigidNamesAvoiding C scope progSigs name own typeArgs).map Prod.fst = typeArgs ∧
      ∀ p ∈ rigidNamesAvoiding C scope progSigs name own typeArgs,
        p.2 ∉ scope.get ∧ p.2 ∉ progSigs.get ∧ p.2 ∉ own () := by
  unfold rigidNamesAvoiding
  split
  · rename_i hempty
    rw [List.isEmpty_iff.mp hempty]
    exact ⟨fun p hp => absurd hp List.not_mem_nil, List.nodup_nil,
      fun p hp => absurd hp List.not_mem_nil, rfl, fun p hp => absurd hp List.not_mem_nil⟩
  · generalize scope.get = s
    generalize progSigs.get = q
    generalize ho : (Std.HashSet.ofList (own ()) : Std.HashSet String) = o
    have hl : ∀ n, (C.knownTypes.containsName n || s.contains n || q.contains n ||
        o.contains n) = true → n ∈ C.knownTypes.keys ++ s.toList ++ q.toList ++ o.toList := by
      intro n hn
      simp only [Bool.or_eq_true_iff] at hn
      simp only [List.mem_append]
      rcases hn with ((hk | hs) | hq) | hm
      · exact Or.inl (Or.inl (Or.inl (Std.HashMap.mem_keys.mpr
          ((KnownTypes.containsName_eq_true_iff_mem _ _).mp hk))))
      · exact Or.inl (Or.inl (Or.inr (Std.HashSet.mem_toList.mpr
          (Std.HashSet.mem_iff_contains.mpr hs))))
      · exact Or.inl (Or.inr (Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hq)))
      · exact Or.inr (Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hm))
    have hfuel : (C.knownTypes.keys ++ s.toList ++ q.toList ++ o.toList).length
        ≤ C.knownTypes.size + s.size + q.size + o.size := by
      simp only [List.length_append, Std.HashMap.length_keys, Std.HashSet.length_toList]
      omega
    obtain ⟨hpfx, hnd, hfst, hfresh⟩ := mintRigidNames_spec name _ _ typeArgs _ hl hfuel
    have hnot : ∀ m, (C.knownTypes.containsName m || s.contains m || q.contains m ||
        o.contains m) = false → m ∉ C.knownTypes ∧ m ∉ s ∧ m ∉ q ∧ m ∉ own () := by
      intro m hmt
      simp only [Bool.or_eq_false_iff] at hmt
      obtain ⟨⟨⟨hk, hs⟩, hq⟩, hmo⟩ := hmt
      refine ⟨fun hm => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_⟩
      · rw [(KnownTypes.containsName_eq_true_iff_mem _ _).mpr hm] at hk
        cases hk
      · rw [Std.HashSet.mem_iff_contains.mp hm] at hs
        cases hs
      · rw [Std.HashSet.mem_iff_contains.mp hm] at hq
        cases hq
      · have hmem : m ∈ o := ho ▸ Std.HashSet.mem_ofList_of_mem _ hm
        rw [Std.HashSet.mem_iff_contains.mp hmem] at hmo
        cases hmo
    exact ⟨hpfx, hnd, fun p hp => (hnot _ (hfresh p hp)).1, hfst,
      fun p hp => (hnot _ (hfresh p hp)).2⟩

/-! ### The renaming of reserved type parameters -/

/-- A name starting with `a` starts with no reserved prefix. -/
private theorem isAllowedName_of_prefix_a {n : String} (h : "a".toList <+: n.toList) :
    isAllowedName n = true := by
  obtain ⟨rest, hrest⟩ := h
  rw [isAllowedName_eq_toList]
  simp only [← hrest]
  simp [reservedNamePrefixes, genTyPrefix, skolemPrefix, elimTyPrefix, precondTyVarPrefix,
    callTyVarPrefix, List.isPrefixOf]

/-- `List.lookup` finds every first component of the list. -/
private theorem lookup_isSome_of_mem {ren : List (String × String)} {a : String}
    (h : a ∈ ren.map Prod.fst) : (ren.lookup a).isSome = true := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  exact List.lookup_isSome_iff.mpr ⟨p, hp, beq_self_eq_true _⟩

/-- `reservedTypeArgsRenaming` pairs each reserved type parameter, in order, with a distinct
    allowed name outside `avoid ()`. -/
private theorem reservedTypeArgsRenaming_spec (typeArgs : List String)
    (avoid : Unit → List String) :
    (reservedTypeArgsRenaming typeArgs avoid).map Prod.fst =
        typeArgs.filter (!isAllowedName ·) ∧
      ((reservedTypeArgsRenaming typeArgs avoid).map Prod.snd).Nodup ∧
      ∀ p ∈ reservedTypeArgsRenaming typeArgs avoid,
        p.2 ∉ avoid () ∧ isAllowedName p.2 = true := by
  unfold reservedTypeArgsRenaming
  dsimp only
  split
  · rename_i hempty
    refine ⟨(List.isEmpty_iff.mp hempty).symm, List.nodup_nil, ?_⟩
    intro p hp
    exact absurd hp List.not_mem_nil
  · let reserved := typeArgs.filter (!isAllowedName ·)
    let bases := reserved.map fun _ => "a"
    let taken := Std.HashSet.ofList (avoid ())
    have hlen : (Strata.Name.freshNames taken bases).1.length = reserved.length := by
      rw [Strata.Name.freshNames_length, List.length_map]
    refine ⟨?_, ?_, ?_⟩
    · exact List.map_fst_zip (Nat.le_of_eq hlen.symm)
    · rw [List.map_snd_zip (Nat.le_of_eq hlen)]
      exact Strata.Name.freshNames_nodup taken bases
    · intro p hp
      have hfresh := (List.of_mem_zip hp).2
      refine ⟨?_, ?_⟩
      · intro hmem
        refine Strata.Name.freshNames_not_mem taken bases p.2 hfresh ?_
        exact Std.HashSet.mem_ofList_of_mem _ hmem
      · obtain ⟨b, hb, hpre⟩ := Strata.Name.freshNames_prefix taken bases p.2 hfresh
        obtain ⟨-, -, rfl⟩ := List.mem_map.mp hb
        exact isAllowedName_of_prefix_a hpre

/-- Type parameters with no reserved prefix get the empty renaming. -/
theorem reservedTypeArgsRenaming_of_allowed {typeArgs : List String}
    (avoid : Unit → List String) (h : ∀ a ∈ typeArgs, isAllowedName a = true) :
    reservedTypeArgsRenaming typeArgs avoid = [] := by
  have hkept : ∀ a ∈ typeArgs, ¬ (!isAllowedName a) = true := by
    intro a ha
    simp only [h a ha, Bool.not_true, Bool.false_eq_true, not_false_eq_true]
  have hnil : typeArgs.filter (!isAllowedName ·) = [] := List.filter_eq_nil_iff.mpr hkept
  unfold reservedTypeArgsRenaming
  simp only [hnil, List.isEmpty_nil, ite_true]

/-- After the reserved renaming, every type parameter is an allowed name. -/
theorem renameTyArgList_reserved_allowed (typeArgs : List String)
    (avoid : Unit → List String) :
    ∀ a ∈ renameTyArgList (reservedTypeArgsRenaming typeArgs avoid) typeArgs,
      isAllowedName a = true := by
  obtain ⟨hfst, -, hren⟩ := reservedTypeArgsRenaming_spec typeArgs avoid
  intro a' ha'
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
  cases hlook : (reservedTypeArgsRenaming typeArgs avoid).lookup a with
  | some n => exact (hren (a, n) (List.mem_of_lookup_eq_some hlook)).2
  | none =>
    simp only [Option.getD_none]
    cases hallowed : isAllowedName a with
    | true => rfl
    | false =>
      have hreserved : (!isAllowedName a) = true := by
        simp only [hallowed, Bool.not_false]
      have hmem : a ∈ (reservedTypeArgsRenaming typeArgs avoid).map Prod.fst := by
        rw [hfst]
        exact List.mem_filter.mpr ⟨ha, hreserved⟩
      have hsome := lookup_isSome_of_mem hmem
      rw [hlook] at hsome
      exact absurd hsome Bool.false_ne_true

/-- If the renamed type parameters are distinct, so are the original ones. -/
theorem nodup_of_renameTyArgList {ren : List (String × String)} {typeArgs : List String}
    (h : (renameTyArgList ren typeArgs).Nodup) : typeArgs.Nodup := by
  refine (List.pairwise_map.mp h).imp ?_
  intro a b hne hab
  subst hab
  exact hne rfl

/-- Each renamed type parameter is a type parameter `ren` keeps or a name `ren` introduces. -/
theorem mem_renameTyArgList {ren : List (String × String)} {typeArgs : List String}
    {a' : String} (h : a' ∈ renameTyArgList ren typeArgs) :
    (a' ∈ typeArgs ∧ ren.lookup a' = none) ∨ ∃ p ∈ ren, p.2 = a' := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
  cases hlook : ren.lookup a with
  | some n => exact Or.inr ⟨(a, n), List.mem_of_lookup_eq_some hlook, rfl⟩
  | none =>
    simp only [Option.getD_none]
    exact Or.inl ⟨ha, hlook⟩

/-- A renaming of distinct type parameters `typeArgs` takes a type whose type variables are all
    in `typeArgs` to one whose type variables are all among the renamed type parameters. -/
theorem freeVars_subst_ofRenaming_mem {ren : List (String × String)} {typeArgs : List String}
    {t : LMonoTy} (hfst : (ren.map Prod.fst).Nodup) (hsrc : ∀ p ∈ ren, p.1 ∈ typeArgs)
    (ht : ∀ v ∈ LMonoTy.freeVars t, v ∈ typeArgs) :
    ∀ v ∈ LMonoTy.freeVars (LMonoTy.subst (Subst.ofRenaming ren) t),
      v ∈ renameTyArgList ren typeArgs := by
  intro v hv
  rcases LMonoTy.mem_freeVars_subst _ t v hv with hρ | ⟨hvt, hnone⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (Subst.mem_freeVars_ofRenaming hρ)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp
      (lookup_isSome_of_mem (List.mem_map_of_mem (f := Prod.fst) hp))
    have hfindP := Strata.Util.HMap.find?_ofList_of_mem_of_nodup hfst hp
    have hfindN := Strata.Util.HMap.find?_ofList_of_mem_of_nodup hfst
      (List.mem_of_lookup_eq_some hn)
    have heq : n = p.2 := Option.some.inj (hfindN.symm.trans hfindP)
    refine List.mem_map.mpr ⟨p.1, hsrc p hp, ?_⟩
    simp only [hn, Option.getD_some, heq]
  · have hlook : ren.lookup v = none := by
      cases hl : ren.lookup v with
      | none => rfl
      | some n =>
        have hmem := List.mem_map_of_mem (f := fun p => (p.1, LMonoTy.ftvar p.2))
          (List.mem_of_lookup_eq_some hl)
        have hnd : ((ren.map fun p => (p.1, LMonoTy.ftvar p.2)).map Prod.fst).Nodup := by
          rw [List.map_map]
          exact hfst
        have hfind := Strata.Util.HMap.find?_ofList_of_mem_of_nodup hnd hmem
        simp only [Subst.ofRenaming, Strata.Util.HMaps.find?_single_scope] at hnone
        rw [hnone] at hfind
        cases hfind
    refine List.mem_map.mpr ⟨v, ht v hvt, ?_⟩
    simp only [hlook, Option.getD_none]

/-- A type variable of `t` that `ren` does not rename is a type variable of `t` renamed by
    `ren`. -/
theorem mem_freeVars_subst_ofRenaming_of_not_mem {ren : List (String × String)} {v : String}
    (t : LMonoTy) (hv : v ∈ LMonoTy.freeVars t) (hnot : v ∉ ren.map Prod.fst) :
    v ∈ LMonoTy.freeVars (LMonoTy.subst (Subst.ofRenaming ren) t) := by
  induction t with
  | ftvar y =>
    simp only [LMonoTy.freeVars, List.mem_singleton] at hv
    subst hv
    rw [LMonoTy.subst_ftvar_of_none (Strata.Util.HMaps.not_mem_keys_find?_none _ v
      fun hk => hnot (Subst.mem_keys_ofRenaming hk))]
    simp only [LMonoTy.freeVars, List.mem_singleton]
  | bitvec n => simp only [LMonoTy.freeVars, List.not_mem_nil] at hv
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons_map, LMonoTy.freeVars]
    simp only [LMonoTy.freeVars] at hv
    obtain ⟨a, ha, hva⟩ := LMonoTys.freeVars_exists hv
    exact LMonoTys.freeVars_mem_subset (List.mem_map_of_mem ha) (ih a ha hva)

/-- The reserved renaming of distinct type parameters, chosen outside a list containing the
    type variables `mentioned`, the rigid type variables of `C` and the free type variables of
    the variables of `Γ`, is a renaming of reserved type parameters that avoids them. -/
theorem reservedTypeArgsRenaming_tyArgRenaming {C : LContext CoreLParams} {Γ : TContext Unit}
    {typeArgs mentioned : List String} (avoid : Unit → List String) (hnd : typeArgs.Nodup)
    (hsub : ∀ v ∈ mentioned ++ C.rigidTypeVars ++ Γ.knownTypeVars, v ∈ avoid ()) :
    TypeSpec.TyArgRenaming C Γ typeArgs mentioned (reservedTypeArgsRenaming typeArgs avoid) := by
  obtain ⟨hfst, hsnd, hren⟩ := reservedTypeArgsRenaming_spec typeArgs avoid
  have hmem : ∀ p ∈ reservedTypeArgsRenaming typeArgs avoid,
      p.1 ∈ typeArgs ∧ isAllowedName p.1 = false := by
    intro p hp
    have hfilter : p.1 ∈ typeArgs.filter (!isAllowedName ·) := hfst ▸ List.mem_map_of_mem hp
    obtain ⟨hin, hreserved⟩ := List.mem_filter.mp hfilter
    have hfalse : isAllowedName p.1 = false := by
      simpa using hreserved
    exact ⟨hin, hfalse⟩
  have hnot : ∀ p ∈ reservedTypeArgsRenaming typeArgs avoid,
      ∀ v ∈ mentioned ++ C.rigidTypeVars ++ Γ.knownTypeVars, p.2 ≠ v := by
    intro p hp v hv heq
    exact (hren p hp).1 (heq ▸ hsub v hv)
  refine ⟨⟨?_, hsnd, fun p hp => ⟨(hmem p hp).1, ?_⟩⟩, fun p hp => ⟨(hmem p hp).2, ?_, ?_⟩⟩
  · rw [hfst]
    exact hnd.sublist List.filter_sublist
  · exact fun hm => hnot p hp _ (List.mem_append_left _ (List.mem_append_left _ hm)) rfl
  · exact fun hm => hnot p hp _ (List.mem_append_left _ (List.mem_append_right _ hm)) rfl
  · exact TContext.isFresh_of_not_mem_knownTypeVars fun hk =>
      hnot p hp _ (List.mem_append_right _ hk) rfl

/-- A renaming of reserved type parameters for one context is one for any context with the same
    rigid type variables and the same variable lookups. -/
theorem TypeSpec.TyArgRenaming.congr {C C' : LContext CoreLParams} {Γ Γ' : TContext Unit}
    {typeArgs mentioned : List String} {ren : List (String × String)}
    (hrigid : C'.rigidTypeVars = C.rigidTypeVars)
    (hscope : TContext.FindEq (T := CoreLParams) Γ' Γ)
    (h : TypeSpec.TyArgRenaming C Γ typeArgs mentioned ren) :
    TypeSpec.TyArgRenaming C' Γ' typeArgs mentioned ren := by
  obtain ⟨hcore, hren⟩ := h
  refine ⟨hcore, fun p hp => ?_⟩
  obtain ⟨hreserved, hnot, hfresh⟩ := hren p hp
  rw [← hrigid] at hnot
  exact ⟨hreserved, hnot, fun x ty hfind => hfresh x ty ((hscope.1 x).symm.trans hfind)⟩

/-- A renaming of reserved type parameters among type parameters that all have allowed names is
    empty: a declaration without reserved type parameters is its only renaming. -/
theorem TypeSpec.TyArgRenaming.eq_nil_of_allowed {C : LContext CoreLParams} {Γ : TContext Unit}
    {typeArgs mentioned : List String} {ren : List (String × String)}
    (hallowed : ∀ a ∈ typeArgs, isAllowedName a = true)
    (h : TypeSpec.TyArgRenaming C Γ typeArgs mentioned ren) : ren = [] := by
  obtain ⟨⟨-, -, hcore⟩, hren⟩ := h
  cases ren with
  | nil => rfl
  | cons p _ =>
    have hin := (hcore p List.mem_cons_self).1
    have hreserved := (hren p List.mem_cons_self).1
    rw [hallowed _ hin] at hreserved
    cases hreserved

/-- Two pairs of a list whose second components are distinct are equal when their second
    components are. -/
private theorem eq_of_mem_of_snd_eq {ren : List (String × String)}
    (h : (ren.map Prod.snd).Nodup) {p q : String × String} (hp : p ∈ ren) (hq : q ∈ ren)
    (he : p.2 = q.2) : p = q := by
  induction ren with
  | nil => exact absurd hp List.not_mem_nil
  | cons r rest ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hp with rfl | hp'
    · rcases List.mem_cons.mp hq with rfl | hq'
      · rfl
      · exact absurd (he ▸ List.mem_map_of_mem (f := Prod.snd) hq') h.1
    · rcases List.mem_cons.mp hq with rfl | hq'
      · exact absurd (he.symm ▸ List.mem_map_of_mem (f := Prod.snd) hp') h.1
      · exact ih h.2 hp' hq'

/-- Renaming distinct type parameters injectively to names outside a list containing them keeps
    them distinct. -/
theorem renameTyArgList_nodup {typeArgs mentioned : List String} {ren : List (String × String)}
    (hnd : typeArgs.Nodup) (hren : TypeSpec.TyArgRenamingCore typeArgs mentioned ren)
    (hsub : ∀ a ∈ typeArgs, a ∈ mentioned) : (renameTyArgList ren typeArgs).Nodup := by
  obtain ⟨-, hsnd, hrn⟩ := hren
  have hkey : ∀ a ∈ typeArgs, ∀ b ∈ typeArgs,
      (ren.lookup a).getD a = (ren.lookup b).getD b → a = b := by
    intro a ha b hb hab
    cases hla : ren.lookup a with
    | some n =>
      have hpa := List.mem_of_lookup_eq_some hla
      cases hlb : ren.lookup b with
      | some m =>
        have hpb := List.mem_of_lookup_eq_some hlb
        simp only [hla, hlb, Option.getD_some] at hab
        subst hab
        exact (Prod.mk.inj (eq_of_mem_of_snd_eq hsnd hpa hpb rfl)).1
      | none =>
        simp only [hla, hlb, Option.getD_some, Option.getD_none] at hab
        exact absurd (hab ▸ hsub b hb) (hrn _ hpa).2
    | none =>
      cases hlb : ren.lookup b with
      | some m =>
        have hpb := List.mem_of_lookup_eq_some hlb
        simp only [hla, hlb, Option.getD_some, Option.getD_none] at hab
        exact absurd (hab ▸ hsub a ha) (hrn _ hpb).2
      | none =>
        simp only [hla, hlb, Option.getD_none] at hab
        exact hab
  unfold renameTyArgList
  exact List.pairwise_map.mpr (hnd.imp_of_mem fun ha hb hne hab => hne (hkey _ ha _ hb hab))

/-- Renaming no type parameter leaves a lemma unchanged. -/
theorem Lemma.renameTypeArgs_nil (l : Lemma) : l.renameTypeArgs [] = l := by
  obtain ⟨name, typeArgs, e⟩ := l
  simp only [Lemma.renameTypeArgs, LMonoTy.subst_ofRenaming_nil, mapExprTys_id, renameTyArgList,
    List.lookup_nil, Option.getD_none, List.map_id_fun', id_eq]

/-- `renameReservedWith` returns `x` when the reserved renaming is empty, and otherwise `rename`
    of that renaming. -/
theorem renameReservedWith_cases {α : Type} (typeArgs : List String)
    (avoid : Unit → List String) (rename : List (String × String) → α) (x : α) :
    (renameReservedWith typeArgs avoid rename x = x ∧
        reservedTypeArgsRenaming typeArgs avoid = []) ∨
      renameReservedWith typeArgs avoid rename x =
        rename (reservedTypeArgsRenaming typeArgs avoid) := by
  unfold renameReservedWith
  dsimp only
  split
  · rename_i hempty
    exact Or.inl ⟨rfl, List.isEmpty_iff.mp hempty⟩
  · exact Or.inr rfl

/-- When renaming by the empty list returns `x`, `renameReservedWith` is `rename` of the
    reserved renaming, whether or not that renaming is empty. -/
theorem renameReservedWith_eq_of_nil {α : Type} {typeArgs : List String}
    {avoid : Unit → List String} {rename : List (String × String) → α} {x : α}
    (hnil : rename [] = x) :
    renameReservedWith typeArgs avoid rename x =
      rename (reservedTypeArgsRenaming typeArgs avoid) := by
  rcases renameReservedWith_cases typeArgs avoid rename x with ⟨heq, hren⟩ | heq
  · rw [heq, hren, hnil]
  · exact heq

/-- `renameReservedTypeArgs` renames a lemma by its reserved renaming. -/
theorem Lemma.renameReservedTypeArgs_eq (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (l : Lemma) (annot : Unit → List LMonoTy) :
    l.renameReservedTypeArgs C Env annot = l.renameTypeArgs
      (reservedTypeArgsRenaming l.typeArgs fun u =>
        l.mentionedTyVarsIn (annot u) ++ scopeTyVars C Env) :=
  renameReservedWith_eq_of_nil (Lemma.renameTypeArgs_nil l)

/-- After the checker's renaming, every type parameter of a lemma is an allowed name. -/
theorem Lemma.renameReservedTypeArgs_typeArgs_allowed (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (l : Lemma) (annot : Unit → List LMonoTy) :
    ∀ a ∈ (l.renameReservedTypeArgs C Env annot).typeArgs, isAllowedName a = true := by
  rw [Lemma.renameReservedTypeArgs_eq]
  exact renameTyArgList_reserved_allowed _ _

/-- Every name in `mentioned`, a rigid type variable of `C` or a free type variable of a variable
    in scope in `Env` is among `mentioned ++ scopeTyVars C Env`. -/
theorem mem_append_scopeTyVars {C : Core.Expression.TyContext} {Env : Core.Expression.TyEnv}
    {mentioned : List String} :
    ∀ v ∈ mentioned ++ C.rigidTypeVars ++ Env.context.knownTypeVars,
      v ∈ mentioned ++ scopeTyVars C Env := by
  intro v hv
  simpa only [scopeTyVars, List.append_assoc] using hv

/-- The checker's renaming of a lemma with distinct type parameters, checked in `C` and `Env`
    with written types `annot ()`, renames reserved type parameters injectively to names that are
    neither type parameters, type variables of `annot ()`, nor type variables of the context, and
    keeps them distinct. -/
theorem Lemma.renameReservedTypeArgs_tyArgRenaming (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (l : Lemma) (annot : Unit → List LMonoTy)
    (hnd : l.typeArgs.Nodup) :
    TypeSpec.TyArgRenaming C Env.context l.typeArgs (l.mentionedTyVarsIn (annot ()))
        (reservedTypeArgsRenaming l.typeArgs fun u =>
          l.mentionedTyVarsIn (annot u) ++ scopeTyVars C Env) ∧
      (l.renameReservedTypeArgs C Env annot).typeArgs.Nodup := by
  have hren := reservedTypeArgsRenaming_tyArgRenaming (C := C) (Γ := Env.context)
    (mentioned := l.mentionedTyVarsIn (annot ()))
    (fun u => l.mentionedTyVarsIn (annot u) ++ scopeTyVars C Env) hnd
    mem_append_scopeTyVars
  refine ⟨hren, ?_⟩
  rw [Lemma.renameReservedTypeArgs_eq]
  exact renameTyArgList_nodup hnd hren.1 fun a ha => List.mem_append_left _ ha

/-- `renameReservedTypeArgs` renames a procedure by its reserved renaming. -/
theorem Procedure.renameReservedTypeArgs_eq (avoid : Unit → List String) (proc : Procedure)
    (annot : Unit → List LMonoTy) :
    proc.renameReservedTypeArgs avoid annot = proc.renameTypeArgs
      (reservedTypeArgsRenaming proc.header.typeArgs
        (fun u => proc.mentionedTyVarsIn (annot u) ++ avoid u)) :=
  renameReservedWith_eq_of_nil (Procedure.renameTypeArgs_nil proc)

/-- After the checker's renaming, every type parameter of a procedure is an allowed name. -/
theorem Procedure.renameReservedTypeArgs_typeArgs_allowed (avoid : Unit → List String)
    (proc : Procedure) (annot : Unit → List LMonoTy) :
    ∀ a ∈ (proc.renameReservedTypeArgs avoid annot).header.typeArgs, isAllowedName a = true := by
  rw [Procedure.renameReservedTypeArgs_eq]
  exact renameTyArgList_reserved_allowed _ _

/-- If the renamed type parameters of a procedure are distinct, so are the original ones. -/
theorem Procedure.typeArgs_nodup_of_renameReservedTypeArgs (avoid : Unit → List String)
    (proc : Procedure) (annot : Unit → List LMonoTy)
    (h : (proc.renameReservedTypeArgs avoid annot).header.typeArgs.Nodup) :
    proc.header.typeArgs.Nodup := by
  rw [Procedure.renameReservedTypeArgs_eq] at h
  exact nodup_of_renameTyArgList h

/-- Each type parameter of the renamed procedure is one of its own or a new name outside
    `avoid ()`. -/
theorem Procedure.renameReservedTypeArgs_typeArgs_mem (avoid : Unit → List String)
    (proc : Procedure) (annot : Unit → List LMonoTy) :
    ∀ a ∈ (proc.renameReservedTypeArgs avoid annot).header.typeArgs,
      a ∈ proc.header.typeArgs ∨ a ∉ avoid () := by
  intro a ha
  rw [Procedure.renameReservedTypeArgs_eq] at ha
  rcases mem_renameTyArgList ha with ⟨hmem, -⟩ | ⟨p, hp, rfl⟩
  · exact Or.inl hmem
  · exact Or.inr fun hn =>
      ((reservedTypeArgsRenaming_spec _ _).2.2 p hp).1 (List.mem_append_right _ hn)

/-- Renaming a procedure's distinct type parameters injectively to names it does not mention
    (`TyArgRenamingCore`) keeps them distinct, and keeps every type variable of the signature a
    type parameter. -/
theorem Procedure.renameTypeArgs_sigDeclared {proc : Procedure} {ren : List (String × String)}
    (hren : TypeSpec.TyArgRenamingCore proc.header.typeArgs proc.mentionedTyVars ren)
    (hnd : proc.header.typeArgs.Nodup) (hdecl : proc.header.SigDeclared) :
    (proc.renameTypeArgs ren).header.typeArgs.Nodup ∧
      (proc.renameTypeArgs ren).header.SigDeclared := by
  refine ⟨renameTyArgList_nodup hnd hren fun a ha => List.mem_append_left _ ha, ?_⟩
  obtain ⟨hvIn, hvOut⟩ := Procedure.renameTypeArgs_values proc ren
  have hsrc : ∀ p ∈ ren, p.1 ∈ proc.header.typeArgs := fun p hp => (hren.2.2 p hp).1
  have hty : ∀ tys : LMonoTys,
      (∀ v ∈ LMonoTys.freeVars tys, v ∈ proc.header.typeArgs) →
      ∀ v ∈ LMonoTys.freeVars (tys.map (LMonoTy.subst (Subst.ofRenaming ren))),
        v ∈ renameTyArgList ren proc.header.typeArgs := by
    intro tys htys v hv
    obtain ⟨t', ht', hvt⟩ := LMonoTys.freeVars_exists hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact freeVars_subst_ofRenaming_mem hren.1 hsrc
      (fun w hw => htys w (LMonoTys.freeVars_mem_subset ht hw)) v hvt
  intro v hv
  rw [hvIn, hvOut] at hv
  rcases List.mem_append.mp hv with hin | hout
  · exact hty _ (fun w hw => hdecl w (List.mem_append_left _ hw)) v hin
  · exact hty _ (fun w hw => hdecl w (List.mem_append_right _ hw)) v hout

/-- A procedure mentions each of its type parameters. -/
theorem Procedure.mem_mentionedTyVars_of_typeArg {proc : Procedure} {a : String}
    (ha : a ∈ proc.header.typeArgs) : a ∈ proc.mentionedTyVars := by
  unfold Procedure.mentionedTyVars Procedure.mentionedTyVarsIn declMentionedTyVarsIn
  exact List.mem_append_left _ ha

/-- Every type variable of a procedure's parameter types is one it mentions. -/
theorem Procedure.mem_mentionedTyVars_of_param {proc : Procedure} {t : LMonoTy}
    (ht : t ∈ proc.header.inputs.values ++ proc.header.outputs.values) :
    ∀ v ∈ LMonoTy.freeVars t, v ∈ proc.mentionedTyVars := by
  intro v hv
  unfold Procedure.mentionedTyVars Procedure.mentionedTyVarsIn declMentionedTyVarsIn procAnnotTys
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨t, ?_, hv⟩)
  rcases List.mem_append.mp ht with hin | hout
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ hin)))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hout)))

/-! ### Reserved name prefixes and user-declarable names -/

/-- The rigid prefix is a reserved name prefix. -/
private theorem skolemPrefix_mem_reservedNamePrefixes :
    skolemPrefix ∈ reservedNamePrefixes := by
  simp [skolemPrefix, reservedNamePrefixes]

/-- A name a user may declare does not carry the rigid prefix. -/
private theorem not_skolemPrefix_of_isAllowedName {n : String} (h : isAllowedName n = true) :
    skolemPrefix.toList.isPrefixOf n.toList = false := by
  simp only [isAllowedName_eq_toList, Bool.not_eq_true', List.any_eq_false] at h
  simpa [Bool.eq_false_iff] using h skolemPrefix skolemPrefix_mem_reservedNamePrefixes

/-- A name a user may write satisfies the type-variable policy for user-written types. -/
theorem TyVarAdmissibility.notGeneratedOrRigid_of_isAllowedName {n : String}
    (h : isAllowedName n = true) : TyVarAdmissibility.notGeneratedOrRigid n = true := by
  simp only [TyVarAdmissibility.notGeneratedOrRigid, Bool.and_eq_true, Bool.not_eq_true']
  exact ⟨Bool.eq_false_iff.mpr (not_genTyPrefix_of_isAllowedName h),
    not_skolemPrefix_of_isAllowedName h⟩

/-- The user-written type-variable policy rejects every name with the generated prefix. -/
theorem TyVarAdmissibility.notGeneratedOrRigid_not_genTyPrefix {v : TyIdentifier}
    (h : TyVarAdmissibility.notGeneratedOrRigid v = true) :
    genTyPrefix.toList.isPrefixOf v.toList = false := by
  simp only [TyVarAdmissibility.notGeneratedOrRigid, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1

/-- A successful `typeCheckSource` under the user-written policy agrees with instantiating the
    monotype as a scheme with no bound variables. -/
theorem typeCheckSource_notGeneratedOrRigid_instantiateWithCheck
    (ty resolved : LMonoTy) (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (h : ty.typeCheckSource C Env TyVarAdmissibility.notGeneratedOrRigid = .ok (resolved, Env')) :
    LTy.instantiateWithCheck (.forAll [] ty) C Env = .ok (resolved, Env') :=
  LMonoTy.typeCheckSource_instantiateWithCheck ty resolved C Env Env'
    TyVarAdmissibility.notGeneratedOrRigid
    (fun _ hv => TyVarAdmissibility.notGeneratedOrRigid_not_genTyPrefix hv) h

/-! ### Renaming lookups and registering rigid constants -/

/-- Skolemization maps a renamed type variable to its constant and fixes the others. -/
private theorem skolemizeTy_ftvar (σ : RigidNames) (x : String) :
    skolemizeTy σ (.ftvar x)
      = match σ.find? (fun p => p.1 == x) with
        | some p => .tcons p.2 []
        | none => .ftvar x := by
  cases hfind : σ.find? (fun p => p.1 == x) with
  | none =>
    exact LMonoTy.subst_ftvar_of_none
      (by rw [Subst.find?_ofNullaryConsts, hfind, Option.map_none])
  | some pr =>
    exact LMonoTy.subst_ftvar_of_some
      (by rw [Subst.find?_ofNullaryConsts, hfind, Option.map_some])

/-- A constant carrying the rigid prefix is never a name a user may declare. -/
private theorem rigid_ne_of_isAllowedName {nm n : String} (hnm : ∃ s, nm = skolemPrefix ++ s)
    (hallowed : isAllowedName n = true) : nm ≠ n := by
  obtain ⟨t, ht⟩ := hnm
  intro heq
  have hpfx := not_skolemPrefix_of_isAllowedName hallowed
  rw [← heq, ht, String.toList_isPrefixOf_toList_append skolemPrefix t] at hpfx
  simp at hpfx

/-- No constant of a rigid-prefixed renaming is a name a user may declare. -/
theorem find?_rigid_isAllowedName_none {σ : RigidNames} (hpfx : RigidNamesPrefixed σ)
    {nm : String} (hallowed : isAllowedName nm = true) :
    σ.find? (fun p => p.2 == nm) = none := by
  rw [List.find?_eq_none]
  intro q hq
  simp only [beq_iff_eq]
  exact rigid_ne_of_isAllowedName (hpfx q hq) hallowed

/-- Inserting a rigid-prefixed renaming's constants into a known-types table does not make an
    allowed name known. -/
private theorem knownTypes_foldl_insert_rigid_notContains
    (σ : RigidNames) (x : String) :
    ∀ ks : Lambda.KnownTypes, (∀ q ∈ σ, q.2 ≠ x) →
      Lambda.KnownTypes.containsName ks x = false →
      Lambda.KnownTypes.containsName (σ.foldl (fun ks p => ks.insert p.2 0) ks) x = false := by
  induction σ with
  | nil => intro ks _ hx; exact hx
  | cons q rest ih =>
    intro ks hne hx
    refine ih _ (fun r hr => hne r (List.mem_cons_of_mem q hr)) ?_
    have hqx : q.2 ≠ x := hne q List.mem_cons_self
    simp only [KnownTypes.containsName] at hx ⊢
    simp [Std.HashMap.contains_insert, hx, hqx]

/-- Registering the constants of `σ` does not make known a name that is none of them. -/
theorem addSkolemTypes_notContains_of_ne
    (C : Expression.TyContext) (σ : RigidNames) (x : String) (hne : ∀ q ∈ σ, q.2 ≠ x)
    (hx : C.knownTypes.containsName x = false) :
    (addSkolemTypes C σ).knownTypes.containsName x = false := by
  simp only [addSkolemTypes]
  exact knownTypes_foldl_insert_rigid_notContains σ x C.knownTypes hne hx

/-- Registering rigid constants does not make an allowed name known. -/
private theorem addSkolemTypes_notContains_of_isAllowedName
    (C : Expression.TyContext) (σ : RigidNames) (hpfx : RigidNamesPrefixed σ) (x : String)
    (hallowed : isAllowedName x = true)
    (hx : C.knownTypes.containsName x = false) :
    (addSkolemTypes C σ).knownTypes.containsName x = false := by
  exact addSkolemTypes_notContains_of_ne C σ x
    (fun q hq => rigid_ne_of_isAllowedName (hpfx q hq) hallowed) hx

/-! ### `deskolemizeTy` on lists -/

/-- `deskolemizeTys` is the pointwise map of `deskolemizeTy`. -/
private theorem deskolemizeTys_eq_map (σ : RigidNames) (args : LMonoTys) :
    deskolemizeTys σ args = args.map (deskolemizeTy σ) := by
  induction args with
  | nil => rfl
  | cons a rest ih => unfold deskolemizeTys; rw [ih]; rfl

/-! ### Equations and free variables of `skolemizeTy` and `deskolemizeTy` -/

/-- `skolemizeTy` fixes bitvector types. -/
private theorem skolemizeTy_bitvec (σ : RigidNames) (n : Nat) :
    skolemizeTy σ (.bitvec n) = .bitvec n := by
  exact LMonoTy.subst_bitvec _ n

/-- `skolemizeTy` is the structural map over `tcons` arguments. -/
private theorem skolemizeTy_tcons (σ : RigidNames) (nm : String) (args : LMonoTys) :
    skolemizeTy σ (.tcons nm args) = .tcons nm (args.map (skolemizeTy σ)) := by
  exact LMonoTy.subst_tcons_map _ nm args

/-- Skolemizing `int` gives `int`. -/
theorem skolemizeTy_int (σ : RigidNames) : skolemizeTy σ LMonoTy.int = LMonoTy.int := by
  rw [LMonoTy.int, skolemizeTy_tcons, List.map_nil]

/-- Skolemizing with no rigid names changes nothing. -/
private theorem skolemizeTy_nil (mty : LMonoTy) : skolemizeTy [] mty = mty := by
  induction mty with
  | ftvar x => rw [skolemizeTy_ftvar, List.find?_nil]
  | bitvec n => exact skolemizeTy_bitvec [] n
  | tcons name args ih =>
    rw [skolemizeTy_tcons, (List.map_congr_left fun t ht => ih t ht).trans (List.map_id args)]

/-! ### The skolemizer on each expression form -/

/-- Skolemizing a literal changes nothing. -/
private theorem skolemizeBody_const (nm : Option String) (σ : RigidNames) (m : ExpressionMetadata)
    (c : LConst) : skolemizeBody nm σ (.const m c) = .const m c := by
  simp only [skolemizeBody, LExpr.replaceUserProvidedType]

/-- Skolemizing a bound variable changes nothing. -/
private theorem skolemizeBody_bvar (nm : Option String) (σ : RigidNames) (m : ExpressionMetadata)
    (b : Nat) : skolemizeBody nm σ (.bvar m b) = .bvar m b := by
  simp only [skolemizeBody, LExpr.replaceUserProvidedType]

/-- Skolemizing an operator skolemizes its annotation only when the operator is `nm`. -/
private theorem skolemizeBody_op (nm : Option String) (σ : RigidNames) (m : ExpressionMetadata)
    (o : CoreIdent) (uty : Option LMonoTy) :
    skolemizeBody nm σ (.op m o uty) =
      if nm == some o.name then .op m o (uty.map (skolemizeTy σ)) else .op m o uty := by
  simp only [skolemizeBody, LExpr.replaceUserProvidedType]
  split <;> rfl

/-- Skolemizing a free variable skolemizes its annotation. -/
theorem skolemizeBody_fvar (nm : Option String) (σ : RigidNames) (m : ExpressionMetadata)
    (x : CoreIdent) (uty : Option LMonoTy) :
    skolemizeBody nm σ (.fvar m x uty) = .fvar m x (uty.map (skolemizeTy σ)) := by
  simp only [skolemizeBody, LExpr.replaceUserProvidedType]

/-- Skolemizing an abstraction skolemizes its annotation and body. -/
private theorem skolemizeBody_abs (nm : Option String) (σ : RigidNames) (m : ExpressionMetadata)
    (n : String) (uty : Option LMonoTy) (b : Core.Expression.Expr) :
    skolemizeBody nm σ (.abs m n uty b) =
      .abs m n (uty.map (skolemizeTy σ)) (skolemizeBody nm σ b) := by
  simp only [skolemizeBody, LExpr.replaceUserProvidedType]

/-- Skolemizing a quantifier skolemizes its annotation, trigger and body. -/
private theorem skolemizeBody_quant (nm : Option String) (σ : RigidNames)
    (m : ExpressionMetadata) (qk : QuantifierKind) (n : String) (aty : Option LMonoTy)
    (tr b : Core.Expression.Expr) :
    skolemizeBody nm σ (.quant m qk n aty tr b) =
      .quant m qk n (aty.map (skolemizeTy σ)) (skolemizeBody nm σ tr) (skolemizeBody nm σ b) := by
  simp only [skolemizeBody, LExpr.replaceUserProvidedType]

/-- Skolemizing an application skolemizes both parts. -/
private theorem skolemizeBody_app (nm : Option String) (σ : RigidNames) (m : ExpressionMetadata)
    (e1 e2 : Core.Expression.Expr) :
    skolemizeBody nm σ (.app m e1 e2) = .app m (skolemizeBody nm σ e1) (skolemizeBody nm σ e2) := by
  simp only [skolemizeBody, LExpr.replaceUserProvidedType]

/-- Skolemizing a conditional skolemizes its three parts. -/
private theorem skolemizeBody_ite (nm : Option String) (σ : RigidNames) (m : ExpressionMetadata)
    (c t f : Core.Expression.Expr) :
    skolemizeBody nm σ (.ite m c t f) =
      .ite m (skolemizeBody nm σ c) (skolemizeBody nm σ t) (skolemizeBody nm σ f) := by
  simp only [skolemizeBody, LExpr.replaceUserProvidedType]

/-- Skolemizing an equality skolemizes both sides. -/
private theorem skolemizeBody_eq (nm : Option String) (σ : RigidNames) (m : ExpressionMetadata)
    (e1 e2 : Core.Expression.Expr) :
    skolemizeBody nm σ (.eq m e1 e2) = .eq m (skolemizeBody nm σ e1) (skolemizeBody nm σ e2) := by
  simp only [skolemizeBody, LExpr.replaceUserProvidedType]

/-- Skolemizing an expression with no rigid names changes nothing. -/
theorem skolemizeBody_nil (nm : Option String) (e : Core.Expression.Expr) :
    skolemizeBody nm [] e = e := by
  have hf : skolemizeTy [] = id := funext skolemizeTy_nil
  induction e <;> simp_all [skolemizeBody, LExpr.replaceUserProvidedType]

/-- `if σ.isEmpty then x else y` equals `y` when `x = y` holds whenever `σ` is empty. -/
theorem ite_isEmpty_eq_of_nil {α β : Type _} {σ : List β} {x y : α} (h : σ = [] → x = y) :
    (if σ.isEmpty then x else y) = y := by
  split
  · rename_i hσ
    exact h (List.isEmpty_iff.mp hσ)
  · rfl

/-- Skipping skolemization of an expression when `σ` is empty agrees with skolemizing it. -/
theorem skolemizeBody_unless_isEmpty (nm : Option String) (σ : RigidNames)
    (e : Core.Expression.Expr) :
    (if σ.isEmpty then e else skolemizeBody nm σ e) = skolemizeBody nm σ e := by
  refine ite_isEmpty_eq_of_nil fun hσ => ?_
  rw [hσ, skolemizeBody_nil]

/-! ### The skolemizer on each statement form -/

/-- Skolemizing a command statement skolemizes the command. -/
theorem skolemizeStmt_cmd (nm : Option String) (σ : RigidNames) (c : Command) :
    skolemizeStmt nm σ (.cmd c) = .cmd (skolemizeCmd nm σ c) := by
  simp only [skolemizeStmt, Stmt.mapExpr]

/-- Skolemizing a block skolemizes its body. -/
theorem skolemizeStmt_block (nm : Option String) (σ : RigidNames) (l : String)
    (bss : List Statement) (md : MetaData Expression) :
    skolemizeStmt nm σ (.block l bss md) = .block l (skolemizeStmts nm σ bss) md := by
  simp only [skolemizeStmt, skolemizeStmts, Stmt.mapExpr]

/-- Skolemizing a conditional skolemizes its condition and both branches. -/
theorem skolemizeStmt_ite (nm : Option String) (σ : RigidNames)
    (cond : ExprOrNondet Expression) (tss ess : List Statement) (md : MetaData Expression) :
    skolemizeStmt nm σ (.ite cond tss ess md) =
      .ite (cond.map (skolemizeBody nm σ ·)) (skolemizeStmts nm σ tss)
        (skolemizeStmts nm σ ess) md := by
  cases cond <;> simp only [skolemizeStmt, skolemizeStmts, Stmt.mapExpr, ExprOrNondet.map]

/-- Skolemizing a loop skolemizes its guard, measure, invariants and body. -/
theorem skolemizeStmt_loop (nm : Option String) (σ : RigidNames)
    (g : ExprOrNondet Expression) (m : Option Expression.Expr)
    (i : List (String × Expression.Expr)) (bss : List Statement) (md : MetaData Expression) :
    skolemizeStmt nm σ (.loop g m i bss md) =
      .loop (g.map (skolemizeBody nm σ ·)) (m.map (skolemizeBody nm σ ·))
        (i.map (fun (l, e) => (l, skolemizeBody nm σ e))) (skolemizeStmts nm σ bss) md := by
  cases g <;> simp only [skolemizeStmt, skolemizeStmts, Stmt.mapExpr, ExprOrNondet.map]

/-- Skolemizing an exit changes nothing. -/
theorem skolemizeStmt_exit (nm : Option String) (σ : RigidNames) (l : String)
    (md : MetaData Expression) : skolemizeStmt nm σ (.exit l md) = .exit l md := by
  simp only [skolemizeStmt, Stmt.mapExpr]

/-- Skolemizing a type declaration changes nothing. -/
theorem skolemizeStmt_typeDecl (nm : Option String) (σ : RigidNames)
    (t : TypeConstructor) (md : MetaData Expression) :
    skolemizeStmt nm σ (.typeDecl t md) = .typeDecl t md := by
  simp only [skolemizeStmt, Stmt.mapExpr]

/-- Skolemizing the empty statement list gives the empty list. -/
theorem skolemizeStmts_empty (nm : Option String) (σ : RigidNames) :
    skolemizeStmts nm σ [] = [] := by
  simp only [skolemizeStmts, Block.mapExpr]

/-- Skolemizing a statement list skolemizes its head and its tail. -/
theorem skolemizeStmts_cons (nm : Option String) (σ : RigidNames) (s : Statement)
    (rest : List Statement) :
    skolemizeStmts nm σ (s :: rest) = skolemizeStmt nm σ s :: skolemizeStmts nm σ rest := by
  simp only [skolemizeStmt, skolemizeStmts, Block.mapExpr]

/-- Skolemizing a command with no rigid names changes nothing. -/
theorem skolemizeCmd_nil (nm : Option String) (c : Command) : skolemizeCmd nm [] c = c :=
  mapCmdWith_id _ _ (skolemizeBody_nil nm) skolemizeTy_nil c

/-- Skolemizing a statement list with no rigid names changes nothing. -/
theorem skolemizeStmts_nil (nm : Option String) (ss : List Statement) :
    skolemizeStmts nm [] ss = ss :=
  Block.mapExpr_mapCmdWith_id _ _ (skolemizeBody_nil nm) skolemizeTy_nil ss

mutual
/-- A free variable of a skolemized type is a free variable of the type that `σ` does not
    rename. -/
theorem LMonoTy.mem_freeVars_skolemizeTy (σ : RigidNames) :
    ∀ (mty : LMonoTy) (v : TyIdentifier), v ∈ LMonoTy.freeVars (skolemizeTy σ mty) →
      v ∈ LMonoTy.freeVars mty ∧ v ∉ σ.map Prod.fst
  | .ftvar x, v, hv => by
    rw [skolemizeTy_ftvar] at hv
    cases hfind : σ.find? (fun p => p.1 == x) with
    | some p =>
      rw [hfind] at hv
      simp [LMonoTy.freeVars, LMonoTys.freeVars] at hv
    | none =>
      rw [hfind] at hv
      simp only [LMonoTy.freeVars, List.mem_singleton] at hv
      subst hv
      refine ⟨List.mem_singleton.mpr rfl, ?_⟩
      intro hmem
      obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hmem
      have hne := List.find?_eq_none.mp hfind p hp
      simp [hpx] at hne
  | .bitvec n, v, hv => by
    rw [skolemizeTy_bitvec] at hv
    simp [LMonoTy.freeVars] at hv
  | .tcons nm args, v, hv => by
    rw [skolemizeTy_tcons] at hv
    simp only [LMonoTy.freeVars] at hv ⊢
    exact LMonoTys.mem_freeVars_map_skolemizeTy σ args v hv

/-- A free variable of a list of skolemized types is a free variable of the list that `σ` does not
    rename. -/
private theorem LMonoTys.mem_freeVars_map_skolemizeTy (σ : RigidNames) :
    ∀ (mtys : LMonoTys) (v : TyIdentifier), v ∈ LMonoTys.freeVars (mtys.map (skolemizeTy σ)) →
      v ∈ LMonoTys.freeVars mtys ∧ v ∉ σ.map Prod.fst
  | [], v, hv => by simp [LMonoTys.freeVars] at hv
  | t :: rest, v, hv => by
    simp only [List.map_cons, LMonoTys.freeVars, List.mem_append] at hv ⊢
    rcases hv with hv | hv
    · obtain ⟨h1, h2⟩ := LMonoTy.mem_freeVars_skolemizeTy σ t v hv
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := LMonoTys.mem_freeVars_map_skolemizeTy σ rest v hv
      exact ⟨Or.inr h1, h2⟩
end

/-- Searching a renaming with distinct constants for an entry's constant finds that entry. -/
private theorem find?_rigid_eq_self {σ : RigidNames} (hnd : (σ.map Prod.snd).Nodup)
    {p : String × String} (hp : p ∈ σ) : σ.find? (fun q => q.2 == p.2) = some p := by
  induction σ with
  | nil => exact absurd hp (by simp)
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hp with heq | hp'
    · subst heq; rw [List.find?_cons_of_pos (by simp)]
    · have hne : hd.2 ≠ p.2 := fun hc => hnd.1 ⟨p, hp', hc.symm⟩
      rw [List.find?_cons_of_neg (by simp [hne])]
      exact ih (by simpa using hnd.2) hp'

/-- `deskolemizeTy` fixes type variables. -/
theorem deskolemizeTy_ftvar (σ : RigidNames) (x : String) :
    deskolemizeTy σ (.ftvar x) = .ftvar x := by
  unfold deskolemizeTy
  rfl

/-- `deskolemizeTy` fixes a bit-vector type. -/
theorem deskolemizeTy_bitvec (σ : RigidNames) (n : Nat) :
    deskolemizeTy σ (.bitvec n) = .bitvec n := by
  unfold deskolemizeTy
  rfl

/-- `deskolemizeTy` on a `tcons`: a rigid head becomes the type parameter it stands for
    (discarding the arguments), otherwise it maps over the arguments. -/
theorem deskolemizeTy_tcons (σ : RigidNames) (nm : String) (args : LMonoTys) :
    deskolemizeTy σ (.tcons nm args)
      = match σ.find? (fun p => p.2 == nm) with
        | some p => .ftvar p.1
        | none => .tcons nm (args.map (deskolemizeTy σ)) := by
  have h_unfold : deskolemizeTy σ (.tcons nm args)
      = match σ.find? (fun p => p.2 == nm) with
        | some p => LMonoTy.ftvar p.1
        | none => LMonoTy.tcons nm (deskolemizeTys σ args) := rfl
  rw [h_unfold]
  cases h_find : σ.find? (fun p => p.2 == nm) with
  | none => simp only [deskolemizeTys_eq_map]
  | some a => rfl

/-- Deskolemization maps over the arguments of a `tcons` whose head a user may declare. -/
private theorem deskolemizeTy_tcons_of_isAllowedName {σ : RigidNames} (hpfx : RigidNamesPrefixed σ)
    (nm : String) (hallowed : isAllowedName nm = true) (args : LMonoTys) :
    deskolemizeTy σ (.tcons nm args) = .tcons nm (args.map (deskolemizeTy σ)) := by
  rw [deskolemizeTy_tcons, find?_rigid_isAllowedName_none hpfx hallowed]

/-- A free variable of a deskolemized type is one of the original type or a renamed parameter. -/
theorem freeVars_deskolemizeTy_subset (σ : RigidNames) :
    ∀ (mty : LMonoTy) (v : String),
      v ∈ LMonoTy.freeVars (deskolemizeTy σ mty) →
        v ∈ LMonoTy.freeVars mty ∨ v ∈ σ.map Prod.fst := by
  intro mty
  induction mty with
  | ftvar x =>
    intro v hv
    simp only [deskolemizeTy_ftvar, LMonoTy.freeVars, List.mem_singleton] at hv ⊢
    exact Or.inl hv
  | bitvec n =>
    intro v hv
    simp only [deskolemizeTy, LMonoTy.freeVars, List.not_mem_nil] at hv
  | tcons name args ih =>
    intro v hv
    rw [deskolemizeTy_tcons] at hv
    cases hfind : σ.find? (fun p => p.2 == name) with
    | some p =>
      simp only [hfind, LMonoTy.freeVars, List.mem_singleton] at hv
      subst v
      exact Or.inr
        (List.mem_map.mpr ⟨p, List.mem_of_find?_eq_some hfind, rfl⟩)
    | none =>
      have hv' : v ∈ LMonoTys.freeVars (args.map (deskolemizeTy σ)) := by
        simpa only [hfind, LMonoTy.freeVars] using hv
      simp only [LMonoTy.freeVars]
      obtain ⟨mty, hmty, hv⟩ := LMonoTys.freeVars_exists hv'
      obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hmty
      rcases ih source hsource v hv with hv | hv
      · exact Or.inl (LMonoTys.freeVars_mem_subset hsource hv)
      · exact Or.inr hv

/-- Deskolemizing keeps every type variable admissible under `adm` when the original type's
    variables and the renamed parameters are. -/
theorem freeVars_deskolemizeTy_admissible (σ : RigidNames) {adm : TyVarAdmissibility}
    {mty : LMonoTy} (h : ∀ v ∈ LMonoTy.freeVars mty, adm v = true)
    (h_rig : ∀ p ∈ σ, adm p.1 = true) :
    ∀ v ∈ LMonoTy.freeVars (deskolemizeTy σ mty), adm v = true := by
  intro v hv
  rcases freeVars_deskolemizeTy_subset σ mty v hv with hv | hv
  · exact h v hv
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
    exact h_rig p hp

/-- Deskolemizing by a renaming with distinct constants absorbs skolemization by a sublist. -/
private theorem deskolemizeTy_skolemizeTy_eq_deskolemizeTy_of_sublist
    {inner outer : RigidNames} (hsub : inner.Sublist outer)
    (hnd : (outer.map Prod.snd).Nodup) (t : LMonoTy) :
    deskolemizeTy outer (skolemizeTy inner t) = deskolemizeTy outer t := by
  induction t with
  | ftvar x =>
    rw [skolemizeTy_ftvar]
    cases hfind : inner.find? (fun q => q.1 == x) with
    | none => rfl
    | some p =>
      have hpInner : p ∈ inner := List.mem_of_find?_eq_some hfind
      have hpOuter : p ∈ outer := hsub.subset hpInner
      have hx : p.1 = x := by simpa using List.find?_some hfind
      rw [deskolemizeTy_tcons, find?_rigid_eq_self hnd hpOuter]
      simp only [hx, deskolemizeTy_ftvar]
  | bitvec n => rw [skolemizeTy_bitvec]
  | tcons nm args ih =>
    rw [skolemizeTy_tcons, deskolemizeTy_tcons, deskolemizeTy_tcons]
    cases hfind : outer.find? (fun p => p.2 == nm) with
    | some p => rfl
    | none =>
      simp only [List.map_map]
      exact congrArg (LMonoTy.tcons nm) (List.map_congr_left (fun t ht => ih t ht))

/-- `deskolemizeTy σ` absorbs `skolemizeTy σ` when no two parameters share a constant. -/
theorem deskolemizeTy_skolemizeTy_eq_deskolemizeTy {σ : RigidNames}
    (hnd : (σ.map Prod.snd).Nodup) (t : LMonoTy) :
    deskolemizeTy σ (skolemizeTy σ t) = deskolemizeTy σ t :=
  deskolemizeTy_skolemizeTy_eq_deskolemizeTy_of_sublist (List.Sublist.refl σ) hnd t

/-! ### Sweeping the type-constructor names of a monotype -/

/-- A list-level name sweep holds as soon as it holds of every member. -/
private theorem mtysAllTyConsNames_of_pointwise (p : String → Bool) (mtys : LMonoTys)
    (h : ∀ t ∈ mtys, mtyAllTyConsNames p t = true) :
    mtysAllTyConsNames p mtys = true :=
  List.all_eq_true.mpr h

/-- A list-level name sweep gives the sweep for each member. -/
private theorem mtyAllTyConsNames_of_mem (p : String → Bool) (mtys : LMonoTys)
    (h : mtysAllTyConsNames p mtys = true) :
    ∀ t ∈ mtys, mtyAllTyConsNames p t = true :=
  List.all_eq_true.mp h

/-- A name predicate true of every string sweeps every monotype. -/
private theorem mtyAllTyConsNames_of_forall (p : String → Bool) (mty : LMonoTy)
    (h : ∀ nm, p nm = true) :
    mtyAllTyConsNames p mty = true := by
  induction mty with
  | ftvar x => exact mtyAllTyConsNames_ftvar p x
  | bitvec n => exact mtyAllTyConsNames_bitvec p n
  | tcons nm args ih =>
    simp only [mtyAllTyConsNames_tcons, Bool.and_eq_true]
    exact ⟨h nm, mtysAllTyConsNames_of_pointwise p args ih⟩

/-- A name sweep may be weakened pointwise on names. -/
private theorem mtyAllTyConsNames_mono {p q : String → Bool} (hpq : ∀ nm, p nm = true → q nm = true)
    (mty : LMonoTy) (h : mtyAllTyConsNames p mty = true) :
    mtyAllTyConsNames q mty = true := by
  induction mty with
  | ftvar x => exact mtyAllTyConsNames_ftvar q x
  | bitvec n => exact mtyAllTyConsNames_bitvec q n
  | tcons nm args ih =>
    simp only [mtyAllTyConsNames_tcons, Bool.and_eq_true] at h ⊢
    refine ⟨hpq nm h.1, mtysAllTyConsNames_of_pointwise q args ?_⟩
    intro t ht
    exact ih t ht (mtyAllTyConsNames_of_mem p args h.2 t ht)

/-! ### Type-constructor references of deskolemized types, and arities of rigid constants -/

/-- Substituting type variables for type variables keeps the type-constructor names of a type. -/
private theorem getTypeRefs_subst_of_ftvar {S : Subst}
    (hS : ∀ x : TyIdentifier, ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y) (t : LMonoTy) :
    getTypeRefs (LMonoTy.subst S t) = getTypeRefs t := by
  induction t with
  | ftvar x =>
    obtain ⟨y, hy⟩ := hS x
    rw [hy]
    simp only [getTypeRefs]
  | bitvec n => rw [LMonoTy.subst_bitvec]
  | tcons n args ih =>
    rw [LMonoTy.subst_tcons_map]
    simp only [getTypeRefs, List.flatMap_map, List.cons.injEq, true_and]
    have hcongr : ∀ l : List LMonoTy, (∀ a ∈ l, getTypeRefs (LMonoTy.subst S a) = getTypeRefs a) →
        l.flatMap (fun a => getTypeRefs (LMonoTy.subst S a)) = l.flatMap getTypeRefs := by
      intro l hl
      induction l with
      | nil => rfl
      | cons a rest ihl =>
        simp only [List.flatMap_cons, hl a List.mem_cons_self,
          ihl fun b hb => hl b (List.mem_cons_of_mem _ hb)]
    exact hcongr args ih

/-- Substituting type variables for type variables keeps the type-constructor names of a list of
    types. -/
theorem flatMap_getTypeRefs_subst_of_ftvar {S : Subst}
    (hS : ∀ x : TyIdentifier, ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y) (tys : LMonoTys) :
    (tys.map (LMonoTy.subst S)).flatMap getTypeRefs = tys.flatMap getTypeRefs := by
  rw [List.flatMap_map]
  congr 1
  funext t
  exact getTypeRefs_subst_of_ftvar hS t

/-- Applying `f` to the annotations of an expression keeps the type names of its literals. -/
theorem exprLitTyNames_mapExprTys (f : LMonoTy → LMonoTy) (e : Expression.Expr) :
    exprLitTyNames (mapExprTys f e) = exprLitTyNames e := by
  unfold exprLitTyNames
  rw [getConsts_mapExprTys]

/-- Renaming type parameters keeps the type names of a procedure's literals. -/
private theorem procLitTyNames_renameTypeArgs (proc : Procedure) (ren : List (String × String)) :
    procLitTyNames (proc.renameTypeArgs ren) = procLitTyNames proc := by
  have hfe : ∀ e, exprLitTyNames (mapExprTys (LMonoTy.subst (Subst.ofRenaming ren)) e) =
      (exprLitTyNames e).map id := by
    intro e
    rw [exprLitTyNames_mapExprTys, List.map_id]
  have hcollect := procCollect_renameTypeArgs exprLitTyNames (fun _ => ([] : List String)) id
    ren hfe (fun _ => rfl) proc
  rw [List.map_id] at hcollect
  exact hcollect

/-- A procedure's written types are its parameter types and the annotations that `procCollect`
    lists from its conditions and body. -/
private theorem procAnnotTys_eq (proc : Procedure) :
    procAnnotTys proc = proc.header.inputs.values ++ proc.header.outputs.values ++
      procCollect exprAnnotTys ([·]) proc := by
  simp only [procAnnotTys, procCollect, List.append_assoc]
  rfl

/-- Renaming type parameters keeps the type names a procedure mentions. -/
private theorem procTyNames_renameTypeArgs (proc : Procedure) (ren : List (String × String)) :
    procTyNames (proc.renameTypeArgs ren) (procAnnotTys (proc.renameTypeArgs ren)) =
      procTyNames proc (procAnnotTys proc) := by
  have hannot : procAnnotTys (proc.renameTypeArgs ren) =
      (procAnnotTys proc).map (LMonoTy.subst (Subst.ofRenaming ren)) := by
    have hcollect := procCollect_renameTypeArgs exprAnnotTys ([·])
      (LMonoTy.subst (Subst.ofRenaming ren)) ren
      (exprAnnotTys_mapExprTys (LMonoTy.subst (Subst.ofRenaming ren))) (fun _ => rfl) proc
    rw [procAnnotTys_eq, procAnnotTys_eq, hcollect]
    unfold Procedure.renameTypeArgs Procedure.mapTys
    simp only [ListMap.values_map_snd, List.map_append]
  unfold procTyNames
  rw [hannot, flatMap_getTypeRefs_subst_of_ftvar (Subst.ofRenaming_ftvar ren),
    procLitTyNames_renameTypeArgs]
  congr 1
  unfold Procedure.renameTypeArgs Procedure.mapTys
  cases proc.body <;> simp only [mapStmtsTys_localTypeDecls]

/-- Renaming a procedure's reserved type parameters keeps the type names it mentions. -/
theorem procTyNames_renameReservedTypeArgs (avoid : Unit → List String) (proc : Procedure)
    (annot : Unit → List LMonoTy) :
    procTyNames (proc.renameReservedTypeArgs avoid annot)
        (procAnnotTys (proc.renameReservedTypeArgs avoid annot)) =
      procTyNames proc (procAnnotTys proc) := by
  rw [Procedure.renameReservedTypeArgs_eq]
  exact procTyNames_renameTypeArgs proc _

/-- Renaming a lemma's reserved type parameters keeps the type names its proposition
    mentions. -/
theorem Lemma.exprTyNames_renameReservedTypeArgs (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (l : Lemma) (annot : Unit → List LMonoTy) :
    exprTyNames (l.renameReservedTypeArgs C Env annot).e = exprTyNames l.e := by
  rw [Lemma.renameReservedTypeArgs_eq]
  unfold Lemma.renameTypeArgs exprTyNames
  rw [exprAnnotTys_mapExprTys, flatMap_getTypeRefs_subst_of_ftvar (Subst.ofRenaming_ftvar _),
    exprLitTyNames_mapExprTys]

/-- Registering a renaming's constants keeps the arity of every name the renaming does not use. -/
private theorem knownTypes_foldl_insert_getElem? (σ : RigidNames) :
    ∀ (x : String), σ.find? (fun p => p.2 == x) = none →
      ∀ ks : Lambda.KnownTypes, (σ.foldl (fun ks p => ks.insert p.2 0) ks)[x]? = ks[x]? := by
  induction σ with
  | nil => intro _ _ _; rfl
  | cons q rest ih =>
    intro x hx ks
    rw [List.find?_cons] at hx
    elim_err hx with hq
    have hqx : q.2 ≠ x := by simpa using hq
    rw [List.foldl_cons, ih x hx, Std.HashMap.getElem?_insert,
      ite_eq_right (by simpa using hqx)]

/-- `addSkolemTypes` keeps the arity of every name the renaming does not use. -/
theorem addSkolemTypes_getElem?_of_find?_none (C : LContext CoreLParams) (σ : RigidNames)
    (x : String) (hx : σ.find? (fun p => p.2 == x) = none) :
    (addSkolemTypes C σ).knownTypes[x]? = C.knownTypes[x]? :=
  knownTypes_foldl_insert_getElem? σ x hx C.knownTypes

/-- Searching a renaming for a name it does not use as a constant finds nothing. -/
private theorem find?_eq_none_of_not_mem_map_snd {σ : RigidNames} {x : String}
    (hx : x ∉ σ.map Prod.snd) : σ.find? (fun p => p.2 == x) = none := by
  rw [List.find?_eq_none]
  intro p hp hbeq
  rw [beq_iff_eq] at hbeq
  exact hx (List.mem_map.mpr ⟨p, hp, hbeq⟩)

/-- Registering a renaming's constants gives each of them arity `0`. -/
private theorem knownTypes_foldl_insert_getElem?_of_mem (σ : RigidNames) :
    ∀ (x : String), x ∈ σ.map Prod.snd →
      ∀ ks : Lambda.KnownTypes, (σ.foldl (fun ks p => ks.insert p.2 0) ks)[x]? = some 0 := by
  induction σ with
  | nil => intro x hx; exact absurd hx (by simp)
  | cons q rest ih =>
    intro x hx ks
    rw [List.foldl_cons]
    by_cases hrest : x ∈ rest.map Prod.snd
    · exact ih x hrest _
    · have hnone := find?_eq_none_of_not_mem_map_snd hrest
      have hqx : q.2 = x := by
        simp only [List.map_cons, List.mem_cons] at hx
        rcases hx with hx | hx
        · exact hx.symm
        · exact absurd hx hrest
      rw [knownTypes_foldl_insert_getElem? rest x hnone, hqx]
      simp

/-- After `addSkolemTypes`, a renaming's constant has arity `0` and any other name keeps its
    arity. -/
theorem addSkolemTypes_getElem? (C : LContext CoreLParams) (σ : RigidNames) (x : String) :
    (addSkolemTypes C σ).knownTypes[x]? =
      if x ∈ σ.map Prod.snd then some 0 else C.knownTypes[x]? := by
  by_cases hx : x ∈ σ.map Prod.snd
  · rw [ite_eq_left hx]
    exact knownTypes_foldl_insert_getElem?_of_mem σ x hx C.knownTypes
  · rw [ite_eq_right hx]
    exact addSkolemTypes_getElem?_of_find?_none C σ x (find?_eq_none_of_not_mem_map_snd hx)

/-- Registering one renaming's constants keeps two agreeing known-type tables in agreement. -/
theorem addSkolemTypes_getElem?_congr (C D : LContext CoreLParams) (σ : RigidNames)
    (h : ∀ x : String, C.knownTypes[x]? = D.knownTypes[x]?) (x : String) :
    (addSkolemTypes C σ).knownTypes[x]? = (addSkolemTypes D σ).knownTypes[x]? := by
  rw [addSkolemTypes_getElem?, addSkolemTypes_getElem?, h]

mutual
/-- Every type-constructor reference of a deskolemized type is one the original makes at the
    same arity, under a name the renaming does not use. -/
theorem mem_getTypeConsArities_deskolemizeTy (σ : RigidNames) (mty : LMonoTy)
    (ref : String) (n : Nat)
    (hmem : (ref, n) ∈ getTypeConsArities (deskolemizeTy σ mty)) :
    (ref, n) ∈ getTypeConsArities mty ∧ σ.find? (fun p => p.2 == ref) = none := by
  match mty with
  | .ftvar _ => simp [deskolemizeTy, getTypeConsArities] at hmem
  | .bitvec _ => simp [deskolemizeTy, getTypeConsArities] at hmem
  | .tcons nm args =>
    rw [deskolemizeTy] at hmem
    split at hmem
    · simp [getTypeConsArities] at hmem
    · rename_i hfind
      rw [deskolemizeTys_eq_map] at hmem
      simp only [getTypeConsArities, List.mem_cons, List.length_map] at hmem
      rcases hmem with heq | hflat
      · have hr : ref = nm := congrArg Prod.fst heq
        have hn : n = args.length := congrArg Prod.snd heq
        subst hr
        subst hn
        refine ⟨?_, hfind⟩
        rw [getTypeConsArities]
        exact List.mem_cons_self
      · rw [List.flatMap_map] at hflat
        obtain ⟨harg, hnot⟩ := mem_getTypeConsArities_deskolemizeTys σ args ref n hflat
        refine ⟨?_, hnot⟩
        rw [getTypeConsArities]
        exact List.mem_cons_of_mem _ harg

/-- Every type-constructor reference made by a list of deskolemized types is one the original
    list makes at the same arity, under a name the renaming does not use. -/
private theorem mem_getTypeConsArities_deskolemizeTys (σ : RigidNames) (mtys : LMonoTys)
    (ref : String) (n : Nat)
    (hmem : (ref, n) ∈ mtys.flatMap (fun t => getTypeConsArities (deskolemizeTy σ t))) :
    (ref, n) ∈ mtys.flatMap getTypeConsArities ∧ σ.find? (fun p => p.2 == ref) = none := by
  match mtys with
  | [] => simp at hmem
  | t :: rest =>
    simp only [List.flatMap_cons, List.mem_append] at hmem
    rcases hmem with hhd | htl
    · obtain ⟨ht, hnot⟩ := mem_getTypeConsArities_deskolemizeTy σ t ref n hhd
      refine ⟨?_, hnot⟩
      simp only [List.flatMap_cons, List.mem_append]
      exact Or.inl ht
    · obtain ⟨ht, hnot⟩ := mem_getTypeConsArities_deskolemizeTys σ rest ref n htl
      refine ⟨?_, hnot⟩
      simp only [List.flatMap_cons, List.mem_append]
      exact Or.inr ht
end

/-! ### Types that name no rigid constant -/

/-- A name that differs from every constant of `σ` is not a rigid constant of `σ`. -/
theorem notRigidConst_of_ne {σ : RigidNames} {nm : String} (h : ∀ p ∈ σ, p.2 ≠ nm) :
    notRigidConst σ nm = true :=
  List.all_eq_true.mpr fun p hp => bne_iff_ne.mpr (h p hp)

/-- A type none of whose type-constructor names is a constant of `σ` names no rigid constant
    of `σ`. -/
theorem mtyAllTyConsNames_notRigidConst_of_not_mem {σ : RigidNames} {ty : LMonoTy}
    (h : ∀ p ∈ σ, p.2 ∉ getTypeRefs ty) : mtyAllTyConsNames (notRigidConst σ) ty = true :=
  List.all_eq_true.mpr fun _ hn => notRigidConst_of_ne fun p hp heq => h p hp (heq ▸ hn)

/-- Deskolemization fixes a type naming no constant of `σ`. -/
theorem deskolemizeTy_eq_self_of_notRigidConst {σ : RigidNames} (mty : LMonoTy)
    (h : mtyAllTyConsNames (notRigidConst σ) mty = true) :
    deskolemizeTy σ mty = mty := by
  induction mty with
  | ftvar f => rfl
  | bitvec n => rfl
  | tcons name args ih =>
    simp only [mtyAllTyConsNames_tcons, Bool.and_eq_true] at h
    obtain ⟨hname, hargs⟩ := h
    have hfind : List.find? (fun p => p.2 == name) σ = none := by
      rw [List.find?_eq_none]
      intro q hq
      have hne := List.all_eq_true.mp hname q hq
      simpa only [bne_iff_ne, ne_eq, beq_iff_eq] using hne
    have hmap : args.map (deskolemizeTy σ) = args := by
      refine (List.map_congr_left fun t ht => ?_).trans (List.map_id args)
      exact ih t ht (mtyAllTyConsNames_of_mem _ args hargs t ht)
    rw [deskolemizeTy_tcons, hfind, hmap]

/-- Deskolemizing with no rigid names changes nothing. -/
theorem deskolemizeTy_nil (mty : LMonoTy) : deskolemizeTy [] mty = mty := by
  induction mty with
  | ftvar f => rfl
  | bitvec n => rfl
  | tcons name args ih =>
    have hmap : args.map (deskolemizeTy []) = args :=
      (List.map_congr_left fun t ht => ih t ht).trans (List.map_id args)
    rw [deskolemizeTy_tcons, List.find?_nil, hmap]

/-- Skipping deskolemization when `σ` renames nothing agrees with deskolemizing. -/
private theorem deskolemizeTyIf_eq (σ : RigidNames) : deskolemizeTyIf σ = deskolemizeTy σ := by
  funext ty
  unfold deskolemizeTyIf
  split
  · rename_i hσ
    rw [List.isEmpty_iff.mp hσ, deskolemizeTy_nil]
  · rfl

/-- `finishStored` returns `finishDeskolemized σ S eT` (the elaborated expression with `S`
    applied and deskolemized), together with whether every type annotation of that expression
    satisfies `ok`. -/
theorem finishStored_eq (σ : RigidNames) (S : Subst) (ok : LMonoTy → Bool)
    (eT : LExprT CoreLParams.mono) :
    finishStored σ S ok eT =
      (finishDeskolemized σ S eT, (exprAnnotTys (finishDeskolemized σ S eT)).all ok) := by
  induction eT with
  | const m c => rfl
  | op m o ty =>
    simp only [finishStored, deskolemizeTyIf_eq, finishDeskolemized, LExpr.applySubstT,
      LExpr.replaceMetadata, LExpr.unresolved, LExpr.replaceUserProvidedType, exprAnnotTys,
      Option.map_some, Option.toList_some, List.all_cons, List.all_nil, Bool.and_true]
  | bvar m b => rfl
  | fvar m x ty =>
    simp only [finishStored, deskolemizeTyIf_eq, finishDeskolemized, LExpr.applySubstT,
      LExpr.replaceMetadata, LExpr.unresolved, LExpr.replaceUserProvidedType, exprAnnotTys,
      Option.map_some, Option.toList_some, List.all_cons, List.all_nil, Bool.and_true]
  | app m e1 e2 ih1 ih2 =>
    simp only [finishStored, ih1, ih2]
    simp only [finishDeskolemized, LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved,
      LExpr.replaceUserProvidedType, exprAnnotTys, List.all_append]
  | abs m name t e ih =>
    simp only [finishStored, ih, finishDeskolemized, LExpr.applySubstT, LExpr.replaceMetadata,
      deskolemizeTyIf_eq]
    cases hA : (LMonoTy.subst S m.type).isArrow <;> cases t <;>
      simp [hA, LExpr.unresolved, LExpr.replaceUserProvidedType, exprAnnotTys]
  | quant m qk name ty tr e ihTr ihE =>
    simp only [finishStored, ihTr, ihE]
    simp only [finishDeskolemized, LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved,
      LExpr.replaceUserProvidedType, exprAnnotTys, List.all_append, deskolemizeTyIf_eq,
      Option.map_some, Option.toList_some, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_assoc]
  | ite m c t f ihC ihT ihF =>
    simp only [finishStored, ihC, ihT, ihF]
    simp only [finishDeskolemized, LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved,
      LExpr.replaceUserProvidedType, exprAnnotTys, List.all_append]
  | eq m e1 e2 ih1 ih2 =>
    simp only [finishStored, ih1, ih2]
    simp only [finishDeskolemized, LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved,
      LExpr.replaceUserProvidedType, exprAnnotTys, List.all_append]

/-- If every type annotation of `e` mentions only type variables of `ps`, then every
    annotation type variable of `e` is in `ps`. -/
theorem annotTyVars_mem_of_tyVarsIn {ps : List TyIdentifier} {e : Expression.Expr}
    (h : (exprAnnotTys e).all (tyVarsIn ps) = true) : ∀ v ∈ annotTyVars e, v ∈ ps := by
  intro v hv
  unfold annotTyVars at hv
  obtain ⟨t, ht, hvt⟩ := List.mem_flatMap.mp hv
  have hall := List.all_eq_true.mp h t ht
  unfold tyVarsIn at hall
  simpa only [List.contains_iff_mem] using List.all_eq_true.mp hall v hvt

/-- A sweep over an expression's annotations is monotone in its predicate. -/
theorem allExprTys_mono {p q : LMonoTy → Bool} (hpq : ∀ t, p t = true → q t = true) :
    ∀ e : Expression.Expr, allExprTys p e = true → allExprTys q e = true := by
  intro e h
  rw [allExprTys_eq_all_exprAnnotTys] at h ⊢
  exact List.all_eq_true.mpr (fun t ht => hpq t (List.all_eq_true.mp h t ht))

/-- Deskolemization undoes skolemization on a type scheme whose body names no constant of `σ`,
    when the constants of `σ` are distinct. -/
private theorem mapLTyTys_deskolemize_roundtrip (σ : RigidNames)
    (hnd : (σ.map Prod.snd).Nodup) (ty : LTy)
    (h : allLTyTys (mtyAllTyConsNames (notRigidConst σ)) ty = true) :
    mapLTyTys (deskolemizeTy σ) (mapLTyTys (skolemizeTy σ) ty) = ty := by
  cases ty with
  | forAll vs mty =>
    simp only [allLTyTys] at h
    simp only [mapLTyTys, deskolemizeTy_skolemizeTy_eq_deskolemizeTy hnd,
      deskolemizeTy_eq_self_of_notRigidConst mty h]

/-! ### Deskolemizing registered types -/

mutual
/-- Deskolemization fixes every instance of a registered type when no constant of the renaming
    is registered. -/
theorem deskolemizeTy_eq_self_of_knownInstance {T : LExprParams} {σ : RigidNames}
    (C : LContext T) (h_fresh : RigidNamesFresh C.knownTypes σ)
    (mty : LMonoTy) (h : LMonoTy.knownInstance mty C.knownTypes = true) :
    deskolemizeTy σ mty = mty := by
  match mty with
  | .ftvar x => rfl
  | .bitvec n => rfl
  | .tcons nm args =>
    obtain ⟨-, hmem, hargs⟩ := knownInstance_tcons_inv C.knownTypes nm args h
    have hfind : σ.find? (fun p => p.2 == nm) = none := by
      rw [List.find?_eq_none]
      intro q hq
      simp only [beq_iff_eq]
      intro heq
      exact h_fresh q hq (heq ▸ hmem)
    rw [deskolemizeTy_tcons, hfind]
    exact congrArg (LMonoTy.tcons nm)
      (deskolemizeTys_eq_self_of_knownInstances C h_fresh args hargs)

/-- Deskolemization fixes every list of instances of registered types when no constant of the
    renaming is registered. -/
private theorem deskolemizeTys_eq_self_of_knownInstances {T : LExprParams} {σ : RigidNames}
    (C : LContext T) (h_fresh : RigidNamesFresh C.knownTypes σ)
    (mtys : LMonoTys) (h : LMonoTys.knownInstances mtys C.knownTypes = true) :
    mtys.map (deskolemizeTy σ) = mtys := by
  match mtys with
  | [] => rfl
  | hd :: tl =>
    unfold Lambda.LMonoTys.knownInstances at h
    elim_err h with hhd
    rw [List.map_cons, deskolemizeTy_eq_self_of_knownInstance C h_fresh hd hhd,
      deskolemizeTys_eq_self_of_knownInstances C h_fresh tl h]
end

/-! ### Deskolemizing built-in types and annotation-consistent expressions -/

/-- `deskolemizeTy` fixes a nullary type constructor whose name a user may write. -/
private theorem deskolemizeTy_nullary {σ : RigidNames} (hpfx : RigidNamesPrefixed σ)
    (nm : String) (hallowed : isAllowedName nm = true) :
    deskolemizeTy σ (.tcons nm []) = .tcons nm [] := by
  rw [deskolemizeTy_tcons_of_isAllowedName hpfx nm hallowed []]
  rfl

/-- `deskolemizeTy` fixes `bool`. -/
theorem deskolemizeTy_bool {σ : RigidNames} (hpfx : RigidNamesPrefixed σ) :
    deskolemizeTy σ .bool = .bool :=
  deskolemizeTy_nullary hpfx "bool" (isAllowedName_eq_toList ▸ rfl)

/-- `deskolemizeTy` fixes `int`. -/
theorem deskolemizeTy_int {σ : RigidNames} (hpfx : RigidNamesPrefixed σ) :
    deskolemizeTy σ LMonoTy.int = LMonoTy.int :=
  deskolemizeTy_nullary hpfx "int" (isAllowedName_eq_toList ▸ rfl)

/-- `deskolemizeTy` distributes over `arrow`. -/
private theorem deskolemizeTy_arrow {σ : RigidNames} (hpfx : RigidNamesPrefixed σ) (a b : LMonoTy) :
    deskolemizeTy σ (.arrow a b)
      = .arrow (deskolemizeTy σ a) (deskolemizeTy σ b) := by
  rw [LMonoTy.arrow,
      deskolemizeTy_tcons_of_isAllowedName hpfx "arrow" (isAllowedName_eq_toList ▸ rfl) [a, b]]; rfl

/-- Deskolemization fixes an iterated arrow whose head and arguments it fixes. -/
private theorem deskolemizeTy_mkArrow {σ : RigidNames} (hpfx : RigidNamesPrefixed σ)
    (mty : LMonoTy) (mtys : LMonoTys)
    (h : deskolemizeTy σ mty = mty)
    (hs : ∀ t ∈ mtys, deskolemizeTy σ t = t) :
    deskolemizeTy σ (LMonoTy.mkArrow mty mtys) = LMonoTy.mkArrow mty mtys := by
  induction mtys generalizing mty with
  | nil => simpa only [LMonoTy.mkArrow] using h
  | cons hd tl ih =>
    have hhd : deskolemizeTy σ hd = hd := hs hd List.mem_cons_self
    have htl : ∀ t ∈ tl, deskolemizeTy σ t = t :=
      fun t ht => hs t (List.mem_cons_of_mem hd ht)
    have hrest : deskolemizeTy σ (LMonoTy.mkArrow hd tl) = LMonoTy.mkArrow hd tl :=
      ih hd hhd htl
    simp only [LMonoTy.mkArrow]
    rw [deskolemizeTy_arrow hpfx, h, hrest]

/-- The literals of `e` have unchanged types when no type name of a literal's type is a rigid
    constant of `σ`. -/
theorem ConstTysFixed_of_litTyNames {σ : RigidNames} (e : LExpr CoreLParams.mono)
    (h : ∀ p ∈ σ, p.2 ∉ exprLitTyNames e) : ConstTysFixed σ e := by
  intro c hc
  refine deskolemizeTy_eq_self_of_notRigidConst c.ty
    (mtyAllTyConsNames_notRigidConst_of_not_mem ?_)
  intro p hp hn
  exact h p hp (List.mem_flatMap.mpr ⟨c, hc, hn⟩)

/-- An expression with the same literals as one whose literal types deskolemization fixes has
    its literal types fixed too. -/
theorem ConstTysFixed_of_getConsts_eq {σ : RigidNames} {e e' : LExpr CoreLParams.mono}
    (h : LExpr.getConsts e' = LExpr.getConsts e) (hc : ConstTysFixed σ e) :
    ConstTysFixed σ e' := by
  intro c hmem
  rw [h] at hmem
  exact hc c hmem

/-- An expression with no literals has all its literal types fixed by deskolemization. -/
theorem ConstTysFixed_of_getConsts_nil {σ : RigidNames} {e : LExpr CoreLParams.mono}
    (h : LExpr.getConsts e = []) : ConstTysFixed σ e := by
  intro c hc
  rw [h] at hc
  exact absurd hc List.not_mem_nil

/-- Applying a type substitution to an expression keeps its literals. -/
theorem getConsts_applyTypeSubst (e : Expression.Expr) (S : Subst) :
    LExpr.getConsts (LExpr.applyTypeSubst e S) = LExpr.getConsts e := by
  rw [LExpr.applyTypeSubst_eq_replaceUserProvidedType]
  exact getConsts_mapExprTys _ e

/-- Replacing the input expressions of a call by expressions that have the same literal type
    names, position by position, keeps the literal type names of the call's input expressions. -/
theorem CallArg.getInputExprs_replaceInArgs_litTyNames :
    ∀ (args : List (CallArg Expression)) (L : List Expression.Expr),
      List.Rel₂ (fun l i => exprLitTyNames l = exprLitTyNames i) L (CallArg.getInputExprs args) →
      (CallArg.getInputExprs (CallArg.replaceInArgs args L)).flatMap exprLitTyNames =
        (CallArg.getInputExprs args).flatMap exprLitTyNames
  | [], L, _ => rfl
  | .inArg e :: rest, L, h => by
    have h' : List.Rel₂ (fun l i => exprLitTyNames l = exprLitTyNames i) L
        (e :: CallArg.getInputExprs rest) := by
      simpa only [CallArg.getInputExprs_cons_inArg] using h
    cases h' with
    | cons hl hrest =>
      have ih := CallArg.getInputExprs_replaceInArgs_litTyNames rest _ hrest
      simp only [CallArg.replaceInArgs, CallArg.replaceInArgs.go,
        CallArg.getInputExprs_cons_inArg, List.flatMap_cons, hl] at ih ⊢
      rw [ih]
  | .inoutArg id :: rest, L, h => by
    have h' : List.Rel₂ (fun l i => exprLitTyNames l = exprLitTyNames i) L
        (LExpr.fvar Core.coreLoc id none :: CallArg.getInputExprs rest) := by
      simpa only [CallArg.getInputExprs_cons_inoutArg] using h
    cases h' with
    | cons hl hrest =>
      have ih := CallArg.getInputExprs_replaceInArgs_litTyNames rest _ hrest
      simp only [CallArg.replaceInArgs, CallArg.replaceInArgs.go,
        CallArg.getInputExprs_cons_inoutArg, List.flatMap_cons] at ih ⊢
      rw [ih]
  | .outArg id :: rest, L, h => by
    have h' : List.Rel₂ (fun l i => exprLitTyNames l = exprLitTyNames i) L
        (CallArg.getInputExprs rest) := by
      simpa only [CallArg.getInputExprs_cons_outArg] using h
    have ih := CallArg.getInputExprs_replaceInArgs_litTyNames rest L h'
    simp only [CallArg.replaceInArgs, CallArg.replaceInArgs.go,
      CallArg.getInputExprs_cons_outArg] at ih ⊢
    exact ih

/-- The literals of every expression in `es` have unchanged types when no type name of a
    literal's type in `es` is a rigid constant of `σ`. -/
private theorem ConstTysFixed_of_flatMap {σ : RigidNames} (es : List (LExpr CoreLParams.mono))
    (h : ∀ p ∈ σ, p.2 ∉ es.flatMap exprLitTyNames) :
    ∀ e ∈ es, ConstTysFixed σ e := by
  intro e he
  refine ConstTysFixed_of_litTyNames e fun p hp hn => h p hp ?_
  exact List.mem_flatMap.mpr ⟨e, he, hn⟩

/-- The literal type names of a command statement are those of the expressions the command
    reads. -/
theorem stmtLitTyNames_cmd (c : Command) :
    stmtLitTyNames (.cmd c) = (Statement.cmdExprs c).flatMap exprLitTyNames := by
  rw [stmtLitTyNames, stmtCollect_cmd, cmdCollect_of_ft_nil]

/-- The literal type names of a block are those of its body. -/
theorem stmtLitTyNames_block (l : String) (bss : List Statement) (md : MetaData Expression) :
    stmtLitTyNames (.block l bss md) = stmtsLitTyNames bss :=
  stmtCollect_block _ _ l bss md

/-- The literal type names of a conditional are those of its guard and both branches. -/
theorem stmtLitTyNames_ite (cond : ExprOrNondet Expression) (tss ess : List Statement)
    (md : MetaData Expression) :
    stmtLitTyNames (.ite cond tss ess md) =
      cond.toList.flatMap exprLitTyNames ++ (stmtsLitTyNames tss ++ stmtsLitTyNames ess) :=
  stmtCollect_ite _ _ cond tss ess md

/-- The literal type names of a loop are those of its guard, measure, invariants and body. -/
theorem stmtLitTyNames_loop (g : ExprOrNondet Expression) (m : Option Expression.Expr)
    (i : List (String × Expression.Expr)) (body : List Statement) (md : MetaData Expression) :
    stmtLitTyNames (.loop g m i body md) =
      (Statement.loopExprs g m i).flatMap exprLitTyNames ++ stmtsLitTyNames body :=
  stmtCollect_loop _ _ g m i body md

/-- The literal type names of a statement list are those of its first statement and the rest. -/
theorem stmtsLitTyNames_cons (s : Statement) (ss : List Statement) :
    stmtsLitTyNames (s :: ss) = stmtLitTyNames s ++ stmtsLitTyNames ss :=
  stmtsCollect_cons _ _ s ss

/-- The literals of a command statement have types fixed by deskolemization when no literal type
    name of the statement is a rigid constant. -/
theorem ConstTysFixed_of_stmtLitTyNames_cmd {σ : RigidNames} {c : Command}
    (h : ∀ p ∈ σ, p.2 ∉ stmtLitTyNames (.cmd c)) :
    ∀ e ∈ Statement.cmdExprs c, ConstTysFixed σ e := by
  refine ConstTysFixed_of_flatMap _ fun p hp hn => h p hp ?_
  rw [stmtLitTyNames_cmd]
  exact hn

/-- Skolemizing the annotations of an expression keeps its literals. -/
private theorem getConsts_skolemizeBody (nm : Option String) (σ : RigidNames)
    (e : Expression.Expr) :
    LExpr.getConsts (skolemizeBody nm σ e) = LExpr.getConsts e := by
  induction e with
  | const m c => rfl
  | bvar m i => rfl
  | fvar m x ty => rfl
  | op m o ty =>
    simp only [skolemizeBody_op]
    split <;> rfl
  | abs m name ty body ih =>
    simp only [skolemizeBody_abs, LExpr.getConsts]
    exact ih
  | quant m qk name ty tr body ihtr ihbody =>
    simp only [skolemizeBody_quant, LExpr.getConsts]
    rw [ihtr, ihbody]
  | app m e1 e2 ih1 ih2 =>
    simp only [skolemizeBody_app, LExpr.getConsts]
    rw [ih1, ih2]
  | ite m c t f ihc iht ihf =>
    simp only [skolemizeBody_ite, LExpr.getConsts]
    rw [ihc, iht, ihf]
  | eq m e1 e2 ih1 ih2 =>
    simp only [skolemizeBody_eq, LExpr.getConsts]
    rw [ih1, ih2]

/-- Skolemizing the annotations of an expression keeps the type names of its literals. -/
private theorem exprLitTyNames_skolemizeBody (nm : Option String) (σ : RigidNames)
    (e : Expression.Expr) :
    exprLitTyNames (skolemizeBody nm σ e) = exprLitTyNames e := by
  unfold exprLitTyNames
  rw [getConsts_skolemizeBody]

/-- Skolemizing the annotations of a command keeps the type names of the literals of the
    expressions it reads. -/
private theorem cmdExprs_litTyNames_skolemizeCmd (nm : Option String) (σ : RigidNames)
    (c : Command) :
    (Statement.cmdExprs (skolemizeCmd nm σ c)).flatMap exprLitTyNames =
      (Statement.cmdExprs c).flatMap exprLitTyNames := by
  cases c with
  | cmd cc =>
    cases cc with
    | init x ty e md =>
      cases e <;> simp only [skolemizeCmd, mapCmdWith, Statement.cmdExprs, Cmd.readExprs,
        ExprOrNondet.map, ExprOrNondet.toList, List.flatMap_cons, List.flatMap_nil,
        exprLitTyNames_skolemizeBody]
    | set x e md =>
      cases e <;> simp only [skolemizeCmd, mapCmdWith, Statement.cmdExprs, Cmd.readExprs,
        ExprOrNondet.map, ExprOrNondet.toList, List.flatMap_cons, List.flatMap_nil,
        exprLitTyNames_skolemizeBody]
    | assert l b md | assume l b md | cover l b md =>
      simp only [skolemizeCmd, mapCmdWith, Statement.cmdExprs, Cmd.readExprs, List.flatMap_cons,
        List.flatMap_nil, exprLitTyNames_skolemizeBody]
  | call pname tyArgs args md =>
    simp only [skolemizeCmd, mapCmdWith, Statement.cmdExprs]
    induction args with
    | nil => rfl
    | cons a rest ih =>
      cases a <;> simp only [List.map_cons, CallArg.mapInput,
        CallArg.getInputExprs_cons_inArg, CallArg.getInputExprs_cons_inoutArg,
        CallArg.getInputExprs_cons_outArg, List.flatMap_cons,
        exprLitTyNames_skolemizeBody] at ih ⊢ <;>
        simp only [ih]

/-- The empty statement list has no literal type names. -/
theorem stmtsLitTyNames_nil : stmtsLitTyNames [] = [] :=
  stmtsCollect_nil _ _

/-- A map that keeps the literal type names of each expression keeps those of a loop's guard,
    measure and invariants. -/
theorem loopExprs_flatMap_litTyNames_map (f : Expression.Expr → Expression.Expr)
    (hf : ∀ e, exprLitTyNames (f e) = exprLitTyNames e) (g : ExprOrNondet Expression)
    (m : Option Expression.Expr) (i : List (String × Expression.Expr)) :
    (Statement.loopExprs (g.map f) (m.map f) (i.map (fun (l, e) => (l, f e)))).flatMap
        exprLitTyNames = (Statement.loopExprs g m i).flatMap exprLitTyNames := by
  have hg : (g.map f).toList.flatMap exprLitTyNames = g.toList.flatMap exprLitTyNames := by
    cases g <;> simp only [ExprOrNondet.map, ExprOrNondet.toList, List.flatMap_cons,
      List.flatMap_nil, hf]
  have hm : (m.map f).toList.flatMap exprLitTyNames = m.toList.flatMap exprLitTyNames := by
    cases m <;> simp only [Option.map, Option.toList, List.flatMap_cons, List.flatMap_nil, hf]
  have hi : ((i.map (fun (l, e) => (l, f e))).map (·.2)).flatMap exprLitTyNames =
      (i.map (·.2)).flatMap exprLitTyNames := by
    induction i with
    | nil => rfl
    | cons q rest ih => simp only [List.map_cons, List.flatMap_cons, hf, ih]
  simp only [Statement.loopExprs, List.flatMap_append, hg, hm, hi]

/-- Skolemizing the annotations of a statement list keeps the type names of its literals. -/
theorem stmtsLitTyNames_skolemizeStmts (nm : Option String) (σ : RigidNames)
    (ss : List Statement) :
    stmtsLitTyNames (skolemizeStmts nm σ ss) = stmtsLitTyNames ss := by
  have hf : ∀ e, exprLitTyNames (skolemizeBody nm σ e) = exprLitTyNames e :=
    exprLitTyNames_skolemizeBody nm σ
  have hguard : ∀ g : ExprOrNondet Expression,
      (g.map (skolemizeBody nm σ ·)).toList.flatMap exprLitTyNames =
        g.toList.flatMap exprLitTyNames := by
    intro g
    cases g <;> simp only [ExprOrNondet.map, ExprOrNondet.toList, List.flatMap_cons,
      List.flatMap_nil, hf]
  refine Block.mapExpr.induct
    (fun s => stmtLitTyNames (skolemizeStmt nm σ s) = stmtLitTyNames s)
    (fun ss => stmtsLitTyNames (skolemizeStmts nm σ ss) = stmtsLitTyNames ss)
    ?cmd ?block ?iteDet ?iteNondet ?loopDet ?loopNondet ?exit ?typeDecl ?nil ?cons ss
  case cmd =>
    intro c
    simp only [skolemizeStmt_cmd, stmtLitTyNames_cmd]
    exact cmdExprs_litTyNames_skolemizeCmd nm σ c
  case block =>
    intro l bss md ih
    simp only [skolemizeStmt_block, stmtLitTyNames_block]
    exact ih
  case iteDet =>
    intro c tss ess md iht ihe
    simp only [skolemizeStmt_ite, stmtLitTyNames_ite, ExprOrNondet.map, ExprOrNondet.toList,
      List.flatMap_cons, List.flatMap_nil, hf, iht, ihe]
  case iteNondet =>
    intro tss ess md iht ihe
    simp only [skolemizeStmt_ite, stmtLitTyNames_ite, ExprOrNondet.map, ExprOrNondet.toList,
      List.flatMap_nil, iht, ihe]
  case loopDet =>
    intro g m i body md ih
    simp only [skolemizeStmt_loop, stmtLitTyNames_loop, ih]
    rw [loopExprs_flatMap_litTyNames_map _ hf]
  case loopNondet =>
    intro m i body md ih
    simp only [skolemizeStmt_loop, stmtLitTyNames_loop, ih]
    rw [loopExprs_flatMap_litTyNames_map _ hf]
  case exit =>
    intro l md
    simp only [skolemizeStmt_exit, stmtLitTyNames, stmtCollect, stmtOwnCollect, List.append_nil]
  case typeDecl =>
    intro tc md
    simp only [skolemizeStmt_typeDecl, stmtLitTyNames, stmtCollect, stmtOwnCollect,
      List.append_nil]
  case nil => rw [skolemizeStmts_empty]
  case cons =>
    intro s rest ihs ihr
    simp only [skolemizeStmts_cons, stmtsLitTyNames_cons, ihs, ihr]

/-- No literal type name of a block's body is a rigid constant when none of the block's is. -/
theorem stmtLitTyNames_block_body {σ : RigidNames} {l : String} {bss : List Statement}
    {md : MetaData Expression} (h : ∀ p ∈ σ, p.2 ∉ stmtLitTyNames (.block l bss md)) :
    ∀ p ∈ σ, p.2 ∉ stmtsLitTyNames bss := by
  intro p hp hn
  refine h p hp ?_
  rw [stmtLitTyNames_block]
  exact hn

/-- The guard's literals have types fixed by deskolemization, and no literal type name of either
    branch is a rigid constant, when no literal type name of the conditional is. -/
theorem stmtLitTyNames_ite_parts {σ : RigidNames} {cond : ExprOrNondet Expression}
    {tss ess : List Statement} {md : MetaData Expression}
    (h : ∀ p ∈ σ, p.2 ∉ stmtLitTyNames (.ite cond tss ess md)) :
    (∀ e ∈ cond.toList, ConstTysFixed σ e) ∧ (∀ p ∈ σ, p.2 ∉ stmtsLitTyNames tss) ∧
      (∀ p ∈ σ, p.2 ∉ stmtsLitTyNames ess) := by
  refine ⟨ConstTysFixed_of_flatMap _ fun p hp hn => h p hp ?_,
    fun p hp hn => h p hp ?_, fun p hp hn => h p hp ?_⟩
  · rw [stmtLitTyNames_ite]
    exact List.mem_append_left _ hn
  · rw [stmtLitTyNames_ite]
    exact List.mem_append_right _ (List.mem_append_left _ hn)
  · rw [stmtLitTyNames_ite]
    exact List.mem_append_right _ (List.mem_append_right _ hn)

/-- The literals of a loop's guard, measure and invariants have types fixed by deskolemization,
    and no literal type name of its body is a rigid constant, when no literal type name of the
    loop is. -/
theorem stmtLitTyNames_loop_parts {σ : RigidNames} {g : ExprOrNondet Expression}
    {m : Option Expression.Expr} {i : List (String × Expression.Expr)} {body : List Statement}
    {md : MetaData Expression}
    (h : ∀ p ∈ σ, p.2 ∉ stmtLitTyNames (.loop g m i body md)) :
    (∀ e ∈ Statement.loopExprs g m i, ConstTysFixed σ e) ∧
      (∀ p ∈ σ, p.2 ∉ stmtsLitTyNames body) := by
  refine ⟨ConstTysFixed_of_flatMap _ fun p hp hn => h p hp ?_, fun p hp hn => h p hp ?_⟩
  · rw [stmtLitTyNames_loop]
    exact List.mem_append_left _ hn
  · rw [stmtLitTyNames_loop]
    exact List.mem_append_right _ hn

/-- No literal type name of the first statement, or of the rest, of a statement list is a rigid
    constant when none of the list's is. -/
theorem stmtsLitTyNames_cons_parts {σ : RigidNames} {s : Statement} {ss : List Statement}
    (h : ∀ p ∈ σ, p.2 ∉ stmtsLitTyNames (s :: ss)) :
    (∀ p ∈ σ, p.2 ∉ stmtLitTyNames s) ∧ (∀ p ∈ σ, p.2 ∉ stmtsLitTyNames ss) := by
  refine ⟨fun p hp hn => h p hp ?_, fun p hp hn => h p hp ?_⟩
  · rw [stmtsLitTyNames_cons]
    exact List.mem_append_left _ hn
  · rw [stmtsLitTyNames_cons]
    exact List.mem_append_right _ hn

/-- Deskolemizing the user-written type annotations of an annotation-consistent expression
    keeps it annotation-consistent, with the binder context and result type deskolemized,
    when no literal's type names a rigid constant. -/
theorem HasTypeA_replaceUserProvidedType_deskolemizeTy {σ : RigidNames}
    (hpfx : RigidNamesPrefixed σ)
    (Δ : List LMonoTy) (e : LExpr CoreLParams.mono) (τ : LMonoTy)
    (hc : ConstTysFixed σ e)
    (h : LExpr.HasTypeA Δ e τ) :
    LExpr.HasTypeA (Δ.map (deskolemizeTy σ))
      (LExpr.replaceUserProvidedType e (deskolemizeTy σ)) (deskolemizeTy σ τ) :=
  LExpr.HasTypeA_replaceUserProvidedType_map (T := CoreLParams) (deskolemizeTy σ)
    (deskolemizeTy_arrow hpfx) (deskolemizeTy_bool hpfx) Δ e τ hc h

end Core

end -- public section
