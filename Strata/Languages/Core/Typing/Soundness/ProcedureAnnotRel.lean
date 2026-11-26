/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Soundness.Procedure
public import Strata.Languages.Core.Typing.Soundness.StatementInitTys
public import Strata.Languages.Core.Typing.Soundness.FunctionAnnotRel
import all Strata.Languages.Core.Typing.Soundness.Procedure
import all Strata.Languages.Core.Typing.Soundness.StatementInitTys
import all Strata.Languages.Core.Typing.Soundness.FunctionAnnotRel
import all Strata.Languages.Core.Typing.Soundness.Statement
import all Strata.Languages.Core.Typing.Soundness.Command
import all Strata.Languages.Core.Typing.Soundness.Function
import all Strata.Languages.Core.Typing.Props.TypeSkolemProps
import all Strata.Languages.Core.Typing.Props.ProcedureTypeProps
import all Strata.Languages.Core.Typing.Props.StatementEraseProps
import all Strata.Languages.Core.Typing.Props.ExprEraseProps
import all Strata.Languages.Core.ProcedureType
import all Strata.Languages.Core.ProcedureTypeProps
import all Strata.Languages.Core.Procedure
import all Strata.Languages.Core.TypeSkolem
import all Strata.Languages.Core.FunctionType
import Strata.Util.Tactics

/-! # Annotations of checked procedures

The procedure checker returns each procedure with its reserved type parameters renamed, its
signature types alias-resolved, the declared types of its variable declarations replaced by the
solved ones, and its expressions elaborated. `Procedure.typeCheck_annotRel` shows that the result
differs from the input only in those annotations. -/

namespace Core

open Lambda Imperative

public section

/-- `ty'` is the written type `ty` with its type variables instantiated, up to alias expansion,
    by a substitution that leaves every type variable in `rigid` unchanged. -/
def RigidInitTyRel (aliases : List TypeAlias) (rigid : List String) (ty ty' : LMonoTy) : Prop :=
  ∃ S : Subst, (∀ v ∈ rigid, LMonoTy.subst S (.ftvar v) = .ftvar v) ∧
    AliasEquiv aliases (LMonoTy.subst S ty) ty'

/-- `p'` is the checked form of the written procedure `p`: both erase to the same procedure; for
    one renaming `ren` of reserved type parameters, the type parameters of `p'` are those of `p`
    renamed to names the procedure does not mention, every signature type of `p'` is the written
    one renamed and alias-resolved, and every declared type of a variable declaration of `p'` is
    the written one renamed, instantiated up to aliases by a substitution that leaves the type
    parameters of `p'` unchanged. -/
def ProcAnnotRel (aliases : List TypeAlias) (p p' : Procedure) : Prop :=
  p'.eraseAnnots = p.eraseAnnots ∧
  (∃ ren : List (String × String),
    ReservedRenaming p.header.typeArgs p.mentionedTyVars ren ∧
    p'.header.typeArgs = renameTyArgList ren p.header.typeArgs ∧
    List.Rel₂ (SigTyRel aliases ren) p.header.inputs.values p'.header.inputs.values ∧
    List.Rel₂ (SigTyRel aliases ren) p.header.outputs.values p'.header.outputs.values ∧
    List.Rel₂ (RigidInitTyRel aliases p'.header.typeArgs) (p.initTys.map (renamedTy ren))
      p'.initTys)

variable {sc ps : Thunk (Std.HashSet String)} {tn : Unit → List String}

/-- If `fc` and `fg` keep the erasure of commands and expressions, mapping a control flow graph's
    commands by `fc` and its guards and block metadata expressions by `fg` keeps the graph's
    erasure. -/
private theorem DetCFG.eraseAnnots_mapCmdsGuards (cfg : DetCFG) (fc : Command → Command)
    (fg : Expression.Expr → Expression.Expr)
    (hc : ∀ c, Command.eraseAnnots (fc c) = Command.eraseAnnots c)
    (hg : ∀ e, (fg e).eraseTypes = e.eraseTypes) :
    DetCFG.eraseAnnots (DetCFG.mapCmdsGuards cfg fc fg) = DetCFG.eraseAnnots cfg := by
  unfold DetCFG.eraseAnnots DetCFG.mapCmdsGuards
  congr 1
  simp only [List.map_map, Function.comp_def]
  refine List.map_congr_left fun lb _ => ?_
  rcases lb with ⟨l, ⟨cs, tr, bmd⟩⟩
  simp only [hc, Imperative.MetaData.mapExprs_mapExprs_of _ _ hg]
  cases tr <;> simp only [hg]

/-- A condition the checker accepts is returned with the erasure of the written condition. -/
private theorem Procedure.checkCondition_eraseTypes
    {C : Expression.TyContext} {Env : Expression.TyEnv} {nm : CoreIdent} {σ : RigidNames}
    {label : CoreLabel} {chk chk' : Procedure.Check}
    (h : Procedure.checkCondition C Env nm σ label chk = .ok chk') :
    Procedure.Check.eraseTypes chk' = Procedure.Check.eraseTypes chk := by
  obtain ⟨et, EnvR, hres, -, rfl, -⟩ := Procedure.checkCondition_ok_inv h
  simp only [Procedure.Check.eraseTypes, eraseTypes_finishDeskolemized,
    SourceExpr.resolveWithType_unresolved_eraseTypes _ _ _ _ _ _ hres, eraseTypes_skolemizeBody]

/-- Pointwise related lists of conditions erase to the same list. -/
private theorem erase_checks_of_rel₂
    {R : CoreLabel × Procedure.Check → CoreLabel × Procedure.Check → Prop}
    (hR : ∀ a b, R a b →
      b.1 = a.1 ∧ Procedure.Check.eraseTypes b.2 = Procedure.Check.eraseTypes a.2)
    {l l' : List (CoreLabel × Procedure.Check)} (h : List.Rel₂ R l l') :
    l'.map (fun (x, c) => (x, Procedure.Check.eraseTypes c))
      = l.map (fun (x, c) => (x, Procedure.Check.eraseTypes c)) := by
  refine (List.Rel₂.map_eq (f := fun (x : CoreLabel × Procedure.Check) =>
    (x.1, Procedure.Check.eraseTypes x.2)) ?_ h).symm
  intro a b hab
  obtain ⟨h1, h2⟩ := hR a b hab
  simp only [h1, h2]

/-- The checker's core run returns a procedure that erases like the written one. -/
private theorem Procedure.typeCheckCore_eraseAnnots_eq
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {p : Program}
    {q q' : Procedure} {md : MetaData Expression}
    (h : Procedure.typeCheckCore sc ps C Env p q md tn = .ok (q', Env')) :
    q'.eraseAnnots = q.eraseAnnots := by
  obtain ⟨-, insR, outsR, run⟩ := Procedure.typeCheckCore_ok_inv h
  have hlen : ∀ (sig : @LMonoTySignature Unit) (tys : LMonoTys),
      sig.values.length = tys.length → (sig.map Prod.fst).length = tys.length := by
    intro sig tys hl
    have h1 := ListMap.keys.length (ls := sig)
    have h2 := ListMap.values_length sig
    rw [ListMap.keys_eq_map_fst] at h1
    omega
  have hin : (q.header.inputs.keys.zip insR).map (fun p => (p.1, LMonoTy.erased))
      = q.header.inputs.map (fun p => (p.1, LMonoTy.erased)) := by
    rw [ListMap.keys_eq_map_fst]
    exact zip_keys_map_erased (q.header.inputs : List (CoreIdent × LMonoTy)) insR
      (hlen _ _ (List.Rel₂.length_eq run.insKnown))
  have hout : (q.header.outputs.keys.zip outsR).map (fun p => (p.1, LMonoTy.erased))
      = q.header.outputs.map (fun p => (p.1, LMonoTy.erased)) := by
    rw [ListMap.keys_eq_map_fst]
    exact zip_keys_map_erased (q.header.outputs : List (CoreIdent × LMonoTy)) outsR
      (hlen _ _ (List.Rel₂.length_eq run.outsKnown))
  have hcond : ∀ (E : Expression.TyEnv) (sig : @LMonoTySignature Unit)
      (a b : CoreLabel × Procedure.Check),
      b.1 = a.1 ∧ Procedure.checkCondition (addSkolemTypes C (Procedure.rigidNames sc ps C q tn))
        (Function.formalsEnv E (Procedure.rigidNames sc ps C q tn) sig) q.header.name
        (Procedure.rigidNames sc ps C q tn) a.1 a.2 = .ok b.2 →
      b.1 = a.1 ∧ Procedure.Check.eraseTypes b.2 = Procedure.Check.eraseTypes a.2 :=
    fun _ _ _ _ hb => ⟨hb.1, Procedure.checkCondition_eraseTypes hb.2⟩
  have hpre := erase_checks_of_rel₂ (hcond _ _) run.preconditionsRel
  have hpost := erase_checks_of_rel₂ (hcond _ _) run.postconditionsRel
  have hspec : Procedure.Spec.eraseTypes q'.spec = Procedure.Spec.eraseTypes q.spec := by
    unfold Procedure.Spec.eraseTypes
    rw [hpre, hpost]
  cases hb : q.body with
  | structured ss o =>
    obtain ⟨ssOut, EnvX, hB, -, hbody'⟩ := run.bodyStructured ss o hb
    have hstmts : Statements.eraseAnnots
        (mapStmtsTys (deskolemizeTy (Procedure.rigidNames sc ps C q tn)) ssOut)
        = Statements.eraseAnnots ss := by
      rw [Statements.eraseAnnots_mapStmtsTys, Statement.typeCheck_eraseAnnots_eq _ _ _ _ _ _ _ hB,
        Statements.eraseAnnots_skolemizeStmts]
    unfold Procedure.eraseAnnots
    rw [hbody', hb, hspec, run.header]
    dsimp only
    rw [hstmts]
    congr 1
    congr 1 <;> first | exact hin | exact hout
  | cfg c o =>
    obtain ⟨loc, cOut, EnvX, hrunC, hbody'⟩ := run.bodyCfg c o hb
    have hcfg : DetCFG.eraseAnnots (DetCFG.mapCmdsGuards cOut
        (mapCmdTys (deskolemizeTy (Procedure.rigidNames sc ps C q tn)))
        (mapExprTys (deskolemizeTy (Procedure.rigidNames sc ps C q tn))))
        = DetCFG.eraseAnnots c := by
      rw [DetCFG.eraseAnnots_mapCmdsGuards _ _ _ (Command.eraseAnnots_mapCmdTys _)
        (LExpr.eraseTypes_mapExprTys _), CFG.typeCheck_eraseAnnots_eq hrunC,
        DetCFG.eraseAnnots_mapCmdsGuards _ _ _ (Command.eraseAnnots_skolemizeCmd _ _)
        (eraseTypes_skolemizeBody _ _)]
    unfold Procedure.eraseAnnots
    rw [hbody', hb, hspec, run.header]
    dsimp only
    rw [hcfg]
    congr 1
    congr 1 <;> first | exact hin | exact hout
  | abstract =>
    unfold Procedure.eraseAnnots
    rw [run.bodyAbstract hb, hb, hspec, run.header]
    dsimp only
    congr 1
    congr 1 <;> first | exact hin | exact hout

/-- The core run keeps the type parameters and alias-resolves the parameter types. -/
private theorem Procedure.typeCheckCore_signature
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {p : Program}
    {q q' : Procedure} {md : MetaData Expression}
    (h : Procedure.typeCheckCore sc ps C Env p q md tn = .ok (q', Env')) :
    q'.header.typeArgs = q.header.typeArgs ∧
    q'.header.inputs.values = q.header.inputs.values.map (resolveTy Env.context.aliases) ∧
    q'.header.outputs.values = q.header.outputs.values.map (resolveTy Env.context.aliases) := by
  have hres := Procedure.typeCheckCore_sigResolved C Env Env' p q q' md h
  exact ⟨Procedure.typeCheckCore_typeArgs_eq C Env Env' p q q' md h, hres.inputsVals,
    hres.outputsVals⟩

/-- The declared types of a procedure with a structured body are those of its statements. -/
private theorem Procedure.initTys_structured {q : Procedure} {ss : List Statement} {o : Bool}
    (hb : q.body = .structured ss o) : q.initTys = Statements.initTys ss := by
  simp only [Procedure.initTys, hb]

/-- The declared types of a procedure with a control flow graph body are those of its blocks. -/
private theorem Procedure.initTys_cfg {q : Procedure} {c : DetCFG} {o : Bool}
    (hb : q.body = .cfg c o) : q.initTys = DetCFG.initTys c := by
  simp only [Procedure.initTys, hb]

/-- Skolemizing a statement list skolemizes each declared type. -/
private theorem Statements.initTys_skolemizeStmts (nm : Option String) (σ : RigidNames)
    (ss : List Statement) :
    Statements.initTys (skolemizeStmts nm σ ss) = (Statements.initTys ss).map (skolemizeTy σ) := by
  unfold Statements.initTys
  rw [skolemizeStmts_eq_mapExpr, Block.initTypes_mapExpr _ _ (mapLTyTys (skolemizeTy σ)) ?_ ss,
    List.map_map, List.map_map]
  · rfl
  · intro c
    cases c with
    | cmd cc =>
      cases cc <;> simp only [skolemizeCmd, mapCmdWith, CmdExt.initTypes, Cmd.initTypes,
        List.map_cons, List.map_nil, ExprOrNondet.map]
    | call => rfl

/-- Rewriting the type annotations of a statement list rewrites each declared type. -/
private theorem Statements.initTys_mapStmtsTys (f : LMonoTy → LMonoTy) (ss : List Statement) :
    Statements.initTys (mapStmtsTys f ss) = (Statements.initTys ss).map f := by
  unfold Statements.initTys
  rw [mapStmtsTys, Block.initTypes_mapExpr _ _ (mapLTyTys f) ?_ ss, List.map_map, List.map_map]
  · rfl
  · intro c
    cases c with
    | cmd cc =>
      cases cc <;> simp only [mapCmdTys, mapCmdWith, CmdExt.initTypes, Cmd.initTypes,
        List.map_cons, List.map_nil, ExprOrNondet.map]
    | call => rfl

/-- Every declared type of a variable declaration is among the type annotations of the
    statements. -/
private theorem Statements.initTys_subset_annotTys (ss : List Statement) :
    ∀ t ∈ Statements.initTys ss, t ∈ stmtsAnnotTys ss := by
  induction ss using Block.mapExpr.induct
    (motive1 := fun s => ∀ t ∈ (Stmt.initTypes (P := Expression) (C := Command) s).map
      LTy.toMonoTypeUnsafe, t ∈ stmtCollect exprAnnotTys ([·]) s) <;>
    simp_all only [Statements.initTys, stmtsAnnotTys, stmtCollect, stmtsCollect, stmtOwnCollect,
      cmdCollect, Stmt.initTypes, Block.initTypes, HasInitTypesImp.initTypes, List.map_append,
      List.map_nil, List.mem_append, List.mem_flatMap, List.mem_map, List.append_nil,
      List.nil_append, implies_true] <;>
    grind

/-- Deskolemizing an instance of a skolemized type gives an instance of the type, up to aliases,
    by a substitution that leaves the renamed type parameters unchanged, when no constant of the
    renaming occurs in the type. -/
private theorem RigidInitTyRel.deskolemizeTy {A : List TypeAlias} {σ : RigidNames}
    (hnd : (σ.map Prod.snd).Nodup) (hns : AliasesNoSkolem σ A) {t T : LMonoTy}
    (ht : mtyAllTyConsNames (notRigidConst σ) t = true) (h : InitTyRel A (skolemizeTy σ t) T) :
    RigidInitTyRel A (σ.map Prod.fst) t (deskolemizeTy σ T) := by
  obtain ⟨S, hS⟩ := h
  have hae := AliasEquiv_deskolemizeTy hS hns
  have hfree := freeVars_skolemizeTy_not_mem σ t
  obtain ⟨τ, hfix, hτ⟩ := deskolemizeTy_subst_instance_fixing σ S (skolemizeTy σ t) hfree
  rw [hτ, deskolemizeTy_skolemizeTy_eq_deskolemizeTy hnd,
    deskolemizeTy_eq_self_of_notRigidConst t ht] at hae
  exact ⟨τ, fun v hv => hfix v fun hmem => hfree v hmem hv, hae⟩

/-- Deskolemizing the right list of a pointwise instance relation between the skolemized written
    types and the checked ones gives the relation between the written types and the
    deskolemized checked ones. -/
private theorem rel₂_initTyRel_deskolemizeTy {A : List TypeAlias} {σ : RigidNames}
    (hnd : (σ.map Prod.snd).Nodup) (hns : AliasesNoSkolem σ A) :
    ∀ {l X : List LMonoTy}, (∀ t ∈ l, mtyAllTyConsNames (notRigidConst σ) t = true) →
      List.Rel₂ (InitTyRel A) (l.map (skolemizeTy σ)) X →
      List.Rel₂ (RigidInitTyRel A (σ.map Prod.fst)) l (X.map (deskolemizeTy σ))
  | [], X, _, h => by
    cases h
    exact .nil
  | t :: l, X, hl, h => by
    cases h with
    | cons hhd hrest =>
      exact .cons (RigidInitTyRel.deskolemizeTy hnd hns (hl t List.mem_cons_self) hhd)
        (rel₂_initTyRel_deskolemizeTy hnd hns
          (fun t' ht' => hl t' (List.mem_cons_of_mem _ ht')) hrest)

/-- The declared types of a control flow graph are those of the commands of its blocks, in
    order. -/
private theorem DetCFG.initTys_eq (c : DetCFG) :
    c.initTys = c.blocks.flatMap fun (_, blk) => blk.cmds.flatMap cmdInitTys := by
  simp only [DetCFG.initTys, Imperative.DetCFG.initTypes, List.map_flatMap]
  rfl

/-- Rewriting each command of a control flow graph by a map that rewrites the declared types it
    collects rewrites the declared types the graph collects. -/
private theorem DetCFG.initTys_mapCmdsGuards (c : DetCFG) (fc : Command → Command)
    (fg : Expression.Expr → Expression.Expr) (F : LMonoTy → LMonoTy)
    (hc : ∀ cmd, cmdInitTys (fc cmd) = (cmdInitTys cmd).map F) :
    (DetCFG.mapCmdsGuards c fc fg).initTys = c.initTys.map F := by
  unfold DetCFG.mapCmdsGuards
  simp only [DetCFG.initTys_eq, List.flatMap_map, List.map_flatMap, hc]

/-- Skolemizing a command skolemizes each declared type it declares. -/
private theorem cmdInitTys_skolemizeCmd (nm : Option String) (σ : RigidNames)
    (c : Command) :
    cmdInitTys (skolemizeCmd nm σ c) = (cmdInitTys c).map (skolemizeTy σ) := by
  unfold cmdInitTys
  cases c with
  | cmd cc =>
    cases cc <;> simp only [skolemizeCmd, mapCmdWith, CmdExt.initTypes, Cmd.initTypes,
      List.map_cons, List.map_nil, LTy.toMonoTypeUnsafe, mapLTyTys, ExprOrNondet.map]
  | call => rfl

/-- Rewriting the type annotations of a command rewrites each declared type it declares. -/
private theorem cmdInitTys_mapCmdTys (f : LMonoTy → LMonoTy) (c : Command) :
    cmdInitTys (mapCmdTys f c) = (cmdInitTys c).map f := by
  unfold cmdInitTys
  cases c with
  | cmd cc =>
    cases cc <;> simp only [mapCmdTys, mapCmdWith, CmdExt.initTypes, Cmd.initTypes,
      List.map_cons, List.map_nil, LTy.toMonoTypeUnsafe, mapLTyTys, ExprOrNondet.map]
  | call => rfl

/-- Every declared type a procedure collects is among the types it writes. -/
private theorem Procedure.initTys_subset_annotTys (q : Procedure) :
    ∀ t ∈ q.initTys, t ∈ procAnnotTys q := by
  intro t ht
  unfold procAnnotTys
  refine List.mem_append_right _ ?_
  cases hb : q.body with
  | structured ss o =>
    rw [Procedure.initTys_structured hb] at ht
    exact Statements.initTys_subset_annotTys ss t ht
  | abstract =>
    simp only [Procedure.initTys, hb, List.not_mem_nil] at ht
  | cfg c o =>
    rw [Procedure.initTys_cfg hb] at ht
    simp only [DetCFG.initTys_eq, List.mem_flatMap] at ht
    obtain ⟨lb, hlb, cmd, hcmd, ht⟩ := ht
    simp only [cmdInitTys, List.mem_map] at ht
    obtain ⟨ty, hty, rfl⟩ := ht
    have hmem : ty.toMonoTypeUnsafe ∈ cmdCollect exprAnnotTys ([·]) cmd := by
      simp only [cmdCollect, List.mem_append, List.mem_flatMap, List.mem_singleton]
      exact Or.inl (Or.inl ⟨ty, hty, rfl⟩)
    simp only [bodyAnnotTys, bodyCollect, List.mem_flatMap]
    exact ⟨lb, hlb, List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨cmd, hcmd, hmem⟩))⟩

/-- Related lists whose related elements have related images have related concatenations. -/
private theorem rel₂_flatMap_rel {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → List γ} {g : β → List δ} (hfg : ∀ a b, R a b → List.Rel₂ S (f a) (g b)) :
    ∀ {l : List α} {l' : List β}, List.Rel₂ R l l' → List.Rel₂ S (l.flatMap f) (l'.flatMap g)
  | _, _, .nil => .nil
  | _, _, .cons hab hrest => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact List.Rel₂.append (hfg _ _ hab) (rel₂_flatMap_rel hfg hrest)

/-- Declared types related as type schemes are related as monotypes. -/
private theorem rel₂_declTyRel_toMono {A : List TypeAlias} :
    ∀ {l X : List LTy}, List.Rel₂ (DeclTyRel A) l X →
      List.Rel₂ (InitTyRel A) (l.map LTy.toMonoTypeUnsafe) (X.map LTy.toMonoTypeUnsafe)
  | _, _, .nil => .nil
  | _, _, .cons hhd hrest => by
    obtain ⟨t', rfl, hrel⟩ := hhd
    exact .cons hrel (rel₂_declTyRel_toMono hrest)

/-- The returned CFG's declared types are instances of the written ones, up to the aliases of the
    incoming environment. -/
private theorem CFG.typeCheck_initTys {C : Expression.TyContext} {Env : Expression.TyEnv}
    {P : Program} {proc : Procedure} {cfg : DetCFG} {sourceLoc : Strata.FileRange}
    {res : DetCFG × Expression.TyEnv}
    (hwf : TContext.AliasesWF Env.context)
    (hrun : CFG.typeCheck C Env P proc cfg sourceLoc = .ok res) :
    List.Rel₂ (InitTyRel Env.context.aliases) cfg.initTys res.1.initTys := by
  have hwfA : ∀ a ∈ Env.context.aliases, TypeAlias.WF a := TContext.AliasesWF.mem hwf
  have hb := CFG.typeCheck_blocksRel_aliases (C := C) (P := P) (proc := proc)
    (fun x y => List.Rel₂ (DeclTyRel Env.context.aliases) (CmdExt.initTypes x)
      (CmdExt.initTypes y)) (fun _ _ => True)
    (fun E E' x y hE h => by
      have hwfE : TContext.AliasesWF E.context := fun a ha => hwf a (hE ▸ ha)
      have hrel := Statement.typeCheckCmd_declTyRel C E E' P x y hwfE h
      rwa [hE] at hrel)
    (fun x y S hxy => by
      rw [Command.initTypes_subst]
      refine List.Rel₂.map_right (LTy.subst S) (fun a b hab => ?_) hxy
      obtain ⟨t', rfl, hrel⟩ := hab
      exact ⟨LMonoTy.subst S t', rfl, InitTyRel.subst hwfA S hrel⟩)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial) hrun
  rw [DetCFG.initTys_eq, DetCFG.initTys_eq]
  refine rel₂_flatMap_rel (fun lb lb' hlb => ?_) hb.2
  refine rel₂_flatMap_rel (fun x y hxy => ?_) hlb.2.1
  exact rel₂_declTyRel_toMono hxy

/-- Each declared type of a variable declaration the core run returns is an instance of the
    written one, up to the aliases of the incoming environment, by a substitution that leaves
    the type parameters unchanged. -/
private theorem Procedure.typeCheckCore_initTyRel
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {p : Program}
    {q q' : Procedure} {md : MetaData Expression}
    (h : Procedure.typeCheckCore sc ps C Env p q md tn = .ok (q', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (htn : ∀ n ∈ procTyNames q (procAnnotTys q), n ∈ tn ())
    (hdecl : q.header.SigDeclared)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions) :
    List.Rel₂ (RigidInitTyRel Env.context.aliases q.header.typeArgs) q.initTys q'.initTys := by
  rw [← (Procedure.rigidNames_fresh sc ps C q tn).2.2.2.1]
  obtain ⟨-, insR, outsR, run⟩ := Procedure.typeCheckCore_ok_inv h
  have hnd := (Procedure.rigidNames_fresh sc ps C q tn).2.1
  have hns := (Procedure.rigidNames_spec sc ps C Env q tn hcov).noSkolemAmbient.aliases
  have hσ := Procedure.typeCheckCore_signatureFreeVars_rigid C Env Env' p q q' md h hdecl
    h_env.aliasesWF
  have hfac' : FactorySigWF (addSkolemTypes C (Procedure.rigidNames sc ps C q tn)).functions := by
    simpa only [addSkolemTypes_functions] using h_fac
  have hwf := formalsEnv_TEnvWF Env (Procedure.rigidNames sc ps C q tn) (bodySig q'.header)
    h_env (bodySig_freeVars_mem _ _ hσ)
  have hne := skolemScopeEnv_types_ne (Procedure.rigidNames sc ps C q tn) Env (bodySig q'.header)
  have haliases := formalsEnv_aliases Env (Procedure.rigidNames sc ps C q tn) (bodySig q'.header)
  have hnot : ∀ t ∈ q.initTys,
      mtyAllTyConsNames (notRigidConst (Procedure.rigidNames sc ps C q tn)) t = true :=
    fun t ht => mtyAllTyConsNames_notRigidConst_of_not_mem fun pr hpr =>
      Procedure.rigidNames_not_procAnnotTys sc ps C q tn htn pr hpr t
        (Procedure.initTys_subset_annotTys q t ht)
  cases hb : q.body with
  | structured ss o =>
    obtain ⟨ssOut, EnvX, hB, -, hbody'⟩ := run.bodyStructured ss o hb
    have hrel := Statement.typeCheck_initTyRel _ _ _ p (some q) _ ssOut hB hwf hfac' hne
    rw [haliases, Statements.initTys_skolemizeStmts] at hrel
    rw [Procedure.initTys_structured hb] at hnot
    rw [Procedure.initTys_structured hb, Procedure.initTys_structured hbody',
      Statements.initTys_mapStmtsTys]
    exact rel₂_initTyRel_deskolemizeTy hnd hns hnot hrel
  | cfg c o =>
    obtain ⟨loc, cOut, EnvX, hrunC, hbody'⟩ := run.bodyCfg c o hb
    have hrel := CFG.typeCheck_initTys hwf.aliasesWF hrunC
    rw [haliases, DetCFG.initTys_mapCmdsGuards c _ _
      (skolemizeTy (Procedure.rigidNames sc ps C q tn))
      (cmdInitTys_skolemizeCmd none _)] at hrel
    rw [Procedure.initTys_cfg hb] at hnot
    rw [Procedure.initTys_cfg hb, Procedure.initTys_cfg hbody',
      DetCFG.initTys_mapCmdsGuards cOut _ _ (deskolemizeTy (Procedure.rigidNames sc ps C q tn))
        (fun cmd => cmdInitTys_mapCmdTys _ cmd)]
    exact rel₂_initTyRel_deskolemizeTy hnd hns hnot hrel
  | abstract =>
    simp only [Procedure.initTys, hb, run.bodyAbstract hb]
    exact .nil

/-- The erasure of a signature list with renamed types is that of the original. -/
private theorem erase_sig_rename (ren : List (String × String))
    (sig : List (CoreIdent × LMonoTy)) :
    (sig.map fun p => (p.1, renamedTy ren p.2)).map (fun (x, _) => (x, LMonoTy.erased))
      = sig.map (fun (x, _) => (x, LMonoTy.erased)) := by
  induction sig with
  | nil => rfl
  | cons a sig ih => simp only [List.map_cons, ih]

/-- Renaming the types of each condition keeps the erasure of the conditions. -/
private theorem erase_checks_rename (ren : List (String × String))
    (cs : List (CoreLabel × Procedure.Check)) :
    (cs.map fun p => (p.1, { p.2 with expr := mapExprTys (renamedTy ren) p.2.expr })).map
        (fun (l, c) => (l, Procedure.Check.eraseTypes c))
      = cs.map (fun (l, c) => (l, Procedure.Check.eraseTypes c)) := by
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, ih]
    simp only [Procedure.Check.eraseTypes, LExpr.eraseTypes_mapExprTys]

/-- Renaming the type parameters of a procedure leaves its erasure unchanged. -/
private theorem Procedure.eraseAnnots_renameTypeArgs (q : Procedure)
    (ren : List (String × String)) :
    (q.renameTypeArgs ren).eraseAnnots = q.eraseAnnots := by
  unfold Procedure.eraseAnnots Procedure.renameTypeArgs Procedure.mapTys Procedure.Spec.eraseTypes
  congr 1
  · rw [erase_sig_rename ren q.header.inputs, erase_sig_rename ren q.header.outputs]
    simp only [renameTyArgList, List.map_map, Function.comp_def]
  · rw [erase_checks_rename ren q.spec.preconditions,
      erase_checks_rename ren q.spec.postconditions]
  · cases q.body with
    | structured ss o => simp only [Statements.eraseAnnots_mapStmtsTys]
    | cfg c o =>
      simp only [DetCFG.eraseAnnots_mapCmdsGuards c _ _ (Command.eraseAnnots_mapCmdTys _)
        (LExpr.eraseTypes_mapExprTys _)]
    | abstract => rfl

/-- Renaming the type parameters of a procedure renames each declared type. -/
private theorem Procedure.initTys_renameTypeArgs (q : Procedure) (ren : List (String × String)) :
    (q.renameTypeArgs ren).initTys = q.initTys.map (renamedTy ren) := by
  unfold Procedure.initTys Procedure.renameTypeArgs Procedure.mapTys
  cases q.body with
  | structured ss o => exact Statements.initTys_mapStmtsTys _ ss
  | cfg c o => exact DetCFG.initTys_mapCmdsGuards c _ _ _ (cmdInitTys_mapCmdTys _)
  | abstract => rfl

/-- A procedure `Procedure.typeCheckIn` accepts is returned as its written form with the
    reserved type parameters renamed, the signature types alias-resolved, the declared types
    instantiated without refining a type parameter, and the expressions elaborated. -/
theorem Procedure.typeCheckIn_annotRel (scope progSigs : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheckIn scope progSigs C Env p proc md = .ok (proc', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ scope.get)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions) :
    ProcAnnotRel Env.context.aliases proc proc' := by
  have hnd := Procedure.typeCheckIn_typeArgs_nodup h
  have hcore := Procedure.typeCheckIn_core_ok h
  obtain ⟨-, hdecl, -⟩ := Procedure.typeCheckIn_renamed_headerNames h
  unfold Procedure.renamedForCheck at hdecl
  have htn : ∀ n ∈ procTyNames
      (proc.renameReservedTypeArgs (fun _ => Statement.substTyVars Env ++ scopeTyVars C Env)
        fun _ => procAnnotTys proc)
      (procAnnotTys (proc.renameReservedTypeArgs
        (fun _ => Statement.substTyVars Env ++ scopeTyVars C Env) fun _ => procAnnotTys proc)),
      n ∈ procTyNames proc (procAnnotTys proc) := by
    intro n hn
    rw [procTyNames_renameReservedTypeArgs] at hn
    exact hn
  rw [Procedure.renameReservedTypeArgs_eq] at hcore hdecl htn
  have hres := reservedTypeArgsRenaming_reservedRenaming proc.header.typeArgs
    proc.mentionedTyVars
    (fun u => proc.mentionedTyVarsIn (procAnnotTys proc) ++
      (Statement.substTyVars Env ++ scopeTyVars C Env)) hnd
    (fun v hv => List.mem_append_left _ hv)
  generalize reservedTypeArgsRenaming proc.header.typeArgs
    (fun u => proc.mentionedTyVarsIn (procAnnotTys proc) ++
      (Statement.substTyVars Env ++ scopeTyVars C Env)) = ren at *
  have herase := Procedure.typeCheckCore_eraseAnnots_eq hcore
  obtain ⟨hta, hin, hout⟩ := Procedure.typeCheckCore_signature hcore
  have hinit := Procedure.typeCheckCore_initTyRel hcore hcov htn hdecl h_env h_fac
  obtain ⟨hvIn, hvOut⟩ := Procedure.renameTypeArgs_values proc ren
  refine ⟨?_, ren, hres, ?_, ?_, ?_, ?_⟩
  · rw [herase, Procedure.eraseAnnots_renameTypeArgs]
  · rw [hta]
    rfl
  · rw [hin, hvIn, List.map_map]
    exact List.Rel₂.self_map (fun ty => resolveTy Env.context.aliases (renamedTy ren ty)) _
      fun _ _ => rfl
  · rw [hout, hvOut, List.map_map]
    exact List.Rel₂.self_map (fun ty => resolveTy Env.context.aliases (renamedTy ren ty)) _
      fun _ _ => rfl
  · rw [Procedure.initTys_renameTypeArgs] at hinit
    rw [hta]
    exact hinit

/-- A procedure `Procedure.typeCheck` accepts is returned as its written form with the reserved
    type parameters renamed, the signature types alias-resolved, the declared types instantiated
    without refining a type parameter, and the expressions elaborated. -/
theorem Procedure.typeCheck_annotRel
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (p : Program)
    (proc proc' : Procedure) (md : MetaData Expression)
    (h : Procedure.typeCheck C Env p proc md = .ok (proc', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions) :
    ProcAnnotRel Env.context.aliases proc proc' :=
  Procedure.typeCheckIn_annotRel _ _ C Env Env' p proc proc' md h (scopeTyNameThunk_cover C Env)
    h_env h_fac

end

end Core
