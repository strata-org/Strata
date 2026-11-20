/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementType
public import Strata.Languages.Core.TypeSkolem
public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.Languages.Core.Typing.Spec.StatementTypeSpec
public import Strata.Languages.Core.Typing.Props.CmdTypeSpecProps
public import Strata.Languages.Core.Typing.Props.TypeSkolemProps
public import Strata.Languages.Core.Typing.Props.FunctionTypeProps
import Strata.Languages.Core.StatementProps
import Strata.DL.Lambda.LExprWFProps
import Strata.DL.Lambda.FactoryProps
import Strata.DL.Lambda.LExprTypeSpecProps
import Strata.Util.StringProps
import all Strata.Languages.Core.StatementType
import all Strata.Languages.Core.Typing.Props.TypeSkolemProps
import Strata.Languages.Core.Typing.Spec.TypeSpecShared
import Strata.Languages.Core.Statement
import Strata.DL.Imperative.Cmd
import Strata.DL.Lambda.LTyUnify
import Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.TypeFactory

/-! # Properties of Core statement type substitution and statement typing

Statement typing is stable under type substitution, scope changes and identifier-table changes.

Key theorems:
* `Command.modifiedVars_subst`, `Statement_subst_modifiedVars`: type substitution keeps the
  variables a statement modifies.
* `StatementsHasType_transport`: typing moves to a scope with the same lookups and aliases.
* `checkTysKnown_toOption`: the registered-type check succeeds exactly on registered instances.
* `StatementsWellTyped.of_findEq`, `StatementsWellTyped.withIdents`: well-typedness moves to a
  scope with the same lookups, and does not depend on the identifier table. -/

public section

namespace Core

open Lambda Imperative

/-- The statement substitution worker returns the reversed accumulator followed by the
    substituted input list. -/
private theorem Statement_subst_go_eq (S : Subst) (ss acc : List Statement) :
    Statement.Statement.subst.go S ss acc =
      acc.reverse ++ ss.map (Statement.Statement.subst S) := by
  induction ss generalizing acc with
  | nil =>
    simp only [Statement.Statement.subst.go, List.map_nil, List.append_nil]
  | cons s rest ih =>
    simp only [Statement.Statement.subst.go, ih, List.reverse_cons, List.map_cons,
      List.append_assoc, List.cons_append, List.nil_append]

/-- Substituting types in a command preserves the variables it may modify. -/
theorem Command.modifiedVars_subst (S : Subst) (c : Command) :
    Command.modifiedVars (Statement.Command.subst S c) = Command.modifiedVars c := by
  cases c with
  | cmd cc =>
    cases cc <;>
      simp only [Statement.Command.subst, Statement.Cmd.subst, Command.modifiedVars,
        CmdExt.modifiedVars, Cmd.modifiedVars]
  | call pname tyArgs args md =>
    simp only [Statement.Command.subst, Command.modifiedVars]
    exact CallArg.getLhs_map_congr (fun e => e.applyTypeSubst S) args

/-- Applying a type substitution to a command rewrites the type arguments and the `inArg`
    expressions of the call it is, if any, with the substitution and leaves the rest of the call
    alone. -/
theorem Command.callSites_subst (S : Subst) (c : Command) :
    Command.callSites (Statement.Command.subst S c) =
      (Command.callSites c).map fun cs =>
        { cs with tyArgs := cs.tyArgs.map (·.map (LTy.subst S)),
                  args := cs.args.map (CallArg.mapInput (·.applyTypeSubst S)) } := by
  cases c <;> rfl

/-- Substituting command types preserves the variables introduced by the command. -/
theorem Command.definedVars_subst (S : Subst) (c : Command) :
    Command.definedVars (Statement.Command.subst S c) = Command.definedVars c := by
  cases c with
  | cmd cc =>
    cases cc <;>
      simp only [Statement.Command.subst, Statement.Cmd.subst, Command.definedVars,
        CmdExt.definedVars, Cmd.definedVars]
  | call pname args md => simp only [Statement.Command.subst, Command.definedVars,
    CmdExt.definedVars]

/-- Substituting types in a statement preserves its modified variables. -/
theorem Statement_subst_modifiedVars (S : Subst) (s : Statement) :
    Stmt.modifiedVars (Statement.Statement.subst S s) = Stmt.modifiedVars s := by
  induction s using Stmt.mapExpr.induct (motive2 := fun ss =>
      Block.modifiedVars (ss.map (Statement.Statement.subst S)) = Block.modifiedVars ss) with
  | case1 c => exact Command.modifiedVars_subst S c
  | _ => simp_all only [Statement.Statement.subst, Stmt.modifiedVars, Block.modifiedVars,
      Statement_subst_go_eq, List.reverse_nil, List.nil_append, List.map_cons, List.map_nil]

/-- The statement substitution worker preserves the modified variables of its input list. -/
private theorem Statement_subst_go_modifiedVars (S : Subst) (ss : List Statement) :
    Block.modifiedVars (Statement.Statement.subst.go S ss []) =
      Block.modifiedVars ss :=
  Statement_subst_modifiedVars S (.block "" ss #[])

/-- The statement substitution worker preserves the scoped defined variables of its input list. -/
private theorem Statement_subst_go_definedVars (S : Subst) (ss : List Statement) :
    ∀ b, Block.definedVars (Statement.Statement.subst.go S ss []) b
      = Block.definedVars ss b := by
  rw [Statement_subst_go_eq, List.reverse_nil, List.nil_append]
  induction ss using Block.mapExpr.induct (motive1 := fun s =>
      ∀ b, Stmt.definedVars (Statement.Statement.subst S s) b = Stmt.definedVars s b) with
  | case1 c => exact Command.definedVars_subst S c
  | _ => simp_all only [Statement.Statement.subst, Stmt.definedVars, Block.definedVars,
      Statement_subst_go_eq, List.reverse_nil, List.nil_append, List.map_cons, List.map_nil,
      implies_true]

/-- Substituting command types preserves the names of procedures it may call. -/
private theorem CmdExt.calledProcedureNames_subst (S : Subst) (c : Command) :
    CmdExt.calledProcedureNames (Statement.Command.subst S c)
      = CmdExt.calledProcedureNames c := by
  cases c with
  | cmd cc => cases cc <;> simp [Statement.Command.subst, Statement.Cmd.subst]
  | call pname args md => simp [Statement.Command.subst]

/-- The statement substitution worker preserves the procedures called by its input list. -/
private theorem Statement_subst_go_calledProcedureNames (S : Subst) (ss : List Statement) :
    Statements.calledProcedureNames (Statement.Statement.subst.go S ss [])
      = Statements.calledProcedureNames ss := by
  rw [Statement_subst_go_eq, List.reverse_nil, List.nil_append]
  induction ss using Block.mapExpr.induct (motive1 := fun s =>
      Statement.calledProcedureNames (Statement.Statement.subst S s)
        = Statement.calledProcedureNames s) <;>
    simp_all only [Statement.Statement.subst, Statement.calledProcedureNames_cmd,
      Statement.calledProcedureNames_block, Statement.calledProcedureNames_ite,
      Statement.calledProcedureNames_loop, Statements.calledProcedureNames_cons,
      CmdExt.calledProcedureNames_subst, Statement_subst_go_eq, List.reverse_nil,
      List.nil_append, List.map_cons, List.map_nil]

/-- Substituting types in a command keeps the type names of the literals of the expressions it
    reads. -/
theorem Command.cmdExprs_litTyNames_subst (S : Subst) (c : Command) :
    (Statement.cmdExprs (Statement.Command.subst S c)).flatMap exprLitTyNames =
      (Statement.cmdExprs c).flatMap exprLitTyNames := by
  have hsub : ∀ e : Expression.Expr,
      exprLitTyNames (e.applyTypeSubst S) = exprLitTyNames e := by
    intro e
    unfold exprLitTyNames
    rw [getConsts_applyTypeSubst]
  have hopt : ∀ e : ExprOrNondet Expression,
      (e.map (LExpr.applyTypeSubst · S)).toList.flatMap exprLitTyNames =
        e.toList.flatMap exprLitTyNames := by
    intro e
    cases e <;> simp only [ExprOrNondet.map, ExprOrNondet.toList, List.flatMap_cons,
      List.flatMap_nil, hsub]
  cases c with
  | cmd cc =>
    cases cc with
    | init x ty e md =>
      simp only [Statement.Command.subst, Statement.Cmd.subst, Statement.cmdExprs,
        Cmd.readExprs]
      exact hopt e
    | set x e md =>
      simp only [Statement.Command.subst, Statement.Cmd.subst, Statement.cmdExprs,
        Cmd.readExprs]
      exact hopt e
    | assert l b md | assume l b md | cover l b md =>
      simp only [Statement.Command.subst, Statement.Cmd.subst, Statement.cmdExprs,
        Cmd.readExprs, List.flatMap_cons, List.flatMap_nil, hsub]
  | call pname tyArgs args md =>
    simp only [Statement.Command.subst, Statement.cmdExprs]
    induction args with
    | nil => rfl
    | cons a rest ih =>
      cases a <;> simp only [List.map_cons, Statement.CallArg.subst, CallArg.mapInput,
        CallArg.getInputExprs_cons_inArg, CallArg.getInputExprs_cons_inoutArg,
        CallArg.getInputExprs_cons_outArg, List.flatMap_cons, hsub] at ih ⊢ <;>
        simp only [ih]

/-- Substituting types in a statement list keeps the type names of its literals. -/
theorem stmtsLitTyNames_map_subst (S : Subst) (ss : List Statement) :
    stmtsLitTyNames (ss.map (Statement.Statement.subst S)) = stmtsLitTyNames ss := by
  have hsub : ∀ e : Expression.Expr,
      exprLitTyNames (e.applyTypeSubst S) = exprLitTyNames e := by
    intro e
    unfold exprLitTyNames
    rw [getConsts_applyTypeSubst]
  induction ss using Block.mapExpr.induct (motive1 := fun s =>
      stmtLitTyNames (Statement.Statement.subst S s) = stmtLitTyNames s) with
  | case1 c =>
    simp only [Statement.Statement.subst, stmtLitTyNames_cmd]
    exact Command.cmdExprs_litTyNames_subst S c
  | case2 l bss md ih =>
    simp only [Statement.Statement.subst, stmtLitTyNames_block, Statement_subst_go_eq,
      List.reverse_nil, List.nil_append]
    exact ih
  | case3 c tss ess md iht ihe =>
    simp only [Statement.Statement.subst, stmtLitTyNames_ite, Statement_subst_go_eq,
      List.reverse_nil, List.nil_append, ExprOrNondet.map, ExprOrNondet.toList,
      List.flatMap_cons, List.flatMap_nil, hsub, iht, ihe]
  | case4 tss ess md iht ihe =>
    simp only [Statement.Statement.subst, stmtLitTyNames_ite, Statement_subst_go_eq,
      List.reverse_nil, List.nil_append, ExprOrNondet.map, ExprOrNondet.toList,
      List.flatMap_nil, iht, ihe]
  | case5 g m i body md ih =>
    simp only [Statement.Statement.subst, stmtLitTyNames_loop, Statement_subst_go_eq,
      List.reverse_nil, List.nil_append, ih]
    rw [loopExprs_flatMap_litTyNames_map _ hsub]
  | case6 m i body md ih =>
    simp only [Statement.Statement.subst, stmtLitTyNames_loop, Statement_subst_go_eq,
      List.reverse_nil, List.nil_append, ih]
    rw [loopExprs_flatMap_litTyNames_map _ hsub]
  | case7 l md =>
    simp only [Statement.Statement.subst, stmtLitTyNames, stmtCollect, stmtOwnCollect,
      List.append_nil]
  | case8 tc md =>
    simp only [Statement.Statement.subst, stmtLitTyNames, stmtCollect, stmtOwnCollect,
      List.append_nil]
  | case9 => rfl
  | case10 s rest ihs ihr =>
    simp only [List.map_cons, stmtsLitTyNames_cons, ihs, ihr]

namespace TypeSpec

open Lambda LExpr Imperative

/-- Statement-list typing by the typechecker spec with written type variables transfers to a
    type scope with the same lookups and aliases, with an output scope of the same lookups and
    aliases. -/
theorem StatementsHasType_transport {P : Program}
    {C : LContext CoreLParams} {Γ Ξ : TContext Unit} {Δ : WrittenEnv} {L : List String}
    {ss : List Statement} {Cout : LContext CoreLParams} {Γout : TContext Unit}
    {Δout : WrittenEnv} (hR : TContext.FindEq (T := CoreLParams) Ξ Γ)
    (h : StatementsHasType P C Γ Δ L ss Cout Γout Δout) :
    ∃ Γout', StatementsHasType P C Ξ Δ L ss Cout Γout' Δout ∧
      TContext.FindEq (T := CoreLParams) Γout' Γout := by
  refine StatementsHasType.rec
    (motive_1 := fun C Γ Δ L s C' Γ' Δ' _ => ∀ Ξ, TContext.FindEq (T := CoreLParams) Ξ Γ →
      ∃ Ξ', StatementHasType P C Ξ Δ L s C' Ξ' Δ' ∧
        TContext.FindEq (T := CoreLParams) Ξ' Γ')
    (motive_2 := fun C Γ Δ L ss C' Γ' Δ' _ => ∀ Ξ, TContext.FindEq (T := CoreLParams) Ξ Γ →
      ∃ Ξ', StatementsHasType P C Ξ Δ L ss C' Ξ' Δ' ∧
        TContext.FindEq (T := CoreLParams) Ξ' Γ')
    ?cmd ?block ?ite_det ?ite_nondet ?loop ?exit ?typeDecl ?nil ?cons h Ξ hR
  case cmd =>
    intro C Γ Γc Δ Δ' L c Γ' hce hEqv Ξ hfe
    obtain ⟨Γce', hce', hfe_ce⟩ := CmdExtHasType_transport hfe hce
    exact ⟨Γce', .cmd _ _ _ _ _ _ _ _ hce' (TContext.Equiv.refl _),
      hfe_ce.trans hEqv.toFindEq.symm⟩
  case block =>
    intro C Γ Δ Cb Γb Δb L label body md Γ' hnotin _ hEqv ih Ξ hfe
    obtain ⟨Γb', hbody', _⟩ := ih Ξ hfe
    exact ⟨Ξ, .block _ _ _ _ _ _ _ _ _ _ _ hnotin hbody' (TContext.Equiv.refl _),
      hfe.trans hEqv.toFindEq.symm⟩
  case ite_det =>
    intro C Γ Δ Ct Γt Δt Ce Γe Δe L cond thenb elseb md Γ' hcond hcondAnn hcondScope _ _ hEqv
      iht ihe Ξ hfe
    obtain ⟨Γt', ht', _⟩ := iht Ξ hfe
    obtain ⟨Γe', he', _⟩ := ihe Ξ hfe
    exact ⟨Ξ, .ite_det _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (HasType_FindEq C _ _ _ _ hfe hcond)
      (writtenAnnotsOk_of_aliases_eq hfe.aliases hcondAnn) hcondScope ht' he'
      (TContext.Equiv.refl _), hfe.trans hEqv.toFindEq.symm⟩
  case ite_nondet =>
    intro C Γ Δ Ct Γt Δt Ce Γe Δe L thenb elseb md Γ' _ _ hEqv iht ihe Ξ hfe
    obtain ⟨Γt', ht', _⟩ := iht Ξ hfe
    obtain ⟨Γe', he', _⟩ := ihe Ξ hfe
    exact ⟨Ξ, .ite_nondet _ _ _ _ _ _ _ _ _ _ _ _ _ _ ht' he' (TContext.Equiv.refl _),
      hfe.trans hEqv.toFindEq.symm⟩
  case loop =>
    intro C Γ Δ Cb Γb Δb L guard measure invariants body md Γ' hg hgAnn hm hmAnn hinv hinvAnn
      hgS hmS hinvS _ hEqv ih Ξ hfe
    obtain ⟨Γb', hbody', _⟩ := ih Ξ hfe
    exact ⟨Ξ, .loop _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun g hgd => HasType_FindEq C _ _ _ _ hfe (hg g hgd))
      (fun g hgd => writtenAnnotsOk_of_aliases_eq hfe.aliases (hgAnn g hgd))
      (fun m hms => HasType_FindEq C _ _ _ _ hfe (hm m hms))
      (fun m hms => writtenAnnotsOk_of_aliases_eq hfe.aliases (hmAnn m hms))
      (fun p hp => HasType_FindEq C _ _ _ _ hfe (hinv p hp))
      (fun p hp => writtenAnnotsOk_of_aliases_eq hfe.aliases (hinvAnn p hp))
      hgS hmS hinvS hbody' (TContext.Equiv.refl _), hfe.trans hEqv.toFindEq.symm⟩
  case exit =>
    intro C Γ Δ L label md Γ' hmem hEqv Ξ hfe
    exact ⟨Ξ, .exit _ _ _ _ _ _ _ hmem (TContext.Equiv.refl _), hfe.trans hEqv.toFindEq.symm⟩
  case typeDecl =>
    intro C C' Γ Δ L tc md Γ' hprog hnotAlias hadd hEqv Ξ hfe
    exact ⟨Ξ, .typeDecl _ _ _ _ _ _ _ _ hprog
      (nameNotAlias_of_aliases_eq hfe.aliases hnotAlias) hadd (TContext.Equiv.refl _),
      hfe.trans hEqv.toFindEq.symm⟩
  case nil =>
    intro C Γ Δ L Γ' hEqv Ξ hfe
    exact ⟨Ξ, .nil _ _ _ _ _ (TContext.Equiv.refl _), hfe.trans hEqv.toFindEq.symm⟩
  case cons =>
    intro C C' C'' Γ Γ' Γ'' Δ Δ' Δ'' L s ss _ _ ihstmt ihtail Ξ hfe
    obtain ⟨Γs', hstmt', hfe_s⟩ := ihstmt Ξ hfe
    obtain ⟨Γt', htail', hfe_t⟩ := ihtail Γs' hfe_s
    exact ⟨Γt', .cons _ _ _ _ _ _ _ _ _ _ _ _ hstmt' htail', hfe_t⟩

end TypeSpec

namespace Statement

/-! ## The registered-type walk -/

/-- The annotations of `s`, outside its nested statement lists, use only type constructors
    registered in `ks`. -/
def ownTysDeclared (ks : Lambda.KnownTypes) (s : Statement) : Bool :=
  (stmtOwnAnnotTys s).all (LMonoTy.knownInstance · ks)

/-- The registrations in force after `s`, or `none` if `undeclaredTyUseStmt` rejects `s`. -/
def tysDeclaredStmt (ks : Lambda.KnownTypes) (s : Statement) : Option Lambda.KnownTypes :=
  (undeclaredTyUseStmt ks s).toOption

/-- The registrations in force after `ss`, or `none` if `undeclaredTyUseStmts` rejects `ss`. -/
def tysDeclaredStmts (ks : Lambda.KnownTypes) (ss : List Statement) : Option Lambda.KnownTypes :=
  (undeclaredTyUseStmts ks ss).toOption

/-- `unknownTysCons` finds no unregistered constructor in `ts` exactly when each of `ts` is a
    registered instance. -/
private theorem unknownTysCons_eq_nil_iff (ks : Lambda.KnownTypes) (ts : LMonoTys) :
    unknownTysCons ks ts = [] ↔ ts.all (fun t => LMonoTy.knownInstance t ks) = true := by
  rw [List.all_eq_true]
  constructor
  · intro hnil t ht
    rw [LMonoTy.knownInstance_iff_getTypeConsArities]
    intro ref href
    have hnot := List.filter_eq_nil_iff.mp (List.map_eq_nil_iff.mp hnil) ref
      (List.mem_flatMap.mpr ⟨t, ht, href⟩)
    cases hc : ks.contains { name := ref.1, metadata := ref.2 } with
    | true => rfl
    | false =>
      rw [hc] at hnot
      exact absurd rfl hnot
  · intro hall
    rw [unknownTysCons, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro ref href
    obtain ⟨t, ht, hreft⟩ := List.mem_flatMap.mp href
    rw [(LMonoTy.knownInstance_iff_getTypeConsArities ks t).mp (hall t ht) ref hreft]
    exact Bool.false_ne_true

/-- An optional expression's annotations all satisfy `p` exactly when every type
    `exprOrNondetAnnotTys` lists does. -/
private theorem allExprOrNondetTys_eq_all_exprOrNondetAnnotTys (p : LMonoTy → Bool)
    (e : ExprOrNondet Expression) :
    allExprOrNondetTys p e = (exprOrNondetAnnotTys e).all p := by
  cases e <;> simp only [allExprOrNondetTys, exprOrNondetAnnotTys, ExprOrNondet.toList,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, allExprTys_eq_all_exprAnnotTys,
    List.all_nil]

/-- A command's annotations all satisfy `p` exactly when every type `cmdAnnotTys` lists does. -/
theorem allCmdTys_eq_all_cmdAnnotTys (p : LMonoTy → Bool) (c : Command) :
    allCmdTys p c = (cmdAnnotTys c).all p := by
  cases c with
  | cmd cc =>
    cases cc with
    | init x ty e md =>
      cases ty
      cases e <;> simp only [allCmdTys, allLTyTys, allExprOrNondetTys, cmdAnnotTys, cmdCollect,
        CmdExt.initTypes, Cmd.initTypes, Statement.cmdTyArgs, cmdExprs, Cmd.readExprs,
        ExprOrNondet.toList, LTy.toMonoTypeUnsafe, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.singleton_append, List.all_cons, List.all_nil, allExprTys_eq_all_exprAnnotTys]
    | set x e md =>
      cases e <;> simp only [allCmdTys, allExprOrNondetTys, cmdAnnotTys, cmdCollect,
        CmdExt.initTypes, Cmd.initTypes, Statement.cmdTyArgs, cmdExprs, Cmd.readExprs,
        ExprOrNondet.toList, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.nil_append, List.all_nil, allExprTys_eq_all_exprAnnotTys]
    | assert l b md | assume l b md | cover l b md =>
      simp only [allCmdTys, cmdAnnotTys, cmdCollect, CmdExt.initTypes, Cmd.initTypes,
        Statement.cmdTyArgs, cmdExprs, Cmd.readExprs, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.nil_append, allExprTys_eq_all_exprAnnotTys]
  | call pname tyArgs args md =>
    have htys : (tyArgs.all (·.all (allLTyTys p))) =
        ((tyArgs.getD []).flatMap (fun ty => [ty.toMonoTypeUnsafe])).all p := by
      cases tyArgs with
      | none => rfl
      | some tys =>
        simp only [Option.all_some, Option.getD_some]
        induction tys with
        | nil => rfl
        | cons ty rest ih =>
          cases ty
          simp only [List.all_cons, List.flatMap_cons, List.singleton_append,
            LTy.toMonoTypeUnsafe, allLTyTys, ih]
    have hargs : (args.all fun
          | .inArg e => allExprTys p e
          | .inoutArg _ => true
          | .outArg _ => true) =
        ((CallArg.getInputExprs args).flatMap exprAnnotTys).all p := by
      induction args with
      | nil => rfl
      | cons a rest ih =>
        cases a <;> simp only [List.all_cons, CallArg.getInputExprs_cons_inArg,
          CallArg.getInputExprs_cons_inoutArg, CallArg.getInputExprs_cons_outArg,
          List.flatMap_cons, List.all_append, allExprTys_eq_all_exprAnnotTys,
          exprAnnotTys, Option.toList_none, List.all_nil, Bool.true_and] at ih ⊢ <;>
          simp only [ih]
    simp only [allCmdTys, cmdAnnotTys, cmdCollect, CmdExt.initTypes, Statement.cmdTyArgs,
      cmdExprs, List.flatMap_nil, List.nil_append, List.all_append]
    rw [htys]
    exact congrArg (_ && ·) hargs

/-- If every type annotation of a call satisfies `p`, then so does each stored type argument. -/
theorem allCmdTys_call_tyArgs {p : LMonoTy → Bool} {pname : String}
    {tyArgs : Option (List Expression.Ty)} {args : List (CallArg Expression)}
    {md : MetaData Expression}
    (h : allCmdTys p (.call pname tyArgs args md) = true) :
    ∀ tys, tyArgs = some tys → ∀ ty ∈ tys, p ty.toMonoTypeUnsafe = true := by
  intro tys htys ty hty
  subst htys
  simp only [allCmdTys, Bool.and_eq_true, Option.all_some, List.all_eq_true] at h
  have hty' := h.1 ty hty
  cases ty
  exact hty'

mutual

/-- A statement's annotations all satisfy `p` exactly when every type `stmtAnnotTys` lists
    does. -/
theorem allStmtTys_eq_all_stmtAnnotTys (p : LMonoTy → Bool) :
    (s : Statement) → allStmtTys p s = (stmtAnnotTys s).all p
  | .cmd c => by
    simp only [allStmtTys, stmtAnnotTys, stmtCollect, stmtOwnCollect, List.append_nil,
      allCmdTys_eq_all_cmdAnnotTys, cmdAnnotTys]
  | .block _ bss _ => by
    simp only [allStmtTys, stmtAnnotTys, stmtCollect, stmtOwnCollect, List.nil_append,
      allStmtsTys_eq_all_stmtsAnnotTys p bss, stmtsAnnotTys]
  | .ite cond tss ess _ => by
    simp only [allStmtTys, stmtAnnotTys, stmtCollect, stmtOwnCollect, List.all_append,
      Bool.and_assoc, allExprOrNondetTys_eq_all_exprOrNondetAnnotTys, exprOrNondetAnnotTys,
      allStmtsTys_eq_all_stmtsAnnotTys p tss, allStmtsTys_eq_all_stmtsAnnotTys p ess,
      stmtsAnnotTys]
  | .loop g m i bss _ => by
    simp only [allStmtTys, stmtAnnotTys, stmtCollect, stmtOwnCollect, List.all_append,
      List.all_flatMap, allExprOrNondetTys_eq_all_exprOrNondetAnnotTys, exprOrNondetAnnotTys,
      allStmtsTys_eq_all_stmtsAnnotTys p bss, stmtsAnnotTys,
      allExprTys_eq_all_exprAnnotTys, loopExprs, List.all_map]
    cases g <;> cases m <;> simp only [Option.all, Option.toList, List.all_cons,
      List.all_nil, Bool.and_true, Bool.true_and, allExprTys_eq_all_exprAnnotTys,
      ExprOrNondet.toList, Function.comp_def, Bool.and_assoc]
  | .exit _ _ | .typeDecl _ _ => by
    simp only [allStmtTys, stmtAnnotTys, stmtCollect, stmtOwnCollect, List.append_nil,
      List.all_nil]

/-- A statement list's annotations all satisfy `p` exactly when every type `stmtsAnnotTys`
    lists does. -/
theorem allStmtsTys_eq_all_stmtsAnnotTys (p : LMonoTy → Bool) :
    (ss : List Statement) → allStmtsTys p ss = (stmtsAnnotTys ss).all p
  | [] => by
    simp only [allStmtsTys, stmtsAnnotTys, stmtsCollect, List.all_nil]
  | s :: rest => by
    simp only [allStmtsTys, stmtsAnnotTys, stmtsCollect, List.all_append,
      allStmtTys_eq_all_stmtAnnotTys p s, allStmtsTys_eq_all_stmtsAnnotTys p rest, stmtAnnotTys]

end

/-- Turning a bind of `Except` computations into an option binds the options. -/
private theorem toOption_bind {ε α β : Type} (x : Except ε α) (f : α → Except ε β) :
    (x >>= f).toOption = x.toOption.bind fun a => (f a).toOption := by
  cases x <;> rfl

/-- `checkTysKnown` succeeds exactly when each of `tys` is a registered instance. -/
theorem checkTysKnown_toOption (ks : Lambda.KnownTypes) (tys : List LMonoTy)
    (msg : List String → String) :
    (checkTysKnown ks tys msg).toOption =
      if tys.all (fun t => LMonoTy.knownInstance t ks) then some () else none := by
  have hiff := unknownTysCons_eq_nil_iff ks tys
  unfold checkTysKnown
  split
  · rename_i hnil
    have hempty : unknownTysCons ks tys = [] := by
      cases hu : unknownTysCons ks tys with
      | nil => rfl
      | cons n ns => rw [hu, List.eraseDups_cons] at hnil; exact absurd hnil (by simp)
    rw [hiff.mp hempty]
    rfl
  · rename_i ns hne
    have hnonempty : unknownTysCons ks tys ≠ [] := by
      intro hu
      rw [hu] at hne
      exact hne rfl
    have hfalse : tys.all (fun t => LMonoTy.knownInstance t ks) = false := by
      cases hall : tys.all (fun t => LMonoTy.knownInstance t ks) with
      | false => rfl
      | true => exact absurd (hiff.mpr hall) hnonempty
    rw [hfalse]
    rfl

/-- `tysDeclaredStmt` fails when the statement's own annotations are not registered instances,
    and otherwise returns the registrations after the statement once its nested lists pass. -/
theorem tysDeclaredStmt_eq (ks : Lambda.KnownTypes) (s : Statement) :
    tysDeclaredStmt ks s =
      if !ownTysDeclared ks s then none
      else
        match s with
        | .typeDecl tc _ => some (ks.insert tc.name tc.numargs)
        | .block _ bss _ => do let _ ← tysDeclaredStmts ks bss; some ks
        | .ite _ tss ess _ => do
          let _ ← tysDeclaredStmts ks tss
          let _ ← tysDeclaredStmts ks ess
          some ks
        | .loop _ _ _ bss _ => do let _ ← tysDeclaredStmts ks bss; some ks
        | .cmd _ | .exit _ _ => some ks := by
  unfold ownTysDeclared
  unfold tysDeclaredStmt tysDeclaredStmts
  cases s with
  | cmd c =>
    rw [undeclaredTyUseStmt, toOption_bind, checkTysKnown_toOption]
    cases (stmtOwnAnnotTys _).all (fun t => LMonoTy.knownInstance t ks) <;> rfl
  | ite cond tss ess md =>
    rw [undeclaredTyUseStmt, toOption_bind, checkTysKnown_toOption]
    cases (stmtOwnAnnotTys _).all (fun t => LMonoTy.knownInstance t ks)
    · rfl
    · simp only [Bool.not_true, Bool.false_eq_true, reduceIte]
      cases undeclaredTyUseStmts ks tss <;> cases undeclaredTyUseStmts ks ess <;> rfl
  | loop g m i bss md =>
    rw [undeclaredTyUseStmt, toOption_bind, checkTysKnown_toOption]
    cases (stmtOwnAnnotTys _).all (fun t => LMonoTy.knownInstance t ks)
    · rfl
    · simp only [Bool.not_true, Bool.false_eq_true, reduceIte]
      cases undeclaredTyUseStmts ks bss <;> rfl
  | block label bss md =>
    rw [undeclaredTyUseStmt, toOption_bind]
    rfl
  | typeDecl | exit => rfl

/-- `tysDeclaredStmts` accepts the empty list without registering anything. -/
theorem tysDeclaredStmts_nil (ks : Lambda.KnownTypes) : tysDeclaredStmts ks [] = some ks := by
  unfold tysDeclaredStmts
  rw [undeclaredTyUseStmts]
  rfl

/-- `tysDeclaredStmts` checks the head and then the rest against the registrations after it. -/
theorem tysDeclaredStmts_cons (ks : Lambda.KnownTypes) (s : Statement) (rest : List Statement) :
    tysDeclaredStmts ks (s :: rest) =
      (do let ks ← tysDeclaredStmt ks s; tysDeclaredStmts ks rest) := by
  unfold tysDeclaredStmts tysDeclaredStmt
  rw [undeclaredTyUseStmts, toOption_bind]
  rfl

/-- A name was generated during a check exactly when it is the generator prefix followed by the
    decimal spelling of a counter value in the range the check advanced through. -/
theorem generatedDuring_iff (before after : TState) (key : TyIdentifier) :
    generatedDuring before after key = true ↔
      ∃ n ∈ List.range' before.tyGen (after.tyGen - before.tyGen),
        key = TState.tyPrefix ++ toString n := by
  constructor
  · intro h
    simp only [generatedDuring, Bool.and_eq_true] at h
    obtain ⟨hpre, hm⟩ := h
    rw [List.isPrefixOf_iff_prefix] at hpre
    obtain ⟨t, ht⟩ := hpre
    have hdrop : key.toList.drop TState.tyPrefix.toList.length = t := by
      rw [← ht, List.drop_left]
    rw [hdrop] at hm
    cases hp : listCharToNat? t with
    | none => rw [hp] at hm; exact absurd hm Bool.false_ne_true
    | some n =>
      rw [hp] at hm
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm
      obtain ⟨⟨hlo, hhi⟩, hts⟩ := hm
      refine ⟨n, ?_, ?_⟩
      · rw [List.mem_range'_1]
        exact ⟨hlo, by omega⟩
      · apply String.toList_injective
        rw [String.toList_append, hts, ht]
  · rintro ⟨n, hn, rfl⟩
    rw [List.mem_range'_1] at hn
    obtain ⟨hlo, hhi⟩ := hn
    have hl : (TState.tyPrefix ++ toString n).toList.drop TState.tyPrefix.toList.length
        = (toString n).toList := by
      rw [String.toList_append, List.drop_left]
    simp only [generatedDuring, hl, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      String.toList_isPrefixOf_toList_append, listCharToNat?_roundtrip]
    refine ⟨trivial, ⟨hlo, ?_⟩, trivial⟩
    omega

end Statement

section StatementTransport

open TypeSpec
open Strata.Util (HMaps)

/-! ### Statement typing across scopes, contexts and programs -/

/-- Statement typing with written type variables in scope preserves the ambient
    rigid-type-variable list. -/
theorem TypeSpec.StatementHasType.rigid_eq
    {P : Program} {C C' : LContext CoreLParams} {Γ Γ' : TContext Unit}
    {Δ Δ' : WrittenEnv} {L : List String} {s : Statement}
    (h : StatementHasType P C Γ Δ L s C' Γ' Δ') :
    C'.rigidTypeVars = C.rigidTypeVars := by
  cases h with
  | cmd | block | ite_det | ite_nondet | loop | exit => rfl
  | typeDecl =>
    rename_i hadd _
    exact addKnownTypeWithError_rigidTypeVars hadd

/-- `StatementsHasType` is invariant under changing the context's `idents` field. -/
theorem StatementsHasType_idents_irrel
    {P : Program} {Γ : TContext Unit} {Δ : WrittenEnv} {L : List String}
    {ss : List Statement} {Cin Cout : LContext CoreLParams} {Γout : TContext Unit}
    {Δout : WrittenEnv}
    (h : StatementsHasType P Cin Γ Δ L ss Cout Γout Δout) :
    ∀ (C : Expression.TyContext) (j : Identifiers Unit), Cin = { C with idents := j } →
      ∃ Cbase, Cout = { Cbase with idents := j } ∧
        StatementsHasType P C Γ Δ L ss Cbase Γout Δout := by
  refine StatementsHasType.rec
    (motive_1 := fun Cin Γ Δ L s Cout Γout Δout _ =>
      ∀ (C : Expression.TyContext) (j : Identifiers Unit), Cin = { C with idents := j } →
        ∃ Cbase, Cout = { Cbase with idents := j } ∧
          StatementHasType P C Γ Δ L s Cbase Γout Δout)
    (motive_2 := fun Cin Γ Δ L ss Cout Γout Δout _ =>
      ∀ (C : Expression.TyContext) (j : Identifiers Unit), Cin = { C with idents := j } →
        ∃ Cbase, Cout = { Cbase with idents := j } ∧
          StatementsHasType P C Γ Δ L ss Cbase Γout Δout)
    ?cmd ?block ?ite_det ?ite_nondet ?loop ?exit ?typeDecl ?nil ?cons h
  case cmd =>
    intro C0 Γ' Γc Δ Δ' L c Γ'' hce hEqv C j hCin
    subst hCin
    exact ⟨C, rfl, .cmd _ _ _ _ _ _ _ _ (CmdExtHasType_idents_irrel C P j Γ' c Γc hce) hEqv⟩
  case block =>
    intro C0 Γ' Δ Cb Γb Δb L label body md Γ'' hnotin _ hEqv ih C j hCin
    subst hCin
    obtain ⟨Cb', _, hbody'⟩ := ih C j rfl
    exact ⟨C, rfl, .block _ _ _ _ _ _ _ _ _ _ _ hnotin hbody' hEqv⟩
  case ite_det =>
    intro C0 Γ' Δ Ct Γt Δt Ce Γe Δe L cond thenb elseb md Γ'' hcond hcondAnn hcondScope _ _ hEqv
      iht ihe C j hCin
    subst hCin
    obtain ⟨Ct', _, hthen'⟩ := iht C j rfl
    obtain ⟨Ce', _, helse'⟩ := ihe C j rfl
    exact ⟨C, rfl, .ite_det _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (HasType_idents_irrel C j Γ' _ _ hcond)
      (writtenAnnotsOk_idents_irrel C j Γ' cond hcondAnn) hcondScope hthen'
      helse' hEqv⟩
  case ite_nondet =>
    intro C0 Γ' Δ Ct Γt Δt Ce Γe Δe L thenb elseb md Γ'' _ _ hEqv iht ihe C j hCin
    subst hCin
    obtain ⟨Ct', _, hthen'⟩ := iht C j rfl
    obtain ⟨Ce', _, helse'⟩ := ihe C j rfl
    exact ⟨C, rfl, .ite_nondet _ _ _ _ _ _ _ _ _ _ _ _ _ _ hthen' helse' hEqv⟩
  case loop =>
    intro C0 Γ' Δ Cb Γb Δb L guard measure invariants body md Γ'' hg hgAnn hm hmAnn hinv
      hinvAnn hgS hmS hiS _ hEqv ih C j hCin
    subst hCin
    obtain ⟨Cb', _, hbody'⟩ := ih C j rfl
    refine ⟨C, rfl, .loop _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ hgS hmS hiS hbody'
      hEqv⟩
    · intro g hgv; exact HasType_idents_irrel C j Γ' _ _ (hg g hgv)
    · intro g hgv; exact writtenAnnotsOk_idents_irrel C j Γ' g (hgAnn g hgv)
    · intro m hmv; exact HasType_idents_irrel C j Γ' _ _ (hm m hmv)
    · intro m hmv; exact writtenAnnotsOk_idents_irrel C j Γ' m (hmAnn m hmv)
    · intro pinv hp
      exact HasType_idents_irrel C j Γ' _ _ (hinv pinv hp)
    · intro pinv hp
      exact writtenAnnotsOk_idents_irrel C j Γ' pinv.2 (hinvAnn pinv hp)
  case exit =>
    intro C0 Γ' Δ L label md Γ'' hlabel hEqv C j hCin
    subst hCin
    exact ⟨C, rfl, .exit _ _ _ _ _ _ _ hlabel hEqv⟩
  case typeDecl =>
    intro C0 C' Γ' Δ L tc md Γ'' hprog hnotAlias haddk hEqv C j hCin
    subst hCin
    obtain ⟨haddk', hjeq⟩ := addKnownTypeWithError_setIdents C j
      { name := tc.name, metadata := tc.numargs } default C' haddk
    refine ⟨{ C' with idents := C.idents }, ?_,
      .typeDecl _ _ _ _ _ _ _ _ hprog hnotAlias haddk' hEqv⟩
    rw [← hjeq]
  case nil =>
    intro C0 Γ' Δ L Γ'' hEqv C j hCin
    subst hCin
    exact ⟨C, rfl, .nil _ _ _ _ _ hEqv⟩
  case cons =>
    intro C0 C' C'' Γ' Γ'' Γ''' Δ Δ' Δ'' L s ss _ _ ihs ihss C j hCin
    subst hCin
    obtain ⟨Cbase1, hCb1, hs'⟩ := ihs C j rfl
    obtain ⟨Cbase2, hCb2, hss'⟩ := ihss Cbase1 j hCb1
    exact ⟨Cbase2, hCb2, .cons _ _ _ _ _ _ _ _ _ _ _ _ hs' hss'⟩

/-! ### Variable scopes with the same lookups -/

/-- A `call` argument condition (a looked-up bare variable or a well-typed expression) carries
    over to scopes with the same lookups and a typing that the given one implies. -/
private theorem callInputMatch_mono {C C' : LContext CoreLParams} {ts ts' : TypeScopes}
    (hfind : ∀ x, ts'.find? x = ts.find? x) {mty : LMonoTy}
    (hexpr : ∀ e, ExprWellTyped C ts e mty → ExprWellTyped C' ts' e mty) (e : Expression.Expr)
    (h : match e with
      | .fvar _ x none => ts.find? x = some (.forAll [] mty)
      | e => ExprWellTyped C ts e mty) :
    match (generalizing := false) e with
    | .fvar _ x none => ts'.find? x = some (.forAll [] mty)
    | e => ExprWellTyped C' ts' e mty := by
  match e with
  | .fvar _ x none => exact (hfind x).trans h
  | .fvar _ _ (some _) | .const .. | .op .. | .bvar .. | .abs .. | .quant .. | .app .. | .ite ..
  | .eq .. => exact hexpr _ h

/-- An imperative command typed from variable scopes `ts` is typed from any scopes with the same
    lookups, ending in scopes with the same lookups as its original output. -/
private theorem TypeSpec.CmdWellTyped.of_findEq {C : LContext CoreLParams}
    {ts tsIn ts' : TypeScopes} {c : Cmd Expression} (h : CmdWellTyped C ts c ts')
    (hfind : ∀ x, tsIn.find? x = ts.find? x) :
    ∃ tsOut, CmdWellTyped C tsIn c tsOut ∧ ∀ x, tsOut.find? x = ts'.find? x := by
  cases h with
  | init_det x _ _ mty _ _ hnone hfv hxty hwk hexpr hEqv =>
    have hnone' : tsIn.find? x = none := (hfind x).trans hnone
    exact ⟨tsIn.insert x (.forAll [] mty), .init_det _ _ _ _ _ _ _ hnone' hfv hxty hwk
      (hexpr.of_find? hfind) (HMaps.Equiv.refl _),
      fun y => (HMaps.find?_insert_congr hfind x _ y).trans (hEqv.find? y).symm⟩
  | init_nondet x _ mty _ _ hnone hxty hwk hEqv =>
    have hnone' : tsIn.find? x = none := (hfind x).trans hnone
    exact ⟨tsIn.insert x (.forAll [] mty), .init_nondet _ _ _ _ _ _ hnone' hxty hwk
      (HMaps.Equiv.refl _),
      fun y => (HMaps.find?_insert_congr hfind x _ y).trans (hEqv.find? y).symm⟩
  | set_det x _ _ _ _ hx hexpr hEqv =>
    exact ⟨tsIn, .set_det _ _ _ _ _ _ ((hfind x).trans hx) (hexpr.of_find? hfind)
      (HMaps.Equiv.refl _), fun y => (hfind y).trans (hEqv.find? y).symm⟩
  | set_nondet x _ _ _ hx hEqv =>
    exact ⟨tsIn, .set_nondet _ _ _ _ _ ((hfind x).trans hx) (HMaps.Equiv.refl _),
      fun y => (hfind y).trans (hEqv.find? y).symm⟩
  | assert _ _ _ _ hexpr hEqv =>
    exact ⟨tsIn, .assert _ _ _ _ _ (hexpr.of_find? hfind) (HMaps.Equiv.refl _),
      fun y => (hfind y).trans (hEqv.find? y).symm⟩
  | assume _ _ _ _ hexpr hEqv =>
    exact ⟨tsIn, .assume _ _ _ _ _ (hexpr.of_find? hfind) (HMaps.Equiv.refl _),
      fun y => (hfind y).trans (hEqv.find? y).symm⟩
  | cover _ _ _ _ hexpr hEqv =>
    exact ⟨tsIn, .cover _ _ _ _ _ (hexpr.of_find? hfind) (HMaps.Equiv.refl _),
      fun y => (hfind y).trans (hEqv.find? y).symm⟩

/-- An extended command typed from variable scopes `ts` is typed from any scopes with the same
    lookups, ending in scopes with the same lookups as its original output. -/
private theorem TypeSpec.CmdExtWellTyped.of_findEq {C : LContext CoreLParams} {P : Program}
    {ts tsIn ts' : TypeScopes} {c : Command} (h : CmdExtWellTyped C P ts c ts')
    (hfind : ∀ x, tsIn.find? x = ts.find? x) :
    ∃ tsOut, CmdExtWellTyped C P tsIn c tsOut ∧ ∀ x, tsOut.find? x = ts'.find? x := by
  cases h with
  | cmd _ _ hc =>
    obtain ⟨tsOut, hc', hout⟩ := hc.of_findEq hfind
    exact ⟨tsOut, .cmd _ _ _ hc', hout⟩
  | call _ _ _ _ _ σ _ hpf hwf hlhs hargs hlhsTy hinst hkind hEqv =>
    refine ⟨tsIn, .call _ _ _ _ _ _ σ _ hpf hwf ?_ ?_ ?_ hinst hkind (HMaps.Equiv.refl _),
      fun y => (hfind y).trans (hEqv.find? y).symm⟩
    · intro v hv
      rw [hfind v]
      exact hlhs v hv
    · intro i hi hj
      exact callInputMatch_mono hfind (fun _ he => he.of_find? hfind) _ (hargs i hi hj)
    · intro i hi hj
      exact (hfind _).trans (hlhsTy i hi hj)

mutual

/-- A statement typed from variable scopes `ts` is typed from any scopes with the same lookups,
    ending in scopes with the same lookups as its original output. -/
theorem TypeSpec.StatementWellTyped.of_findEq {P : Program} {C C' : LContext CoreLParams}
    {ts tsIn ts' : TypeScopes} {L : List String} {s : Statement}
    (h : StatementWellTyped P C ts L s C' ts') (hfind : ∀ x, tsIn.find? x = ts.find? x) :
    ∃ tsOut, StatementWellTyped P C tsIn L s C' tsOut ∧ ∀ x, tsOut.find? x = ts'.find? x :=
  match h with
  | .cmd _ _ _ _ _ hc => by
    obtain ⟨tsOut, hc', hout⟩ := hc.of_findEq hfind
    exact ⟨tsOut, .cmd _ _ _ _ _ hc', hout⟩
  | .block _ _ _ _ _ _ _ _ _ hl hb hEqv => by
    obtain ⟨_, hb', -⟩ := TypeSpec.StatementsWellTyped.of_findEq hb hfind
    exact ⟨tsIn, .block _ _ _ _ _ _ _ _ _ hl hb' (HMaps.Equiv.refl _),
      fun y => (hfind y).trans (hEqv.find? y).symm⟩
  | .ite_det _ _ _ _ _ _ _ _ _ _ _ _ hc ht he hEqv => by
    obtain ⟨_, ht', -⟩ := TypeSpec.StatementsWellTyped.of_findEq ht hfind
    obtain ⟨_, he', -⟩ := TypeSpec.StatementsWellTyped.of_findEq he hfind
    exact ⟨tsIn, .ite_det _ _ _ _ _ _ _ _ _ _ _ _ (hc.of_find? hfind) ht' he'
      (HMaps.Equiv.refl _), fun y => (hfind y).trans (hEqv.find? y).symm⟩
  | .ite_nondet _ _ _ _ _ _ _ _ _ _ _ ht he hEqv => by
    obtain ⟨_, ht', -⟩ := TypeSpec.StatementsWellTyped.of_findEq ht hfind
    obtain ⟨_, he', -⟩ := TypeSpec.StatementsWellTyped.of_findEq he hfind
    exact ⟨tsIn, .ite_nondet _ _ _ _ _ _ _ _ _ _ _ ht' he' (HMaps.Equiv.refl _),
      fun y => (hfind y).trans (hEqv.find? y).symm⟩
  | .loop _ _ _ _ _ _ _ _ _ _ _ hg hm hi hb hEqv => by
    obtain ⟨_, hb', -⟩ := TypeSpec.StatementsWellTyped.of_findEq hb hfind
    exact ⟨tsIn, .loop _ _ _ _ _ _ _ _ _ _ _ (fun g hgd => (hg g hgd).of_find? hfind)
      (fun m hmd => (hm m hmd).of_find? hfind) (fun p hp => (hi p hp).of_find? hfind) hb'
      (HMaps.Equiv.refl _), fun y => (hfind y).trans (hEqv.find? y).symm⟩
  | .exit _ _ _ _ _ _ hl hEqv =>
    ⟨tsIn, .exit _ _ _ _ _ _ hl (HMaps.Equiv.refl _),
      fun y => (hfind y).trans (hEqv.find? y).symm⟩
  | .typeDecl _ _ _ _ _ _ _ hn hadd hEqv =>
    ⟨tsIn, .typeDecl _ _ _ _ _ _ _ hn hadd (HMaps.Equiv.refl _),
      fun y => (hfind y).trans (hEqv.find? y).symm⟩

/-- A statement list typed from variable scopes `ts` is typed from any scopes with the same
    lookups, ending in scopes with the same lookups as its original output. -/
theorem TypeSpec.StatementsWellTyped.of_findEq {P : Program} {C C' : LContext CoreLParams}
    {ts tsIn ts' : TypeScopes} {L : List String} {ss : List Statement}
    (h : StatementsWellTyped P C ts L ss C' ts') (hfind : ∀ x, tsIn.find? x = ts.find? x) :
    ∃ tsOut, StatementsWellTyped P C tsIn L ss C' tsOut ∧ ∀ x, tsOut.find? x = ts'.find? x :=
  match h with
  | .nil _ _ _ _ hEqv =>
    ⟨tsIn, .nil _ _ _ _ (HMaps.Equiv.refl _), fun y => (hfind y).trans (hEqv.find? y).symm⟩
  | .cons _ _ _ _ _ _ _ _ _ hs ht => by
    obtain ⟨tsM, hs', hm⟩ := TypeSpec.StatementWellTyped.of_findEq hs hfind
    obtain ⟨tsOut, ht', hout⟩ := TypeSpec.StatementsWellTyped.of_findEq ht hm
    exact ⟨tsOut, .cons _ _ _ _ _ _ _ _ _ hs' ht', hout⟩

end

/-! ### Changing the program and the identifier table -/

/-- A well-typed extended command stays well typed against a program giving every procedure it
    calls a signature with the same parameter names and every instantiation of the original. -/
private theorem TypeSpec.CmdExtWellTyped.program_congr_calls {C : LContext CoreLParams}
    {P1 P2 : Program}
    {ts ts' : TypeScopes} {c : Command}
    (hagree : ProcedureCallsRel ProcSigInstOf P1 P2 (CmdExt.calledProcedureNames c))
    (h : CmdExtWellTyped C P1 ts c ts') : CmdExtWellTyped C P2 ts c ts' := by
  cases h with
  | cmd _ _ hc => exact .cmd _ _ _ hc
  | call pname tyArgs callArgs proc md σ _ hpf hcall hlhs hin hout hinst hkind hEqv =>
    have hpmem : pname ∈ CmdExt.calledProcedureNames (.call pname tyArgs callArgs md) := by
      simp only [CmdExt.calledProcedureNames_call, List.mem_singleton]
    obtain ⟨proc2, hpf2, hsig⟩ := hagree pname hpmem proc hpf
    obtain ⟨σ2, hins, houts, htyArgs⟩ := hsig.inst σ
    refine .call _ pname tyArgs callArgs proc2 md σ2 _ hpf2
      (hcall.transfer (.boolConst Core.valueLoc true) hpf hpf2 hsig.inputsKeys hsig.outputsKeys rfl)
      hlhs ?_ ?_ ?_ hkind hEqv
    · intro i hi hj
      have hlen := congrArg List.length hins
      simp only [List.length_map] at hlen
      have hj1 : i < proc.header.inputs.values.length := hlen ▸ hj
      have hat := List.getElem_of_eq hins (by simpa only [List.length_map] using hj)
      simp only [List.getElem_map] at hat
      rw [hat]
      exact hin i hi hj1
    · intro i hi hj
      have hlen := congrArg List.length houts
      simp only [List.length_map] at hlen
      have hj1 : i < proc.header.outputs.values.length := hlen ▸ hj
      have hat := List.getElem_of_eq houts (by simpa only [List.length_map] using hj)
      simp only [List.getElem_map] at hat
      rw [hat]
      exact hout i hi hj1
    · have hmap := congrArg (List.map (fun t => Lambda.LTy.forAll [] t)) htyArgs
      simp only [List.map_map] at hmap
      rw [hinst]
      exact congrArg some hmap.symm

mutual

/-- A well-typed statement stays well typed against a program giving every procedure it calls a
    signature with every instantiation of the original's, and declaring only type names the
    original program declares. -/
theorem TypeSpec.StatementWellTyped.program_congr_calls {P1 P2 : Program}
    {C C' : LContext CoreLParams}
    {ts ts' : TypeScopes} {L : List String} {s : Statement}
    (hnames : ∀ n ∈ programNamesOfKind P2 .type, n ∈ programNamesOfKind P1 .type)
    (hagree : ProcedureCallsRel ProcSigInstOf P1 P2 (Statement.calledProcedureNames s))
    (h : StatementWellTyped P1 C ts L s C' ts') : StatementWellTyped P2 C ts L s C' ts' :=
  match h with
  | .cmd _ _ _ _ _ hc => by
    rw [Statement.calledProcedureNames_cmd] at hagree
    exact .cmd _ _ _ _ _ (TypeSpec.CmdExtWellTyped.program_congr_calls hagree hc)
  | .block _ _ _ _ _ _ _ _ _ hl hb hEqv => by
    rw [Statement.calledProcedureNames_block] at hagree
    exact .block _ _ _ _ _ _ _ _ _ hl
      (TypeSpec.StatementsWellTyped.program_congr_calls hnames hagree hb) hEqv
  | .ite_det _ _ _ _ _ _ _ _ _ _ _ _ hc ht he hEqv => by
    simp only [Statement.calledProcedureNames_ite] at hagree
    exact .ite_det _ _ _ _ _ _ _ _ _ _ _ _ hc
      (TypeSpec.StatementsWellTyped.program_congr_calls hnames hagree.append_left ht)
      (TypeSpec.StatementsWellTyped.program_congr_calls hnames hagree.append_right he) hEqv
  | .ite_nondet _ _ _ _ _ _ _ _ _ _ _ ht he hEqv => by
    simp only [Statement.calledProcedureNames_ite] at hagree
    exact .ite_nondet _ _ _ _ _ _ _ _ _ _ _
      (TypeSpec.StatementsWellTyped.program_congr_calls hnames hagree.append_left ht)
      (TypeSpec.StatementsWellTyped.program_congr_calls hnames hagree.append_right he) hEqv
  | .loop _ _ _ _ _ _ _ _ _ _ _ hg hm hi hb hEqv => by
    rw [Statement.calledProcedureNames_loop] at hagree
    exact .loop _ _ _ _ _ _ _ _ _ _ _ hg hm hi
      (TypeSpec.StatementsWellTyped.program_congr_calls hnames hagree hb) hEqv
  | .exit _ _ _ _ _ _ hl hEqv => .exit _ _ _ _ _ _ hl hEqv
  | .typeDecl _ _ _ _ _ _ _ hn hadd hEqv =>
    .typeDecl _ _ _ _ _ _ _ (fun n hn2 => hn n (hnames n hn2)) hadd hEqv

/-- A well-typed statement list stays well typed against a program giving every procedure it
    calls a signature with every instantiation of the original's, and declaring only type names
    the original program declares. -/
theorem TypeSpec.StatementsWellTyped.program_congr_calls {P1 P2 : Program}
    {C C' : LContext CoreLParams}
    {ts ts' : TypeScopes} {L : List String} {ss : List Statement}
    (hnames : ∀ n ∈ programNamesOfKind P2 .type, n ∈ programNamesOfKind P1 .type)
    (hagree : ProcedureCallsRel ProcSigInstOf P1 P2 (Statements.calledProcedureNames ss))
    (h : StatementsWellTyped P1 C ts L ss C' ts') : StatementsWellTyped P2 C ts L ss C' ts' :=
  match h with
  | .nil _ _ _ _ hEqv => .nil _ _ _ _ hEqv
  | .cons _ _ _ _ _ _ _ _ _ hs ht => by
    simp only [Statements.calledProcedureNames_cons] at hagree
    exact .cons _ _ _ _ _ _ _ _ _
      (TypeSpec.StatementWellTyped.program_congr_calls hnames hagree.append_left hs)
      (TypeSpec.StatementsWellTyped.program_congr_calls hnames hagree.append_right ht)

end

/-- Extended command well-typedness does not depend on the context's `idents` field. -/
private theorem TypeSpec.CmdExtWellTyped.withIdents {C : Expression.TyContext}
    {j : Identifiers Unit}
    {P : Program} {ts ts' : TypeScopes} {c : Command}
    (h : CmdExtWellTyped { C with idents := j } P ts c ts') : CmdExtWellTyped C P ts c ts' := by
  cases h with
  | cmd _ _ hc =>
    refine .cmd _ _ _ ?_
    cases hc with
    | init_det _ _ _ _ _ _ hnone hfv hxty hwk he hEqv =>
      exact .init_det _ _ _ _ _ _ _ hnone hfv hxty hwk he.withIdents hEqv
    | init_nondet _ _ _ _ _ hnone hxty hwk hEqv =>
      exact .init_nondet _ _ _ _ _ _ hnone hxty hwk hEqv
    | set_det _ _ _ _ _ hx he hEqv => exact .set_det _ _ _ _ _ _ hx he.withIdents hEqv
    | set_nondet _ _ _ _ hx hEqv => exact .set_nondet _ _ _ _ _ hx hEqv
    | assert _ _ _ _ he hEqv => exact .assert _ _ _ _ _ he.withIdents hEqv
    | assume _ _ _ _ he hEqv => exact .assume _ _ _ _ _ he.withIdents hEqv
    | cover _ _ _ _ he hEqv => exact .cover _ _ _ _ _ he.withIdents hEqv
  | call _ _ _ _ _ _ _ hpf hcall hlhs hin hout hinst hkind hEqv =>
    refine .call _ _ _ _ _ _ _ _ hpf hcall hlhs ?_ hout hinst ?_ hEqv
    · intro i hi hj
      exact callInputMatch_mono (fun _ => rfl) (fun _ he => he.withIdents) _ (hin i hi hj)
    · intro tys htys ty hty
      rw [← LContext.WellKindedTy_setIdents C j]
      exact hkind tys htys ty hty

mutual

/-- Statement well-typedness does not depend on the context's `idents` field: replacing it in
    the input context replaces it in the output context. -/
theorem TypeSpec.StatementWellTyped.withIdents {P : Program} {Cin Cout : LContext CoreLParams}
    {ts ts' : TypeScopes} {L : List String} {s : Statement}
    (h : StatementWellTyped P Cin ts L s Cout ts') :
    ∀ (C : Expression.TyContext) (j : Identifiers Unit), Cin = { C with idents := j } →
      ∃ Cbase, Cout = { Cbase with idents := j } ∧ StatementWellTyped P C ts L s Cbase ts' :=
  match h with
  | .cmd _ _ _ _ _ hc => fun C j hC => by
    subst hC
    exact ⟨C, rfl, .cmd _ _ _ _ _ hc.withIdents⟩
  | .block _ _ _ _ _ _ _ _ _ hl hb hEqv => fun C j hC => by
    obtain ⟨_, -, hb'⟩ := TypeSpec.StatementsWellTyped.withIdents hb C j hC
    subst hC
    exact ⟨C, rfl, .block _ _ _ _ _ _ _ _ _ hl hb' hEqv⟩
  | .ite_det _ _ _ _ _ _ _ _ _ _ _ _ hc ht he hEqv => fun C j hC => by
    obtain ⟨_, -, ht'⟩ := TypeSpec.StatementsWellTyped.withIdents ht C j hC
    obtain ⟨_, -, he'⟩ := TypeSpec.StatementsWellTyped.withIdents he C j hC
    subst hC
    exact ⟨C, rfl, .ite_det _ _ _ _ _ _ _ _ _ _ _ _ hc.withIdents ht' he' hEqv⟩
  | .ite_nondet _ _ _ _ _ _ _ _ _ _ _ ht he hEqv => fun C j hC => by
    obtain ⟨_, -, ht'⟩ := TypeSpec.StatementsWellTyped.withIdents ht C j hC
    obtain ⟨_, -, he'⟩ := TypeSpec.StatementsWellTyped.withIdents he C j hC
    subst hC
    exact ⟨C, rfl, .ite_nondet _ _ _ _ _ _ _ _ _ _ _ ht' he' hEqv⟩
  | .loop _ _ _ _ _ _ _ _ _ _ _ hg hm hi hb hEqv => fun C j hC => by
    obtain ⟨_, -, hb'⟩ := TypeSpec.StatementsWellTyped.withIdents hb C j hC
    subst hC
    exact ⟨C, rfl, .loop _ _ _ _ _ _ _ _ _ _ _ (fun g hgd => (hg g hgd).withIdents)
      (fun m hmd => (hm m hmd).withIdents) (fun p hp => (hi p hp).withIdents) hb' hEqv⟩
  | .exit _ _ _ _ _ _ hl hEqv => fun C j hC => by
    subst hC
    exact ⟨C, rfl, .exit _ _ _ _ _ _ hl hEqv⟩
  | .typeDecl _ C' _ _ _ _ _ hn hadd hEqv => fun C j hC => by
    subst hC
    obtain ⟨hadd', hjeq⟩ := addKnownTypeWithError_setIdents C j _ default C' hadd
    refine ⟨{ C' with idents := C.idents }, ?_, .typeDecl _ _ _ _ _ _ _ hn hadd' hEqv⟩
    rw [← hjeq]

/-- Statement-list well-typedness does not depend on the context's `idents` field: replacing it
    in the input context replaces it in the output context. -/
theorem TypeSpec.StatementsWellTyped.withIdents {P : Program} {Cin Cout : LContext CoreLParams}
    {ts ts' : TypeScopes} {L : List String} {ss : List Statement}
    (h : StatementsWellTyped P Cin ts L ss Cout ts') :
    ∀ (C : Expression.TyContext) (j : Identifiers Unit), Cin = { C with idents := j } →
      ∃ Cbase, Cout = { Cbase with idents := j } ∧ StatementsWellTyped P C ts L ss Cbase ts' :=
  match h with
  | .nil _ _ _ _ hEqv => fun C j hC => by
    subst hC
    exact ⟨C, rfl, .nil _ _ _ _ hEqv⟩
  | .cons _ _ _ _ _ _ _ _ _ hs ht => fun C j hC => by
    obtain ⟨Cm, hCm, hs'⟩ := TypeSpec.StatementWellTyped.withIdents hs C j hC
    obtain ⟨Co, hCo, ht'⟩ := TypeSpec.StatementsWellTyped.withIdents ht Cm j hCm
    exact ⟨Co, hCo, .cons _ _ _ _ _ _ _ _ _ hs' ht'⟩

end

end StatementTransport

end Core

end
