/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Soundness.Statement
import all Strata.Languages.Core.Typing.Soundness.Command
import all Strata.Languages.Core.Typing.Soundness.Statement
import all Strata.Languages.Core.Typing.Props.StatementEraseProps
import all Strata.Languages.Core.StatementType
import all Strata.Languages.Core.WrittenTyVarScope
import all Strata.Languages.Core.TypeSkolem
import all Strata.Languages.Core.CmdType
import all Strata.DL.Lambda.LExprTypeSpec
import all Strata.DL.Lambda.LTyUnify
import all Strata.DL.Imperative.Cmd

/-! # Declared types of variable declarations after statement checking

The checker replaces the declared type of each `init` by the type it solved for. The main theorem
`Statement.typeCheck_initTyRel` shows that each checked declared type is an instance of the
written one, up to aliases. -/

namespace Core

open Lambda Imperative

public section

/-- `ty'` is the written type `ty` with its type variables instantiated, up to alias expansion. -/
def InitTyRel (aliases : List TypeAlias) (ty ty' : LMonoTy) : Prop :=
  ∃ S : Subst, AliasEquiv aliases (LMonoTy.subst S ty) ty'

/-- Instantiating the type variables of the declared type further keeps it an instance of the
    written type. -/
theorem InitTyRel.subst {A : List TypeAlias} {ty t : LMonoTy}
    (hwf : ∀ a ∈ A, TypeAlias.WF a) (S : Subst) (h : InitTyRel A ty t) :
    InitTyRel A ty (LMonoTy.subst S t) := by
  obtain ⟨S0, hS0⟩ := h
  obtain ⟨T, hT⟩ := LMonoTy.exists_subst_subst S S0 ty
  exact ⟨T, hT ▸ LExpr.AliasEquiv_subst A _ _ S hS0 hwf⟩

/-- A type that is an instance of an instance of the written type is an instance of the written
    type. -/
theorem InitTyRel.of_subst {A : List TypeAlias} {ty t : LMonoTy} (R : Subst)
    (h : InitTyRel A (LMonoTy.subst R ty) t) : InitTyRel A ty t := by
  obtain ⟨S0, hS0⟩ := h
  obtain ⟨T, hT⟩ := LMonoTy.exists_subst_subst S0 R ty
  exact ⟨T, hT ▸ hS0⟩

/-- A type alias-equivalent to the written type is an instance of it, by the empty
    substitution. -/
theorem InitTyRel.of_aliasEquiv {A : List TypeAlias} {ty t : LMonoTy}
    (h : AliasEquiv A ty t) : InitTyRel A ty t := by
  refine ⟨[], ?_⟩
  have hnil : LMonoTy.subst [] ty = ty := by
    simp only [LMonoTy.subst, Subst.hasEmptyScopes, List.all_nil, ite_true]
  rw [hnil]
  exact h

/-- The relation between the declared type of an `init` before checking and after: the checked
    type is a monotype that instantiates the written one, up to aliases. -/
def DeclTyRel (A : List TypeAlias) (ty ty' : LTy) : Prop :=
  ∃ t', ty' = .forAll [] t' ∧ InitTyRel A ty.toMonoTypeUnsafe t'

/-- Checking a command turns the declared type of an `init` into a monotype that instantiates the
    written one, up to the aliases of the input environment. -/
theorem Statement.typeCheckCmd_declTyRel
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program) (c c' : Command)
    (hwf : TContext.AliasesWF Env.context)
    (h : Statement.typeCheckCmd C Env P c = .ok (c', Env')) :
    List.Rel₂ (DeclTyRel Env.context.aliases) (CmdExt.initTypes c) (CmdExt.initTypes c') := by
  have hinit : ∀ {xty xtyP xtyQ : LTy} {E1 E3 E4 : TEnv Unit},
      CmdType.preprocess C Env xty = .ok (xtyP, E1) →
      CmdType.postprocess C E3 xtyP = .ok (xtyQ, E4) →
      DeclTyRel Env.context.aliases xty xtyQ := by
    intro xty xtyP xtyQ E1 E3 E4 hpre hpost
    obtain ⟨m0, r, rfl, rfl, -, hae, -⟩ := CmdType.preprocess_inv C Env E1 xty xtyP hpre
    refine ⟨_, (CmdType.postprocess_inv C _ _ _ _ hpost).1, ?_⟩
    exact InitTyRel.subst (TContext.AliasesWF.mem hwf) _ (InitTyRel.of_aliasEquiv hae)
  cases typeCheckCmd_ok_inv h with
  | cmd run hfun =>
    cases run with
    | initDet hlookup hself hpre hinfer hunify hpost =>
      exact List.Rel₂.cons (hinit hpre hpost) List.Rel₂.nil
    | initNondet hlookup hpre hpost =>
      exact List.Rel₂.cons (hinit hpre hpost) List.Rel₂.nil
    | setDet => exact List.Rel₂.nil
    | setNondet => exact List.Rel₂.nil
    | assert => exact List.Rel₂.nil
    | assume => exact List.Rel₂.nil
    | cover => exact List.Rel₂.nil
  | call => exact List.Rel₂.nil

/-- Applying a substitution to a command applies it to each declared type. -/
theorem Command.initTypes_subst (S : Subst) (c : Command) :
    CmdExt.initTypes (Statement.Command.subst S c) = (CmdExt.initTypes c).map (LTy.subst S) := by
  cases c with
  | cmd cc =>
    cases cc <;> simp only [Statement.Command.subst, Statement.Cmd.subst, CmdExt.initTypes,
      Cmd.initTypes, List.map_cons, List.map_nil]
  | call => rfl

/-- Mapping a command-wise rewrite that maps `F` over each command's declared types maps `F`
    over the declared types of the list. -/
theorem Block.initTypes_mapExpr (g : Expression.Expr → Expression.Expr) (mc : Command → Command)
    (F : LTy → LTy) (hmc : ∀ c, CmdExt.initTypes (mc c) = (CmdExt.initTypes c).map F)
    (ss : List Statement) :
    Block.initTypes (P := Expression) (C := Command) (Block.mapExpr g mc ss) =
      (Block.initTypes (P := Expression) (C := Command) ss).map F := by
  induction ss using Block.mapExpr.induct
    (motive1 := fun s => Stmt.initTypes (P := Expression) (C := Command) (Stmt.mapExpr g mc s) =
      (Stmt.initTypes (P := Expression) (C := Command) s).map F) <;>
    simp_all only [Stmt.mapExpr, Block.mapExpr, Stmt.initTypes, Block.initTypes,
      HasInitTypesImp.initTypes, List.map_append, List.map_nil]

/-- Applying a type substitution to each statement of a list applies it to each declared type. -/
private theorem Block.initTypes_map_subst (S : Subst) (ss : List Statement) :
    Block.initTypes (P := Expression) (C := Command) (ss.map (Statement.Statement.subst S)) =
      (Block.initTypes (P := Expression) (C := Command) ss).map (LTy.subst S) := by
  rw [map_subst_eq_mapExpr]
  exact Block.initTypes_mapExpr _ _ _ (Command.initTypes_subst S) ss

/-- Renaming the written type variables of a command replaces each declared type by an instance
    of it. -/
private theorem renameCmd_initTypes (rigid : List TyIdentifier) (m : WrittenTyVarScope.ScopeMap)
    (st : WrittenTyVarScope.ScopeState) (cmd : Command) :
    List.Rel₂ (fun (ty r : LTy) => ∃ R : Subst,
        r.toMonoTypeUnsafe = LMonoTy.subst R ty.toMonoTypeUnsafe)
      (CmdExt.initTypes cmd) (CmdExt.initTypes (WrittenTyVarScope.renameCmd rigid m st cmd).1) := by
  cases cmd with
  | cmd cc =>
    cases cc with
    | init x ty e md =>
      cases ty with
      | forAll xs t =>
        cases xs with
        | nil =>
          refine List.Rel₂.cons ?_ List.Rel₂.nil
          exact ⟨_, rfl⟩
        | cons a as =>
          refine List.Rel₂.cons ?_ List.Rel₂.nil
          exact ⟨[], by simp only [LMonoTy.subst, Subst.hasEmptyScopes, List.all_nil, ite_true]⟩
    | set x e md => exact List.Rel₂.nil
    | assert l e md => exact List.Rel₂.nil
    | assume l e md => exact List.Rel₂.nil
    | cover l e md => exact List.Rel₂.nil
  | call => exact List.Rel₂.nil

/-- Checking a renamed command relates each declared type of the written command to the checked
    one: the checked type is a monotype that instantiates the written one, up to the aliases of
    the input environment. -/
private theorem Statement.typeCheckCmd_renameCmd_declTyRel
    (C : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program) (cmd c' : Command)
    (rigid : List TyIdentifier) (m : WrittenTyVarScope.ScopeMap)
    (st : WrittenTyVarScope.ScopeState) (hwf : TContext.AliasesWF Env.context)
    (h : Statement.typeCheckCmd C Env P (WrittenTyVarScope.renameCmd rigid m st cmd).1
      = .ok (c', Env')) :
    List.Rel₂ (DeclTyRel Env.context.aliases) (CmdExt.initTypes cmd) (CmdExt.initTypes c') := by
  refine ((renameCmd_initTypes rigid m st cmd).comp
    (Statement.typeCheckCmd_declTyRel C Env Env' P _ c' hwf h)).imp ?_
  intro ty ty' ⟨r, ⟨R, hR⟩, ⟨t', ht', hrel⟩⟩
  refine ⟨t', ht', InitTyRel.of_subst R ?_⟩
  rw [← hR]
  exact hrel

open WrittenTyVarScope (ScopeMap ScopeState renameCmd)

/-- The declared types of a statement list. -/
private abbrev blockTys (ss : List Statement) : List LTy :=
  Block.initTypes (P := Expression) (C := Command) ss

/-- The declared types of a concatenation of statement lists are those of each list, in order. -/
private theorem blockTys_append (a b : List Statement) :
    blockTys (a ++ b) = blockTys a ++ blockTys b :=
  Block.initTypes_append a b

/-- The declared types of a statement list are those of its first statement followed by those of
    the rest. -/
private theorem blockTys_cons (s : Statement) (ss : List Statement) :
    blockTys (s :: ss) = Stmt.initTypes (P := Expression) (C := Command) s ++ blockTys ss :=
  rfl

/-- The declared types of an output list after emitting `s'` are those emitted before, those of
    `s'`, and those still to come. -/
private theorem blockTys_emit {acc out : List Statement} {s' : Statement} {X : List LTy}
    (hX : blockTys out = blockTys (s' :: acc).reverse ++ X) :
    blockTys out =
      blockTys acc.reverse ++ (Stmt.initTypes (P := Expression) (C := Command) s' ++ X) := by
  rw [hX, List.reverse_cons, blockTys_append]
  simp only [blockTys, Block.initTypes, List.append_nil, List.append_assoc]

/-- With nothing emitted, the declared types of the output are those that are still to come. -/
private theorem blockTys_of_nil_acc {out : List Statement} {X : List LTy}
    (hX : blockTys out = blockTys ([] : List Statement).reverse ++ X) : blockTys out = X := by
  rw [hX]
  rfl

/-- A relation between declared types that does not change when the alias list is rewritten to
    an equal one. -/
private theorem rel₂_of_aliases_eq {A A' : List TypeAlias} {l : List LTy} {X : List LTy}
    (hA : A = A') (h : List.Rel₂ (DeclTyRel A) l X) : List.Rel₂ (DeclTyRel A') l X := by
  subst hA
  exact h

/-- A successful statement walk turns the declared types of the statements it has yet to check
    into the declared types it appends to those already emitted, each an instance of the written
    one up to aliases. -/
private theorem go_declTyRel
    (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) (P : Program)
    (op : Option Procedure) (ss acc ss' : List Statement) (labels : List String)
    {m : ScopeMap} {st st' : ScopeState}
    (h : @Core.Statement.typeCheckAux.go P op C Env ss acc labels m st
      = .ok (ss', Env', C', st'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (h_ne : Env.context.types ≠ []) :
    ∃ X, blockTys ss' = blockTys acc.reverse ++ X ∧
      List.Rel₂ (DeclTyRel Env.context.aliases) (blockTys ss) X := by
  have hstep : ∀ (Env Eb : TEnv Unit) (bs : List Statement) (X : List LTy),
      EnvScopeStep Env Eb → LExpr.TEnvWF (T := CoreLParams) Env → Env.context.types ≠ [] →
      List.Rel₂ (DeclTyRel Eb.context.aliases) (blockTys bs) X →
      List.Rel₂ (DeclTyRel Env.context.aliases) (blockTys bs) X := by
    intro Env Eb bs X hR he hne hrel
    exact rel₂_of_aliases_eq (hR.facts he hne).1.2 hrel
  refine go_ok_induct
    (motive := fun C Env ss acc _ _ _ out _ _ _ => LExpr.TEnvWF (T := CoreLParams) Env →
      FactorySigWF C.functions → Env.context.types ≠ [] →
      ∃ X, blockTys out = blockTys acc.reverse ++ X ∧
        List.Rel₂ (DeclTyRel Env.context.aliases) (blockTys ss) X)
    (motiveB := fun C Env ss acc _ _ _ out _ _ _ => LExpr.TEnvWF (T := CoreLParams) Env →
      FactorySigWF C.functions → Env.context.types ≠ [] →
      ∃ X, blockTys out = blockTys acc.reverse ++ X ∧
        List.Rel₂ (DeclTyRel Env.context.aliases) (blockTys ss) X)
    ?nil ?cmd ?block ?ite ?loop ?exit ?typeDecl ?blockScope ?blockFlat C Env ss acc labels ss'
    Env' C' h he hf h_ne
  case nil =>
    intro _ _ _ _ _ _ _ _ _
    exact ⟨[], by simp only [List.append_nil], List.Rel₂.nil⟩
  case cmd =>
    intro C Env acc labels m st srest cmd c' Env1 ss' Env' C' st' htc _ _ ih he hf h_ne
    have hwf1 := Statement.typeCheckCmd_preserves_TEnvWF C Env Env1 P _ c' htc he hf
    obtain ⟨X, hX, hrel⟩ := ih hwf1 hf
      (Statement.typeCheckCmd_preserves_context_types_ne C Env Env1 P _ c' htc h_ne)
    have hal : Env1.context.aliases = Env.context.aliases :=
      (Statement.typeCheckCmd_preserves_context C Env Env1 P _ c' htc).2
    have hcmd := Statement.typeCheckCmd_renameCmd_declTyRel C Env Env1 P cmd c' _ m st
      he.aliasesWF htc
    refine ⟨CmdExt.initTypes c' ++ X, blockTys_emit hX, ?_⟩
    rw [blockTys_cons]
    exact List.Rel₂.append hcmd (rel₂_of_aliases_eq hal hrel)
  case block =>
    intro C Env acc labels m st srest label bss md bss' Eb stb ss' Env' C' st' _ hgb ihb _ ih
      he hf h_ne
    obtain ⟨Xb, hXb, hrelb⟩ := ihb he hf h_ne
    obtain ⟨-, hwfb, hneb⟩ := (EnvScopeStep.of_goBlock hgb hf).facts he h_ne
    obtain ⟨X, hX, hrel⟩ := ih hwfb hf hneb
    refine ⟨Xb ++ X, ?_, ?_⟩
    · have hemit := blockTys_emit hX
      rw [hemit]
      simp only [Stmt.initTypes]
      have hb : Block.initTypes (P := Expression) (C := Command) bss' = Xb :=
        blockTys_of_nil_acc hXb
      rw [hb]
    · rw [blockTys_cons]
      exact List.Rel₂.append hrelb
        (hstep Env Eb srest X (EnvScopeStep.of_goBlock hgb hf) he h_ne hrel)
  case ite =>
    intro C Env acc labels m st srest cond tss ess md condElab Ec tss' Et stt ess' Ee ste ss'
      Env' C' st' hcond _ hgt iht hge ihe _ ih he hf h_ne
    have hEc : EnvScopeStep Env Ec := hcond.chain.scope hf
    have hEt : EnvScopeStep Env Et := hEc.trans (EnvScopeStep.of_goBlock hgt hf)
    have hEe : EnvScopeStep Env Ee := hEt.trans (EnvScopeStep.of_goBlock hge hf)
    obtain ⟨-, hwfc, hnec⟩ := hEc.facts he h_ne
    obtain ⟨-, hwft, hnet⟩ := hEt.facts he h_ne
    obtain ⟨-, hwfe, hnee⟩ := hEe.facts he h_ne
    obtain ⟨Xt, hXt, hrelt⟩ := iht hwfc hf hnec
    obtain ⟨Xe, hXe, hrele⟩ := ihe hwft hf hnet
    obtain ⟨X, hX, hrel⟩ := ih hwfe hf hnee
    refine ⟨Xt ++ (Xe ++ X), ?_, ?_⟩
    · rw [blockTys_emit hX]
      simp only [Stmt.initTypes]
      have ht : Block.initTypes (P := Expression) (C := Command) tss' = Xt :=
        blockTys_of_nil_acc hXt
      have he' : Block.initTypes (P := Expression) (C := Command) ess' = Xe :=
        blockTys_of_nil_acc hXe
      rw [ht, he', List.append_assoc]
    · rw [blockTys_cons]
      simp only [Stmt.initTypes, List.append_assoc]
      exact List.Rel₂.append (hstep Env Ec tss Xt hEc he h_ne hrelt)
        (List.Rel₂.append (hstep Env Et ess Xe hEt he h_ne hrele)
          (hstep Env Ee srest X hEe he h_ne hrel))
  case loop =>
    intro C Env acc labels m st srest guard measure invariant bss md guardElab Eg measureElab Em
      invElab Efold bss' Eb stb ss' Env' C' st' hg hm hi _ hgb ihb _ ih he hf h_ne
    have hEfold : EnvScopeStep Env Efold := (loopHead_chain hg hm hi).scope hf
    have hEb : EnvScopeStep Env Eb := hEfold.trans (EnvScopeStep.of_goBlock hgb hf)
    obtain ⟨-, hwff, hnef⟩ := hEfold.facts he h_ne
    obtain ⟨-, hwfb, hneb⟩ := hEb.facts he h_ne
    obtain ⟨Xb, hXb, hrelb⟩ := ihb hwff hf hnef
    obtain ⟨X, hX, hrel⟩ := ih hwfb hf hneb
    refine ⟨Xb ++ X, ?_, ?_⟩
    · rw [blockTys_emit hX]
      simp only [Stmt.initTypes]
      have hb : Block.initTypes (P := Expression) (C := Command) bss' = Xb :=
        blockTys_of_nil_acc hXb
      rw [hb]
    · rw [blockTys_cons]
      simp only [Stmt.initTypes]
      exact List.Rel₂.append (hstep Env Efold bss Xb hEfold he h_ne hrelb)
        (hstep Env Eb srest X hEb he h_ne hrel)
  case exit =>
    intro C Env acc labels m st srest l md ss' Env' C' st' _ _ _ ih he hf h_ne
    obtain ⟨X, hX, hrel⟩ := ih he hf h_ne
    exact ⟨X, by simpa only [Stmt.initTypes, List.nil_append] using blockTys_emit hX, hrel⟩
  case typeDecl =>
    intro C Env acc labels m st srest tc md Cnew ss' Env' C' st' htc _ ih he hf h_ne
    obtain ⟨X, hX, hrel⟩ := ih he (TypeConstructor.typeCheck_functions_eq htc ▸ hf) h_ne
    exact ⟨X, by simpa only [Stmt.initTypes, List.nil_append] using blockTys_emit hX, hrel⟩
  case blockScope =>
    intro C Env bss acc labels m st ss' Ego Cgo st' _ ih he hf _
    obtain ⟨X, hX, hrel⟩ := ih (pushEmptyContext_preserves_TEnvWF (T := CoreLParams) Env he) hf
      (TEnv.pushEmptyContext_types_ne_nil (T := CoreLParams) Env)
    refine ⟨X, hX, rel₂_of_aliases_eq ?_ hrel⟩
    simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context]
  case blockFlat => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ih

/-- Applying a substitution to declared types that instantiate the written ones keeps them
    instances of the written ones. -/
private theorem rel₂_declTyRel_subst {A : List TypeAlias} (hwf : ∀ a ∈ A, TypeAlias.WF a)
    (S : Subst) {l X : List LTy} (h : List.Rel₂ (DeclTyRel A) l X) :
    List.Rel₂ (InitTyRel A) (l.map LTy.toMonoTypeUnsafe)
      ((X.map (LTy.subst S)).map LTy.toMonoTypeUnsafe) := by
  induction h with
  | nil => exact List.Rel₂.nil
  | cons hhd _ ih =>
    obtain ⟨t', rfl, hrel⟩ := hhd
    exact List.Rel₂.cons (InitTyRel.subst hwf S hrel) ih

/-- Statement checking turns each declared type into an instance of the written one, up to the
    aliases of the input environment. -/
theorem Statement.typeCheck_initTyRel
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (P : Program)
    (op : Option Procedure) (ss ss' : List Statement)
    (h : Statement.typeCheck C Env P op ss = .ok (ss', Env'))
    (he : LExpr.TEnvWF (T := CoreLParams) Env) (hf : FactorySigWF C.functions)
    (hne : Env.context.types ≠ []) :
    List.Rel₂ (InitTyRel Env.context.aliases) (Statements.initTys ss) (Statements.initTys ss') := by
  obtain ⟨ssA, E1, C1, hr, rfl, -, -⟩ :=
    Statement.typeCheck_ok_inv C Env Env' P op ss ss' h
  obtain ⟨_, hgo⟩ := typeCheckAux_ok_inv hr
  obtain ⟨X, hX, hrel⟩ := go_declTyRel C C1 Env E1 P op ss [] ssA [] hgo he hf hne
  rw [Statement_subst_go_eq, List.reverse_nil, List.nil_append]
  unfold Statements.initTys
  rw [Block.initTypes_map_subst]
  rw [show Block.initTypes (P := Expression) (C := Command) ssA = X from blockTys_of_nil_acc hX]
  exact rel₂_declTyRel_subst (TContext.AliasesWF.mem he.aliasesWF) _ hrel

end

end Core
