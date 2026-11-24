/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Soundness.Core
public import Strata.Languages.Core.Typing.Soundness.ProcedureAnnotRel
import all Strata.Languages.Core.Typing.Soundness.Core
import all Strata.Languages.Core.Typing.Soundness.ProcedureAnnotRel
import all Strata.Languages.Core.Axiom

/-! # Annotations of checked programs

`Core.typeCheck` returns each declaration of a program with its annotations changed: expressions
are elaborated, type parameters of functions, procedures and lemmas are renamed, signature and
datatype types are alias-resolved, the body of a type synonym is alias-resolved, and the declared
types of variable declarations are instantiated. `Core.typeCheck_annotRel` shows that this is all
the checker changes, and `Core.typeCheck_eraseAnnots` that the result erases to the same program. -/

namespace Core

open Lambda Imperative
open TypeSpec

public section

/-- The aliases in scope after a declaration of the checked program, given those before it: a
    type synonym adds the alias with its stored body. -/
def Decl.aliasesAfter (aliases : List TypeAlias) : Decl → List TypeAlias
  | .type (.syn ts) _ => { name := ts.name, typeArgs := ts.typeArgs, type := ts.type } :: aliases
  | _ => aliases

/-- All constructor argument types of a list of datatypes, in order. -/
def TypeDecl.constrTys (ds : List (LDatatype Unit)) : List LMonoTy :=
  ds.flatMap fun d => d.constrs.flatMap fun c => c.args.map Prod.snd

/-- `l'` is the checked form of the written lemma `l`: both erase to the same lemma, and the
    type parameters of `l'` are those of `l` with some reserved ones renamed to names the lemma
    does not mention. -/
def LemmaAnnotRel (l l' : Lemma) : Prop :=
  l'.eraseAnnots = l.eraseAnnots ∧
  ∃ ren : List (String × String),
    ReservedRenaming l.typeArgs l.mentionedTyVars ren ∧ l'.typeArgs = renameTyArgList ren l.typeArgs

/-- `d'` is the checked form of the written declaration `d`, checked with the aliases `aliases`
    in scope: both erase to the same declaration, and the types the erasure drops are related as
    follows. A synonym body and every datatype constructor argument type is alias-resolved. A
    lemma, function, recursive function block or procedure is related by its own relation. -/
def DeclAnnotRel (aliases : List TypeAlias) (d d' : Decl) : Prop :=
  d'.eraseAnnots = d.eraseAnnots ∧
  match d, d' with
  | .type (.syn ts) _, .type (.syn ts') _ => ts'.type = resolveTy aliases ts.type
  | .type (.data ds) _, .type (.data ds') _ =>
      TypeDecl.constrTys ds' = (TypeDecl.constrTys ds).map (resolveTy aliases)
  | .lemma l _, .lemma l' _ => LemmaAnnotRel l l'
  | .proc p _, .proc p' _ => ProcAnnotRel aliases p p'
  | .func f _, .func f' _ => FuncAnnotRel aliases f f'
  | .recFuncBlock fs _, .recFuncBlock fs' _ => List.Rel₂ (FuncAnnotRel aliases) fs fs'
  | .type (.con _) _, _ | .ax .., _ | .distinct .., _ => True
  | _, _ => False

/-- The declarations `ds'` are the checked forms of the written declarations `ds`, each related
    under the aliases that the synonyms before it in `ds'` declare, starting from `aliases`. -/
inductive DeclsAnnotRel : List TypeAlias → List Decl → List Decl → Prop where
  | nil (aliases : List TypeAlias) : DeclsAnnotRel aliases [] []
  | cons {aliases : List TypeAlias} {d d' : Decl} {ds ds' : List Decl} :
      DeclAnnotRel aliases d d' → DeclsAnnotRel (d'.aliasesAfter aliases) ds ds' →
      DeclsAnnotRel aliases (d :: ds) (d' :: ds')

/-- `P'` is the checked form of the written program `P`, checked with no alias in scope at the
    start. -/
def ProgramAnnotRel (P P' : Program) : Prop :=
  DeclsAnnotRel [] P.decls P'.decls

/-! ### Axioms, lemmas and distinct declarations -/

/-- A proposition `typeCheckProp` accepts is returned with the erasure of the written one. -/
private theorem typeCheckProp_eraseTypes {scope : Thunk (Std.HashSet String)} {kind : String}
    {name : CoreLabel} {typeArgs : List TyIdentifier} {C : Expression.TyContext}
    {Env Env' : Expression.TyEnv} {e e' : Expression.Expr} {tyNames : Unit → List String}
    (h : typeCheckProp scope kind name typeArgs C Env e tyNames = .ok (e', Env')) :
    e'.eraseTypes = e.eraseTypes := by
  unfold typeCheckProp at h
  simp only [bind, Except.bind] at h
  elim_err h with r hprop
  obtain ⟨out, stored, EnvR⟩ := r
  elim_err h with hstored
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨et, -, hresolve, rfl, -⟩ := Function.checkBoolProp_ok_inv (Except.mapError_ok_h' hprop)
  rw [eraseTypes_finishDeskolemized,
    SourceExpr.resolveWithType_unresolved_eraseTypes _ _ _ _ _ _ hresolve, eraseTypes_skolemizeBody]

/-- A checked lemma is the written lemma with its type parameters renamed and its proposition
    replaced by one with the same erasure. -/
private theorem Lemma.typeCheckIn_annotRel {scope : Thunk (Std.HashSet String)}
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {l l' : Lemma}
    (h : Lemma.typeCheckIn scope C Env l = .ok (l', Env')) : LemmaAnnotRel l l' := by
  obtain ⟨hnd, ⟨e', hl'⟩, hprop⟩ := Lemma.typeCheckIn_ok h
  subst hl'
  have he := typeCheckProp_eraseTypes hprop
  rw [Lemma.renameReservedTypeArgs_eq] at he ⊢
  have hres := reservedTypeArgsRenaming_reservedRenaming l.typeArgs l.mentionedTyVars
    (fun u => l.mentionedTyVarsIn (exprAnnotTys l.e) ++ scopeTyVars C Env) hnd
    (fun v hv => List.mem_append_left _ hv)
  generalize reservedTypeArgsRenaming l.typeArgs
    (fun u => l.mentionedTyVarsIn (exprAnnotTys l.e) ++ scopeTyVars C Env) = ren at he hres ⊢
  simp only [Lemma.renameTypeArgs, LExpr.eraseTypes_mapExprTys] at he
  refine ⟨?_, ren, hres, rfl⟩
  simp only [Lemma.eraseAnnots, Lemma.eraseTypes, Lemma.renameTypeArgs, renameTyArgList,
    List.map_map, Function.comp_def, he]

/-- Checked distinct expressions erase like the written ones. -/
private theorem Distinct.typeCheck_eraseTypes {C : Expression.TyContext}
    {Env Env' : Expression.TyEnv} {name : Expression.Ident} {es es' : List Expression.Expr}
    (h : Distinct.typeCheck C Env name es = .ok (es', Env')) :
    es'.map LExpr.eraseTypes = es.map LExpr.eraseTypes := by
  obtain ⟨ets, S, -, hres, -, rfl, -⟩ := Distinct.typeCheck_success C Env Env' name es _ h
  simp only [List.map_map, Function.comp_def, LExpr.eraseTypes_unresolved_applySubstT]
  exact SourceExpr.resolves_unresolved_eraseTypes C es Env ets Env' hres

/-! ### Type declarations -/

/-- Zipping the keys of a field list with its mapped types maps the types of the fields. -/
private theorem zip_map_snd {α β : Type} (f : β → β) :
    ∀ args : List (α × β),
      (args.map (·.1)).zip ((args.map (·.2)).map f) = args.map fun a => (a.1, f a.2)
  | [] => rfl
  | a :: rest => by simp only [List.map_cons, List.zip_cons_cons, zip_map_snd f rest]

/-- Alias resolution of the field list of a constructor resolves each field type and keeps the
    field names. -/
private theorem LConstrs.resolveAliases.go_eq
    {args args' : List (Identifier Unit × LMonoTy)} {Env Env2 : Expression.TyEnv}
    (h : LConstrs.resolveAliases.go args Env = .ok (args', Env2)) :
    args' = args.map fun a => (a.1, resolveTy Env.context.aliases a.2) := by
  simp only [LConstrs.resolveAliases.go, bind, Except.bind] at h
  elim_err h with v hv
  obtain ⟨tys', Env'⟩ := v
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  rw [TContext.resolveTys_of_resolveAliases (T := CoreLParams) hv, resolveTy_context]
  exact zip_map_snd _ args

/-- Alias resolution of a constructor list resolves the field types of each constructor. -/
private theorem LConstrs.resolveAliases_eq {cs cs' : List (LConstr Unit)}
    {Env Env2 : Expression.TyEnv} (h : LConstrs.resolveAliases cs Env = .ok (cs', Env2)) :
    cs' = cs.map fun c =>
      { c with args := c.args.map fun a => (a.1, resolveTy Env.context.aliases a.2) } := by
  induction cs generalizing cs' Env2 with
  | nil =>
    simp only [LConstrs.resolveAliases, List.foldrM_nil, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | cons c rest ih =>
    obtain ⟨acc, Envc, args', hrest, hgo, rfl⟩ := LConstrs.resolveAliases_cons_inv h
    rw [LConstrs.resolveAliases_env_eq rest Env acc Envc hrest] at hgo
    simp only [List.map_cons, LConstrs.resolveAliases.go_eq hgo, ih hrest]

/-- Alias resolution of a mutual datatype block keeps the erasure of every datatype and resolves
    every constructor field type. -/
private theorem MutualDatatype.resolveAliases_annotRel {block block_r : List (LDatatype Unit)}
    {Env Env2 : Expression.TyEnv}
    (h : MutualDatatype.resolveAliases block Env = .ok (block_r, Env2)) :
    block_r.map LDatatype.eraseAnnots = block.map LDatatype.eraseAnnots ∧
    TypeDecl.constrTys block_r =
      (TypeDecl.constrTys block).map (resolveTy Env.context.aliases) := by
  induction block generalizing block_r Env2 with
  | nil =>
    simp only [MutualDatatype.resolveAliases, List.foldrM_nil, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, rfl⟩
  | cons d rest ih =>
    obtain ⟨acc, Envd, constrs', d_r, hrest, hcon, rfl, hname, hta, hconstrs⟩ :=
      MutualDatatype.resolveAliases_cons_inv h
    obtain ⟨hera, hty⟩ := ih hrest
    rw [MutualDatatype.resolveAliases_env_eq rest acc Env Envd hrest] at hcon
    have hcs := LConstrs.resolveAliases_eq hcon
    rw [← hconstrs] at hcs
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, hera, List.cons.injEq, and_true]
      unfold LDatatype.eraseAnnots
      simp only [hname, hta, hcs, List.map_map, Function.comp_def]
    · simp only [TypeDecl.constrTys, List.flatMap_cons, List.map_append, hcs] at hty ⊢
      simp only [List.flatMap_map, Function.comp_def, List.map_flatMap, List.map_map, hty]

/-! ### One declaration step -/

/-- The continuation of a declaration step that returns the step's results. -/
private abbrev stepId : Decl → Expression.TyContext → Expression.TyEnv →
    Std.HashSet String →
    Except Strata.Message (Decl × Expression.TyContext × Expression.TyEnv × Std.HashSet String) :=
  fun d C E S => .ok (d, C, E, S)

/-- An accepted declaration step returns the checked form of the declaration, and the aliases of
    the resulting environment are those the checked declaration adds. -/
private theorem step_annotRel (program : Program) {PS : Thunk (Std.HashSet String)}
    {S S2 : Std.HashSet String} {C C2 : Expression.TyContext} {Env Env2 : Expression.TyEnv}
    {i : Identifiers Unit} {d d' : Decl} {C3 : LContext CoreLParams} {Ξ : TContext Unit}
    (hwf : LExpr.TEnvWF (T := CoreLParams) Env) (hfac : FactorySigWF C.functions)
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (hstep : DeclHasType program C Env.context d C3 Ξ)
    (hfe : TContext.FindEq (T := CoreLParams) Env2.context Ξ)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env d stepId
      = .ok (d', C2, Env2, S2)) :
    DeclAnnotRel Env.context.aliases d d' ∧
      Env2.context.aliases = d'.aliasesAfter Env.context.aliases := by
  cases d with
  | type td md =>
    cases td with
    | con tc =>
      obtain ⟨idents, ctx, -, -, -, hrec⟩ :=
        Program.typeCheck.stepThen_type_con_inversion program C Env i tc md stepId _ h
      simp only [stepId, Except.ok.injEq, Prod.mk.injEq] at hrec
      obtain ⟨rfl, -, rfl, -⟩ := hrec
      exact ⟨⟨rfl, trivial⟩, rfl⟩
    | syn ts =>
      obtain ⟨idents, v, storedTy, Env_ra, -, -, -, -, hres, haliases, -, -, hrec⟩ :=
        Program.typeCheck.stepThen_type_syn_inversion program C Env i ts md stepId _ h
      simp only [stepId, Except.ok.injEq, Prod.mk.injEq] at hrec
      obtain ⟨rfl, -, rfl, -⟩ := hrec
      refine ⟨⟨rfl, ?_⟩, haliases⟩
      show storedTy = _
      rw [TContext.resolveTy_of_resolveAliases (T := CoreLParams) hres, resolveTy_context]
    | data block =>
      obtain ⟨idents, block_r, C', -, hres, -, -, hrec⟩ :=
        Program.typeCheck.stepThen_type_data_inversion program C Env i block md stepId _ h
      simp only [stepId, Except.ok.injEq, Prod.mk.injEq] at hrec
      obtain ⟨rfl, -, rfl, -⟩ := hrec
      obtain ⟨hera, hty⟩ := MutualDatatype.resolveAliases_annotRel hres
      refine ⟨⟨?_, ?_⟩, rfl⟩
      · simp only [Decl.eraseAnnots, TypeDecl.eraseAnnots, hera]
      · show TypeDecl.constrTys block_r = _
        exact hty
  | ax a md =>
    obtain ⟨idents, d1, EnvA, -, hcheck, hrec⟩ :=
      Program.typeCheck.stepThen_prop_inversion program C Env i (.ax a md) stepId _ rfl h
    simp only [stepId, Except.ok.injEq, Prod.mk.injEq] at hrec
    obtain ⟨rfl, -, rfl, -⟩ := hrec
    obtain ⟨e', hax, -⟩ :=
      Decl.propCheck?_inv (d := .ax a md) (C := { C with idents := i }) (S := S) rfl hcheck
    obtain ⟨rfl, hcheckAx⟩ := hax a md rfl
    have he := typeCheckProp_eraseTypes hcheckAx
    cases hstep
    refine ⟨⟨?_, trivial⟩, hfe.aliases⟩
    simp only [Decl.eraseAnnots, Axiom.eraseTypes, he]
  | lemma l md =>
    obtain ⟨idents, d1, EnvA, -, hcheck, hrec⟩ :=
      Program.typeCheck.stepThen_prop_inversion program C Env i (.lemma l md) stepId _ rfl h
    simp only [stepId, Except.ok.injEq, Prod.mk.injEq] at hrec
    obtain ⟨rfl, -, rfl, -⟩ := hrec
    obtain ⟨e', -, hlem⟩ :=
      Decl.propCheck?_inv (d := .lemma l md) (C := { C with idents := i }) (S := S) rfl hcheck
    obtain ⟨l', rfl, -, hcheckLem⟩ := hlem l md rfl
    have hrel := Lemma.typeCheckIn_annotRel hcheckLem
    cases hstep
    exact ⟨⟨by simp only [Decl.eraseAnnots, hrel.1], hrel⟩, hfe.aliases⟩
  | distinct l es md =>
    obtain ⟨idents, es', EnvR, -, hcheck, hrec⟩ :=
      Program.typeCheck.stepThen_distinct_route program { C with idents := i } Env l es md stepId
        _ h
    simp only [stepId, Except.ok.injEq, Prod.mk.injEq] at hrec
    obtain ⟨rfl, -, rfl, -⟩ := hrec
    have he := Distinct.typeCheck_eraseTypes hcheck
    cases hstep
    exact ⟨⟨by simp only [Decl.eraseAnnots, he], trivial⟩, hfe.aliases⟩
  | proc p md =>
    obtain ⟨idents, p', Env3, htc, -, -, hrec⟩ :=
      Program.typeCheck.stepThen_proc_inversion program C Env i p md stepId _ h
    simp only [stepId, Except.ok.injEq, Prod.mk.injEq] at hrec
    obtain ⟨rfl, -, rfl, -⟩ := hrec
    have hcovP : ∀ n ∈ scopeTyNames { C with idents := idents } Env.pushEmptySubstScope,
        n ∈ (Thunk.pure S).get := by
      rw [scopeTyNames_setIdents]
      exact scopeTyNames_cover_of_context_eq (TEnv.pushEmptySubstScope_context_eq Env) hcov
    have hrel := Procedure.typeCheckIn_annotRel _ _ _ _ _ _ _ _ _ htc hcovP
      (pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env hwf) hfac
    rw [TEnv.pushEmptySubstScope_context_eq] at hrel
    cases hstep
    exact ⟨⟨by simp only [Decl.eraseAnnots, hrel.1], hrel⟩, hfe.aliases⟩
  | func f md =>
    obtain ⟨idents, renamed, f', -, -, -, htc, hrec⟩ :=
      WF.Program.typeCheck.stepThen_func_inversion program C Env i f md stepId _ h
    simp only [stepId, Except.ok.injEq, Prod.mk.injEq] at hrec
    obtain ⟨rfl, -, rfl, -⟩ := hrec
    have hrel := Function.typeCheckIn_annotRel htc
    rw [TEnv.pushEmptySubstScope_context_eq] at hrel
    exact ⟨⟨by simp only [Decl.eraseAnnots, hrel.1], hrel⟩, rfl⟩
  | recFuncBlock fs md =>
    obtain ⟨idents, fs', C', E', S', htc, -, -, -, hrec⟩ :=
      Program.typeCheck.stepThen_recFuncBlock_inversion program C Env i fs md stepId _ h
    simp only [stepId, Except.ok.injEq, Prod.mk.injEq] at hrec
    obtain ⟨rfl, -, rfl, -⟩ := hrec
    have hrel := RecFuncBlock.typeCheck_annotRel htc
    rw [TEnv.pushEmptySubstScope_context_eq] at hrel
    have hera : fs'.map Function.eraseAnnots = fs.map Function.eraseAnnots :=
      (List.Rel₂.map_eq (R := FuncAnnotRel Env.context.aliases) (f := Function.eraseAnnots)
        (g := Function.eraseAnnots) (fun _ _ hab => hab.1.symm) hrel).symm
    cases hstep
    exact ⟨⟨by simp only [Decl.eraseAnnots, hera], hrel⟩, hfe.aliases⟩

/-! ### The declaration walk -/

/-- A successful walk of the remaining declarations returns, after the declarations accumulated
    so far, the checked forms of the remaining ones, each related under the aliases in scope
    where it is checked. -/
private theorem goWith_annotRel (program : Program) (PS : Thunk (Std.HashSet String))
    (hsigs : ProcSigsDeclared program) (hP : ∀ n ∈ program.procSigTyNames, n ∈ PS.get) :
    ∀ (decls : List Decl) (S : Std.HashSet String) (C : Expression.TyContext)
      (Env : Expression.TyEnv) (i : Identifiers Unit) (acc out : Decls) (Env' : Expression.TyEnv),
      Program.typeCheck.goWith program PS S { C with idents := i } Env decls acc
        = .ok (out, Env') →
      (∀ n ∈ scopeTyNames C Env, n ∈ S) →
      TypeCheckLoopInvariant FactorySigWF C Env i →
      ∃ new, out = acc.reverse ++ new ∧ DeclsAnnotRel Env.context.aliases decls new := by
  intro decls
  induction decls with
  | nil =>
    intro S C Env i acc out Env' h _ _
    simp only [Program.typeCheck.goWith, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨[], List.append_nil _ |>.symm, DeclsAnnotRel.nil _⟩
  | cons d ds IH =>
    intro S C Env i acc out Env' h hcov hinv
    rw [Program.typeCheck.goWith] at h
    obtain ⟨i', C2, Env2, Ξ, d', hstep, hfe, hinv2, _, hrec, hdet⟩ :=
      decl_declHasType program C Env d _ _ i hsigs hP hinv hcov h
    obtain ⟨hrel, hal⟩ := step_annotRel program hinv.envWF hinv.factory hcov hstep hfe (hdet stepId)
    obtain ⟨new, hout, hrest⟩ := IH _ C2 Env2 i' (d' :: acc) out Env' hrec
      (Program.typeCheck.stepThen_next_cover program _ _ h hcov hdet) hinv2
    refine ⟨d' :: new, by simp only [hout, List.reverse_cons, List.append_assoc,
      List.singleton_append], DeclsAnnotRel.cons hrel ?_⟩
    rw [← hal]
    exact hrest

/-! ### Programs -/

/-- A program `Program.typeCheckIn` accepts in a well-formed ambient context, against a set `S`
    holding every type name in scope there, is returned with each declaration the checked form
    of the written one. -/
theorem Program.typeCheckIn_annotRel (S : Std.HashSet String)
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (program program' : Program)
    (h : Program.typeCheckIn S C Env program = .ok (program', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_coh : AliasRegistryCoherent C Env C.idents) (h_aliasBodies : AliasBodiesKnown C Env.context)
    (h_mono : MonoScope Env.context) :
    DeclsAnnotRel Env.context.aliases program.decls program'.decls := by
  obtain ⟨out, hgo, rfl⟩ := Program.typeCheckIn_ok_inv S C Env Env' program program' h
  obtain ⟨new, hout, hrel⟩ := goWith_annotRel program (procSigTyNameThunk program)
    (Program.typeCheck.goWith_procSigsDeclared hgo) (procSigTyNameThunk_cover program)
    program.decls S C (Program.typeCheck.startEnv Env) C.idents [] out Env' hgo
    (scopeTyNames_cover_of_context_eq (Program.typeCheck.startEnv_context Env) hcov)
    ⟨TEnv.updateSubst_globalScope_preserves_TEnvWF (T := CoreLParams) Env h_env, h_fac,
      (TEnv.updateSubst_checkContextTypesClosed (T := CoreLParams) Env _).trans h_closed,
      Program.typeCheck.startEnv_context Env ▸ h_aliasBodies,
      Program.typeCheck.startEnv_context Env ▸ h_mono,
      AliasRegistryCoherent.of_aliases_eq
        (congrArg (·.aliases) (Program.typeCheck.startEnv_context Env)) h_coh,
      AmbientClear.start Env⟩
  rw [Program.typeCheck.startEnv_context] at hrel
  simpa only [List.reverse_nil, List.nil_append, hout] using hrel

/-- A program `Program.typeCheck` accepts in a well-formed ambient context is returned with
    each declaration the checked form of the written one. -/
theorem Program.typeCheck_annotRel
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (program program' : Program)
    (h : Program.typeCheck C Env program = .ok (program', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_coh : AliasRegistryCoherent C Env C.idents) (h_aliasBodies : AliasBodiesKnown C Env.context)
    (h_mono : MonoScope Env.context) :
    DeclsAnnotRel Env.context.aliases program.decls program'.decls :=
  Program.typeCheckIn_annotRel _ C Env Env' program program' h (scopeTyNameThunk_cover C Env)
    h_env h_fac h_closed h_coh h_aliasBodies h_mono

/-- Related declaration lists erase to the same list. -/
private theorem DeclsAnnotRel.eraseAnnots_eq {aliases : List TypeAlias} {ds ds' : List Decl}
    (h : DeclsAnnotRel aliases ds ds') : ds'.map Decl.eraseAnnots = ds.map Decl.eraseAnnots := by
  induction h with
  | nil => rfl
  | cons hd _ ih => simp only [List.map_cons, hd.1, ih]

/-- The program `Core.typeCheck` returns is the checked form of the written program.

    A call's stored type arguments are not related to the written ones, which the checker
    ignores. They are the instance of the procedure's type parameters that `CmdExtWellTyped.call`
    fixes from the checked argument and result types (`Core.typeCheck_sound_output`), so those
    two theorems together determine them for every type parameter that occurs in the procedure's
    signature.

    Written binder and free-variable type annotations are not related to the checked ones here:
    erasure drops them, and this relation does not say that the checker keeps each written
    annotation up to aliases. -/
theorem typeCheck_annotRel
    (options : VerifyOptions) (program program' : Program)
    (factory : Option (Lambda.Factory CoreLParams)) (moreFns : Lambda.Factory CoreLParams)
    (h : Core.typeCheck options program factory moreFns = .ok program') :
    ProgramAnnotRel program program' := by
  obtain ⟨functions, S, Env', -, h_fac, -, hprog, hcov, -⟩ :=
    typeCheck_extraFunctions_inv options program program' factory moreFns h
  exact Program.typeCheckIn_annotRel S _ Lambda.TEnv.default Env' program program' hprog hcov
    (Lambda.LExpr.TEnvWF_default (T := CoreLParams)) h_fac
    (Lambda.LExpr.checkContextTypesClosed_default (T := CoreLParams))
    aliasRegistryCoherent_init aliasBodiesKnown_init monoScope_init

/-- The program `Core.typeCheck` returns erases to the same program as the written one. -/
theorem typeCheck_eraseAnnots
    (options : VerifyOptions) (program program' : Program)
    (factory : Option (Lambda.Factory CoreLParams)) (moreFns : Lambda.Factory CoreLParams)
    (h : Core.typeCheck options program factory moreFns = .ok program') :
    program'.eraseAnnots = program.eraseAnnots := by
  have hrel := (typeCheck_annotRel options program program' factory moreFns h).eraseAnnots_eq
  simp only [Program.eraseAnnots, hrel]

end

end Core
