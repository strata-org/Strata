/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.TypingSpec
public import Strata.Languages.Core.Typing.Spec.StatementTypeSpec
public import Strata.Languages.Core.CallWFProps
public import Strata.Languages.Core.InstExprTyping
import all Strata.DL.Lambda.LExprTypeSpec
import all Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.LExprTypeEnvProps
import Strata.Languages.Core.ProcedureProps
import Strata.Languages.Core.ProgramProps
import Strata.Languages.Core.IdentifiersProps
import all Strata.Languages.Core.Statement
import all Strata.Languages.Core.Procedure
import all Strata.Languages.Core.Program
import all Strata.DL.Imperative.Procedure
import all Strata.Languages.Core.Typing.Spec.CmdTypeSpec
import all Strata.Languages.Core.Typing.Spec.TypeSpecShared
import Strata.Languages.Core.StatementProps
import Strata.DL.Lambda.LTyProps
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.DL.Lambda.LExprWFProps
import Strata.DL.Lambda.Denote.LExprAnnotatedProps
import all Strata.DL.Lambda.Denote.LExprDenoteTySubst
import Strata.DL.Lambda.LTyUnifyProps
import Strata.DL.Lambda.FactoryProps
import Strata.Languages.Core.ExpressionsProps

/-! ## Properties of the typechecker spec and of well-typedness

A well-typed program with structured bodies has well-formed calls:
`ProgramWellTyped.callsWellFormed`. The `withRigid` theorems, such as
`StatementsWellTyped.withRigid`, say well-typedness ignores the context's rigid type
variables.

Further key results:
* `TypeScopes.instVarTyping_of_find?`, `TypeScopes.instVarTyping_of_equiv`: the variable typing
  of scopes with a type substitution applied to every declared type, and its agreement with the
  scopes' declarations.
* The `scopeExtends` theorems (for base and extended commands, statements and statement lists)
  say well-typed code ends in scopes that keep every declaration it started with.
* `ProgramWellTyped.procWellTyped`: a procedure declared in a well-typed program is well typed.
* The `allDeclTys_mono` theorems say well-typed code declares variables, and instantiates calls,
  only at monotypes; `StatementsWellTyped.initTypes_mono` says every variable it declares has a
  monotype, and `ProcWellTyped.initTypesMono` says the same for a well-typed procedure with a
  structured body.
  `ProcWellTyped.declTysScoped` says the type variables of its local declarations and call type
  arguments are type parameters of the procedure.
* `procBodyScopes_find?_some`, `procBodyScopes_find?_none`: which names a procedure's body scope
  binds, and at which types. `procBodyScopes_inst`: the body scope of an instance of a procedure
  is that of the procedure with the type arguments substituted.
* `storeHasTyping_of_equiv`, `storeFresh_of_equiv`: stores conform to equivalent scopes alike.
  `TypeScopes.storeFresh_instVarTyping`: instantiating the scopes does not change which
  variables are declared.
* `ExprWellTyped.hasType_inst`, `exprWellTyped_eval_progress_inst`, `eval_bool_progress_inst`,
  `exprWellTyped_varsDefined_inst`: a well-typed expression, with a type substitution applied,
  has a declarative type, evaluates, and has its free variables bound, in a store that
  conforms to the scopes with the substitution applied. -/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative
open Strata.Util (HMaps)

public section

/-! ### Variable typings of scopes -/

/-- Instantiating by the empty substitution leaves the variable typing unchanged. -/
theorem TypeScopes.instVarTyping_empty (ts : TypeScopes) :
    ts.instVarTyping Subst.empty = ts.find? := by
  funext x
  simp only [TypeScopes.instVarTyping]
  cases hx : ts.find? x with
  | none => rfl
  | some ty =>
    cases ty
    simp only [Option.map_some, mapLTyTys, Subst.empty, LMonoTy.subst_nil]

/-- A declared variable has its declared type with the substitution applied. -/
theorem TypeScopes.instVarTyping_of_find? {S : Subst} {ts : TypeScopes} {x : Expression.Ident}
    {ty : LTy} (h : ts.find? x = some ty) :
    ts.instVarTyping S x = some (mapLTyTys (LMonoTy.subst S) ty) := by
  simp only [TypeScopes.instVarTyping, h, Option.map_some]

/-- Equivalent scopes give the same instantiated variable typing. -/
theorem TypeScopes.instVarTyping_of_equiv {S : Subst} {ts ts' : TypeScopes}
    (h : HMaps.Equiv ts' ts) : ts'.instVarTyping S = ts.instVarTyping S := by
  funext x
  simp only [TypeScopes.instVarTyping, HMaps.Equiv.find? h x]

/-- Scopes equivalent to `ts` with `x` inserted at the monotype `mty` give the instantiated
    typing of `ts`, except that `x` has the type `mty` with the substitution applied. -/
theorem TypeScopes.instVarTyping_insert {S : Subst} {ts ts' : TypeScopes}
    {x : Expression.Ident} {mty : LMonoTy}
    (hequiv : HMaps.Equiv ts' (ts.insert x (.forAll [] mty))) :
    ts'.instVarTyping S = fun y =>
      if y = x then some (.forAll [] (LMonoTy.subst S mty)) else ts.instVarTyping S y := by
  funext y
  rw [TypeScopes.instVarTyping_of_equiv hequiv]
  by_cases hyx : y = x
  · subst hyx
    simp only [TypeScopes.instVarTyping, HMaps.find?_insert_self, Option.map_some, mapLTyTys,
      ite_true]
  · simp only [TypeScopes.instVarTyping, HMaps.find?_insert_ne ts y x _ hyx, hyx, ite_false]

/-- A store binds nothing outside the instantiated variable typing of scopes exactly when it
    binds nothing outside the scopes: instantiation does not change which variables are
    declared. -/
theorem TypeScopes.storeFresh_instVarTyping {σ : CoreStore} {S : Subst} {ts : TypeScopes} :
    StoreFresh σ (ts.instVarTyping S) ↔ StoreFresh σ ts.find? := by
  constructor
  · intro h x hx
    apply h x
    simp only [TypeScopes.instVarTyping, Option.map_eq_none_iff]
    exact hx
  · intro h x hx
    apply h x
    simp only [TypeScopes.instVarTyping, Option.map_eq_none_iff] at hx
    exact hx

/-- A store that conforms to scopes also conforms to equivalent scopes. -/
theorem storeHasTyping_of_equiv {F : Expression.Factory} {S : Subst} {σ : CoreStore}
    {ts ts' : TypeScopes}
    (hequiv : HMaps.Equiv ts' ts) (hs : StoreHasTyping F σ (ts.instVarTyping S)) :
    StoreHasTyping F σ (ts'.instVarTyping S) := by
  rw [TypeScopes.instVarTyping_of_equiv hequiv]
  exact hs

/-- A store that binds nothing outside some scopes binds nothing outside equivalent scopes. -/
theorem storeFresh_of_equiv {σ : CoreStore} {ts ts' : TypeScopes}
    (hequiv : HMaps.Equiv ts' ts) (hs : StoreFresh σ ts.find?) :
    StoreFresh σ ts'.find? := by
  intro x hx
  have hx' : ts'.find? x = none := hx
  have hfind : ts.find? x = none := by
    rw [← HMaps.Equiv.find? hequiv x]
    exact hx'
  exact hs x hfind

/-! ### Typing does not read the rigid type variables -/

/-- Expression typing does not read the rigid type variables of the context. -/
private theorem exprWellTyped_withRigid (C : LContext CoreLParams)
    (r : List TyIdentifier) :
    ExprWellTyped { C with rigidTypeVars := r } = ExprWellTyped C := by
  funext ts e mty
  exact propext
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.fvarsDeclared, h.2.2.opsInstantiate,
      h.2.2.opsKnown⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.fvarsDeclared, h.2.2.opsInstantiate,
      h.2.2.opsKnown⟩⟩

/-- Imperative command typing does not read the rigid type variables of the
    context. -/
private theorem CmdWellTyped.withRigid {C : LContext CoreLParams}
    {ts ts' : TypeScopes} {c : Cmd Expression} (r : List TyIdentifier)
    (h : CmdWellTyped C ts c ts') :
    CmdWellTyped { C with rigidTypeVars := r } ts c ts' := by
  cases h <;> constructor <;>
    first
      | assumption
      | exact exprWellTyped_withRigid C r ▸ ‹ExprWellTyped C _ _ _›

/-- Extended command typing does not read the rigid type variables of the
    context. -/
private theorem CmdExtWellTyped.withRigid {C : LContext CoreLParams}
    {P : Program} {ts ts' : TypeScopes} {c : Command} (r : List TyIdentifier)
    (h : CmdExtWellTyped C P ts c ts') :
    CmdExtWellTyped { C with rigidTypeVars := r } P ts c ts' := by
  cases h with
  | cmd _ _ hc => exact .cmd _ _ _ (hc.withRigid r)
  | call _ _ _ _ _ _ _ hfind hwf hlhs hargs hlhsTy hinst hkind hequiv =>
    refine .call _ _ _ _ _ _ _ _ hfind hwf hlhs ?_ hlhsTy hinst hkind hequiv
    rw [exprWellTyped_withRigid]
    exact hargs

mutual

/-- Statement typing does not read the rigid type variables of the context:
    replacing them in the input context replaces them in the output
    context. -/
theorem StatementWellTyped.withRigid {P : Program} {C C' : LContext CoreLParams}
    {ts ts' : TypeScopes} {L : List String} {s : Statement}
    (r : List TyIdentifier) (h : StatementWellTyped P C ts L s C' ts') :
    StatementWellTyped P { C with rigidTypeVars := r } ts L s
      { C' with rigidTypeVars := r } ts' :=
  match h with
  | .cmd _ _ _ _ _ hc => .cmd _ _ _ _ _ (hc.withRigid r)
  | .block _ _ _ _ _ _ _ _ _ hl hb heq =>
      .block _ _ _ _ _ _ _ _ _ hl (StatementsWellTyped.withRigid r hb) heq
  | .ite_det _ _ _ _ _ _ _ _ _ _ _ _ hc ht he heq =>
      .ite_det _ _ _ _ _ _ _ _ _ _ _ _ (exprWellTyped_withRigid C r ▸ hc)
        (StatementsWellTyped.withRigid r ht)
        (StatementsWellTyped.withRigid r he) heq
  | .ite_nondet _ _ _ _ _ _ _ _ _ _ _ ht he heq =>
      .ite_nondet _ _ _ _ _ _ _ _ _ _ _ (StatementsWellTyped.withRigid r ht)
        (StatementsWellTyped.withRigid r he) heq
  | .loop _ _ _ _ _ _ _ _ _ _ _ hg hm hi hb heq =>
      .loop _ _ _ _ _ _ _ _ _ _ _
        (fun g hgd => exprWellTyped_withRigid C r ▸ hg g hgd)
        (fun m hmd => exprWellTyped_withRigid C r ▸ hm m hmd)
        (fun p hp => exprWellTyped_withRigid C r ▸ hi p hp)
        (StatementsWellTyped.withRigid r hb) heq
  | .exit _ _ _ _ _ _ hl heq => .exit _ _ _ _ _ _ hl heq
  | .typeDecl _ _ _ _ _ _ _ hn hadd heq =>
      .typeDecl _ _ _ _ _ _ _ hn
        (addKnownTypeWithError_setRigidTypeVars r hadd) heq

/-- Statement-list typing does not read the rigid type variables of the
    context: replacing them in the input context replaces them in the output
    context. -/
theorem StatementsWellTyped.withRigid {P : Program}
    {C C' : LContext CoreLParams} {ts ts' : TypeScopes} {L : List String}
    {ss : List Statement} (r : List TyIdentifier)
    (h : StatementsWellTyped P C ts L ss C' ts') :
    StatementsWellTyped P { C with rigidTypeVars := r } ts L ss
      { C' with rigidTypeVars := r } ts' :=
  match h with
  | .nil _ _ _ _ heq => .nil _ _ _ _ heq
  | .cons _ _ _ _ _ _ _ _ _ hs ht =>
      .cons _ _ _ _ _ _ _ _ _ (StatementWellTyped.withRigid r hs)
        (StatementsWellTyped.withRigid r ht)

end

/-- Procedure body typing does not read the rigid type variables of the
    context. -/
theorem ProcBodyWellTyped.withRigid {P : Program} {C : LContext CoreLParams}
    {ts : TypeScopes} {body : Procedure.Body} (r : List TyIdentifier)
    (h : ProcBodyWellTyped P C ts body) :
    ProcBodyWellTyped P { C with rigidTypeVars := r } ts body :=
  match h with
  | .structured _ _ _ _ hss =>
    .structured _ _ _ _ (StatementsWellTyped.withRigid r hss)
  | .cfg c o => .cfg c o
  | .abstract => .abstract

/-! ### Well-typed programs have well-formed calls -/

mutual

/-- Every call in a well-typed statement is well-formed in `P`. -/
private theorem StatementWellTyped.callsWF {P : Program} {C C' : LContext CoreLParams}
    {ts ts' : TypeScopes} {L : List String} {s : Statement}
    (h : StatementWellTyped P C ts L s C' ts') :
    ∀ c ∈ Statement.callSites s, WF.WFcallProp P c.procName c.args :=
  match h with
  | .cmd _ _ _ _ _ hc =>
    match hc with
    | .cmd _ _ _ _ => by simp [Statement.callSites, Command.callSites]
    | .call _ _ _ _ _ _ _ _ _ hwf _ _ _ _ _ _ => by
      intro c hc
      simp only [Statement.callSites, Command.callSites, List.mem_singleton] at hc
      subst hc
      exact hwf
  | .block _ _ _ _ _ _ _ _ _ _ hb _ => by
    simpa only [Statement.callSites] using StatementsWellTyped.callsWF hb
  | .ite_det _ _ _ _ _ _ _ _ _ _ _ _ _ ht he _ => by
    intro c hc
    simp only [Statement.callSites, List.mem_append] at hc
    exact hc.elim (StatementsWellTyped.callsWF ht c) (StatementsWellTyped.callsWF he c)
  | .ite_nondet _ _ _ _ _ _ _ _ _ _ _ ht he _ => by
    intro c hc
    simp only [Statement.callSites, List.mem_append] at hc
    exact hc.elim (StatementsWellTyped.callsWF ht c) (StatementsWellTyped.callsWF he c)
  | .loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb _ => by
    simpa only [Statement.callSites] using StatementsWellTyped.callsWF hb
  | .exit _ _ _ _ _ _ _ _ => by simp [Statement.callSites]
  | .typeDecl _ _ _ _ _ _ _ _ _ _ => by simp [Statement.callSites]

/-- Every call in a well-typed statement list is well-formed in `P`. -/
private theorem StatementsWellTyped.callsWF {P : Program} {C C' : LContext CoreLParams}
    {ts ts' : TypeScopes} {L : List String} {ss : List Statement}
    (h : StatementsWellTyped P C ts L ss C' ts') :
    ∀ c ∈ Statements.callSites ss, WF.WFcallProp P c.procName c.args :=
  match h with
  | .nil _ _ _ _ _ => by simp [Statements.callSites]
  | .cons _ _ _ _ _ _ _ _ _ hs hss => by
    intro c hc
    simp only [Statements.callSites, List.mem_append] at hc
    exact hc.elim (StatementWellTyped.callsWF hs c) (StatementsWellTyped.callsWF hss c)

end

/-- Every call in a well-typed declaration list is well-formed in `P`, given that every call of
    its CFG bodies is. -/
private theorem DeclsWellTyped.callsWF {P : Program} {C C' : LContext CoreLParams}
    {ts : TypeScopes} {ds : List Decl} (h : DeclsWellTyped P C ts ds C')
    (hcfg : ∀ q md (g : DetCFG) opq, Decl.proc q md ∈ ds → q.body = .cfg g opq →
      ∀ c ∈ q.callSites, WF.WFcallProp P c.procName c.args) :
    ∀ c ∈ ds.flatMap Decl.callSites, WF.WFcallProp P c.procName c.args := by
  induction h with
  | nil => simp
  | cons _ _ _ _ _ _ hd _ ih =>
    intro c hc
    simp only [List.flatMap_cons, List.mem_append] at hc
    refine hc.elim (fun hc => ?_)
      (ih (fun q md g o hmem => hcfg q md g o (List.mem_cons_of_mem _ hmem)) c)
    cases hd with
    | proc _ proc md hp =>
      simp only [Decl.callSites] at hc
      cases hbody : proc.body with
      | cfg g o => exact hcfg proc md g o (List.mem_cons_self ..) hbody c hc
      | abstract => simp [Procedure.callSites, hbody] at hc
      | structured _ =>
        simp only [Procedure.callSites] at hc
        rw [hbody] at hc
        have hbt := hp.bodyTyped
        rw [hbody] at hbt
        cases hbt with
        | structured _ _ _ _ hss => exact StatementsWellTyped.callsWF hss c hc
    | _ => simp [Decl.callSites] at hc

/-- A well-typed program has only well-formed calls, given that every call of its CFG bodies is
    well-formed. -/
theorem ProgramWellTyped.callsWellFormed {C : LContext CoreLParams} {ts : TypeScopes}
    {P : Program} (h : ProgramWellTyped C ts P)
    (hcfg : ∀ q md (g : DetCFG) opq, Decl.proc q md ∈ P.decls → q.body = .cfg g opq →
      ∀ c ∈ q.callSites, WF.WFcallProp P c.procName c.args) :
    P.callsWellFormed := by
  obtain ⟨-, _, hds⟩ := h
  exact DeclsWellTyped.callsWF hds hcfg

/-- A well-typed call is of a declared procedure with well-formed arguments, under a
    substitution `σ` of the procedure's type parameters: the call's result variables are
    declared, the types of its arguments and of its result variables are the procedure's
    formal types instantiated by `σ`, and its type arguments are the images of the type
    parameters under `σ`. -/
theorem CmdExtWellTyped.call_inv {C : LContext CoreLParams} {P : Program} {ts ts' : TypeScopes}
    {n : String} {tyArgs : Option (List Expression.Ty)} {callArgs : List (CallArg Expression)}
    {md : MetaData Expression}
    (h : CmdExtWellTyped C P ts (.call n tyArgs callArgs md) ts') :
    ∃ proc σ, Program.Procedure.find? P n = some proc ∧ WF.WFcallProp P n callArgs ∧
      (∀ v, v ∈ CallArg.getLhs callArgs → (ts.find? v).isSome) ∧
      (∀ i (hi : i < (CallArg.getInputExprs callArgs).length)
           (hj : i < proc.header.inputs.values.length),
        match (CallArg.getInputExprs callArgs)[i] with
        | .fvar _ x none => ts.find? x =
            some (.forAll [] (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ])
              (proc.header.inputs.values[i])))
        | e => ExprWellTyped C ts e
            (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (proc.header.inputs.values[i]))) ∧
      (∀ i (hi : i < (CallArg.getLhs callArgs).length)
           (hj : i < proc.header.outputs.values.length),
        ts.find? ((CallArg.getLhs callArgs)[i]) =
          some (.forAll [] (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ])
            (proc.header.outputs.values[i])))) ∧
      tyArgs = some (proc.header.typeArgs.map
        (fun a => .forAll [] (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (.ftvar a)))) := by
  cases h with
  | call _ _ _ proc _ σ _ hfind hwf hlhs hin hout htyArgs _ =>
    exact ⟨proc, σ, hfind, hwf, hlhs, hin, hout, htyArgs⟩

/-! ### Well-typed code keeps scope declarations and has well-typed procedures -/

/-- Equivalent scopes keep every declaration. -/
private theorem ScopeExtends.of_equiv {ts ts' : TypeScopes} (hequiv : HMaps.Equiv ts' ts) :
    ScopeExtends ts ts' := by
  intro x ty hx
  rw [HMaps.Equiv.find? hequiv x]
  exact hx

/-- Scopes equivalent to the scopes with a fresh variable inserted keep every declaration of the
    original scopes. -/
private theorem ScopeExtends.of_equiv_insert {ts ts' : TypeScopes} {x : Expression.Ident}
    {ty : LTy} (hfresh : ts.find? x = none) (hequiv : HMaps.Equiv ts' (ts.insert x ty)) :
    ScopeExtends ts ts' := by
  intro y yty hy
  rw [HMaps.Equiv.find? hequiv y]
  by_cases hyx : y = x
  · subst hyx
    rw [hfresh] at hy
    cases hy
  · rw [HMaps.find?_insert_ne ts y x ty hyx]
    exact hy

/-- A variable declared in scopes has the same instantiated type in any scopes that extend
    them. -/
theorem TypeScopes.instVarTyping_of_scopeExtends {S : Subst} {ts ts' : TypeScopes}
    (hext : ScopeExtends ts ts') {x : Expression.Ident} {ty : LTy}
    (hx : ts.instVarTyping S x = some ty) : ts'.instVarTyping S x = some ty := by
  simp only [TypeScopes.instVarTyping, Option.map_eq_some_iff] at hx ⊢
  obtain ⟨ty0, hty0, rfl⟩ := hx
  exact ⟨ty0, hext x ty0 hty0, rfl⟩

/-- A store that conforms to scopes also conforms to any scopes it extends. -/
theorem storeHasTyping_of_scopeExtends {F : Expression.Factory} {S : Subst}
    {σ : CoreStore} {ts ts' : TypeScopes} (hext : ScopeExtends ts ts')
    (hs : StoreHasTyping F σ (ts'.instVarTyping S)) :
    StoreHasTyping F σ (ts.instVarTyping S) := by
  intro x ty hx
  exact hs x ty (TypeScopes.instVarTyping_of_scopeExtends hext hx)

/-- A well-typed base command ends in scopes that keep every declaration it started with. -/
private theorem CmdWellTyped.scopeExtends {C : LContext CoreLParams} {ts ts' : TypeScopes}
    {c : Cmd Expression} (h : CmdWellTyped C ts c ts') : ScopeExtends ts ts' := by
  cases h with
  | init_det =>
    rename_i hfresh _ _ _ _ hequiv
    exact ScopeExtends.of_equiv_insert hfresh hequiv
  | init_nondet =>
    rename_i hfresh _ _ hequiv
    exact ScopeExtends.of_equiv_insert hfresh hequiv
  | set_det => rename_i hequiv; exact ScopeExtends.of_equiv hequiv
  | set_nondet => rename_i hequiv; exact ScopeExtends.of_equiv hequiv
  | assert => rename_i hequiv; exact ScopeExtends.of_equiv hequiv
  | assume => rename_i hequiv; exact ScopeExtends.of_equiv hequiv
  | cover => rename_i hequiv; exact ScopeExtends.of_equiv hequiv

/-- A well-typed extended command ends in scopes that keep every declaration it started
    with. -/
private theorem CmdExtWellTyped.scopeExtends {C : LContext CoreLParams} {P : Program}
    {ts ts' : TypeScopes} {c : Command} (h : CmdExtWellTyped C P ts c ts') :
    ScopeExtends ts ts' := by
  cases h with
  | cmd => rename_i hcmd; exact CmdWellTyped.scopeExtends hcmd
  | call => rename_i hequiv; exact ScopeExtends.of_equiv hequiv

/-- A well-typed statement ends in scopes that keep every declaration it started with. -/
theorem StatementWellTyped.scopeExtends {P : Program} {C C' : LContext CoreLParams}
    {ts ts' : TypeScopes} {L : List String} {s : Statement}
    (h : StatementWellTyped P C ts L s C' ts') : ScopeExtends ts ts' := by
  cases h with
  | cmd => rename_i hcmd; exact CmdExtWellTyped.scopeExtends hcmd
  | block => rename_i hequiv; exact ScopeExtends.of_equiv hequiv
  | ite_det => rename_i hequiv; exact ScopeExtends.of_equiv hequiv
  | ite_nondet => rename_i hequiv; exact ScopeExtends.of_equiv hequiv
  | loop => rename_i hequiv; exact ScopeExtends.of_equiv hequiv
  | exit => rename_i hequiv; exact ScopeExtends.of_equiv hequiv
  | typeDecl => rename_i hequiv; exact ScopeExtends.of_equiv hequiv

/-- A well-typed statement list ends in scopes that keep every declaration it started with. -/
theorem StatementsWellTyped.scopeExtends {P : Program} {C C' : LContext CoreLParams}
    {ts ts' : TypeScopes} {L : List String} {ss : List Statement}
    (h : StatementsWellTyped P C ts L ss C' ts') : ScopeExtends ts ts' := by
  induction ss generalizing C ts with
  | nil =>
    cases h with
    | nil => rename_i hequiv; exact ScopeExtends.of_equiv hequiv
  | cons s rest ih =>
    cases h with
    | cons =>
      rename_i hhead hrest
      exact fun x ty hx => ih hrest x ty (StatementWellTyped.scopeExtends hhead x ty hx)

/-- A procedure in a well-typed declaration list is well typed in the scopes of the list. -/
private theorem DeclsWellTyped.procWellTyped {P : Program} {C C' : LContext CoreLParams}
    {ts : TypeScopes} {ds : List Decl} {proc : Procedure} {md : MetaData Expression}
    (h : DeclsWellTyped P C ts ds C') (hmem : Decl.proc proc md ∈ ds) :
    ∃ C0, ProcWellTyped P C0 ts proc := by
  induction h with
  | nil => exact absurd hmem List.not_mem_nil
  | cons _ _ _ _ d _ hd _ ih =>
    rcases List.mem_cons.mp hmem with hhead | htail
    · subst hhead
      cases hd with
      | proc _ _ _ hproc => exact ⟨_, hproc⟩
    · exact ih htail

/-- A procedure declared in a well-typed program is well typed in the scopes of the program,
    in the context the program has built up before the declaration. -/
theorem ProgramWellTyped.procWellTyped {C0 : LContext CoreLParams} {ts0 : TypeScopes}
    {P : Program} {proc : Procedure} {md : MetaData Expression}
    (h : ProgramWellTyped C0 ts0 P) (hmem : Decl.proc proc md ∈ P.decls) :
    ∃ C, ProcWellTyped P C ts0 proc := by
  obtain ⟨_, _, hds⟩ := h
  exact DeclsWellTyped.procWellTyped hds hmem

/-- A procedure found by name in a well-typed program is well typed. -/
theorem ProgramWellTyped.procWellTyped_of_find? {C0 : LContext CoreLParams} {ts0 : TypeScopes}
    {P : Program} {n : String} {proc : Procedure}
    (h : ProgramWellTyped C0 ts0 P) (hfind : Program.Procedure.find? P n = some proc) :
    ∃ C, ProcWellTyped P C ts0 proc := by
  obtain ⟨_, hmem, -⟩ := Program.Procedure.find?_mem_decls P n proc hfind
  exact h.procWellTyped hmem

/-! ### Well-typed bodies declare variables only at monotypes -/

/-- Every variable a well-typed base command declares is declared at a monotype. -/
theorem CmdWellTyped.initTypes_mono {C : LContext CoreLParams} {ts ts' : TypeScopes}
    {c : Cmd Expression} (h : CmdWellTyped C ts c ts') :
    ∀ ty ∈ Cmd.initTypes c, ty.isMonoType = true := by
  intro ty hty
  cases h with
  | init_det =>
    rename_i hxty _ _ _
    subst hxty
    simp only [Cmd.initTypes, List.mem_singleton] at hty
    subst hty
    rfl
  | init_nondet =>
    rename_i hxty _ _
    subst hxty
    simp only [Cmd.initTypes, List.mem_singleton] at hty
    subst hty
    rfl
  | set_det => simp only [Cmd.initTypes, List.not_mem_nil] at hty
  | set_nondet => simp only [Cmd.initTypes, List.not_mem_nil] at hty
  | assert => simp only [Cmd.initTypes, List.not_mem_nil] at hty
  | assume => simp only [Cmd.initTypes, List.not_mem_nil] at hty
  | cover => simp only [Cmd.initTypes, List.not_mem_nil] at hty

/-- A well-typed command declares variables only at monotypes, and a well-typed call carries
    only monotypes as type arguments. -/
private theorem CmdExtWellTyped.allDeclTys_mono {C : LContext CoreLParams} {P : Program}
    {ts ts' : TypeScopes} {c : Command} (h : CmdExtWellTyped C P ts c ts') :
    Statement.AllDeclTys (fun ty => ∃ τ, ty = .forAll [] τ) (.cmd c) := by
  cases h with
  | cmd =>
    rename_i hcmd
    have hmonoInit := CmdWellTyped.initTypes_mono hcmd
    cases hcmd with
    | init_det =>
      exact LTy.eq_forAll_nil_of_isMonoType (hmonoInit _ (List.mem_singleton_self _))
    | init_nondet =>
      exact LTy.eq_forAll_nil_of_isMonoType (hmonoInit _ (List.mem_singleton_self _))
    | _ => trivial
  | call _ _ _ _ _ _ _ _ _ _ _ _ htyArgs _ =>
    intro tys htys ty hty
    rw [htyArgs] at htys
    cases htys
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hty
    exact ⟨_, rfl⟩

mutual

/-- A well-typed statement declares variables, and instantiates calls, only at monotypes. -/
theorem StatementWellTyped.allDeclTys_mono {P : Program} {C C' : LContext CoreLParams}
    {ts ts' : TypeScopes} {L : List String} {s : Statement}
    (h : StatementWellTyped P C ts L s C' ts') :
    Statement.AllDeclTys (fun ty => ∃ τ, ty = .forAll [] τ) s :=
  match h with
  | .cmd _ _ _ _ _ hc => CmdExtWellTyped.allDeclTys_mono hc
  | .block _ _ _ _ _ _ _ _ _ _ hb _ => StatementsWellTyped.allDeclTys_mono hb
  | .ite_det _ _ _ _ _ _ _ _ _ _ _ _ _ ht he _ =>
    ⟨StatementsWellTyped.allDeclTys_mono ht, StatementsWellTyped.allDeclTys_mono he⟩
  | .ite_nondet _ _ _ _ _ _ _ _ _ _ _ ht he _ =>
    ⟨StatementsWellTyped.allDeclTys_mono ht, StatementsWellTyped.allDeclTys_mono he⟩
  | .loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb _ => StatementsWellTyped.allDeclTys_mono hb
  | .exit _ _ _ _ _ _ _ _ => trivial
  | .typeDecl _ _ _ _ _ _ _ _ _ _ => trivial

/-- A well-typed statement list declares variables, and instantiates calls, only at
    monotypes. -/
theorem StatementsWellTyped.allDeclTys_mono {P : Program} {C C' : LContext CoreLParams}
    {ts ts' : TypeScopes} {L : List String} {ss : List Statement}
    (h : StatementsWellTyped P C ts L ss C' ts') :
    Statements.AllDeclTys (fun ty => ∃ τ, ty = .forAll [] τ) ss :=
  match h with
  | .nil _ _ _ _ _ => trivial
  | .cons _ _ _ _ _ _ _ _ _ hs hss =>
    ⟨StatementWellTyped.allDeclTys_mono hs, StatementsWellTyped.allDeclTys_mono hss⟩

end

/-- Every variable declared anywhere in a well-typed statement list is declared at a
    monotype. -/
theorem StatementsWellTyped.initTypes_mono {P : Program} {C C' : LContext CoreLParams}
    {ts ts' : TypeScopes} {L : List String} {ss : List Statement}
    (h : StatementsWellTyped P C ts L ss C' ts') :
    ∀ ty ∈ Imperative.Block.initTypes ss, ty.isMonoType = true := by
  intro ty hty
  obtain ⟨τ, rfl⟩ := Statements.AllDeclTys.of_mem_initTypes ss
    (StatementsWellTyped.allDeclTys_mono h) ty hty
  rfl

/-- A well-typed procedure with a structured body declares variables in its body only at
    monotypes (`initTypesMono`). A CFG body carries no typing obligation, so the lemma is
    stated for structured bodies. -/
theorem ProcWellTyped.initTypesMono {P : Program} {C : LContext CoreLParams} {ts : TypeScopes}
    {proc : Procedure} {ss : List Statement} (h : ProcWellTyped P C ts proc)
    {opq : Bool} (hss : proc.body = .structured ss opq) : proc.initTypesMono = true := by
  have hbody : ProcBodyWellTyped P C (procBodyScopes ts proc) proc.body := h.bodyTyped
  rw [hss] at hbody
  cases hbody with
  | structured =>
    rename_i hstmts
    simp only [Procedure.initTypesMono, hss, List.all_eq_true]
    exact StatementsWellTyped.initTypes_mono hstmts

/-- In a well-typed procedure with a structured body, every type variable in a local
    declaration's type or a call type argument is a type parameter of the procedure. -/
theorem ProcWellTyped.declTysScoped {P : Program} {C : LContext CoreLParams} {ts : TypeScopes}
    {proc : Procedure} {ss : List Statement} {opq : Bool} (h : ProcWellTyped P C ts proc)
    (hss : proc.body = .structured ss opq) :
    Statements.AllDeclTys (fun ty => ∀ τ, ty = .forAll [] τ →
      ∀ a ∈ LMonoTy.freeVars τ, a ∈ proc.header.typeArgs) ss := by
  have hbound := h.declTyVarsBound
  rw [hss] at hbound
  refine Statements.AllDeclTys.of_stmtCollect (fe := fun _ => []) (ft := LMonoTy.freeVars)
    (Q := fun a => a ∈ proc.header.typeArgs) ?_ ss hbound
  intro ty hty τ hτ
  subst hτ
  exact hty

/-- A free type variable of a formal's type (an input or an output type) of a well-typed
    procedure is one of the procedure's type parameters. -/
theorem ProcWellTyped.typeArg_of_mem_freeVars_formal {P : Program} {C : LContext CoreLParams}
    {ts : TypeScopes} {proc : Procedure} (h : ProcWellTyped P C ts proc) {ty : LMonoTy}
    (hty : ty ∈ proc.header.inputs.values ++ proc.header.outputs.values) {a : TyIdentifier}
    (ha : a ∈ ty.freeVars) : a ∈ proc.header.typeArgs := by
  apply h.noUndeclaredVars
  rcases List.mem_append.1 hty with hin | hout
  · exact List.mem_append_left _ (LMonoTys.freeVars_mem_subset hin ha)
  · exact List.mem_append_right _ (LMonoTys.freeVars_mem_subset hout ha)

/-! ### Scopes built from signatures -/

/-- Looking up a name in the scope of a signature that is the concatenation of two signatures
    gives the binding of the second when it has one, and the binding of the first otherwise. -/
private theorem formalsScope_find?_append (a b : @LMonoTySignature Unit) (x : CoreIdent) :
    (formalsScope (a ++ b)).find? x =
      ((formalsScope b).find? x).or ((formalsScope a).find? x) := by
  unfold formalsScope
  have hmap : List.map (fun q : CoreIdent × LMonoTy => (q.1, LTy.forAll [] q.2)) (a ++ b) =
      List.map (fun q : CoreIdent × LMonoTy => (q.1, LTy.forAll [] q.2)) a ++
        List.map (fun q : CoreIdent × LMonoTy => (q.1, LTy.forAll [] q.2)) b := List.map_append
  rw [hmap]
  exact Strata.Util.HMap.find?_ofList_append _ _ x

/-- Pairing each type with the trivial scheme leaves the list of names unchanged. -/
private theorem formalsScope_map_fst (l : List (CoreIdent × LMonoTy)) :
    (l.map (fun q => (q.1, LTy.forAll [] q.2))).map Prod.fst = l.map Prod.fst := by
  simp only [List.map_map, Function.comp_def]

/-- A name that the signature does not bind is unbound in its scope. -/
private theorem formalsScope_find?_of_not_mem (sig : @LMonoTySignature Unit) {x : CoreIdent}
    (hx : x ∉ sig.keys) : (formalsScope sig).find? x = none := by
  unfold formalsScope
  rw [ListMap.keys_eq_map_fst] at hx
  have hkeys : x ∉ (sig.map (fun q => (q.1, LTy.forAll [] q.2))).map Prod.fst := by
    rw [formalsScope_map_fst sig]
    exact hx
  exact Strata.Util.HMap.find?_ofList_of_not_mem hkeys

/-- In the scope of a signature with distinct names, each name has the trivial scheme over
    the type the signature gives it. -/
private theorem formalsScope_find?_of_mem (sig : @LMonoTySignature Unit) (hnd : sig.keys.Nodup)
    {x : CoreIdent} {ty : LMonoTy} (hmem : (x, ty) ∈ sig.toList) :
    (formalsScope sig).find? x = some (.forAll [] ty) := by
  unfold formalsScope
  rw [ListMap.keys_eq_map_fst] at hnd
  have hkeys : ((sig.map (fun q => (q.1, LTy.forAll [] q.2))).map Prod.fst).Nodup := by
    rw [formalsScope_map_fst sig]
    exact hnd
  exact Strata.Util.HMap.find?_ofList_of_mem_of_nodup hkeys
    (List.mem_map.2 ⟨(x, ty), hmem, rfl⟩)

/-- A name that the signature binds is bound in its scope. -/
private theorem formalsScope_find?_isSome_of_mem_keys (sig : @LMonoTySignature Unit)
    {x : CoreIdent} (hx : x ∈ sig.keys) : ∃ t, (formalsScope sig).find? x = some t := by
  unfold formalsScope
  apply Strata.Util.HMap.find?_ofList_of_mem_keys
  rw [ListMap.keys_eq_map_fst] at hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
  exact List.mem_map.2 ⟨(q.1, LTy.forAll [] q.2), List.mem_map.2 ⟨q, hq, rfl⟩, rfl⟩

/-- The scope of a procedure body binds, in order of precedence, the inputs, the outputs and the
    `old` copies of the in-out parameters, over the global scopes. -/
private theorem procBodyScopes_find? (ts : TypeScopes) (proc : Procedure) (x : CoreIdent) :
    (procBodyScopes ts proc).find? x =
      ((formalsScope proc.header.inputs).find? x).or
        (((formalsScope proc.header.outputs).find? x).or
          (((formalsScope (oldInoutSig proc.header.getInoutParams.toList)).find? x).or
            (ts.find? x))) := by
  have hscope : procBodyScopes ts proc = ts.push (formalsScope
      (oldInoutSig proc.header.getInoutParams.toList ++ proc.header.outputs ++
        proc.header.inputs)) := rfl
  rw [hscope, HMaps.find?_push]
  simp only [formalsScope_find?_append]
  rw [Option.or_assoc, Option.or_assoc]

/-- In the scope of the `old` copies of distinctly named formals, a bound name is the `old` copy
    of one of the formals, and its scheme is the trivial scheme over the formal's type. -/
private theorem formalsScope_old_find?_some (G : List (CoreIdent × LMonoTy))
    (hnd : (G.map Prod.fst).Nodup) {x : CoreIdent} {ty : LTy}
    (h : (formalsScope (oldInoutSig G)).find? x = some ty) :
    ∃ g t, (g, t) ∈ G ∧ x = CoreIdent.mkOld g.name ∧ ty = .forAll [] t := by
  by_cases hx : x ∈ (oldInoutSig G).keys
  · rw [ListMap.keys_eq_map_fst] at hx
    obtain ⟨q, hq, hqx⟩ := List.mem_map.1 hx
    obtain ⟨⟨g, t⟩, hgt, rfl⟩ := List.mem_map.1 hq
    have hinj : Function.Injective (fun id : CoreIdent => CoreIdent.mkOld id.name) :=
      fun _ _ hab => CoreIdent.eq_of_mkOld_eq hab
    have hnd' : (oldInoutSig G).keys.Nodup := by
      have hmap : ((G.map Prod.fst).map (fun id : CoreIdent => CoreIdent.mkOld id.name)).Nodup :=
        List.Pairwise.map (fun id : CoreIdent => CoreIdent.mkOld id.name)
          (fun _ _ hab hfab => hab (hinj hfab)) hnd
      rw [ListMap.keys_eq_map_fst]
      simp only [oldInoutSig, List.map_map, Function.comp_def] at hmap ⊢
      exact hmap
    have hxg : CoreIdent.mkOld g.name = x := hqx
    subst hxg
    have hq' : (CoreIdent.mkOld g.name, t) ∈ (oldInoutSig G).toList := hq
    rw [formalsScope_find?_of_mem (oldInoutSig G) hnd' hq'] at h
    exact ⟨g, t, hgt, rfl, (Option.some.inj h).symm⟩
  · rw [formalsScope_find?_of_not_mem (oldInoutSig G) hx] at h
    exact nomatch h

/-- Applying a function to the types of a signature applies it to the bodies of the schemes in
    its scope. -/
private theorem formalsScope_find?_map (sig : @LMonoTySignature Unit) (f : LMonoTy → LMonoTy)
    (x : CoreIdent) :
    (formalsScope (sig.map (fun q => (q.1, f q.2)))).find? x =
      ((formalsScope sig).find? x).map (mapLTyTys f) := by
  unfold formalsScope
  have hlist : ∀ l : List (CoreIdent × LMonoTy),
      (Strata.Util.HMap.ofList ((l.map (fun q => (q.1, f q.2))).map
        (fun q => (q.1, LTy.forAll [] q.2)))).find? x =
      ((Strata.Util.HMap.ofList (l.map (fun q => (q.1, LTy.forAll [] q.2)))).find? x).map
        (mapLTyTys f) := by
    intro l
    have hl : (l.map (fun q => (q.1, f q.2))).map (fun q => (q.1, LTy.forAll [] q.2)) =
        (l.map (fun q => (q.1, LTy.forAll [] q.2))).map (fun p => (p.1, mapLTyTys f p.2)) := by
      simp only [List.map_map, Function.comp_def, mapLTyTys]
    rw [hl]
    exact Strata.Util.HMap.find?_ofList_map_snd _ _ x
  exact hlist sig

/-- The `old` copies of the in-out parameters of an instance of a procedure are those of the
    procedure with the types mapped. -/
private theorem oldInoutSig_map (G : List (CoreIdent × LMonoTy)) (f : LMonoTy → LMonoTy) :
    oldInoutSig (G.map (fun q => (q.1, f q.2))) =
      (oldInoutSig G).map (fun q => (q.1, f q.2)) := by
  simp only [oldInoutSig, List.map_map, Function.comp_def]
  rfl

/-- The scope of the body of an instance of a procedure binds each name at the scheme that the
    scope of the procedure body gives it, with the substitution of the type arguments applied
    to the scheme's body, when the global scopes bind nothing. -/
private theorem procBodyScopes_inst_find? {ts0 : TypeScopes} {proc inst : Procedure}
    {tys : List Expression.Ty} (ht0 : ∀ x, ts0.find? x = none)
    (h : proc.instantiateTypes tys = some inst) :
    ∃ ms, tys.mapM LTy.toMonoType? = some ms ∧ ∀ x,
      (procBodyScopes ts0 inst).find? x =
        ((procBodyScopes ts0 proc).find? x).map (mapLTyTys
          (LMonoTy.subst (Strata.Util.HMaps.ofScopes [proc.header.typeArgs.zip ms]))) := by
  obtain ⟨ms, hms, hin, hout, -⟩ := Procedure.instantiateTypes_spec h
  obtain ⟨-, hkout⟩ := Procedure.instantiateTypes_keys h
  refine ⟨ms, hms, fun x => ?_⟩
  have hgio : inst.header.getInoutParams.toList =
      proc.header.getInoutParams.toList.map (fun q => (q.1, LMonoTy.subst
        (Strata.Util.HMaps.ofScopes [proc.header.typeArgs.zip ms]) q.2)) := by
    unfold Procedure.Header.getInoutParams Core.getInoutParams
    rw [hkout, hin]
    exact List.filter_map
  rw [procBodyScopes_find?, procBodyScopes_find?, hgio, hin, hout, oldInoutSig_map,
    formalsScope_find?_map, formalsScope_find?_map, formalsScope_find?_map, ht0 x]
  cases (formalsScope proc.header.inputs).find? x <;>
    cases (formalsScope proc.header.outputs).find? x <;>
    cases (formalsScope (oldInoutSig proc.header.getInoutParams.toList)).find? x <;> rfl

/-- Instantiating a procedure at type arguments `tys` instantiates the variable typing of its
    body scope: when the global scopes `ts0` declare nothing, the body scope of the instance
    types each name as the body scope of the procedure does, with the substitution of the type
    arguments applied. -/
theorem procBodyScopes_inst {ts0 : TypeScopes} {proc inst : Procedure}
    {tys : List Expression.Ty} (ht0 : ∀ x, ts0.find? x = none)
    (h : proc.instantiateTypes tys = some inst) :
    ∃ ms, tys.mapM LTy.toMonoType? = some ms ∧
      (procBodyScopes ts0 inst).find? =
        (procBodyScopes ts0 proc).instVarTyping
          (Strata.Util.HMaps.ofScopes [proc.header.typeArgs.zip ms]) := by
  obtain ⟨ms, hms, hfind⟩ := procBodyScopes_inst_find? ht0 h
  exact ⟨ms, hms, funext hfind⟩

/-- A name that the procedure body scope binds is an input, an output that is not an input, or
    the `old` copy of an in-out parameter, and its scheme is the trivial scheme over the type of
    that formal. The global scopes bind nothing at the name, and the input names are distinct,
    as are the output names. -/
theorem procBodyScopes_find?_some {ts : TypeScopes} {proc : Procedure} {x : CoreIdent}
    {ty : LTy} (hts : ts.find? x = none) (hin : proc.header.inputs.keys.Nodup)
    (hout : proc.header.outputs.keys.Nodup)
    (h : (procBodyScopes ts proc).find? x = some ty) :
    (∃ t, (x, t) ∈ proc.header.inputs.toList ∧ ty = .forAll [] t) ∨
    (x ∉ proc.header.inputs.keys ∧
      ∃ t, (x, t) ∈ proc.header.outputs.toList ∧ ty = .forAll [] t) ∨
    (x ∉ proc.header.inputs.keys ∧ x ∉ proc.header.outputs.keys ∧
      ∃ g t, (g, t) ∈ proc.header.getInoutParams.toList ∧ x = CoreIdent.mkOld g.name ∧
        ty = .forAll [] t) := by
  rw [procBodyScopes_find?, hts, Option.or_none] at h
  by_cases hI : x ∈ proc.header.inputs.keys
  · have hI' := hI
    rw [ListMap.keys_eq_map_fst] at hI'
    obtain ⟨⟨x1, t⟩, hq, hx1⟩ := List.mem_map.1 hI'
    have hx1' : x1 = x := hx1
    subst hx1'
    rw [formalsScope_find?_of_mem proc.header.inputs hin hq] at h
    exact .inl ⟨t, hq, (Option.some.inj h).symm⟩
  · rw [formalsScope_find?_of_not_mem proc.header.inputs hI, Option.none_or] at h
    by_cases hO : x ∈ proc.header.outputs.keys
    · have hO' := hO
      rw [ListMap.keys_eq_map_fst] at hO'
      obtain ⟨⟨x1, t⟩, hq, hx1⟩ := List.mem_map.1 hO'
      have hx1' : x1 = x := hx1
      subst hx1'
      rw [formalsScope_find?_of_mem proc.header.outputs hout hq] at h
      exact .inr (.inl ⟨hI, t, hq, (Option.some.inj h).symm⟩)
    · rw [formalsScope_find?_of_not_mem proc.header.outputs hO, Option.none_or] at h
      have hinL : (proc.header.inputs.toList.map Prod.fst).Nodup := by
        rw [ListMap.keys_eq_map_fst] at hin
        exact hin
      have hGnd : (proc.header.getInoutParams.toList.map Prod.fst).Nodup := by
        have hsub : proc.header.getInoutParams.toList.Sublist proc.header.inputs.toList :=
          List.filter_sublist
        exact (hsub.map Prod.fst).nodup hinL
      obtain ⟨g, t, hgt, hxg, hty⟩ := formalsScope_old_find?_some _ hGnd h
      exact .inr (.inr ⟨hI, hO, g, t, hgt, hxg, hty⟩)

/-- A name that the procedure body scope does not bind is neither an input, nor an output, nor
    the `old` copy of an in-out parameter. -/
theorem procBodyScopes_find?_none {ts : TypeScopes} {proc : Procedure} {x : CoreIdent}
    (h : (procBodyScopes ts proc).find? x = none) :
    x ∉ proc.header.inputs.keys ∧ x ∉ proc.header.outputs.keys ∧
      ∀ g ∈ proc.header.getInoutParams.keys, x ≠ CoreIdent.mkOld g.name := by
  rw [procBodyScopes_find?] at h
  simp only [Option.or_eq_none_iff] at h
  obtain ⟨hin, hout, hold, -⟩ := h
  refine ⟨fun hx => ?_, fun hx => ?_, fun g hg hxg => ?_⟩
  · obtain ⟨t, ht⟩ := formalsScope_find?_isSome_of_mem_keys _ hx
    rw [ht] at hin
    exact nomatch hin
  · obtain ⟨t, ht⟩ := formalsScope_find?_isSome_of_mem_keys _ hx
    rw [ht] at hout
    exact nomatch hout
  · rw [ListMap.keys_eq_map_fst] at hg
    obtain ⟨⟨g1, t⟩, hq, hg1⟩ := List.mem_map.1 hg
    have hg1' : g1 = g := hg1
    subst hg1'
    have hmem : x ∈ (oldInoutSig proc.header.getInoutParams.toList).keys := by
      rw [ListMap.keys_eq_map_fst, hxg]
      exact List.mem_map.2 ⟨(CoreIdent.mkOld g1.name, t), List.mem_map.2 ⟨(g1, t), hq, rfl⟩, rfl⟩
    obtain ⟨t', ht⟩ := formalsScope_find?_isSome_of_mem_keys _ hmem
    rw [ht] at hold
    exact nomatch hold

/-- A procedure that occurs in a program's declarations is what `Program.Procedure.find?`
    returns for its own name, provided the names the program declares as procedures are
    distinct. -/
theorem find?_of_mem_of_programNamesOfKind_nodup
    (P : Program) (q : Procedure) (mdq : MetaData Expression)
    (hnodup : (programNamesOfKind P .proc).Nodup)
    (hmem : Decl.proc q mdq ∈ P.decls) :
    Program.Procedure.find? P q.header.name = some q := by
  have hfilt : P.decls.filter (fun d => declNameKind d == DeclKind.proc) =
      P.decls.filter (fun d => d.kind == DeclKind.proc) := by
    apply List.filter_congr
    intro d _
    cases d <;> rfl
  have hnodup' : ((P.decls.filter (fun d => d.kind == DeclKind.proc)).flatMap
      Decl.names).Nodup := by
    rw [← hfilt]
    exact hnodup
  exact Program.Procedure.find?_of_mem_of_procNames_nodup P.decls q mdq hnodup' hmem

/-! ### Evaluating well-typed expressions -/

/-- Each free variable of a well-typed expression carries an annotation, and
    the scopes declare it at that annotation. -/
private theorem exprWellTyped_declared {C : LContext CoreLParams} {ts : TypeScopes}
    {e : Expression.Expr} {mty : LMonoTy} (he : ExprWellTyped C ts e mty) :
    ∀ x ty, (x, ty) ∈ LExpr.freeVars e →
      ∃ τ, ty = some τ ∧ ts.find? x = some (.forAll [] τ) := by
  intro x ty hx
  have hsome := LExpr.HasTypeA.freeVars_annotated he.1 x ty hx
  obtain ⟨τ, rfl⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨τ, rfl, he.2.2.fvarsDeclared x τ hx⟩

/-- Every free variable of an expression that is well typed in scopes `ts`, with the type
    substitution `S` applied to its annotations, is bound in a store that conforms to `ts` with
    `S` applied. -/
theorem exprWellTyped_varsDefined_inst {C : LContext CoreLParams} {ts : TypeScopes}
    {e : Expression.Expr} {mty : LMonoTy} {f : Expression.Factory} {σ : CoreStore}
    (S : Subst) (he : ExprWellTyped C ts e mty)
    (hs : StoreHasTyping f σ (ts.instVarTyping S)) :
    SemanticStore.varsDefined
      (· ∈ HasFvars.getFvars (P := Expression) (mapExprTys (LMonoTy.subst S) e)) σ := by
  rw [getFvars_mapExprTys]
  intro x hx
  have hmem : x ∈ LExpr.LExpr.getVars e := hx
  rw [Lambda.getVars_eq_freeVars_idents, List.mem_map] at hmem
  obtain ⟨⟨x', ty⟩, hfree, rfl⟩ := hmem
  obtain ⟨τ, -, hτ⟩ := exprWellTyped_declared he x' ty hfree
  obtain ⟨v, hv, -⟩ := hs x' _ (TypeScopes.instVarTyping_of_find? hτ)
  simp only [hv, Option.isSome_some]

/-- An expression that is well typed at `mty` in scopes `ts` has, after a substitution `S` is
    applied to its annotations, the declarative type `S mty` under the variable typing of `ts`
    with `S` applied, provided `S mty` is ground. -/
theorem ExprWellTyped.hasType_inst {C : LContext CoreLParams} {ts : TypeScopes}
    {e : Expression.Expr} {mty : LMonoTy} (S : Subst) (he : ExprWellTyped C ts e mty)
    (hground : (LMonoTy.subst S mty).IsGround) :
    Expression.HasType (ts.instVarTyping S) (mapExprTys (LMonoTy.subst S) e)
      (.forAll [] (LMonoTy.subst S mty)) := by
  have hdecl := exprWellTyped_declared he
  have hty0 : LExpr.HasTypeA (T := CoreLParams) []
      (LExpr.applyTypeSubst e S) (LMonoTy.subst S mty) := by
    simpa using Lambda.applyTypeSubst_typeCheck (T := CoreLParams) S he.1
  rw [LExpr.applyTypeSubst_eq_replaceUserProvidedType] at hty0
  have hfv : LExpr.freeVars (mapExprTys (LMonoTy.subst S) e) =
      (LExpr.freeVars e).map (fun p => (p.1, p.2.map (LMonoTy.subst S))) :=
    LExpr.freeVars_replaceUserProvidedType e (LMonoTy.subst S)
  have hvarAnn : ∀ x ty, (x, ty) ∈ LExpr.freeVars (mapExprTys (LMonoTy.subst S) e) →
      ∃ τ, ty = some τ ∧
        (fun x => ((ts.instVarTyping S) x).bind LTy.toMonoType?) x = some τ := by
    intro x ty hx
    rw [hfv, List.mem_map] at hx
    obtain ⟨⟨x0, ty0⟩, hmem, hpair⟩ := hx
    obtain ⟨τ, rfl, hτ⟩ := hdecl x0 ty0 hmem
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    refine ⟨LMonoTy.subst S τ, rfl, ?_⟩
    have hfind : ts.find? x0 = some (.forAll [] τ) := hτ
    simp only [TypeScopes.instVarTyping, hfind, Option.map_some, Option.bind_some,
      Lambda.mapLTyTys, LTy.toMonoType?]
  have hvar : (mapExprTys (LMonoTy.subst S) e).annotateFvars
      (fun x => ((ts.instVarTyping S) x).bind LTy.toMonoType?) =
      mapExprTys (LMonoTy.subst S) e :=
    LExpr.annotateFvars_eq_self _ hvarAnn
  have hdef : ∀ x ∈ LExpr.LExpr.getVars (mapExprTys (LMonoTy.subst S) e),
      ((ts.instVarTyping S) x).isSome = true := by
    intro x hx
    rw [Lambda.getVars_eq_freeVars_idents, List.mem_map] at hx
    obtain ⟨⟨x', ty⟩, hmem, rfl⟩ := hx
    obtain ⟨τ, -, hτ⟩ := hvarAnn x' ty hmem
    cases hinst : (ts.instVarTyping S) x' with
    | none => simp only [hinst, Option.bind_none] at hτ; cases hτ
    | some t => simp only [Option.isSome_some]
  have hty : LExpr.HasTypeA []
      ((mapExprTys (LMonoTy.subst S) e).annotateFvars
        (fun x => ((ts.instVarTyping S) x).bind LTy.toMonoType?)) (LMonoTy.subst S mty) := by
    rw [hvar]
    exact hty0
  exact ⟨LMonoTy.subst S mty, rfl, hground, hdef, hty⟩

/-- An expression that is well typed at `mty`, with a substitution `S` applied to its
    annotations so that `S mty` is ground, evaluates in a store that conforms to the scopes with
    `S` applied. The value has type `S mty`. -/
theorem exprWellTyped_eval_progress_inst {C : LContext CoreLParams} {ts : TypeScopes}
    {e : Expression.Expr} {mty : LMonoTy} {f : Expression.Factory} {σ : CoreStore}
    (S : Subst) (he : ExprWellTyped C ts e mty) (hground : (LMonoTy.subst S mty).IsGround)
    (hs : StoreHasTyping f σ (ts.instVarTyping S)) :
    ∃ v, Expression.eval f σ (mapExprTys (LMonoTy.subst S) e) = some v ∧
      HasVal.valueOfTy f v (.forAll [] (LMonoTy.subst S mty)) :=
  eval_of_hasType f (ts.instVarTyping S) σ _ _ (he.hasType_inst S hground) hs

/-- A free variable without an annotation, declared in `ts` at a monotype, is bound in a store
    that conforms to `ts` with the substitution `S` applied, to a value of the monotype with
    `S` applied; and it evaluates to that value. -/
theorem fvar_evaluable {ts : TypeScopes} {m : ExpressionMetadata} {x : Expression.Ident}
    {mty : LMonoTy} {f : Expression.Factory} {σ : CoreStore} (S : Subst)
    (he : ts.find? x = some (.forAll [] mty)) (hs : StoreHasTyping f σ (ts.instVarTyping S)) :
    SemanticStore.varsDefined
        (· ∈ HasFvars.getFvars (P := Expression)
          (mapExprTys (LMonoTy.subst S) (LExpr.fvar m x none : Expression.Expr))) σ ∧
      ∃ v, Expression.eval f σ
          (mapExprTys (LMonoTy.subst S) (LExpr.fvar m x none : Expression.Expr)) = some v ∧
        HasVal.valueOfTy f v (.forAll [] (LMonoTy.subst S mty)) := by
  rw [mapExprTys_fvar_none]
  obtain ⟨v, hv, hvty⟩ := hs x _ (TypeScopes.instVarTyping_of_find? he)
  have hval : HasVal.value f v := LawfulHasVal.valueOfTy_isVal f v _ hvty
  refine ⟨?_, v, Lambda.LExpr.denoteEval_fvar hv hval, hvty⟩
  intro y hy
  have hyx : y = x := by
    have hy' : y ∈ LExpr.LExpr.getVars (LExpr.fvar m x none : Expression.Expr) := hy
    simpa only [LExpr.LExpr.getVars, List.mem_singleton] using hy'
  subst hyx
  simp only [hv, Option.isSome_some]

/-- A well-typed Boolean condition, with a substitution `S` applied to its annotations,
    evaluates in a store that conforms to the scopes with `S` applied to `true` or to `false`. -/
theorem eval_bool_progress_inst {C : LContext CoreLParams} {ts : TypeScopes}
    {e : Expression.Expr} {f : Expression.Factory} {σ : CoreStore}
    (S : Subst) (he : ExprWellTyped C ts e .bool)
    (hs : StoreHasTyping f σ (ts.instVarTyping S)) :
    ∃ v, Expression.eval f σ (mapExprTys (LMonoTy.subst S) e) = some v ∧
      (v = HasBool.ttVal f ∨ v = HasBool.ffVal f) := by
  have hb : LMonoTy.subst S LMonoTy.bool = LMonoTy.bool := LMonoTy.subst_bool S
  have hground : (LMonoTy.subst S LMonoTy.bool).IsGround := by
    rw [hb]
    simp only [LMonoTy.IsGround]
    rfl
  obtain ⟨v, hv, hvty⟩ := exprWellTyped_eval_progress_inst S he hground hs
  rw [hb] at hvty
  exact ⟨v, hv, valueOfTy_bool f v hvty⟩

end -- public section

end TypeSpec
end Core
