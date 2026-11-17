/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.TypingSpec
public import Strata.Languages.Core.Typing.Spec.StatementTypeSpec
public import Strata.Languages.Core.CallWFProps
import all Strata.DL.Lambda.LExprTypeSpec
import all Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.LExprTypeEnvProps
import all Strata.Languages.Core.Statement
import all Strata.Languages.Core.Procedure
import all Strata.Languages.Core.Program
import all Strata.DL.Imperative.Procedure
import all Strata.Languages.Core.Typing.Spec.CmdTypeSpec

/-! ## Properties of the typechecker spec and of well-typedness

A well-typed program with structured bodies has well-formed calls:
`ProgramWellTyped.callsWellFormed`. The `withRigid` theorems, such as
`StatementsWellTyped.withRigid`, say well-typedness ignores the context's rigid type
variables. -/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

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
  | call _ _ _ _ _ _ hfind hwf hlhs hargs hlhsTy hequiv =>
    refine .call _ _ _ _ _ _ _ hfind hwf hlhs ?_ hlhsTy hequiv
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
  | .structured _ _ _ hss =>
    .structured _ _ _ (StatementsWellTyped.withRigid r hss)
  | .cfg c => .cfg c

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
    | .call _ _ _ _ _ _ _ _ hwf _ _ _ _ => by
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
    (hcfg : ∀ q md (g : DetCFG), Decl.proc q md ∈ ds → q.body = .cfg g →
      ∀ c ∈ q.callSites, WF.WFcallProp P c.procName c.args) :
    ∀ c ∈ ds.flatMap Decl.callSites, WF.WFcallProp P c.procName c.args := by
  induction h with
  | nil => simp
  | cons _ _ _ _ _ _ hd _ ih =>
    intro c hc
    simp only [List.flatMap_cons, List.mem_append] at hc
    refine hc.elim (fun hc => ?_)
      (ih (fun q md g hmem => hcfg q md g (List.mem_cons_of_mem _ hmem)) c)
    cases hd with
    | proc _ proc md hp =>
      simp only [Decl.callSites] at hc
      cases hbody : proc.body with
      | cfg g => exact hcfg proc md g (List.mem_cons_self ..) hbody c hc
      | structured _ =>
        simp only [Procedure.callSites] at hc
        rw [hbody] at hc
        have hbt := hp.bodyTyped
        rw [hbody] at hbt
        cases hbt with
        | structured _ _ _ hss => exact StatementsWellTyped.callsWF hss c hc
    | _ => simp [Decl.callSites] at hc

/-- A well-typed program has only well-formed calls, given that every call of its CFG bodies is
    well-formed. -/
theorem ProgramWellTyped.callsWellFormed {C : LContext CoreLParams} {ts : TypeScopes}
    {P : Program} (h : ProgramWellTyped C ts P)
    (hcfg : ∀ q md (g : DetCFG), Decl.proc q md ∈ P.decls → q.body = .cfg g →
      ∀ c ∈ q.callSites, WF.WFcallProp P c.procName c.args) :
    P.callsWellFormed := by
  obtain ⟨-, _, hds⟩ := h
  exact DeclsWellTyped.callsWF hds hcfg

end -- public section

end TypeSpec
end Core
