/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.TypingSpec
import all Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.LExprTypeEnvProps

/-! ## Properties of the typing relation

Typing does not read the rigid type variables of the context: replacing them
keeps statements, statement lists and procedure bodies well typed
(`StatementWellTyped.withRigid`, `StatementsWellTyped.withRigid`,
`ProcBodyWellTyped.withRigid`). -/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

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

end -- public section

end TypeSpec
end Core
