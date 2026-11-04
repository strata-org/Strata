/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.LangDef

/-! # Properties of the Imperative initial-environment gates

Key results:
  * `BlockInitEnvWF.generatedNamesFresh` — no name under a reserved prefix is
    defined in a block-well-formed initial store. -/

public section

namespace Imperative

namespace Logic

/-- No name under a reserved prefix is defined in a block-well-formed initial
store: this is the contrapositive of `reservedFresh`. -/
theorem BlockInitEnvWF.generatedNamesFresh {P : PureExpr} [HasBool P] [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasSubstFvar P]
    [HasIdent P] [HasOps P] [DecidableEq P.Ident]
    {CmdT : Type} [HasVarsImp P CmdT] [HasOpsImp P CmdT]
    [HasInitTypesImp P CmdT] [HasTypedVarsImp P CmdT]
    {params : InitEnvWFParams P} {ss : List (Stmt P CmdT)} {ρ : Env P}
    (h : BlockInitEnvWF params ss ρ) :
    Env.varsUndefined (P := P)
      (fun name => ∃ pfx ∈ params.prefixIdents,
        pfx.toList.isPrefixOf name.toList) ρ := by
  intro ident hident
  obtain ⟨name, ⟨pfx, hpfx, hprefix⟩, rfl⟩ := hident
  cases hstore : ρ.store (HasIdent.ident (P := P) name) with
  | none => rfl
  | some value =>
    exact absurd hprefix
      (h.reservedFresh (HasIdent.ident (P := P) name)
        (by rw [hstore]; rfl) name rfl pfx hpfx)

end Logic

end Imperative

end -- public section
