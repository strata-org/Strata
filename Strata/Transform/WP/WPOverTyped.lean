/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverSpec
public import Strata.Transform.WP.WPOverEval

/-! # Typed loop-free expressions off the path

Off the loop-free path the guarded program still evaluates the loop-free expressions it lays
out inside conditionals (`set n := ite(κ, e, n)`, `assume κ ⟹ a`, the guard `κ ∧ c`): a
conditional evaluates only when both of its arms do.  A loop-free expression typed under the
typing predicate of a `TypedEval`, whose annotations agree with a typing `Γ` of the scope that
agrees with the final type maps (`TyCtx`), evaluates there to a value of its type
(`OffInv.resTy`).

Key theorems: `OffInv.resTy`. -/

namespace Imperative
namespace WP

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iSF : HasSubstFvar P] [iHI : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHFs : HasFvars P]
  [iWL : WPLang P] [iIL : WPIteLang P]
  [iOp : HasOps P] [iLF : LawfulHasFvar P] [iFs : LawfulHasFvars P] [iLV : LawfulHasVal P]
omit iIL
omit iFs iOp iLF iLB iLI iLV
variable {tE : TypedEval P}

variable {F : P.Factory} {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident}
  {Lc S V : List P.Ident} {Ex : P.Ident → Prop} {κ : RE P} {st : WSt P}
  {σL σL2 : SemanticStore P}

include iFs iLB iOp iLF in
/-- **A typed loop-free expression evaluates off the path.**  Off the loop-free path (`OffInv` at
    `st`, for the scope `S` and the variables `V` read later, of the guarded store `σL`), a
    renaming `ren` by the current WP names of an expression `e` of the scope read later, typed at
    `ty`, whose annotations agree with a typing `Γ` of the scope that agrees with the final type
    maps (`TyCtx`), resolves to values of type `ty` in every store `σL2` extending `σL`. -/
theorem OffInv.resTy (hF : WellFormedSemanticEvalBase F)
    (hO : OffInv F T Y Lc Ex st κ S V σL) (hC2 : WellFormedStore σL2 F)
    (h2 : ∀ m w, σL m = some w → σL2 m = some w) {Γ : VarTyping P} (hΓ : TyCtx T Y st S Γ)
    {e : P.Expr} {ty : P.Ty} {ren : List (P.Ident × P.Ident)} (he : tE.Typ e ty)
    (hann : Γ.annotates (HasFvars.getTypedFvars e))
    (hren : ∀ p ∈ ren, p.1 ∈ exprFV e ∧ curName st p.1 = some p.2)
    (hrd : ∀ y ∈ exprFV e, ∃ n, curName st y = some n ∧ (n = y ∨ (y, n) ∈ ren))
    (hS : ∀ y ∈ exprFV e, y ∈ S) (hV : ∀ y ∈ exprFV e, y ∈ V) :
    ResTy F σL2 T Y (.user e ren) ty := by
  have hfv : ∀ p ∈ HasFvars.getTypedFvars e, p.1 ∈ exprFV e := fun p hp =>
    mem_exprFV.2 (LawfulHasFvars.mem_getFvars_of_typed _ _ _ hp)
  have hb : ∀ y ∈ exprFV e, ∀ n, curName st y = some n → ∃ w, σL n = some w ∧ σL2 n = some w ∧
      ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty := fun y hy n hn =>
    (hO.defd y (hS y hy) (hV y hy) n hn).imp fun w h => ⟨h.1, h2 _ _ h.1, h.2⟩
  refine resTy_user tE hF (σ := fun y => (curName st y).bind σL) (fun y v h => ?_) hC2 he
    (fun p hp => ?_) (fun y hy hnr => ?_) fun p hp => ?_
  · cases hc : curName st y <;> simp only [hc, Option.bind_none, Option.bind_some,
      reduceCtorEq] at h
    exact hO.canonL _ _ h
  · obtain ⟨hp1, hc⟩ := hren p hp
    obtain ⟨w, hw, hw2, -⟩ := hb _ hp1 _ hc
    simp [hc, hw, hw2]
  · obtain ⟨n, hn, rfl | hm⟩ := hrd y hy
    · obtain ⟨w, hw, hw2, -⟩ := hb _ hy _ hn
      simp [hn, hw, hw2]
    · exact absurd rfl (hnr (y, n) hm)
  · obtain ⟨n, hn, -⟩ := hrd p.1 (hfv p hp)
    obtain ⟨w, hw, -, hwt⟩ := hb _ (hfv p hp) n hn
    exact ⟨w, by simp [hn, hw], hwt _ (hΓ p.1 (hS _ (hfv p hp)) p.2 (hann _ _ hp) n hn)⟩

end -- public section

end WP
end Imperative
