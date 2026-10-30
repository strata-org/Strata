/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.Simulation
public import Strata.Transform.Passive.ProgramProps
public import Strata.Transform.Passive.SimulationProps
public import Strata.DL.Imperative.BigStep.SemProps
import Strata.Util.ExceptProps

/-! # Obligation stores and typed loop-free stores

Vocabulary shared by the correctness proofs of the WP and SSA phases: the names an obligation
store binds (`DomIn`), and the requirement that the loop-free values a
list reads have their declared types (`TyOK`), which the obligation program's `init`s need
since they bind values of their declared types.  A failing trace splits along `++`
(`claim_split`).

Key definitions: `DomIn`, `TyOK`.

Key theorems: `claim_split`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iB : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iBo : HasBool P] [iFv : HasFvar P] [iSu : HasSubstFvar P] [iId : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iFs : HasFvars P] [iW : WPLang P]
  [iOp : HasOps P] [iLF : LawfulHasFvar P] [iLFs : LawfulHasFvars P] [iLV : LawfulHasVal P]
omit iB iLB iSu iId iLI iHa iFs iW iOp iLF iLFs iLV

/-! ## Obligation stores: bound names -/

/-- The obligation store binds only names of `D`. -/
@[expose] def DomIn (σ' : SemanticStore P) (D : List P.Ident) : Prop := ∀ x, (σ' x).isSome → x ∈ D


variable {F : P.Factory} {Lc S : List P.Ident} {ss B : PStmts P} {r : Outcome P}
  {X X' : Outcome P → Prop} {c : CmdExt P} {s : PStmt P} {rest : PStmts P}
  {σp σ σ' : SemanticStore P} {l : String} {e v : P.Expr} {md : MetaData P} {evs : List (Event P)}
  {o : Outcome P} {K K' : Outcome P → Prop} {t : AssertId P} {a b : List (Event P)}

/-! ## Typed loop-free stores and Boolean values -/

/-- The loop-free values of the variables in scope `S` that the continuation reads (`V`) are
    values of their declared types `tys`. -/
@[expose] def TyOK (F : P.Factory) (tys : Tys P) (S V : List P.Ident) (σ : SemanticStore P) :
    Prop :=
  ∀ x ∈ S, x ∈ V → ∀ ty, tys.get? x = some ty → ∀ w, σ x = some w → HasVal.valueOfTy F w ty

omit iDE iFv in
/-- The Boolean constants have the Boolean type. -/
theorem bool_valueOfTy (hb : v = tt ∨ v = ff) : HasVal.valueOfTy F v HasBool.boolTy :=
  hb.elim (· ▸ (HasBool.boolIsValOfTy F).1) (· ▸ (HasBool.boolIsValOfTy F).2)

/-! ## Splitting a failing trace -/

omit iDE iFv in
/-- If the events `a ++ b`, with `b` nonempty, claim a failure of `t`, then `a` is feasible
    and `b` claims it. -/
theorem claim_split (hb : b ≠ []) (h : Claim t (a ++ b)) :
    Trace.AssumptionsHold P evalInterp () a ∧ Claim t b := by
  obtain ⟨evs, e, he, hA, hf⟩ := h
  obtain ⟨b, e', rfl⟩ := (List.eq_nil_or_concat b).resolve_left hb
  obtain ⟨rfl, ⟨⟩⟩ := List.append_inj' (by simpa using he : a ++ b ++ [e'] = evs ++ [e]) rfl
  exact ⟨fun c hc => hA c (by simp [hc]), b, _, by simp, fun c hc => hA c (by simp [hc]), hf⟩

end -- public section

end WP
end Imperative
