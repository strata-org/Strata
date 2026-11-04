/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.Program

/-! # Typed loop-free stores

Vocabulary shared by the correctness proofs of the WP and SSA phases: the requirement that the
loop-free values a list reads have their declared types (`TyOK`), which the obligation program's
`init`s need since they bind values of their declared types, and the Boolean constants have the
Boolean type (`bool_valueOfTy`).

Key definitions: `TyOK`.

Key theorems: `bool_valueOfTy`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iB : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iBo : HasBool P] [iFv : HasFvar P] [iSu : HasSubstFvar P] [iId : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iFs : HasFvars P] [iW : WPLang P]
  [iOp : HasOps P] [iLF : LawfulHasFvar P] [iLFs : LawfulHasFvars P] [iLV : LawfulHasVal P]
omit iB iLB iSu iId iLI iHa iFs iW iOp iLF iLFs iLV

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
theorem bool_valueOfTy {v : P.Val} (hb : v = HasBool.ttVal F ∨ v = HasBool.ffVal F) :
    HasVal.valueOfTy F v HasBool.boolTy :=
  hb.elim (· ▸ (HasBool.boolIsValOfTy F).1) (· ▸ (HasBool.boolIsValOfTy F).2)

end -- public section

end WP
end Imperative
