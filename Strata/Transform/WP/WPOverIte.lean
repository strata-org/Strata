/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverIteLaid
public import Strata.Transform.WP.WPOverIteReal

/-! # The simulation through deterministic `ite`s

The walk of a deterministic `ite` is the laid-out walk when an obligation follows it and the
real-branch walk otherwise, so it has the simulation property (`Spec`) when the walks of its arms
have it.

Key theorems: `stmtSpec_ite`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P]
  [HasFvar P] [HasSubstFvar P] [HasIdent P] [LawfulHasIdent P] [Hashable P.Ident] [HasFvars P]
  [WPLang P] [iIL : WPIteLang P] [HasOps P] [LawfulHasFvar P] [LawfulHasFvars P] [LawfulHasVal P]
omit iIL
variable {tE : TypedEval P}

include iIL in
/-- The walk of a deterministic `ite` has the simulation property when the walks of its arms
    (at the same depth, under every context and obligation bit) have it. -/
theorem stmtSpec_ite {F : P.Factory} (hF : WellFormedSemanticEvalBase F) {Lc : List P.Ident}
    {κ : RE P} {d : Nat} {f : Bool} {c : P.Expr} {tss ess : PStmts P} (md : MetaData P)
    (hT : ∀ κ' fE, ListSpec F tE Lc κ' d fE tss) (hE : ∀ κ' fE, ListSpec F tE Lc κ' d fE ess) :
    StmtSpec F tE Lc κ d f (.ite (.det c) tss ess md) := by
  cases f <;> rw [StmtSpec, wpStmt]
  · exact iteRealSpec hF md (hT .top false) (hE .top false)
  · exact iteLaidSpec hF md (hT · true) (hE · true)

end -- public section

end WP
end Imperative
