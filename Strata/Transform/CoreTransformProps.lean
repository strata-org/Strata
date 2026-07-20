/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemanticsProps

/-! # Transformation-generic store/run helpers

Small, transformation-agnostic store/run inversion lemmas shared across the
structured-to-unstructured passes (`projectStore_undef_at`,
`stmts_cons_terminal_inv`).  They depend only on the base statement semantics, so
they sit below every pass-specific correctness proof. -/

public section

namespace Imperative

variable {P : PureExpr}

/-! ## Store/run inversion helpers -/

/-- `projectStore` reverts to `none` on parent-undefined keys. -/
theorem projectStore_undef_at {P : PureExpr}
    {σ_parent σ_inner : SemanticStore P} {x : P.Ident}
    (h : σ_parent x = none) :
    projectStore σ_parent σ_inner x = none := by
  unfold projectStore
  simp [h]

/-- Split `.stmts (s :: rest) ρ ⟶* .terminal ρ'` into head and tail runs. -/
theorem stmts_cons_terminal_inv
    [HasFvar P] [HasBool P] [HasBoolOps P] [HasVal P] [HasFvars P] [HasVarsPure P P.Expr]
    {extendFactory : ExtendFactory P}
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))} {ρ ρ' : Env P}
    (h : StepStmtStar P (EvalCmd P) extendFactory (.stmts (s :: rest) ρ) (.terminal ρ')) :
    ∃ ρ_mid : Env P,
      StepStmtStar P (EvalCmd P) extendFactory (.stmt s ρ) (.terminal ρ_mid) ∧
      StepStmtStar P (EvalCmd P) extendFactory (.stmts rest ρ_mid) (.terminal ρ') := by
  cases h with
  | step _ _ _ h1 hr1 => cases h1; exact seq_reaches_terminal P (EvalCmd P) extendFactory hr1

end Imperative

end -- public section
