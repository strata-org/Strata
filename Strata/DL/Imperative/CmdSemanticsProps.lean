/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Util.ListUtils
public import Strata.DL.Util.Nodup
import all Strata.DL.Util.ListUtils
import all Strata.DL.Util.Nodup

/-! # Generic property lemmas for `Imperative.CmdSemantics`

  Pure-Imperative property lemmas about `substDefined` / `substNodup`
  that do not depend on any specific `PureExpr` instantiation (e.g.,
  Core).  Live here rather than in `Strata.Transform.SubstProps`
  because they are reusable across any transform that introduces fresh
  variables and substitutes them. -/

public section

namespace Imperative

/-- The tail of a `substDefined` cons-list still satisfies `substDefined`. -/
theorem subst_defined_tail
    {P : PureExpr} {σ σ' : SemanticStore P}
    {h : P.Ident × P.Ident}
    {t : List (P.Ident × P.Ident)} :
    Imperative.substDefined σ σ' (h :: t) →
    Imperative.substDefined σ σ' t := by
  intros Hsubst k1 k2 Hin
  apply Hsubst
  exact List.mem_cons_of_mem h Hin

/-- The tail of a `substNodup` cons-list still satisfies `substNodup`. -/
theorem subst_nodup_tail
    {P : PureExpr}
    {h : P.Ident × P.Ident}
    {t : List (P.Ident × P.Ident)} :
    Imperative.substNodup (h :: t) →
    Imperative.substNodup t := by
  intros Hsubst
  simp [Imperative.substNodup] at *
  exact (List.nodup_cons.mp (nodup_middle Hsubst.right)).right

end Imperative

end -- public section
