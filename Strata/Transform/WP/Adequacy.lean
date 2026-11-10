/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BigStep.Adequacy
public import Strata.Transform.Passive.SimulationProps

/-! # Well-scoped lists are loop-free

A well-scoped loop-free list (`Block.WellScoped`) has no loop at any depth (`wfl_noLoops`).

Key theorems: `wfl_noLoops`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [HasBool P] [HasFvar P]
  [HasFvars P]

variable {F : P.Factory} {Lc : List P.Ident}

omit [HasBool P] [HasFvar P] in
/-- A well-scoped loop-free list (`Block.WellScoped`) has no loop at any depth. -/
theorem wfl_noLoops : ∀ {S : List P.Ident} {ss : PStmts P}, Block.WellScoped Lc S ss →
    Block.noLoops ss = true := by
  intro S ss h
  induction S, ss using Block.WellScoped.induct
    (motive_2 := fun S s => Stmt.WellScoped Lc S s → Stmt.noLoops s = true) <;>
    grind [Block.WellScoped, Stmt.WellScoped, Block.noLoops, Stmt.noLoops, Block.allSubstmts,
      Stmt.allSubstmts, Stmt.isNotLoop]

end -- public section

end WP
end Imperative
