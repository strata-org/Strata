/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.WellTyped

/-! # Properties of well-typed statement lists

`Block.condsTyped` of a concatenation of statement lists is that of its parts.

Key theorems: `Block.condsTyped_append`. -/

namespace Imperative

public section

variable {P : PureExpr} [HasBool P]

/-- `Block.condsTyped` of a concatenation is that of its parts. -/
theorem Block.condsTyped_append {Typ : P.Expr → P.Ty → Prop} :
    ∀ (a b : List (Stmt P (CmdExt P))),
      Block.condsTyped Typ (a ++ b) ↔ Block.condsTyped Typ a ∧ Block.condsTyped Typ b
  | [], _ => by simp [Block.condsTyped]
  | s :: a, b => by simp [Block.condsTyped, Block.condsTyped_append a b, and_assoc]

end -- public section

end Imperative
