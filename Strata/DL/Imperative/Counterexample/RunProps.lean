/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Counterexample.Run
public import Strata.DL.Imperative.InterpreterCallEmbed
import all Strata.DL.Imperative.Counterexample.Run

/-! # Properties of level-(a) counterexamples and back-link outcomes

Key theorems:
- `BackLinkOutcome.isFail_iff`: the executable `isFail` flag holds exactly when there
  are no unconfirmed slices and a claim is present.
- `Calls.isTopLevelAt_embedCexA`: embedding a counterexample into the call-aware
  command type keeps it at the top level of the embedded statements.
-/

namespace Imperative

public section

/-- The executable `isFail` flag holds exactly when there are no unconfirmed slices
    and a claim is present. -/
theorem BackLinkOutcome.isFail_iff {P : PureExpr} [InterpLang P] {CmdT : Type}
    (o : BackLinkOutcome P CmdT) :
    o.isFail = true ↔ o.slices = [] ∧ o.claim.isSome := by simp [isFail]

namespace Calls

variable {P : PureExpr} [InterpLang P]

/-- A counterexample at the top level of `stmts` (`isTopLevelAt`) stays at the top level
    of the embedded statements after its embedding into the call-aware command type
    (`embedCexA`, `embedBlock`). -/
theorem isTopLevelAt_embedCexA {stmts : List (Stmt P (Cmd P))} {cex : CexA P (Cmd P)}
    (h : isTopLevelAt stmts cex) : isTopLevelAt (embedBlock stmts) (embedCexA cex) := by
  rcases cex with ⟨_ | _ | _ | _ | _ | _ | _, _⟩ <;> first | exact h.elim | exact congrArg _ h

end Calls

end -- public section

end Imperative
