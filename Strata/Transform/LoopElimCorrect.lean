/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.LoopElim
import Strata.Transform.CoreSpecification
import Strata.DL.Imperative.StmtSemanticsSmallStep
import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Util.Relations

/-! # Loop-Elimination Transformation Correctness

The top-level theorem is `loopElim_overapproximatesAggressive`: the
loop-eliminated program aggressively overapproximates the original.

For each source execution reaching terminal `ρ'`, the transformed program
either reaches the same terminal `ρ'` (exact simulation), or terminates at
some `ρ''` with `hasFailure = true` (an invariant VC failed).
-/

namespace Core.LoopElim

open Imperative Specification Core Imperative.LoopElim

variable (π : String → Option Procedure)
variable (φ : CoreEval → PureFunc Expression → CoreEval)

private abbrev CoreStar := StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)

/-! ## Projecting removeLoopsM results -/

noncomputable def stmtResult (σ : StringGenState) (s : Statement) : Statement :=
  (StateT.run (Stmt.removeLoopsM s) σ).fst.snd

noncomputable def blockResult (σ : StringGenState) (ss : Statements) : Statements :=
  (StateT.run (Block.removeLoopsM ss) σ).fst.snd

noncomputable def stmtPostState (σ : StringGenState) (s : Statement) : StringGenState :=
  (StateT.run (Stmt.removeLoopsM s) σ).snd

/-! ## Top-level theorem -/

/-- Loop elimination aggressively overapproximates: for each source
    execution reaching terminal `ρ'`, the transformed program either
    reaches the same `ρ'` or terminates with `hasFailure = true`.
    Similarly for exiting configurations. -/
theorem loopElim_overapproximatesAggressive
    (hwf_ext : WFEvalExtension φ) (σ : StringGenState) :
    Transform.OverapproximatesAggressively
      (Specification.Lang.core π φ)
      (Specification.Lang.core π φ)
      (fun s => some (stmtResult σ s)) := by
  sorry

end Core.LoopElim
