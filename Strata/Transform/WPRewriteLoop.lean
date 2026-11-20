/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WPLoop
public import Strata.Transform.GuardProp
public import Strata.Transform.CtorFold
public import Strata.Transform.BetaReduce

/-! # The rewrite loop of `--vcgen wp`

After the SSA phase, each procedure body of the obligation program is rewritten by a *round* of
six passes, in this order: beta reduction (`Core.BetaReduce.betaReduceBlock`), guard
forwarding, the inlining of single-use definitions at `Core.WPLoop.loopNorm` and the erasure of
unread definitions (the three of `Core.WPLoop.wpRound`), guard propagation
(`Imperative.GuardProp.guardProp`) and the constructor fold (`Core.CtorFold.ctorFold`).  Each
of the last five passes can create work for each of the others, and beta reduction creates work
for all five; the inlining and the constructor fold can create a redex only by turning a
conditional whose arms are functions into one of its arms.  The loop repeats the round on each
body until a round leaves the body unchanged, so when it stops that way its output is a fixpoint
of every pass, beta reduction included.

The loop's fuel is that of `Core.WPLoop.wpLoopBody`: one more round than the number of
statements and expression nodes of the body at loop entry (`Core.WPLoop.blockSize`).  A loop
that runs out of fuel returns the body after the last round and reports it (the statistics
counter `wpLoop.fuelExhausted`).  The result is always the output of some number of rounds,
whatever the fuel.

The pipeline phase runs the round through `roundF`, whose middle three passes are
`Core.WPLoop.wpRoundF`, equal to `Core.WPLoop.wpRound (Core.WPLoop.loopNorm fac)`.

Key definitions: `Core.WPRewriteLoop.round`,
`Core.WPRewriteLoop.roundF`, `Core.WPRewriteLoop.loopBody`, `Core.WPRewriteLoop.loopBodyF`,
`Core.wpRewriteLoopPipelinePhase`. -/

namespace Core

public section

namespace WPRewriteLoop

open Imperative

/-- **One round of the loop** at the factory `fac`: beta reduction, guard forwarding, the
    inlining of single-use definitions at `Core.WPLoop.loopNorm fac`, the erasure of unread
    definitions, guard propagation, then the constructor fold. -/
@[expose] def round (fac : Lambda.Factory CoreLParams) (ss : Statements) : Statements :=
  CtorFold.ctorFold fac (GuardProp.guardProp (WPLoop.wpRound (WPLoop.loopNorm fac)
    (BetaReduce.betaReduceBlock ss)))

/-- `round fac` with its middle three passes run by `Core.WPLoop.wpRoundF fac`. -/
@[expose] def roundF (fac : Lambda.Factory CoreLParams) (ss : Statements) : Statements :=
  CtorFold.ctorFold fac (GuardProp.guardProp (WPLoop.wpRoundF fac (BetaReduce.betaReduceBlock ss)))

/-- **The loop on a procedure body**, with the fuel of `Core.WPLoop.wpLoopBody`: the rewritten
    body, the number of rounds run, and whether the fuel ran out. -/
@[expose] def loopBody (fac : Lambda.Factory CoreLParams) (ss : Statements) :
    Statements × Nat × Bool :=
  WPLoop.loopFix (round fac) (WPLoop.blockSize ss + 1) ss 0

/-- `loopBody fac` with the rounds run by `roundF fac`. -/
@[expose] def loopBodyF (fac : Lambda.Factory CoreLParams) (ss : Statements) :
    Statements × Nat × Bool :=
  WPLoop.loopFix (roundF fac) (WPLoop.blockSize ss + 1) ss 0

end WPRewriteLoop

/-- The rewrite loop pipeline phase of `--vcgen wp`: repeats beta reduction, guard forwarding,
    the inlining of single-use definitions, the erasure of unread definitions, guard propagation
    and the constructor fold on each procedure body until a round leaves the body unchanged
    (`Core.WPLoop.wpLoopProgramWith` with `Core.WPRewriteLoop.loopBodyF`), the inlining and the
    fold normalizing under the factory `wpFactory moreFns` of the program; it fails with the
    error of that factory when it fails.  It requires what its components require: an
    obligation program (`hasObligationForm`, `staticSingleAssignment`, no calls, loops or CFG
    bodies) whose function preconditions are checked (`noPrecondsFromFuncs`) and that is
    type-checked (`typeAnnotated`).  It does not establish `noBetaRedexes`: it rewrites only
    procedure bodies, so function bodies and axioms keep their redexes, and `--vcgen wp` runs
    `betaReducePipelinePhase` after it.  Each component keeps the facts listed in `preserves`. -/
def wpRewriteLoopPipelinePhase
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) : PipelinePhase :=
  modelPreservingPipelinePhase "wpLoop"
    (fun program => do
      let fac ← Transform.liftDiag (wpFactory moreFns program)
      WPLoop.wpLoopProgramWith (WPRewriteLoop.loopBodyF fac) program)
    (requires := factSet![.noCFGBodies, .noCalls, .noLoops, .staticSingleAssignment,
                         .noPrecondsFromFuncs, .hasObligationForm, .typeAnnotated])
    (establishes := factSet![])
    (preserves := obligationRewritePreserves)

end -- public section

end Core
