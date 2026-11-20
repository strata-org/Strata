/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init

/-! # Marker assumptions of the abstraction phases

An abstraction phase (call elimination, insertion of loop invariant checks, loop elimination)
replaces code by an over-approximation and labels the assumptions it places on the paths through
that over-approximation with a reserved prefix. The phase's model check reads these labels in an
obligation's path condition (`obligationHasLabelPrefix`): a counterexample on such a path may come
from the over-approximation, not from an execution. A *marker* is an assumption with such a label.
Each phase rejects a program that already has a label with its prefix (`rejectMarkerLabels`), so
the only assumptions with that prefix are those it generates.

A marker must therefore stay in the path condition even when its condition simplifies to `true`;
symbolic evaluation keeps it (`EvalContext.keepsTrueAssume`). The prefixes are defined here, where
the phases and the evaluator can both import them. -/

namespace Core

public section

/-- Label prefix of the marker assumptions of call elimination: the postcondition assumptions of
    a call. -/
def CallElim.callElimAssumePrefix : String := "$__callElimAssume_"

/-- Label prefix of the marker assumptions of the insertion of loop invariant checks: the
    invariant and measure assumptions it inserts. -/
def insertLoopInvAssumePrefix : String := "$__insertLoopInvAssume_"

/-- Label prefix of the marker assumptions of loop elimination: the assumptions of the guard and
    of its negation around the arbitrary iteration. -/
def loopElimAssumePrefix : String := "$__loopElimAssume_"

/-- The label prefixes of the marker assumptions of the abstraction phases: those of call
    elimination, of the insertion of loop invariant checks and of loop elimination. -/
def abstractionMarkerPrefixes : List String :=
  [CallElim.callElimAssumePrefix, insertLoopInvAssumePrefix, loopElimAssumePrefix]

/-- Whether `label` is the label of a marker assumption of an abstraction phase: it starts with
    one of `abstractionMarkerPrefixes`. -/
def isAbstractionMarker (label : String) : Bool :=
  abstractionMarkerPrefixes.any fun pfx => label.startsWith pfx

end -- public section

end Core
