/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init

/-! # Marker assumptions of the abstraction phases

An abstraction phase (call elimination, insertion of loop invariant checks, loop elimination,
CFG loop elimination)
replaces code by an over-approximation and labels the assumptions it places on the paths through
that over-approximation with a reserved prefix. The phase's model check reads these labels in an
obligation's path condition (`obligationHasLabelPrefix`): a counterexample on such a path may come
from the over-approximation, not from an execution. A *marker* is an assumption with such a label.
Each phase rejects a program that already has a label with its prefix (`rejectMarkerLabels`), so
the only assumptions with that prefix are those it generates. A front end that models code Strata
does not see marks each call to such a model in the same way (`externalAssumePrefix`), and
reserves that prefix in its own input.

A marker must therefore stay in the path condition even when its condition simplifies to `true`;
symbolic evaluation keeps it (`EvalContext.keepsTrueAssume`). The prefixes are defined here, where
the phases and the evaluator can both import them. -/

namespace Core

public section

/-- Label prefix of the marker assumptions of call elimination: the postcondition assumptions of
    a call. -/
def CallElim.callElimAssumePrefix : String := "$__callElimAssume_"

/-- Label prefix of the marker assumption of call elimination on a call that havocs outputs of a
    callee without postconditions: the assumption `true` after the havocs. Only call elimination
    generates labels with it, so, unlike a postcondition assumption, whose label is derived from
    the postcondition's, such a marker's condition is always `true`. -/
def CallElim.callElimHavocPrefix : String := "$__callElimHavoc_"

/-- Label prefix of the postcondition assumptions of a call to an opaque procedure. They are not
    markers, so this prefix is not one of `abstractionMarkerPrefixes`: the contract of an opaque
    procedure is its call semantics, so a path through the call's replacement is a path of the
    program. `rejectMarkerLabels` does not reserve it, so a written label that starts with it is
    accepted. -/
def CallElim.callElimPostPrefix : String := "callElimPost_"

/-- Label prefix of the marker assumptions of the insertion of loop invariant checks: the
    invariant and measure assumptions it inserts. -/
def insertLoopInvAssumePrefix : String := "$__insertLoopInvAssume_"

/-- Label prefix of the marker assumptions of loop elimination: the assumptions of the guard and
    of its negation around the arbitrary iteration. -/
def loopElimAssumePrefix : String := "$__loopElimAssume_"

/-- Label prefix of the marker assumptions of CFG loop elimination: the assumptions of its cut of
    each loop, before and after the havoc of the loop's variables. -/
def CFGLoopElim.cfgLoopElimAssumePrefix : String := "$__cfgLoopElimAssume_"

/-- Label prefix of the marker assumptions of a front end's modelling of code that Strata does not
    see: the assumption `true` that a front end places right after a call to a procedure without a
    body that models such code (Cortex's lowering to Core, `Cortex.ToCore`). The call itself means
    the callee's contract, so call elimination replaces it exactly; the marker records that the
    contract is a model of unseen code, so a counterexample through the call may come from the
    model, not from an execution of that code. -/
def externalAssumePrefix : String := "$__externalAssume_"

/-- The label prefixes of the marker assumptions of the abstraction phases: the two of call
    elimination, those of the insertion of loop invariant checks, of loop elimination, of CFG loop
    elimination and of a front end's modelling of unseen code. -/
def abstractionMarkerPrefixes : List String :=
  [CallElim.callElimAssumePrefix, CallElim.callElimHavocPrefix, insertLoopInvAssumePrefix,
   loopElimAssumePrefix, CFGLoopElim.cfgLoopElimAssumePrefix, externalAssumePrefix]

/-- Whether `label` is the label of a marker assumption of an abstraction phase: it starts with
    one of `abstractionMarkerPrefixes`. -/
def isAbstractionMarker (label : String) : Bool :=
  abstractionMarkerPrefixes.any fun pfx => label.startsWith pfx

end -- public section

end Core
