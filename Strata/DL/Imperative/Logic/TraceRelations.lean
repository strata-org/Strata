/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdTrace
public import Strata.Util.Relations
public import Strata.Util.ListUtils

/-! # Imperative trace relations

Definition module for the relations that compare event traces produced by
source and target semantics.  Their property proofs (reflexivity, monotonicity,
composition, and the `evalCmdE_replay_extends` replay lemma) live in the companion
`Strata.DL.Imperative.Logic.TraceRelationsProps`.

The event-level building blocks these relations are phrased over are not trace
concepts and live with the events they belong to: `Event.isTrueAssumeOrAssert`,
`EventArg.ExtendsEnv`, and `Event.ExtendsEnv` in
`Strata.DL.Imperative.CmdTrace`, which in turn builds on `StoreExtendsWith` from
`Strata.DL.Imperative.StoreRelations`.

Index of relations defined here:

* `TraceStuttersEnv` — trace correspondence permitting true assume/assert
  stuttering under allowed factories and classified target-only bindings.
* `TraceExtendsEnv` — the stutter-free, genuinely transitive refinement of
  `TraceStuttersEnv`: equal-length traces related event-by-event by
  `Event.ExtendsEnv`.
-/

namespace Imperative

public section

/-- Trace correspondence allowing target event snapshots to extend source
snapshots with additional bindings whose names satisfy `allowedVarName`.
Semantically true assertions and assumptions captured under a factory satisfying
`allowedFactory` may stutter on either side; covers may not stutter.

Register classification alone does not imply equal expression evaluation when
an expression reads a newly defined target register. Transporting assertion
validity through this relation under an abstract `ConditionInterp` therefore
requires two additional compatibility conditions: related event arguments must
have the same interpreted truth value, and every operationally true stuttered
condition captured under an allowed factory must hold in that interpretation. -/
inductive TraceStuttersEnv {P : PureExpr} [HasBool P]
    (allowedVarName : P.Ident → Prop) (allowedFactory : P.Factory → Prop) :
    Trace P → Trace P → Prop where
  | nil : TraceStuttersEnv allowedVarName allowedFactory [] []
  | lockstep :
      sourceEvent.ExtendsEnv allowedVarName targetEvent →
      TraceStuttersEnv allowedVarName allowedFactory source target →
      TraceStuttersEnv allowedVarName allowedFactory
        (sourceEvent :: source) (targetEvent :: target)
  | stutter_left :
      allowedFactory sourceEvent.condition.factory →
      sourceEvent.isTrueAssumeOrAssert →
      TraceStuttersEnv allowedVarName allowedFactory source target →
      TraceStuttersEnv allowedVarName allowedFactory (sourceEvent :: source) target
  | stutter_right :
      allowedFactory targetEvent.condition.factory →
      targetEvent.isTrueAssumeOrAssert →
      TraceStuttersEnv allowedVarName allowedFactory source target →
      TraceStuttersEnv allowedVarName allowedFactory source (targetEvent :: target)

/-- Pointwise (equal-length) trace correspondence: the two traces have equal
length and corresponding events are related by `Event.ExtendsEnv allowedVarName`.
This is the stutter-free refinement of `TraceStuttersEnv`: no assertion or
assumption may be inserted or dropped on either side. Because every step is
matched one-to-one, this relation is genuinely transitive, so composing
pointwise passes yields a single `TraceExtendsEnv` rather than a nested `RComp`.
Transitivity is only structural: transporting assertion validity additionally
requires `ConditionInterp.StableUnderExtendsEnv allowedVarName`, which ensures
that target-only bindings do not change the interpreted truth of a condition. -/
@[expose] def TraceExtendsEnv {P : PureExpr} (allowedVarName : P.Ident → Prop)
    (source target : Trace P) : Prop :=
  List.Rel₂ (Event.ExtendsEnv allowedVarName) source target

end -- public section
end Imperative
