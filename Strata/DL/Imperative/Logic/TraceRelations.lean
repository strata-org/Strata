/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdTrace
public import Strata.DL.Imperative.CmdTraceWF
public import Strata.DL.Imperative.Logic.TraceInterp
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

* `Trace.StuttersEnv` — trace correspondence permitting true assume/assert
  stuttering under allowed factories and classified target-only bindings.
* `TraceExtendsEnv` — the stutter-free, genuinely transitive refinement of
  `Trace.StuttersEnv`: equal-length traces related event-by-event by
  `Event.ExtendsEnv`.
* `EventArg.WithWF R` — an event-argument relation `R` strengthened with
  free-variable store agreement and evaluator evidence on both snapshots, with
  its event and trace liftings `Event.WithWF` and `Trace.WithWF`. The
  structured transforms relate their traces by
  `Trace.WithWF (EventArg.ExtendsEnv Extra)`.
* `Trace.WeakensAssumes` — the target trace is the source trace with each event replaced by
  a counterpart under a condition interpretation (`Event.WeakensAssume`: the same assertion
  or cover, or a weaker assumption), and any assumption possibly dropped.
* `Trace.MayDropEvents` — the target trace is a sublist of the source trace: it keeps some
  source events in order and drops the others; `Trace.InsertsTrueAssumes` — the target trace
  is the source trace with operationally true assumptions inserted.
* `Trace.PreservesLastEvent R` — the target trace ends with the last source event, after
  events related by `R` to those before it; `Trace.HasExtraEvents R Extra` — the target trace
  is one related by `R` followed by extra events satisfying `Extra`.
* `Trace.ReflectsLastAssertion` — a condition on a trace relation: a source trace ending with
  an assertion is related only to target traces containing it after assumptions implied by
  those before it in the source.
* `Trace.ImpliesAssertValidity` — the validity of every assertion of the target trace implies
  that of every assertion of the source trace; `Trace.ImpliesReachability` — the reachability
  of the source trace implies that of the target trace.
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
inductive Trace.StuttersEnv {P : PureExpr} [HasBool P]
    (allowedVarName : P.Ident → Prop) (allowedFactory : P.Factory → Prop) :
    Trace P → Trace P → Prop where
  | nil : Trace.StuttersEnv allowedVarName allowedFactory [] []
  | lockstep :
      sourceEvent.ExtendsEnv allowedVarName targetEvent →
      Trace.StuttersEnv allowedVarName allowedFactory source target →
      Trace.StuttersEnv allowedVarName allowedFactory
        (sourceEvent :: source) (targetEvent :: target)
  | stutter_left :
      allowedFactory sourceEvent.condition.factory →
      sourceEvent.isTrueAssumeOrAssert →
      Trace.StuttersEnv allowedVarName allowedFactory source target →
      Trace.StuttersEnv allowedVarName allowedFactory (sourceEvent :: source) target
  | stutter_right :
      allowedFactory targetEvent.condition.factory →
      targetEvent.isTrueAssumeOrAssert →
      Trace.StuttersEnv allowedVarName allowedFactory source target →
      Trace.StuttersEnv allowedVarName allowedFactory source (targetEvent :: target)

/-- Pointwise (equal-length) trace correspondence: the two traces have equal
length and corresponding events are related by `Event.ExtendsEnv allowedVarName`.
This is the stutter-free refinement of `Trace.StuttersEnv`: no assertion or
assumption may be inserted or dropped on either side. Because every step is
matched one-to-one, this relation is genuinely transitive, so composing
pointwise passes yields a single `TraceExtendsEnv` rather than a nested `RComp`.
Transitivity is only structural: transporting assertion validity additionally
requires `ConditionInterp.StableUnderExtendsEnv allowedVarName`, which ensures
that target-only bindings do not change the interpreted truth of a condition. -/
@[expose] def TraceExtendsEnv {P : PureExpr} (allowedVarName : P.Ident → Prop)
    (source target : Trace P) : Prop :=
  List.Rel₂ (Event.ExtendsEnv allowedVarName) source target

/-- An event-argument relation `R` strengthened with the semantic evidence
needed to transport the captured expression's value: the stores agree on the
expression's free variables, both stores hold only values, and the source
factory's evaluator respects free-variable store agreement. -/
structure EventArg.WithWF {P : PureExpr} [HasVal P] [HasFvars P]
    (R : EventArg P → EventArg P → Prop) (source target : EventArg P) : Prop where
  rel : R source target
  store_fv : StoreAgreesOnFvars source.store target.store source.expr
  sourceStoreWF : WellFormedStore source.store source.factory
  targetStoreWF : WellFormedStore target.store target.factory
  exprCongr : WellFormedSemanticEvalExprCongr source.factory

/-- Same-kind event matching induced by `EventArg.WithWF R`. -/
abbrev Event.WithWF {P : PureExpr} [HasVal P] [HasFvars P]
    (R : EventArg P → EventArg P → Prop) : Event P → Event P → Prop :=
  Event.Matches (EventArg.WithWF R)

/-- Pointwise `Event.WithWF R` matching for traces. -/
abbrev Trace.WithWF {P : PureExpr} [HasVal P] [HasFvars P]
    (R : EventArg P → EventArg P → Prop) : Trace P → Trace P → Prop :=
  List.Rel₂ (Event.WithWF (P := P) R)

section WeakensAssumes

variable {P : PureExpr}

/-- An event of a source trace and its counterpart in a target trace, under the interpretation
    `I`: an assertion, or a cover, with the same label and metadata whose condition holds in
    exactly the worlds the source's holds in; or an assumption with the same label and metadata
    whose condition holds in every world the source's holds in. -/
@[expose] def Event.WeakensAssume (I : ConditionInterp P) : Event P → Event P → Prop
  | .assert a, .assert b | .cover a, .cover b =>
    a.label = b.label ∧ a.metadata = b.metadata ∧ ∀ w, I.holds w a ↔ I.holds w b
  | .assume a, .assume b =>
    a.label = b.label ∧ a.metadata = b.metadata ∧ ∀ w, I.holds w a → I.holds w b
  | _, _ => False

/-- `target` is `source` with each event replaced by a counterpart (`Event.WeakensAssume I`),
    except that any assumption of `source` may be missing from `target`.  The order is kept and
    `target` has no other event, so every assertion of `source` that fails under `I` after
    assumptions holding under `I` has a counterpart in `target`, with the same label, that fails
    after assumptions holding under `I`. -/
inductive Trace.WeakensAssumes (I : ConditionInterp P) : Trace P → Trace P → Prop where
  | nil : Trace.WeakensAssumes I [] []
  | cons {e e' : Event P} {t t' : Trace P} :
      Event.WeakensAssume I e e' → Trace.WeakensAssumes I t t' →
      Trace.WeakensAssumes I (e :: t) (e' :: t')
  | dropAssume {a : EventArg P} {t t' : Trace P} :
      Trace.WeakensAssumes I t t' → Trace.WeakensAssumes I (.assume a :: t) t'

end WeakensAssumes

section DropsAndInserts

variable {P : PureExpr}

/-- `target` keeps some events of `source`, unchanged and in order, and drops the others, of any
    kind: `target` is a sublist of `source` (`List.Sublist`).  Every assumption of `target` is
    one of `source`.  Loop elimination relates its traces this way, up to inserted true
    assumptions (`Trace.InsertsTrueAssumes`): the target replays one iteration of each loop,
    dropping the events, assertions included, of the others. -/
abbrev Trace.MayDropEvents (source target : Trace P) : Prop :=
  target.Sublist source

/-- `target` is `source` with assumptions inserted whose conditions evaluate to `true` under a
    factory satisfying `allowedFactory`.  Loop elimination inserts the assumption of a loop
    guard where it holds. -/
inductive Trace.InsertsTrueAssumes [HasBool P] (allowedFactory : P.Factory → Prop) :
    Trace P → Trace P → Prop where
  | nil : Trace.InsertsTrueAssumes allowedFactory [] []
  | keep {e : Event P} {t t' : Trace P} :
      Trace.InsertsTrueAssumes allowedFactory t t' →
      Trace.InsertsTrueAssumes allowedFactory (e :: t) (e :: t')
  | assume {a : EventArg P} {t t' : Trace P} :
      allowedFactory a.factory →
      P.eval a.factory a.store a.expr = some (HasBool.ttVal a.factory) →
      Trace.InsertsTrueAssumes allowedFactory t t' →
      Trace.InsertsTrueAssumes allowedFactory t (.assume a :: t')

/-- `target` ends with the last event of `source`, after events related by `R` to those before
    it in `source`; the empty trace is related only to itself.  So an assertion ending `source`
    ends `target`. -/
@[expose] def Trace.PreservesLastEvent (R : Trace P → Trace P → Prop)
    (source target : Trace P) : Prop :=
  source = [] ∧ target = [] ∨
  ∃ pre pre' e, source = pre ++ [e] ∧ target = pre' ++ [e] ∧ R pre pre'

/-- `target` is a trace related to `source` by `R` followed by extra events satisfying
    `Extra`. -/
@[expose] def Trace.HasExtraEvents (R : Trace P → Trace P → Prop) (Extra : Trace P → Prop)
    (source target : Trace P) : Prop :=
  ∃ target₁ extra, target = target₁ ++ extra ∧ R source target₁ ∧ Extra extra

end DropsAndInserts

section TraceInterpRelations

variable {P : PureExpr}

/-- A trace relation `R` *reflects last assertions* under `I` when a source trace ending with
    an assertion is related only to target traces that contain that assertion after assumptions
    holding in every world where those before it in the source hold.  Such a relation carries
    the validity of an assertion occurrence back from the target to the source; see
    `Transform.overapproximatesTraces2UptoWhen_assertValid_of_reflectsLastAssertion`. -/
@[expose] def Trace.ReflectsLastAssertion (I : ConditionInterp P)
    (R : Trace P → Trace P → Prop) : Prop :=
  ∀ pre c target, R (pre ++ [.assert c]) target →
    ∃ pre' post, target = pre' ++ .assert c :: post ∧
      ∀ world, Trace.AssumptionsHold P I world pre → Trace.AssumptionsHold P I world pre'

/-- Under `I`, the validity of every assertion of `target` implies that of every assertion of
    `source`: a target trace whose assertions are all valid is related only to source traces
    whose assertions are all valid. -/
@[expose] def Trace.ImpliesAssertValidity (I : ConditionInterp P) (source target : Trace P) :
    Prop :=
  Trace.AssertionsValid P I target → Trace.AssertionsValid P I source

/-- Under `I`, the reachability of `source` implies that of `target`: some world satisfies
    every assumption of `target` when some world satisfies every assumption of `source`. -/
@[expose] def Trace.ImpliesReachability (I : ConditionInterp P) (source target : Trace P) :
    Prop :=
  Trace.Reachable P I source → Trace.Reachable P I target

end TraceInterpRelations

end -- public section
end Imperative
