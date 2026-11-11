/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.TraceRelations
public import Strata.DL.Imperative.Logic.TraceInterpProps
public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CmdSemanticsProps
public import Strata.DL.Imperative.StmtSemanticsProps
public import Strata.Util.Relations
public import Strata.Util.ListUtils

/-! # Properties of the Imperative trace relations

Companion to `Strata.DL.Imperative.Logic.TraceRelations`, which carries the
compact definitions of the trace relations `Trace.StuttersEnv` /
`TraceExtendsEnv`; the event-level relations they build on,
`EventArg.ExtendsEnv` / `Event.ExtendsEnv`, are defined in
`Strata.DL.Imperative.CmdTrace`.  This module collects the property proofs for
all four. The store- and environment-level laws live
with the semantics they belong to: the command-level `StoreAgreement` and
`StoreExtendsWith` laws in `Strata.DL.Imperative.StoreRelationsProps`, and the
statement-level `StoreExtendsWith.projectStore`,
`StoreAgreement.of_projectStore`, and `Env.ExtendsWith.refl` / `.trans_union` in
`Strata.DL.Imperative.StmtSemanticsProps`.

Key theorem families:

* **`evalCmdE_replay_extends`** replays a canonical event-producing command on
  an extending target store, preserving the classified store extension and
  relating the emitted snapshots by the pointwise `TraceExtendsEnv`.
* **Composition laws** `EventArg.ExtendsEnv.trans_union` /
  `Event.ExtendsEnv.trans_union` / `TraceExtendsEnv.trans_union` chain two
  stages while unioning their extra-register classes.
* **Semantic transport laws** transfer assumption satisfaction and reachability
  forward across `Trace.StuttersEnv`, and reflect assertion validity backward,
  under `ConditionInterp.StableUnderExtendsEnv` and
  `ConditionInterp.TrueStutterHolds`.
* **Reflexivity / monotonicity / append laws** for each relation, the
  `Trace.StuttersEnv.Cmd.emittedEvents_stuttersEnv` command-snapshot law, and the
  `TraceExtendsEnv.toTraceStuttersEnv` refinement.
* **Semantic matching** `TraceExtendsEnv.toMatches` upgrades lockstep extension
  to a pointwise match under any semantic argument relation, given defined
  source reads and well-formed snapshots; `Event.Matches.comp` and
  `Trace.matches_comp` compose such matches.
* **`WithWF` strengthenings** of `EventArg.ExtendsEnv` (`EventArg.WithWF` is
  defined in `TraceRelations`): `EventArg.WithWF.mono` / `trans` /
  `label_metadata` / `factory_label_metadata`, with trace-level `Trace.WithWF.append` /
  `toExtendsEnv` /
  `of_extends` / `mono` / `trans` / `toTraceStuttersEnv` /
  `assertionValidFrom_reflect`.
* **`Trace.WeakensAssumes`** is reflexive and transitive
  (`Trace.WeakensAssumes.refl`, `Trace.WeakensAssumes.trans`), as is its event-level
  counterpart relation `Event.WeakensAssume`.  It carries assumption satisfaction from
  the source to the target (`Trace.WeakensAssumes.assumptionsHold_transfer`) and reflects
  assertion validity from the target to the source
  (`Trace.WeakensAssumes.assertionsValid_reflect`).
* **`Trace.InsertsTrueAssumes`** is reflexive and closed under concatenation (`refl`,
  `append`) and carries assumption satisfaction forward under
  `ConditionInterp.TrueStutterHolds` (`assumptionsHold`).  So is its composition with
  `Trace.MayDropEvents`, a `List.Sublist` (`Trace.mayDropEvents_insertsTrueAssumes_*`;
  `drop_left` drops a prefix of the source).  `Trace.PreservesLastEvent` composes on the
  left (`append_left`), and a relation preserving the last event followed by extra events
  reflects last assertions (`Trace.PreservesLastEvent.reflectsLastAssertion`).
* **`Trace.InsertsAsserts`** and **`Trace.InsertsCheckedAssumes`** hold under a larger set of
  allowed factories (`mono_allowed`), and, under an interpretation for which conditions with the
  same value hold alike (and, for the second, true conditions hold), reflect assertion validity
  (`reflect`, `assertionsValidFromP_reflect`) and carry reachability forward
  (`reachable_transfer`, for the second when the inserted checks of the target are valid); so
  does their composition (`Trace.insertsAsserts_insertsCheckedAssumes_*`).
-/

namespace Imperative

public section

namespace EventArg.ExtendsEnv

/-- With no permitted target-only bindings, event-argument extension is
ordinary equality. -/
theorem eq_of_false {P : PureExpr} {source target : EventArg P}
    (h : source.ExtendsEnv (fun _ => False) target) : source = target := by
  obtain ⟨hfactory, hstore, hlabel, hexpr, hmetadata⟩ := h
  have hstoreEq := StoreExtendsWith.eq_of_false hstore
  cases source
  cases target
  cases hfactory
  cases hstoreEq
  cases hlabel
  cases hexpr
  cases hmetadata
  rfl

/-- Every event argument extends itself. -/
theorem refl {P : PureExpr} (Extra : P.Ident → Prop) (arg : EventArg P) :
    arg.ExtendsEnv Extra arg :=
  ⟨rfl, StoreExtendsWith.refl Extra _, rfl, rfl, rfl⟩

/-- Widening the accepted class of target-only registers preserves
event-argument extension. -/
theorem mono {P : PureExpr} {Extra Extra' : P.Ident → Prop}
    (hsub : ∀ ident, Extra ident → Extra' ident)
    {source target : EventArg P} (h : source.ExtendsEnv Extra target) :
    source.ExtendsEnv Extra' target :=
  ⟨h.1, h.2.1.mono hsub, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Event-argument extension composes while unioning extra-register classes. -/
theorem trans_union {P : PureExpr} {Extra₁ Extra₂ : P.Ident → Prop}
    {first second third : EventArg P}
    (h₁ : first.ExtendsEnv Extra₁ second)
    (h₂ : second.ExtendsEnv Extra₂ third) :
    first.ExtendsEnv (fun ident => Extra₁ ident ∨ Extra₂ ident) third :=
  ⟨h₁.1.trans h₂.1,
   StoreExtendsWith.trans_union h₁.2.1 h₂.2.1,
   h₁.2.2.1.trans h₂.2.2.1,
   h₁.2.2.2.1.trans h₂.2.2.2.1,
   h₁.2.2.2.2.trans h₂.2.2.2.2⟩

end EventArg.ExtendsEnv

/-- Every condition interpretation is stable when target-only bindings are
forbidden: `EventArg.ExtendsEnv false` is equality, so both interpreted
conditions are identical. -/
theorem ConditionInterp.stableUnderExtendsEnv_false {P : PureExpr}
    (I : ConditionInterp P) : I.StableUnderExtendsEnv (fun _ => False) := by
  intro _ source target hext
  rw [EventArg.ExtendsEnv.eq_of_false hext]

namespace Event.ExtendsEnv

/-- Every event extends itself. -/
theorem refl {P : PureExpr} (Extra : P.Ident → Prop) (event : Event P) :
    event.ExtendsEnv Extra event := by
  cases event <;> exact EventArg.ExtendsEnv.refl Extra _

/-- Widening the accepted class of target-only registers preserves event
extension. -/
theorem mono {P : PureExpr} {Extra Extra' : P.Ident → Prop}
    (hsub : ∀ ident, Extra ident → Extra' ident)
    {source target : Event P} (h : source.ExtendsEnv Extra target) :
    source.ExtendsEnv Extra' target := by
  cases source <;> cases target <;>
    simp_all only [Event.ExtendsEnv, Event.Matches]
  all_goals exact EventArg.ExtendsEnv.mono hsub h

/-- Event extension composes while unioning extra-register classes. -/
theorem trans_union {P : PureExpr} {Extra₁ Extra₂ : P.Ident → Prop}
    {first second third : Event P}
    (h₁ : first.ExtendsEnv Extra₁ second)
    (h₂ : second.ExtendsEnv Extra₂ third) :
    first.ExtendsEnv (fun ident => Extra₁ ident ∨ Extra₂ ident) third := by
  cases first <;> cases second <;> cases third <;>
    simp_all only [Event.ExtendsEnv, Event.Matches]
  all_goals exact EventArg.ExtendsEnv.trans_union h₁ h₂

end Event.ExtendsEnv

namespace Trace.StuttersEnv

/-- Every trace extends itself. -/
theorem refl {P : PureExpr} [HasBool P]
    (allowedVarName : P.Ident → Prop) (allowedFactory : P.Factory → Prop)
    (trace : Trace P) :
    Trace.StuttersEnv allowedVarName allowedFactory trace trace := by
  induction trace with
  | nil => exact .nil
  | cons event rest ih => exact .lockstep (Event.ExtendsEnv.refl allowedVarName event) ih

/-- Widening the accepted class of target-only registers preserves
environment-extending trace correspondence. -/
theorem mono {P : PureExpr} [HasBool P]
    {allowedVarName allowedVarName' : P.Ident → Prop}
    {allowedFactory : P.Factory → Prop}
    (hsub : ∀ ident, allowedVarName ident → allowedVarName' ident)
    {source target : Trace P}
    (h : Trace.StuttersEnv allowedVarName allowedFactory source target) :
    Trace.StuttersEnv allowedVarName' allowedFactory source target := by
  induction h with
  | nil => exact .nil
  | lockstep hevent _ ih => exact .lockstep (hevent.mono hsub) ih
  | stutter_left hadmissible htrue _ ih => exact .stutter_left hadmissible htrue ih
  | stutter_right hadmissible htrue _ ih => exact .stutter_right hadmissible htrue ih

/-- Environment-extending trace correspondence composes over chronological
append. -/
theorem append {P : PureExpr} [HasBool P]
    {allowedVarName : P.Ident → Prop} {allowedFactory : P.Factory → Prop}
    {source₁ target₁ source₂ target₂ : Trace P}
    (h₁ : Trace.StuttersEnv allowedVarName allowedFactory source₁ target₁)
    (h₂ : Trace.StuttersEnv allowedVarName allowedFactory source₂ target₂) :
    Trace.StuttersEnv allowedVarName allowedFactory
      (source₁ ++ source₂) (target₁ ++ target₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | lockstep hevent _ ih => exact .lockstep hevent ih
  | stutter_left hadmissible htrue _ ih => exact .stutter_left hadmissible htrue ih
  | stutter_right hadmissible htrue _ ih => exact .stutter_right hadmissible htrue ih

/-- A common exact prefix preserves environment-extending trace
correspondence. -/
theorem prepend {P : PureExpr} [HasBool P]
    (allowedVarName : P.Ident → Prop) (allowedFactory : P.Factory → Prop)
    (common : Trace P) {source target : Trace P}
    (h : Trace.StuttersEnv allowedVarName allowedFactory source target) :
    Trace.StuttersEnv allowedVarName allowedFactory
      (common ++ source) (common ++ target) :=
  (refl allowedVarName allowedFactory common).append h

end Trace.StuttersEnv

/-! ## Semantic transport across `Trace.StuttersEnv` -/

section StuttersEnvInterpretation

variable {P : PureExpr} [HasBool P]

/-- `Trace.StuttersEnv` transfers assumption satisfaction from source to target:
any world satisfying the source trace's assumptions satisfies the target's.
Dropped-left stutter weakens the source assumptions; inserted-right stutter adds
an assumption the evaluator deemed true (`htrue`); and paired assumptions agree
by stability (`hstable`). -/
theorem Trace.StuttersEnv.assumptionsHold_transfer
    {I : ConditionInterp P} {allowedVarName : P.Ident → Prop}
    {allowedFactory : P.Factory → Prop}
    (hstable : I.StableUnderExtendsEnv allowedVarName)
    (htrue : I.TrueStutterHolds allowedFactory)
    {source target : Trace P}
    (h : Trace.StuttersEnv allowedVarName allowedFactory source target) :
    ∀ (world : I.World),
      Trace.AssumptionsHold P I world source →
      Trace.AssumptionsHold P I world target := by
  induction h with
  | nil => intro world hsrc; exact hsrc
  | @lockstep s t se te hevent hrest ih =>
    intro world hsrc
    have htail : Trace.AssumptionsHold P I world t :=
      ih world (fun c hc => hsrc c (List.mem_cons_of_mem _ hc))
    cases te with
    | assert tc => rw [Trace.assumptionsHold_cons_assert]; exact htail
    | cover tc => rw [Trace.assumptionsHold_cons_cover]; exact htail
    | assume tc =>
      rw [Trace.assumptionsHold_cons_assume]
      refine ⟨?_, htail⟩
      cases se with
      | assume sc =>
        simp only [Event.ExtendsEnv, Event.Matches] at hevent
        exact (hstable world sc tc hevent).mp (hsrc sc (by simp))
      | assert sc => simp [Event.ExtendsEnv, Event.Matches] at hevent
      | cover sc => simp [Event.ExtendsEnv, Event.Matches] at hevent
  | @stutter_left s t se hadmissible he hrest ih =>
    intro world hsrc
    exact ih world (fun c hc => hsrc c (List.mem_cons_of_mem _ hc))
  | @stutter_right s t te hadmissible he hrest ih =>
    intro world hsrc
    have htail : Trace.AssumptionsHold P I world t := ih world hsrc
    cases te with
    | assert tc => rw [Trace.assumptionsHold_cons_assert]; exact htail
    | cover tc => simp [Event.isTrueAssumeOrAssert] at he
    | assume tc =>
      rw [Trace.assumptionsHold_cons_assume]
      simp only [Event.isTrueAssumeOrAssert] at he
      exact ⟨htrue tc hadmissible he world, htail⟩

/-- `Trace.StuttersEnv` transfers reachability forward: a reachable source trace
has a reachable target trace (same world witness). -/
theorem Trace.StuttersEnv.reachable_transfer
    {I : ConditionInterp P} {allowedVarName : P.Ident → Prop}
    {allowedFactory : P.Factory → Prop}
    (hstable : I.StableUnderExtendsEnv allowedVarName)
    (htrue : I.TrueStutterHolds allowedFactory)
    {source target : Trace P}
    (h : Trace.StuttersEnv allowedVarName allowedFactory source target)
    (hreach : Trace.Reachable P I source) : Trace.Reachable P I target := by
  obtain ⟨world, hworld⟩ := hreach
  exact ⟨world, Trace.StuttersEnv.assumptionsHold_transfer hstable htrue h world hworld⟩

/-- Accumulator-generalized validity reflection: if assumption satisfaction
transfers between related accumulators, target-trace assertion validity reflects
to the source trace. Proved by induction on the trace correspondence. -/
private theorem Trace.StuttersEnv.assertionsValidFrom_reflect
    {I : ConditionInterp P} {allowedVarName : P.Ident → Prop}
    {allowedFactory : P.Factory → Prop}
    (hstable : I.StableUnderExtendsEnv allowedVarName)
    (htrue : I.TrueStutterHolds allowedFactory)
    {source target : Trace P}
    (h : Trace.StuttersEnv allowedVarName allowedFactory source target) :
    ∀ (accS accT : Trace P),
      (∀ world, Trace.AssumptionsHold P I world accS →
        Trace.AssumptionsHold P I world accT) →
      Trace.AssertionsValidFromP P I (fun _ => True) accT target →
      Trace.AssertionsValidFromP P I (fun _ => True) accS source := by
  induction h with
  | nil => intro accS accT _ _; trivial
  | @lockstep s t se te hevent hrest ih =>
    intro accS accT hacc hvalid
    cases se with
    | assert sc =>
      cases te with
      | assert tc =>
        simp only [Event.ExtendsEnv, Event.Matches] at hevent
        obtain ⟨hv1, hv2⟩ := hvalid
        refine ⟨fun _ world hhold => ?_, ih accS accT hacc hv2⟩
        exact (hstable world sc tc hevent).mpr (hv1 trivial world (hacc world hhold))
      | assume tc => simp [Event.ExtendsEnv, Event.Matches] at hevent
      | cover tc => simp [Event.ExtendsEnv, Event.Matches] at hevent
    | assume sc =>
      cases te with
      | assert tc => simp [Event.ExtendsEnv, Event.Matches] at hevent
      | assume tc =>
        simp only [Event.ExtendsEnv, Event.Matches] at hevent
        refine ih (accS ++ [Event.assume sc]) (accT ++ [Event.assume tc]) ?_ hvalid
        intro world hhold
        rw [Trace.AssumptionsHold_append_assume] at hhold ⊢
        exact ⟨hacc world hhold.1, (hstable world sc tc hevent).mp hhold.2⟩
      | cover tc => simp [Event.ExtendsEnv, Event.Matches] at hevent
    | cover sc =>
      cases te with
      | assert tc => simp [Event.ExtendsEnv, Event.Matches] at hevent
      | assume tc => simp [Event.ExtendsEnv, Event.Matches] at hevent
      | cover tc => exact ih accS accT hacc hvalid
  | @stutter_left s t se hadmissible he hrest ih =>
    intro accS accT hacc hvalid
    cases se with
    | assert sc =>
      simp only [Event.isTrueAssumeOrAssert] at he
      exact ⟨fun _ world _ => htrue sc hadmissible he world, ih accS accT hacc hvalid⟩
    | assume sc =>
      simp only [Event.isTrueAssumeOrAssert] at he
      refine ih (accS ++ [Event.assume sc]) accT ?_ hvalid
      intro world hhold
      rw [Trace.AssumptionsHold_append_assume] at hhold
      exact hacc world hhold.1
    | cover sc => simp [Event.isTrueAssumeOrAssert] at he
  | @stutter_right s t te hadmissible he hrest ih =>
    intro accS accT hacc hvalid
    cases te with
    | assert tc =>
      obtain ⟨_, hv2⟩ := hvalid
      exact ih accS accT hacc hv2
    | assume tc =>
      simp only [Event.isTrueAssumeOrAssert] at he
      refine ih accS (accT ++ [Event.assume tc]) ?_ hvalid
      intro world hhold
      rw [Trace.AssumptionsHold_append_assume]
      exact ⟨hacc world hhold, htrue tc hadmissible he world⟩
    | cover tc => simp [Event.isTrueAssumeOrAssert] at he

/-- Whole-trace validity reflection across `Trace.StuttersEnv`: target validity
reflects to source validity under semantic stability.  The empty-accumulator
instance of `assertionsValidFrom_reflect`. -/
theorem Trace.StuttersEnv.assertionsValid_reflect
    {I : ConditionInterp P} {allowedVarName : P.Ident → Prop}
    {allowedFactory : P.Factory → Prop}
    (hstable : I.StableUnderExtendsEnv allowedVarName)
    (htrue : I.TrueStutterHolds allowedFactory)
    {source target : Trace P}
    (h : Trace.StuttersEnv allowedVarName allowedFactory source target)
    (hvalid : Trace.AssertionsValid P I target) :
    Trace.AssertionsValid P I source :=
  Trace.StuttersEnv.assertionsValidFrom_reflect hstable htrue h [] [] (fun _ h => h) hvalid

end StuttersEnvInterpretation

namespace TraceExtendsEnv

/-- Every trace is in lockstep with itself. -/
theorem refl {P : PureExpr} (allowedVarName : P.Ident → Prop)
    (trace : Trace P) : TraceExtendsEnv allowedVarName trace trace := by
  induction trace with
  | nil => exact .nil
  | cons event rest ih =>
      exact .cons (Event.ExtendsEnv.refl allowedVarName event) ih

/-- Widening the accepted class of target-only registers preserves lockstep
trace correspondence. -/
theorem mono {P : PureExpr} {allowedVarName allowedVarName' : P.Ident → Prop}
    (hsub : ∀ ident, allowedVarName ident → allowedVarName' ident)
    {source target : Trace P} (h : TraceExtendsEnv allowedVarName source target) :
    TraceExtendsEnv allowedVarName' source target := by
  induction h with
  | nil => exact .nil
  | cons hevent _ ih => exact .cons (hevent.mono hsub) ih

/-- Lockstep trace correspondence composes over chronological append. -/
theorem append {P : PureExpr} {allowedVarName : P.Ident → Prop}
    {source₁ target₁ source₂ target₂ : Trace P}
    (h₁ : TraceExtendsEnv allowedVarName source₁ target₁)
    (h₂ : TraceExtendsEnv allowedVarName source₂ target₂) :
    TraceExtendsEnv allowedVarName (source₁ ++ source₂) (target₁ ++ target₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons hevent _ ih => exact .cons hevent ih

/-- The same command observed in classified extending stores emits
lockstep-related traces.  Each command emits a fixed number of events whose kind
depends only on the command, not on the store, so the source and target traces
have equal length and their single (assert/assume/cover) event corresponds by
`Event.ExtendsEnv`. -/
theorem Cmd.emittedEvents_extendsEnv {P : PureExpr} [HasBool P]
    (allowedVarName : P.Ident → Prop) (command : Cmd P) (factory : P.Factory)
    {sourceStore targetStore : SemanticStore P}
    (hstore : StoreExtendsWith allowedVarName sourceStore targetStore) :
    TraceExtendsEnv allowedVarName
      (Cmd.emittedEvents P command factory sourceStore)
      (Cmd.emittedEvents P command factory targetStore) := by
  cases command with
  | init | set => exact .nil
  | assert | assume | cover =>
      exact .cons ⟨rfl, hstore, rfl, rfl, rfl⟩ .nil

/-- Consecutive lockstep correspondences compose, unioning the accepted
target-only register classes.  This is the sound transitivity principle
`Trace.StuttersEnv` lacks: two-sided true-event stuttering would let a middle
event be extended to one reading a newly added binding, but a lockstep middle
event is matched exactly, so the classes compose. -/
theorem trans_union {P : PureExpr}
    {allowedVarName₁ allowedVarName₂ : P.Ident → Prop}
    {source middle target : Trace P}
    (h₁ : TraceExtendsEnv allowedVarName₁ source middle)
    (h₂ : TraceExtendsEnv allowedVarName₂ middle target) :
    TraceExtendsEnv (fun ident => allowedVarName₁ ident ∨ allowedVarName₂ ident)
      source target := by
  induction h₁ generalizing target with
  | nil =>
      cases h₂
      exact .nil
  | cons hab _ ih =>
      cases h₂ with
      | cons hbc hrest => exact .cons (Event.ExtendsEnv.trans_union hab hbc) (ih hrest)

/-- Consecutive lockstep correspondences using the same accepted class compose. -/
theorem trans {P : PureExpr} {allowedVarName : P.Ident → Prop}
    {source middle target : Trace P}
    (h₁ : TraceExtendsEnv allowedVarName source middle)
    (h₂ : TraceExtendsEnv allowedVarName middle target) :
    TraceExtendsEnv allowedVarName source target :=
  (trans_union h₁ h₂).mono (fun _ h => h.elim id id)

/-- Pointwise trace correspondence refines the stuttering correspondence: every
pointwise (lockstep) step is in particular a non-stuttering `Trace.StuttersEnv`
step. -/
theorem toTraceStuttersEnv {P : PureExpr} [HasBool P]
    {allowedVarName : P.Ident → Prop} {allowedFactory : P.Factory → Prop}
    {source target : Trace P}
    (h : TraceExtendsEnv allowedVarName source target) :
    Trace.StuttersEnv allowedVarName allowedFactory source target := by
  induction h with
  | nil => exact .nil
  | cons hevent _ ih => exact .lockstep hevent ih

end TraceExtendsEnv

/-- The same command observed in classified extending stores emits
stutter-related traces, as a corollary of its pointwise event correspondence. -/
theorem Trace.StuttersEnv.Cmd.emittedEvents_stuttersEnv
    {P : PureExpr} [HasBool P]
    (allowedVarName : P.Ident → Prop) (allowedFactory : P.Factory → Prop)
    (command : Cmd P) (factory : P.Factory)
    {sourceStore targetStore : SemanticStore P}
    (hstore : StoreExtendsWith allowedVarName sourceStore targetStore) :
    Trace.StuttersEnv allowedVarName allowedFactory
      (Cmd.emittedEvents P command factory sourceStore)
      (Cmd.emittedEvents P command factory targetStore) :=
  (TraceExtendsEnv.Cmd.emittedEvents_extendsEnv
    allowedVarName command factory hstore).toTraceStuttersEnv

/-- `SemanticStore.update` is the canonical result of initializing an
undefined slot. -/
private theorem initState_update {P : PureExpr} [DecidableEq P.Ident]
    {σ : SemanticStore P} {ident : P.Ident} {value : P.Val}
    (hnone : σ ident = none) :
    InitState P σ ident value (SemanticStore.update σ ident value) :=
  .init hnone (by simp [SemanticStore.update])
    (by intro other hne; simp [SemanticStore.update, Ne.symm hne])

/-- `SemanticStore.update` is the canonical result of updating a defined slot. -/
private theorem updateState_update {P : PureExpr} [DecidableEq P.Ident]
    {σ : SemanticStore P} {ident : P.Ident} {value old : P.Val}
    (hold : σ ident = some old) :
    UpdateState P σ ident value (SemanticStore.update σ ident value) :=
  .update hold (by simp [SemanticStore.update])
    (by intro other hne; simp [SemanticStore.update, Ne.symm hne])

/-- Replay a canonical event-producing command on an extending target store, in
pointwise lockstep.  The replay preserves classified store extension and relates
the command's observable snapshots with the pointwise `TraceExtendsEnv`.

Key idea: replaying the *same* command `c` on an extending store emits the same
number and kinds of events because event shape depends only on the command, so
the source and target traces correspond event-by-event. Store extension supplies
every value read by the source evaluation and is preserved by the resulting
store updates. -/
theorem evalCmdE_replay_extends {P : PureExpr} [HasFvar P] [HasFvars P]
    [HasBoolOps P] [HasIdent P] [DecidableEq P.Ident]
    (Extra : P.Ident → Prop) (f : P.Factory)
    (σs σt σs' : SemanticStore P) (c : Cmd P) (emitted : Trace P)
    (hext : StoreExtendsWith Extra σs σt)
    (heval : EvalCmdE P f σs c σs' emitted)
    (hwf : WellFormedSemanticEvalMono f)
    (hinit : ∀ x ∈ Cmd.definedVars c, σt x = none) :
    ∃ σt', EvalCmdE P f σt c σt'
          (Cmd.emittedEvents P c f σt)
      ∧ StoreExtendsWith Extra σs' σt'
      ∧ TraceExtendsEnv Extra emitted (Cmd.emittedEvents P c f σt) := by
  cases heval with
  | eval_init he hstate hty hwfv =>
      rename_i e v x ty md
      have hnone : σt x = none := hinit x (by
        with_unfolding_all exact List.mem_singleton.mpr rfl)
      have het : P.eval f σt e = some v :=
        hwf e v σs σt (storeAgreement_supplies_mono_premise _ _ hext.1) he
      let σt' := SemanticStore.update σt x v
      have htstate : InitState P σt x v σt' := initState_update hnone
      have hnones : σs x = none := by cases hstate; assumption
      rw [InitStateUniqueResult hstate (initState_update hnones)]
      refine ⟨σt', .eval_init het htstate hty hwfv,
        StoreExtendsWith.update_both hext, ?_⟩
      exact TraceExtendsEnv.Cmd.emittedEvents_extendsEnv Extra (.init x ty (.det e) md) f hext
  | eval_init_unconstrained hstate hty hwfv =>
      rename_i x v ty md
      have hnone : σt x = none := hinit x (by
        with_unfolding_all exact List.mem_singleton.mpr rfl)
      let σt' := SemanticStore.update σt x v
      have htstate : InitState P σt x v σt' := initState_update hnone
      have hnones : σs x = none := by cases hstate; assumption
      rw [InitStateUniqueResult hstate (initState_update hnones)]
      refine ⟨σt', .eval_init_unconstrained htstate hty hwfv,
        StoreExtendsWith.update_both hext, ?_⟩
      exact TraceExtendsEnv.Cmd.emittedEvents_extendsEnv Extra (.init x ty .nondet md) f hext
  | eval_set he hstate hty hwfv =>
      rename_i e v x md
      have het : P.eval f σt e = some v :=
        hwf e v σs σt (storeAgreement_supplies_mono_premise _ _ hext.1) he
      obtain ⟨old, ty, hold, holdty, hvty⟩ := hty
      have holdt : σt x = some old :=
        storeAgreement_supplies_mono_premise _ _ hext.1 x old hold
      let σt' := SemanticStore.update σt x v
      have htstate : UpdateState P σt x v σt' := updateState_update holdt
      rw [UpdateStateUniqueResult hstate (updateState_update hold)]
      refine ⟨σt', .eval_set het htstate ⟨old, ty, holdt, holdty, hvty⟩ hwfv,
        StoreExtendsWith.update_both hext, ?_⟩
      exact TraceExtendsEnv.Cmd.emittedEvents_extendsEnv Extra (.set x (.det e) md) f hext
  | eval_set_nondet hstate hty hwfv =>
      rename_i x v md
      obtain ⟨old, ty, hold, holdty, hvty⟩ := hty
      have holdt : σt x = some old :=
        storeAgreement_supplies_mono_premise _ _ hext.1 x old hold
      let σt' := SemanticStore.update σt x v
      have htstate : UpdateState P σt x v σt' := updateState_update holdt
      rw [UpdateStateUniqueResult hstate (updateState_update hold)]
      refine ⟨σt', .eval_set_nondet htstate ⟨old, ty, holdt, holdty, hvty⟩ hwfv,
        StoreExtendsWith.update_both hext, ?_⟩
      exact TraceExtendsEnv.Cmd.emittedEvents_extendsEnv Extra (.set x .nondet md) f hext
  | eval_assert =>
      rename_i label e md
      exact ⟨σt, .eval_assert, hext,
        TraceExtendsEnv.Cmd.emittedEvents_extendsEnv Extra (.assert label e md) f hext⟩
  | eval_assume =>
      rename_i label e md
      exact ⟨σt, .eval_assume, hext,
        TraceExtendsEnv.Cmd.emittedEvents_extendsEnv Extra (.assume label e md) f hext⟩
  | eval_cover =>
      rename_i label e md
      exact ⟨σt, .eval_cover, hext,
        TraceExtendsEnv.Cmd.emittedEvents_extendsEnv Extra (.cover label e md) f hext⟩

/-- Pointwise environment extension strengthens to any semantic argument
relation once source reads are defined and both traces carry well-formed
snapshots. Source-defined free variables are preserved by the store extension,
which supplies free-variable store agreement. -/
theorem TraceExtendsEnv.toMatches {P : PureExpr} [HasVal P] [HasFvars P]
    {Extra : P.Ident → Prop} {ArgRel : EventArg P → EventArg P → Prop}
    (hmk : ∀ {source target : EventArg P},
      source.ExtendsEnv Extra target →
      StoreAgreesOnFvars source.store target.store source.expr →
      source.SemanticWF → target.SemanticWF → ArgRel source target)
    {source target : Trace P}
    (hext : TraceExtendsEnv Extra source target)
    (hreads : Trace.readsDefined source)
    (hsourceWF : Trace.semanticWF source)
    (htargetWF : Trace.semanticWF target) :
    List.Rel₂ (Event.Matches ArgRel) source target := by
  induction hext with
  | nil => exact .nil
  | cons hhead htail ih =>
      rename_i sourceEvent targetEvent sourceTail targetTail
      have hreadHead := hreads _ List.mem_cons_self
      have hsourceHead := hsourceWF _ List.mem_cons_self
      have htargetHead := htargetWF _ List.mem_cons_self
      refine .cons ?_ (ih
        (fun event hevent => hreads event (List.mem_cons_of_mem _ hevent))
        (fun event hevent => hsourceWF event (List.mem_cons_of_mem _ hevent))
        (fun event hevent => htargetWF event (List.mem_cons_of_mem _ hevent)))
      cases sourceEvent <;> cases targetEvent <;>
        simp_all only [Event.ExtendsEnv, Event.Matches,
          Event.readsDefined, Event.semanticWF]
      all_goals
        refine hmk hhead ?_ hsourceHead htargetHead
        intro ident hident
        exact hhead.2.1.1 ident (by
          simpa [SemanticStore.varsDefined] using hreadHead ident hident)

/-- Same-kind event matching composes through a middle event. -/
theorem Event.Matches.comp {P : PureExpr}
    {R₁ R₂ R₃ : EventArg P → EventArg P → Prop}
    (hcomp : ∀ {first second third : EventArg P},
      R₁ first second → R₂ second third → R₃ first third)
    {first second third : Event P}
    (h₁ : Event.Matches R₁ first second) (h₂ : Event.Matches R₂ second third) :
    Event.Matches R₃ first third := by
  cases first <;> cases second <;> cases third
  all_goals first
    | exact hcomp h₁ h₂
    | exact False.elim h₁
    | exact False.elim h₂

/-- Pointwise same-kind event matching composes through a middle trace. -/
theorem Trace.matches_comp {P : PureExpr}
    {R₁ R₂ R₃ : EventArg P → EventArg P → Prop}
    (hcomp : ∀ {first second third : EventArg P},
      R₁ first second → R₂ second third → R₃ first third)
    {first second third : Trace P}
    (h₁ : List.Rel₂ (Event.Matches R₁) first second)
    (h₂ : List.Rel₂ (Event.Matches R₂) second third) :
    List.Rel₂ (Event.Matches R₃) first third := by
  induction h₁ generalizing third with
  | nil => cases h₂; exact .nil
  | cons hhead _ ih =>
      cases h₂ with
      | cons hhead₂ htail₂ =>
          exact .cons (Event.Matches.comp (R₁ := R₁) (R₂ := R₂) (R₃ := R₃)
            hcomp hhead hhead₂) (ih htail₂)

/-! ## `WithWF` strengthenings of `ExtendsEnv` -/

namespace EventArg.WithWF

/-- Widening the accepted class of target-only bindings preserves
`WithWF (ExtendsEnv _)`. -/
theorem mono {P : PureExpr} [HasVal P] [HasFvars P]
    {Extra Extra' : P.Ident → Prop} (hsub : ∀ ident, Extra ident → Extra' ident)
    {source target : EventArg P}
    (h : EventArg.WithWF (EventArg.ExtendsEnv Extra) source target) :
    EventArg.WithWF (EventArg.ExtendsEnv Extra') source target :=
  { h with rel := EventArg.ExtendsEnv.mono hsub h.rel }

/-- `WithWF (ExtendsEnv _)` composes while unioning the classes of target-only
bindings. -/
theorem trans {P : PureExpr} [HasVal P] [HasFvars P]
    {Extra₁ Extra₂ : P.Ident → Prop} {first second third : EventArg P}
    (h₁ : EventArg.WithWF (EventArg.ExtendsEnv Extra₁) first second)
    (h₂ : EventArg.WithWF (EventArg.ExtendsEnv Extra₂) second third) :
    EventArg.WithWF
      (EventArg.ExtendsEnv (fun ident => Extra₁ ident ∨ Extra₂ ident)) first third where
  rel := EventArg.ExtendsEnv.trans_union h₁.rel h₂.rel
  store_fv := by
    intro ident hident
    calc
      first.store ident = second.store ident := h₁.store_fv ident hident
      _ = third.store ident := h₂.store_fv ident (by
        rw [← h₁.rel.2.2.2.1]
        exact hident)
  sourceStoreWF := h₁.sourceStoreWF
  targetStoreWF := h₂.targetStoreWF
  exprCongr := h₁.exprCongr

/-- Arguments related by `WithWF (ExtendsEnv _)` carry the same assertion label
and metadata. -/
theorem label_metadata {P : PureExpr} [HasVal P] [HasFvars P]
    {Extra : P.Ident → Prop} {source target : EventArg P}
    (h : EventArg.WithWF (EventArg.ExtendsEnv Extra) source target) :
    source.label = target.label ∧ source.metadata = target.metadata := by
  obtain ⟨_, _, hlabel, _, hmd⟩ := h.rel
  exact ⟨hlabel, hmd⟩

/-- `WithWF (ExtendsEnv _)` keeps the factory, the label and the metadata of the source
argument. -/
theorem factory_label_metadata {P : PureExpr} [HasVal P] [HasFvars P]
    {Extra : P.Ident → Prop} {source target : EventArg P}
    (h : EventArg.WithWF (EventArg.ExtendsEnv Extra) source target) :
    target.factory = source.factory ∧ source.label = target.label ∧
      source.metadata = target.metadata :=
  ⟨h.rel.1.symm, h.label_metadata⟩

end EventArg.WithWF

/-- Forgetting the well-formedness evidence recovers ordinary event extension. -/
theorem Event.WithWF.toExtendsEnv {P : PureExpr} [HasVal P] [HasFvars P]
    {Extra : P.Ident → Prop} {source target : Event P}
    (h : Event.WithWF (EventArg.ExtendsEnv Extra) source target) :
    Event.ExtendsEnv Extra source target := by
  cases source <;> cases target <;>
    simp_all only [Event.WithWF, Event.Matches, Event.ExtendsEnv]
  all_goals exact h.rel

namespace Trace.WithWF

/-- `Trace.WithWF R` is closed under append, for any argument relation `R`. -/
theorem append {P : PureExpr} [HasVal P] [HasFvars P]
    {R : EventArg P → EventArg P → Prop} {s₁ s₂ t₁ t₂ : Trace P}
    (h₁ : Trace.WithWF R s₁ t₁) (h₂ : Trace.WithWF R s₂ t₂) :
    Trace.WithWF R (s₁ ++ s₂) (t₁ ++ t₂) :=
  List.Rel₂.append h₁ h₂

/-- Forgetting the well-formedness evidence pointwise recovers trace extension. -/
theorem toExtendsEnv {P : PureExpr} [HasVal P] [HasFvars P]
    {Extra : P.Ident → Prop} {source target : Trace P}
    (h : Trace.WithWF (EventArg.ExtendsEnv Extra) source target) :
    TraceExtendsEnv Extra source target :=
  h.imp fun _ _ => Event.WithWF.toExtendsEnv

/-- Ordinary lockstep extension strengthens to `WithWF` matching when source
event reads are defined and both traces carry well-formed snapshots. -/
theorem of_extends {P : PureExpr} [HasVal P] [HasFvars P]
    {Extra : P.Ident → Prop} {source target : Trace P}
    (hext : TraceExtendsEnv Extra source target)
    (hreads : Trace.readsDefined source)
    (hsourceWF : Trace.semanticWF source)
    (htargetWF : Trace.semanticWF target) :
    Trace.WithWF (EventArg.ExtendsEnv Extra) source target :=
  TraceExtendsEnv.toMatches
    (fun hext hfv hsource htarget =>
      ⟨hext, hfv, hsource.storeWellDefined, htarget.storeWellDefined,
        hsource.exprCongr⟩)
    hext hreads hsourceWF htargetWF

/-- Widening the accepted class of target-only bindings preserves
`Trace.WithWF (ExtendsEnv _)`. -/
theorem mono {P : PureExpr} [HasVal P] [HasFvars P]
    {Extra Extra' : P.Ident → Prop} (hsub : ∀ ident, Extra ident → Extra' ident)
    {source target : Trace P}
    (h : Trace.WithWF (EventArg.ExtendsEnv Extra) source target) :
    Trace.WithWF (EventArg.ExtendsEnv Extra') source target :=
  h.imp fun {source target} hevent => by
    cases source <;> cases target <;>
      simp_all only [Event.WithWF, Event.Matches]
    all_goals exact hevent.mono hsub

/-- `Trace.WithWF (ExtendsEnv _)` composes through a middle trace while unioning
the classes of target-only bindings. -/
theorem trans {P : PureExpr} [HasVal P] [HasFvars P]
    {Extra₁ Extra₂ : P.Ident → Prop} {first second third : Trace P}
    (h₁ : Trace.WithWF (EventArg.ExtendsEnv Extra₁) first second)
    (h₂ : Trace.WithWF (EventArg.ExtendsEnv Extra₂) second third) :
    Trace.WithWF
      (EventArg.ExtendsEnv (fun ident => Extra₁ ident ∨ Extra₂ ident)) first third :=
  Trace.matches_comp
    (R₁ := EventArg.WithWF (EventArg.ExtendsEnv Extra₁))
    (R₂ := EventArg.WithWF (EventArg.ExtendsEnv Extra₂))
    (R₃ := EventArg.WithWF
      (EventArg.ExtendsEnv (fun ident => Extra₁ ident ∨ Extra₂ ident)))
    (fun h₁ h₂ => EventArg.WithWF.trans h₁ h₂) h₁ h₂

/-- `Trace.WithWF (ExtendsEnv _)` is also a stuttering correspondence. -/
theorem toTraceStuttersEnv {P : PureExpr} [HasBool P] [HasFvars P]
    {Extra : P.Ident → Prop} {allowedFactory : P.Factory → Prop}
    {source target : Trace P}
    (h : Trace.WithWF (EventArg.ExtendsEnv Extra) source target) :
    Trace.StuttersEnv Extra allowedFactory source target :=
  h.toExtendsEnv.toTraceStuttersEnv

/-- `Trace.WithWF (ExtendsEnv _)` reflects assertion validity for any condition
interpretation stable under `EventArg.WithWF (ExtendsEnv _)`. -/
theorem assertionValidFrom_reflect {P : PureExpr} [HasVal P] [HasFvars P]
    {Extra : P.Ident → Prop} {I : ConditionInterp P}
    (hstable : I.StableUnder (EventArg.WithWF (EventArg.ExtendsEnv Extra)))
    {source target : Trace P}
    (h : Trace.WithWF (EventArg.ExtendsEnv Extra) source target)
    (aid : AssertId P) :
    Trace.AssertionValidFrom P I aid [] target →
      Trace.AssertionValidFrom P I aid [] source :=
  Trace.AssertionValidFrom_matches_reflect hstable
    (fun h => EventArg.WithWF.label_metadata h) aid .nil h

end Trace.WithWF

section WeakensAssumes

variable {P : PureExpr}

/-- Every event is its own counterpart. -/
theorem Event.WeakensAssume.refl (I : ConditionInterp P) : ∀ e : Event P, Event.WeakensAssume I e e
  | .assert _ | .cover _ => ⟨rfl, rfl, fun _ => .rfl⟩
  | .assume _ => ⟨rfl, rfl, fun _ => id⟩

/-- Counterparts compose. -/
theorem Event.WeakensAssume.trans {I : ConditionInterp P} {e₁ e₂ e₃ : Event P}
    (h₁ : Event.WeakensAssume I e₁ e₂) (h₂ : Event.WeakensAssume I e₂ e₃) :
    Event.WeakensAssume I e₁ e₃ := by
  cases e₁ <;> cases e₂ <;> cases e₃ <;> simp only [Event.WeakensAssume] at h₁ h₂ ⊢ <;>
    first
    | exact ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, fun w => (h₁.2.2 w).trans (h₂.2.2 w)⟩
    | exact ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, fun w h => h₂.2.2 w (h₁.2.2 w h)⟩

/-- `Trace.WeakensAssumes I` is reflexive. -/
theorem Trace.WeakensAssumes.refl (I : ConditionInterp P) :
    ∀ t : Trace P, Trace.WeakensAssumes I t t
  | [] => .nil
  | e :: t => .cons (Event.WeakensAssume.refl I e) (Trace.WeakensAssumes.refl I t)

/-- `Trace.WeakensAssumes I` is transitive: an event of the middle trace that is dropped from
    the last one is an assumption, so its counterpart in the first trace is one too and is
    dropped. -/
theorem Trace.WeakensAssumes.trans {I : ConditionInterp P} {t₁ t₂ t₃ : Trace P}
    (h₁ : Trace.WeakensAssumes I t₁ t₂) (h₂ : Trace.WeakensAssumes I t₂ t₃) :
    Trace.WeakensAssumes I t₁ t₃ := by
  induction h₁ generalizing t₃ with
  | nil => exact h₂
  | @cons e e' _ _ he _ ih =>
    cases h₂ with
    | cons he' h => exact .cons (he.trans he') (ih h)
    | dropAssume h =>
      cases e <;> simp only [Event.WeakensAssume] at he
      exact .dropAssume (ih h)
  | dropAssume _ ih => exact .dropAssume (ih h₂)

/-- Assumptions of the source holding in a world hold in it for the target: every assumption of
    the target is the counterpart of one of the source, which holds in every world the
    source's does. -/
theorem Trace.WeakensAssumes.assumptionsHold_transfer {I : ConditionInterp P} {s t : Trace P}
    (h : Trace.WeakensAssumes I s t) {w : I.World} (hs : Trace.AssumptionsHold P I w s) :
    Trace.AssumptionsHold P I w t := by
  induction h with
  | nil => exact hs
  | @cons e e' _ _ he _ ih =>
    cases e <;> cases e' <;> simp only [Event.WeakensAssume] at he <;>
      simp only [Trace.assumptionsHold_cons_assert, Trace.assumptionsHold_cons_assume,
        Trace.assumptionsHold_cons_cover] at hs ⊢
    · exact ih hs
    · exact ⟨he.2.2 w hs.1, ih hs.2⟩
    · exact ih hs
  | dropAssume _ ih => exact ih ((Trace.assumptionsHold_cons_assume I w _ _).1 hs).2

/-- Assertion validity reflects from the target to the source, from assumptions accumulated
    before the source whose holding in a world gives that of those accumulated before the
    target. -/
private theorem Trace.WeakensAssumes.assertionsValidFrom_reflect {I : ConditionInterp P}
    {s t : Trace P} (h : Trace.WeakensAssumes I s t) :
    ∀ {acc acc' : Trace P},
      (∀ w, Trace.AssumptionsHold P I w acc → Trace.AssumptionsHold P I w acc') →
      Trace.AssertionsValidFrom P I acc' t → Trace.AssertionsValidFrom P I acc s := by
  induction h with
  | nil => exact fun _ _ => trivial
  | @cons e e' _ _ he _ ih =>
    intro acc acc' hacc hv
    cases e <;> cases e' <;> simp only [Event.WeakensAssume] at he
    · exact ⟨fun _ w hw => (he.2.2 w).2 (hv.1 trivial w (hacc w hw)), ih hacc hv.2⟩
    · refine ih (fun w hw => ?_) hv
      rw [Trace.AssumptionsHold_append_assume] at hw ⊢
      exact ⟨hacc w hw.1, he.2.2 w hw.2⟩
    · exact ih hacc hv
  | dropAssume _ ih =>
    intro acc acc' hacc hv
    exact ih (fun w hw => hacc w fun c hc => hw c (List.mem_append_left _ hc)) hv

/-- Assertion validity reflects from the target to the source. -/
theorem Trace.WeakensAssumes.assertionsValid_reflect {I : ConditionInterp P} {s t : Trace P}
    (h : Trace.WeakensAssumes I s t) (hv : Trace.AssertionsValid P I t) :
    Trace.AssertionsValid P I s :=
  h.assertionsValidFrom_reflect (fun _ hw => hw) hv

end WeakensAssumes

section DropsAndInserts

variable {P : PureExpr}

section InsertsTrueAssumes

variable [HasBool P] {allowed : P.Factory → Prop}

/-- Every trace is itself with no assumption inserted. -/
theorem Trace.InsertsTrueAssumes.refl : ∀ t : Trace P, Trace.InsertsTrueAssumes allowed t t
  | [] => .nil
  | _ :: t => .keep (Trace.InsertsTrueAssumes.refl t)

/-- `Trace.InsertsTrueAssumes` is closed under concatenation. -/
theorem Trace.InsertsTrueAssumes.append {a a' b b' : Trace P}
    (ha : Trace.InsertsTrueAssumes allowed a a') (hb : Trace.InsertsTrueAssumes allowed b b') :
    Trace.InsertsTrueAssumes allowed (a ++ b) (a' ++ b') := by
  induction ha with
  | nil => exact hb
  | keep _ ih => exact .keep ih
  | assume hf he _ ih => exact .assume hf he ih

/-- The assumptions of `t` with true assumptions inserted hold in every world where those of `t`
    hold, when every operationally true condition under an allowed factory holds in every
    world. -/
theorem Trace.InsertsTrueAssumes.assumptionsHold {I : ConditionInterp P}
    (htrue : I.TrueStutterHolds allowed) {t t' : Trace P}
    (h : Trace.InsertsTrueAssumes allowed t t') {w : I.World}
    (hA : Trace.AssumptionsHold P I w t) : Trace.AssumptionsHold P I w t' := by
  induction h with
  | nil => exact hA
  | keep _ ih =>
    intro c hc
    rcases List.mem_cons.1 hc with hc | hc
    · exact hA c (hc ▸ List.mem_cons_self ..)
    · exact ih (fun c' hc' => hA c' (List.mem_cons_of_mem _ hc')) c hc
  | @assume a _ _ hf he _ ih =>
    intro c hc
    rcases List.mem_cons.1 hc with hc | hc
    · cases hc
      exact htrue a hf he w
    · exact ih hA c hc

/-- Inserting true assumptions under some allowed factories inserts them under any larger set of
    allowed factories. -/
private theorem Trace.InsertsTrueAssumes.mono {allowed' : P.Factory → Prop}
    (hmono : ∀ F, allowed F → allowed' F) {t t' : Trace P}
    (h : Trace.InsertsTrueAssumes allowed t t') : Trace.InsertsTrueAssumes allowed' t t' := by
  induction h with
  | nil => exact .nil
  | keep _ ih => exact .keep ih
  | assume hf he _ ih => exact .assume (hmono _ hf) he ih

/-- Dropping events, then inserting true assumptions, is reflexive. -/
theorem Trace.mayDropEvents_insertsTrueAssumes_refl (t : Trace P) :
    RComp Trace.MayDropEvents (Trace.InsertsTrueAssumes allowed) t t :=
  ⟨t, .refl t, .refl t⟩

/-- Dropping events, then inserting true assumptions, is closed under concatenation. -/
theorem Trace.mayDropEvents_insertsTrueAssumes_append {a a' b b' : Trace P}
    (ha : RComp Trace.MayDropEvents (Trace.InsertsTrueAssumes allowed) a a')
    (hb : RComp Trace.MayDropEvents (Trace.InsertsTrueAssumes allowed) b b') :
    RComp Trace.MayDropEvents (Trace.InsertsTrueAssumes allowed) (a ++ b) (a' ++ b') :=
  have ⟨_, ha₁, ha₂⟩ := ha
  have ⟨_, hb₁, hb₂⟩ := hb
  ⟨_, ha₁.append hb₁, ha₂.append hb₂⟩

/-- Dropping a whole prefix of the source keeps dropping events, then inserting true
    assumptions. -/
theorem Trace.mayDropEvents_insertsTrueAssumes_drop_left (a : Trace P) {b b' : Trace P}
    (h : RComp Trace.MayDropEvents (Trace.InsertsTrueAssumes allowed) b b') :
    RComp Trace.MayDropEvents (Trace.InsertsTrueAssumes allowed) (a ++ b) b' :=
  have ⟨_, h₁, h₂⟩ := h
  ⟨_, List.sublist_append_of_sublist_right h₁, h₂⟩

/-- Dropping events, then inserting true assumptions under some allowed factories, relates the
    same traces under any larger set of allowed factories. -/
theorem Trace.mayDropEvents_insertsTrueAssumes_mono {allowed' : P.Factory → Prop}
    (hmono : ∀ F, allowed F → allowed' F) {t t' : Trace P}
    (h : RComp Trace.MayDropEvents (Trace.InsertsTrueAssumes allowed) t t') :
    RComp Trace.MayDropEvents (Trace.InsertsTrueAssumes allowed') t t' :=
  have ⟨_, h₁, h₂⟩ := h
  ⟨_, h₁, h₂.mono hmono⟩

/-- The assumptions of a trace related to `t` by dropping events, then inserting true
    assumptions, hold in every world where those of `t` hold, when every operationally true
    condition under an allowed factory holds in every world. -/
theorem Trace.mayDropEvents_insertsTrueAssumes_assumptionsHold {I : ConditionInterp P}
    (htrue : I.TrueStutterHolds allowed) {t t' : Trace P}
    (h : RComp Trace.MayDropEvents (Trace.InsertsTrueAssumes allowed) t t') {w : I.World}
    (hA : Trace.AssumptionsHold P I w t) : Trace.AssumptionsHold P I w t' :=
  have ⟨_, h₁, h₂⟩ := h
  h₂.assumptionsHold htrue fun c hc => hA c (h₁.subset hc)

end InsertsTrueAssumes

section InsertsAsserts

variable [HasBool P] {allowed : P.Factory → Prop}

/-- Inserting assertions under some allowed factories inserts them under any larger set of
    allowed factories. -/
theorem Trace.InsertsAsserts.mono_allowed {allowed' : P.Factory → Prop}
    (hmono : ∀ F, allowed F → allowed' F) {t t' : Trace P}
    (h : Trace.InsertsAsserts allowed t t') : Trace.InsertsAsserts allowed' t t' := by
  induction h with
  | nil => exact .nil
  | @keep e e' _ _ he _ ih =>
    refine .keep ?_ ih
    cases e <;> cases e' <;> simp only [Event.SameValue] at he ⊢ <;>
      first | exact he.elim | exact ⟨he.1, he.2.1, hmono _ he.2.2.1, he.2.2.2⟩
  | assert _ ih => exact .assert ih

/-- **Reflecting validity across inserted assertions.**  For an interpretation `I` under which
    conditions with the same value hold alike under allowed factories
    (`EventArg.SameValue`), and a filter `keep` of assertions that depends only on label and
    metadata: when the target `t'` keeps `keep` valid after the assumptions `A'`, and `A'`
    holds where `A` does, then `t` keeps `keep` valid after `A`, and the assumptions of `t'`
    hold where those of `A` and `t` do. -/
theorem Trace.InsertsAsserts.reflect {I : ConditionInterp P}
    (hstable : I.StableUnder (EventArg.SameValue allowed)) {keep : EventArg P → Prop}
    (hkeep : ∀ a b, b.label = a.label → b.metadata = a.metadata → keep a → keep b)
    {t t' : Trace P} (h : Trace.InsertsAsserts allowed t t') :
    ∀ {A A' : Trace P},
    (∀ w, Trace.AssumptionsHold P I w A → Trace.AssumptionsHold P I w A') →
    Trace.AssertionsValidFromP P I keep A' t' →
    Trace.AssertionsValidFromP P I keep A t ∧
      ∀ w, Trace.AssumptionsHold P I w A → Trace.AssumptionsHold P I w t →
        Trace.AssumptionsHold P I w t' := by
  induction h with
  | nil => exact fun _ _ => ⟨trivial, fun _ _ _ => by simp [Trace.AssumptionsHold]⟩
  | @keep e e' t t' he _ ih =>
    intro A A' himp hv
    rcases e with a | a | a <;> rcases e' with b | b | b <;>
      simp only [Event.SameValue] at he <;> try exact he.elim
    · obtain ⟨hl, hm, hs⟩ := he
      obtain ⟨ih₁, ih₂⟩ := ih himp hv.2
      refine ⟨⟨fun hk w hw => (hstable w a b hs).2 (hv.1 (hkeep a b hl hm hk) w (himp w hw)),
        ih₁⟩, fun w hA ht => ?_⟩
      simp only [Trace.assumptionsHold_cons_assert] at ht ⊢
      exact ih₂ w hA ht
    · obtain ⟨-, -, hs⟩ := he
      obtain ⟨ih₁, ih₂⟩ := ih (A := A ++ [.assume a]) (A' := A' ++ [.assume b])
        (fun w hw => by
          rw [Trace.AssumptionsHold_append_assume] at hw ⊢
          exact ⟨himp w hw.1, (hstable w a b hs).1 hw.2⟩) hv
      refine ⟨ih₁, fun w hA ht => ?_⟩
      simp only [Trace.assumptionsHold_cons_assume] at ht ⊢
      exact ⟨(hstable w a b hs).1 ht.1,
        ih₂ w ((Trace.AssumptionsHold_append_assume I w A a).2 ⟨hA, ht.1⟩) ht.2⟩
    · obtain ⟨ih₁, ih₂⟩ := ih himp hv
      refine ⟨ih₁, fun w hA ht => ?_⟩
      simp only [Trace.assumptionsHold_cons_cover] at ht ⊢
      exact ih₂ w hA ht
  | assert _ ih =>
    intro A A' himp hv
    obtain ⟨ih₁, ih₂⟩ := ih himp hv.2
    exact ⟨ih₁, fun w hA ht => by
      simp only [Trace.assumptionsHold_cons_assert]; exact ih₂ w hA ht⟩

/-- Under an interpretation for which conditions with the same value hold alike under allowed
    factories, the validity of the assertions of the target satisfying `keep` implies that of
    the assertions of the source satisfying `keep`, for a filter `keep` depending only on label
    and metadata. -/
theorem Trace.InsertsAsserts.assertionsValidFromP_reflect {I : ConditionInterp P}
    (hstable : I.StableUnder (EventArg.SameValue allowed)) {keep : EventArg P → Prop}
    (hkeep : ∀ a b, b.label = a.label → b.metadata = a.metadata → keep a → keep b)
    {t t' : Trace P} (h : Trace.InsertsAsserts allowed t t')
    (hv : Trace.AssertionsValidFromP P I keep [] t') : Trace.AssertionsValidFromP P I keep [] t :=
  (h.reflect hstable hkeep (fun _ h => h) hv).1

omit [HasBool P] in
/-- No assertion is kept by the empty filter, so every trace keeps it valid. -/
private theorem assertionsValidFromP_false {I : ConditionInterp P} :
    ∀ (A t : Trace P), Trace.AssertionsValidFromP P I (fun _ => False) A t
  | _, [] => trivial
  | _, .assume _ :: rest => assertionsValidFromP_false _ rest
  | _, .assert _ :: rest => ⟨False.elim, assertionsValidFromP_false _ rest⟩
  | _, .cover _ :: rest => assertionsValidFromP_false _ rest

/-- Under an interpretation for which conditions with the same value hold alike under allowed
    factories, the target is reachable where the source is. -/
theorem Trace.InsertsAsserts.reachable_transfer {I : ConditionInterp P}
    (hstable : I.StableUnder (EventArg.SameValue allowed)) {t t' : Trace P}
    (h : Trace.InsertsAsserts allowed t t') (hr : Trace.Reachable P I t) :
    Trace.Reachable P I t' :=
  have ⟨w, hw⟩ := hr
  ⟨w, (h.reflect hstable (keep := fun _ => False) (fun _ _ _ _ h => h) (A := []) (A' := [])
    (fun _ h => h) (assertionsValidFromP_false _ _)).2 w (by simp [Trace.AssumptionsHold]) hw⟩

end InsertsAsserts

section InsertsCheckedAssumes

variable [HasBool P] {allowed : P.Factory → Prop} {Checks : EventArg P → Prop}

/-- Inserting checked assumptions under some allowed factories inserts them under any larger set
    of allowed factories. -/
theorem Trace.InsertsCheckedAssumes.mono_allowed {allowed' : P.Factory → Prop}
    (hmono : ∀ F, allowed F → allowed' F) {before t t' : Trace P}
    (h : Trace.InsertsCheckedAssumes allowed Checks before t t') :
    Trace.InsertsCheckedAssumes allowed' Checks before t t' := by
  induction h with
  | nil => exact .nil
  | keep _ ih => exact .keep ih
  | assumeTrue hf he _ ih => exact .assumeTrue (hmono _ hf) he ih
  | assumeChecked hc hC hs _ ih =>
    exact .assumeChecked hc hC ⟨hmono _ hs.1, hs.2⟩ ih

/-- **Reflecting validity across inserted checked assumptions.**  For an interpretation `I`
    under which conditions with the same value hold alike and true conditions hold, both under
    allowed factories: when the target `t'` keeps (`Checks c ∨ keep c`) valid after the
    assumptions `A'`, its checking assertions before it hold where `A'` does, and `A'` holds
    where `A` does, then `t` keeps `keep` valid after `A`, and the assumptions of `t'` hold
    where those of `A` and `t` do. -/
theorem Trace.InsertsCheckedAssumes.reflect {I : ConditionInterp P}
    (hstable : I.StableUnder (EventArg.SameValue allowed)) (htrue : I.TrueStutterHolds allowed)
    {keep : EventArg P → Prop} {before t t' : Trace P}
    (h : Trace.InsertsCheckedAssumes allowed Checks before t t') :
    ∀ {A A' : Trace P},
    (∀ c, Event.assert c ∈ before → Checks c → ∀ w, Trace.AssumptionsHold P I w A' →
      I.holds w c) →
    (∀ w, Trace.AssumptionsHold P I w A → Trace.AssumptionsHold P I w A') →
    Trace.AssertionsValidFromP P I (fun c => Checks c ∨ keep c) A' t' →
    Trace.AssertionsValidFromP P I keep A t ∧
      ∀ w, Trace.AssumptionsHold P I w A → Trace.AssumptionsHold P I w t →
        Trace.AssumptionsHold P I w t' := by
  -- Membership in the events after an appended non-assertion.
  have hnotAssert : ∀ {b : Trace P} {e : Event P} {c : EventArg P}, (∀ a, e ≠ .assert a) →
      Event.assert c ∈ b ++ [e] → Event.assert c ∈ b := fun hne hc => by
    rcases List.mem_append.1 hc with hc | hc
    · exact hc
    · exact absurd (List.mem_singleton.1 hc).symm (hne _)
  induction h with
  | nil => exact fun _ _ _ => ⟨trivial, fun _ _ _ => by simp [Trace.AssumptionsHold]⟩
  | @keep before e t t' _ ih =>
    intro A A' hC himp hv
    rcases e with a | a | a
    · obtain ⟨ih₁, ih₂⟩ := ih (A := A) (A' := A') (fun c hc hCk w hw => by
          rcases List.mem_append.1 hc with hc | hc
          · exact hC c hc hCk w hw
          · cases List.mem_singleton.1 hc
            exact hv.1 (.inl hCk) w hw) himp hv.2
      refine ⟨⟨fun hk w hw => hv.1 (.inr hk) w (himp w hw), ih₁⟩, fun w hA ht => ?_⟩
      simp only [Trace.assumptionsHold_cons_assert] at ht ⊢
      exact ih₂ w hA ht
    · obtain ⟨ih₁, ih₂⟩ := ih (A := A ++ [.assume a]) (A' := A' ++ [.assume a])
        (fun c hc hCk w hw => hC c (hnotAssert (by simp) hc) hCk w
          ((Trace.AssumptionsHold_append_assume I w A' a).1 hw).1)
        (fun w hw => by
          rw [Trace.AssumptionsHold_append_assume] at hw ⊢
          exact ⟨himp w hw.1, hw.2⟩) hv
      refine ⟨ih₁, fun w hA ht => ?_⟩
      simp only [Trace.assumptionsHold_cons_assume] at ht ⊢
      exact ⟨ht.1, ih₂ w ((Trace.AssumptionsHold_append_assume I w A a).2 ⟨hA, ht.1⟩) ht.2⟩
    · obtain ⟨ih₁, ih₂⟩ := ih (A := A) (A' := A')
        (fun c hc hCk w hw => hC c (hnotAssert (by simp) hc) hCk w hw) himp hv
      refine ⟨ih₁, fun w hA ht => ?_⟩
      simp only [Trace.assumptionsHold_cons_cover] at ht ⊢
      exact ih₂ w hA ht
  | @assumeTrue before a t t' hf he _ ih =>
    intro A A' hC himp hv
    have ha : ∀ w, I.holds w a := htrue a hf he
    obtain ⟨ih₁, ih₂⟩ := ih (A := A) (A' := A' ++ [.assume a])
      (fun c hc hCk w hw => hC c (hnotAssert (by simp) hc) hCk w
        ((Trace.AssumptionsHold_append_assume I w A' a).1 hw).1)
      (fun w hw => (Trace.AssumptionsHold_append_assume I w A' a).2 ⟨himp w hw, ha w⟩) hv
    exact ⟨ih₁, fun w hA ht => by
      simp only [Trace.assumptionsHold_cons_assume]; exact ⟨ha w, ih₂ w hA ht⟩⟩
  | @assumeChecked before a c t t' hc hCk hs _ ih =>
    intro A A' hC himp hv
    have ha : ∀ w, Trace.AssumptionsHold P I w A → I.holds w a :=
      fun w hw => (hstable w c a hs).1 (hC c hc hCk w (himp w hw))
    obtain ⟨ih₁, ih₂⟩ := ih (A := A) (A' := A' ++ [.assume a])
      (fun c' hc' hCk' w hw => hC c' (hnotAssert (by simp) hc') hCk' w
        ((Trace.AssumptionsHold_append_assume I w A' a).1 hw).1)
      (fun w hw => (Trace.AssumptionsHold_append_assume I w A' a).2 ⟨himp w hw, ha w hw⟩) hv
    exact ⟨ih₁, fun w hA ht => by
      simp only [Trace.assumptionsHold_cons_assume]; exact ⟨ha w hA, ih₂ w hA ht⟩⟩

/-- Under an interpretation for which conditions with the same value hold alike and true
    conditions hold, under allowed factories, the validity of the assertions of the target
    satisfying `Checks` or `keep` implies that of the assertions of the source satisfying
    `keep`. -/
theorem Trace.InsertsCheckedAssumes.assertionsValidFromP_reflect {I : ConditionInterp P}
    (hstable : I.StableUnder (EventArg.SameValue allowed)) (htrue : I.TrueStutterHolds allowed)
    {keep : EventArg P → Prop} {t t' : Trace P}
    (h : Trace.InsertsCheckedAssumes allowed Checks [] t t')
    (hv : Trace.AssertionsValidFromP P I (fun c => Checks c ∨ keep c) [] t') :
    Trace.AssertionsValidFromP P I keep [] t :=
  (h.reflect hstable htrue (fun _ hc => by simp at hc) (fun _ h => h) hv).1

/-- Under an interpretation for which conditions with the same value hold alike and true
    conditions hold, under allowed factories, the target is reachable where the source is,
    when its assertions satisfying `Checks` are valid. -/
theorem Trace.InsertsCheckedAssumes.reachable_transfer {I : ConditionInterp P}
    (hstable : I.StableUnder (EventArg.SameValue allowed)) (htrue : I.TrueStutterHolds allowed)
    {t t' : Trace P} (h : Trace.InsertsCheckedAssumes allowed Checks [] t t')
    (hv : Trace.AssertionsValidFromP P I Checks [] t') (hr : Trace.Reachable P I t) :
    Trace.Reachable P I t' :=
  have ⟨w, hw⟩ := hr
  ⟨w, (h.reflect hstable htrue (keep := fun _ => False) (fun _ hc => by simp at hc)
    (fun _ h => h) (Trace.AssertionsValidFromP.mono_keep I (fun _ h => h.elim id False.elim) hv)).2
    w (by simp [Trace.AssumptionsHold]) hw⟩

/-- Inserting assertions, then checked assumptions, under some allowed factories, relates the
    same traces under any larger set of allowed factories. -/
theorem Trace.insertsAsserts_insertsCheckedAssumes_mono {allowed' : P.Factory → Prop}
    (hmono : ∀ F, allowed F → allowed' F) {t t' : Trace P}
    (h : RComp (Trace.InsertsAsserts allowed) (Trace.InsertsCheckedAssumes allowed Checks [])
      t t') :
    RComp (Trace.InsertsAsserts allowed') (Trace.InsertsCheckedAssumes allowed' Checks []) t t' :=
  have ⟨_, h₁, h₂⟩ := h
  ⟨_, h₁.mono_allowed hmono, h₂.mono_allowed hmono⟩

/-- **Validity reflected across inserted assertions and then checked assumptions.**  Under an
    interpretation for which conditions with the same value hold alike and true conditions
    hold, under allowed factories, the validity of the assertions of the target satisfying
    `Checks` or `keep` implies that of the assertions of the source satisfying `keep`, for a
    filter `keep` depending only on label and metadata. -/
theorem Trace.insertsAsserts_insertsCheckedAssumes_assertionsValidFromP_reflect
    {I : ConditionInterp P} (hstable : I.StableUnder (EventArg.SameValue allowed))
    (htrue : I.TrueStutterHolds allowed) {keep : EventArg P → Prop}
    (hkeep : ∀ a b, b.label = a.label → b.metadata = a.metadata → keep a → keep b)
    {t t' : Trace P}
    (h : RComp (Trace.InsertsAsserts allowed) (Trace.InsertsCheckedAssumes allowed Checks [])
      t t')
    (hv : Trace.AssertionsValidFromP P I (fun c => Checks c ∨ keep c) [] t') :
    Trace.AssertionsValidFromP P I keep [] t :=
  have ⟨_, h₁, h₂⟩ := h
  h₁.assertionsValidFromP_reflect hstable hkeep (h₂.assertionsValidFromP_reflect hstable htrue hv)

/-- Under an interpretation for which conditions with the same value hold alike and true
    conditions hold, under allowed factories, the validity of the assertions of the target
    implies that of the assertions of the source, across inserted assertions and then checked
    assumptions. -/
theorem Trace.insertsAsserts_insertsCheckedAssumes_assertionsValid_reflect
    {I : ConditionInterp P} (hstable : I.StableUnder (EventArg.SameValue allowed))
    (htrue : I.TrueStutterHolds allowed) {t t' : Trace P}
    (h : RComp (Trace.InsertsAsserts allowed) (Trace.InsertsCheckedAssumes allowed Checks [])
      t t')
    (hv : Trace.AssertionsValid P I t') : Trace.AssertionsValid P I t :=
  Trace.insertsAsserts_insertsCheckedAssumes_assertionsValidFromP_reflect hstable htrue
    (keep := fun _ => True) (fun _ _ _ _ h => h) h
    (Trace.AssertionsValidFromP.mono_keep I (fun _ _ => trivial) hv)

/-- Under an interpretation for which conditions with the same value hold alike and true
    conditions hold, under allowed factories, the target is reachable where the source is,
    across inserted assertions and then checked assumptions, when the assertions of the target
    satisfying `Checks` are valid. -/
theorem Trace.insertsAsserts_insertsCheckedAssumes_reachable_transfer {I : ConditionInterp P}
    (hstable : I.StableUnder (EventArg.SameValue allowed)) (htrue : I.TrueStutterHolds allowed)
    {t t' : Trace P}
    (h : RComp (Trace.InsertsAsserts allowed) (Trace.InsertsCheckedAssumes allowed Checks [])
      t t')
    (hv : Trace.AssertionsValidFromP P I Checks [] t') (hr : Trace.Reachable P I t) :
    Trace.Reachable P I t' :=
  have ⟨_, h₁, h₂⟩ := h
  h₂.reachable_transfer hstable htrue hv (h₁.reachable_transfer hstable hr)

end InsertsCheckedAssumes

/-- A relation closed under concatenation, relating `a` to `a'`, followed by a nonempty target
    preserving the last event of `b`, preserves the last event of `a ++ b`. -/
theorem Trace.PreservesLastEvent.append_left {R : Trace P → Trace P → Prop}
    (happ : ∀ {a a' b b' : Trace P}, R a a' → R b b' → R (a ++ b) (a' ++ b'))
    {a a' b b' : Trace P} (ha : R a a') (hb : Trace.PreservesLastEvent R b b')
    (hne : b' ≠ []) : Trace.PreservesLastEvent R (a ++ b) (a' ++ b') := by
  rcases hb with ⟨-, rfl⟩ | ⟨pre, pre', e, rfl, rfl, h⟩
  · exact absurd rfl hne
  · exact .inr ⟨a ++ pre, a' ++ pre', e, by simp, by simp, happ ha h⟩

/-- A relation `R` carrying assumption satisfaction from source to target: a target preserving
    the last event of the source, after events related by `R`, followed by any extra events,
    reflects last assertions. -/
theorem Trace.PreservesLastEvent.reflectsLastAssertion {I : ConditionInterp P}
    {R : Trace P → Trace P → Prop} {Extra : Trace P → Prop}
    (hR : ∀ {t t' : Trace P} {w : I.World}, R t t' → Trace.AssumptionsHold P I w t →
      Trace.AssumptionsHold P I w t') :
    Trace.ReflectsLastAssertion I
      (Trace.HasExtraEvents (Trace.PreservesLastEvent R) Extra) := by
  intro pre c target ⟨target₁, extra, htgt, hlast, _⟩
  rcases hlast with ⟨h, -⟩ | ⟨pre₁, pre', e, he, rfl, h⟩
  · simp at h
  · obtain ⟨rfl, he'⟩ := List.append_inj' he rfl
    obtain rfl := List.singleton_inj.1 he'
    exact ⟨pre', extra, by simp [htgt], fun _ hw => hR h hw⟩

end DropsAndInserts

end -- public section
end Imperative
