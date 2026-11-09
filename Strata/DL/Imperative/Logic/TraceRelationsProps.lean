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
compact definitions of the trace relations `TraceStuttersEnv` /
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
  forward across `TraceStuttersEnv`, and reflect assertion validity backward,
  under `ConditionInterp.StableUnderExtendsEnv` and
  `ConditionInterp.TrueStutterHolds`.
* **Reflexivity / monotonicity / append laws** for each relation, the
  `TraceStuttersEnv.Cmd.emittedEvents_stuttersEnv` command-snapshot law, and the
  `TraceExtendsEnv.toTraceStuttersEnv` refinement.
* **Semantic matching** `TraceExtendsEnv.toMatches` upgrades lockstep extension
  to a pointwise match under any semantic argument relation, given defined
  source reads and well-formed snapshots; `Event.Matches.comp` and
  `Trace.matches_comp` compose such matches.
* **`WithWF` strengthenings** of `EventArg.ExtendsEnv` (`EventArg.WithWF` is
  defined in `TraceRelations`): `EventArg.WithWF.mono` / `trans` /
  `label_metadata`, with trace-level `Trace.WithWF.append` / `toExtendsEnv` /
  `of_extends` / `mono` / `trans` / `toTraceStuttersEnv` /
  `assertionValidFrom_reflect`.
* **`Trace.WeakensAssumes`** is reflexive and transitive
  (`Trace.WeakensAssumes.refl`, `Trace.WeakensAssumes.trans`), as is its event-level
  counterpart relation `Event.WeakensAssume`.
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

namespace TraceStuttersEnv

/-- Every trace extends itself. -/
theorem refl {P : PureExpr} [HasBool P]
    (allowedVarName : P.Ident → Prop) (allowedFactory : P.Factory → Prop)
    (trace : Trace P) :
    TraceStuttersEnv allowedVarName allowedFactory trace trace := by
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
    (h : TraceStuttersEnv allowedVarName allowedFactory source target) :
    TraceStuttersEnv allowedVarName' allowedFactory source target := by
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
    (h₁ : TraceStuttersEnv allowedVarName allowedFactory source₁ target₁)
    (h₂ : TraceStuttersEnv allowedVarName allowedFactory source₂ target₂) :
    TraceStuttersEnv allowedVarName allowedFactory
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
    (h : TraceStuttersEnv allowedVarName allowedFactory source target) :
    TraceStuttersEnv allowedVarName allowedFactory
      (common ++ source) (common ++ target) :=
  (refl allowedVarName allowedFactory common).append h

end TraceStuttersEnv

/-! ## Semantic transport across `TraceStuttersEnv` -/

section StuttersEnvInterpretation

variable {P : PureExpr} [HasBool P]

/-- `TraceStuttersEnv` transfers assumption satisfaction from source to target:
any world satisfying the source trace's assumptions satisfies the target's.
Dropped-left stutter weakens the source assumptions; inserted-right stutter adds
an assumption the evaluator deemed true (`htrue`); and paired assumptions agree
by stability (`hstable`). -/
theorem TraceStuttersEnv.assumptionsHold_transfer
    {I : ConditionInterp P} {allowedVarName : P.Ident → Prop}
    {allowedFactory : P.Factory → Prop}
    (hstable : I.StableUnderExtendsEnv allowedVarName)
    (htrue : I.TrueStutterHolds allowedFactory)
    {source target : Trace P}
    (h : TraceStuttersEnv allowedVarName allowedFactory source target) :
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

/-- `TraceStuttersEnv` transfers reachability forward: a reachable source trace
has a reachable target trace (same world witness). -/
theorem TraceStuttersEnv.reachable_transfer
    {I : ConditionInterp P} {allowedVarName : P.Ident → Prop}
    {allowedFactory : P.Factory → Prop}
    (hstable : I.StableUnderExtendsEnv allowedVarName)
    (htrue : I.TrueStutterHolds allowedFactory)
    {source target : Trace P}
    (h : TraceStuttersEnv allowedVarName allowedFactory source target)
    (hreach : Trace.Reachable P I source) : Trace.Reachable P I target := by
  obtain ⟨world, hworld⟩ := hreach
  exact ⟨world, TraceStuttersEnv.assumptionsHold_transfer hstable htrue h world hworld⟩

/-- Accumulator-generalized validity reflection: if assumption satisfaction
transfers between related accumulators, target-trace assertion validity reflects
to the source trace. Proved by induction on the trace correspondence. -/
private theorem TraceStuttersEnv.assertionsValidFrom_reflect
    {I : ConditionInterp P} {allowedVarName : P.Ident → Prop}
    {allowedFactory : P.Factory → Prop}
    (hstable : I.StableUnderExtendsEnv allowedVarName)
    (htrue : I.TrueStutterHolds allowedFactory)
    {source target : Trace P}
    (h : TraceStuttersEnv allowedVarName allowedFactory source target) :
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

/-- Whole-trace validity reflection across `TraceStuttersEnv`: target validity
reflects to source validity under semantic stability.  The empty-accumulator
instance of `assertionsValidFrom_reflect`. -/
theorem TraceStuttersEnv.assertionsValid_reflect
    {I : ConditionInterp P} {allowedVarName : P.Ident → Prop}
    {allowedFactory : P.Factory → Prop}
    (hstable : I.StableUnderExtendsEnv allowedVarName)
    (htrue : I.TrueStutterHolds allowedFactory)
    {source target : Trace P}
    (h : TraceStuttersEnv allowedVarName allowedFactory source target)
    (hvalid : Trace.AssertionsValid P I target) :
    Trace.AssertionsValid P I source :=
  TraceStuttersEnv.assertionsValidFrom_reflect hstable htrue h [] [] (fun _ h => h) hvalid

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
`TraceStuttersEnv` lacks: two-sided true-event stuttering would let a middle
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
pointwise (lockstep) step is in particular a non-stuttering `TraceStuttersEnv`
step. -/
theorem toTraceStuttersEnv {P : PureExpr} [HasBool P]
    {allowedVarName : P.Ident → Prop} {allowedFactory : P.Factory → Prop}
    {source target : Trace P}
    (h : TraceExtendsEnv allowedVarName source target) :
    TraceStuttersEnv allowedVarName allowedFactory source target := by
  induction h with
  | nil => exact .nil
  | cons hevent _ ih => exact .lockstep hevent ih

end TraceExtendsEnv

/-- The same command observed in classified extending stores emits
stutter-related traces, as a corollary of its pointwise event correspondence. -/
theorem TraceStuttersEnv.Cmd.emittedEvents_stuttersEnv
    {P : PureExpr} [HasBool P]
    (allowedVarName : P.Ident → Prop) (allowedFactory : P.Factory → Prop)
    (command : Cmd P) (factory : P.Factory)
    {sourceStore targetStore : SemanticStore P}
    (hstore : StoreExtendsWith allowedVarName sourceStore targetStore) :
    TraceStuttersEnv allowedVarName allowedFactory
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
    TraceStuttersEnv Extra allowedFactory source target :=
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

end WeakensAssumes

end -- public section
end Imperative
