/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.TraceInterp
import all Strata.DL.Imperative.Logic.TraceInterp
import all Strata.DL.Imperative.CmdTrace
import all Strata.DL.Imperative.Cmd
import all Strata.Util.ListUtils
import all Strata.Util.ListUtilsProps

---------------------------------------------------------------------
/-! # Deductive trace interpretation metatheory

Proves assertion validity and cover satisfiability under assumption weakening,
together with basic assumption-prefix algebra.

## Key results

- `Trace.AssertionsValidFromP.mono_assumptions` — transports filtered
  assertion validity when accumulated assumptions are strengthened;
  `AssertionsValidFrom` and `AssertionValidFrom` are its two specializations.
- `Trace.AssertionValidFrom.drop_true_assumption` — removes a universally true
  assumption from an accumulated validity prefix.
- `Trace.AssumptionsHold_append_assume` — characterizes assumption satisfaction
  after appending one assumption event.
- `Trace.CoverSatisfiableFrom.mono_assumptions` — preserves per-ID cover
  satisfiability when accumulated assumptions are weakened.
-/

namespace Imperative

public section

/-! ## Trace validity under assumption strengthening -/

/-- Predicate-filtered assertion validity is contravariant in accumulated
assumptions: if `stronger` follows whenever `weaker` holds, validity under
`stronger` implies validity under `weaker`. -/
theorem Trace.AssertionsValidFromP.mono_assumptions
    {P : PureExpr} (I : ConditionInterp P) (keep : EventArg P → Prop)
    {weaker stronger trace : Trace P}
    (himp : ∀ world, Trace.AssumptionsHold P I world weaker →
      Trace.AssumptionsHold P I world stronger)
    (hvalid : Trace.AssertionsValidFromP P I keep stronger trace) :
    Trace.AssertionsValidFromP P I keep weaker trace := by
  induction trace generalizing weaker stronger with
  | nil => trivial
  | cons event rest ih =>
    cases event with
    | assert condition =>
      exact ⟨fun hkeep world hweak => hvalid.1 hkeep world (himp world hweak),
        ih himp hvalid.2⟩
    | assume condition =>
      apply ih (hvalid := hvalid)
      intro world hweakPlus
      intro observed hmem
      rcases List.mem_append.mp hmem with hmem | hsingle
      · exact (himp world (fun c hc => hweakPlus c
          (List.mem_append_left _ hc))) observed hmem
      · have heq : Event.assume observed = Event.assume condition :=
          List.mem_singleton.mp hsingle
        have hcondition : observed = condition := Event.assume.inj heq
        subst observed
        exact hweakPlus condition
          (List.mem_append_right _ (List.mem_singleton_self (Event.assume condition)))
    | cover _ => exact ih himp hvalid

/-- Validity of all assertions is contravariant in accumulated assumptions. -/
theorem Trace.AssertionsValidFrom.mono_assumptions
    {P : PureExpr} (I : ConditionInterp P)
    {weaker stronger trace : Trace P}
    (himp : ∀ world, Trace.AssumptionsHold P I world weaker →
      Trace.AssumptionsHold P I world stronger)
    (hvalid : Trace.AssertionsValidFrom P I stronger trace) :
    Trace.AssertionsValidFrom P I weaker trace :=
  Trace.AssertionsValidFromP.mono_assumptions I (fun _ => True) himp hvalid

/-- Per-identifier assertion validity is contravariant in accumulated assumptions. -/
theorem Trace.AssertionValidFrom.mono_assumptions
    {P : PureExpr} (I : ConditionInterp P) (aid : AssertId P)
    {weaker stronger trace : Trace P}
    (himp : ∀ world, Trace.AssumptionsHold P I world weaker →
      Trace.AssumptionsHold P I world stronger)
    (hvalid : Trace.AssertionValidFrom P I aid stronger trace) :
    Trace.AssertionValidFrom P I aid weaker trace :=
  Trace.AssertionsValidFromP.mono_assumptions I
    (fun condition => condition.label = aid.label ∧ condition.expr = aid.expr)
    himp hvalid

/-- A universally true inserted assumption can be removed from the accumulated
prefix of a per-assert validity proof. -/
theorem Trace.AssertionValidFrom.drop_true_assumption
    {P : PureExpr} (I : ConditionInterp P) (aid : AssertId P)
    {assumptions trace : Trace P} {condition : EventArg P}
    (htrue : ∀ world, I.holds world condition)
    (hvalid : Trace.AssertionValidFrom P I aid
      (assumptions ++ [Event.assume condition]) trace) :
    Trace.AssertionValidFrom P I aid assumptions trace := by
  apply Trace.AssertionValidFrom.mono_assumptions I aid
    (stronger := assumptions ++ [Event.assume condition])
  · intro world h assumptionsEvent hmem
    rcases List.mem_append.mp hmem with hmem | hsingle
    · exact h _ hmem
    · have heq : Event.assume assumptionsEvent = Event.assume condition :=
        List.mem_singleton.mp hsingle
      have hcondition : assumptionsEvent = condition := Event.assume.inj heq
      subst assumptionsEvent
      exact htrue world
  · exact hvalid

/-! ## Assumption-prefix algebra -/

/-- Appending one assumption extends `AssumptionsHold` by exactly that
condition. -/
theorem Trace.AssumptionsHold_append_assume
    {P : PureExpr} (I : ConditionInterp P) (world : I.World)
    (prior : Trace P) (condition : EventArg P) :
    Trace.AssumptionsHold P I world (prior ++ [Event.assume condition]) ↔
      Trace.AssumptionsHold P I world prior ∧ I.holds world condition := by
  constructor
  · intro h
    exact ⟨fun c hc => h c (List.mem_append_left _ hc),
      h condition (List.mem_append_right _ (List.mem_singleton_self _))⟩
  · rintro ⟨hprior, hcondition⟩ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hprior c hc
    · have heq : Event.assume c = Event.assume condition := List.mem_singleton.mp hc
      have : c = condition := Event.assume.inj heq
      subst c
      exact hcondition

/-- Cover satisfiability is preserved when accumulated assumptions are weakened. -/
theorem Trace.CoverSatisfiableFrom.mono_assumptions
    {P : PureExpr} (I : ConditionInterp P) (cid : CoverId P)
    {weaker stronger trace : Trace P}
    (himp : ∀ world, Trace.AssumptionsHold P I world stronger →
      Trace.AssumptionsHold P I world weaker)
    (hcover : Trace.CoverSatisfiableFrom P I cid stronger trace) :
    Trace.CoverSatisfiableFrom P I cid weaker trace := by
  induction trace generalizing weaker stronger with
  | nil => exact hcover
  | cons event rest ih =>
    cases event with
    | assert _ => exact ih himp hcover
    | cover condition =>
      rcases hcover with hhere | hlater
      · obtain ⟨hmatch, world, hstrong, hcondition⟩ := hhere
        exact .inl ⟨hmatch, world, himp world hstrong, hcondition⟩
      · exact .inr (ih himp hlater)
    | assume condition =>
      apply ih (hcover := hcover)
      intro world hstrong
      rw [Trace.AssumptionsHold_append_assume] at hstrong ⊢
      exact ⟨himp world hstrong.1, hstrong.2⟩

/-- Assumption satisfaction ignores a leading assertion. -/
@[simp] theorem Trace.assumptionsHold_cons_assert
    {P : PureExpr} (I : ConditionInterp P) (world : I.World)
    (condition : EventArg P) (rest : Trace P) :
    Trace.AssumptionsHold P I world (Event.assert condition :: rest) ↔
      Trace.AssumptionsHold P I world rest := by
  simp [Trace.AssumptionsHold]

/-- Assumption satisfaction ignores a leading cover. -/
@[simp] theorem Trace.assumptionsHold_cons_cover
    {P : PureExpr} (I : ConditionInterp P) (world : I.World)
    (condition : EventArg P) (rest : Trace P) :
    Trace.AssumptionsHold P I world (Event.cover condition :: rest) ↔
      Trace.AssumptionsHold P I world rest := by
  simp [Trace.AssumptionsHold]

/-- Assumption satisfaction of a leading assumption is its condition together
with satisfaction of the remaining assumptions. -/
@[simp] theorem Trace.assumptionsHold_cons_assume
    {P : PureExpr} (I : ConditionInterp P) (world : I.World)
    (condition : EventArg P) (rest : Trace P) :
    Trace.AssumptionsHold P I world (Event.assume condition :: rest) ↔
      I.holds world condition ∧ Trace.AssumptionsHold P I world rest := by
  constructor
  · intro h
    exact ⟨h condition List.mem_cons_self,
      fun c hc => h c (List.mem_cons_of_mem _ hc)⟩
  · rintro ⟨hcondition, hrest⟩ c hc
    rcases List.mem_cons.mp hc with heq | hc
    · have : c = condition := Event.assume.inj heq
      subst c
      exact hcondition
    · exact hrest c hc

end -- public section
end Imperative
