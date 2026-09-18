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
- `Trace.AssertionsValidFromP.mono_keep`,
  `Trace.AssertionValid.of_assertionsValid`, and
  `Trace.AssertionsValid.of_all_assertionValid` — weaken the assertion filter
  and relate whole-trace validity to pointwise assertion-identifier validity.
- `Trace.AssertionValidFrom.drop_true_assumption` — removes a universally true
  assumption from an accumulated validity prefix.
- `Trace.AssumptionsHold_append_assume` and `Trace.AssumptionsHold_append` —
  characterize assumption satisfaction under trace extension and concatenation.
- `Trace.Reachable.left_of_append` / `right_of_append` — project reachability
  from a concatenated trace to either component.
- `Trace.AssertionsValid.append`, `Trace.AssertionsValid.left_of_append`, and
  `Trace.AssertionsValid.append_of_reachable_left` — compose, restrict, and
  conditionally sequence trace validity.
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

/-! ## Trace validity under `keep` weakening -/

/-- Filtered assertion validity is antimonotone in the `keep` filter: a `weaker`
filter (implied by `stronger`) keeps no more obligations, so validity under the
`stronger` filter implies validity under the `weaker` one. The `keep` predicate
occurs only as the antecedent of each assertion obligation. -/
theorem Trace.AssertionsValidFromP.mono_keep
    {P : PureExpr} (I : ConditionInterp P) {keepStrong keepWeak : EventArg P → Prop}
    {assumptions trace : Trace P}
    (himp : ∀ condition, keepWeak condition → keepStrong condition)
    (hvalid : Trace.AssertionsValidFromP P I keepStrong assumptions trace) :
    Trace.AssertionsValidFromP P I keepWeak assumptions trace := by
  induction trace generalizing assumptions with
  | nil => trivial
  | cons event rest ih =>
    cases event with
    | assert condition =>
      exact ⟨fun hkeep => hvalid.1 (himp condition hkeep), ih hvalid.2⟩
    | assume condition => exact ih hvalid
    | cover _ => exact ih hvalid

/-- Validity of every assertion implies validity of the occurrences matching one
assertion identifier: `AssertionValid` keeps a subset of what `AssertionsValid`
keeps. -/
theorem Trace.AssertionValid.of_assertionsValid
    {P : PureExpr} (I : ConditionInterp P) (aid : AssertId P)
    {trace : Trace P}
    (hvalid : Trace.AssertionsValid P I trace) :
    Trace.AssertionValid P I aid trace :=
  Trace.AssertionsValidFromP.mono_keep I (fun _ _ => trivial) hvalid

/-- Validity of every assertion identifier implies validity of every assertion
occurrence in the trace. -/
theorem Trace.AssertionsValidFrom.of_all_assertionValidFrom
    {P : PureExpr} (I : ConditionInterp P) {assumptions trace : Trace P}
    (hvalid : ∀ aid, Trace.AssertionValidFrom P I aid assumptions trace) :
    Trace.AssertionsValidFrom P I assumptions trace := by
  induction trace generalizing assumptions with
  | nil => trivial
  | cons event rest ih =>
    cases event with
    | assert condition =>
      refine ⟨?_, ih (fun aid => (hvalid aid).2)⟩
      intro _ world hassum
      exact (hvalid ⟨condition.label, condition.expr⟩).1
        ⟨rfl, rfl⟩ world hassum
    | assume _ => exact ih hvalid
    | cover _ => exact ih hvalid

/-- Pointwise validity of every assertion identifier is equivalent to
whole-trace assertion validity. -/
theorem Trace.AssertionsValid.of_all_assertionValid
    {P : PureExpr} (I : ConditionInterp P) {trace : Trace P}
    (hvalid : ∀ aid, Trace.AssertionValid P I aid trace) :
    Trace.AssertionsValid P I trace :=
  Trace.AssertionsValidFrom.of_all_assertionValidFrom I hvalid

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

/-! ## Trace concatenation -/

/-- Assumption satisfaction distributes over trace concatenation. -/
theorem Trace.AssumptionsHold_append
    {P : PureExpr} (I : ConditionInterp P) (world : I.World)
    (left right : Trace P) :
    Trace.AssumptionsHold P I world (left ++ right) ↔
      Trace.AssumptionsHold P I world left ∧
      Trace.AssumptionsHold P I world right := by
  constructor
  · intro h
    exact ⟨fun c hc => h c (List.mem_append_left _ hc),
      fun c hc => h c (List.mem_append_right _ hc)⟩
  · rintro ⟨hl, hr⟩ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hl c hc
    · exact hr c hc

/-- Reachability of a concatenated trace implies reachability of its prefix. -/
theorem Trace.Reachable.left_of_append
    {P : PureExpr} (I : ConditionInterp P) {left right : Trace P}
    (h : Trace.Reachable P I (left ++ right)) : Trace.Reachable P I left := by
  obtain ⟨world, hworld⟩ := h
  exact ⟨world, (Trace.AssumptionsHold_append I world left right).mp hworld |>.1⟩

/-- Reachability of a concatenated trace implies reachability of its suffix. -/
theorem Trace.Reachable.right_of_append
    {P : PureExpr} (I : ConditionInterp P) {left right : Trace P}
    (h : Trace.Reachable P I (left ++ right)) : Trace.Reachable P I right := by
  obtain ⟨world, hworld⟩ := h
  exact ⟨world, (Trace.AssumptionsHold_append I world left right).mp hworld |>.2⟩

/-- Valid traces remain valid when concatenated chronologically. Assumptions in
`left` may additionally discharge assertions in `right`. -/
theorem Trace.AssertionsValidFrom.append
    {P : PureExpr} (I : ConditionInterp P)
    {assumptions left right : Trace P}
    (hleft : Trace.AssertionsValidFrom P I assumptions left)
    (hright : Trace.AssertionsValid P I right) :
    Trace.AssertionsValidFrom P I assumptions (left ++ right) := by
  induction left generalizing assumptions with
  | nil =>
      apply Trace.AssertionsValidFrom.mono_assumptions I
        (stronger := [])
      · intro world _ condition hmem
        simp at hmem
      · exact hright
  | cons event rest ih =>
      cases event with
      | assert _ => exact ⟨hleft.1, ih hleft.2⟩
      | assume _ => exact ih hleft
      | cover _ => exact ih hleft

/-- Concatenating two valid traces yields a valid trace. -/
theorem Trace.AssertionsValid.append
    {P : PureExpr} (I : ConditionInterp P) {left right : Trace P}
    (hleft : Trace.AssertionsValid P I left)
    (hright : Trace.AssertionsValid P I right) :
    Trace.AssertionsValid P I (left ++ right) :=
  Trace.AssertionsValidFrom.append I hleft hright

/-- Validity of a concatenated trace restricts to its chronological prefix. -/
theorem Trace.AssertionsValidFrom.left_of_append
    {P : PureExpr} (I : ConditionInterp P)
    {assumptions left right : Trace P}
    (hvalid : Trace.AssertionsValidFrom P I assumptions (left ++ right)) :
    Trace.AssertionsValidFrom P I assumptions left := by
  induction left generalizing assumptions with
  | nil => trivial
  | cons event rest ih =>
    cases event with
    | assert _ => exact ⟨hvalid.1, ih hvalid.2⟩
    | assume _ => exact ih hvalid
    | cover _ => exact ih hvalid

/-- Validity of all assertions in a concatenated trace implies validity of all
assertions in its prefix. -/
theorem Trace.AssertionsValid.left_of_append
    {P : PureExpr} (I : ConditionInterp P) {left right : Trace P}
    (hvalid : Trace.AssertionsValid P I (left ++ right)) :
    Trace.AssertionsValid P I left :=
  Trace.AssertionsValidFrom.left_of_append I hvalid

/-! ## Validity under an unsatisfiable accumulator -/

/-- When the accumulated assumptions can never be satisfied, every assertion in
the remaining trace is vacuously valid: its guard is discharged by the
impossible antecedent, and later assumptions only strengthen an already
unsatisfiable prefix. -/
theorem Trace.AssertionsValidFrom.of_unsatisfiable_assumptions
    {P : PureExpr} (I : ConditionInterp P) {acc trace : Trace P}
    (hunsat : ∀ world, ¬ Trace.AssumptionsHold P I world acc) :
    Trace.AssertionsValidFrom P I acc trace := by
  induction trace generalizing acc with
  | nil => trivial
  | cons event rest ih =>
    cases event with
    | assert _ =>
        exact ⟨fun _ world hhold => absurd hhold (hunsat world), ih hunsat⟩
    | assume condition =>
        exact ih (fun world hhold =>
          hunsat world
            ((Trace.AssumptionsHold_append_assume I world acc condition).mp hhold).1)
    | cover _ => exact ih hunsat

/-- Chronological concatenation where the suffix need only be valid when the
prefix under the accumulated assumptions is jointly satisfiable. If that
combined prefix is unsatisfiable, the suffix's assertions are vacuously valid. -/
theorem Trace.AssertionsValidFrom.append_cond
    {P : PureExpr} (I : ConditionInterp P) {acc left right : Trace P}
    (hleft : Trace.AssertionsValidFrom P I acc left)
    (hright : Trace.Reachable P I (acc ++ left) →
      Trace.AssertionsValid P I right) :
    Trace.AssertionsValidFrom P I acc (left ++ right) := by
  induction left generalizing acc with
  | nil =>
      simp only [List.append_nil, List.nil_append] at hright ⊢
      by_cases hs : Trace.Reachable P I acc
      · exact Trace.AssertionsValidFrom.mono_assumptions I (stronger := [])
          (fun world _ c hc => by simp at hc) (hright hs)
      · exact Trace.AssertionsValidFrom.of_unsatisfiable_assumptions I
          (fun world hhold => hs ⟨world, hhold⟩)
  | cons event rest ih =>
      cases event with
      | assert condition =>
          refine ⟨hleft.1, ih hleft.2 ?_⟩
          rintro ⟨world, hhold⟩
          refine hright ⟨world, ?_⟩
          rw [Trace.AssumptionsHold_append] at hhold ⊢
          exact ⟨hhold.1,
            (Trace.assumptionsHold_cons_assert I world condition rest).mpr hhold.2⟩
      | assume condition =>
          show Trace.AssertionsValidFrom P I
            (acc ++ [Event.assume condition]) (rest ++ right)
          refine ih hleft ?_
          rintro ⟨world, hhold⟩
          refine hright ⟨world, ?_⟩
          rw [List.append_assoc] at hhold
          exact hhold
      | cover condition =>
          refine ih hleft ?_
          rintro ⟨world, hhold⟩
          refine hright ⟨world, ?_⟩
          rw [Trace.AssumptionsHold_append] at hhold ⊢
          exact ⟨hhold.1,
            (Trace.assumptionsHold_cons_cover I world condition rest).mpr hhold.2⟩

/-- Sequencing rule for assertion validity: the prefix is valid, and the suffix
need only be valid when the prefix is reachable. -/
theorem Trace.AssertionsValid.append_of_reachable_left
    {P : PureExpr} (I : ConditionInterp P) {left right : Trace P}
    (hleft : Trace.AssertionsValid P I left)
    (hright : Trace.Reachable P I left → Trace.AssertionsValid P I right) :
    Trace.AssertionsValid P I (left ++ right) := by
  refine Trace.AssertionsValidFrom.append_cond I hleft (fun hex => hright ?_)
  simpa using hex

end -- public section
end Imperative
