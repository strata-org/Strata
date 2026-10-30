/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Analysis.ProcedureCorrectness
public import Strata.Transform.CoreSpecificationProps
public import Strata.DL.Imperative.Logic.TerminationProps
import Strata.Languages.Core.StatementSemanticsProps
import Strata.DL.Imperative.CmdSemanticsProps
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.Util.RelationsProps
import all Strata.Languages.Core.Procedure
import all Strata.Util.ListMap

/-! # Correctness of Core procedures: properties

## Key results

- `assertionsValid_postconditionEvents_iff` — checking a procedure's
  postconditions as assertions appended to a trace means the trace is valid
  and each postcondition holds in every world satisfying its assumptions.
- `procedureAssertsValidOnTraces_of_overapproximates` — a transformation that
  overapproximates a procedure body's traces preserves
  `ProcedureAssertsValidOnTraces` backwards.
-/

public section

namespace Core.Specification

open Core Core.Logic Imperative Strata.Logic Imperative.Logic

/-! ## Postconditions checked on the trace

The contract of `ProcedureAssertsValidOnTraces` appends a procedure's
postconditions to each finished run's trace as assertion events. Validity of
the result splits into validity of the run's own trace and each postcondition
holding in every world that satisfies the run's assumptions. -/

/-- Assumptions are the only events `AssumptionsHold` reads. -/
private theorem assumptionsHold_cons_nonassume (I : ConditionInterp Expression)
    (world : I.World) (acc rest : Trace Expression) (e : Event Expression)
    (he : ∀ c, e ≠ Event.assume c) :
    Trace.AssumptionsHold Expression I world (acc ++ e :: rest) ↔
      Trace.AssumptionsHold Expression I world (acc ++ rest) := by
  constructor <;> intro h c hc <;> apply h c
  · rcases List.mem_append.mp hc with hc | hc
    · exact List.mem_append_left _ hc
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hc)
  · rcases List.mem_append.mp hc with hc | hc
    · exact List.mem_append_left _ hc
    · rcases List.mem_cons.mp hc with hc | hc
      · exact absurd hc.symm (he c)
      · exact List.mem_append_right _ hc

/-- Validity of a trace followed by assertions only: the trace's own assertions
    are valid, and each appended assertion holds in every world satisfying the
    trace's assumptions. -/
private theorem assertionsValidFromP_append_asserts (I : ConditionInterp Expression)
    (ps : Trace Expression) (hps : ∀ e ∈ ps, ∃ c, e = Event.assert c) :
    ∀ (tr acc : Trace Expression),
      Trace.AssertionsValidFromP Expression I (fun _ => True) acc (tr ++ ps) ↔
        Trace.AssertionsValidFromP Expression I (fun _ => True) acc tr ∧
        ∀ world, Trace.AssumptionsHold Expression I world (acc ++ tr) →
          ∀ c, Event.assert c ∈ ps → I.holds world c
  | [], acc => by
    simp only [List.nil_append, List.append_nil]
    induction ps with
    | nil => simp [Trace.AssertionsValidFromP]
    | cons e ps ih =>
      obtain ⟨c, rfl⟩ := hps e List.mem_cons_self
      have ih := ih (fun e he => hps e (List.mem_cons_of_mem _ he))
      simp only [Trace.AssertionsValidFromP, ih, List.mem_cons, Event.assert.injEq,
        forall_const, true_and]
      constructor
      · rintro ⟨h1, h2⟩ world hw c' (rfl | hc')
        · exact h1 world hw
        · exact h2 world hw c' hc'
      · intro h
        exact ⟨fun world hw => h world hw c (.inl rfl),
          fun world hw c' hc' => h world hw c' (.inr hc')⟩
  | (.assume c) :: tr, acc => by
    simp only [List.cons_append, Trace.AssertionsValidFromP]
    rw [assertionsValidFromP_append_asserts I ps hps tr]
    simp [List.append_assoc]
  | (.assert c) :: tr, acc => by
    simp only [List.cons_append, Trace.AssertionsValidFromP]
    rw [assertionsValidFromP_append_asserts I ps hps tr]
    have hiff : ∀ world, Trace.AssumptionsHold Expression I world (acc ++ Event.assert c :: tr) ↔
        Trace.AssumptionsHold Expression I world (acc ++ tr) :=
      fun world => assumptionsHold_cons_nonassume I world acc tr _ (by simp)
    simp only [hiff, and_assoc]
  | (.cover c) :: tr, acc => by
    simp only [List.cons_append, Trace.AssertionsValidFromP]
    rw [assertionsValidFromP_append_asserts I ps hps tr]
    have hiff : ∀ world, Trace.AssumptionsHold Expression I world (acc ++ Event.cover c :: tr) ↔
        Trace.AssumptionsHold Expression I world (acc ++ tr) :=
      fun world => assumptionsHold_cons_nonassume I world acc tr _ (by simp)
    simp only [hiff]

/-- A trace followed by a procedure's postcondition events is assertion-valid
    exactly when the trace is, and each postcondition holds in every world that
    satisfies the trace's assumptions. With a single world, this is the clause
    of a Hoare triple: postconditions hold when the trace is reachable. -/
theorem assertionsValid_postconditionEvents_iff (I : ConditionInterp Expression)
    (proc : Procedure) (tr : Trace Expression) (ρ' : Imperative.Env Expression) :
    Trace.AssertionsValid Expression I (tr ++ postconditionEvents proc ρ') ↔
      Trace.AssertionsValid Expression I tr ∧
        ∀ world, Trace.AssumptionsHold Expression I world tr →
          ∀ c, Event.assert c ∈ postconditionEvents proc ρ' → I.holds world c := by
  have hps : ∀ e ∈ postconditionEvents proc ρ', ∃ c, e = Event.assert c := by
    intro e he
    simp only [postconditionEvents, defaultAssertEvents, Imperative.Calls.defaultAssertEvents,
      List.mem_filterMap] at he
    obtain ⟨⟨label, check⟩, _, hc⟩ := he
    by_cases hattr : check.attr = .Default
    · simp only [hattr, ite_true, Option.some.injEq] at hc
      exact ⟨_, hc.symm⟩
    · simp [hattr] at hc
  unfold Trace.AssertionsValid Trace.AssertionsValidFrom
  rw [assertionsValidFromP_append_asserts _ _ hps tr []]
  simp only [List.nil_append]

/-! ## Procedure correctness along trace overapproximation

A transformation that overapproximates a procedure body's traces preserves
`ProcedureAssertsValidOnTraces` backwards: if the transformed procedure is
correct, so is the original. This is the direction an analysis needs, since it
runs on the transformed program and reports on the original.

Each part of `ProcedureAssertsValidOnTraces` transports separately, and neither
needs the body to terminate. Validity on every finite prefix goes through the
overapproximation's clause on prefixes; the contract goes through its
clauses on terminating and exiting runs.

The overapproximation is stated over `EventLang.coreBlock`, on the one-element
statement list holding the body block, which is the statement the
contract reads. The prefix part reads runs of the block itself, so the proof moves
between a run of a statement and a run of the list holding only it.
-/

section OverapproximatesTraces

variable {π : String → Option Procedure}

/-- **Procedure correctness transports back along a trace overapproximation.**

    `T` overapproximates the traces of the source body block, as a one-element
    statement list, by those of the target body block, from entry environments
    the source contract admits. The two procedures have the same header and
    specification, and the axioms visible to the source are visible to the
    target (`h_axioms`). If the target procedure is correct on traces, so is
    the source.

    `ProcEnvWF` makes the source body well formed from its entry environments,
    which is what the overapproximation needs; the overapproximation in turn
    makes the target body well formed from them, so they are entry
    environments of the target too. -/
theorem procedureAssertsValidOnTraces_of_overapproximates
    (I : ConditionInterp Expression) (params : Core.Logic.InitEnvWFParams)
    (name : String) (p p' : Program) (proc proc' : Procedure) (ss ss' : Statements)
    (h_find : p.findProcByString? name = some proc) (h_body : proc.body = .structured ss)
    (h_find' : p'.findProcByString? name = some proc') (h_body' : proc'.body = .structured ss')
    (h_header : proc'.header = proc.header) (h_spec : proc'.spec = proc.spec)
    (h_axioms : ∀ ρ₀, AxiomsBeforeProcedureDecl name p ρ₀ →
      AxiomsBeforeProcedureDecl name p' ρ₀)
    (T : Statements → Option Statements) (pre : Statements → Prop)
    (h_over : Imperative.Specification.Transform.OverapproximatesTracesWhen (· = ·)
      (Core.Logic.EventLang.coreBlock p.findProcByString?)
      (Core.Logic.EventLang.coreBlock p'.findProcByString?) T pre params params)
    (h_T : T [Stmt.block "" ss #[]] = some [Stmt.block "" ss' #[]])
    (h_pre : pre [Stmt.block "" ss #[]])
    (h : ProcedureAssertsValidOnTraces I params name p') :
    ProcedureAssertsValidOnTraces I params name p := by
  have h_sim := fun ρ₀ (hent : ProcEntryEnv params name p proc ρ₀) =>
    h_over _ _ h_T h_pre ρ₀ ρ₀ rfl (hent.1.structuredBodyWF ss h_body)
  have h_entry : ∀ ρ₀, ProcEntryEnv params name p proc ρ₀ →
      ProcEntryEnv params name p' proc' ρ₀ := by
    intro ρ₀ hent
    refine ⟨hent.1.of_sameSignature h_header h_spec ?_ ?_, h_axioms ρ₀ hent.2⟩
    · intro ss'' hb
      rw [h_body'] at hb
      cases hb
      exact (h_sim ρ₀ hent).2.2.2
    · intro cfg hb
      rw [h_body'] at hb
      cases hb
  have h_post : ∀ ρ, postconditionEvents proc' ρ = postconditionEvents proc ρ := by
    intro ρ
    simp only [postconditionEvents, h_spec]
  refine
    { procedureExists := ⟨proc, h_find⟩
      assertsValid := ?_
      contract := ?_ }
  · ----- Validity on every finite prefix -----
    intro a
    obtain ⟨proc'', ss'', hf'', hb'', hv⟩ := h.assertsValid a
    have hproc : proc'' = proc' := Option.some.inj (hf''.symm.trans h_find')
    subst hproc
    have hss : ss'' = ss' := Imperative.Body.structured.inj (hb''.symm.trans h_body')
    subst hss
    refine ⟨proc, ss, h_find, h_body, ?_⟩
    intro ρ₀ cfg tr hent hrun
    obtain ⟨cfg₂, tr₂, hrun₂, rfl⟩ := (h_sim ρ₀ hent).1 _ tr (Core.stmt_run_to_singleton_runE hrun)
    obtain ⟨cfg₃, hrun₃⟩ := Core.singleton_run_to_stmt_runE hrun₂
    exact hv ρ₀ cfg₃ _ (h_entry ρ₀ hent) hrun₃
  · ----- The contract -----
    intro proc'' ss'' hf'' hb''
    have hproc : proc'' = proc := Option.some.inj (hf''.symm.trans h_find)
    subst hproc
    have hss : ss'' = ss := Imperative.Body.structured.inj (hb''.symm.trans h_body)
    subst hss
    have htarget := h.contract proc' ss' h_find' h_body'
    intro ρ₀ ρ' tr hent hrun
    have hr := h_sim ρ₀ hent
    have htgt : ∃ ρ'', ρ' = ρ'' ∧
        (Core.Logic.EventLang.coreBlock p'.findProcByString?).TerminatesAt
          [Stmt.block "" ss' #[]] ρ₀ tr ρ'' := by
      rcases hrun with hterm | ⟨lbl, hexit⟩
      · obtain ⟨ρ'', tr', hrun', henv, rfl⟩ := hr.2.1 ρ' tr hterm
        exact ⟨ρ'', henv, .inl hrun'⟩
      · obtain ⟨ρ'', tr', hrun', henv, rfl⟩ := hr.2.2.1 lbl ρ' tr hexit
        exact ⟨ρ'', henv, .inr ⟨lbl, hrun'⟩⟩
    obtain ⟨ρ'', rfl, htgt⟩ := htgt
    simpa [h_post] using htarget ρ₀ ρ' tr (h_entry ρ₀ hent) htgt

end OverapproximatesTraces

end Core.Specification

end -- public section
