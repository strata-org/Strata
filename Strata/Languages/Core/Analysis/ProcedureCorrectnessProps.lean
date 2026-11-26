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
- `axiomsBeforeProcedureDecl_of_noAxioms`: a procedure preceded by no axiom or
  `distinct` declaration has no axiom assumption at its entry.
- `AxiomsBeforeProcedureDecl.callee`: at a call, the axioms of a callee declared no
  later than the caller follow from the caller's entry, when they read no variable
  (`AxiomsBeforeProcedureDecl.of_declaredBefore`, `AxiomsBeforeProcedureDecl.of_closed`).
- `AxiomsBeforeProcedureDecl.eval_of_mem`, `AxiomsBeforeProcedureDecl.pairwise_of_mem`:
  at an entry satisfying `AxiomsBeforeProcedureDecl`, each axiom declared before the
  procedure evaluates to `true`, and the expressions of each `distinct` declared
  before it evaluate pairwise differently.
-/

public section

namespace Core.Specification

open Core Core.Logic Imperative Strata.Logic Imperative.Logic

/-! ## Axioms and distincts visible to a procedure -/

/-- If no axiom or `distinct` declaration precedes `entryProcName`, every environment
    satisfies `AxiomsBeforeProcedureDecl`. -/
theorem axiomsBeforeProcedureDecl_of_noAxioms {entryProcName : String} {p : Program}
    (h : (p.declsBeforeProcedure entryProcName).all fun d =>
      match d with
      | .ax _ _ | .distinct _ _ _ => false
      | _ => true)
    (ρ₀ : Imperative.Env Expression) :
    AxiomsBeforeProcedureDecl entryProcName p ρ₀ := by
  simp only [List.all_eq_true] at h
  unfold AxiomsBeforeProcedureDecl
  generalize p.declsBeforeProcedure entryProcName = decls at h
  induction decls with
  | nil => trivial
  | cons d ds ih =>
      rw [List.foldr_cons]
      have hd := h d List.mem_cons_self
      have hds := ih fun d hdmem => h d (List.mem_cons_of_mem _ hdmem)
      cases d <;> simp at hd
      all_goals exact hds

/-- Each axiom declared before `entryProcName` evaluates to `true` in an environment
    satisfying `AxiomsBeforeProcedureDecl`. -/
theorem AxiomsBeforeProcedureDecl.eval_of_mem {entryProcName : String} {p : Program}
    {ρ₀ : Imperative.Env Expression}
    (h : AxiomsBeforeProcedureDecl entryProcName p ρ₀)
    {a : Axiom} {md : Imperative.MetaData Expression}
    (ha : Decl.ax a md ∈ p.declsBeforeProcedure entryProcName) :
    Expression.eval ρ₀.factory ρ₀.store a.e = some (HasBool.ttVal ρ₀.factory) := by
  unfold AxiomsBeforeProcedureDecl at h
  generalize p.declsBeforeProcedure entryProcName = decls at h ha
  induction decls with
  | nil => cases ha
  | cons d ds ih =>
    rcases List.mem_cons.mp ha with rfl | hm
    · exact h.1
    · cases d <;> simp only [List.foldr_cons] at h <;> first | exact ih h.2 hm | exact ih h hm

/-- The expressions of each `distinct` declaration before `entryProcName` evaluate
    pairwise differently in an environment satisfying `AxiomsBeforeProcedureDecl`. -/
theorem AxiomsBeforeProcedureDecl.pairwise_of_mem {entryProcName : String} {p : Program}
    {ρ₀ : Imperative.Env Expression}
    (h : AxiomsBeforeProcedureDecl entryProcName p ρ₀)
    {name : Expression.Ident} {es : List Expression.Expr}
    {md : Imperative.MetaData Expression}
    (hd : Decl.distinct name es md ∈ p.declsBeforeProcedure entryProcName) :
    List.Pairwise (fun e₁ e₂ =>
      Expression.eval ρ₀.factory ρ₀.store e₁ ≠ Expression.eval ρ₀.factory ρ₀.store e₂) es := by
  unfold AxiomsBeforeProcedureDecl at h
  generalize p.declsBeforeProcedure entryProcName = decls at h hd
  induction decls with
  | nil => cases hd
  | cons d ds ih =>
    rcases List.mem_cons.mp hd with rfl | hm
    · exact h.1
    · cases d <;> simp only [List.foldr_cons] at h <;> first | exact ih h.2 hm | exact ih h hm

/-! ### Axioms at a call

A call needs the callee's axioms at the callee's entry store
(`Hoare.Procedure.call_of_contract`). The caller has its own axioms at its entry. When the
callee is declared no later than the caller, its axioms are among the caller's, and when
they read no variable they hold in every store over the same factory. A run keeps the
factory, so the caller's entry assumption gives the callee's at every call. -/

/-- **Closed axioms hold by the factory alone.** If the axioms and `distinct` declarations
    before `entryProcName` read no variable, they hold in an environment once they hold in
    one with the same factory. -/
theorem AxiomsBeforeProcedureDecl.of_closed {entryProcName : String} {p : Program}
    {ρ ρ' : Imperative.Env Expression}
    (hclosed : p.axiomsClosedBeforeProcedure entryProcName = Bool.true)
    (hfac : ρ.factory = ρ'.factory)
    (h : AxiomsBeforeProcedureDecl entryProcName p ρ) :
    AxiomsBeforeProcedureDecl entryProcName p ρ' := by
  obtain ⟨σ, f⟩ := ρ
  obtain ⟨σ', f'⟩ := ρ'
  obtain rfl : f = f' := hfac
  -- a closed expression evaluates alike in every store
  have heval : ∀ {e : Expression.Expr} (σ₁ σ₂ : CoreStore), e.freeVars.isEmpty = Bool.true →
      Expression.eval f σ₁ e = Expression.eval f σ₂ e := fun {e} _ _ he =>
    Lambda.LExpr.denoteEval_congr e fun _ _ hx => by
      rw [List.isEmpty_iff.mp he] at hx; cases hx
  unfold AxiomsBeforeProcedureDecl at h ⊢
  unfold Program.axiomsClosedBeforeProcedure at hclosed
  rw [List.all_eq_true] at hclosed
  generalize p.declsBeforeProcedure entryProcName = decls at h hclosed
  induction decls with
  | nil => trivial
  | cons d ds ih =>
    have hd := hclosed d List.mem_cons_self
    have hds := fun h' => ih h' fun d hdm => hclosed d (List.mem_cons_of_mem _ hdm)
    cases d with
    | ax a md =>
      simp only [List.foldr_cons] at h ⊢
      exact ⟨(heval σ' σ hd).trans h.1, hds h.2⟩
    | distinct name es md =>
      simp only [List.foldr_cons] at h ⊢
      have hes := List.all_eq_true.mp hd
      exact ⟨h.1.imp_of_mem fun {e₁ e₂} h₁ h₂ hne heq => hne <|
        (heval σ σ' (hes e₁ h₁)).trans <| heq.trans (heval σ' σ (hes e₂ h₂)), hds h.2⟩
    | _ => simpa only [List.foldr_cons] using hds (by simpa only [List.foldr_cons] using h)

/-- **A procedure declared no later sees no more axioms.** If the declarations before
    `callee` are at most as many as those before `caller`, an environment that satisfies
    the axioms before `caller` satisfies those before `callee`. -/
theorem AxiomsBeforeProcedureDecl.of_declaredBefore {caller callee : String} {p : Program}
    {ρ : Imperative.Env Expression}
    (hbefore : (p.declsBeforeProcedure callee).length ≤ (p.declsBeforeProcedure caller).length)
    (h : AxiomsBeforeProcedureDecl caller p ρ) :
    AxiomsBeforeProcedureDecl callee p ρ := by
  obtain ⟨rest, hrest⟩ : p.declsBeforeProcedure callee <+: p.declsBeforeProcedure caller :=
    List.prefix_of_prefix_length_le (List.takeWhile_prefix _) (List.takeWhile_prefix _) hbefore
  unfold AxiomsBeforeProcedureDecl at h ⊢
  rw [← hrest] at h
  generalize p.declsBeforeProcedure callee = decls at h
  induction decls with
  | nil => trivial
  | cons d ds ih =>
    cases d <;> simp only [List.cons_append, List.foldr_cons] at h ⊢ <;>
      first | exact ⟨h.1, ih h.2⟩ | exact ih h

/-- **The callee's axioms at a call, from the caller's entry.** Let `callee` be declared no
    later than `caller`, with axioms and `distinct` declarations that read no variable. An
    environment that satisfies the axioms before `caller` gives, for every store over its
    factory, an environment that satisfies the axioms before `callee`. This is the premise
    `haxioms` of `Hoare.Procedure.call_of_contract`, since a run keeps the factory. -/
theorem AxiomsBeforeProcedureDecl.callee {caller callee : String} {p : Program}
    {ρ ρ' : Imperative.Env Expression}
    (hbefore : (p.declsBeforeProcedure callee).length ≤ (p.declsBeforeProcedure caller).length)
    (hclosed : p.axiomsClosedBeforeProcedure callee = Bool.true)
    (hfac : ρ.factory = ρ'.factory)
    (h : AxiomsBeforeProcedureDecl caller p ρ) :
    AxiomsBeforeProcedureDecl callee p ρ' :=
  (h.of_declaredBefore hbefore).of_closed hclosed hfac


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
    specification, the axioms visible to the source are visible to the
    target (`h_axioms`), and both see the same factory (`h_factory`). If the
    target procedure is correct on traces, so is the source.

    `ProcEnvWF` makes the source body well formed from its entry environments,
    which is what the overapproximation needs; the overapproximation in turn
    makes the target body well formed from them, so they are entry
    environments of the target too. -/
theorem procedureAssertsValidOnTraces_of_overapproximates
    (I : ConditionInterp Expression) (params : Core.Logic.InitEnvWFParams)
    (name : String) (p p' : Program) (proc proc' : Procedure) (ss ss' : Statements)
    (h_find : p.findProcByString? name = some proc) (h_body : proc.body = .structured ss opq)
    (h_find' : p'.findProcByString? name = some proc') (h_body' : proc'.body = .structured ss' opq)
    (h_header : proc'.header = proc.header) (h_spec : proc'.spec = proc.spec)
    (h_axioms : ∀ ρ₀, AxiomsBeforeProcedureDecl name p ρ₀ →
      AxiomsBeforeProcedureDecl name p' ρ₀)
    (h_factory : p'.factoryBeforeProcedure name = p.factoryBeforeProcedure name)
    (T : Statements → Option Statements) (pre : Statements → Prop)
    (h_over : Imperative.Specification.Transform.OverapproximatesTracesWhen (· = ·)
      (Core.Logic.EventLang.coreBlock p.findProcByString?)
      (Core.Logic.EventLang.coreBlock p'.findProcByString?) T pre params params)
    (h_T : T [Stmt.block "" ss #[]] = some [Stmt.block "" ss' #[]])
    (h_pre : pre [Stmt.block "" ss #[]])
    (h : ProcedureAssertsValidOnTraces I params name p') :
    ProcedureAssertsValidOnTraces I params name p := by
  have h_sim := fun ρ₀ (hent : ProcEntryEnv params name p proc ρ₀) =>
    h_over _ _ h_T h_pre ρ₀ ρ₀ rfl (hent.1.structuredBodyWF ss _ h_body)
  have h_entry : ∀ ρ₀, ProcEntryEnv params name p proc ρ₀ →
      ProcEntryEnv params name p' proc' ρ₀ := by
    intro ρ₀ hent
    refine ⟨hent.1.of_sameSignature h_header h_spec ?_ ?_, h_axioms ρ₀ hent.2.1,
      hent.2.2.trans h_factory.symm⟩
    · intro ss'' _ hb
      rw [h_body'] at hb
      cases hb
      exact (h_sim ρ₀ hent).2.2.2
    · intro cfg _ hb
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
    obtain ⟨proc'', ss'', _, hf'', hb'', hv⟩ := h.assertsValid a
    have hproc : proc'' = proc' := Option.some.inj (hf''.symm.trans h_find')
    subst hproc
    have hss : ss'' = ss' := (Imperative.Body.structured.inj (hb''.symm.trans h_body')).1
    subst hss
    refine ⟨proc, ss, _, h_find, h_body, ?_⟩
    intro ρ₀ cfg tr hent hrun
    obtain ⟨cfg₂, tr₂, hrun₂, rfl⟩ := (h_sim ρ₀ hent).1 _ tr (Core.stmt_run_to_singleton_runE hrun)
    obtain ⟨cfg₃, hrun₃⟩ := Core.singleton_run_to_stmt_runE hrun₂
    exact hv ρ₀ cfg₃ _ (h_entry ρ₀ hent) hrun₃
  · ----- The contract -----
    intro proc'' ss'' _ hf'' hb''
    have hproc : proc'' = proc := Option.some.inj (hf''.symm.trans h_find)
    subst hproc
    have hss : ss'' = ss := (Imperative.Body.structured.inj (hb''.symm.trans h_body)).1
    subst hss
    have htarget := h.contract proc' ss' _ h_find' h_body'
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
