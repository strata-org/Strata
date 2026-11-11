/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Analysis.DeductiveVerification
public import Strata.Languages.Core.Analysis.ProcedureCorrectnessProps
public import Strata.DL.Imperative.Analysis.DeductiveVerificationProps
public import Strata.DL.Imperative.Analysis.DefinitionsProps
public import Strata.Languages.Core.Logic.TraceInterpUsingDenoteProps
import Strata.Languages.Core.IntEvalProps
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.DL.Lambda.LExprWFProps
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.DL.Imperative.Logic.TraceInterpProps
import Strata.Languages.Core.ProgramProps

/-! # Deductive verification of Core programs: properties

## Key results

- `Analysis.isDeductiveVerifier_pipelineVerify` — a pipeline of phases that each
  overapproximate the runs of every entry point, followed by a deductive
  verifier, is a deductive verifier.
- `Analysis.PhaseOverapproximates.preservesDeductiveVerification` — such a
  phase meets `PhasePreservesDeductiveVerification`, the per-phase hypothesis of
  `CoreVerifyIsDeductive`.
- `Analysis.deductiveVerificationOnCoreWith_of_overapproximates` — deductive
  verification carries back from a program whose entries' runs overapproximate
  another's.
- `Analysis.PhaseOverapproximatesFrom.preservesDeductiveVerification` — a phase that
  overapproximates the runs of every entry meets `PhasePreservesDeductiveVerificationFrom`.
- `Analysis.deductiveVerificationOnCore_of_with` — deductive verification over a base factory
  implies deductive verification as `DeductiveVerificationOnCore` reads it.
- `Analysis.PhasesRun.preservesDeductiveVerification` — a pipeline of phases that each
  preserve deductive verification under a kept invariant preserves it.
- `Analysis.declFormulasTyped_eval_isSome` — a declaration's closed Boolean formulas have a
  value in every model.
- `Analysis.formulasTypedB_eval_isSome` — the same, for every declaration of a program that
  passes `Program.formulasTypedB`.
- `Analysis.distinctPairExpr_holds_iff` — the declarations entry and a procedure entry read a
  `distinct` pair the same way when both expressions have values of one sort.
- `Analysis.declsRun_trace`, `Analysis.declsRun_full` — the traces of a run from the
  declarations entry.
- `Analysis.assumptionsHold_declsTrace` — the assumptions of a declarations trace hold exactly
  when the declarations' facts do (`DeclsFactsHold`).
- `Analysis.assertionsValidFromP_declsTrace` — when the assertions of a declarations trace are
  valid.
- `Analysis.DeclsReflect.runsOverapproximate` — runs from two declarations entries
  overapproximate each other when the declarations reflect each other.
- `Analysis.deductiveVerificationOnCoreWith_of_declsReflect` — deductive verification carries
  back from `p'` to a program `p` without entry procedures.
- `Analysis.PhaseReflectsLemmas.preservesDeductiveVerification` — a phase that reflects the
  declarations entry preserves deductive verification on programs without procedures
  (`NoProcedures`).
- `Analysis.PhaseReflectsLemmas.overapproximates` — on such programs it meets
  `PhaseOverapproximatesFrom`, the contract over every entry.

How the reading of `DeductiveVerificationOnCore` (evaluation to `true`) relates to
`DenoteBasedInterp F` is `Core.Logic.evalInterp_holds_iff_denoteBasedInterp`
(`Strata.Languages.Core.Logic.TraceInterpUsingDenoteProps`); the former name
`Core.Specification.evalInterp_holds_iff_denoteBasedInterp` remains as a deprecated alias.
-/

public section

namespace Core.Specification

open Core Core.Logic Imperative Strata.Logic Imperative.Logic

/-- For a condition captured under a runtime factory over `F`, reading it under its own
    runtime factory (`Imperative.BigStep.evalInterp`) agrees with `DenoteBasedInterp F` in
    every world.  Deprecated: use `Core.Logic.evalInterp_holds_iff_denoteBasedInterp`. -/
@[deprecated Core.Logic.evalInterp_holds_iff_denoteBasedInterp (since := "2026-11-11")]
theorem evalInterp_holds_iff_denoteBasedInterp {F : Lambda.Factory Core.CoreLParams}
    (w : (DenoteBasedInterp F).World) (c : Imperative.EventArg Expression)
    (hc : c.factory.factory = F) :
    (Imperative.BigStep.evalInterp : ConditionInterp Expression).holds () c ↔
      (DenoteBasedInterp F).holds w c :=
  Core.Logic.evalInterp_holds_iff_denoteBasedInterp w c hc

/-! ## Pipelines of overapproximating phases -/

namespace Analysis

/-- `vcResultsVerdict` claims only `valid` or `unknown`, so reading it back
    through `keepValid` changes nothing. -/
private theorem vcResultsVerdict_keepValid {E : Type _} {E' : Type _} (results : VCResults)
    (a : Imperative.AssertId Expression) :
    (vcResultsVerdict (Entry := E) results a).keepValid = vcResultsVerdict (Entry := E') results a := by
  unfold vcResultsVerdict
  split <;> rfl

/-- Deductive verification of a program whose entries' runs overapproximate those of
    another program's entries carries back to that program. -/
theorem deductiveVerificationOnCoreWith_of_overapproximates
    {base base' : Lambda.Factory CoreLParams} {p p' : Program}
    (hover : ∀ w, IsCoreEntryAt base p w →
      ∃ w', w.Corresponds w' ∧ IsCoreEntryAt base' p' w' ∧
        (coreEventLangWithDecls (coreStartWithDecls p w).1).RunsOverapproximate
          (Strata.Analysis.ValidityReflected Imperative.BigStep.evalInterp)
          (coreEventLangWithDecls (coreStartWithDecls p' w').1)
            (coreStartWithDecls p w).2 (coreStartWithDecls p' w').2)
    {entryPoints : List String} {results : VCResults}
    (hdv : DeductiveVerificationOnCoreWith base' ⟨entryPoints, p'⟩ results) :
    DeductiveVerificationOnCoreWith base ⟨entryPoints, p⟩ results := by
  have hv := Strata.Analysis.DeductiveVerification.of_runsOverapproximate
    (E₁ := coreEntriesFrom base) (E₂ := coreEntriesFrom base')
    (p₁ := (⟨entryPoints, p⟩ : CoreVerifierInput)) (p₂ := (⟨entryPoints, p'⟩ : CoreVerifierInput))
    (fun w hw => by
      have hw' : IsCoreEntryAt base p w := by
        cases w with
        | proc => exact hw.2
        | decls => exact hw
      obtain ⟨w', hcorr, hw'', hov⟩ := hover w hw'
      refine ⟨w', ?_, hov⟩
      cases w with
      | proc v =>
        cases w' with
        | proc v' =>
          have hn : v'.procName = v.procName := hcorr
          exact ⟨hn ▸ hw.1, hw''⟩
        | decls => exact hcorr.elim
      | decls =>
        cases w' with
        | proc => exact hcorr.elim
        | decls => exact hw'')
    (fun _ _ h => h) hdv
  simp only [vcResultsVerdict_keepValid] at hv
  exact hv

/-- **A phase that overapproximates the runs of every entry preserves deductive
    verification backwards.** -/
theorem PhaseOverapproximatesFrom.preservesDeductiveVerification
    {pre : Transform.CoreTransformState → Program → Prop} {phase : PipelinePhase}
    (h : PhaseOverapproximatesFrom pre phase) :
    PhasePreservesDeductiveVerificationFrom pre phase :=
  fun s p s' p' hpre hrun _ _ hdv =>
    deductiveVerificationOnCoreWith_of_overapproximates (h s p s' p' hpre hrun) hdv

/-- **A closed Boolean formula has a value** in every model, under every store: the direction
    of `declFormulasTyped` the declarations entry needs. -/
theorem declFormulasTyped_eval_isSome {d : Decl} (h : declFormulasTyped d = Bool.true)
    (f : Expression.Factory) (σ : CoreStore) {e : Expression.Expr} (he : e ∈ declFormulas d) :
    (Expression.eval f σ e).isSome := by
  have he' := List.all_eq_true.mp h e he
  simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at he'
  obtain ⟨hfv, hty⟩ := he'
  have hT : (e.annotateFvars (Lambda.ValStore.ann (T := CoreLParams) σ)).HasTypeA [] .bool := by
    rw [Lambda.LExpr.annotateFvars_eq_self e (fun x ty hx => by simp [hfv] at hx)]
    exact Lambda.LExpr.typeCheck_to_HasTypeA hty
  have hd : Lambda.ValStore.Defines (T := CoreLParams) σ f.model.tcInterp e := fun x hx => by
    rw [Lambda.getVars_eq_freeVars_idents, hfv] at hx; simp at hx
  rw [Expression.eval_eq, Lambda.LExpr.denoteEval_of_hasTypeA hd hT rfl]
  rfl

/-- **Every declaration formula of a program that passes `Program.formulasTypedB` has a value**
    in every model, under every store. -/
theorem formulasTypedB_eval_isSome {p : Program} (h : Program.formulasTypedB p = Bool.true)
    {d : Decl} (hd : d ∈ p.decls) (f : Expression.Factory) (σ : CoreStore)
    {e : Expression.Expr} (he : e ∈ declFormulas d) : (Expression.eval f σ e).isSome :=
  declFormulasTyped_eval_isSome (List.all_eq_true.mp h d hd) f σ he

/-- A procedure entry over any base is an entry of mainline's procedure entries. A bridge
    between the two sets of entry definitions, to be retired when `CoreEntry` and
    `IsCoreEntry` are extended in place to cover declarations. -/
theorem isCoreEntryAt_proc_iff {base : Lambda.Factory CoreLParams} {p : Program}
    {w : CoreEntry} : IsCoreEntryAt base p (.proc w) ↔ IsCoreEntry p w :=
  Iff.rfl

/-- **Deductive verification over a base factory is deductive verification as mainline
    reads it**, which has only the procedure entries: those are entries of the program
    over any base, with the same runs and the same reading of conditions. A bridge, to be
    retired with the parallel definitions once `CoreEntry` covers declarations. -/
theorem deductiveVerificationOnCore_of_with {base : Lambda.Factory CoreLParams}
    {input : CoreVerifierInput} {results : VCResults}
    (h : DeductiveVerificationOnCoreWith base input results) :
    DeductiveVerificationOnCore input results := by
  have hv := Strata.Analysis.DeductiveVerification.of_runsOverapproximate
    (E₁ := coreEntries) (E₂ := coreEntriesFrom base) (p₁ := input) (p₂ := input)
    (R := fun t t' => t = t')
    (fun w hw => ⟨.proc w, hw, fun n t c hr => ⟨n, t, c, hr, rfl⟩⟩)
    (fun _ _ ht => ht ▸ fun _ ha => ha) h
  simp only [vcResultsVerdict_keepValid] at hv
  exact hv

/-- **The two entries read a `distinct` pair the same way** when both expressions have
    values of one sort: the declarations entry assumes `distinctPairExpr a b`
    (`declAssumes`), and a procedure entry assumes that the values of `a` and `b` differ
    (`AxiomsBeforeProcedureDecl`). Type checking does not yet require one sort. -/
theorem distinctPairExpr_holds_iff {f : Expression.Factory} {σ : CoreStore}
    {a b : Expression.Expr} {va vb : Expression.Val}
    (ha : Expression.eval f σ a = some va) (hb : Expression.eval f σ b = some vb)
    (hs : va.sort = vb.sort) :
    Expression.eval f σ (distinctPairExpr a b) = some (HasBool.ttVal f) ↔
      Expression.eval f σ a ≠ Expression.eval f σ b := by
  have hF := eval_boolConst f (m := ()) σ Bool.false
  have hT := eval_boolConst f (m := ()) σ Bool.true
  unfold distinctPairExpr
  rw [ha, hb]
  by_cases hab : va = vb
  · subst hab
    rw [eval_ite f (eval_eq_true f ha hb) hF hT rfl]
    simp only [↓reduceIte, ne_eq, not_true_eq_false, iff_false]
    intro h
    exact HasBool.ttVal_ne_ffVal f (Option.some.inj h).symm
  · rw [eval_ite f (eval_eq_false f ha hb hs hab) hF hT rfl]
    simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, Option.some.injEq, hab, not_false_eq_true,
      iff_true]
    rfl

/-- A phase that preserves deductive verification from what `pre` admits preserves it from
    what any stronger `pre'` admits. -/
theorem PhasePreservesDeductiveVerificationFrom.mono
    {pre pre' : Transform.CoreTransformState → Program → Prop} {phase : PipelinePhase}
    (h : PhasePreservesDeductiveVerificationFrom pre phase) (hle : ∀ s p, pre' s p → pre s p) :
    PhasePreservesDeductiveVerificationFrom pre' phase :=
  fun s p s' p' hp hrun => h s p s' p' (hle s p hp) hrun

/-- **A pipeline of phases that each preserve deductive verification preserves it**, from
    the states and programs an invariant `Inv` admits, when every phase keeps `Inv` and
    preserves deductive verification from what `Inv` admits. A phase proved from a weaker
    precondition meets the second hypothesis through
    `PhasePreservesDeductiveVerificationFrom.mono`. -/
theorem PhasesRun.preservesDeductiveVerification
    {Inv : Transform.CoreTransformState → Program → Prop} {phases : List PipelinePhase}
    (hkeep : ∀ phase ∈ phases, ∀ s p s' p', Inv s p → phase.Runs s p s' p' → Inv s' p')
    (hpres : ∀ phase ∈ phases, PhasePreservesDeductiveVerificationFrom Inv phase)
    {s s' : Transform.CoreTransformState} {p p' : Program}
    (hinv : Inv s p) (hrun : PhasesRun phases s p s' p')
    {entryPoints : List String} {results : VCResults}
    (hdv : DeductiveVerificationOnCoreWith s'.factory ⟨entryPoints, p'⟩ results) :
    DeductiveVerificationOnCoreWith s.factory ⟨entryPoints, p⟩ results := by
  induction hrun with
  | nil => exact hdv
  | @cons phase rest s p s₁ p₁ s' p' hone _ ih =>
    have hmem : phase ∈ phase :: rest := List.mem_cons_self
    have h₁ := ih (fun q hq => hkeep q (List.mem_cons_of_mem _ hq))
      (fun q hq => hpres q (List.mem_cons_of_mem _ hq)) (hkeep phase hmem s p s₁ p₁ hinv hone) hdv
    exact hpres phase hmem s p s₁ p₁ hinv hone entryPoints results h₁

/-- The empty result array reports `unknown` for every assertion. -/
private theorem vcResultsVerdict_empty {E : Type _} (a : Imperative.AssertId Expression) :
    vcResultsVerdict (Entry := E) #[] a = .unknown none := by
  simp [vcResultsVerdict]

/-- Validity reflection composed with itself is validity reflection. -/
private theorem validityReflected_comp
    {t t' : List (Event Expression)}
    (h : RComp (Strata.Analysis.ValidityReflected Imperative.BigStep.evalInterp)
      (Strata.Analysis.ValidityReflected Imperative.BigStep.evalInterp) t t') :
    Strata.Analysis.ValidityReflected Imperative.BigStep.evalInterp t t' :=
  RComp.collapse (Strata.Analysis.ValidityReflected.trans _) (fun _ _ h => h) (fun _ _ h => h) h

/-- The identity pipeline overapproximates. -/
private theorem phaseOverapproximates_some :
    PhaseOverapproximates (fun p p' => some p = some p') := by
  intro p p' h w hw
  cases h
  exact ⟨w, rfl, hw,
    EventLang.RunsOverapproximate.refl (Strata.Analysis.ValidityReflected.refl _) _⟩

/-- Running phases that each overapproximate overapproximates. -/
private theorem phaseOverapproximates_runPhases :
    ∀ phases : List (Program → Option Program),
      (∀ phase ∈ phases, PhaseOverapproximates (fun p p' => phase p = some p')) →
      PhaseOverapproximates (fun p p' => runPhases phases p = some p')
  | [], _ => phaseOverapproximates_some
  | phase :: rest, h => by
    intro p p'' hrun w hw
    simp only [runPhases, Option.bind_eq_some_iff] at hrun
    obtain ⟨p', hphase, hrest⟩ := hrun
    obtain ⟨w', hname', hw', hover⟩ :=
      h phase (List.mem_cons_self ..) p p' hphase w hw
    obtain ⟨w'', hname'', hw'', hover'⟩ :=
      phaseOverapproximates_runPhases rest (fun q hq => h q (List.mem_cons_of_mem _ hq))
        p' p'' hrest w' hw'
    exact ⟨w'', hname''.trans hname', hw'',
      (hover.trans hover').mono fun _ _ h => validityReflected_comp h⟩

/-- Deductive verification of the program a phase produces is deductive
    verification of its input, when the phase overapproximates. -/
private theorem deductiveVerificationOnCore_of_overapproximates
    {R : Program → Program → Prop}
    (h : PhaseOverapproximates R) {p p' : Program} (hR : R p p')
    {entryPoints : List String} {results : VCResults}
    (hdv : DeductiveVerificationOnCore ⟨entryPoints, p'⟩ results) :
    DeductiveVerificationOnCore ⟨entryPoints, p⟩ results := by
  have hv := Strata.Analysis.DeductiveVerification.of_runsOverapproximate
    (E₁ := coreEntries) (E₂ := coreEntries)
    (p₁ := (⟨entryPoints, p⟩ : CoreVerifierInput)) (p₂ := (⟨entryPoints, p'⟩ : CoreVerifierInput))
    (fun w ⟨hmem, hw⟩ => by
      obtain ⟨w', hname, hw', hover⟩ := h p p' hR w hw
      refine ⟨w', ⟨hname ▸ hmem, hw'⟩, ?_⟩
      exact hover)
    (fun _ _ h => h) hdv
  simp only [vcResultsVerdict_keepValid] at hv
  exact hv

/-- **A phase that overapproximates the runs of every entry point preserves
    deductive verification backwards.** -/
theorem PhaseOverapproximates.preservesDeductiveVerification {phase : PipelinePhase}
    (h : PhaseOverapproximates phase.Transforms) :
    PhasePreservesDeductiveVerification phase :=
  fun _ _ ht _ _ => deductiveVerificationOnCore_of_overapproximates h ht

/-- **A pipeline of overapproximating phases followed by a deductive verifier is
    a deductive verifier.** Each `valid` verdict the final phase reports holds
    on every bounded run of the transformed program, and every run of the
    original has a transformed run whose validity implies its own. -/
theorem isDeductiveVerifier_pipelineVerify
    (phases : List (Program → Option Program)) (vcg : CoreVerifierInput → VCResults)
    (hphases : ∀ phase ∈ phases, PhaseOverapproximates (fun p p' => phase p = some p'))
    (hvcg : IsDeductiveVerifier vcg) :
    IsDeductiveVerifier (pipelineVerify phases vcg) := by
  intro input
  unfold pipelineVerify
  cases hrun : runPhases phases input.prog with
  | none =>
    intro a
    rw [vcResultsVerdict_empty]
    trivial
  | some p' =>
    exact deductiveVerificationOnCore_of_overapproximates
      (phaseOverapproximates_runPhases phases hphases) hrun (hvcg ⟨input.entryPoints, p'⟩)


/-! ## Traces of the declarations entry

A run from a program's declarations entry reads its declarations in order (`declsLang`):
it raises the events of a prefix of them (`declsRun_trace`), and some run raises the events
of all of them (`declsRun_full`). An assertion of such a trace is a lemma of the program,
and it is valid exactly when the lemma holds whenever the conditions the declarations
before it assume hold (`assertionsValidFromP_declsTrace`).

From that, the shape a phase proof takes on programs without procedures: each lemma of
the input must have a lemma of the output with the same name and metadata such that,
whenever the input's assumptions before the input lemma hold, the output's assumptions
before the output lemma hold and the output lemma's truth implies the input lemma's
(`DeclsReflect`). The output may drop, merge or rewrite assumptions, and may add lemmas.
-/

/-- A run over no declarations raises no events. -/
@[simp] theorem declsTrace_nil (ρ : Imperative.Env Expression) : declsTrace ρ [] = [] := rfl

/-- A run over `d :: ds` raises `d`'s events, then those of `ds`. -/
@[simp] theorem declsTrace_cons (ρ : Imperative.Env Expression) (d : Decl) (ds : List Decl) :
    declsTrace ρ (d :: ds) = declEvents ρ d ++ declsTrace ρ ds := rfl

/-- A terminal configuration takes no step. -/
private theorem terminal_reaches {ρ : Imperative.Env Expression} :
    ∀ {n : Nat} {t : List (Event Expression)} {c : DeclsCfg},
      declsLang.ReachesWithin n (.terminal ρ) t c → t = []
  | 0, _, _, ⟨_, ht⟩ => ht
  | _ + 1, _, _, .inl ⟨_, ht⟩ => ht
  | _ + 1, _, _, .inr ⟨_, _, _, hstep, _, _⟩ => by
    have hstep : DeclsStep _ _ _ := hstep
    cases hstep

/-- **A run from the declarations raises the events of a prefix of them.** -/
theorem declsRun_trace {ρ : Imperative.Env Expression} :
    ∀ {n : Nat} {ds : List Decl} {t : List (Event Expression)} {c : DeclsCfg},
      declsLang.ReachesWithin n (.run ρ ds) t c → ∃ k, t = declsTrace ρ (ds.take k)
  | 0, _, _, _, ⟨_, ht⟩ => ⟨0, by simp [ht]⟩
  | _ + 1, _, _, _, .inl ⟨_, ht⟩ => ⟨0, by simp [ht]⟩
  | _ + 1, _, _, _, .inr ⟨_, _, _, hstep, hrest, ht⟩ => by
    have hstep : DeclsStep _ _ _ := hstep
    cases hstep with
    | decl =>
      obtain ⟨k, rfl⟩ := declsRun_trace hrest
      exact ⟨k + 1, by simp [ht]⟩
    | done =>
      exact ⟨0, by simp [ht, terminal_reaches hrest]⟩

/-- **Some run from the declarations raises the events of all of them.** -/
theorem declsRun_full (ρ : Imperative.Env Expression) :
    ∀ ds : List Decl,
      declsLang.ReachesWithin (ds.length + 1) (.run ρ ds) (declsTrace ρ ds) (.terminal ρ)
  | [] => .inr ⟨[], .terminal ρ, [], DeclsStep.done, ⟨rfl, rfl⟩, rfl⟩
  | d :: ds => .inr ⟨declEvents ρ d, .run ρ ds, declsTrace ρ ds, DeclsStep.decl,
      declsRun_full ρ ds, rfl⟩

/-! ## Assumptions and assertions of a declarations trace -/

/-- A declaration's events assume exactly what it assumes. -/
private theorem assume_mem_declEvents {ρ : Imperative.Env Expression} {d : Decl}
    {c : EventArg Expression} : Event.assume c ∈ declEvents ρ d ↔ c ∈ declAssumes ρ d := by
  cases d with
  | lemma l md =>
    simp only [declEvents, declAssumes, List.not_mem_nil, iff_false]
    split <;> simp
  | _ => simp [declEvents]

/-- **The assumptions of a declarations trace hold exactly when the declarations' facts
    do.** -/
theorem assumptionsHold_declsTrace {w : Unit} {ρ : Imperative.Env Expression}
    {ds : List Decl} :
    Trace.AssumptionsHold Expression Imperative.BigStep.evalInterp w (declsTrace ρ ds) ↔
      DeclsFactsHold ds ρ := by
  simp only [Trace.AssumptionsHold, declsTrace, List.mem_flatMap, DeclsFactsHold]
  constructor
  · intro h d hd c hc
    exact h c ⟨d, hd, assume_mem_declEvents.mpr hc⟩
  · rintro h c ⟨d, hd, hc⟩
    exact h d hd c (assume_mem_declEvents.mp hc)

/-- Assertion validity over assumptions followed by more assumptions. -/
private theorem assertionsValidFromP_assumes (keep : EventArg Expression → Prop) :
    ∀ (cs : List (EventArg Expression)) (acc rest : List (Event Expression)),
      Trace.AssertionsValidFromP Expression Imperative.BigStep.evalInterp keep acc
          (cs.map .assume ++ rest) ↔
        Trace.AssertionsValidFromP Expression Imperative.BigStep.evalInterp keep
          (acc ++ cs.map .assume) rest
  | [], acc, rest => by simp
  | c :: cs, acc, rest => by
    simp only [List.map_cons, List.cons_append, Trace.AssertionsValidFromP]
    rw [assertionsValidFromP_assumes keep cs]
    simp

/-- **When the assertions of a declarations trace are valid**: each lemma that is asserted
    holds whenever the assumptions accumulated so far and those of the declarations before
    it hold. -/
theorem assertionsValidFromP_declsTrace (keep : EventArg Expression → Prop)
    (ρ : Imperative.Env Expression) :
    ∀ (ds : List Decl) (acc : List (Event Expression)),
      Trace.AssertionsValidFromP Expression Imperative.BigStep.evalInterp keep acc
          (declsTrace ρ ds) ↔
        ∀ i l md, ds[i]? = some (.lemma l md) →
          (Expression.eval ρ.factory ρ.store l.e).isSome →
          keep (lemmaEvent l md ρ) → ∀ w,
            Trace.AssumptionsHold Expression Imperative.BigStep.evalInterp w
              (acc ++ declsTrace ρ (ds.take i)) →
            Imperative.BigStep.evalInterp.holds w (lemmaEvent l md ρ)
  | [], acc => by simp [Trace.AssertionsValidFromP]
  | d :: ds, acc => by
    have ih := assertionsValidFromP_declsTrace keep ρ ds
    rw [declsTrace_cons]
    constructor
    · intro h i l md hi hs hk w ha
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        simp only [declEvents, hs, ↓reduceIte, List.cons_append, List.nil_append,
          Trace.AssertionsValidFromP] at h
        simpa using h.1 hk w (by simpa using ha)
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi
        simp only [List.take_succ_cons, declsTrace_cons] at ha
        cases d with
        | lemma l₀ md₀ =>
          simp only [declEvents] at h ha
          split at h
          · rename_i hs₀
            simp only [List.cons_append, List.nil_append, Trace.AssertionsValidFromP] at h
            simp only [hs₀, ↓reduceIte, List.cons_append, List.nil_append] at ha
            rw [Trace.AssumptionsHold_append, Trace.assumptionsHold_cons_assert,
              ← Trace.AssumptionsHold_append] at ha
            exact (ih acc).mp h.2 i l md hi hs hk w ha
          · rename_i hs₀
            simp only [hs₀, Bool.false_eq_true, ↓reduceIte, List.nil_append] at h ha
            exact (ih acc).mp h i l md hi hs hk w ha
        | _ =>
          simp only [declEvents] at h ha
          rw [assertionsValidFromP_assumes] at h
          exact (ih _).mp h i l md hi hs hk w (by simpa [List.append_assoc] using ha)
    · intro h
      cases d with
      | lemma l₀ md₀ =>
        simp only [declEvents]
        split
        · rename_i hs₀
          simp only [List.cons_append, List.nil_append, Trace.AssertionsValidFromP]
          refine ⟨fun hk w ha => h 0 l₀ md₀ rfl hs₀ hk w (by simpa using ha), ?_⟩
          refine (ih acc).mpr fun i l md hi hs hk w ha => h (i + 1) l md hi hs hk w ?_
          simp only [List.take_succ_cons, declsTrace_cons, declEvents, hs₀, ↓reduceIte,
            List.cons_append, List.nil_append]
          rw [Trace.AssumptionsHold_append, Trace.assumptionsHold_cons_assert,
            ← Trace.AssumptionsHold_append]; exact ha
        · rename_i hs₀
          simp only [List.nil_append]
          refine (ih acc).mpr fun i l md hi hs hk w ha => h (i + 1) l md hi hs hk w ?_
          simpa [List.take_succ_cons, declsTrace_cons, declEvents, hs₀] using ha
      | _ =>
        simp only [declEvents]
        rw [assertionsValidFromP_assumes]
        refine (ih _).mpr fun i l md hi hs hk w ha => h (i + 1) l md hi hs hk w ?_
        simpa [List.take_succ_cons, declsTrace_cons, declEvents, List.append_assoc] using ha

/-! ## Declarations that reflect each other -/

/-- Declarations reflect themselves. -/
theorem DeclsReflect.refl (ρ : Imperative.Env Expression) (ds : List Decl) :
    DeclsReflect ρ ds ρ ds :=
  fun i l _ hi hs hf => ⟨i, l, hi, rfl, hs, hf, id⟩

/-- **Runs from declarations overapproximate those from declarations they reflect**, for
    validity: every run of the first raises a prefix of its declarations' events, and the
    run over all of the second's raises an assertion for each of those lemmas, valid only
    if the first's is. -/
theorem DeclsReflect.runsOverapproximate {ρ ρ' : Imperative.Env Expression}
    {ds ds' : List Decl} (h : DeclsReflect ρ ds ρ' ds') :
    declsLang.RunsOverapproximate (Strata.Analysis.ValidityReflected Imperative.BigStep.evalInterp)
      declsLang (DeclsCfg.run ρ ds) (DeclsCfg.run ρ' ds') := by
  intro n trace c hrun
  obtain ⟨k, rfl⟩ := declsRun_trace hrun
  refine ⟨ds'.length + 1, _, _, declsRun_full ρ' ds', ?_⟩
  intro a ha
  unfold Trace.AssertionValid Trace.AssertionValidFrom at ha ⊢
  rw [assertionsValidFromP_declsTrace] at ha ⊢
  intro i l md hi hs hk w hassm
  have hik : i < k := by
    rcases Nat.lt_or_ge i k with hlt | hge
    · exact hlt
    · rw [List.getElem?_take_eq_none hge] at hi
      cases hi
  rw [List.getElem?_take_of_lt hik] at hi
  rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hik), List.nil_append] at hassm
  obtain ⟨j, l', hj, hname, hs', hf', himp'⟩ :=
    h i l md hi hs (assumptionsHold_declsTrace.mp hassm)
  have hk' : (lemmaEvent l' md ρ').label = a.label ∧ (lemmaEvent l' md ρ').metadata = a.md := by
    simp only [lemmaEvent, declArg] at hk ⊢
    exact ⟨hname.trans hk.1, hk.2⟩
  exact himp' (ha j l' md hj hs' hk' () (by simpa using assumptionsHold_declsTrace.mpr hf'))

/-- **Entries of a program without procedure entries are overapproximated** by those of a
    program whose declarations reflect its declarations: the only entry is the declarations
    entry, and declarations that reflect each other overapproximate each other's runs. The
    case split `deductiveVerificationOnCoreWith_of_declsReflect` and
    `PhaseReflectsLemmas.overapproximates` share. -/
private theorem entriesOverapproximate_of_declsReflect
    {base base' : Lambda.Factory CoreLParams} {p p' : Program}
    (hnoproc : ∀ w, ¬ IsCoreEntryAt base p (.proc w))
    (hdecls : ∀ ρ, IsCoreEntryAt base p (.decls ρ) →
      ∃ ρ', IsCoreEntryAt base' p' (.decls ρ') ∧ DeclsReflect ρ p.decls ρ' p'.decls) :
    ∀ w, IsCoreEntryAt base p w →
      ∃ w', w.Corresponds w' ∧ IsCoreEntryAt base' p' w' ∧
        (coreEventLangWithDecls (coreStartWithDecls p w).1).RunsOverapproximate
          (Strata.Analysis.ValidityReflected Imperative.BigStep.evalInterp)
          (coreEventLangWithDecls (coreStartWithDecls p' w').1)
            (coreStartWithDecls p w).2 (coreStartWithDecls p' w').2 := by
  intro w hw
  cases w with
  | proc w => exact absurd hw (hnoproc w)
  | decls ρ =>
    obtain ⟨ρ', hw', hr⟩ := hdecls ρ hw
    exact ⟨.decls ρ', trivial, hw', hr.runsOverapproximate⟩

/-- **Deductive verification carries back through the declarations entry.** If `p` has no
    entry procedure, and the declarations of each declarations entry of `p` over `base` are
    reflected by those of a declarations entry of `p'` over `base'`, deductive verification
    of `p'` is deductive verification of `p`. -/
theorem deductiveVerificationOnCoreWith_of_declsReflect
    {base base' : Lambda.Factory CoreLParams} {p p' : Program}
    (hnoproc : ∀ w, ¬ IsCoreEntryAt base p (.proc w))
    (hdecls : ∀ ρ, IsCoreEntryAt base p (.decls ρ) →
      ∃ ρ', IsCoreEntryAt base' p' (.decls ρ') ∧ DeclsReflect ρ p.decls ρ' p'.decls)
    {entryPoints : List String} {results : VCResults}
    (hdv : DeductiveVerificationOnCoreWith base' ⟨entryPoints, p'⟩ results) :
    DeductiveVerificationOnCoreWith base ⟨entryPoints, p⟩ results :=
  deductiveVerificationOnCoreWith_of_overapproximates
    (entriesOverapproximate_of_declsReflect hnoproc hdecls) hdv

/-! ## Phases on programs without procedures -/

/-- A program without procedures has no procedure entry. -/
private theorem NoProcedures.not_procEntry {base : Lambda.Factory CoreLParams} {p : Program}
    (h : NoProcedures p) (w : CoreEntry) : ¬ IsCoreEntryAt base p (.proc w) := by
  intro ⟨hfind, _⟩
  simp only [Program.findProcByString?, Option.bind_eq_some_iff] at hfind
  obtain ⟨d, hd, _⟩ := hfind
  exact h d (Program.find?_mem hd) (Program.find?_kind hd)

/-- **A phase that reflects the declarations entry preserves deductive verification
    backwards on programs without procedures.** -/
theorem PhaseReflectsLemmas.preservesDeductiveVerification
    {pre : Transform.CoreTransformState → Program → Prop} {phase : PipelinePhase}
    (h : PhaseReflectsLemmas pre phase) :
    PhasePreservesDeductiveVerificationFrom (fun s p => pre s p ∧ NoProcedures p) phase :=
  fun s p s' p' ⟨hpre, hnp⟩ hrun _ _ hdv =>
    deductiveVerificationOnCoreWith_of_declsReflect (hnp.not_procEntry)
      (h s p s' p' hpre hrun) hdv

/-- **A phase that reflects the declarations entry overapproximates every entry on programs
    without procedures** (`PhaseOverapproximatesFrom`, the contract that also covers
    procedure entries): such a program's only entry is its declarations entry. -/
theorem PhaseReflectsLemmas.overapproximates
    {pre : Transform.CoreTransformState → Program → Prop} {phase : PipelinePhase}
    (h : PhaseReflectsLemmas pre phase) :
    PhaseOverapproximatesFrom (fun s p => pre s p ∧ NoProcedures p) phase :=
  fun s p s' p' ⟨hpre, hnp⟩ hrun =>
    entriesOverapproximate_of_declsReflect hnp.not_procEntry (h s p s' p' hpre hrun)

end Analysis

end Core.Specification

end -- public section
