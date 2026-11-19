/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.Prog

/-!
# Simulation of whole-program runs

`entry_sim` lifts `fund` to `runEntry`, the interpreter's entry point. If a pass satisfies
`PassRel` and the two programs are related by `ProgRel`, then running the target with `K`
times the fuel gives the same outcome as running the source, in related states and with
related traces, unless the source run gets stuck. Neither run may use a step budget, and
the source run must not run out of fuel.

* `ERel S`: the outcomes are equal up to refusal messages (`eraseO`), the states are
  related by `S.st` and the traces by `TrRel`. If the source gets stuck, nothing is claimed.
* `NotOOFEntry`: the run did not end with `outOfFuel`.
* `fs_initEntry`, `entryInitState_rel`: initialisation of the program and of file-scope
  globals gives related states.
* `entry_body`: a body related by `ImplRel` gives the same outcome class (`EB`, `ECls`).
* `entry_sim`: the theorem above.
-/

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

section
variable [Reserved] {E : StmtExprMd → StmtExprMd → Prop} {G : StackFrame}

omit [Reserved] in
theorem run_recover (x y : EvalM PM α) (σ : EvalState) (τ : Trace) :
    run ((fun s => InterpHost.recover (x s) (y s)) : EvalM PM α) σ τ =
      match run x σ τ with
      | .error (.fail _) => run y σ τ
      | r => r := by
  unfold run
  simp only [ExceptT.run, StateT.run, InterpHost.recover]
  rcases x σ τ with (e | e) | r <;> rfl

theorem fs_recover {A : α → β → Prop} {x y : EvalM PM α} {x' y' : EvalM PM β}
    (hx : FS (Sm E Gl G) A x x') (hy : FS (Sm E Gl G) A y y') :
    FS (Sm E Gl G) A ((fun s => InterpHost.recover (x s) (y s)) : EvalM PM α)
      ((fun s => InterpHost.recover (x' s) (y' s)) : EvalM PM β) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  rw [run_recover] at hn ⊢
  rw [run_recover]
  have h0 := hx.sim σ σ' τ τ' hs ht
  rcases r : run x σ τ with (m | m) | ⟨⟨c | a, σ1⟩, τ1⟩ <;> rw [r] at hn h0 <;> dsimp only at hn ⊢
  · have h1 := h0 not_OOF_error
    rcases r' : run x' σ' τ' with (m' | m') | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;> rw [r'] at h1 <;> dsimp only
    · exact hy.sim σ σ' τ τ' hs ht hn
    · exact absurd (h1 (.mk _)) stuck_fail
    · exact absurd h1 stuck_fail
    · exact absurd h1 stuck_fail
  · exact RR.ofStuck (.mk m) _
  all_goals
    have h1 := h0 (by first | exact hn | exact not_OOF_ok)
    rcases r' : run x' σ' τ' with (m' | m') | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;> rw [r'] at h1 <;> dsimp only <;>
      simp only [RR, ExRel, false_and] at h1 ⊢
    all_goals exact h1

theorem fs_attemptEval {x x' : EvalM PM Value} (hpl : Plain G) (h : FS (Sm E Gl G) Eq x x') :
    FS (Sm E Gl G) Eq (attemptEval x) (attemptEval x') := by
  unfold attemptEval
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  have hσ : StRel G (IxRel E) σ σ' := hσ
  refine fs_recover (fs_tryCatch (fs_bind h (fun a b hab => by subst hab; exact fs_pure rfl))
    (fun c hc => ?_) ?_ (fun L hL hok => fs_bind (fs_modifyRel (fun a a' ha => by
      have := hσ.stack.regs hpl a.globals; strelw ha [hσ.steps, hσ.steps', hσ.seek, hσ.seek', hσ.ops, hσ.ops'])) (fun _ _ _ => fs_pure rfl))
    (fun w => fs_bind (fs_modifyTo (S := (Sm E Gl G).atWin w) (T := Sm E Gl G) (fun a a' hw => by
      have ha := hw.2.1; have := hσ.stack.regs hpl a.globals; strelw ha [hσ.steps, hσ.steps', hσ.seek, hσ.seek', hσ.ops, hσ.ops']) rfl)
      (fun _ _ _ => fs_pure rfl)))
    (fs_bind (fs_modifyRel (fun a a' ha => by
      have := hσ.stack.regs hpl a.globals; strelw ha [hσ.steps, hσ.steps', hσ.seek, hσ.seek', hσ.ops, hσ.ops'])) (fun _ _ _ => fs_pure rfl))
  · cases c <;> first
      | exact fs_throw _ hc
      | exact fs_bind (fs_modifyRel (fun a a' ha => by
          have := hσ.stack.regs hpl a.globals; strelw ha [hσ.steps, hσ.steps', hσ.seek, hσ.seek', hσ.ops, hσ.ops'])) (fun _ _ _ => fs_pure rfl)
  · intro σ τ
    simp [run_throw, OOF]

theorem IxRel.noWitness_insert {ix ix' : ProgramIndex} (h : IxRel E ix ix') (k : String) :
    IxRel E { ix with noWitness := ix.noWitness.insert k } { ix' with noWitness := ix'.noWitness.insert k } :=
  { h with noWitness := by simp only [h.noWitness], extra := Reserved.ixX_congr E ix ix' _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩ h.extra }

theorem IxRel.witness_insert {ix ix' : ProgramIndex} (h : IxRel E ix ix') (k : String) (v : Value) :
    IxRel E { ix with witnesses := ix.witnesses.insert k v } { ix' with witnesses := ix'.witnesses.insert k v } :=
  { h with witnesses := by simp only [h.witnesses], extra := Reserved.ixX_congr E ix ix' _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩ h.extra }

omit [Reserved] in
theorem forIn_nonAlias {m : Type → Type} [Monad m] [LawfulMonad m] {β : Type} (l : List TypeDefinition) (init : β)
    (f : TypeDefinition → β → m (ForInStep β)) (hf : ∀ a r, f (.Alias a) r = pure (.yield r)) :
    forIn l init f = forIn (nonAliasTypes l) init f := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : ∃ a, x = .Alias a
    · obtain ⟨a, rfl⟩ := hx
      rw [nonAlias_cons_alias, List.forIn_cons, hf, pure_bind]
      exact ih _
    · rw [nonAlias_cons_other (fun a h => hx ⟨a, h⟩), List.forIn_cons, List.forIn_cons]
      congr 1
      funext r
      cases r <;> simp [ih]

end

section
variable [Reserved] {G : StackFrame} {cfg : ExternalBackendM PM} {E Rw : StmtExprMd → StmtExprMd → Prop} {K : Nat}
  {Gl : String → Prop} (hp : PassRel cfg E Rw K Gl)
include hp

set_option hygiene false in
macro "cons_tac" : tactic => `(tactic| (
  rw [foldl_nonAlias (l := p.types), foldl_nonAlias (l := q.types)]
  · refine hr.types.foldl_rel (Inv := MapRel (ConsRel E)) (fun acc acc' a b hacc hab => ?_) (MapRel.empty _)
    cases hab with
    | constrained hc => dsimp only; rw [hc.name]; exact hacc.insert _ hc
    | _ => exact hacc
  all_goals intro _ _; rfl))

omit hp in
theorem fs_report {c c' : ConstrainedType} (msg msg' : String) :
    FS (Sm E Gl G) Eq
      (do
        let failure := Strata.Message.withRange c.witness.source msg
        emitEvent (.check .constraint none failure false (← get))
        modify fun (st : EvalState) => { st with assertFailures := st.assertFailures.push failure })
      (do
        let failure := Strata.Message.withRange c'.witness.source msg'
        emitEvent (.check .constraint none failure false (← get))
        modify fun (st : EvalState) => { st with assertFailures := st.assertFailures.push failure }) := by
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  exact fs_bind (fs_emitE (S := Sm E Gl G) (evRel_fail (E := _)) ⟨rfl, trivial, rfl, _, hσ⟩)
    (fun _ _ _ => fs_modifyRel (fun a a' ha => by strel ha))

set_option hygiene false in
macro "rep_tac" : tactic => `(tactic|
  first
  | exact fs_bind (fs_bind fs_get (fun a a' ha => fs_bind (fs_emitE (S := Sm E Gl G) (evRel_fail (E := _)) ⟨rfl, trivial, rfl, _, ha⟩)
      (fun _ _ _ => fs_modifyRel (fun b b' hb => by strel hb)))) (fun _ _ _ => fs_pure rfl)
  | exact fs_bind fs_get (fun a a' ha => fs_bind (fs_emitE (S := Sm E Gl G) (evRel_fail (E := _)) ⟨rfl, trivial, rfl, _, ha⟩)
      (fun _ _ _ => fs_bind (fs_modifyRel (fun b b' hb => by strel hb)) (fun _ _ _ => fs_pure rfl))))

set_option hygiene false in
macro "wit_tac" : tactic => `(tactic| (
  refine fs_bind (fs_modifyRel (fun a a' ha => { ha with index := ha.index.witness_insert _ _ }))
    (fun _ _ _ => ?_)
  refine fs_bind (fs_forIn (constraintChain_rel (E := E) hr.unalias (by cons_tac) _ _ _ hc)
    (fun k k' hk _ => ?_)) (fun _ _ _ => fs_pure rfl)
  refine fs_bind fs_get (fun s1 s1' hs1 => ?_)
  have hs1 : StRel G (IxRel E) s1 s1' := hs1
  rw [← hk.valueName]
  refine fs_bind (fs_modifyRel (fun a a' ha => by have := hk.vname; have := hk.vnameV; strel ha)) (fun _ _ _ => ?_)
  refine fs_bind (fs_attemptEval hpl (ev _ _ hk.constraint hk.constraintV hk.constraintOK)) (fun r r' hrr => ?_)
  subst hrr
  refine fs_bind (fs_modifyRel (fun a a' ha => by have := hs1.stack.regs hpl a.globals; strelw ha [])) (fun _ _ _ => ?_)
  cases r with
  | some r =>
    refine fs_bind (fs_liftM (isTrue_pconst r)) (fun b b' hb => ?_)
    subst hb
    refine fs_ite (fun _ => ?_) (fun _ => ?_)
    · first
      | exact fs_pure rfl
      | exact fs_pure rfl
    · rep_tac
  | none => dsimp only; rep_tac))

/-- For a pass satisfying `PassRel`, programs related by `ProgRel E` and entry procedures related by
`ProcRel E`, the program initialisation `initEntry` with fuel `n` is simulated by the target's with
fuel at least `K * n`. The stack frame `G` must not mention the pass's valued-return output
(`Strict`) and must leave the pass's hooks trivial (`Plain`). -/
theorem fs_initEntry {p q : LaurelProgram} (hr : ProgRel E p q) {main main' : Procedure}
    (hm : ProcRel E main main') {o o' : Options} {n : Nat} (hn : o.fuel = n) (hM : K * n ≤ o'.fuel)
    (hG : Strict G) (hpl : Plain G) (fo : Bool := false) :
    FS (Sm E Gl G) Eq (initEntry cfg o p main fo) (initEntry cfg o' q main' fo) := by
  have ih := fund hp n
  have ev : ∀ a a', E a a' → Reserved.vok E a a' → Hered FinP a →
      FS (Sm E Gl G) Eq (evalExprMd cfg n a) (evalExprMd cfg o'.fuel a') :=
    fun a a' h hv hf => exprMdE hp ih h hv (hf.mono (fun _ => finP_nodeOK)) hM
  unfold initEntry
  simp only [hn, ← hr.types.length_eq]
  rw [forIn_nonAlias p.types, forIn_nonAlias q.types]
  rotate_left
  · intro _ _; simp
  · intro _ _; simp
  refine fs_bind (fs_forIn hr.types (fun t t' ht _ => ?_)) (fun _ _ _ => ?_)
  · cases ht with
    | @constrained c c' hc =>
      dsimp only
      rw [← hc.name]
      refine fs_bind (fs_modifyRel (fun a a' ha => by strel ha)) (fun _ _ _ => ?_)
      refine fs_bind fs_get (fun σ σ' hσ => ?_)
      have hσ : StRel G (IxRel E) σ σ' := hσ
      rw [hσ.index.witnesses]
      cases σ.index.witnesses[c.name.text]? with
      | some v =>
        simp only [pure_bind]
        wit_tac
      | none =>
        refine fs_bind (fs_attemptEval hpl (ev _ _ hc.witness hc.witnessV hc.witnessOK)) (fun r r' hrr => ?_)
        subst hrr
        cases r with
        | none =>
          dsimp only
          refine fs_bind (fs_bind fs_get (fun a a' ha => fs_bind (fs_emitE (S := Sm E Gl G) (evRel_fail (E := _)) ⟨rfl, trivial, rfl, _, ha⟩)
            (fun _ _ _ => fs_modifyRel (fun b b' hb => by strel hb)))) (fun _ _ _ => ?_)
          refine fs_bind (fs_modifyRel (fun a a' ha => ?_)) (fun _ _ _ => fs_pure rfl)
          exact { ha with index := ha.index.noWitness_insert _ }
        | some v =>
          dsimp only
          wit_tac
    | _ => exact fs_pure rfl
  · refine fs_bind (fs_modifyRel (fun a a' ha => by strel ha)) (fun _ _ _ => ?_)
    refine fs_bind (fs_forIn hm.outputs.withMem (fun x x' hx _ => ?_)) (fun _ _ _ => ?_)
    · obtain ⟨⟨hxn, hxt⟩, hxm⟩ := hx
      have hx := hm.outNames x hxm
      exact fs_bind (fs_modifyRel (fun a a' ha => by
        rw [← hxn, ha.index.defaultR hxt]; strelw ha [])) (fun _ _ _ => fs_pure rfl)
    · cases fo
      · simp only [Bool.false_eq_true, ite_false]
        by_cases hg : Reserved.noGlobals
        · have h1 := hr.noGlobals hg
          have h2 : q.staticFields = [] := by
            have := hr.fields.length_eq
            rw [h1] at this
            exact List.eq_nil_of_length_eq_zero this.symm
          rw [h1, h2]
          exact fs_pure rfl
        refine fs_bind (fs_forIn hr.fields.withMem (fun f f' hf0 _ => ?_)) (fun _ _ _ => fs_pure rfl)
        obtain ⟨⟨hn1, hty, hi, hfo, hfv⟩, hfm⟩ := hf0
        have hfo' : ∀ o, Reserved.vret = some o → f.name.text ≠ o := fun o ho => hr.outG o ho f hfm
        rw [← hn1]
        revert hi hfo hfv
        cases f.initializer <;> cases f'.initializer <;> simp only [ORel, false_implies, true_implies]
        · intro _ _
          exact fs_bind (fs_modifyRel (fun a a' ha => by
            strelw ha [ha.index.defaultR hty])) (fun _ _ _ => fs_pure rfl)
        · intro hi hfo hfv
          refine fs_bind (fs_modifyRel (fun a a' ha => by strel ha)) (fun _ _ _ => ?_)
          exact fs_bind (ev _ _ hi (hfv _ _ rfl rfl) (hfo _ rfl)) (fun x y hxy => by
            subst hxy
            exact fs_bind (fs_modifyRel (fun a a' ha => by
              strel ha)) (fun _ _ _ => fs_pure rfl))
      · simp only [ite_true]
        refine fs_bind fs_get (fun σ σ' hσ => ?_)
        have hσ : StRel G (IxRel E) σ σ' := hσ
        rw [← hσ.heap]
        refine fs_bind (fs_chooseHeap _) (fun h h' hh => ?_)
        subst hh
        refine fs_bind (fs_modifyRel (fun a a' ha => by strel ha)) (fun _ _ _ => ?_)
        by_cases hg : Reserved.noGlobals
        · have h1 := hr.noGlobals hg
          have h2 : q.staticFields = [] := by
            have := hr.fields.length_eq
            rw [h1] at this
            exact List.eq_nil_of_length_eq_zero this.symm
          rw [h1, h2]
          exact fs_pure rfl
        refine fs_bind (fs_forIn hr.fields.withMem (fun f f' hf0 _ => ?_)) (fun _ _ _ => fs_pure rfl)
        obtain ⟨⟨hn1, hty, -, -, -⟩, hfm⟩ := hf0
        have hfo' : ∀ o, Reserved.vret = some o → f.name.text ≠ o := fun o ho => hr.outG o ho f hfm
        rw [← hn1]
        refine fs_bind fs_get (fun σ σ' hσ => ?_)
        have hσ : StRel G (IxRel E) σ σ' := hσ
        rw [hσ.index.defaultR hty]
        refine fs_bind (fs_chooseInit _ _ _ _) (fun v v' hv => ?_)
        subst hv
        exact fs_bind (fs_modifyRel (fun a a' ha => by strel ha)) (fun _ _ _ => fs_pure rfl)


def ERel (S : SimRel) : Except HErr ((Outcome × EvalState) × Trace) →
    Except HErr ((Outcome × EvalState) × Trace) → Prop
  | .error e, .error e' => Stuck e' → Stuck e
  | .error e, .ok _ => Stuck e
  | .ok ((o, σ), τ), .ok ((o', σ'), τ') => eraseO o = eraseO o' ∧ S.st σ σ' ∧ TrRel S τ τ'
  | _, _ => False

omit [Reserved] hp in
theorem ERel.ofStuck {S : SimRel} {e : HErr} (h : Stuck e) (r' : Except HErr ((Outcome × EvalState) × Trace)) :
    ERel S (.error e) r' := by
  rcases r' with _ | _
  · exact fun _ => h
  · exact h

def NotOOFEntry : Except HErr ((Outcome × EvalState) × Trace) → Prop
  | .ok ((.outOfFuel, _), _) => False
  | _ => True

omit [Reserved] hp in
theorem pm_bind_run (X : EvalM PM α) (σ : EvalState) (f : Except Control α × EvalState → PM β) (τ : Trace) :
    ((ExceptT.run X).run σ >>= f) τ = match run X σ τ with
      | .error e => .error e
      | .ok (r, τ') => f r τ' := by
  show (StateT.bind ((ExceptT.run X).run σ) f) τ = _
  simp only [StateT.bind, run, bind, Except.bind, StateT.run]
  generalize ExceptT.run X σ τ = r
  rcases r with e | ⟨r, τ'⟩ <;> rfl

omit hp in
theorem BodyRel.impl {outs : List Parameter} {b b' : Body} (h : BodyRel E outs b b') :
    ORel (ImplRel E outs) b.implementation b'.implementation := by
  cases h <;> simp only [Body.implementation, ORel] <;> assumption

omit hp in
/-- For programs related by `ProgRel E`, the initial interpreter states `entryInitState o p` and
`entryInitState o' q` are related by `StRel {} (IxRel E)`, provided neither run uses a step budget
and both have the same `printAsserts` option. -/
theorem entryInitState_rel {p q : LaurelProgram} (hr : ProgRel E p q) {o o' : Options}
    (hl : o.limitSteps = false) (hl' : o'.limitSteps = false) (hq : o.printAsserts = o'.printAsserts) :
    StRel {} (IxRel E) (entryInitState o p) (entryInitState o' q) := by
  refine ⟨SR.fresh Clean.empty, WFG.empty, fun _ _ _ h => by simp [entryInitState] at h, rfl, ?_, ?_, ?_, rfl,
    fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, True.intro, rfl, rfl, rfl, hr.index, fun k _ => by simp [entryInitState],
    fun k _ => by simp [entryInitState], fun _ _ _ h => by simp [entryInitState] at h,
    fun _ _ => by simp [entryInitState]⟩
  · simp [entryInitState, hl]
  · simp [entryInitState, hl']
  · simp [entryInitState, hq]

omit [Reserved] hp in
theorem run_runB (x : EvalM PM Unit) (σ : EvalState) (τ : Trace) :
    run (runB x) σ τ = match run x σ τ with
      | .error e => .error e
      | .ok ((.ok _, σ1), τ1) => .ok ((.ok none, σ1), τ1)
      | .ok ((.error c, σ1), τ1) => match c with
        | .return_ [] => .ok ((.ok none, σ1), τ1)
        | .return_ [v] => .ok ((.ok (some v), σ1), τ1)
        | c => .ok ((.error c, σ1), τ1) := by
  simp only [runB, run_tryCatch, run_bind]
  rcases run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩
  · rfl
  · cases c with
    | return_ vs => rcases vs with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
    | _ => rfl
  · rfl

omit [Reserved] hp in
theorem runB_not_oof {x : EvalM PM Unit} {σ : EvalState} {τ : Trace} (h : ¬ OOF (run x σ τ)) :
    ¬ OOF (run (runB x) σ τ) := by
  rw [run_runB]
  revert h
  rcases run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;> intro h
  · exact not_OOF_error
  · rcases c with (_ | ⟨_, _ | ⟨_, _⟩⟩) | _ | _ | _ | _ | _ | _ | _ <;> first | exact not_OOF_ok | exact h
  · exact not_OOF_ok

def ECls : Except Control Unit → Option Outcome
  | .ok () => some .completed
  | .error (.return_ _) => some .completed
  | .error (.throw_ v) => some (.escaped v)
  | .error .outOfFuel => some .outOfFuel
  | .error .infeasible => some .infeasible
  | .error (.refused _) => some (.refused "")
  | .error _ => none

def EB (S : SimRel) : R Unit → R Unit → Prop
  | .error e, .error e' => Stuck e' → Stuck e
  | .error e, .ok _ => Stuck e
  | .ok ((r, σ), τ), .ok ((r', σ'), τ') => ECls r = ECls r' ∧ S.st σ σ' ∧ TrRel S τ τ'
  | _, _ => False

omit [Reserved] hp in
theorem ecls_throw {r : Except Control Unit} {v : Value} (h : ECls r = some (.escaped v)) : r = .error (.throw_ v) := by
  rcases r with c | u
  · cases c <;> simp only [ECls, Option.some.injEq, Outcome.escaped.injEq, reduceCtorEq] at h
    rw [h]
  · simp [ECls] at h

omit [Reserved] hp in
theorem eb_escape {S : SimRel} {Q : EvalState → EvalState → Prop} {x y : EvalM PM Unit} {P P' : Procedure}
    (ht : P'.throwsType.isNone = P.throwsType.isNone) (hx : ExcOK S P P')
    (hU : ∀ σ σ' f f', S.st σ σ' → S.st { σ with assertFailures := σ.assertFailures.push f }
      { σ' with assertFailures := σ'.assertFailures.push f' })
    (h : ∀ σ σ' τ τ', Q σ σ' → TrRel S τ τ' → ¬ OOF (run x σ τ) → EB S (run x σ τ) (run y σ' τ')) :
    ∀ σ σ' τ τ', Q σ σ' → TrRel S τ τ' → ¬ OOF (run (tryCatch x (escapeSig P)) σ τ) →
      EB S (run (tryCatch x (escapeSig P)) σ τ) (run (tryCatch y (escapeSig P')) σ' τ') := by
  intro σ σ' τ τ' hq htr hn
  rw [run_tryCatch] at hn ⊢
  rw [run_tryCatch]
  have hn0 : ¬ OOF (run x σ τ) := by
    intro ho
    apply hn
    rcases r : run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;> rw [r] at ho
    · exact absurd ho not_OOF_error
    · rw [OOF_err] at ho; subst ho
      dsimp only
      rw [run_escapeSig_other (fun v h => by cases h)]
      exact OOF_err.mpr rfl
    · exact absurd ho not_OOF_ok
  have h0 := h σ σ' τ τ' hq htr hn0
  have hoth : ∀ (Q : Procedure) (c : Control) σ τ, (∀ v, c ≠ .throw_ v) →
      run (escapeSig Q c : EvalM PM Unit) σ τ = .ok ((.error c, σ), τ) :=
    fun Q c σ τ hc => run_escapeSig_other (fun v e => absurd e (hc v)) σ τ
  rcases r : run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;>
    rcases r' : run y σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;> rw [r, r'] at h0 <;> dsimp only
  · exact h0
  · rcases run_escapeSig_ok_or_stuck (α := Unit) P' c' σ1' τ1' with ⟨q, hq⟩ | ⟨m, hq⟩
    · rw [hq]; exact h0
    · rw [hq]; exact fun _ => h0
  · exact h0
  · exact h0.elim
  · obtain ⟨hcls, hst, htr1⟩ := h0
    by_cases hth : ∃ v, c = .throw_ v
    · obtain ⟨v, rfl⟩ := hth
      have hc' := ecls_throw (hcls.symm.trans rfl : ECls (.error c') = some (.escaped v))
      cases hc'
      cases hb : P.throwsType.isNone
      · obtain ⟨t, htt⟩ := Option.isSome_iff_exists.mp (by simpa using hb)
        obtain ⟨t', htt', hxe⟩ := hx σ1 σ1' v t hst htt
        rw [run_escapeSig_some htt, run_escapeSig_some htt', hxe]
        split
        · exact ⟨rfl, hst, htr1⟩
        · exact fun _ => ⟨_⟩
      · rw [run_escapeSig_throw hb, run_escapeSig_throw (by rw [ht, hb])]
        refine ⟨rfl, hU _ _ _ _ hst, ?_, htr1.2⟩
        simp only [Array.toList_push, nFail_concat]
        rw [htr1.1]
        rfl
    · have hc : ∀ v, c ≠ .throw_ v := fun v e => hth ⟨v, e⟩
      have hc' : ∀ v, c' ≠ .throw_ v := fun v e => by
        subst e
        have := ecls_throw (hcls.trans rfl : ECls (.error c) = some (.escaped v))
        cases this
        exact hc v rfl
      rw [hoth P c _ _ hc, hoth P' c' _ _ hc']
      exact ⟨hcls, hst, htr1⟩
  · obtain ⟨hcls, hst, htr1⟩ := h0
    have hc : ∀ v, c ≠ .throw_ v := fun v e => by subst e; simp [ECls] at hcls
    rw [hoth P c _ _ hc]
    exact ⟨hcls, hst, htr1⟩
  · exact h0.elim
  · obtain ⟨hcls, hst, htr1⟩ := h0
    have hc' : ∀ v, c' ≠ .throw_ v := fun v e => by subst e; simp [ECls] at hcls
    rw [hoth P' c' _ _ hc']
    exact ⟨hcls, hst, htr1⟩
  · exact h0

omit [Reserved] hp in
theorem eb_of_rr {S : SimRel} {r r' : R Unit} (h : RR S S Eq r r') (hret : S.ret = none)
    (hw : ∀ v σ σ', ¬ S.win v σ σ') : EB S r r' := by
  rcases r with e | ⟨⟨c | a, σ⟩, τ⟩ <;> rcases r' with e' | ⟨⟨c' | b, σ'⟩, τ'⟩ <;>
    simp only [RR, ExRel, false_and] at h <;> simp only [EB]
  all_goals first
    | exact h
    | (obtain ⟨hsg, ht⟩ := h
       obtain ⟨hcr, -, hs⟩ := hsg.same (hw · σ σ')
       rw [hret] at hcr
       rcases CtlR.eq hcr with rfl | ⟨_, _, rfl, rfl⟩ <;> exact ⟨rfl, hs, ht⟩)
    | exact ⟨trivial, h.2⟩

omit hp in
theorem sigR_sm0 {c c' : Control} {σ σ' : EvalState} (h : SigR (Sm0 E Gl G) c c' σ σ') :
    (c = c' ∨ ∃ r r', c = .refused r ∧ c' = .refused r') ∧ StRel G (IxRel E) σ σ' := by
  obtain ⟨hcr, -, hs⟩ := h.same (fun _ h => h)
  exact ⟨CtlR.eq hcr, hs⟩

omit hp in
theorem eb_of_runB {x y : EvalM PM Unit} {σ σ' : EvalState} {τ τ' : Trace}
    (h : RR (Sm E Gl {}) (Sm0 E Gl {}) Eq (run (runB x) σ τ) (run (runB y) σ' τ')) :
    EB (Sm E Gl {}) (run x σ τ) (run y σ' τ') := by
  rw [run_runB, run_runB] at h
  revert h
  rcases run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;> rcases run y σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;>
    (try rcases c with (_ | ⟨_, _ | ⟨_, _⟩⟩) | _ | _ | _ | _ | _ | _ | _) <;>
    (try rcases c' with (_ | ⟨_, _ | ⟨_, _⟩⟩) | _ | _ | _ | _ | _ | _ | _) <;>
    simp only [RR, ExRel, EB, ECls, false_and, imp_self] <;>
    first
      | (intro h; exact ⟨rfl, h.2⟩)
      | (intro h; exact ⟨by simp_all, h.2⟩)
      | (intro h
         obtain ⟨he, hs⟩ := sigR_sm0 h.1
         rcases he with he | ⟨_, _, he1, he2⟩ <;> (try cases he) <;> (try cases he1) <;> (try cases he2) <;>
           first | exact ⟨trivial, hs, h.2⟩ | exact ⟨rfl, hs, h.2⟩)
      | (intro h; simp_all)
      | trivial

def NotValued (b : StmtExprMd) : Prop :=
  (∀ e s, b ≠ ⟨.Return [e], s⟩) ∧ (∀ e s0 s, b ≠ ⟨.Block [⟨.Return [e], s0⟩] none [] none, s⟩)

/-- For a pass satisfying `PassRel`, a procedure body `body` related to `body'` by `ImplRel E outs`
gives the same outcome class (`EB`, `ECls`) when run with fuel `n` as `body'` run with fuel
`M ≥ K * n`, in related states and with related traces, unless the source run gets stuck or runs
out of fuel. If the pass has a return label, the target needs fuel `K * (n + 1) ≤ M + 1` and the body
must not be a valued `return` (`NotValued`); the body must also satisfy `OvOK {}`. -/
theorem entry_body {n M : Nat} (hW : Reserved.retLabel ≠ none → K * (n + 1) ≤ M + 1) (hM : K * n ≤ M)
    {outs : List Parameter} {body body' : StmtExprMd} (hi : ImplRel E outs body body')
    (hV : Reserved.retLabel ≠ none → NotValued body) (hbo : OvOK {} body) :
    ∀ s1 s1' τ1 τ1', StRel {} (IxRel E) s1 s1' → TrRel (Sm E Gl {}) τ1 τ1' → ¬ OOF (run (evalStmt cfg n body) s1 τ1) →
      EB (Sm E Gl {}) (run (evalStmt cfg n body) s1 τ1) (run (evalStmt cfg M body') s1' τ1') := by
  intro s1 s1' τ1 τ1' hs ht hn
  cases hi with
  | plain hnone h =>
    exact eb_of_rr (((fund hp n).stmt (G := {}) _ _ (hp.closed _ _ h) hbo _ hM).sim _ _ _ _ hs ht hn) hnone
      (fun v _ _ => Sm.noWin _ not_free_empty v)
  | wrapBlock hL hss =>
    exact eb_of_runB ((wrap_block hp (fund_le hp n) hL hss M (hW (by rw [hL]; simp))).sim _ _ _ _ hs ht
      (runB_not_oof hn))
  | wrapOther hL hb hd hlb hann =>
    exact eb_of_runB ((wrap_other hp (fund hp n) hL hb hd hlb hann M (hW (by rw [hL]; simp))).sim _ _ _ _ hs ht
      (runB_not_oof hn))
  | valued hL =>
    exact absurd rfl ((hV (by rw [hL]; simp)).1 _ _)
  | valuedB hL =>
    exact absurd rfl ((hV (by rw [hL]; simp)).2 _ _ _)

/-- Simulation of whole-program runs. For a pass satisfying `PassRel` and programs related by
`ProgRel E`, running the target with fuel at least `K` times the source's gives an `ERel`-related
result to running the source: the same outcome up to refusal messages, related states and related
traces, unless the source gets stuck. The hypotheses: both runs use the same entry procedure, whose
name is not reserved and which is not `valued` in `p`, neither run uses a step budget, both have the
same `printAsserts`, and the source run does not run out of fuel. If the pass has a return label, the
target fuel must also satisfy `K * (n + 1) ≤ o'.fuel + 1` and the entry body must not be a valued
`return`. -/
theorem entry_sim {p q : LaurelProgram} (hr : ProgRel E p q) {o o' : Options} {n : Nat}
    (hn : o.fuel = n) (hM : K * n ≤ o'.fuel) (he : o.entryProcedure = o'.entryProcedure)
    (hl : o.limitSteps = false) (hl' : o'.limitSteps = false) (hq : o.printAsserts = o'.printAsserts)
    (hent : ¬ Reserved.resProc o.entryProcedure)
    (hW : Reserved.retLabel ≠ none → K * (n + 1) ≤ o'.fuel + 1)
    (hV : Reserved.retLabel ≠ none → ∀ main, p.staticProcedures.find? (fun x => x.name.text == o.entryProcedure) =
      some main → ∀ b, main.body.implementation = some b → NotValued b)
    (hEV : ∀ main, p.staticProcedures.find? (fun x => x.name.text == o.entryProcedure) = some main →
      valued main = false)
    {τ τ' : Trace} (ht : TrRel (Sm E Gl {}) τ τ') (hnf : NotOOFEntry (runEntry cfg o p τ)) :
    ERel (Sm E Gl {}) (runEntry cfg o p τ) (runEntry cfg o' q τ') := by
  have hf : ORel (ProcRel E) (p.staticProcedures.find? fun x => x.name.text == o.entryProcedure)
      (q.staticProcedures.find? fun x => x.name.text == o.entryProcedure) := by
    obtain ⟨ps, extra, hqs, hps, hex⟩ := hr.procs
    have h1 := hps.find? (p := fun x => x.name.text == o.entryProcedure)
      (p' := fun x => x.name.text == o.entryProcedure) (fun a b hab => by
        rcases hab.nameText with he | ⟨ha, hb⟩
        · rw [he]
        · have e1 : (a.name.text == o.entryProcedure) = false := by
            simp only [beq_eq_false_iff_ne]; intro h; exact hent (h ▸ ha)
          have e2 : (b.name.text == o.entryProcedure) = false := by
            simp only [beq_eq_false_iff_ne]; intro h; exact hent (h ▸ hb)
          rw [e1, e2])
    have h2 : extra.find? (fun x => x.name.text == o.entryProcedure) = none := by
      rw [List.find?_eq_none]
      intro x hx he'
      simp only [beq_iff_eq] at he'
      exact hent (he' ▸ (hex x hx).1)
    rw [hqs, List.find?_append, h2]
    revert h1
    cases List.find? (fun x => x.name.text == o.entryProcedure) p.staticProcedures <;>
      cases List.find? (fun x => x.name.text == o.entryProcedure) ps <;> simp [ORel]
  have hinit := entryInitState_rel hr hl hl' hq
  unfold runEntry at hnf ⊢
  simp only [← he] at hnf ⊢
  revert hf hnf
  generalize ha : List.find? (fun x => x.name.text == o.entryProcedure) p.staticProcedures = a
  generalize List.find? (fun x => x.name.text == o.entryProcedure) q.staticProcedures = b
  intro hnf hf
  cases a <;> cases b <;> simp only [ORel] at hf
  · exact fun h => absurd h stuck_fail
  · rename_i main main'
    dsimp only at hnf ⊢
    have hi := hf.body.impl
    have hV' := fun h => hV h main ha
    have hBO := hf.bodyOK
    rw [procG_void (hEV main ha)] at hBO
    revert hi hnf hV' hBO
    generalize main.body.implementation = i
    generalize main'.body.implementation = i'
    intro hnf hi hV' hBO
    cases i <;> cases i' <;> simp only [ORel] at hi
    · exact ⟨rfl, hinit, ht⟩
    · rename_i body body'
      have hbody := entry_body hp (cfg := cfg) hW hM hi (fun h => hV' h body rfl) (hBO body rfl)
      have hstart : StRel {} (IxRel E) (entryStart o p main) (entryStart o' q main') := by
        have hfold : main'.outputs.foldl (fun (acc : StackFrame) w =>
              acc.insert w.name.text (defaultValue (entryInitState o' q).index w.type.val)) {} =
            main.outputs.foldl (fun (acc : StackFrame) w =>
              acc.insert w.name.text (defaultValue (entryInitState o p).index w.type.val)) {} :=
          (L2.foldl_congr hf.outputs (fun acc x y hxy => by rw [hxy.1, hinit.index.defaultR hxy.2]) _).symm
        unfold entryStart
        simp only [hfold]
        have := SR.fresh (gs := (entryInitState o p).globals) (Clean.empty.foldl (l := main.outputs) (fun x => x.name.text)
          (fun x => defaultValue (entryInitState o p).index x.type.val) hf.outNames)
        strelw hinit []
      have hI := (fs_initEntry (G := {}) hp hr hf hn hM Strict.empty plain_empty).sim _ _ τ τ' hstart ht
      dsimp only at hnf ⊢
      rw [pm_bind_run] at hnf ⊢
      rw [pm_bind_run]
      rcases r1 : run (initEntry cfg o p main) (entryStart o p main) τ with e | ⟨⟨c | u, s1⟩, τ1⟩ <;>
        rw [r1] at hnf hI <;> dsimp only at hnf
      · have := hI not_OOF_error
        rcases r1' : run (initEntry cfg o' q main') (entryStart o' q main') τ' with e' | ⟨⟨c' | u', s1'⟩, τ1'⟩ <;>
          rw [r1'] at this <;> simp only [RR] at this
        all_goals first | exact this | exact ERel.ofStuck this _
      · by_cases hc : c = .outOfFuel
        · subst hc; simp [NotOOFEntry, pure, StateT.pure, Except.pure] at hnf
        · have := hI (by rw [OOF_err]; exact hc)
          rcases r1' : run (initEntry cfg o' q main') (entryStart o' q main') τ' with e' | ⟨⟨c' | u', s1'⟩, τ1'⟩ <;>
            rw [r1'] at this <;> simp only [RR, ExRel, false_and] at this
          obtain ⟨hsg, ht1⟩ := this
          obtain ⟨hcr, -, hs1⟩ := hsg.same (fun v => Sm.noWin _ not_free_empty v)
          rcases hcr with rfl | ⟨L, hL, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
          · dsimp only
            cases c <;> first | exact absurd rfl hc | trivial | exact fun h => absurd h stuck_fail
          · first | trivial | exact fun h => absurd h stuck_fail
          · exact ⟨rfl, hs1, ht1⟩
      · have := hI not_OOF_ok
        rcases r1' : run (initEntry cfg o' q main') (entryStart o' q main') τ' with e' | ⟨⟨c' | u', s1'⟩, τ1'⟩ <;>
          rw [r1'] at this <;> simp only [RR, ExRel, false_and] at this
        obtain ⟨-, hs1, ht1⟩ := this
        dsimp only at hnf ⊢
        simp only [pure_bind] at hnf ⊢
        rw [pm_bind_run] at hnf ⊢
        rw [pm_bind_run]
        rw [hn] at hnf ⊢

        have hB := eb_escape (P := main) (P' := main') (by rw [hf.throws]) (excOK_of hf.throws hf.throwsTy) (fun _ _ _ _ ha => by strel ha)
          hbody s1 s1' τ1 τ1' hs1 ht1
        rcases r2 : run (tryCatch (evalStmt cfg n body) (escapeSig main)) s1 τ1 with e | ⟨⟨c | u, s2⟩, τ2⟩ <;>
          rw [r2] at hnf hB <;> dsimp only at hnf
        · have := hB not_OOF_error
          rcases r2' : run (tryCatch (evalStmt cfg o'.fuel body') (escapeSig main')) s1' τ1' with e' | ⟨⟨c' | u', s2'⟩, τ2'⟩ <;>
            rw [r2'] at this <;> simp only [EB] at this
          all_goals first | exact this | exact ERel.ofStuck this _
        · by_cases hc : c = .outOfFuel
          · subst hc; simp [NotOOFEntry, pure, StateT.pure, Except.pure] at hnf
          · have := hB (by rw [OOF_err]; exact hc)
            rcases r2' : run (tryCatch (evalStmt cfg o'.fuel body') (escapeSig main')) s1' τ1' with e' | ⟨⟨c' | u', s2'⟩, τ2'⟩ <;>
              rw [r2'] at this <;> simp only [EB] at this <;>
              obtain ⟨hcls, hs2, ht2⟩ := this <;> dsimp only <;>
              cases c <;> (try cases c') <;>
              (try simp only [ECls, reduceCtorEq, Option.some.injEq, Outcome.escaped.injEq] at hcls) <;>
              first | exact absurd rfl hc | trivial | exact fun h => absurd h stuck_fail | exact ⟨rfl, hs2, ht2⟩ | (subst hcls; exact ⟨rfl, hs2, ht2⟩)
        · have := hB not_OOF_ok
          rcases r2' : run (tryCatch (evalStmt cfg o'.fuel body') (escapeSig main')) s1' τ1' with e' | ⟨⟨c' | u', s2'⟩, τ2'⟩ <;>
            rw [r2'] at this <;> simp only [EB] at this <;>
            obtain ⟨hcls, hs2, ht2⟩ := this <;> dsimp only <;> (try cases c') <;>
            (try simp only [ECls, reduceCtorEq, Option.some.injEq] at hcls) <;> first | trivial | exact fun h => absurd h stuck_fail | exact ⟨rfl, hs2, ht2⟩

end

end Strata.Laurel.PassSemantics
