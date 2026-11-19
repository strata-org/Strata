/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.Entry

/-!
# Simulation of runs that start at a procedure

This file proves the counterpart of `entry_sim` for `runProcAt`, which starts a run at a
given procedure with chosen arguments and assumed preconditions. It covers passes without
a return label.

* `procAct`: the part of `runProcAt` after initialisation: choose the arguments, assume
  the preconditions and call the procedure.
* `procAt_sim`: if `P` and `P'` are related by `ProcRel` in programs related by `ProgRel`,
  then running `P'` with `K` times the fuel gives an `ERel`-related result to running `P`.
* `procAt_all`: every static procedure of the source has a static procedure in the target
  for which `procAt_sim` holds.
-/

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

section
variable [Reserved] {cfg : ExternalBackendM PM} {E Rw : StmtExprMd → StmtExprMd → Prop} {K : Nat}
  {Gl : String → Prop} (hp : PassRel cfg E Rw K Gl)
include hp

def procAct (cfg : ExternalBackendM PM) (o : Options) (P : Procedure) : EvalM PM (Array Value) := do
  let index := (← get).index
  let args ← P.inputs.mapM fun i => liftM (InterpHost.chooseInit i.name.text
    (some (index.unalias i.type.val)) (defaultValue index i.type.val) : PM Value)
  assumePreconditions cfg o.fuel P args
  invokeProc cfg o.fuel P.name.source { P with preconditions := [] } args (top := true)

omit [Reserved] hp in
/-- `runProcAt` unfolds to initialising the program from `entryStart`, then running `procAct` and turning
its result into an `Outcome`. Holds by definition. -/
theorem runProcAt_eq (o : Options) (p : LaurelProgram) (P : Procedure) :
    runProcAt cfg o p P = (do
      let start := entryStart o p P
      let start ← match ← ((initEntry cfg o p P cfg.modular).run.run start) with
        | (.ok (), s') => pure s'
        | (.error .outOfFuel, s') => return (Outcome.outOfFuel, s')
        | (.error .infeasible, s') => return (Outcome.infeasible, s')
        | (.error (.refused r), s') => return (Outcome.refused r, s')
        | (.error (.throw_ v), _) =>
            InterpHost.fail s!"uncaught throw of {v.display} initialising file-scope globals"
        | (.error _, _) => InterpHost.fail "unexpected control flow initialising file-scope globals"
      let res ← ((procAct cfg o P).run.run start)
      match res with
      | (.ok _,                 s') => pure (Outcome.completed, s')
      | (.error (.return_ _),    s') => pure (Outcome.completed, s')
      | (.error (.throw_ v),     s') => pure (Outcome.escaped v, s')
      | (.error .outOfFuel,      s') => pure (Outcome.outOfFuel, s')
      | (.error .infeasible,     s') => pure (Outcome.infeasible, s')
      | (.error (.refused r),     s') => pure (Outcome.refused r, s')
      | (.error (.exit_ l),      _)  =>
          InterpHost.fail s!"`exit {l}` with no enclosing block labelled '{l}'"
      | (.error (.goto_ l),      _)  =>
          InterpHost.fail s!"`goto {l}` with no enclosing block labelled '{l}'"
      | (.error (.jump_ l _),    _)  =>
          InterpHost.fail s!"no block labelled '{l}' to jump to"
      | (.error .suspended,      _)  =>
          InterpHost.fail "`yield` with no coroutine to suspend") := rfl

omit hp in
theorem stripPre_rel {P P' : Procedure} (h : ProcRel E P P') :
    ProcRel E { P with preconditions := [] } { P' with preconditions := [] } :=
  { h with pre := .nil, preOK := fun _ hc => by cases hc }

/-- Given `FundAt` at fuel `n` and procedures related by `ProcRelB E`, assuming the preconditions of `P`
on the arguments `args` with fuel `n + 1` is simulated by assuming those of `P'` with fuel at least
`K * (n + 1)`. -/
theorem fs_assumePre {n : Nat} (ih : FundAt cfg E Rw K Gl n) {P P' : Procedure} (hP : ProcRelB E P P')
    (args : List Value) {M' : Nat} (hM' : K * (n + 1) ≤ M') :
    FS (Sm E Gl {}) Eq (assumePreconditions cfg (n + 1) P args) (assumePreconditions cfg M' P' args) := by
  obtain ⟨M, rfl, hM⟩ := fuel_split hp.K_pos hM'
  have hcs := hP.pre
  simp only [assumePreconditions]
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  have hσ : StRel {} (IxRel E) σ σ' := hσ
  rw [zipFold_sig hP.inputs (fun acc x y v h => by simp only [h])]
  refine fs_switch (G' := condG) (fun a a' ha => by
    have := SR.freshC (gs := a.globals) (Clean.params P.inputs args hP.inNames); strel ha) ?_
  refine fs_bind (fs_tryCatch (fs_bind (S := Sm E Gl condG) (T := Sm E Gl condG) (U := Sm E Gl condG) (A := Eq) ?_ (fun _ _ _ => fs_pure rfl))
    (fun sig hsig => ?_) ?_ (fun L hL hok => ?_) (fun v => fs_noWin _ not_free_condG v)) (fun _ _ _ => ?_)
  · refine fs_forIn hcs.withMem (fun c c' ⟨hc, hm⟩ _ => ?_)
    rw [← hc.1]
    refine fs_ite (fun _ => ?_) (fun _ =>  fs_pure rfl)
    refine fs_bind fs_get (fun s s' hs => ?_)
    refine fs_bind (fs_emitE (S := Sm E Gl condG) (evRel_fail (E := _)) ⟨hc.2.1, _, hs⟩) (fun _ _ _ => ?_)
    refine fs_bind (exprMdE hp ih hc.2.1 hc.2.2 (hP.preOK c hm) hM) (fun v v' hv => ?_)
    subst hv
    refine fs_bind (fs_liftM (isTrue_pconst _)) (fun b b' hb => ?_)
    subst hb
    exact fs_ite (fun _ =>  fs_pure rfl)
      (fun _ => fs_bind (fs_throw (A := Eq) _) (fun _ _ _ => fs_pure rfl))
  · exact fs_switch (G := condG) (fun a a' ha => by
      have := hσ.stack; have := hσ.wf; have := hσ.gk; have := hσ.gk'; have := hσ.entR; have := hσ.globals; have := hσ.entryClean; have := hσ.egk; strelw ha [hσ.seek, hσ.seek', hσ.coroSelf, hσ.coroSelf', hσ.globals, hσ.ops, hσ.ops'])
      (fs_throwT _ (CtlOK.ofCond hsig))
  · intro σ τ
    simp [run_bind, run_throw, run_modify, OOF]
  · exact fs_switch (G := condG) (fun a a' ha => by
      have := hσ.stack; have := hσ.wf; have := hσ.gk; have := hσ.gk'; have := hσ.entR; have := hσ.globals; have := hσ.entryClean; have := hσ.egk; strelw ha [hσ.seek, hσ.seek', hσ.coroSelf, hσ.coroSelf', hσ.globals, hσ.ops, hσ.ops'])
      (fs_throwTM hL (CtlOK.ofCond (Gl := Gl) (c := .return_ []) hok))
  · exact fs_switch1 (G := condG) (fun a a' ha => by
      have := hσ.stack; have := hσ.wf; have := hσ.gk; have := hσ.gk'; have := hσ.entR; have := hσ.globals; have := hσ.entryClean; have := hσ.egk; strelw ha [hσ.seek, hσ.seek', hσ.coroSelf, hσ.coroSelf', hσ.globals, hσ.ops, hσ.ops'])

/-- For procedures related by `ProcRel E`, `procAct` with fuel `n + 1` (choose the arguments, assume the
preconditions, call the procedure) is simulated by `procAct` on the target with fuel at least
`K * (n + 1)`, with equal results. -/
theorem fs_procAct {P P' : Procedure} (hP : ProcRel E P P') {o o' : Options} {n : Nat}
    (hn : o.fuel = n + 1) (hM : K * (n + 1) ≤ o'.fuel) :
    FS (Sm E Gl {}) Eq (procAct cfg o P) (procAct cfg o' P') := by
  unfold procAct
  refine fs_bind fs_get (fun σ σ' hσ => ?_)
  have hσ : StRel {} (IxRel E) σ σ' := hσ
  refine fs_bind (fs_mapM hP.inputs
    (fun a b hab => by rw [hσ.index.defaultR hab.2, hab.1]; exact fs_chooseInit _ _ _ _)) (fun xs ys h => ?_)
  subst h
  rw [hn]
  refine fs_bind (fs_assumePre hp (fund hp n) hP.toB _ hM) (fun _ _ _ => ?_)
  exact fstep_procT hp (fund hp n) (fund_le hp n) true _ _ _ _ _ (stripPre_rel hP).toB _ hM

/-- Simulation of runs that start at a procedure. For a pass satisfying `PassRel` without a return
label, programs related by `ProgRel E` and procedures `P`, `P'` related by `ProcRel E`, running the
target from `P'` with fuel at least `K` times the source's gives an `ERel`-related result to running
the source from `P`, unless the source gets stuck. Neither run may use a step budget, both must have
the same `printAsserts`, and the source run must not run out of fuel. -/
theorem procAt_sim {p q : LaurelProgram} (hr : ProgRel E p q) {o o' : Options} {n : Nat}
    (hn : o.fuel = n + 1) (hM : K * (n + 1) ≤ o'.fuel)
    (hl : o.limitSteps = false) (hl' : o'.limitSteps = false) (hq : o.printAsserts = o'.printAsserts)
    (hret : Reserved.retLabel = none) {P P' : Procedure} (hP : ProcRel E P P')
    {τ τ' : Trace} (ht : TrRel (Sm E Gl {}) τ τ') (hnf : NotOOFEntry (runProcAt cfg o p P τ)) :
    ERel (Sm E Gl {}) (runProcAt cfg o p P τ) (runProcAt cfg o' q P' τ') := by
  have hinit := entryInitState_rel hr hl hl' hq
  have hstart : StRel {} (IxRel E) (entryStart o p P) (entryStart o' q P') := by
    have hfold : P'.outputs.foldl (fun (acc : StackFrame) w =>
          acc.insert w.name.text (defaultValue (entryInitState o' q).index w.type.val)) {} =
        P.outputs.foldl (fun (acc : StackFrame) w =>
          acc.insert w.name.text (defaultValue (entryInitState o p).index w.type.val)) {} :=
      (L2.foldl_congr hP.outputs (fun acc x y hxy => by rw [hxy.1, hinit.index.defaultR hxy.2]) _).symm
    unfold entryStart
    simp only [hfold]
    have := SR.fresh (gs := (entryInitState o p).globals) (Clean.empty.foldl (l := P.outputs) (fun x => x.name.text)
      (fun x => defaultValue (entryInitState o p).index x.type.val) hP.outNames)
    strelw hinit []
  have hI := (fs_initEntry (G := {}) hp hr hP hn (by omega) Strict.empty plain_empty cfg.modular).sim _ _ τ τ' hstart ht
  rw [runProcAt_eq] at hnf ⊢
  rw [runProcAt_eq]
  dsimp only at hnf ⊢
  rw [pm_bind_run] at hnf ⊢
  rw [pm_bind_run]
  rcases r1 : run (initEntry cfg o p P cfg.modular) (entryStart o p P) τ with e | ⟨⟨c | u, s1⟩, τ1⟩ <;>
    rw [r1] at hnf hI <;> dsimp only at hnf
  · have := hI not_OOF_error
    rcases r1' : run (initEntry cfg o' q P' cfg.modular) (entryStart o' q P') τ' with e' | ⟨⟨c' | u', s1'⟩, τ1'⟩ <;>
      rw [r1'] at this <;> simp only [RR] at this
    all_goals first | exact this | exact ERel.ofStuck this _
  · by_cases hc : c = .outOfFuel
    · subst hc; simp [NotOOFEntry, pure, StateT.pure, Except.pure] at hnf
    · have := hI (by rw [OOF_err]; exact hc)
      rcases r1' : run (initEntry cfg o' q P' cfg.modular) (entryStart o' q P') τ' with e' | ⟨⟨c' | u', s1'⟩, τ1'⟩ <;>
        rw [r1'] at this <;> simp only [RR, ExRel, false_and] at this
      obtain ⟨hsg, ht1⟩ := this
      obtain ⟨hcr, -, hs1⟩ := hsg.same (fun v => Sm.noWin _ not_free_empty v)
      rcases hcr with rfl | ⟨L, hL, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
      · dsimp only
        cases c <;> first | exact absurd rfl hc | trivial | exact fun h => absurd h stuck_fail
      · first | trivial | exact fun h => absurd h stuck_fail
      · exact ⟨rfl, hs1, ht1⟩
  · have := hI not_OOF_ok
    rcases r1' : run (initEntry cfg o' q P' cfg.modular) (entryStart o' q P') τ' with e' | ⟨⟨c' | u', s1'⟩, τ1'⟩ <;>
      rw [r1'] at this <;> simp only [RR, ExRel, false_and] at this
    obtain ⟨-, hs1, ht1⟩ := this
    dsimp only at hnf ⊢
    simp only [pure_bind] at hnf ⊢
    rw [pm_bind_run] at hnf ⊢
    rw [pm_bind_run]
    have hB := (fs_procAct hp hP hn hM).sim s1 s1' τ1 τ1' hs1 ht1
    rcases r2 : run (procAct cfg o P) s1 τ1 with e | ⟨⟨c | u, s2⟩, τ2⟩ <;>
      rw [r2] at hnf hB <;> dsimp only at hnf
    · have := hB not_OOF_error
      rcases r2' : run (procAct cfg o' P') s1' τ1' with e' | ⟨⟨c' | u', s2'⟩, τ2'⟩ <;>
        rw [r2'] at this <;> simp only [RR] at this
      all_goals first | exact this | exact ERel.ofStuck this _
    · by_cases hc : c = .outOfFuel
      · subst hc; simp [NotOOFEntry, pure, StateT.pure, Except.pure] at hnf
      · have := hB (by rw [OOF_err]; exact hc)
        rcases r2' : run (procAct cfg o' P') s1' τ1' with e' | ⟨⟨c' | u', s2'⟩, τ2'⟩ <;>
          rw [r2'] at this <;> simp only [RR, ExRel, false_and] at this
        obtain ⟨hsg, ht2⟩ := this
        obtain ⟨hcr, -, hs2⟩ := hsg.same (fun v => Sm.noWin _ not_free_empty v)
        rcases hcr with hcc | ⟨L, hL, -, -⟩ | ⟨_, _, rfl, rfl⟩
        · subst hcc
          dsimp only
          cases c <;> first | exact absurd rfl hc | exact ⟨rfl, hs2, ht2⟩ | exact fun h => absurd h stuck_fail
        · exact absurd (hret ▸ hL : (none : Option String) = some L) (by simp)
        · exact ⟨rfl, hs2, ht2⟩
    · have := hB not_OOF_ok
      rcases r2' : run (procAct cfg o' P') s1' τ1' with e' | ⟨⟨c' | u', s2'⟩, τ2'⟩ <;>
        rw [r2'] at this <;> simp only [RR, ExRel, false_and] at this
      exact ⟨rfl, this.2.1, this.2.2⟩

omit [Reserved] hp in
theorem L2.exists_of_mem {R : α → β → Prop} {l : List α} {l' : List β} (h : L2 R l l') {a : α} (ha : a ∈ l) :
    ∃ b ∈ l', R a b := by
  induction h with
  | nil => cases ha
  | cons hab _ ih =>
    rcases List.mem_cons.mp ha with rfl | hm
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨b, hb, hr⟩ := ih hm
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

/-- For a pass satisfying `PassRel` without a return label and programs related by `ProgRel E`, every
static procedure `P` of the source has a static procedure `P'` of the target such that, for related
traces, running the target from `P'` with fuel at least `K` times the source's gives an
`ERel`-related result to running the source from `P`, unless the source run gets stuck or runs out
of fuel. Neither run may use a step budget and both must have the same `printAsserts`. -/
theorem procAt_all {p q : LaurelProgram} (hr : ProgRel E p q) {o o' : Options} {n : Nat}
    (hn : o.fuel = n + 1) (hM : K * (n + 1) ≤ o'.fuel)
    (hl : o.limitSteps = false) (hl' : o'.limitSteps = false) (hq : o.printAsserts = o'.printAsserts)
    (hret : Reserved.retLabel = none) {P : Procedure} (hPm : P ∈ p.staticProcedures) :
    ∃ P' ∈ q.staticProcedures, ∀ τ τ', TrRel (Sm E Gl {}) τ τ' → NotOOFEntry (runProcAt cfg o p P τ) →
      ERel (Sm E Gl {}) (runProcAt cfg o p P τ) (runProcAt cfg o' q P' τ') := by
  obtain ⟨ps, extra, hqs, hps, -⟩ := hr.procs
  obtain ⟨P', hP'm, hPP⟩ := hps.exists_of_mem hPm
  refine ⟨P', by rw [hqs]; exact List.mem_append_left _ hP'm, fun τ τ' ht hnf => ?_⟩
  exact procAt_sim hp hr hn hM hl hl' hq hret hPP ht hnf

end

end Strata.Laurel.PassSemantics
