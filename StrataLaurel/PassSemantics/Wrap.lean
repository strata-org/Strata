/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.Fund

/-!
# Simulation lemmas for wrapped procedure bodies

A pass may wrap a procedure body in a labelled block, so that `return` becomes an exit
from that block. This file proves the simulation lemmas `FundProof.lean` needs for such
bodies, including a `return e` that the pass turns into an assignment to the single output
followed by an exit.

* `runB x`: runs `x` and turns `return` into a result value.
* `Sm0`: `Sm` with no return label, used for the caller's side of a wrapped body.
* `body_wrap`: a body simulates the same statements wrapped in a block labelled with the
  return label.
* `body_valued_gen`, `body_valuedB_gen`: `return e` simulates the assignment of `e` to the
  output followed by an exit.
* `FSV` and `fs_bindV`: a variant of `FSH` whose value relation can depend on the states,
  and its `bind` rule.
* `procTail` and `procTail_ofAt`: the end of a procedure call (postcondition checks and
  output collection), and its simulation when the body returned a value.
-/

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

def runB (x : EvalM PM Unit) : EvalM PM (Option Value) :=
  tryCatch (do x; pure none) fun
    | .return_ [] => pure none
    | .return_ [v] => pure (some v)
    | c => throw c

theorem ext_run {x y : EvalM PM α} (h : ∀ σ τ, run x σ τ = run y σ τ) : x = y := by
  funext σ τ
  exact h σ τ

theorem tc_runB (x : EvalM PM Unit) (H : Control → EvalM PM (Option Value))
    (hH0 : H (.return_ []) = pure none) (hH1 : ∀ v, H (.return_ [v]) = pure (some v)) :
    tryCatch (x >>= fun _ => pure none) H = tryCatch (runB x) H := by
  refine ext_run (fun σ τ => ?_)
  simp only [runB, run_tryCatch, run_bind]
  rcases run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;> dsimp only
  · cases c with
    | return_ vs => rcases vs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> simp only [hH0, hH1, run_throw, run_pure]
    | _ => simp only [run_throw]
  · rfl

section
variable [Reserved] {E : StmtExprMd → StmtExprMd → Prop} {Gl : String → Prop}

def Sm0 (E : StmtExprMd → StmtExprMd → Prop) (Gl : String → Prop) (G : StackFrame) : SimRel :=
  ⟨StRel G (IxRel E), EvRel E, CtlOK Gl G, none, fun _ _ _ => False⟩

theorem fsh_sm0 {T U : SimRel} {A : α → β → Prop} {x : EvalM PM α} {y : EvalM PM β} {G : StackFrame}
    (h : FSH (Sm E Gl G) T U A x y) : FSH (Sm0 E Gl G) T U A x y := ⟨h.sim⟩


/-- A body `X` simulates the same statements `ss'` wrapped in a block labelled with the pass's return
label `L`. If `X` is simulated by running `ss'` in a block scope, where a source `return` may become
`exit L`, then `runB X` is simulated by `runB` of the labelled block, which catches that `exit L`.
Escaping signals are related by `Sm0`, which has no return label. `L` must be reserved and not an exit label
that may escape (`¬ Gl L`) and the pass has no valued return. -/
theorem body_wrap {cfg : ExternalBackendM PM} {M : Nat} {X : EvalM PM Unit} {ss' : List StmtExprMd} {s' : FileRange}
    {L : String} {G : StackFrame} (hL : Reserved.retLabel = some L) (hGl : ¬ Gl L) (hvn : Reserved.vret = none)
    (hres : Reserved.resLabel L)
    (hin : FS (Sm E Gl G) (fun _ _ => True) X (withBlockScope ss' (evalStmtList cfg M ss' false))) :
    FSH (Sm E Gl G) (Sm E Gl G) (Sm0 E Gl G) Eq (runB X)
      (runB (evalStmt cfg (M + 1) ⟨.Block ss' (some L) [] none, s'⟩)) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have hs' : StRel G (IxRel E) σ σ' := hs
  have hkeep : KeepsOL (withBlockScope ss' (evalStmtList cfg M ss' false)) :=
    fun o => OLKeep.withBlockScope ((keepsAt cfg M).list ss' false o)
  simp only [runB, evalStmt, List.forIn_nil, pure_bind, run_tryCatch, run_bind, run_get, run_withOpenLabel] at hn ⊢
  have r0 := hin.sim σ { σ' with openLabels := L :: σ'.openLabels } τ τ' (hs'.pushOL hres) ht
  rcases r : run X σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;> rw [r] at r0 hn <;>
    rcases r' : run (withBlockScope ss' (evalStmtList cfg M ss' false)) { σ' with openLabels := L :: σ'.openLabels } τ' with
      e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;>
    rw [r'] at r0 <;> dsimp only at hn ⊢
  · first | trivial | exact r0 not_OOF_error
  · first | exact RR.ofStuck (r0 not_OOF_error) _ | exact RV.ofStuck (r0 not_OOF_error) _ | exact r0 not_OOF_error
  · first | exact RR.ofStuck (r0 not_OOF_error) _ | exact RV.ofStuck (r0 not_OOF_error) _ | exact r0 not_OOF_error
  · have hn0 : ¬ OOF (Except.ok ((Except.error c, σ1), τ1) : R Unit) := by
      rw [OOF_err]; rintro rfl; exact hn (by simp [run_throw, OOF])
    exact absurd (r0 hn0) (by simp [RR])
  · have hn0 : ¬ OOF (Except.ok ((Except.error c, σ1), τ1) : R Unit) := by
      rw [OOF_err]; rintro rfl; exact hn (by simp [run_throw, OOF])
    obtain ⟨hsg, ht1⟩ := r0 hn0
    obtain ⟨hcr, hok, hs1⟩ := hsg.same (fun v => Sm.noWin _ (not_free_none hvn _) v)
    have hk := (hkeep (L :: σ'.openLabels)).keep _ _ _ _ _ rfl r'
    have hs2 : StRel G (IxRel E) σ1 { σ1' with openLabels := σ'.openLabels } := (hs1 : StRel G (IxRel E) σ1 σ1').restoreOL hk hres
    rcases hcr with rfl | ⟨L', hL', rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
    · cases c with
      | exit_ l =>
        have hne : (l == L) = false := by
          simp only [beq_eq_false_iff_ne]; rintro rfl; exact hGl hok
        simp only [hne, Bool.false_eq_true, ite_false, run_throw]
        exact ⟨.inl ⟨.inl rfl, hok, hs2⟩, ht1⟩
      | return_ v =>
        rcases v with _ | ⟨w, _ | ⟨_, _⟩⟩
        · simp only [run_throw, run_pure, RR, ExRel]
          exact ⟨trivial, hs2, ht1⟩
        · simp only [run_throw, run_pure, RR, ExRel]
          exact ⟨trivial, hs2, ht1⟩
        · exact (hok : False).elim
      | goto_ l =>
        have hne : (l == L) = false := by
          simp only [beq_eq_false_iff_ne]; rintro rfl; exact hGl hok
        simp only [hne, Bool.false_eq_true, ite_false, run_throw]
        exact ⟨.inl ⟨.inl rfl, hok, hs2⟩, ht1⟩
      | _ =>
        simp only [run_throw, RR, ExRel]
        exact ⟨.inl ⟨.inl rfl, hok, hs2⟩, ht1⟩
    · have : L' = L := Option.some.inj (hL'.symm.trans hL)
      subst this
      simp only [beq_self_eq_true, ite_true, run_modify, run_pure, RR, ExRel]
      have hs3 : StRel G (IxRel E) σ1 { σ1' with cursor := σ'.cursor, seek := none } := by
        strel (hs1 : StRel G (IxRel E) σ1 σ1')
      exact ⟨trivial, hs3.restoreOL hk hres, ht1⟩
    · simp only [run_throw, RR, ExRel] at *
      exact ⟨.inl ⟨.inr (.inr ⟨_, _, rfl, rfl⟩), hok, hs2⟩, ht1⟩
  · have hn0 : ¬ OOF (Except.ok ((Except.error c, σ1), τ1) : R Unit) := by
      rw [OOF_err]; rintro rfl; exact hn (by simp [run_throw, OOF])
    exact absurd (r0 hn0) (by simp [RR, ExRel])
  · exact absurd (r0 not_OOF_ok) (by simp [RR])
  · exact absurd (r0 not_OOF_ok) (by simp [RR, ExRel])
  · obtain ⟨-, hs1, ht1⟩ := r0 not_OOF_ok
    have hk := (hkeep (L :: σ'.openLabels)).keep _ _ _ _ _ rfl r'
    have hs2 : StRel G (IxRel E) σ1 { σ1' with openLabels := σ'.openLabels } := (hs1 : StRel G (IxRel E) σ1 σ1').restoreOL hk hres
    simp only [run_pure, RR, ExRel]
    exact ⟨trivial, hs2, ht1⟩

omit [Reserved] in
theorem withBlockScope_nil {l : List StmtExprMd} (h : blockDeclarations l = []) (act : EvalM PM α) :
    withBlockScope l act = act := by
  unfold withBlockScope
  simp [h]

theorem fs_wrapBlock_inner {cfg : ExternalBackendM PM} {n M : Nat} {ss ss' : List StmtExprMd} {s : FileRange}
    {G : StackFrame}
    (hin : FS (Sm E Gl G) Eq (withBlockScope ss (evalStmtList cfg n ss false))
      (withBlockScope ss' (evalStmtList cfg M ss' false))) :
    FS (Sm E Gl G) (fun _ _ => True) (evalStmt cfg (n + 1) ⟨.Block ss none [] none, s⟩)
      (withBlockScope ss' (evalStmtList cfg M ss' false)) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have hs' : StRel G (IxRel E) σ σ' := hs
  simp only [evalStmt, run_bind, run_chargeStep hs'.steps] at hn ⊢
  have r0 := hin.sim σ σ' τ τ' hs ht
  rcases r : run (withBlockScope ss (evalStmtList cfg n ss false)) σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;>
    rw [r] at r0 hn <;> dsimp only at hn ⊢
  · have := r0 not_OOF_error
    revert this
    rcases run (withBlockScope ss' (evalStmtList cfg M ss' false)) σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;>
      simp [RR]
  · have := r0 (by rw [OOF_err] at hn ⊢; exact hn)
    revert this
    rcases run (withBlockScope ss' (evalStmtList cfg M ss' false)) σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;>
      simp only [RR, ExRel, false_and, imp_self]
  · have := r0 not_OOF_ok
    revert this
    rcases run (withBlockScope ss' (evalStmtList cfg M ss' false)) σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;>
      simp only [RR, ExRel, false_and, imp_self, run_pure]
    exact fun ⟨_, h1, h2⟩ => ⟨trivial, h1, h2⟩

omit [Reserved] in
/-- A statement list none of whose statements holds a label never lands a jump, so running it is running its
statements one after the other: the handler for jumps only rethrows. -/
theorem evalStmtList_plain {cfg : ExternalBackendM PM} {m : Nat} {ss : List StmtExprMd}
    (hl : ∀ s ∈ ss, statementLabels s = []) :
    evalStmtList cfg (m + 1) ss false =
      (get >>= fun st => if st.coroSelf.isNone = true then
        (ss.forM (fun s => do
            modify fun (st : EvalState) => { st with stmtSite := s.source }
            if (stackAnnotation? s).isNone then withOperandWindow s (evalStmt cfg m s)) >>= fun _ => pure default)
      else
        evalStmtListGo cfg m false st.cursor (seekEntry st.seek).1 (seekEntry st.seek).2 (seekEntry st.seek).1
          (ss.drop (seekEntry st.seek).1)) := by
  have hnone : ∀ l, ss.findIdx? (fun t => (statementLabels t).contains l) = none := by
    intro l
    rw [List.findIdx?_eq_none_iff]
    intro t ht
    rw [hl t ht]
    rfl
  refine ext_run (fun σ τ => ?_)
  unfold evalStmtList
  simp only [run_bind, run_get, Bool.false_eq_true, ite_false]
  split
  · simp only [run_bind, run_tryCatch]
    rcases hr : run (ss.forM fun s => do
        modify fun (st : EvalState) => { st with stmtSite := s.source }
        if (stackAnnotation? s).isNone then withOperandWindow s (evalStmt cfg m s)) σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩
    · rfl
    · cases c with
      | jump_ l d => simp only [hnone l, run_throw]
      | _ => simp [run_throw]
    · rfl
  · rfl

theorem fs_wrapOther_inner {cfg : ExternalBackendM PM} {n M : Nat} {b b' : StmtExprMd} {G : StackFrame}
    (hd : blockDeclarations [b'] = []) (hl : ∀ l, Gl l → l ∉ statementLabels b')
    (hann : (stackAnnotation? b').isNone = true)
    (hb : FS (Sm E Gl G) Eq (evalStmt cfg n b) (evalStmt cfg M b')) :
    FS (Sm E Gl G) (fun _ _ => True) (evalStmt cfg n b)
      (withBlockScope [b'] (evalStmtList cfg (M + 1) [b'] false)) := by
  rw [withBlockScope_nil hd]
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have hs' : StRel G (IxRel E) σ σ' := hs
  simp only [evalStmtList, run_bind, run_get, hs'.coroSelf', Option.isNone_none, ite_true, Bool.false_eq_true,
    ite_false, List.forM_eq_forM, List.forM_cons, List.forM_nil, bind_assoc, pure_bind, run_modify, hann,
    run_tryCatch]
  have r0 := hb.sim σ { σ' with stmtSite := b'.source } τ τ' (by strel hs') ht hn
  simp only [hs'.coroSelf', hs'.ops'] at r0
  simp only [run_wow_nil, hs'.ops']
  revert r0
  generalize run (evalStmt cfg M b') _ τ' = y
  rcases run (evalStmt cfg n b) σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;>
    rcases y with e' | ⟨⟨c' | b1, σ1'⟩, τ1'⟩ <;> intro r0 <;> simp only [run_pure]
  · exact r0
  · exact RR.ofStuck r0 _
  · exact RR.ofStuck r0 _
  · exact (r0 : False).elim
  · cases c' with
    | jump_ l d =>
      obtain ⟨hsg, ht1⟩ := r0
      rcases hsg with ⟨hcr, hok, hs1⟩ | ⟨v, h1, h2, h3⟩
      · rcases hcr with rfl | ⟨L, -, -, h⟩ | ⟨_, _, -, h⟩
        · have hf : List.findIdx? (fun t => (statementLabels t).contains l) [b'] = none := by
            rw [List.findIdx?_eq_none_iff]
            intro t ht
            rw [List.mem_singleton.mp ht]
            cases hc : (statementLabels b').contains l
            · rfl
            · exact absurd (List.contains_iff_mem.mp hc) (hl l hok)
          simp only [hf, run_throw]
          exact ⟨.inl ⟨.inl rfl, hok, hs1⟩, ht1⟩
        · cases h
        · cases h
      · cases h2
    | _ =>
      first
        | exact r0
        | (simp only [run_throw]; exact r0)
  · exact (r0.1 : False).elim
  · exact (r0 : False).elim
  · exact (r0.1 : False).elim
  · obtain ⟨-, hs1, ht1⟩ := r0
    exact ⟨trivial, hs1, ht1⟩

def RV (T U : SimRel) (A : α → β → EvalState → EvalState → Prop) : R α → R β → Prop
  | .error e, .error e' => Stuck e' → Stuck e
  | .error e, .ok _ => Stuck e
  | .ok ((.ok a, σ), τ), .ok ((.ok b, σ'), τ') => A a b σ σ' ∧ TrRel T τ τ'
  | .ok ((.error c, σ), τ), .ok ((.error c', σ'), τ') => SigR U c c' σ σ' ∧ TrRel U τ τ'
  | _, _ => False

omit [Reserved] in
theorem RV.reRef {T U : SimRel} {A : α → β → EvalState → EvalState → Prop} {a : R α} {b : R β} (q' : String)
    (h : RV T U A a b) : RV T U A a (PassSemantics.reRef q' b) := by
  rcases b with e' | ⟨⟨c' | b, σ'⟩, τ'⟩
  · exact h
  · cases c' with
    | refused r' =>
      rw [show PassSemantics.reRef q' (.ok ((.error (.refused r'), σ'), τ') : R β) = .ok ((.error (.refused q'), σ'), τ') from rfl]
      rcases a with e | ⟨⟨c | a, σ⟩, τ⟩
      · exact h
      · simp only [RV] at h ⊢
        obtain ⟨hs, ht⟩ := h
        refine ⟨?_, ht⟩
        rcases hs with ⟨hc, hok, hst⟩ | ⟨v, _, h2, _⟩
        · refine .inl ⟨?_, hok, hst⟩
          rcases hc with rfl | ⟨L, _, _, h2⟩ | ⟨r, _, rfl, _⟩
          · exact .inr (.inr ⟨_, _, rfl, rfl⟩)
          · cases h2
          · exact .inr (.inr ⟨_, _, rfl, rfl⟩)
        · cases h2
      · simp only [RV] at h
    | _ => exact h
  · exact h

omit [Reserved] in
theorem RV.ofStuck {T U : SimRel} {A : α → β → EvalState → EvalState → Prop} {e : HErr} (h : Stuck e)
    (r' : R β) : RV T U A (.error e : R α) r' := by
  rcases r' with _ | _
  · exact fun _ => h
  · exact h

structure FSV (S T U : SimRel) (A : α → β → EvalState → EvalState → Prop) (x : EvalM PM α) (y : EvalM PM β) :
    Prop where
  sim : ∀ σ σ' τ τ', S.st σ σ' → TrRel S τ τ' → ¬ OOF (run x σ τ) → RV T U A (run x σ τ) (run y σ' τ')

def At (T : SimRel) (σ0 σ0' : EvalState) : SimRel := ⟨fun σ σ' => σ = σ0 ∧ σ' = σ0', T.ev, T.ok, T.ret, T.win⟩

omit [Reserved] in
/-- `bind` rule for `FSV`: if `x` is simulated by `y` with values related by `A` depending on the end
states, and for all values `a`, `b` and states `σ0`, `σ0'` with `A a b σ0 σ0'` the continuation `f a`
is simulated by `g b` from exactly those states (`At T σ0 σ0'`), then `x >>= f` is simulated by
`y >>= g`. -/
theorem fs_bindV {S T U V : SimRel} {A : α → β → EvalState → EvalState → Prop} {B : γ → δ → Prop}
    {x : EvalM PM α} {y : EvalM PM β} {f : α → EvalM PM γ} {g : β → EvalM PM δ} (hx : FSV S T U A x y)
    (hf : ∀ a b σ0 σ0', A a b σ0 σ0' → FSH (At T σ0 σ0') V U B (f a) (g b)) : FSH S V U B (x >>= f) (y >>= g) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have h0 := hx.sim σ σ' τ τ' hs ht (not_oof_bind hn)
  simp only [run_bind] at hn ⊢
  rcases r : run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;>
    rcases r' : run y σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;> rw [r, r'] at h0 <;> rw [r] at hn <;>
    simp only [RV] at h0 ⊢
  stuck_close
  all_goals first
    | (simp only [RR, ExRel]; exact h0)
    | exact (hf _ _ _ _ h0.1).sim _ _ _ _ ⟨rfl, rfl⟩ h0.2 hn

omit [Reserved] in
theorem FSV.ofFSH {S T U : SimRel} {A' : α → β → Prop} {A : α → β → EvalState → EvalState → Prop}
    {x : EvalM PM α} {y : EvalM PM β} (h : FSH S T U A' x y) (hA : ∀ a b σ σ', A' a b → T.st σ σ' → A a b σ σ') :
    FSV S T U A x y := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have h0 := h.sim σ σ' τ τ' hs ht hn
  revert h0
  rcases run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;> rcases run y σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;>
    simp only [RR, ExRel, RV, imp_self, false_and]
  exact fun ⟨h1, h2, h3⟩ => ⟨hA _ _ _ _ h1 h2, h3⟩

omit [Reserved] in
theorem FSH.ofAt {S T U : SimRel} {A : α → β → Prop} {x : EvalM PM α} {y y' : EvalM PM β} {σ0 σ0' σ0'' : EvalState}
    (h : FSH S T U A x y') (hs : S.st σ0 σ0'') (hy : ∀ τ', run y σ0' τ' = run y' σ0'' τ') :
    FSH (At S σ0 σ0') T U A x y := by
  refine ⟨fun σ σ' τ τ' hst ht hn => ?_⟩
  obtain ⟨rfl, rfl⟩ := hst
  rw [hy]
  exact h.sim σ σ0'' τ τ' hs ht hn


def procTail (cfg : ExternalBackendM PM) (fuel : Nat) (proc : Procedure) (posts : List Condition)
    (frames : List ModifiesGroup) (skip : Bool) (calleeStack : StackFrame) (entry : Array HeapObject × Std.HashMap String Value)
    (restoreCaller : EvalM PM Unit) (outs : List Parameter) (returned : Option Value) : EvalM PM (Array Value) := do
  let calleeFrame := (← get).stack
  unless skip do
    tryCatch (checkPostconditions cfg fuel proc posts frames calleeStack entry calleeFrame returned)
      fun sig => do restoreCaller; throw sig
  restoreCaller
  match returned with
  | some v => pure #[v]
  | none => pure (outs.toArray.map fun o => calleeFrame[o.name.text]?.getD .unset)

omit [Reserved] in
theorem checkPost_stack (cfg : ExternalBackendM PM) (f : Nat) (P : Procedure) (ps : List Condition)
    (fr : List ModifiesGroup) (ef : StackFrame) (ent : Array HeapObject × Std.HashMap String Value) (xf : StackFrame) (r : Option Value)
    {g : EvalState → EvalState} (hg : ∀ σ s, g { σ with stack := s } = g σ)
    (σ : EvalState) (s : StackFrame) (τ : Trace) :
    run (tryCatch (checkPostconditions cfg f P ps fr ef ent xf r) fun sig => do modify g; throw sig)
        { σ with stack := s } τ =
      run (tryCatch (checkPostconditions cfg f P ps fr ef ent xf r) fun sig => do modify g; throw sig) σ τ := by
  cases f with
  | zero => simp only [checkPostconditions, run_tryCatch, run_throw, run_bind, run_modify, hg]
  | succ f => simp only [checkPostconditions, run_tryCatch, run_bind, run_get, run_modify]

omit [Reserved] in
theorem checkPost_valued (cfg : ExternalBackendM PM) (f : Nat) {P : Procedure} {o o' : Parameter}
    (ho : P.outputs = [o']) (hn : o'.name.text = o.name.text) (ps : List Condition) (fr : List ModifiesGroup) (ef : StackFrame)
    (ent : Array HeapObject × Std.HashMap String Value)
    {xf : StackFrame} {v : Value} (hv : xf[o.name.text]? = some v) (xf2 : StackFrame) :
    checkPostconditions cfg f P ps fr ef ent xf none = checkPostconditions cfg f P ps fr ef ent xf2 (some v) := by
  cases f with
  | zero => rfl
  | succ f => simp only [checkPostconditions, Interpreter.postOutputs, ho, hn, List.foldl_cons, List.foldl_nil, hv,
      Option.getD_some]

omit [Reserved] in
theorem procTail_valued (cfg : ExternalBackendM PM) (fuel : Nat) {proc : Procedure} {o o' : Parameter}
    (ho : proc.outputs = [o']) (hn : o'.name.text = o.name.text) {outs : List Parameter} (hos : outs = [o]) (posts : List Condition)
    (frames : List ModifiesGroup) (sk : Bool) (cs : StackFrame)
    (ent : Array HeapObject × Std.HashMap String Value) {g : EvalState → EvalState}
    (hg : ∀ σ s, g { σ with stack := s } = g σ) (σ : EvalState) (s : StackFrame) (v : Value) (τ : Trace) :
    run (procTail cfg fuel proc posts frames sk cs ent (modify g) outs none) { σ with stack := s.insert o.name.text v } τ =
      run (procTail cfg fuel proc posts frames sk cs ent (modify g) outs (some v)) { σ with stack := s } τ := by
  have hv : (s.insert o.name.text v)[o.name.text]? = some v := by simp
  simp only [procTail, run_bind, run_get]
  rw [checkPost_valued cfg fuel ho hn posts frames cs ent hv s]
  split
  · simp only [run_bind, run_modify, run_pure, hg]
    simp [hos]
  · simp only [run_bind]
    rw [checkPost_stack cfg fuel proc posts frames cs ent s (some v) hg σ (s.insert o.name.text v),
      checkPost_stack cfg fuel proc posts frames cs ent s (some v) hg σ s]
    rcases run (tryCatch (checkPostconditions cfg fuel proc posts frames cs ent s (some v))
      fun sig => do modify g; throw sig) σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩
    · rfl
    · rfl
    · simp [run_modify, run_pure, hos]

def VA (E : StmtExprMd → StmtExprMd → Prop) (o : Parameter) (r r' : Option Value) (σ σ' : EvalState) : Prop :=
  (r = r' ∧ StRel {} (IxRel E) σ σ') ∨
    (∃ v s0, r = some v ∧ r' = none ∧ σ'.stack = s0.insert o.name.text v ∧
      StRel {} (IxRel E) σ { σ' with stack := s0 })

omit [Reserved] in
theorem evalStmt_assign1 {cfg : ExternalBackendM PM} {M : Nat} {e' : StmtExprMd} (hy : NotYield e')
    (t : VariableMd) (ht : isStackVar t = false) (s2 : FileRange) :
    evalStmt cfg (M + 1) ⟨.Assign [t] e', s2⟩ =
      (assignTarget cfg M t.val >>= fun w => evalExprMd cfg M e' >>= fun v => writeUpdate w v) := by
  have hnp : isStackPushTarget [t] = false := by simp [isStackPushTarget, ht]
  simp only [evalStmt, hnp, Bool.false_eq_true, ite_false]
  split
  · rename_i h; simp [NotYield, h] at hy
  · rfl

omit [Reserved] in
theorem run_assignLocal {x : Identifier} {v : Value} {σ : EvalState} (hg : σ.globals.contains x.text = false)
    (τ : Trace) :
    run (assignLocal x v : EvalM PM Unit) σ τ = .ok ((.ok (), { σ with stack := σ.stack.insert x.text v }), τ) := by
  simp only [assignLocal, run_modify, hg, Bool.false_eq_true, ite_false]
  split <;> rfl

/-- A source `return e` simulates a target block labelled with the return label `L` whose statements are
`a`, which evaluates `e'` and assigns it to the output `o`, then `x`, which exits `L`. Neither
statement declares a name and `e` is simulated by `e'` with equal values. The results are related by
`VA E o`: equal results in related states, or the source returned `v` and the target holds `v` in `o`
on top of a related stack. The pass has the return label `L`, which may not escape, sets
`noGlobals`, and has no valued return. -/
theorem body_valued_gen {cfg : ExternalBackendM PM} {n M : Nat} {e e' a x : StmtExprMd} {o : Parameter}
    {s s' : FileRange} {L : String} (hL : Reserved.retLabel = some L) (hGl : ¬ Gl L) (hng : Reserved.noGlobals)
    (hvn : Reserved.vret = none) (hres : Reserved.resLabel L)
    (ha : evalStmt cfg (M + 2) a = (evalExprMd cfg (M + 1) e' >>= fun v => assignLocal o.name v))
    (hx : x.val = .Goto L .blockEnd) (hd : blockDeclarations [a, x] = [])
    (hann : (stackAnnotation? a).isNone = true) (hla : statementLabels a = [])
    (hexp : FS (Sm E Gl {}) Eq (evalExprMd cfg n e) (evalExprMd cfg (M + 1) e')) :
    FSV (Sm E Gl {}) (Sm E Gl {}) (Sm0 E Gl {}) (VA E o) (runB (evalStmt cfg (n + 1) ⟨.Return [e], s⟩))
      (runB (evalStmt cfg (M + 4) ⟨.Block [a, x] (some L) [] none, s'⟩)) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have hs' : StRel {} (IxRel E) σ σ' := hs
  rcases x with ⟨xv, xs⟩
  dsimp only at hx
  subst hx
  have hkeep : KeepsOL (evalExprMd cfg (M + 1) e') := (keepsAt cfg (M + 1)).exprMd e'
  have hlx : statementLabels (⟨.Goto L .blockEnd, xs⟩ : StmtExprMd) = [] :=
    statementLabels_other _ _ (by intros; nofun) (by intros; nofun)
  have hl' : ∀ t ∈ [a, (⟨.Goto L .blockEnd, xs⟩ : StmtExprMd)], statementLabels t = [] := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hla
    · exact hlx
  have hxa : (stackAnnotation? (⟨.Goto L .blockEnd, xs⟩ : StmtExprMd)).isNone = true := by simp [stackAnnotation?]
  simp only [runB, evalStmt, List.forIn_nil, pure_bind, List.mapM_cons, List.mapM_nil, withBlockScope_nil hd,
    evalStmtList_plain hl', bind_assoc, pure_bind, run_tryCatch, run_bind, run_get, hs'.coroSelf', Option.isNone_none,
    ite_true, List.forM_eq_forM, List.forM_cons, List.forM_nil, run_modify, ha,
    run_wow_nil, hs'.ops', run_withOpenLabel, hann, hxa] at hn ⊢
  have r0 := hexp.sim σ { σ' with openLabels := L :: σ'.openLabels, stmtSite := a.source } τ τ'
    (StRel.site (hs'.pushOL hres) a.source) ht
  simp only [hs'.coroSelf', hs'.ops'] at r0
  rcases r : run (evalExprMd cfg n e) σ τ with e0 | ⟨⟨c | v, σ1⟩, τ1⟩ <;> rw [r] at r0 hn <;>
    revert r0 <;>
    generalize hY : run (evalExprMd cfg (M + 1) e') _ τ' = Y <;> intro r0 <;>
    rcases Y with e1 | ⟨⟨c' | v', σ1'⟩, τ1'⟩ <;> dsimp only at hn ⊢
  · first | trivial | exact r0 not_OOF_error
  · first | exact RR.ofStuck (r0 not_OOF_error) _ | exact RV.ofStuck (r0 not_OOF_error) _ | exact r0 not_OOF_error
  · first | exact RR.ofStuck (r0 not_OOF_error) _ | exact RV.ofStuck (r0 not_OOF_error) _ | exact r0 not_OOF_error
  · have hn0 : ¬ OOF (Except.ok ((Except.error c, σ1), τ1) : R Value) := by
      rw [OOF_err]; rintro rfl; exact hn (by simp [run_throw, OOF])
    exact absurd (r0 hn0) (by simp [RR])
  · have hn0 : ¬ OOF (Except.ok ((Except.error c, σ1), τ1) : R Value) := by
      rw [OOF_err]; rintro rfl; exact hn (by simp [run_throw, OOF])
    obtain ⟨hsg, ht1⟩ := r0 hn0
    obtain ⟨hcr, hok, hs1⟩ := hsg.same (fun v => Sm.noWin _ (not_free_none hvn _) v)
    have hs1' : StRel {} (IxRel E) σ1 σ1' := hs1
    have hk := (hkeep (L :: σ'.openLabels)).keep _ _ _ _ _ rfl hY
    have hs2 : StRel {} (IxRel E) σ1 { σ1' with openLabels := σ'.openLabels } := hs1'.restoreOL hk hres
    rcases hcr with rfl | ⟨L', hL', rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
    · cases c with
      | exit_ l =>
        have hne : (l == L) = false := by
          simp only [beq_eq_false_iff_ne]; rintro rfl; exact hGl hok
        simp only [hne, Bool.false_eq_true, ite_false, run_throw]
        exact ⟨.inl ⟨.inl rfl, hok, hs2⟩, ht1⟩
      | return_ w =>
        rcases w with _ | ⟨_, _ | ⟨_, _⟩⟩
        · simp only [run_throw, run_pure, RV]
          exact ⟨.inl ⟨rfl, hs2⟩, ht1⟩
        · simp only [run_throw, run_pure, RV]
          exact ⟨.inl ⟨rfl, hs2⟩, ht1⟩
        · first | exact (hok : False).elim | exact (h : False).elim | exact (hc : False).elim
      | goto_ l =>
        have hne : (l == L) = false := by
          simp only [beq_eq_false_iff_ne]; rintro rfl; exact hGl hok
        simp only [hne, Bool.false_eq_true, ite_false, run_throw]
        exact ⟨.inl ⟨.inl rfl, hok, hs2⟩, ht1⟩
      | _ =>
        simp only [run_throw, RV]
        exact ⟨.inl ⟨.inl rfl, hok, hs2⟩, ht1⟩
    · have : L' = L := Option.some.inj (hL'.symm.trans hL)
      subst this
      simp only [beq_self_eq_true, ite_true, run_modify, run_pure, RV]
      have hs3 : StRel {} (IxRel E) σ1 { σ1' with cursor := σ'.cursor, seek := none } := by strel hs1'
      exact ⟨.inl ⟨rfl, hs3.restoreOL hk hres⟩, ht1⟩
    · simp only [run_throw, RR, ExRel] at *
      exact ⟨.inl ⟨.inr (.inr ⟨_, _, rfl, rfl⟩), hok, hs2⟩, ht1⟩
  · have hn0 : ¬ OOF (Except.ok ((Except.error c, σ1), τ1) : R Value) := by
      rw [OOF_err]; rintro rfl; exact hn (by simp [run_throw, OOF])
    exact absurd (r0 hn0) (by simp [RR, ExRel])
  · exact absurd (r0 not_OOF_ok) (by simp [RR])
  · exact absurd (r0 not_OOF_ok) (by simp [RR, ExRel])
  · obtain ⟨rfl, hs1, ht1⟩ := r0 not_OOF_ok
    have hs1' : StRel {} (IxRel E) σ1 σ1' := hs1
    have hk := (hkeep (L :: σ'.openLabels)).keep _ _ _ _ _ rfl hY
    have hgl : σ1'.globals.contains o.name.text = false := hs1'.gk' _ (.inl hng)
    simp only [run_assignLocal hgl, run_wow_nil, hs1'.ops', run_bind, run_get, hk, List.contains_cons,
      beq_self_eq_true, Bool.true_or, ite_true, run_throw, run_modify, run_pure, RV]
    have hs3 : StRel {} (IxRel E) σ1 { σ1' with cursor := σ'.cursor, seek := none, stmtSite := xs } := by strel hs1'
    refine ⟨.inr ⟨v, σ1'.stack, rfl, rfl, rfl, ?_⟩, ht1⟩
    have h4 := hs3.restoreOL hk hres
    rw [← hs1'.ops'] at ⊢
    exact h4

/-- A source block containing only `return e` simulates a target block labelled with the return label
`L` that contains an unlabelled block of `a`, which evaluates `e'` and assigns it to the output `o`,
then `x`, which exits `L`. Neither statement declares a name and `e` is simulated by `e'` with equal
values. The results are related by `VA E o`: equal results in related states, or the source returned
`v` and the target holds `v` in `o` on top of a related stack. The pass has the return label `L`,
which may not escape, sets `noGlobals`, and has no valued return. -/
theorem body_valuedB_gen {cfg : ExternalBackendM PM} {n M : Nat} {e e' a x : StmtExprMd} {o : Parameter}
    {s s' s0 s4 : FileRange} {L : String} (hL : Reserved.retLabel = some L) (hGl : ¬ Gl L) (hng : Reserved.noGlobals)
    (hvn : Reserved.vret = none) (hres : Reserved.resLabel L)
    (ha : evalStmt cfg (M + 2) a = (evalExprMd cfg (M + 1) e' >>= fun v => assignLocal o.name v))
    (hx : x.val = .Goto L .blockEnd) (hd : blockDeclarations [a, x] = [])
    (hann : (stackAnnotation? a).isNone = true) (hla : statementLabels a = [])
    (hexp : FS (Sm E Gl {}) Eq (evalExprMd cfg n e) (evalExprMd cfg (M + 1) e')) :
    FSV (Sm E Gl {}) (Sm E Gl {}) (Sm0 E Gl {}) (VA E o)
      (runB (evalStmt cfg (n + 3) ⟨.Block [⟨.Return [e], s0⟩] none [] none, s⟩))
      (runB (evalStmt cfg (M + 6) ⟨.Block [⟨.Block [a, x] none [] none, s4⟩] (some L) [] none, s'⟩)) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have hs' : StRel {} (IxRel E) σ σ' := hs
  rcases x with ⟨xv, xs⟩
  dsimp only at hx
  subst hx
  have hkeep : KeepsOL (evalExprMd cfg (M + 1) e') := (keepsAt cfg (M + 1)).exprMd e'
  have hlx : statementLabels (⟨.Goto L .blockEnd, xs⟩ : StmtExprMd) = [] :=
    statementLabels_other _ _ (by intros; nofun) (by intros; nofun)
  have hl' : ∀ t ∈ [a, (⟨.Goto L .blockEnd, xs⟩ : StmtExprMd)], statementLabels t = [] := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hla
    · exact hlx
  have hxa : (stackAnnotation? (⟨.Goto L .blockEnd, xs⟩ : StmtExprMd)).isNone = true := by simp [stackAnnotation?]
  have hd0 : blockDeclarations [(⟨.Return [e], s0⟩ : StmtExprMd)] = [] := by simp [blockDeclarations]
  have hd4 : blockDeclarations [(⟨.Block [a, ⟨.Goto L .blockEnd, xs⟩] none [] none, s4⟩ : StmtExprMd)] = [] := by
    simp [blockDeclarations]
  have hl0 : ∀ t ∈ [(⟨.Return [e], s0⟩ : StmtExprMd)], statementLabels t = [] := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    exact statementLabels_other _ _ (by intros; nofun) (by intros; nofun)
  have hl4 : ∀ t ∈ [(⟨.Block [a, ⟨.Goto L .blockEnd, xs⟩] none [] none, s4⟩ : StmtExprMd)], statementLabels t = [] := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    rw [statementLabels_block]
    simp [hla, hlx]
  have hra : (stackAnnotation? (⟨.Return [e], s0⟩ : StmtExprMd)).isNone = true := by simp [stackAnnotation?]
  have hba : (stackAnnotation? (⟨.Block [a, ⟨.Goto L .blockEnd, xs⟩] none [] none, s4⟩ : StmtExprMd)).isNone = true := by
    simp [stackAnnotation?]
  simp only [runB, evalStmt, List.forIn_nil, pure_bind, List.mapM_cons, List.mapM_nil, withBlockScope_nil hd,
    withBlockScope_nil hd0, withBlockScope_nil hd4, evalStmtList_plain hl', evalStmtList_plain hl0,
    evalStmtList_plain hl4, run_chargeStep, hs'.steps, hs'.steps', bind_assoc, pure_bind, run_tryCatch, run_bind,
    run_get, hs'.coroSelf, hs'.coroSelf', Option.isNone_none, ite_true, List.forM_eq_forM, List.forM_cons,
    List.forM_nil, run_modify, ha, run_wow_nil, hs'.ops, hs'.ops', run_withOpenLabel, hann, hxa, hra, hba] at hn ⊢
  have r0 := hexp.sim { σ with stmtSite := s0 } { σ' with openLabels := L :: σ'.openLabels, stmtSite := a.source } τ τ'
    (StRel.site (StRel.pushOL (by strel hs' : StRel {} (IxRel E) { σ with stmtSite := s0 } σ') hres) a.source) ht
  simp only [hs'.coroSelf, hs'.coroSelf', hs'.ops, hs'.ops', hs'.steps, hs'.steps'] at r0
  revert r0 hn
  generalize run (evalExprMd cfg n e) _ τ = X
  intro hn r0
  rcases X with e0 | ⟨⟨c | v, σ1⟩, τ1⟩ <;>
    revert r0 <;>
    generalize hY : run (evalExprMd cfg (M + 1) e') _ τ' = Y <;> intro r0 <;>
    rcases Y with e1 | ⟨⟨c' | v', σ1'⟩, τ1'⟩ <;> dsimp only at hn ⊢
  · first | trivial | exact r0 not_OOF_error
  · first | exact RR.ofStuck (r0 not_OOF_error) _ | exact RV.ofStuck (r0 not_OOF_error) _ | exact r0 not_OOF_error
  · first | exact RR.ofStuck (r0 not_OOF_error) _ | exact RV.ofStuck (r0 not_OOF_error) _ | exact r0 not_OOF_error
  · have hn0 : ¬ OOF (Except.ok ((Except.error c, σ1), τ1) : R Value) := by
      rw [OOF_err]; rintro rfl; exact hn (by simp [run_throw, OOF])
    exact absurd (r0 hn0) (by simp [RR])
  · have hn0 : ¬ OOF (Except.ok ((Except.error c, σ1), τ1) : R Value) := by
      rw [OOF_err]; rintro rfl; exact hn (by simp [run_throw, OOF])
    obtain ⟨hsg, ht1⟩ := r0 hn0
    obtain ⟨hcr, hok, hs1⟩ := hsg.same (fun v => Sm.noWin _ (not_free_none hvn _) v)
    have hs1' : StRel {} (IxRel E) σ1 σ1' := hs1
    have hk := (hkeep (L :: σ'.openLabels)).keep _ _ _ _ _ rfl hY
    have hs2 : StRel {} (IxRel E) σ1 { σ1' with openLabels := σ'.openLabels } := hs1'.restoreOL hk hres
    rcases hcr with rfl | ⟨L', hL', rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
    · cases c with
      | exit_ l =>
        have hne : (l == L) = false := by
          simp only [beq_eq_false_iff_ne]; rintro rfl; exact hGl hok
        simp only [hne, Bool.false_eq_true, ite_false, run_throw]
        exact ⟨.inl ⟨.inl rfl, hok, hs2⟩, ht1⟩
      | return_ w =>
        rcases w with _ | ⟨_, _ | ⟨_, _⟩⟩
        · simp only [run_throw, run_pure, RV]
          exact ⟨.inl ⟨rfl, hs2⟩, ht1⟩
        · simp only [run_throw, run_pure, RV]
          exact ⟨.inl ⟨rfl, hs2⟩, ht1⟩
        · first | exact (hok : False).elim | exact (h : False).elim | exact (hc : False).elim
      | goto_ l =>
        have hne : (l == L) = false := by
          simp only [beq_eq_false_iff_ne]; rintro rfl; exact hGl hok
        simp only [hne, Bool.false_eq_true, ite_false, run_throw]
        exact ⟨.inl ⟨.inl rfl, hok, hs2⟩, ht1⟩
      | _ =>
        simp only [run_throw, RV]
        exact ⟨.inl ⟨.inl rfl, hok, hs2⟩, ht1⟩
    · have : L' = L := Option.some.inj (hL'.symm.trans hL)
      subst this
      simp only [beq_self_eq_true, ite_true, run_modify, run_pure, RV]
      have hs3 : StRel {} (IxRel E) σ1 { σ1' with cursor := σ'.cursor, seek := none } := by strel hs1'
      exact ⟨.inl ⟨rfl, hs3.restoreOL hk hres⟩, ht1⟩
    · simp only [run_throw, RR, ExRel] at *
      exact ⟨.inl ⟨.inr (.inr ⟨_, _, rfl, rfl⟩), hok, hs2⟩, ht1⟩
  · have hn0 : ¬ OOF (Except.ok ((Except.error c, σ1), τ1) : R Value) := by
      rw [OOF_err]; rintro rfl; exact hn (by simp [run_throw, OOF])
    exact absurd (r0 hn0) (by simp [RR, ExRel])
  · exact absurd (r0 not_OOF_ok) (by simp [RR])
  · exact absurd (r0 not_OOF_ok) (by simp [RR, ExRel])
  · obtain ⟨rfl, hs1, ht1⟩ := r0 not_OOF_ok
    have hs1' : StRel {} (IxRel E) σ1 σ1' := hs1
    have hk := (hkeep (L :: σ'.openLabels)).keep _ _ _ _ _ rfl hY
    have hgl : σ1'.globals.contains o.name.text = false := hs1'.gk' _ (.inl hng)
    simp only [run_assignLocal hgl, run_wow_nil, hs1'.ops', run_bind, run_get, hk, List.contains_cons,
      beq_self_eq_true, Bool.true_or, ite_true, run_throw, run_modify, run_pure, RV]
    have hs3 : StRel {} (IxRel E) σ1 { σ1' with cursor := σ'.cursor, seek := none, stmtSite := xs } := by strel hs1'
    refine ⟨.inr ⟨v, σ1'.stack, rfl, rfl, rfl, ?_⟩, ht1⟩
    have h4 := hs3.restoreOL hk hres
    rw [← hs1'.ops'] at ⊢
    exact h4

omit [Reserved] in
/-- `tryCatch` rule for `FSV`: if `x` is simulated by `y`, the handlers `h c` and `h' c` simulate for
every signal `c` that `U` lets escape, and `h` rethrows `outOfFuel`, then `tryCatch x h` is simulated
by `tryCatch y h'`. `hm` covers a source `return` that became `exit L` for the return label `L`. `U`
must have no valued-return case (`hw`), and `h'` must treat every refusal message alike (`hrf`). -/
theorem fs_tryCatchV {S T U V : SimRel} {A : α → β → EvalState → EvalState → Prop}
    {x : EvalM PM α} {y : EvalM PM β} {h : Control → EvalM PM α} {h' : Control → EvalM PM β}
    (hx : FSV S T U A x y) (hh : ∀ c, U.ok c → FSV U T V A (h c) (h' c)) (hk : KeepsOOF h)
    (hm : ∀ L, U.ret = some L → U.ok (.return_ []) → FSV U T V A (h (.return_ [])) (h' (.exit_ L)) := by
      intro L hL; cases hL)
    (hw : ∀ v σ σ', ¬ U.win v σ σ' := by intro _ _ _ h; exact h)
    (hrf : RefFree h' := by
      intro _ _ _ _; first
        | (simp [reRef, run_bind, run_modify, run_throw, run_get, run_pure]; done)
        | (rw [run_escapeSig_other (fun _ h => by cases h), run_escapeSig_other (fun _ h => by cases h)]; rfl)) :
    FSV S T V A (tryCatch x h) (tryCatch y h') := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have h0 := hx.sim σ σ' τ τ' hs ht (not_oof_tryCatch hk hn)
  simp only [run_tryCatch] at hn ⊢
  rcases r : run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;>
    rcases r' : run y σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;> rw [r, r'] at h0 <;> rw [r] at hn
  all_goals try (exact RV.ofStuck h0 _)
  all_goals simp only [RV] at h0 ⊢
  stuck_close
  · obtain ⟨hsg, ht1⟩ := h0
    obtain ⟨hcr, hok, hs1⟩ := hsg.same (hw · σ1 σ1')
    rcases hcr with rfl | ⟨L, hL, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
    · exact (hh c hok).sim σ1 σ1' τ1 τ1' hs1 ht1 hn
    · exact (hm L hL hok).sim σ1 σ1' τ1 τ1' hs1 ht1 hn
    · rw [hrf _ _ σ1' τ1']
      exact RV.reRef _ ((hh _ hok).sim σ1 σ1' τ1 τ1' hs1 ht1 hn)
  · exact h0

omit [Reserved] in
theorem fs_tryCatchVW {S T U V : SimRel} {A : α → β → EvalState → EvalState → Prop}
    {x : EvalM PM α} {y : EvalM PM β} {h : Control → EvalM PM α} {h' : Control → EvalM PM β}
    (hx : FSV S T U A x y) (hh : ∀ c, U.ok c → FSV U T V A (h c) (h' c)) (hk : KeepsOOF h)
    (hm : ∀ L, U.ret = some L → U.ok (.return_ []) → FSV U T V A (h (.return_ [])) (h' (.exit_ L)))
    (hwin : ∀ v, FSV (U.atWin v) T V A (h (.return_ [v])) (h' (.return_ [])))
    (hrf : RefFree h' := by
      intro _ _ _ _; first
        | (simp [reRef, run_bind, run_modify, run_throw, run_get, run_pure]; done)
        | (rw [run_escapeSig_other (fun _ h => by cases h), run_escapeSig_other (fun _ h => by cases h)]; rfl)) :
    FSV S T V A (tryCatch x h) (tryCatch y h') := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have h0 := hx.sim σ σ' τ τ' hs ht (not_oof_tryCatch hk hn)
  simp only [run_tryCatch] at hn ⊢
  rcases r : run x σ τ with e | ⟨⟨c | a, σ1⟩, τ1⟩ <;>
    rcases r' : run y σ' τ' with e' | ⟨⟨c' | b, σ1'⟩, τ1'⟩ <;> rw [r, r'] at h0 <;> rw [r] at hn
  all_goals try (exact RV.ofStuck h0 _)
  all_goals simp only [RV] at h0 ⊢
  stuck_close
  · obtain ⟨hsg, ht1⟩ := h0
    rcases hsg with ⟨hcr, hok, hs1⟩ | ⟨v, rfl, rfl, hw1⟩
    · rcases hcr with rfl | ⟨L, hL, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
      · exact (hh c hok).sim σ1 σ1' τ1 τ1' hs1 ht1 hn
      · exact (hm L hL hok).sim σ1 σ1' τ1 τ1' hs1 ht1 hn
      · rw [hrf _ _ σ1' τ1']
        exact RV.reRef _ ((hh _ hok).sim σ1 σ1' τ1 τ1' hs1 ht1 hn)
    · exact (hwin v).sim σ1 σ1' τ1 τ1' hw1 ht1 hn
  · exact h0

omit [Reserved] in
/-- The end of a procedure call that returned the value `v` can be replaced by the end of a call that
returned nothing but holds `v` in its single output `o`. If `x` is simulated by `procTail` with
`returned = some v`, then, from a source state `σ0` and a target state `σ0'` whose stack is `s0` with
`o` set to `v`, where `σ0` is related to `σ0'` with stack `s0`, `x` is simulated by `procTail` with
`returned = none`. `proc` has exactly one output with the name of `o`, and restoring the caller's
state ignores the current stack. -/
theorem procTail_ofAt {S T U : SimRel} {A : α → Array Value → Prop} {x : EvalM PM α} {cfg : ExternalBackendM PM}
    {f : Nat} {proc : Procedure} {o o' : Parameter} (ho : proc.outputs = [o']) (hn : o'.name.text = o.name.text)
    {outs : List Parameter}
    (hos : outs = [o]) {ps : List Condition} {fr : List ModifiesGroup} {sk : Bool}
    {cs : StackFrame} {ent : Array HeapObject × Std.HashMap String Value} {g : EvalState → EvalState}
    (hg : ∀ σ s, g { σ with stack := s } = g σ) {v : Value} {σ0 σ0' : EvalState} {s0 : StackFrame}
    (h : FSH S T U A x (procTail cfg f proc ps fr sk cs ent (modify g) outs (some v)))
    (hs : S.st σ0 { σ0' with stack := s0 }) (hstk : σ0'.stack = s0.insert o.name.text v) :
    FSH (At S σ0 σ0') T U A x (procTail cfg f proc ps fr sk cs ent (modify g) outs none) := by
  refine FSH.ofAt h hs (fun τ' => ?_)
  have e : σ0' = { σ0' with stack := s0.insert o.name.text v } := by rw [← hstk]
  rw [e, procTail_valued cfg f ho hn hos ps fr sk cs ent hg]

end

end Strata.Laurel.PassSemantics
