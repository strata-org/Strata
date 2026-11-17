/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.JumpScope

/-!
# A statement list lands the jumps to its own blocks

A statement list run outside a coroutine body catches every `jump_` to a label one of its
statements holds and carries on from that statement, so such a `jump_` never leaves the list.
`landFree_block`: a `jump_` that leaves a block with no invariants and no decreases clause,
run outside a coroutine body, is to none of the labels the block holds (`statementLabels`): the
block's own label is open while it runs (`jkAt`), and its statement list lands the others. A
jump back to the start of a labelled block runs its list again, still outside a coroutine body
(`cnAt`).

`LandFree S x` says that a `jump_` `x` returns, started outside a coroutine body, is to no label
in `S`.
-/

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

/-- The statement-position labels the statements of a list hold. -/
def flatLabels (ss : List StmtExprMd) : List String := (ss.map statementLabels).flatten

/-- A `jump_` that `x` returns, started outside a coroutine body, is to no label in `S`. -/
def LandFree (S : List String) (x : EvalM PM α) : Prop :=
  ∀ σ τ l d σ1 τ1, σ.coroSelf = none → run x σ τ = .ok ((.error (.jump_ l d), σ1), τ1) → l ∉ S

theorem LandFree.ofNoJ {S : List String} {x : EvalM PM α} (h : NoJ x) : LandFree S x :=
  fun _ _ _ _ _ _ _ hr => absurd hr (h _ _ _ _ _ _)

theorem LandFree.throw {S : List String} {c : Control} (hc : ∀ l d, c = .jump_ l d → l ∉ S) :
    LandFree S (throw c : EvalM PM α) := by
  intro σ τ l d σ1 τ1 _ h
  rw [run_throw] at h
  simp only [Except.ok.injEq, Prod.mk.injEq, Except.error.injEq] at h
  exact hc l d h.1.1

theorem LandFree.bind {S : List String} {x : EvalM PM α} {f : α → EvalM PM β} (hx : LandFree S x) (hxc : CN x)
    (hf : ∀ a, LandFree S (f a)) : LandFree S (x >>= f) := by
  intro σ τ l d σ1 τ1 hσ h
  rw [run_bind] at h
  rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at h
  · cases h
  · simp only [Except.ok.injEq, Prod.mk.injEq, Except.error.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact hx _ _ _ _ _ _ hσ hr
  · exact hf a _ _ _ _ _ _ (hxc.keep _ _ _ _ _ hσ hr) h

theorem LandFree.getBind {S : List String} {f : EvalState → EvalM PM β}
    (hf : ∀ s, s.coroSelf = none → LandFree S (f s)) : LandFree S (MonadState.get >>= f) := by
  intro σ τ l d σ1 τ1 hσ h
  rw [run_bind, run_get] at h
  exact hf σ hσ _ _ _ _ _ _ hσ h

/-- The signals `tryCatch x h` returns come from its handler. -/
theorem LandFree.tryCatch {S : List String} {x : EvalM PM α} {h : Control → EvalM PM α} (hxc : CN x)
    (hh : ∀ c, LandFree S (h c)) : LandFree S (MonadExcept.tryCatch x h) := by
  intro σ τ l d σ1 τ1 hσ he
  rw [run_tryCatch] at he
  rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at he
  · cases he
  · exact hh c _ _ _ _ _ _ (hxc.keep _ _ _ _ _ hσ hr) he
  · cases he

/-- `tryCatch` whose handler rethrows the signals the body returns: a `jump_` the handler returns on a signal
of the body that is a `jump_` to no label in `S` is to no label in `S`. -/
theorem LandFree.tryCatchR {S : List String} {x : EvalM PM α} {h : Control → EvalM PM α} (hx : LandFree S x)
    (hxc : CN x) (hh : ∀ c, (∀ l d, c = .jump_ l d → l ∉ S) → LandFree S (h c)) :
    LandFree S (MonadExcept.tryCatch x h) := by
  intro σ τ l d σ1 τ1 hσ he
  rw [run_tryCatch] at he
  rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at he
  · cases he
  · exact hh c (fun l' d' e => hx _ _ _ _ _ _ hσ (e ▸ hr)) _ _ _ _ _ _ (hxc.keep _ _ _ _ _ hσ hr) he
  · cases he

theorem not_mem_flatLabels_of_findIdx {ss : List StmtExprMd} {l : String}
    (h : ss.findIdx? (fun t => (statementLabels t).contains l) = none) : l ∉ flatLabels ss := by
  rw [List.findIdx?_eq_none_iff] at h
  simp only [flatLabels, List.mem_flatten, List.mem_map, not_exists, not_and]
  rintro _ ⟨t, ht, rfl⟩ hl
  have := h t ht
  simp [hl] at this

/-- A labelled block's run lets out no `jump_` to its own label, which is open while it runs, nor, if its
statements let none out, to theirs. -/
theorem LandFree.withOpenLabel {S : List String} {X : String} {x : EvalM PM α} (h1 : LandFree S x)
    (h2 : KeepsJK x) : LandFree (X :: S) (withOpenLabel X x) := by
  intro σ τ l d σ1 τ1 hσ h
  rw [run_withOpenLabel] at h
  rcases hr : run x { σ with openLabels := X :: σ.openLabels } τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at h
  · cases h
  · simp only [Except.ok.injEq, Prod.mk.injEq, Except.error.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    have a := h1 { σ with openLabels := X :: σ.openLabels } _ _ _ _ _ hσ hr
    have b := (h2 (X :: σ.openLabels)).nj _ _ _ _ _ _ rfl hr
    simp only [List.mem_cons, not_or] at b ⊢
    exact ⟨b.1, a⟩
  · cases h

theorem noJ_chargeStep : NoJ (chargeStep : EvalM PM Unit) := by
  unfold chargeStep
  refine NoJ.getBind (fun s => ?_)
  split
  · exact NoJ.pure _
  · exact NoJ.throw (fun _ _ h => by cases h)
  · exact NoJ.modify _

theorem LandFree.withBlockScope {S : List String} {l : List StmtExprMd} {x : EvalM PM α} (hx : LandFree S x)
    (hxc : CN x) : LandFree S (Interpreter.withBlockScope l x) := by
  unfold Interpreter.withBlockScope
  dsimp only
  split
  · exact hx
  · refine LandFree.getBind (fun st hst => ?_)
    simp only [hst, Option.isSome_none, Bool.false_eq_true, ite_false]
    refine LandFree.bind (LandFree.tryCatchR hx hxc (fun c hc => ?_)) ?_ (fun r => LandFree.ofNoJ ?_)
    · split
      · exact LandFree.throw hc
      · exact LandFree.bind (LandFree.ofNoJ (NoJ.modify _)) (CN.modify (fun σ hσ => hσ)) (fun _ => LandFree.throw hc)
    · refine CN.tryCatch hxc (fun c => ?_)
      split
      · exact CN.throw _
      · exact CN.bind (CN.modify (fun σ hσ => hσ)) (fun _ => CN.throw _)
    · exact NoJ.bind (NoJ.modify _) (fun _ => NoJ.pure _)

theorem LandFree.withOperandWindow {S : List String} {t : StmtExprMd} {x : EvalM PM α} (hx : LandFree S x)
    (hxc : CN x) : LandFree S (Interpreter.withOperandWindow t x) := by
  unfold Interpreter.withOperandWindow
  refine LandFree.getBind (fun st hst => ?_)
  split
  · exact hx
  · simp (config := { zeta := true }) only []
    split
    · exact hx
    · split
      · refine LandFree.bind (LandFree.ofNoJ (NoJ.evalError _)) (cn_evalError _) (fun _ => ?_)
        refine LandFree.bind (LandFree.ofNoJ (NoJ.set _)) (CN.set _ hst) (fun _ => ?_)
        refine LandFree.bind (LandFree.tryCatchR hx hxc (fun c hc => ?_)) ?_
          (fun _ => LandFree.ofNoJ (NoJ.bind (NoJ.modify _) (fun _ => NoJ.pure _)))
        · exact LandFree.bind (LandFree.ofNoJ (NoJ.modify _)) (CN.modify (fun σ hσ => hσ)) (fun _ => LandFree.throw hc)
        · exact CN.tryCatch hxc (fun _ => CN.bind (CN.modify (fun σ hσ => hσ)) (fun _ => CN.throw _))
      · refine LandFree.bind (LandFree.ofNoJ (NoJ.set _)) (CN.set _ hst) (fun _ => ?_)
        refine LandFree.bind (LandFree.tryCatchR hx hxc (fun c hc => ?_)) ?_
          (fun _ => LandFree.ofNoJ (NoJ.bind (NoJ.modify _) (fun _ => NoJ.pure _)))
        · exact LandFree.bind (LandFree.ofNoJ (NoJ.modify _)) (CN.modify (fun σ hσ => hσ)) (fun _ => LandFree.throw hc)
        · exact CN.tryCatch hxc (fun _ => CN.bind (CN.modify (fun σ hσ => hσ)) (fun _ => CN.throw _))

/-- `x` run from `σ` never returns a `jump_`. -/
def NoJAt (x : EvalM PM α) (σ : EvalState) : Prop :=
  ∀ τ l d σ1 τ1, run x σ τ ≠ .ok ((.error (.jump_ l d), σ1), τ1)

theorem NoJAt.ofNoJ {x : EvalM PM α} {σ : EvalState} (h : NoJ x) : NoJAt x σ := fun _ _ _ _ _ => h _ _ _ _ _ _

theorem NoJAt.bind {x : EvalM PM α} {f : α → EvalM PM β} {σ : EvalState} (hx : NoJAt x σ)
    (hf : ∀ τ a σ1 τ1, run x σ τ = .ok ((.ok a, σ1), τ1) → NoJAt (f a) σ1) : NoJAt (x >>= f) σ := by
  intro τ l d σ1 τ1 h
  rw [run_bind] at h
  rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at h
  · cases h
  · simp only [Except.ok.injEq, Prod.mk.injEq, Except.error.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact hx _ _ _ _ _ hr
  · exact hf τ a σ2 τ2 hr _ _ _ _ _ h

theorem NoJAt.tryCatch {x : EvalM PM α} {h : Control → EvalM PM α} {σ : EvalState} (hx : NoJAt x σ)
    (hh : ∀ c, NotJump c → NoJ (h c)) : NoJAt (MonadExcept.tryCatch x h) σ := by
  intro τ l d σ1 τ1 he
  rw [run_tryCatch] at he
  rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at he
  · cases he
  · exact hh c (fun l' d' hc => hx _ _ _ _ _ (hc ▸ hr)) _ _ _ _ _ _ he
  · cases he

/-- An operand window around an action that returns no `jump_` from any state with the open labels and
coroutine position of `σ` returns none from `σ`: the window only moves operands. -/
theorem NoJAt.withOperandWindow {t : StmtExprMd} {x : EvalM PM α} {σ : EvalState}
    (hx : ∀ σ', σ'.openLabels = σ.openLabels → σ'.coroSelf = σ.coroSelf → NoJAt x σ') :
    NoJAt (Interpreter.withOperandWindow t x) σ := by
  unfold Interpreter.withOperandWindow
  refine NoJAt.bind (NoJAt.ofNoJ NoJ.get) (fun τ a σ1 τ1 h => ?_)
  rw [run_get] at h
  cases h
  split
  · exact hx σ rfl rfl
  · simp (config := { zeta := true }) only []
    split
    · exact hx σ rfl rfl
    · split
      · refine NoJAt.bind (NoJAt.ofNoJ (NoJ.evalError _)) (fun τ' u σ2 τ2 h' => absurd h' ?_)
        obtain ⟨m, hm⟩ := run_evalError (α := PUnit) "this reads more stack values than were pushed" σ τ'
        rw [hm]
        nofun
      · refine NoJAt.bind (NoJAt.ofNoJ (NoJ.set _)) (fun τ u σ2 τ2 h => ?_)
        cases h
        exact NoJAt.bind (NoJAt.tryCatch (hx _ rfl rfl) (fun c hc => NoJ.bind (NoJ.modify _) (fun _ => NoJ.throw hc)))
          (fun _ _ _ _ _ => NoJAt.ofNoJ (NoJ.bind (NoJ.modify _) (fun _ => NoJ.pure _)))

variable (cfg : ExternalBackendM PM)

/-- An expression evaluation never lets a `jump_` out: it is a jump boundary. -/
theorem noJ_evalExprMd (m : Nat) (e : StmtExprMd) : NoJ (evalExprMd cfg m e) := by
  cases m with
  | zero => rw [evalExprMd]; exact NoJ.throw (fun _ _ h => by cases h)
  | succ m => rw [evalExprMd]; exact noJ_jumpBoundary _

/-- A call never lets a `jump_` out: it is a jump boundary. -/
theorem noJ_invokeProc (m : Nat) (site : FileRange) (P : Procedure) (args : List Value) (top : Bool) :
    NoJ (invokeProc cfg m site P args top) := by
  cases m with
  | zero => rw [invokeProc]; exact NoJ.throw (fun _ _ h => by cases h)
  | succ m => rw [invokeProc]; exact noJ_jumpBoundary _

/-- A `jump_` that leaves `runFrom` is to no label its statements hold: its handler lands those. -/
theorem landFree_runFrom : ∀ (m : Nat) (ss : List StmtExprMd) (k : Nat) (l : String) (d : GotoDestination),
    LandFree (flatLabels ss) (runFrom cfg m ss k l d)
  | 0, ss, k, l, d => by
    rw [runFrom]
    exact LandFree.throw (fun _ _ h => by cases h)
  | m + 1, ss, k, l, d => by
    have ih := cnAt cfg m
    rw [runFrom]
    refine LandFree.bind (LandFree.tryCatch (by cn_tac) (fun c => ?_)) (by cn_tac) (fun r => ?_)
    · split
      · split
        · exact LandFree.ofNoJ (NoJ.pure _)
        · exact LandFree.throw (fun l' d' h => by
            cases h
            exact not_mem_flatLabels_of_findIdx ‹_›)
      · next _ hne => exact LandFree.throw (fun l' d' h => (hne l' d' h).elim)
    · split
      · exact LandFree.ofNoJ (NoJ.pure _)
      · exact LandFree.bind (LandFree.ofNoJ noJ_chargeStep) cn_chargeStep (fun _ => landFree_runFrom m ss _ _ _)

/-- A `jump_` that leaves a statement list run as statements outside a coroutine body is to no label its
statements hold. -/
theorem landFree_list : ∀ (m : Nat) (ss : List StmtExprMd), LandFree (flatLabels ss) (evalStmtList cfg m ss false)
  | 0, ss => by
    rw [evalStmtList]
    exact LandFree.throw (fun _ _ h => by cases h)
  | m + 1, ss => by
    have ih := cnAt cfg m
    rw [evalStmtList]
    refine LandFree.getBind (fun st hst => ?_)
    simp only [hst, Option.isNone_none, ite_true, Bool.false_eq_true, ite_false]
    refine LandFree.bind (LandFree.tryCatch (by cn_tac) (fun c => ?_)) (by cn_tac) (fun r => ?_)
    · split
      · split
        · exact LandFree.ofNoJ (NoJ.pure _)
        · exact LandFree.throw (fun l' d' h => by
            cases h
            exact not_mem_flatLabels_of_findIdx ‹_›)
      · next _ hne => exact LandFree.throw (fun l' d' h => (hne l' d' h).elim)
    · split
      · exact LandFree.ofNoJ (NoJ.pure _)
      · exact LandFree.bind (LandFree.ofNoJ noJ_chargeStep) cn_chargeStep (fun _ =>
          LandFree.bind (landFree_runFrom cfg m ss _ _ _) (ih.runFrom _ _ _ _) (fun _ => LandFree.ofNoJ (NoJ.pure _)))

/-- The statements of a labelled block and its handler for the signals that leave or restart it. -/
theorem landFree_arm {m : Nat} {ss : List StmtExprMd} {lab : String} {base : List Nat}
    (hloop : LandFree (flatLabels ss) (evalBlockLoop cfg m ss lab [] base)) :
    LandFree (flatLabels ss) (MonadExcept.tryCatch
      (do let _ ← Interpreter.withBlockScope ss (evalStmtList cfg m ss (asExpr := false)); pure ())
      (fun (c : Control) => match c with
        | .exit_ l =>
            if l == lab then
              modify fun (s : EvalState) => { s with cursor := base, seek := none }
            else throw (.exit_ l)
        | .goto_ l =>
            if l == lab then do
              modify fun (s : EvalState) => { s with cursor := base, seek := none }
              chargeStep
              evalBlockLoop cfg m ss lab [] base
            else throw (.goto_ l)
        | other => throw other : Control → EvalM PM Unit)) := by
  have ih := cnAt cfg m
  have hl : CN (Interpreter.withBlockScope ss (evalStmtList cfg m ss false)) := CN.withBlockScope (ih.list ss false)
  refine LandFree.tryCatchR (LandFree.bind (LandFree.withBlockScope (landFree_list cfg m ss) (ih.list ss false)) hl
    (fun _ => LandFree.ofNoJ (NoJ.pure _))) (CN.bind hl (fun _ => CN.pure _)) (fun c hc => ?_)
  cases c with
  | exit_ l =>
    dsimp only
    split
    · exact LandFree.ofNoJ (NoJ.modify _)
    · exact LandFree.throw (fun _ _ h => by cases h)
  | goto_ l =>
    dsimp only
    split
    · exact LandFree.bind (LandFree.ofNoJ (NoJ.modify _)) (CN.modify (fun σ hσ => hσ)) (fun _ =>
        LandFree.bind (LandFree.ofNoJ noJ_chargeStep) cn_chargeStep (fun _ => hloop))
    · exact LandFree.throw (fun _ _ h => by cases h)
  | _ => exact LandFree.throw hc

/-- A `jump_` that leaves a labelled block's loop is to no label its statements hold. -/
theorem landFree_blockLoop : ∀ (m : Nat) (ss : List StmtExprMd) (lab : String) (base : List Nat),
    LandFree (flatLabels ss) (evalBlockLoop cfg m ss lab [] base)
  | 0, ss, lab, base => by
    rw [evalBlockLoop]
    exact LandFree.throw (fun _ _ h => by cases h)
  | m + 1, ss, lab, base => by
    rw [evalBlockLoop]
    simp only [List.forIn_nil, pure_bind]
    exact landFree_arm cfg (landFree_blockLoop m ss lab base)

/-- A `jump_` that leaves a block with no invariants and no decreases clause, run outside a coroutine body, is
to none of the labels the block holds. -/
theorem landFree_block (m : Nat) (ss : List StmtExprMd) (lab : Option String) (src : FileRange) :
    LandFree (statementLabels ⟨.Block ss lab [] none, src⟩) (evalStmt cfg (m + 1) ⟨.Block ss lab [] none, src⟩) := by
  have ih := cnAt cfg m
  rw [statementLabels_block]
  cases lab with
  | none =>
    simp only [Option.toList_none, List.nil_append]
    rw [evalStmt]
    exact LandFree.bind (LandFree.ofNoJ noJ_chargeStep) cn_chargeStep (fun _ =>
      LandFree.bind (LandFree.withBlockScope (landFree_list cfg m ss) (ih.list ss false))
        (CN.withBlockScope (ih.list ss false)) (fun _ => LandFree.ofNoJ (NoJ.pure _)))
  | some X =>
    simp only [Option.toList_some, List.singleton_append]
    rw [evalStmt]
    refine LandFree.getBind (fun s _ => ?_)
    refine LandFree.withOpenLabel ?_ ?_
    · simp only [List.forIn_nil, pure_bind]
      exact landFree_arm cfg (landFree_blockLoop cfg m ss X s.cursor)
    · intro o
      have ih := jkAt cfg m
      jk_tac

theorem findIdx_none_of_not_mem {ss : List StmtExprMd} {l : String} (h : l ∉ flatLabels ss) :
    ss.findIdx? (fun t => (statementLabels t).contains l) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro t ht
  cases hc : (statementLabels t).contains l
  · rfl
  · exact absurd (by simp only [flatLabels, List.mem_flatten, List.mem_map]; exact ⟨_, ⟨t, ht, rfl⟩,
      List.contains_iff_mem.mp hc⟩) h

/-- A statement list run outside a coroutine body whose statements, run one after the other, return no `jump_`
to a label they hold, runs as those statements: its handler for jumps only rethrows. -/
theorem run_evalStmtList_noLand {m : Nat} {ss : List StmtExprMd} {σ : EvalState} {τ : Trace}
    (hco : σ.coroSelf = none)
    (hF : ∀ l d σ1 τ1, run (ss.forM fun s => do
        modify fun (st : EvalState) => { st with stmtSite := s.source }
        if (stackAnnotation? s).isNone then withOperandWindow s (evalStmt cfg m s)) σ τ =
          .ok ((.error (.jump_ l d), σ1), τ1) → l ∉ flatLabels ss) :
    run (evalStmtList cfg (m + 1) ss false) σ τ =
      run ((ss.forM fun s => do
        modify fun (st : EvalState) => { st with stmtSite := s.source }
        if (stackAnnotation? s).isNone then withOperandWindow s (evalStmt cfg m s)) >>= fun _ => pure default) σ τ := by
  rw [evalStmtList, run_bind, run_get]
  simp only [hco, Option.isNone_none, ite_true, Bool.false_eq_true, ite_false]
  rw [run_bind, run_tryCatch, run_bind, run_bind]
  revert hF
  rcases run (ss.forM fun s => do
        modify fun (st : EvalState) => { st with stmtSite := s.source }
        if (stackAnnotation? s).isNone then withOperandWindow s (evalStmt cfg m s)) σ τ with
    e | ⟨⟨c | u, σ1⟩, τ1⟩ <;> intro hF
  · rfl
  · cases c
    case jump_ l d =>
      dsimp only
      rw [findIdx_none_of_not_mem (hF l d σ1 τ1 rfl), run_throw]
    all_goals rfl
  · rfl

end Strata.Laurel.PassSemantics
