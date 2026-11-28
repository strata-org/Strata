/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.ValuationToRunSupport
public import Strata.Languages.Core.InterpreterReplayProps
public import Strata.Languages.Core.Counterexample.ValuationToRunProducer
public import Strata.DL.Lambda.LStateProps
import all Strata.Languages.Core.InterpreterReplay
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Imperative.Counterexample.Valuation
import all Strata.Languages.Core.Counterexample.ValuationToRunProducer
import all Strata.Languages.Core.Counterexample.ValuationToRunSupport
import Strata.Languages.Core.Counterexample.BackLinkPhasesProps
public import Strata.Languages.Core.Counterexample.ValuationToRunDriveA
import all Strata.Languages.Core.Counterexample.ValuationToRunDriveA
import Strata.DL.Imperative.Counterexample.Tactics
import all Strata.DL.Lambda.LExprEvalFuelProps
import Strata.Languages.Core.ObligationExtractionProps

/-! # ValuationToRunDrive, continued from `ValuationToRunDriveA`

The reachability drive of the `(b)→(a)` counterexample lift: replaying a passive obligation
program from the environment and oracle reconstructed from a level-`(b)` counterexample
records the obligation's target event, and the `(b)→(a)` producer is valid.

Key definitions:
- `targetEvent`: the event the target statement of an obligation emits, by kind.
- `EventsAreThePathResolved`: the replay at fuel `f + fb` records an event that fires
  `assertFailureHalt` for the target.

Key theorems:
- `eventsAreThePathResolved_holds`: `EventsAreThePathResolved` holds for every obligation.
- `reconstructAssertionFromCexValuation_satisfies_valid_full`: the `(b)→(a)` producer
  `reconstructAssertionFromCexValuation` satisfies the all-counterexample contract
  `ValuationToRunBackLinkValid`.
- `reconstructAssertionFromCexValuation_valid_of_cex`: the producer's outcome is valid for one
  counterexample whose model binds the obligation's reads.
-/

namespace Core
open Imperative
open BackLinkOutcome

public section

variable {d : Nat}

/-! ### Block runs preserve the inner run's trace

Running `.block l frame inner` steps `inner` at the block's current fuel and re-wraps the
result under the frame extended by the inner step's recorded names, and the terminal/exiting
exit step leaves `ReplayState` (hence `traceRev`) untouched, so the block run records exactly
the `traceRev` of the standalone `inner` run at the same fuel, for every frame. -/

/-- One `stepInterp` on a block whose inner is non-terminal/non-exiting steps the
    inner at the block's fuel and re-wraps it under the frame extended by the inner
    configuration's recorded names (`frame.record inner.levelCmd?`). -/
private theorem stepInterp_block_reduce (π : String → Option Procedure) (fuel : Nat)
    (l : Option String) (frame : ScopeFrame Expression)
    (X : IConfig Expression Command)
    (hnt1 : ∀ e, X ≠ .terminal e) (hnt2 : ∀ le e, X ≠ .exiting le e) :
    (stepInterp (replayStepCmd π d) fuel (.block l frame X) : ReplayM Expression (IConfig Expression
        Command))
      = stepInterp (replayStepCmd π d) fuel X >>= fun i =>
          pure (.block l (frame.record X.levelCmd?) i) :=
  stepInterp_block_unfold_gen _ _ _ _ _ hnt1 hnt2

/-- Running `.block l frame inner` records the same final `traceRev` as running `inner`,
    at every fuel and for every frame. -/
private theorem run_block_traceRev_eq (π : String → Option Procedure) (l : Option String) :
    ∀ (F : Nat) (inner : IConfig Expression Command) (frame : ScopeFrame Expression)
      (cfg : ReplayCfg Expression) (st : ReplayState Expression),
      (rrun (runInterp (replayStepCmd π d) F (.block l frame inner)) cfg st).2.traceRev
        = (rrun (runInterp (replayStepCmd π d) F inner) cfg st).2.traceRev := by
  intro F
  induction F <;> intro inner frame cfg st
  case zero => cases inner <;> rfl
  case succ F ih =>
    cases inner
    case terminal | exiting =>
      cases F <;> simp only [runInterp, stepInterp] <;> (try split) <;> rfl
    all_goals
      rw [runInterp_succ_block, stepInterp_block_reduce π _ _ _ _ (by simp) (by simp)]
      simp only [runInterp, rrun, bind_assoc, pure_bind, replayM_run_bind]
      split <;> simp only [ih, rrun]

/-- **`init` fold witness.**  For a det-`init` `name := ev0` at `pre ++ · :: suf` in the
    `evalBounded fb` fold producing `threaded`, with `name` and `ev0`'s reads not re-declared in
    `suf`, `name` not read by `ev0`, and the run store `σRun` agreeing with `threaded` on `ev0`'s
    free vars: at any fuel `≥ fb` the run evaluates `ev0` to a well-typed value `v`, the value
    `threaded` binds `name` to. -/
private theorem init_fold_witness
    (factory : @Lambda.Factory CoreLParams)
    (hWF : Lambda.FactoryWF factory)
    (fb F' : Nat) (hfbF : fb ≤ F' + 2)
    (name : CoreIdent) (ty : Expression.Ty) (ev0 : Expression.Expr)
    (pre suf : Imperative.PathCondition Expression)
    (store threaded σRun : RStore Expression)
    (hfold : Imperative.extendWithVarDecls' (P := Expression)
        (.runtime (evalBounded fb)) factory store
        (pre ++ Imperative.PathConditionEntry.varDecl name ty (.det ev0) :: suf) = some threaded)
    (hnotsuf : ∀ ty'' e'', Imperative.PathConditionEntry.varDecl name ty'' (.det e'') ∉ suf)
    (hnameNotFvar : name ∉ HasFvars.getFvars (P := Expression) ev0)
    (hfvarNotSuf : ∀ x ∈ HasFvars.getFvars (P := Expression) ev0, ∀ t e,
        Imperative.PathConditionEntry.varDecl x t (.det e) ∉ suf)
    (hwfRun : RWellFormedStore σRun factory)
    (hmatch : ∀ x ∈ HasFvars.getFvars (P := Expression) ev0, ∀ w,
        threaded x = some w → σRun x = some w) :
    ∃ v, evalBounded (F' + 2) factory σRun ev0 = some v
      ∧ ((InterpLang.ops (P := Expression)).isValue factory v
          && (InterpLang.ops (P := Expression)).hasType factory v ty) = true
      ∧ (∀ w, threaded name = some w → w = v)
      ∧ threaded name = some v := by
  obtain ⟨dpre, v, -, heval, hvalTy, hname, hsuf⟩ :=
    scope_det_value_gen _ _ _ _ _ _ _ _ _ hfold hnotsuf
  have hmatchPre : ∀ x ∈ HasFvars.getFvars ev0, ∀ w, dpre x = some w → σRun x = some w :=
    fun x hx w h => hmatch x hx w (by
      rw [extendWithVarDecls'_frame_gen _ _ _ _ _ _ hsuf (hfvarNotSuf x hx)]
      simpa [RStore.update, show x ≠ name from fun hEq => hnameNotFvar (hEq ▸ hx)])
  exact ⟨v, cel_agreeEval hWF hfbF hwfRun hmatchPre heval, hvalTy, by simp [hname], hname⟩

/-- **nondet-`ite` lift.**  Any property `Q` of the final `traceRev` of the selected arm
    block's run at fuel `F`, from the state after the oracle pops the branch Boolean, holds of
    the final `traceRev` of the run of the sole nondet-`ite` `.stmts [ite] env` at `F + 2`,
    when the oracle head is the Boolean selecting that arm (the two traces are equal). -/
private theorem driveRecords_ite_lift_pred (Q : List (IEvent Expression) → Prop) (b : Bool)
    (thenSs elseSs : List (Stmt Expression Command)) (md : Imperative.MetaData Expression)
    (env : IEnv Expression) (cfg : ReplayCfg Expression) (st : ReplayState Expression)
    (F : Nat) (rest : List Expression.Expr)
    (hrem : st.remaining = (if b then HasBool.tt (P := Expression) else HasBool.ff (P :=
        Expression)) :: rest)
    (hval : ((InterpLang.ops (P := Expression)).isValue env.factory
              (if b then HasBool.tt (P := Expression) else HasBool.ff (P := Expression))
            && (InterpLang.ops (P := Expression)).hasType env.factory
              (if b then HasBool.tt (P := Expression) else HasBool.ff (P := Expression))
              (HasBool.boolTy (P := Expression))) = true)
    (hinner : Q (rrun (runInterp (replayStepCmd (fun _ => none) d) F
        (.block .none (.opened env.store) (.stmts (if b then thenSs else elseSs) env)))
        cfg { st with
          remaining := rest
          usedRev := (if b then HasBool.tt (P := Expression) else HasBool.ff (P := Expression)) ::
            st.usedRev }).2.traceRev) :
    Q (rrun (runInterp (replayStepCmd (fun _ => none) d) (F + 2)
        (.stmts [.ite .nondet thenSs elseSs md] env)) cfg st).2.traceRev := by
  have hseqs : ∀ (F : Nat) (inner : IConfig Expression Command) (k : Nat)
      (st : ReplayState Expression),
      (rrun (runInterp (replayStepCmd (fun _ => none) d) F (.seqs inner k)) cfg st).2.traceRev
        = (rrun (runInterp (replayStepCmd (fun _ => none) d) F inner) cfg st).2.traceRev := by
    intro F
    induction F <;> intro inner k st
    case zero => cases inner <;> rfl
    case succ F ih =>
      rw [runInterp_succ_nonterminal (P := Expression) _ _ (.seqs inner k) (by simp) (by simp)]
      cases inner
      case terminal e =>
        cases k <;> simp only [stepInterp, pure_bind, ih, runInterp_terminal] <;>
          cases F <;> simp only [runInterp, stepInterp, pure_bind] <;> rfl
      case exiting l e =>
        cases k <;> simp only [stepInterp, pure_bind, ih, runInterp_exiting] <;>
          cases F <;> simp only [runInterp, stepInterp, pure_bind] <;> rfl
      all_goals
        rw [runInterp_succ_nonterminal (P := Expression) _ _ _ (by simp) (by simp)]
        conv => lhs; rw [stepInterp.eq_def (P := Expression)]
        dsimp only
        simp only [rrun, bind_assoc]
        rw [replayM_run_bind (P := Expression), replayM_run_bind (P := Expression)]
        split
        · rename_i a st' _
          cases a <;> simp only [pure_bind]
          all_goals first | exact (ih _ _ _).trans (ih _ _ _).symm | exact ih _ _ _
        · rfl
  rw [runInterp_succ_stmts, rrun_bind_ok _ _ _ _ _ _ (rfl), hseqs,
    runInterp_succ_stmt (P := Expression)]
  cases b <;> rwa [rrun_bind_ok _ _ _ _ _ _ (by
      first
        | exact step_ite_nondet_false_run _ _ _ _ _ _ _ _ _ hrem hval
        | exact step_ite_nondet_true_run _ _ _ _ _ _ _ _ _ hrem hval)]

/-- The reachability drive's **kind-indexed target event**: a cover obligation's target
    statement emits `Event.cover`; every other (assert-family) obligation emits
    `Event.assert`.  `assertFailureHalt` fires on this event's true/false literal by kind. -/
def targetEvent (obligation : ProofObligation Expression)
    (factory : @Lambda.Factory CoreLParams) (σ : RStore Expression)
    (md : Imperative.MetaData Expression) : IEvent Expression :=
  if obligation.property = Imperative.PropertyType.cover then
    REvent.cover ⟨factory, σ, obligation.label, obligation.obligation, md⟩
  else
    REvent.assert ⟨factory, σ, obligation.label, obligation.obligation, md⟩

/-- An assert-family obligation's property (from `convertMetaDataPropertyType`) is never
    `.cover`: the converter returns only `.divisionByZero`/`.arithmeticOverflow`/
    `.outOfBoundsAccess`/`.assert`. -/
private theorem convertMetaDataPropertyType_ne_cover (md : Imperative.MetaData Expression) :
    Imperative.convertMetaDataPropertyType (P := Expression) md ≠
      Imperative.PropertyType.cover := by
  grind [convertMetaDataPropertyType]

/-- **The reachability drive.**  For a step of the `extractGoLinked` walk over `ss` that
    produces the pair `(obligation, link)` (it is in the result `arr` but not in the
    accumulator `acc`), running `.stmts ss env'` at any fuel `F ≥ Block.stepBudget ss + fb`, from
    a run store that agrees with `threaded` (`StoreAgreesThreaded`) and an oracle built
    from the remaining events, records the target event followed (in `traceRev`) by a
    prefix `pre`; `pre` is path-feasible whenever the threaded assumptions hold and the
    initial trace is feasible; and the run store `σRun` at the target agrees with
    `threaded`, is defined at the goal's free vars, and is well-formed. -/
private theorem drive_walk
    (factory : @Lambda.Factory CoreLParams)
    (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink)
    (store threaded : RStore Expression) (fb : Nat)
    (hthreadFlat : Imperative.extendWithVarDecls' (P := Expression)
        (.runtime (evalBounded fb)) factory store
        obligation.assumptions.flatten = some threaded)
    (hWF : Lambda.FactoryWF factory)
    (hssaNodup : (allVarNames obligation.assumptions).Nodup)
    (hssaDisj : ∀ n ∈ allVarNames obligation.assumptions,
        n ∉ (PassiveUnit.forObligation link obligation).inputs.map (·.1))
    (hmb : ModelBinds link obligation factory store)
    (Ftop : Nat) (hFtop : fb ≤ Ftop) :
    ∀ (pc : Imperative.RevPathConditions Expression)
      (events : List ObligationExtraction.ExtractReplayEvent) (ss : Statements),
    ∀ (acc arr : Array ObligationExtraction.LinkedObligation)
      (env' : IEnv Expression) (cfg : ReplayCfg Expression) (st : ReplayState Expression)
      (F : Nat) (evFuture : List ObligationExtraction.ExtractReplayEvent),
      ObligationExtraction.extractGoLinked link.entryStatements pc events ss acc = .ok arr →
      (obligation, link) ∈ arr.toList →
      (obligation, link) ∉ acc.toList →
      events ++ evFuture = link.events →
      eventsToOracle factory store evFuture = some st.remaining →
      StoreAgreesThreaded env'.store.get threaded →
      RWellFormedStore env'.store.get factory →
      WellScopedObl env'.store.get ss →
      env'.factory = factory →
      Block.nondetIteLast ss = true →
      Block.onlyAssertLast ss = true →
      pc.scopes.length ≤ 1 →
      (∀ x, (env'.store.get x).isSome →
        x ∈ (PassiveUnit.forObligation link obligation).inputs.map (·.1)
          ∨ x ∈ allVarNames pc.consume) →
      Block.stepBudget ss + fb ≤ F →
      (cfg.interruptOn = fun _ => none) →
      ∃ (σRun : RStore Expression) (pre : List (IEvent Expression)),
        (targetEvent obligation factory σRun obligation.metadata :: pre)
          <:+ (rrun (runInterp (replayStepCmd (fun _ => none) d) F (.stmts ss env')) cfg
              st).2.traceRev
        ∧ (AssumesHoldThreaded factory obligation threaded fb →
            PathFeasible Ftop st.traceRev → PathFeasible Ftop pre)
        ∧ StoreAgreesThreaded σRun threaded
        ∧ (∀ x ∈ HasFvars.getFvars (P := Expression) obligation.obligation, (σRun x).isSome)
        ∧ RWellFormedStore σRun factory := by
  have hfv : ∀ {e : Expression.Expr} {y}, y ∈ HasFvars.getFvars e →
      y ∈ (Lambda.LExpr.freeVars e).unzip.fst := by
    simp [HasFvars.getFvars, Lambda.getVars_eq_freeVars_idents]
  have hprepend : ∀ pc e y, y ∈ allVarNames (RevPathConditions.prepend pc e).consume ↔
      y ∈ allEntry e ∨ y ∈ allVarNames pc.consume := fun pc e y => by
    rw [show (pc.prepend e).consume = _ from consume_foldl_prepend [e] pc]
    exact (allVarNames_addEntry_perm _ _).mem_iff.trans List.mem_append
  have hdeclMem : ∀ {l : List (PathConditionEntry Expression)} {y t e},
      .varDecl y t e ∈ l → y ∈ l.flatMap allEntry :=
    fun h => List.mem_flatMap.2 ⟨_, h, by simp [allEntry]⟩
  intro pc events ss acc
  induction pc, events, ss, acc using
      ObligationExtraction.extractGoLinked_induct link.entryStatements <;>
    intro arr env cfg st F evFuture hext hmem hnotin hevents horacle hagree hwf hscoped rfl
      hbranch hassert hpc hdom hbudget hcfg
  all_goals try simp only [ObligationExtraction.extractGoLinked_nil,
    ObligationExtraction.extractGoLinked_assert, ObligationExtraction.extractGoLinked_cover,
    ObligationExtraction.extractGoLinked_assume, ObligationExtraction.extractGoLinked_init]
    at hext
  all_goals try simp only [Block.stepBudget, WellScopedObl, Block.nondetIteLast,
    Block.onlyAssertLast, Bool.and_eq_true, List.isEmpty_iff] at hbudget hscoped hbranch hassert
  all_goals try (obtain ⟨F, rfl⟩ : ∃ k, F = k + 3; exact ⟨F - 3, by omega⟩)
  case case1 =>
    cases hext
    exact absurd hmem hnotin
  case case2 | case3 =>
    rename_i obl lnk ih
    rw [run_stmts_passive_head (hstep := by
      first
        | exact step_assert_run (hcfg := hcfg) ..
        | exact step_cover_run (hcfg := hcfg) ..)]
    by_cases hEq : (obligation, link) = (obl, lnk)
    · rw [(Prod.mk.inj hEq).1]
      simp +zetaDelta only [targetEvent, convertMetaDataPropertyType_ne_cover, ↓reduceIte]
      exact ⟨_, _, runInterp_traceRev_suffix _ _ _ {st with traceRev := _ :: st.traceRev},
        fun _ => id, hagree, fun x h => hscoped.1 x (hfv h), hwf⟩
    · obtain ⟨σRun, pre, hsuf, hfeas, hrest⟩ :=
        ih _ _ _ {st with traceRev := _ :: st.traceRev} F _ hext hmem (by simp [hnotin, hEq])
          hevents horacle hagree hwf hscoped.2 rfl hbranch
          (by simp only [Block.onlyAssertLast, hassert]) hpc hdom (by omega) hcfg
      exact ⟨σRun, pre, hsuf,
        fun hA hF => hfeas hA (pathFeasible_cons.2 ⟨fun _ => nofun, hF⟩), hrest⟩
  case case4 pc events rest acc label e md ih =>
    rw [run_stmts_passive_head (hstep := step_assume_run (hcfg := hcfg) ..)]
    obtain ⟨σRun, pre, hsuf, hfeas, hrest⟩ :=
      ih _ _ _ {st with traceRev := _ :: st.traceRev} F _ hext hmem hnotin hevents horacle hagree
        hwf hscoped.2 rfl hbranch hassert (prepend_scopes_length_le_one _ _ hpc)
        (fun x hx => (hdom x hx).imp_right fun h => (hprepend _ _ _).2 (.inr h)) (by omega) hcfg
    refine ⟨σRun, pre, hsuf, fun hA hF => hfeas hA (pathFeasible_cons.2 ⟨?_, hF⟩), hrest⟩
    rintro _ ⟨⟩
    obtain ⟨v, hv, htt⟩ := hA label e (extractGoLinked_pc_entries_subset _ _ _ _ _ _ _ _ hext
      hmem hnotin _ (by rw [consume_flatten_prepend_single _ _ hpc]; simp))
    have he := cel_agreeEval hWF hFtop hwf (fun x h w hw => hagree x w hw (hscoped.1 x (hfv h))) hv
    simp only [he, Option.bind_some, InterpLang.boolLit?, htt, ↓reduceIte]
  case case5 pc events rest acc thenSs elseSs md ihThen ihElse _ =>
    obtain ⟨⟨rfl, hbrThen⟩, hbrElse⟩ := hbranch
    obtain ⟨b, sub, hsub, hmemSub, evTail, hevTail⟩ :=
      extractGoLinked_events_branch_head link.entryStatements pc events thenSs elseSs obligation
        link (by
          simp only [bind, Except.bind, List.append_assoc, List.cons_append, List.nil_append,
            Array.append_assoc, ObligationExtraction.extractGoLinked_ite,
            ObligationExtraction.extractGoLinked_nil] at hext
          grind)
    obtain rfl : evFuture = .branch b :: evTail := by simpa [← hevTail] using hevents
    rcases hor : eventsToOracle env.factory store evTail with _ | oracleTail <;>
      simp! only [eventsToOracle, eventChoice, hor, reduceCtorEq, Option.some.injEq] at horacle
    rw [driveRecords_ite_lift_pred (· = _) b _ _ _ _ _ _ _ _ horacle.symm
        (by cases b <;> exact Bool.and_eq_true _ _ ▸ ⟨Lambda.isValue_const_true .., rfl⟩)
        rfl,
      run_block_traceRev_eq]
    obtain ⟨⟨hasThen, hasElse⟩, -⟩ := hassert
    cases b <;> first | apply ihElse | apply ihThen
    all_goals first | assumption | rfl | omega | exact hscoped.1 | exact hscoped.2 | simp
  case case6 pc events rest acc name ty value md events' ih =>
    obtain ⟨sufAssm, hpre⟩ := extractGoLinked_pc_prefix _ _ _ _ _ _ _ _
      (prepend_scopes_length_le_one _ _ hpc) hext hmem hnotin
    rw [consume_flatten_prepend_single _ _ hpc] at hpre
    simp only [allVarNames, ← hpre, List.flatMap_append, List.nodup_append] at hssaNodup hssaDisj
    cases value <;> simp only [WellScopedObl] at hscoped
    case' det ev0 =>
      obtain ⟨v, heval, hvalTy, hmatchV, -⟩ := init_fold_witness _ hWF fb F (by omega)
        _ _ _ _ _ _ _ _ (by simpa [← hpre] using hthreadFlat)
        (by grind)
        (fun h => by simpa [hscoped.2.1] using hscoped.1 name (hfv h))
        (fun y hy _ _ h => by
          have hyDecl := hdeclMem h
          have hyDom := hdom y (hscoped.1 y (hfv hy))
          grind [allVarNames])
        hwf fun y h w hw => hagree y w hw (hscoped.1 y (hfv h))
      rw [run_stmts_passive_head
        (hstep := step_init_det_run _ _ _ _ _ _ _ _ _ v hscoped.2.1 heval hvalTy)]
      have hscopedRest := hscoped.2.2
      have hvalV := (Bool.and_eq_true _ _ ▸ hvalTy).1
    case' nondet =>
      obtain ⟨fresh, hfresh, harr⟩ := extractGoLinked_acc_append _ _ _ _ _ _ hext
      obtain ⟨evTail, hevTail⟩ := extractGoLinked_events_prefix _ _ _ _ _ _
        (EventsPrefixOK_empty _) hfresh obligation link (by simpa [harr, hnotin] using hmem)
      obtain rfl : evFuture = .nondetWrite name (some ty) :: evTail := by
        simpa [events', ← hevTail] using hevents
      simp only [eventsToOracle] at horacle
      split at horacle <;> simp only [Option.some.injEq, reduceCtorEq] at horacle
      rename_i v oracleTail hchoice hor
      have hvalTy : Lambda.LExpr.isValue env.factory v = true ∧
          valueHasType env.factory v ty = true := by
        cases hst : store name <;>
          simp! only [eventChoice, hst, Option.bind, Option.bind_eq_some_iff, Option.some.injEq]
            at hchoice
        · obtain ⟨w, hw, hd⟩ := hchoice
          simp only [valueHasType, hw, defaultValueIn_hasMonoType _ _ _ hd,
            defaultValueIn_isCanonical _ _ _ hd, and_self]
        · grind [valueHasType, hmb.1.2 name (some ty) (by simp [← hevents])]
      rw [run_stmts_passive_head (hstep := step_init_nondet_run _ _ _ _ _ _ _ _ _ _ hscoped.1
        horacle.symm (Bool.and_eq_true _ _ ▸ hvalTy))]
      have hscopedRest := hscoped.2
      have hvalV := hvalTy.1
      have hmatchV : ∀ w, threaded name = some w → w = v := fun w h => by
        rw [extendWithVarDecls'_frame_gen _ _ _ _ _ name hthreadFlat fun t e h => by
          rw [← hpre] at h
          grind] at h
        grind [eventChoice]
    all_goals
      exact ih _ {env with store := env.store.update name v} _ _ F _ hext hmem hnotin ‹_› ‹_›
        (IStore.get_update env.store name v ▸ storeAgreesThreaded_update _ _ _ _ hagree hmatchV)
        (IStore.get_update env.store name v ▸ wellFormedStore_update _ _ _ _ hwf hvalV)
        (IStore.get_update env.store name v ▸
          (WellScopedObl_dom_congr _ _ _ (update_dom_congr _ _ _ _ _ fun _ => rfl)).1 hscopedRest)
        rfl hbranch hassert (prepend_scopes_length_le_one _ _ hpc)
        (by simp only [IStore.get_update]; grind [allEntry, RStore.update]) (by omega) hcfg
  case case7 =>
    simp [ObligationExtraction.extractGoLinked_unsupported, *] at hext

/-- **The operational drive.**  For every model store and every `(env, oracle)` that
    `valuationToEnv` reconstructs from it, under the extraction provenance, the program shape,
    model-adequacy and scoping premises, and the threaded declarative store `threaded` of the
    level-`(b)` check, the replay at run/halt fuel `f + fb` has a trace suffix
    `targetEvent … :: pre` in which `pre` is `PathFeasible (f + fb)` whenever the level-`(b)`
    check's assumptions hold (`assumptionsHold' … = .isTrue`), at a well-formed run store
    `σRun` agreeing with `threaded` on the goal's free vars. -/
private theorem driveRecordsResolved_holds_strong
    (factory : @Lambda.Factory CoreLParams)
    (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink) :
    ∀ (store : RStore Expression) (env : IEnv Expression)
      (oracle : List Expression.Expr) (f fb : Nat) (threaded : RStore Expression)
      (pc0 : Imperative.RevPathConditions Expression)
      (arr : Array ObligationExtraction.LinkedObligation),
      RootPc pc0 →
      ObligationExtraction.extractLinkedFromStatements pc0 link.entryStatements = .ok arr →
      (obligation, link) ∈ arr.toList →
      valuationToEnv factory (PassiveUnit.forObligation link obligation) obligation link store
        = .ok (env, oracle) →
      checkObligationProgram ((PassiveUnit.forObligation link obligation).inputs.map (·.1))
        link.entryStatements = some f →
      ModelBinds link obligation factory store →
      WellScopedObl env.store.get link.entryStatements →
      Lambda.FactoryWF factory →
      obligation.assumptions.foldlM
        (Imperative.extendWithVarDecls' (P := Expression)
            (.runtime (evalBounded fb)) factory · ·)
            store = some threaded →
      ∃ (σRun : RStore Expression) (pre : List (IEvent Expression)),
        (targetEvent obligation factory σRun obligation.metadata :: pre)
          <:+ (runReplayRun
                (runCoreInterp (m := ReplayM Expression) (fun _ => none) (f + fb)
                  (.stmts link.entryStatements env))
                { oracleConfig := .strict }
                oracle).2.traceRev
        ∧ (Imperative.assumptionsHold' (P := Expression)
            (.runtime (evalBounded fb)) factory threaded
              obligation.assumptions = .isTrue →
            PathFeasible (f + fb) pre)
        ∧ RWellFormedStore σRun factory
        ∧ (∀ x ∈ HasFvars.getFvars obligation.obligation, σRun x = threaded x) := by
  intro store env oracle f fb threaded pc0 arr hroot hok hmem henv hprog hmb hscoped hWF
    hthread
  obtain ⟨hshapeBr, hshapeAs, hsyn, hf⟩ := checkObligationProgram_some hprog
  obtain ⟨hnodup, hdisj⟩ := extractLinked_all_ssa _ _ _ _ _ hok hmem hroot hsyn hshapeBr
  obtain ⟨hfac, hwfEnv⟩ := valuationToEnv_env_facts _ _ _ _ _ _ _ henv
  have hlen : obligation.assumptions.length ≤ 1 := by
    obtain ⟨extras, hextras⟩ := extractLinked_assumes_are_path_folded _ _ _ _ hok hmem
    exact hextras ▸ foldl_addEntry_length_le_one extras pc0.consume
      (by simpa [RevPathConditions.consume] using hroot.1)
  obtain ⟨σRun, pre, hsuf, hfeas, hagreeRun, hdefRun, hwfRun⟩ :=
    drive_walk _ _ _ _ _ _
      (by rcases hassm : obligation.assumptions with _ | ⟨_, _ | _⟩ <;> simp_all!)
      hWF hnodup hdisj hmb (f + fb) (Nat.le_add_left fb f) _ [] _ #[] _ env
      {oracleConfig := .strict} {remaining := oracle} (f + fb) link.events hok hmem nofun rfl
      (valuationToEnv_oracle_eq _ _ _ _ _ _ henv)
      (drive_base_store_agreement _ _ _ _ _ _ _ fb f _ _ hroot _ hok hmem henv hprog hthread)
      hwfEnv hscoped hfac hshapeBr hshapeAs hroot.1
      (fun x hx => .inl (valuationToEnv_inputs_only _ _ _ _ _ _ _ henv x hx)) (by omega)
      rfl
  refine ⟨σRun, pre, by rwa [runCoreInterp_eq],
    fun hassm => hfeas (assumesHold_of_assumptionsHold _ _ _ _ hassm) (pathFeasible_nil _), hwfRun,
    storeAgreesThreaded_pointwise _ _ _ hagreeRun (fun x hx => ?_) hdefRun⟩
  simp only [HasFvars.getFvars, Lambda.getVars_eq_freeVars_idents, List.mem_map, Prod.exists,
    exists_and_right, exists_eq_right] at hx
  obtain ⟨_, hfvMem⟩ := hx
  exact extendWithVarDecls'_foldlM_domain_mono _ _ _ _ _ _ hthread
    (Option.isSome_iff_ne_none.2 (hmb.2 _ hfvMem))

/-- **The drive obligation, at run/halt fuel `f + fb`.**  Under the extraction provenance
    (`arr`/`hok`/`hmem`), the level-`(b)` counterexample claim at fuel `fb`, and the
    reconstruction, shape, model-adequacy and scoping premises, the replay of
    `link.entryStatements` from the reconstructed `(env, oracle)`, run and halted at
    `f + fb`, has in its trace an event that fires `assertFailureHalt` for the target.
    The fuel includes the level-`(b)` counterexample's own validation budget `fb`, so the
    per-step evaluation budget suffices for a goal of any depth. -/
def EventsAreThePathResolved
    (factory : @Lambda.Factory CoreLParams)
    (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink) : Prop :=
  ∀ (store : RStore Expression) (env : IEnv Expression)
    (oracle : List Expression.Expr) (f fb : Nat)
    (pc0 : Imperative.RevPathConditions Expression)
    (arr : Array ObligationExtraction.LinkedObligation),
    RootPc pc0 →
    ObligationExtraction.extractLinkedFromStatements pc0 link.entryStatements = .ok arr →
    (obligation, link) ∈ arr.toList →
    (if obligation.property = Imperative.PropertyType.cover
      then IsValuationObligationCovBounded factory store obligation fb
      else IsValuationObligationCexBounded factory store obligation fb) →
    valuationToEnv factory (PassiveUnit.forObligation link obligation) obligation link store
      = .ok (env, oracle) →
    checkObligationProgram ((PassiveUnit.forObligation link obligation).inputs.map (·.1))
      link.entryStatements = some f →
    ModelBinds link obligation factory store →
    WellScopedObl env.store.get link.entryStatements →
    Lambda.FactoryWF factory →
    ∃ ev ∈ (runReplayRun
              (runCoreInterp (m := ReplayM Expression) (fun _ => none) (f + fb)
                (.stmts link.entryStatements env))
              { oracleConfig := .strict }
              oracle).2.traceRev,
      assertFailureHalt { label := obligation.label, md := obligation.metadata }
        (f + fb) ev = true

/-- **The drive's target event is a failing target occurrence.**  At a run store `σRun`
    agreeing with the level-`(b)` check's threaded declarative store on the goal's free
    variables, the target event `targetEvent obligation factory σRun obligation.metadata` fires
    `assertFailureHalt` at any fuel `f ≥ fb`: its goal evaluates `ff` (assert kind) or `tt`
    (cover kind). -/
private theorem assertFailureHalt_targetEvent
    (factory : @Lambda.Factory CoreLParams)
    (hWF : Lambda.FactoryWF factory)
    (store : RStore Expression) (obligation : ProofObligation Expression)
    (fb f : Nat) (hle : fb ≤ f)
    (hcexb : if obligation.property = Imperative.PropertyType.cover
      then IsValuationObligationCovBounded factory store obligation fb
      else IsValuationObligationCexBounded factory store obligation fb)
    (σRun threaded : RStore Expression)
    (hthread : obligation.assumptions.foldlM
        (Imperative.extendWithVarDecls' (P := Expression)
            (.runtime (evalBounded fb)) factory · ·)
            store = some threaded)
    (hwfRun : RWellFormedStore σRun factory)
    (hagree : ∀ x ∈ HasFvars.getFvars obligation.obligation, σRun x = threaded x) :
    assertFailureHalt { label := obligation.label, md := obligation.metadata } f
      (targetEvent obligation factory σRun obligation.metadata) = true := by
  by_cases hcov : obligation.property = .cover <;>
    simp only [hcov, targetEvent, ↓reduceIte] at hcexb ⊢
  · obtain ⟨v, hv, hm⟩ :=
      bounded_cov_goal_true_on_agreeing_store _ hWF _ _ _ _ hle hcexb _ _ hthread hwfRun hagree
    simp +decide [Calls.assertFailureHalt, InterpLang.boundedEval, hv, hm]
  · obtain ⟨v, hv, hm⟩ :=
      bounded_cex_goal_false_on_agreeing_store _ hWF _ _ _ _ hle hcexb _ _ hthread hwfRun hagree
    simp +decide [Calls.assertFailureHalt, InterpLang.boundedEval, hv, hm]

/-- `EventsAreThePathResolved` holds **unconditionally**: for every factory, obligation
    and link, the replay at `f + fb` records an event firing `assertFailureHalt` for the
    target. -/
theorem eventsAreThePathResolved_holds
    (factory : @Lambda.Factory CoreLParams)
    (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink) :
    EventsAreThePathResolved factory obligation link := by
  intro store env oracle f fb pc0 arr hroot hok hmem hcexb henv hprog hmb hscoped hWF
  have hsplit := hcexb
  split at hsplit
  all_goals first
    | obtain ⟨threaded, hthread, -⟩ := genuine_decompose_gen_cover _ _ _ _ hsplit
    | obtain ⟨threaded, hthread, -⟩ := genuine_decompose_gen _ _ _ _ hsplit
  all_goals
    obtain ⟨σRun, _, hsuf, -, hwfRun, hagree⟩ := driveRecordsResolved_holds_strong
      _ _ _ _ _ _ _ _ _ _ _ hroot hok hmem henv hprog hmb hscoped hWF hthread
    exact ⟨_, mem_of_mem_suffix (.head _) hsuf, assertFailureHalt_targetEvent _ hWF _ _ _ _
      (Nat.le_add_left _ _) hcexb _ _ hthread hwfRun hagree⟩

/-- **Path feasibility of the production run.**  Under the hypotheses of
    `EventsAreThePathResolved`, the fuel-matched **production** replay (`interruptOn :=
    enforceInterrupt target (f + fb)`) of `link.entryStatements` from the reconstructed
    `(env, oracle)` has a `PathFeasible (f + fb)` trace: every `.assume` it records evaluates
    `tt`. -/
private theorem eventsAreThePathResolved_feasible
    (factory : @Lambda.Factory CoreLParams)
    (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink)
    (store : RStore Expression) (env : IEnv Expression)
    (oracle : List Expression.Expr) (f fb : Nat)
    (pc0 : Imperative.RevPathConditions Expression) (hpc0 : RootPc pc0)
    (arr : Array ObligationExtraction.LinkedObligation)
    (hok : ObligationExtraction.extractLinkedFromStatements pc0 link.entryStatements = .ok arr)
    (hmem : (obligation, link) ∈ arr.toList)
    (hcexb : if obligation.property = Imperative.PropertyType.cover
      then IsValuationObligationCovBounded factory store obligation fb
      else IsValuationObligationCexBounded factory store obligation fb)
    (henv : valuationToEnv factory (PassiveUnit.forObligation link obligation) obligation link store
      = .ok (env, oracle))
    (hprog : checkObligationProgram ((PassiveUnit.forObligation link obligation).inputs.map (·.1))
      link.entryStatements = some f)
    (hmb : ModelBinds link obligation factory store)
    (hws : WellScopedObl env.store.get link.entryStatements)
    (hWF : Lambda.FactoryWF factory) :
    PathFeasible (f + fb)
      (runReplayRun
        (runCoreInterp (m := ReplayM Expression) (fun _ => none) (f + fb)
          (.stmts link.entryStatements env))
        { oracleConfig := .strict,
          interruptOn :=
            enforceInterrupt { label := obligation.label, md := obligation.metadata }
            (f + fb) }
        oracle).2.traceRev := by
  have hsplit := hcexb
  split at hsplit
  all_goals first
    | obtain ⟨threaded, hthread, -, hassm⟩ := genuine_decompose_gen_cover _ _ _ _ hsplit
    | obtain ⟨threaded, hthread, -, hassm⟩ := genuine_decompose_gen _ _ _ _ hsplit
  all_goals
    obtain ⟨σRun, pre, hsuf, hfeas, hwfRun, hagree⟩ := driveRecordsResolved_holds_strong
      _ _ _ _ _ _ _ _ _ _ _ hpc0 hok hmem henv hprog hmb hws hWF hthread
    exact pathFeasible_enforce_of_spec_suffix _ _ _ _ _ _ _ pre
      (assertFailureHalt_targetEvent _ hWF _ _ _ _ (Nat.le_add_left _ _) hcexb _ _
        hthread hwfRun hagree) (hfeas hassm) hsuf

/-- **The `(b)→(a)` CexValuation producer is valid on one counterexample.**  For a
    `CexValuation` satisfying `CexValuationValid`, the outcome of
    `reconstructAssertionFromCexValuation` is a `ValidOutcome`:

    * `cex.fuel = some fb`: with a good-shape `predictedFuel = some f` the producer claims the
      top-level slice at fuel `f + fb` without replaying; running the slice at that fuel reaches
      the target with its condition false, on the path the level-`(b)` valuation describes.
    * otherwise the producer replays and claims the `CexA` the replay validates, at the fuel
      the replay used, or returns the top-level slice as the lone unconfirmed slice; if
      `valuationToEnv` fails, the outcome is empty.

    The bridge hypotheses `H_modelBinds`/`H_scoped` (model adequacy and scoping, required only
    at `cex.fuel = some fb`) and `H_H2` (extraction provenance) are the facts the drive
    needs. -/
theorem reconstructAssertionFromCexValuation_valid_of_cex
    (factory : @Lambda.Factory CoreLParams)
    (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink) (defaultFuel : Nat)
    (hWF : Lambda.FactoryWF factory)
    (hCB : Lambda.Factory.ConstrsNotBool factory)
    (cex : CexValuation) (hcexb : CexValuationValid factory obligation cex)
    (H_modelBinds : ∀ fb, cex.fuel = some fb → ModelBinds link obligation factory cex.valuation)
    (H_scoped : ∀ fb env oracle, cex.fuel = some fb →
      valuationToEnv factory (PassiveUnit.forObligation link obligation) obligation link
          cex.valuation = .ok (env, oracle) →
      WellScopedObl env.store.get link.entryStatements)
    (H_H2 : ∃ pc0 arr,
        RootPc pc0 ∧ ObligationExtraction.extractLinkedFromStatements pc0 link.entryStatements = .ok
        arr
      ∧ (obligation, link) ∈ arr.toList)
    :
    ValidOutcome (fun _ => none) { label := obligation.label, md := obligation.metadata }
      link.entryStatements
      (reconstructAssertionFromCexValuation factory (PassiveUnit.forObligation link obligation)
        obligation link (fun _ => none) defaultFuel cex) := by
  obtain ⟨pc0, arr, hroot, hok, hmem⟩ := H_H2
  unfold reconstructAssertionFromCexValuation
  split
  · simp [ValidOutcomeOf, chain, empty]
  rename_i env oracle henv
  have hEnvWF : EnvWF env :=
    let ⟨hfac, hwf⟩ := valuationToEnv_env_facts _ _ _ _ _ _ _ henv
    ⟨hfac ▸ ⟨hWF, hCB⟩, fun _ _ h => Lambda.isValue_getVars_nil _ _ (hwf _ _ h)⟩
  simp only [ObligationExtraction.ExtractBackLink.liftCexValuation]
  split
  · rename_i f fb hprog hfuel
    simp only [CexValuationValid, hfuel] at hcexb
    have hmb := H_modelBinds _ hfuel
    have hws := H_scoped _ _ _ hfuel henv
    simpa [ValidOutcomeOf, chain, isTopLevelAt, CexWF, Calls.genuineFeasible, genuine_iff,
      hEnvWF] using
      And.intro
        (eventsAreThePathResolved_holds _ _ _ _ _ _ _ _ _ _ hroot hok hmem hcexb henv hprog hmb
          hws hWF)
        (eventsAreThePathResolved_feasible _ _ _ _ _ _ _ _ _ hroot _ hok hmem hcexb henv hprog
          hmb hws hWF)
  · split
    · rename_i top hrep
      obtain ⟨c, fuel'⟩ := top
      simp [ValidOutcomeOf, chain, isTopLevelAt, CexWF, replayCandidate_cfg _ _ _ _ _ _ _ hrep,
        hEnvWF, replayCandidate_genuineFeasible _ _ _ _ _ _ _ hrep]
    · simp [ValidOutcomeOf, chain, isTopLevelAt, CexWF, hEnvWF]

/-- **The `(b)→(a)` CexValuation producer is valid for every counterexample.** Under a well-formed
    factory none of whose constructors produces a `Bool`, and the bridge hypotheses
    (`H_modelBinds`/`H_scoped`, here quantified over every `CexValuation` satisfying
    `CexValuationValid` with `cex.fuel = some fb`, and the extraction provenance `H_H2`), the
    producer `reconstructAssertionFromCexValuation` satisfies `ValuationToRunBackLinkValid`: for
    every `CexValuation` satisfying `CexValuationValid`, the outcome it returns is a `ValidOutcome`
    for the target assertion (the obligation's label and metadata) over `link.entryStatements`, with
    no callee procedures. -/
theorem reconstructAssertionFromCexValuation_satisfies_valid_full
    (factory : @Lambda.Factory CoreLParams)
    (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink) (defaultFuel : Nat)
    (hWF : Lambda.FactoryWF factory)
    (hCB : Lambda.Factory.ConstrsNotBool factory)
    (H_modelBinds : ∀ (cex : CexValuation) fb, cex.fuel = some fb →
      CexValuationValid factory obligation cex →
      ModelBinds link obligation factory cex.valuation)
    (H_scoped : ∀ (cex : CexValuation) fb env oracle, cex.fuel = some fb →
      CexValuationValid factory obligation cex →
      valuationToEnv factory (PassiveUnit.forObligation link obligation) obligation link
          cex.valuation = .ok (env, oracle) →
      WellScopedObl env.store.get link.entryStatements)
    (H_H2 : ∃ pc0 arr,
        RootPc pc0 ∧ ObligationExtraction.extractLinkedFromStatements pc0 link.entryStatements = .ok
        arr
      ∧ (obligation, link) ∈ arr.toList)
    :
    ValuationToRunBackLinkValid (fun _ => none)
      { label := obligation.label, md := obligation.metadata }
      factory obligation link.entryStatements
      (reconstructAssertionFromCexValuation factory (PassiveUnit.forObligation link obligation)
        obligation link (fun _ =>
            none) defaultFuel) :=
  fun cex hcex => reconstructAssertionFromCexValuation_valid_of_cex _ _ _ _ hWF hCB cex hcex
    (H_modelBinds cex · · hcex) (H_scoped cex · · · · hcex) H_H2

end -- public section

end Core
