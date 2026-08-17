/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.NondetElim
public import Strata.Transform.NondetElimProps
public import Strata.Transform.LoopInitHoist
public import Strata.Transform.Specification
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.StmtSemanticsProps
import all Strata.DL.Imperative.StmtSemanticsProps
import all Strata.DL.Util.StringGen
import all Strata.Util.Relations
import all Strata.Util.RelationsProps

public section

namespace Imperative

/-! ## Structural postcondition: the pass output has no nondeterministic control

`Block.simpleShape` holds of every output of `Block.nondetElim` (spec guarantee
2): the rewrite replaces each nondeterministic `.ite`/`.loop` guard with a
deterministic read, so no `.ite .nondet`/`.loop .nondet` survives. -/

mutual
/-- The output of `Stmt.nondetElimM s σ` satisfies `simpleShape` (no
nondeterministic control). -/
theorem Stmt.nondetElimM_simpleShape {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.simpleShape (Stmt.nondetElimM s σ).1 = true := by
  match s with
  | .cmd c => simp [Stmt.nondetElimM, Block.simpleShape, Stmt.simpleShape]
  | .block lbl bss md =>
      rw [Stmt.nondetElimM_block_out]
      simp only [Block.simpleShape, Stmt.simpleShape, Bool.and_true]
      exact Block.nondetElimM_simpleShape bss σ
  | .ite (.det e) tss ess md =>
      rw [Stmt.nondetElimM_ite_det_out]
      simp only [Block.simpleShape, Stmt.simpleShape, Bool.and_true,
                 Block.nondetElimM_simpleShape tss σ,
                 Block.nondetElimM_simpleShape ess _]
  | .ite .nondet tss ess md =>
      rw [Stmt.nondetElimM_ite_nondet_out]
      simp only [Block.simpleShape, Stmt.simpleShape, Bool.and_true,
                 Block.nondetElimM_simpleShape tss _,
                 Block.nondetElimM_simpleShape ess _]
  | .loop (.det e) m inv body md =>
      rw [Stmt.nondetElimM_loop_det_out]
      simp only [Block.simpleShape, Stmt.simpleShape, Bool.and_true]
      exact Block.nondetElimM_simpleShape body σ
  | .loop .nondet m inv body md =>
      rw [Stmt.nondetElimM_loop_nondet_out]
      simp only [Block.simpleShape, Stmt.simpleShape, Block.simpleShape_append,
                 Bool.and_true,
                 Block.nondetElimM_simpleShape body _]
  | .exit lbl md => simp [Stmt.nondetElimM, Block.simpleShape, Stmt.simpleShape]
  | .funcDecl d md => simp [Stmt.nondetElimM, Block.simpleShape, Stmt.simpleShape]
  | .typeDecl t md => simp [Stmt.nondetElimM, Block.simpleShape, Stmt.simpleShape]
  termination_by sizeOf s

theorem Block.nondetElimM_simpleShape {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.simpleShape (Block.nondetElimM ss σ).1 = true := by
  match ss with
  | [] => simp [Block.nondetElimM, Block.simpleShape]
  | s :: rest =>
      rw [Block.nondetElimM_cons_out, Block.simpleShape_append]
      simp only [Stmt.nondetElimM_simpleShape s σ,
                 Block.nondetElimM_simpleShape rest _, Bool.and_true]
  termination_by sizeOf ss
end

/-- Top-level structural postcondition: `Block.nondetElim` output has no
nondeterministic control (spec guarantee 2). -/
theorem nondetElim_simpleShape {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) :
    Block.simpleShape (Block.nondetElim ss) = true :=
  Block.nondetElimM_simpleShape ss StringGenState.emp

/-- `nondetElim` removes nondeterministic loops, so its output satisfies
`containsNondetLoop = false` (via the `simpleShape` postcondition). -/
theorem nondetElim_containsNondetLoop {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) :
    Block.containsNondetLoop (Block.nondetElim ss) = false :=
  Block.not_containsNondetLoop_of_simpleShape _ (nondetElim_simpleShape ss)

/-! ## Foundation lemmas for the simulation proof

These are fully-proved building blocks for `nondetElim_simulation`, reused
arm-by-arm.  They live outside the main inductive lemma so that each can be
verified independently. -/

section Foundation

/-- Outcome-generic `.ite .nondet` prefix replay (then side): the chosen branch
`tss` reaching `Env.outcomeConfig oc ρt'` drives the emitted prefix to the same
outcome at the block-projected env (the ite branch runs in a `.block .none`
scope, so the guard `ident` — defined by the `init` prefix — is projected away). -/
theorem step_ndelim_ite_prefix_outcome {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasFvar P] {extendFactory : ExtendFactory P}
    (b : Bool) (ident : P.Ident) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (ρ ρt' : Env P) (oc : Option String)
    (h_none : ρ.store ident = none)
    (hwf_var : WellFormedSemanticEvalVar ρ.factory)
    (hwf_mono : WellFormedSemanticEvalMono ρ.factory)
    (hwfb : WellFormedSemanticEvalBool ρ.factory)
    (h_branch : StepStmtStar P (EvalCmd P) extendFactory
      (.stmts (if b then tss else ess)
        ({ ρ with store := SemanticStore.update ρ.store ident (if b then HasBool.tt else HasBool.ff) } : Env P))
      (Env.outcomeConfig oc ρt')) :
    StepStmtStar P (EvalCmd P) extendFactory
      (.stmts [.cmd (HasInit.init ident HasBool.boolTy (.nondet) md),
               .ite (.det (HasFvar.mkFvar ident)) tss ess md] ρ)
      (Env.outcomeConfig oc ({ ρt' with
        store := projectStore (SemanticStore.update ρ.store ident (if b then HasBool.tt else HasBool.ff)) ρt'.store,
        factory := ρ.factory } : Env P)) := by
  let v : P.Expr := if b then HasBool.tt else HasBool.ff
  have hval : HasVal.value ρ.factory v := by
    simp only [v]; split
    · exact (HasBool.boolIsVal ρ.factory).1
    · exact (HasBool.boolIsVal ρ.factory).2
  let ρg : Env P := { ρ with store := SemanticStore.update ρ.store ident v }
  have h1 : StepStmtStar P (EvalCmd P) extendFactory
      (.stmts [.cmd (HasInit.init ident HasBool.boolTy (.nondet) md),
               .ite (.det (HasFvar.mkFvar ident)) tss ess md] ρ)
      (.stmts [.ite (.det (HasFvar.mkFvar ident)) tss ess md] ρg) :=
    stmts_cons_step P (EvalCmd P) extendFactory _ _ ρ ρg
      (step_init_havoc_to (extendFactory := extendFactory) ident HasBool.boolTy v md ρ h_none hval hwf_var)
  have h_guard : P.eval ρg.factory ρg.store (HasFvar.mkFvar ident) = some v :=
    eval_mkFvar_storeWith ρ.factory ρ.store ident v hval hwf_var hwf_mono
  have hwfb' : WellFormedSemanticEvalBool ρg.factory := hwfb
  have h_blk : StepStmtStar P (EvalCmd P) extendFactory
      (.block .none ρg.store ρg.factory (.stmts (if b then tss else ess) ρg))
      (Env.outcomeConfig oc ({ ρt' with store := projectStore ρg.store ρt'.store, factory := ρg.factory } : Env P)) :=
    blockT_none_build_outcome (extendFactory := extendFactory) _ ρg.store ρg.factory oc ρt' h_branch
  have h2 : StepStmtStar P (EvalCmd P) extendFactory
      (.stmts [.ite (.det (HasFvar.mkFvar ident)) tss ess md] ρg)
      (Env.outcomeConfig oc ({ ρt' with store := projectStore ρg.store ρt'.store, factory := ρg.factory } : Env P)) := by
    refine .step _ _ _ .step_stmts_cons ?_
    cases b with
    | true =>
      exact .step _ _ _ (.step_seq_inner (.step_ite_true h_guard hwfb'))
        (seq_nil_outcome (extendFactory := extendFactory) _ _ oc h_blk)
    | false =>
      exact .step _ _ _ (.step_seq_inner (.step_ite_false h_guard hwfb'))
        (seq_nil_outcome (extendFactory := extendFactory) _ _ oc h_blk)
  exact ReflTrans_Transitive _ _ _ _ h1 h2

/-- From a *clean*-start statement run reaching a *failing* config, the run takes
at least one step.  (A refl run would keep the config at `.stmt s ρ`, whose
`getEnv` is the clean `ρ`, contradicting the failing flag.)  Exposes the first
step and residual. -/
theorem clean_stmt_first_step {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasVarsPure P P.Expr] {extendFactory : ExtendFactory P}
    {s : Stmt P (Cmd P)} {ρ : Env P} {c : Config P (Cmd P)}
    (h_reach : StepStmtStar P (EvalCmd P) extendFactory (.stmt s ρ) c)
    (hc : c.getEnv.hasFailure = true)
    (h_clean : ρ.hasFailure = false) :
    ∃ cfg, StepStmt P (EvalCmd P) extendFactory (.stmt s ρ) cfg ∧
      StepStmtStar P (EvalCmd P) extendFactory cfg c := by
  cases h_reach with
  | refl => exact absurd (by simpa [Config.getEnv] using hc) (by rw [h_clean]; simp)
  | step _ mid _ hstep hrest => exact ⟨mid, hstep, hrest⟩

/-- Singleton-list failing lift: a single statement reaching a *failing* config
(not necessarily terminal/exiting) yields the singleton list reaching a failing
config.  The residual `d` is wrapped as `.seq d []`, whose `getEnv` (hence failure
flag) is `d`'s. -/
theorem stmt_to_singleton_stmts_fail {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasVarsPure P P.Expr] {extendFactory : ExtendFactory P}
    (s : Stmt P (Cmd P)) (ρ : Env P) (d : Config P (Cmd P))
    (h : StepStmtStar P (EvalCmd P) extendFactory (.stmt s ρ) d)
    (hd : d.getEnv.hasFailure = true) :
    ∃ d', StepStmtStar P (EvalCmd P) extendFactory (.stmts [s] ρ) d'
      ∧ d'.getEnv.hasFailure = true :=
  ⟨.seq d ([] : List (Stmt P (Cmd P))),
    .step _ _ _ StepStmt.step_stmts_cons (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h),
    by simpa [Config.getEnv] using hd⟩

/-- Failing `.ite .nondet` prefix replay (then side): the chosen branch `tss`
reaching a *failing* config drives the emitted `init $g; ite $g` prefix to a
failing config (havoc value `tt`). -/
theorem step_ndelim_ite_prefix_fail {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasFvar P] {extendFactory : ExtendFactory P}
    (b : Bool) (ident : P.Ident) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (ρ : Env P) (d : Config P (Cmd P))
    (h_none : ρ.store ident = none)
    (hwf_var : WellFormedSemanticEvalVar ρ.factory)
    (hwf_mono : WellFormedSemanticEvalMono ρ.factory)
    (hwfb : WellFormedSemanticEvalBool ρ.factory)
    (h_branch : StepStmtStar P (EvalCmd P) extendFactory
      (.stmts (if b then tss else ess)
        ({ ρ with store := SemanticStore.update ρ.store ident (if b then HasBool.tt else HasBool.ff) } : Env P)) d)
    (hd : d.getEnv.hasFailure = true) :
    ∃ d', StepStmtStar P (EvalCmd P) extendFactory
      (.stmts [.cmd (HasInit.init ident HasBool.boolTy (.nondet) md),
               .ite (.det (HasFvar.mkFvar ident)) tss ess md] ρ) d'
      ∧ d'.getEnv.hasFailure = true := by
  let v : P.Expr := if b then HasBool.tt else HasBool.ff
  have hval : HasVal.value ρ.factory v := by
    simp only [v]; split
    · exact (HasBool.boolIsVal ρ.factory).1
    · exact (HasBool.boolIsVal ρ.factory).2
  let ρg : Env P := { ρ with store := SemanticStore.update ρ.store ident v }
  have h1 : StepStmtStar P (EvalCmd P) extendFactory
      (.stmts [.cmd (HasInit.init ident HasBool.boolTy (.nondet) md),
               .ite (.det (HasFvar.mkFvar ident)) tss ess md] ρ)
      (.stmts [.ite (.det (HasFvar.mkFvar ident)) tss ess md] ρg) :=
    stmts_cons_step P (EvalCmd P) extendFactory _ _ ρ ρg
      (step_init_havoc_to (extendFactory := extendFactory) ident HasBool.boolTy v md ρ h_none hval hwf_var)
  have h_guard : P.eval ρg.factory ρg.store (HasFvar.mkFvar ident) = some v :=
    eval_mkFvar_storeWith ρ.factory ρ.store ident v hval hwf_var hwf_mono
  -- The single-statement `.ite` scopes the chosen branch in a `.block .none`; run
  -- the branch inside that scope to the failing config `.block none ρg.store ρg.factory d`
  -- (a `.block`'s `getEnv` is its inner config's, so the failure flag is preserved).
  let dblk : Config P (Cmd P) := .block .none ρg.store ρg.factory d
  have h_blk_run : StepStmtStar P (EvalCmd P) extendFactory
      (.block .none ρg.store ρg.factory (.stmts (if b then tss else ess) ρg)) dblk :=
    block_inner_star P (EvalCmd P) extendFactory _ _ .none ρg.store ρg.factory h_branch
  have hdblk : dblk.getEnv.hasFailure = true := by simpa only [dblk, Config.getEnv] using hd
  have h_ite : StepStmtStar P (EvalCmd P) extendFactory
      (.stmt (.ite (.det (HasFvar.mkFvar ident)) tss ess md) ρg) dblk := by
    cases b with
    | true => exact .step _ _ _ (.step_ite_true h_guard hwfb) h_blk_run
    | false => exact .step _ _ _ (.step_ite_false h_guard hwfb) h_blk_run
  obtain ⟨d', h2, hd'⟩ :=
    stmt_to_singleton_stmts_fail (extendFactory := extendFactory)
      (.ite (.det (HasFvar.mkFvar ident)) tss ess md) ρg dblk h_ite hdblk
  exact ⟨d', ReflTrans_Transitive _ _ _ _ h1 h2, hd'⟩

/-! ### ReflTransT decomposition helpers (for the loop fuel induction)

These are pure structured-semantics facts about `StepStmt`/`ReflTransT` (the
*Type*-valued, length-carrying multi-step closure).  They split a run that
reaches `.terminal` into its constituent sub-runs while exposing a strict
length decrease, which is what feeds the `decreasing_by`/`termination_by`
fuel induction used by the `.loop` simulation arms.  They are independent of
the rewritten (target) program shape, so they hold over the source semantics
verbatim. -/

/-- First-step inversion of a deterministic loop run reaching an outcome
(`Env.outcomeConfig oc ρ'`).  The first step is either `step_loop_exit` (guard `ff`,
residual run from `.terminal (ρ + false)`) or `step_loop_enter` (guard `tt`,
residual run from `.seq (.block .none ρ.store ρ.factory (.stmts body (ρ + false))) [loop]`).
The invariant list `inv` is threaded verbatim and plays no role in the
enter/exit inversion; the residual carries a strict len-decrease.  Casing `oc` makes the outcome target a
constructor, so the `.refl` case (which would require `Env.outcomeConfig oc ρ' =
.stmt (.loop …)`) is ruled out by constructor mismatch. -/
theorem loop_det_step_first_inv {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasVarsPure P P.Expr] {extendFactory : ExtendFactory P}
    {e : P.Expr} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {ρ ρ' : Env P} {oc : Option String}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
      (.stmt (.loop (.det e) m inv body md) ρ) (Env.outcomeConfig oc ρ')) :
    (P.eval ρ.factory ρ.store e = some HasBool.ff ∧ WellFormedSemanticEvalBool ρ.factory ∧
        ∃ (hrest : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
            (.terminal ρ)
            (Env.outcomeConfig oc ρ')),
          hrest.len < hstar.len) ∨
    (P.eval ρ.factory ρ.store e = some HasBool.tt ∧ WellFormedSemanticEvalBool ρ.factory ∧
        ∃ (hrest : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
            (.seq (.block .none ρ.store ρ.factory (.stmts body ρ))
              [.loop (.det e) m inv body md])
            (Env.outcomeConfig oc ρ')),
          hrest.len < hstar.len) := by
  cases oc with
  | none =>
    simp only [Env.outcomeConfig] at hstar ⊢
    match hstar with
    | .step _ _ _ (StepStmt.step_loop_exit h_cond hwfb_s) hrest =>
      exact .inl ⟨h_cond, hwfb_s, hrest, by simp only [ReflTransT.len]; omega⟩
    | .step _ _ _ (StepStmt.step_loop_enter h_cond hwfb_s) hrest =>
      exact .inr ⟨h_cond, hwfb_s, hrest, by simp only [ReflTransT.len]; omega⟩
  | some lbl =>
    simp only [Env.outcomeConfig] at hstar ⊢
    match hstar with
    | .step _ _ _ (StepStmt.step_loop_exit h_cond hwfb_s) hrest =>
      exact .inl ⟨h_cond, hwfb_s, hrest, by simp only [ReflTransT.len]; omega⟩
    | .step _ _ _ (StepStmt.step_loop_enter h_cond hwfb_s) hrest =>
      exact .inr ⟨h_cond, hwfb_s, hrest, by simp only [ReflTransT.len]; omega⟩

/-- First-step inversion of a *nondeterministic* loop run reaching an outcome
(`Env.outcomeConfig oc ρ'`).  The first step is either `step_loop_nondet_exit`
(residual run from `.terminal (ρ + false)`) or `step_loop_nondet_enter`
(residual run from `.seq (.block .none ρ.store ρ.factory (.stmts body (ρ + false))) [loop]`).
The invariant list `inv` is threaded verbatim and plays no role in the
enter/exit inversion; the residual carries a strict len-decrease.  Unlike the deterministic variant there is *no*
guard read: the enter/exit choice is genuinely nondeterministic. -/
theorem loop_nondet_step_first_inv {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasVarsPure P P.Expr] {extendFactory : ExtendFactory P}
    {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {ρ ρ' : Env P} {oc : Option String}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
      (.stmt (.loop .nondet m inv body md) ρ) (Env.outcomeConfig oc ρ')) :
    (∃ (hrest : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
        (.terminal ρ)
        (Env.outcomeConfig oc ρ')),
      hrest.len < hstar.len) ∨
    (∃ (hrest : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
        (.seq (.block .none ρ.store ρ.factory (.stmts body ρ))
          [.loop .nondet m inv body md])
        (Env.outcomeConfig oc ρ')),
      hrest.len < hstar.len) := by
  cases oc with
  | none =>
    simp only [Env.outcomeConfig] at hstar ⊢
    match hstar with
    | .step _ _ _ StepStmt.step_loop_nondet_exit hrest =>
      exact .inl ⟨hrest, by simp only [ReflTransT.len]; omega⟩
    | .step _ _ _ StepStmt.step_loop_nondet_enter hrest =>
      exact .inr ⟨hrest, by simp only [ReflTransT.len]; omega⟩
  | some lbl =>
    simp only [Env.outcomeConfig] at hstar ⊢
    match hstar with
    | .step _ _ _ StepStmt.step_loop_nondet_exit hrest =>
      exact .inl ⟨hrest, by simp only [ReflTransT.len]; omega⟩
    | .step _ _ _ StepStmt.step_loop_nondet_enter hrest =>
      exact .inr ⟨hrest, by simp only [ReflTransT.len]; omega⟩

/-- Failing-config first-step inversion of a *nondeterministic* loop run reaching
an arbitrary config `c` (with `c.getEnv.hasFailure = true`).  Same shape as
`loop_nondet_step_first_inv` but keyed on a failing config rather than an
outcome, with one extra disjunct for the *refl* run (the loop start is itself the
failing config, forcing `ρ.hasFailure = true`): the run is either reflexive
(no step taken, `ρ` already failing), or its first step is `step_loop_nondet_exit`
(residual from `.terminal (ρ + false)`) or `step_loop_nondet_enter` (residual from
`.seq (.block .none ρ.store ρ.factory (.stmts body (ρ + false))) [loop]`), with the
residual carrying the failing config and a strict len-decrease. -/
theorem loop_nondet_step_first_inv_fail {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasVarsPure P P.Expr] {extendFactory : ExtendFactory P}
    {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {ρ : Env P} {c : Config P (Cmd P)}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
      (.stmt (.loop .nondet m inv body md) ρ) c)
    (hc : c.getEnv.hasFailure = true) :
    ρ.hasFailure = true ∨
    (∃ (hrest : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
        (.terminal ρ) c),
      hrest.len < hstar.len) ∨
    (∃ (hrest : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
        (.seq (.block .none ρ.store ρ.factory (.stmts body ρ))
          [.loop .nondet m inv body md]) c),
      hrest.len < hstar.len) := by
  match hstar with
  | .refl _ =>
    exact .inl (by simpa [Config.getEnv] using hc)
  | .step _ _ _ StepStmt.step_loop_nondet_exit hrest =>
    exact .inr (.inl ⟨hrest, by simp only [ReflTransT.len]; omega⟩)
  | .step _ _ _ StepStmt.step_loop_nondet_enter hrest =>
    exact .inr (.inr ⟨hrest, by simp only [ReflTransT.len]; omega⟩)

end Foundation

/-! ### Freshness invariant for generated guard variables

The simulation lemma is mutual over `Stmt`/`Block` and threads a
`StringGenState σ`.  Each `.ite .nondet`/`.loop .nondet` generates a fresh guard
`g` at the *current* `σ`, defines it in the target store, then recurses at the
*advanced* state.  To keep generating fresh guards legal under recursion we
track a self-preserving invariant on the target store:

> every gen-shaped string `s` that has **not yet been generated**
> (`s ∉ σ.stringGens`) is undefined in the target store.

A freshly generated `g` is gen-shaped (`gen_hasUnderscoreDigitSuffix`) and not
yet in `σ.stringGens` (`stringGens_gen_not_in`, needs `WF σ`), so the invariant
gives `g`'s slot is `none` — exactly the `init`/`set` precondition.  After
defining `g`, the advanced state's `stringGens` gains `g`, so any *still*-ungenerated
gen-shaped `s` differs from `g` (`ident` injective) and stays `none`. -/

section Freshness

/-- Target-store freshness invariant relative to a generator state `σ`, for a
*kind predicate* `Q` on label strings: every `Q`-string not yet generated by
`σ` is undefined in `σ_tgt`.  Instantiating `Q := HasUnderscoreDigitSuffix`
recovers the blanket gen-shape freshness invariant; a per-kind `Q` lets a
composition argument restrict freshness to just the labels *this* pass generates. -/
@[expose] def GenFreshStore {P : PureExpr} [HasIdent P]
    (Q : String → Prop)
    (σ : StringGenState) (σ_tgt : SemanticStore P) : Prop :=
  ∀ s, Q s → s ∉ σ.stringGens →
    σ_tgt (HasIdent.ident (P := P) s) = none

/-- The freshly-generated guard's slot is undefined in a `GenFreshStore` target,
given `WF σ` and that the freshly generated label satisfies the kind predicate. -/
theorem GenFreshStore_gen_slot_none {P : PureExpr} [HasIdent P]
    {Q : String → Prop}
    {σ : StringGenState} {σ_tgt : SemanticStore P}
    (pf : String) (h_fresh : GenFreshStore Q σ σ_tgt) (hwf : StringGenState.WF σ)
    (hQ : Q (StringGenState.gen pf σ).1) :
    σ_tgt (HasIdent.ident (P := P) (StringGenState.gen pf σ).1) = none :=
  h_fresh _ hQ (StringGenState.stringGens_gen_not_in pf σ hwf)

/-- `GenFreshStore` is preserved across defining the freshly-generated guard
`g := (gen pf σ).1` (via `SemanticStore.update`), advancing the state to `(gen pf σ).2`. -/
theorem GenFreshStore_storeWith_gen {P : PureExpr} [HasIdent P] [DecidableEq P.Ident]
    [LawfulHasIdent P]
    {Q : String → Prop}
    {σ : StringGenState} {σ_tgt : SemanticStore P}
    (pf : String) (b : P.Expr) (h_fresh : GenFreshStore Q σ σ_tgt) :
    GenFreshStore Q (StringGenState.gen pf σ).2
      (SemanticStore.update σ_tgt (HasIdent.ident (P := P) (StringGenState.gen pf σ).1) b) := by
  intro s h_suf h_nin
  rw [StringGenState.stringGens_gen] at h_nin
  have h_ne_g : s ≠ (StringGenState.gen pf σ).1 := fun h => h_nin (h ▸ List.mem_cons_self)
  have h_nin_σ : s ∉ σ.stringGens := fun h => h_nin (List.mem_cons_of_mem _ h)
  have h_ident_ne :
      HasIdent.ident (P := P) s ≠ HasIdent.ident (P := P) (StringGenState.gen pf σ).1 :=
    fun h => h_ne_g (LawfulHasIdent.ident_inj h)
  show (if HasIdent.ident (P := P) s = _ then some b else _) = none
  rw [if_neg h_ident_ne]
  exact h_fresh s h_suf h_nin_σ

/-- `GenFreshStore` strengthens as the generator advances: once more names have
been generated (`GenStep σ σ'`), there are *fewer* ungenerated gen-shaped names,
so the "ungenerated ⟹ undefined" obligation is easier to meet. -/
theorem GenFreshStore_mono {P : PureExpr} [HasIdent P]
    {Q : String → Prop}
    {σ σ' : StringGenState} {σ_tgt : SemanticStore P}
    (h_step : StringGenState.GenStep σ σ')
    (h_fresh : GenFreshStore Q σ σ_tgt) :
    GenFreshStore Q σ' σ_tgt := by
  intro s h_suf h_nin
  exact h_fresh s h_suf (fun h => h_nin (h_step.subset h))

end Freshness

/-! ### Source-shape precondition

The simulation is only sound for source programs that never `init`/`set` a
gen-shaped (`HasUnderscoreDigitSuffix`) variable.  This is carried as an
explicit assumption: the front-ends feeding this pipeline never write such
names, and a source program that re-`init`s a parent-scoped variable inside a
loop body is already stuck under the existing semantics, independent of this
pass.  Without it the theorem is false — a pass-through source
`.cmd (set "$g_0" .nondet)` defines a gen-shaped slot, after which a later
`.ite .nondet`'s inserted `init $g := *` would collide and be stuck.

We carry it as "no `Q`-kind identifier appears among the block's defined +
modified variables" (mirroring the analogous threaded freshness obligation on
`definedVars ++ initVars` / `modifiedVars`).  Membership in `++` distributes
the obligation across sequencing and recursion automatically. -/

/-- The source-shape precondition over a source block: no statement in `ss`
ever defines or modifies a `Q`-kind variable. -/
@[expose] def SrcNoGenWrites {P : PureExpr} [HasIdent P]
    (Q : String → Prop)
    (ss : List (Stmt P (Cmd P))) : Prop :=
  (∀ s : String, Q s → HasIdent.ident (P := P) s ∉ (Block.definedVars ss false ++ Block.modifiedVars ss))

/-- A single `EvalCmd` whose command writes no `Q`-kind variable preserves the
"no `Q`-kind slot is defined" invariant on its store. -/
theorem evalCmd_preserves_src_fresh {P : PureExpr} [HasFvar P] [HasFvars P]
    [HasBoolOps P] [HasIdent P] [HasVarsPure P P.Expr]
    {Q : String → Prop}
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {haf : Bool}
    (h : EvalCmd P f σ c σ' haf)
    (h_src_fresh : ∀ s, Q s →
      σ (HasIdent.ident (P := P) s) = none)
    (h_no_writes : (∀ s : String, Q s → HasIdent.ident (P := P) s ∉ (Cmd.definedVars c ++ Cmd.modifiedVars c))) :
    ∀ s, Q s →
      σ' (HasIdent.ident (P := P) s) = none := by
  intro s h_suf
  have h_none : σ (HasIdent.ident (P := P) s) = none := h_src_fresh s h_suf
  refine evalCmd_preserves_none (P := P) h h_none ?_ ?_
  · intro h_mem
    exact h_no_writes s h_suf (List.mem_append_left _ h_mem)
  · intro h_mem
    exact h_no_writes s h_suf (List.mem_append_right _ h_mem)

section CmdReplayStoreAgree

/-- Replay a source `EvalCmd` step on a target store that *agrees* with the
source (`StoreAgreement`, source-on-left — target may bind strictly more),
given every variable the command `init`s is undefined in the target.  Produces
a target post-store still agreeing with the source post-store.

The target-undefinedness at an `init` site comes from the explicit
`h_tgt_init_undef` premise; the non-init cases need no freshness, since
`StoreAgreement` supplies the expression-variable pointwise equality directly. -/
theorem cmd_replay_storeAgree {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    (f : P.Factory) (σ_src₀ σ_tgt₀ : SemanticStore P)
    (c : Cmd P) (σ_src₁ : SemanticStore P) (failed : Bool)
    (h_agree : StoreAgreement σ_src₀ σ_tgt₀)
    (h_eval : EvalCmd P f σ_src₀ c σ_src₁ failed)
    (h_wf_def : WellFormedSemanticEvalMono f)
    (h_tgt_init_undef : ∀ x ∈ Cmd.definedVars c, σ_tgt₀ x = none) :
    ∃ σ_tgt₁, EvalCmd P f σ_tgt₀ c σ_tgt₁ failed
            ∧ StoreAgreement σ_src₁ σ_tgt₁ := by
  cases h_eval with
  | eval_init heval hinit hwfvar =>
    rename_i ty md e v x
    have h_tgt_x_none : σ_tgt₀ x = none := by
      apply h_tgt_init_undef x
      show x ∈ (Cmd.init x ty (ExprOrNondet.det e) md).definedVars
      with_unfolding_all exact List.mem_singleton.mpr rfl
    have h_eval_tgt : P.eval f σ_tgt₀ e = .some v :=
      h_wf_def e v σ_src₀ σ_tgt₀ (storeAgreement_supplies_mono_premise σ_src₀ σ_tgt₀ h_agree) heval
    cases hinit with
    | init h_xn h_xv h_other =>
      let σ_tgt₁ : SemanticStore P := fun y => if y = x then some v else σ_tgt₀ y
      have h_tgt_x : σ_tgt₁ x = some v := by show (if x = x then _ else _) = _; simp
      have h_tgt_other : ∀ y, x ≠ y → σ_tgt₁ y = σ_tgt₀ y := by
        intro y hxy; show (if y = x then _ else _) = _; rw [if_neg (fun h => hxy h.symm)]
      refine ⟨σ_tgt₁, EvalCmd.eval_init h_eval_tgt (InitState.init h_tgt_x_none h_tgt_x h_tgt_other) hwfvar, ?_⟩
      intro y h_def_y
      have h_y_some : (σ_src₁ y).isSome = true := h_def_y y (List.mem_singleton.mpr rfl)
      by_cases hyx : y = x
      · subst hyx; rw [h_xv, h_tgt_x]
      · rw [h_other y (fun h => hyx h.symm)]
        rw [h_other y (fun h => hyx h.symm)] at h_y_some
        rw [h_tgt_other y (fun h => hyx h.symm)]
        exact h_agree y (fun z hz => by simpa [List.mem_singleton.mp hz] using h_y_some)
  | eval_init_unconstrained hinit hval hwfvar =>
    rename_i ty md x v
    have h_tgt_x_none : σ_tgt₀ x = none := by
      apply h_tgt_init_undef x
      show x ∈ (Cmd.init x ty (ExprOrNondet.nondet) md).definedVars
      with_unfolding_all exact List.mem_singleton.mpr rfl
    cases hinit with
    | init h_xn h_xv h_other =>
      let σ_tgt₁ : SemanticStore P := fun y => if y = x then some v else σ_tgt₀ y
      have h_tgt_x : σ_tgt₁ x = some v := by show (if x = x then _ else _) = _; simp
      have h_tgt_other : ∀ y, x ≠ y → σ_tgt₁ y = σ_tgt₀ y := by
        intro y hxy; show (if y = x then _ else _) = _; rw [if_neg (fun h => hxy h.symm)]
      refine ⟨σ_tgt₁, EvalCmd.eval_init_unconstrained (InitState.init h_tgt_x_none h_tgt_x h_tgt_other) hval hwfvar, ?_⟩
      intro y h_def_y
      have h_y_some : (σ_src₁ y).isSome = true := h_def_y y (List.mem_singleton.mpr rfl)
      by_cases hyx : y = x
      · subst hyx; rw [h_xv, h_tgt_x]
      · rw [h_other y (fun h => hyx h.symm)]
        rw [h_other y (fun h => hyx h.symm)] at h_y_some
        rw [h_tgt_other y (fun h => hyx h.symm)]
        exact h_agree y (fun z hz => by simpa [List.mem_singleton.mp hz] using h_y_some)
  | eval_set heval hupd hwfvar =>
    rename_i md e v x
    have h_eval_tgt : P.eval f σ_tgt₀ e = .some v :=
      h_wf_def e v σ_src₀ σ_tgt₀ (storeAgreement_supplies_mono_premise σ_src₀ σ_tgt₀ h_agree) heval
    cases hupd with
    | update h_xv' h_xv h_other =>
      rename_i v'
      have h_x_def_src : isDefined σ_src₀ [x] := by intro z hz; rw [List.mem_singleton.mp hz, h_xv']; rfl
      have h_tgt_x_old : σ_tgt₀ x = some v' := by rw [← h_agree x h_x_def_src]; exact h_xv'
      let σ_tgt₁ : SemanticStore P := fun y => if y = x then some v else σ_tgt₀ y
      have h_tgt_x : σ_tgt₁ x = some v := by show (if x = x then _ else _) = _; simp
      have h_tgt_other : ∀ y, x ≠ y → σ_tgt₁ y = σ_tgt₀ y := by
        intro y hxy; show (if y = x then _ else _) = _; rw [if_neg (fun h => hxy h.symm)]
      refine ⟨σ_tgt₁, EvalCmd.eval_set h_eval_tgt (UpdateState.update h_tgt_x_old h_tgt_x h_tgt_other) hwfvar, ?_⟩
      intro y h_def_y
      have h_y_some : (σ_src₁ y).isSome = true := h_def_y y (List.mem_singleton.mpr rfl)
      by_cases hyx : y = x
      · subst hyx; rw [h_xv, h_tgt_x]
      · rw [h_other y (fun h => hyx h.symm)]
        rw [h_other y (fun h => hyx h.symm)] at h_y_some
        rw [h_tgt_other y (fun h => hyx h.symm)]
        exact h_agree y (fun z hz => by simpa [List.mem_singleton.mp hz] using h_y_some)
  | eval_set_nondet hupd hval hwfvar =>
    rename_i md x v
    cases hupd with
    | update h_xv' h_xv h_other =>
      rename_i v'
      have h_x_def_src : isDefined σ_src₀ [x] := by intro z hz; rw [List.mem_singleton.mp hz, h_xv']; rfl
      have h_tgt_x_old : σ_tgt₀ x = some v' := by rw [← h_agree x h_x_def_src]; exact h_xv'
      let σ_tgt₁ : SemanticStore P := fun y => if y = x then some v else σ_tgt₀ y
      have h_tgt_x : σ_tgt₁ x = some v := by show (if x = x then _ else _) = _; simp
      have h_tgt_other : ∀ y, x ≠ y → σ_tgt₁ y = σ_tgt₀ y := by
        intro y hxy; show (if y = x then _ else _) = _; rw [if_neg (fun h => hxy h.symm)]
      refine ⟨σ_tgt₁, EvalCmd.eval_set_nondet (UpdateState.update h_tgt_x_old h_tgt_x h_tgt_other) hval hwfvar, ?_⟩
      intro y h_def_y
      have h_y_some : (σ_src₁ y).isSome = true := h_def_y y (List.mem_singleton.mpr rfl)
      by_cases hyx : y = x
      · subst hyx; rw [h_xv, h_tgt_x]
      · rw [h_other y (fun h => hyx h.symm)]
        rw [h_other y (fun h => hyx h.symm)] at h_y_some
        rw [h_tgt_other y (fun h => hyx h.symm)]
        exact h_agree y (fun z hz => by simpa [List.mem_singleton.mp hz] using h_y_some)
  | eval_assert_pass hcond hwfb =>
    rename_i l md e
    have h_eval_tgt : P.eval f σ_tgt₀ e = .some HasBool.tt :=
      h_wf_def e HasBool.tt σ_src₀ σ_tgt₀ (storeAgreement_supplies_mono_premise σ_src₀ σ_tgt₀ h_agree) hcond
    exact ⟨σ_tgt₀, EvalCmd.eval_assert_pass h_eval_tgt hwfb, h_agree⟩
  | eval_assert_fail hcond hwfb =>
    rename_i l md e
    have h_eval_tgt : P.eval f σ_tgt₀ e = .some HasBool.ff :=
      h_wf_def e HasBool.ff σ_src₀ σ_tgt₀ (storeAgreement_supplies_mono_premise σ_src₀ σ_tgt₀ h_agree) hcond
    exact ⟨σ_tgt₀, EvalCmd.eval_assert_fail h_eval_tgt hwfb, h_agree⟩
  | eval_assume hcond hwfb =>
    rename_i l md e
    have h_eval_tgt : P.eval f σ_tgt₀ e = .some HasBool.tt :=
      h_wf_def e HasBool.tt σ_src₀ σ_tgt₀ (storeAgreement_supplies_mono_premise σ_src₀ σ_tgt₀ h_agree) hcond
    exact ⟨σ_tgt₀, EvalCmd.eval_assume h_eval_tgt hwfb, h_agree⟩
  | eval_cover hwfb =>
    exact ⟨σ_tgt₀, EvalCmd.eval_cover hwfb, h_agree⟩

/-- Trace-level `.cmd` replay under `StoreAgreement`: a terminating source
`.cmd c` execution is matched by a terminating target `.cmd c` execution from
any agreeing store (matching evaluator and failure flag), provided every `init`
target of `c` is undefined in the target, with the post-stores agreeing and the
failure flags / evaluators equal. -/
theorem cmd_replay_agreement_storeAgree {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    (extendFactory : ExtendFactory P)
    (c : Cmd P) (ρ_src ρ_src' ρ_tgt : Env P)
    (h_eval_eq : ρ_tgt.factory = ρ_src.factory)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (h_wf_def : WellFormedSemanticEvalMono ρ_src.factory)
    (h_tgt_init_undef : ∀ x ∈ Cmd.definedVars c, ρ_tgt.store x = none)
    (h_term : StepStmtStar P (EvalCmd P) extendFactory
      (.stmt (.cmd c) ρ_src) (.terminal ρ_src')) :
    ∃ ρ_tgt', StepStmtStar P (EvalCmd P) extendFactory
          (.stmt (.cmd c) ρ_tgt) (.terminal ρ_tgt')
        ∧ StoreAgreement ρ_src'.store ρ_tgt'.store
        ∧ ρ_tgt'.hasFailure = ρ_src'.hasFailure
        ∧ ρ_tgt'.factory = ρ_src'.factory := by
  obtain ⟨σ', haf, h_cmd, h_eq⟩ := cmd_step_inv (extendFactory := extendFactory) c ρ_src ρ_src' h_term
  obtain ⟨σ_tgt', h_eval_tgt, h_agree'⟩ :=
    cmd_replay_storeAgree ρ_src.factory ρ_src.store ρ_tgt.store c σ' haf
      h_agree h_cmd h_wf_def h_tgt_init_undef
  have h_eval_tgt' : EvalCmd P ρ_tgt.factory ρ_tgt.store c σ_tgt' haf := h_eval_eq ▸ h_eval_tgt
  refine ⟨{ ρ_tgt with store := σ_tgt', hasFailure := ρ_tgt.hasFailure || haf },
    .step _ _ _ (StepStmt.step_cmd h_eval_tgt') (.refl _), ?_, ?_, ?_⟩
  · subst h_eq; exact h_agree'
  · subst h_eq; simp [h_fail_eq]
  · subst h_eq; exact h_eval_eq

end CmdReplayStoreAgree

/-! ## `StoreAgreement` re-thread of the nondetElim engine (`*_sa`)

**What these prove.** Each `*_sa` lemma is a forward-simulation step: given a
source run (of a statement / loop iteration / block) that reaches some outcome,
it produces a matching run of the *rewritten* program from a store-agreeing
target, and concludes (i) the two output stores still agree (`StoreAgreement`,
source-on-left) and (ii) `Q`-freshness is preserved in both.  They are the
inductive workhorses the top-level soundness theorems compose — not merely
"facts about the resulting state."

**Hypotheses beyond well-formedness.** The target's init-target undefinedness is
carried explicitly as `h_tgt_init_undef` (re-established across each loop
iteration's `projectStore` boundary, since parent-undefined keys stay `none`);
the `_gen` lemmas add a `uniqueInits`/`Nodup` premise; and the
`GenFreshStore`/`h_src_fresh` machinery quarantines the generated guard slots,
orthogonal to the source-var relation.  Each docstring below notes only what is
distinctive to that lemma. -/

/-- Deterministic-loop iteration. -/
private theorem nondetElim_loop_det_sim_iteration_sa {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (extendFactory : ExtendFactory P)
    (e : P.Expr) (m : Option P.Expr) {inv : List (String × P.Expr)}
    (body body' : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ : StringGenState)
    (h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
      ρb_tgt.factory = ρb_src.factory →
      ρb_tgt.hasFailure = ρb_src.hasFailure →
      StoreAgreement ρb_src.store ρb_tgt.store →
      WellFormedSemanticEval ρb_src.factory →
      StringGenState.WF σ →
      (∀ t, Q t →
        ρb_src.store (HasIdent.ident (P := P) t) = none) →
      GenFreshStore Q σ ρb_tgt.store →
      (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
      StepStmtStar P (EvalCmd P) extendFactory (.stmts body ρb_src) (Env.outcomeConfig oc_b ρb') →
      (∀ t, Q t →
          ρb'.store (HasIdent.ident (P := P) t) = none)
        ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P) extendFactory
            (.stmts body' ρb_tgt) (Env.outcomeConfig oc_b ρb_out)
          ∧ StoreAgreement ρb'.store ρb_out.store
          ∧ ρb_out.hasFailure = ρb'.hasFailure
          ∧ ρb_out.factory = ρb'.factory
          ∧ GenFreshStore Q σ_out ρb_out.store)
    (h_nofd_body : Block.noFuncDecl body = true)
    (oc : Option String)
    (ρ_src ρ' ρ_tgt : Env P) (n : Nat)
    (h_eval_eq : ρ_tgt.factory = ρ_src.factory)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : GenFreshStore Q σ ρ_tgt.store)
    (h_tgt_init_undef : ∀ y ∈ Block.initVars body, ρ_tgt.store y = none)
    (hstarT : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
      (.stmt (.loop (.det e) m inv body md) ρ_src) (Env.outcomeConfig oc ρ'))
    (hlen : hstarT.len ≤ n) :
    (∀ t, Q t →
        ρ'.store (HasIdent.ident (P := P) t) = none)
      ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P) extendFactory
          (.stmt (.loop (.det e) m inv body' md) ρ_tgt)
          (Env.outcomeConfig oc ρ_out)
        ∧ StoreAgreement ρ'.store ρ_out.store
        ∧ ρ_out.hasFailure = ρ'.hasFailure
        ∧ ρ_out.factory = ρ'.factory
        ∧ GenFreshStore Q σ ρ_out.store := by
  induction n generalizing oc ρ_src ρ_tgt ρ' with
  | zero =>
    rcases loop_det_step_first_inv (extendFactory := extendFactory) hstarT with
      ⟨_, _, _, hl⟩ | ⟨_, _, _, hl⟩
    · exact absurd (Nat.lt_of_lt_of_le hl hlen) (Nat.not_lt_zero _)
    · exact absurd (Nat.lt_of_lt_of_le hl hlen) (Nat.not_lt_zero _)
  | succ n ih =>
    rcases loop_det_step_first_inv (extendFactory := extendFactory) hstarT with
      ⟨h_cond, hwfb_s, hrest, hl⟩ | ⟨h_cond, hwfb_s, hrest, hl⟩
    · have hlen : hstarT.len ≤ n + 1 := hlen
      cases oc with
      | none =>
        simp only [Env.outcomeConfig] at hrest ⊢
        have hρ'_eq : ρ' = ρ_src := by
          match hrest with
          | .refl _ => rfl
          | .step _ _ _ h _ => exact nomatch h
        have h_cond_t : P.eval ρ_tgt.factory ρ_tgt.store e = some HasBool.ff := by
          rw [h_eval_eq]
          exact hwf.mono e HasBool.ff ρ_src.store ρ_tgt.store
            (storeAgreement_supplies_mono_premise ρ_src.store ρ_tgt.store h_agree) h_cond
        subst hρ'_eq
        refine ⟨h_src_fresh, ρ_tgt, ?_, ?_, ?_, ?_, ?_⟩
        · exact .step _ _ _ (StepStmt.step_loop_exit
            h_cond_t (h_eval_eq ▸ hwf.bool)) (.refl _)
        · simpa using h_agree
        · simp [h_fail_eq]
        · simpa using h_eval_eq
        · simpa using h_tgt_fresh
      | some lbl =>
        exfalso
        simp only [Env.outcomeConfig] at hrest
        match hrest with
        | .step _ _ _ h _ => exact nomatch h
    · have hlen : hstarT.len ≤ n + 1 := hlen
      have h_cond_t : P.eval ρ_tgt.factory ρ_tgt.store e = some HasBool.tt := by
        rw [h_eval_eq]
        exact hwf.mono e HasBool.tt ρ_src.store ρ_tgt.store
          (storeAgreement_supplies_mono_premise ρ_src.store ρ_tgt.store h_agree) h_cond
      have h_block_tgt_to : ∀ (ρb_tgt : Env P),
          StepStmtStar P (EvalCmd P) extendFactory
            (.stmts body' ρ_tgt)
            (.terminal ρb_tgt) →
          StepStmtStar P (EvalCmd P) extendFactory
            (.block .none ρ_tgt.store ρ_tgt.factory (.stmts body' ρ_tgt))
            (.terminal ({ ρb_tgt with store := projectStore ρ_tgt.store ρb_tgt.store, factory := ρ_tgt.factory } : Env P)) := by
        intro ρb_tgt h_run
        refine ReflTrans_Transitive _ _ _ _
          (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_tgt.store ρ_tgt.factory h_run) ?_
        exact .step _ _ _ StepStmt.step_block_done (.refl _)
      cases oc with
      | none =>
        simp only [Env.outcomeConfig] at hrest ⊢
        have hl : hrest.len < hstarT.len := hl
        have ⟨ρ_block, h_block_term, h_loop_stmts, hlen_seq⟩ :=
          seqT_reaches_terminal (extendFactory := extendFactory) hrest
        have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
          blockT_none_reaches_terminal (extendFactory := extendFactory) h_block_term
        have ⟨ρ_x, h_loop_T_T, h_nil, hlen_cons⟩ :=
          stmtsT_cons_terminal (extendFactory := extendFactory) h_loop_stmts
        have hρ_x_eq : ρ_x = ρ' := by
          match h_nil with
          | .step _ _ _ .step_stmts_nil hr2 =>
            match hr2 with
            | .refl _ => rfl
            | .step _ _ _ h _ => exact nomatch h
        subst hρ_x_eq
        have h_body_run : StepStmtStar P (EvalCmd P) extendFactory
            (.stmts body ρ_src) (Env.outcomeConfig none ρ_inner) :=
          reflTransT_to_prop h_inner_term
        obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner,
            h_eval_inner, h_fresh_inner⟩ :=
          h_body_sim none ρ_src ρ_inner ρ_tgt h_eval_eq h_fail_eq h_agree hwf
            h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef h_body_run
        have h_eval_inner_src : ρ_inner.factory = ρ_src.factory :=
          block_noFuncDecl_preserves_factory P (EvalCmd P) extendFactory body ρ_src ρ_inner h_nofd_body
            (by simpa only [Env.outcomeConfig] using h_body_run)
        have heq_ρ_block_full :
            ρ_block = ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store, factory := ρ_src.factory } : Env P) := by
          rw [heq_ρ_block]
        subst heq_ρ_block_full
        let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store, factory := ρ_src.factory }
        let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store, factory := ρ_tgt.factory }
        have h_eval_next : ρ_src_next.factory = ρ_src.factory := rfl
        have hwf_next : WellFormedSemanticEval ρ_src_next.factory := by rw [h_eval_next]; exact hwf
        have h_eval_eq_next : ρ_tgt_next.factory = ρ_src_next.factory := by
          show ρ_tgt.factory = ρ_src.factory; exact h_eval_eq
        have h_fail_eq_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
          show ρ_inner_tgt.hasFailure = ρ_inner.hasFailure; exact h_fail_inner
        have h_agree_next : StoreAgreement ρ_src_next.store ρ_tgt_next.store :=
          StoreAgreement.of_projectStore_parents h_agree h_off_inner
        have h_src_fresh_next : ∀ t, Q t →
            ρ_src_next.store (HasIdent.ident (P := P) t) = none := by
          intro t h_suf
          show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
          show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
              then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
          by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
          · rw [if_pos hp]; exact h_inner_fresh t h_suf
          · rw [if_neg hp]
        have h_tgt_fresh_next : GenFreshStore Q σ ρ_tgt_next.store := by
          intro s h_suf h_notin
          show projectStore ρ_tgt.store ρ_inner_tgt.store (HasIdent.ident (P := P) s) = none
          show (if (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
              then ρ_inner_tgt.store (HasIdent.ident (P := P) s) else none) = none
          rw [h_tgt_fresh s h_suf h_notin]; rfl
        have h_tgt_init_undef_next : ∀ y ∈ Block.initVars body, ρ_tgt_next.store y = none := by
          intro y hy
          show projectStore ρ_tgt.store ρ_inner_tgt.store y = none
          show (if (ρ_tgt.store y).isSome then ρ_inner_tgt.store y else none) = none
          rw [h_tgt_init_undef y hy]; rfl
        have hlen_tail : h_loop_T_T.len ≤ n := by omega
        obtain ⟨h_fresh', ρ_out, h_loop_tgt, h_off', h_fail', h_eval', h_fresh_out⟩ :=
          ih (oc := none) (ρ_src := ρ_src_next) (ρ' := ρ_x) (ρ_tgt := ρ_tgt_next)
            h_eval_eq_next h_fail_eq_next h_agree_next
            hwf_next
            h_src_fresh_next h_tgt_fresh_next h_tgt_init_undef_next h_loop_T_T hlen_tail
        simp only [Env.outcomeConfig] at h_loop_tgt
        refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', h_fresh_out⟩
        refine .step _ _ _ (StepStmt.step_loop_enter
          h_cond_t (h_eval_eq ▸ hwf.bool)) ?_
        have h_body_tgt' : StepStmtStar P (EvalCmd P) extendFactory
            (.stmts body' ρ_tgt)
            (.terminal ρ_inner_tgt) := by
          simpa only [Env.outcomeConfig] using h_body_tgt
        refine ReflTrans_Transitive _ _ _ _
          (ReflTrans_Transitive _ _ _ _
            (seq_inner_star P (EvalCmd P) extendFactory _ _ _ (h_block_tgt_to ρ_inner_tgt h_body_tgt'))
            (.step _ _ _ StepStmt.step_seq_done (.refl _)))
          (ReflTrans_Transitive _ _ _ _
            (stmts_cons_step P (EvalCmd P) extendFactory _ _ ρ_tgt_next ρ_out h_loop_tgt)
            (.step _ _ _ StepStmt.step_stmts_nil (.refl _)))
      | some lbl =>
        simp only [Env.outcomeConfig] at hrest ⊢
        have hl : hrest.len < hstarT.len := hl
        rcases seqT_reaches_exiting (extendFactory := extendFactory) hrest with
          ⟨h_block_exit, hlen_be⟩ | ⟨ρ_block, h_block_term, h_loop_exit, hlen_te⟩
        · have ⟨ρ_inner, h_inner_exit, heq_ρ', hlen_inner⟩ :=
            blockT_none_reaches_exiting (extendFactory := extendFactory) h_block_exit
          have h_body_run : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts body ρ_src) (Env.outcomeConfig (some lbl) ρ_inner) :=
            reflTransT_to_prop h_inner_exit
          obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner,
              h_eval_inner, h_fresh_inner⟩ :=
            h_body_sim (some lbl) ρ_src ρ_inner ρ_tgt h_eval_eq h_fail_eq h_agree hwf
              h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef h_body_run
          subst heq_ρ'
          refine ⟨?_, ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store, factory := ρ_tgt.factory } : Env P),
            ?_, ?_, ?_, ?_, ?_⟩
          · intro t h_suf
            show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
            show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
                then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
            by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
            · rw [if_pos hp]; exact h_inner_fresh t h_suf
            · rw [if_neg hp]
          · refine .step _ _ _ (StepStmt.step_loop_enter
              h_cond_t (h_eval_eq ▸ hwf.bool)) ?_
            have h_body_tgt' : StepStmtStar P (EvalCmd P) extendFactory
                (.stmts body' ρ_tgt)
                (.exiting lbl ρ_inner_tgt) := by
              simpa only [Env.outcomeConfig] using h_body_tgt
            have h_block_tgt_exit : StepStmtStar P (EvalCmd P) extendFactory
                (.block .none ρ_tgt.store ρ_tgt.factory (.stmts body' ρ_tgt))
                (.exiting lbl ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store, factory := ρ_tgt.factory } : Env P)) := by
              refine ReflTrans_Transitive _ _ _ _
                (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_tgt.store ρ_tgt.factory h_body_tgt') ?_
              exact .step _ _ _ (StepStmt.step_block_exit_mismatch (by simp)) (.refl _)
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_block_tgt_exit) ?_
            exact .step _ _ _ StepStmt.step_seq_exit (.refl _)
          · exact StoreAgreement.of_projectStore_parents h_agree h_off_inner
          · exact h_fail_inner
          · show ρ_tgt.factory = ρ_src.factory; exact h_eval_eq
          · intro s h_suf h_notin
            show projectStore ρ_tgt.store ρ_inner_tgt.store (HasIdent.ident (P := P) s) = none
            show (if (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
                then ρ_inner_tgt.store (HasIdent.ident (P := P) s) else none) = none
            rw [h_tgt_fresh s h_suf h_notin]; rfl
        · have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
            blockT_none_reaches_terminal (extendFactory := extendFactory) h_block_term
          have ⟨h_loop_T_exit, hlen_cons⟩ :=
            stmtsT_singleton_exiting (extendFactory := extendFactory) h_loop_exit
          have h_body_run : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts body ρ_src) (Env.outcomeConfig none ρ_inner) :=
            reflTransT_to_prop h_inner_term
          obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner,
              h_eval_inner, h_fresh_inner⟩ :=
            h_body_sim none ρ_src ρ_inner ρ_tgt h_eval_eq h_fail_eq h_agree hwf
              h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef h_body_run
          have h_eval_inner_src : ρ_inner.factory = ρ_src.factory :=
            block_noFuncDecl_preserves_factory P (EvalCmd P) extendFactory body ρ_src ρ_inner h_nofd_body
              (by simpa only [Env.outcomeConfig] using h_body_run)
          have heq_ρ_block_full :
              ρ_block = ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store, factory := ρ_src.factory } : Env P) := by
            rw [heq_ρ_block]
          subst heq_ρ_block_full
          let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store, factory := ρ_src.factory }
          let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store, factory := ρ_tgt.factory }
          have h_eval_next : ρ_src_next.factory = ρ_src.factory := rfl
          have hwf_next : WellFormedSemanticEval ρ_src_next.factory := by rw [h_eval_next]; exact hwf
          have h_eval_eq_next : ρ_tgt_next.factory = ρ_src_next.factory := by
            show ρ_tgt.factory = ρ_src.factory; exact h_eval_eq
          have h_fail_eq_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
            show ρ_inner_tgt.hasFailure = ρ_inner.hasFailure; exact h_fail_inner
          have h_agree_next : StoreAgreement ρ_src_next.store ρ_tgt_next.store :=
            StoreAgreement.of_projectStore_parents h_agree h_off_inner
          have h_src_fresh_next : ∀ t, Q t →
              ρ_src_next.store (HasIdent.ident (P := P) t) = none := by
            intro t h_suf
            show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
            show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
                then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
            by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
            · rw [if_pos hp]; exact h_inner_fresh t h_suf
            · rw [if_neg hp]
          have h_tgt_fresh_next : GenFreshStore Q σ ρ_tgt_next.store := by
            intro s h_suf h_notin
            show projectStore ρ_tgt.store ρ_inner_tgt.store (HasIdent.ident (P := P) s) = none
            show (if (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
                then ρ_inner_tgt.store (HasIdent.ident (P := P) s) else none) = none
            rw [h_tgt_fresh s h_suf h_notin]; rfl
          have h_tgt_init_undef_next : ∀ y ∈ Block.initVars body, ρ_tgt_next.store y = none := by
            intro y hy
            show projectStore ρ_tgt.store ρ_inner_tgt.store y = none
            show (if (ρ_tgt.store y).isSome then ρ_inner_tgt.store y else none) = none
            rw [h_tgt_init_undef y hy]; rfl
          have hlen_tail : h_loop_T_exit.len ≤ n := by omega
          obtain ⟨h_fresh', ρ_out, h_loop_tgt, h_off', h_fail', h_eval', h_fresh_out⟩ :=
            ih (oc := some lbl) (ρ_src := ρ_src_next) (ρ' := ρ') (ρ_tgt := ρ_tgt_next)
              h_eval_eq_next h_fail_eq_next h_agree_next
              hwf_next
              h_src_fresh_next h_tgt_fresh_next h_tgt_init_undef_next h_loop_T_exit hlen_tail
          simp only [Env.outcomeConfig] at h_loop_tgt
          refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', h_fresh_out⟩
          refine .step _ _ _ (StepStmt.step_loop_enter
            h_cond_t (h_eval_eq ▸ hwf.bool)) ?_
          have h_body_tgt' : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts body' ρ_tgt)
              (.terminal ρ_inner_tgt) := by
            simpa only [Env.outcomeConfig] using h_body_tgt
          have h_loop_stmts_exit : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts [.loop (.det e) m inv body' md] ρ_tgt_next)
              (.exiting lbl ρ_out) := by
            refine .step _ _ _ StepStmt.step_stmts_cons ?_
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_loop_tgt) ?_
            exact .step _ _ _ StepStmt.step_seq_exit (.refl _)
          refine ReflTrans_Transitive _ _ _ _
            (ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _ (h_block_tgt_to ρ_inner_tgt h_body_tgt'))
              (.step _ _ _ StepStmt.step_seq_done (.refl _)))
            h_loop_stmts_exit

/-- When the rewritten loop's fresh guard is already `ff`, a terminating source
run of the loop is matched by the target det-loop taking its exit branch
immediately: the resulting stores still agree and every `Q`-name stays fresh.
(The nondet-loop EXIT case; used by both fuel cases of the iteration lemma.) -/
private theorem loop_nondet_exit_close_sa {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (extendFactory : ExtendFactory P)
    (ident : P.Ident) (m : Option P.Expr) {inv : List (String × P.Expr)}
    (body' : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ : StringGenState)
    (oc : Option String)
    (ρ_src ρ' ρ_tgt : Env P)
    (h_eval_eq : ρ_tgt.factory = ρ_src.factory)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : GenFreshStore Q σ ρ_tgt.store)
    (h_guard_def : ρ_tgt.store ident = some HasBool.ff)
    (hrest : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
      (.terminal ρ_src)
      (Env.outcomeConfig oc ρ')) :
    (∀ t, Q t →
        ρ'.store (HasIdent.ident (P := P) t) = none)
      ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P) extendFactory
          (.stmt (.loop (.det (HasFvar.mkFvar ident)) m inv
            (body' ++ [.cmd (HasHavoc.havoc ident md)]) md) ρ_tgt)
          (Env.outcomeConfig oc ρ_out)
        ∧ StoreAgreement ρ'.store ρ_out.store
        ∧ ρ_out.hasFailure = ρ'.hasFailure
        ∧ ρ_out.factory = ρ'.factory
        ∧ GenFreshStore Q σ ρ_out.store := by
  cases oc with
  | some lbl =>
    exfalso
    simp only [Env.outcomeConfig] at hrest
    match hrest with
    | .step _ _ _ h _ => exact nomatch h
  | none =>
    simp only [Env.outcomeConfig] at hrest ⊢
    have hρ'_eq : ρ' = ρ_src := by
      match hrest with
      | .refl _ => rfl
      | .step _ _ _ h _ => exact nomatch h
    have h_guard_ff : P.eval ρ_tgt.factory ρ_tgt.store (HasFvar.mkFvar ident) = some HasBool.ff := by
      rw [h_eval_eq]
      exact eval_mkFvar_of_value ρ_src.factory ρ_tgt.store ident HasBool.ff
        (HasBool.boolIsVal ρ_src.factory).2 h_guard_def hwf.var hwf.mono
    subst hρ'_eq
    refine ⟨h_src_fresh, ρ_tgt, ?_, ?_, ?_, ?_, ?_⟩
    · exact .step _ _ _ (StepStmt.step_loop_exit
        h_guard_ff (h_eval_eq ▸ hwf.bool)) (.refl _)
    · exact h_agree
    · exact h_fail_eq
    · exact h_eval_eq
    · exact h_tgt_fresh

/-- Nondeterministic-loop iteration (fuel-bounded induction on the source run). -/
private theorem nondetElim_loop_nondet_sim_iteration_sa {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (extendFactory : ExtendFactory P)
    (g : String) (m : Option P.Expr) {inv : List (String × P.Expr)}
    (body body' : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ σ_out : StringGenState)
    (h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
      ρb_tgt.factory = ρb_src.factory →
      ρb_tgt.hasFailure = ρb_src.hasFailure →
      StoreAgreement ρb_src.store ρb_tgt.store →
      WellFormedSemanticEval ρb_src.factory →
      StringGenState.WF σ →
      (∀ t, Q t →
        ρb_src.store (HasIdent.ident (P := P) t) = none) →
      GenFreshStore Q σ ρb_tgt.store →
      (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
      StepStmtStar P (EvalCmd P) extendFactory (.stmts body ρb_src) (Env.outcomeConfig oc_b ρb') →
      (∀ t, Q t →
          ρb'.store (HasIdent.ident (P := P) t) = none)
        ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P) extendFactory
            (.stmts body' ρb_tgt) (Env.outcomeConfig oc_b ρb_out)
          ∧ StoreAgreement ρb'.store ρb_out.store
          ∧ ρb_out.hasFailure = ρb'.hasFailure
          ∧ ρb_out.factory = ρb'.factory
          ∧ GenFreshStore Q σ_out ρb_out.store)
    (h_g_gen : Q g)
    (_h_g_in : g ∈ σ.stringGens)
    (h_nofd_body : Block.noFuncDecl body = true)
    (oc : Option String)
    (ρ_src ρ' ρ_tgt : Env P) (n : Nat)
    (h_eval_eq : ρ_tgt.factory = ρ_src.factory)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : GenFreshStore Q σ ρ_tgt.store)
    (h_tgt_init_undef : ∀ y ∈ Block.initVars body, ρ_tgt.store y = none)
    (entering : Bool)
    (h_guard_def : ρ_tgt.store (HasIdent.ident (P := P) g)
      = some (if entering then HasBool.tt else HasBool.ff))
    (h_src_first :
      (entering = false ∧ ∃ (hrest : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
          (.terminal ρ_src)
          (Env.outcomeConfig oc ρ')), hrest.len ≤ n) ∨
      (entering = true ∧ ∃ (hrest : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
          (.seq (.block .none ρ_src.store ρ_src.factory (.stmts body ρ_src))
            [.loop .nondet m inv body md])
          (Env.outcomeConfig oc ρ')), hrest.len ≤ n)) :
    (∀ t, Q t →
        ρ'.store (HasIdent.ident (P := P) t) = none)
      ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P) extendFactory
          (.stmt (.loop (.det (HasFvar.mkFvar (HasIdent.ident (P := P) g))) m
            inv
            (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md) ρ_tgt)
          (Env.outcomeConfig oc ρ_out)
        ∧ StoreAgreement ρ'.store ρ_out.store
        ∧ ρ_out.hasFailure = ρ'.hasFailure
        ∧ ρ_out.factory = ρ'.factory
        ∧ GenFreshStore Q σ ρ_out.store := by
  induction n generalizing oc ρ_src ρ_tgt ρ' entering with
  | zero =>
    rcases h_src_first with ⟨h_ent, hrest, hl⟩ | ⟨h_ent, hrest, hl⟩
    · subst h_ent
      simp only [Bool.false_eq_true, if_false] at h_guard_def
      exact loop_nondet_exit_close_sa extendFactory (HasIdent.ident (P := P) g) m body' md σ
        oc ρ_src ρ' ρ_tgt h_eval_eq h_fail_eq h_agree hwf
        h_src_fresh h_tgt_fresh h_guard_def hrest
    · exfalso
      subst h_ent
      cases oc <;> simp only [Env.outcomeConfig] at hrest <;>
        (match hrest with
         | .step _ _ _ _ _ => simp only [ReflTransT.len] at hl; omega)
  | succ n ih =>
    rcases h_src_first with ⟨h_ent, hrest, hl⟩ | ⟨h_ent, hrest, hl⟩
    · subst h_ent
      simp only [Bool.false_eq_true, if_false] at h_guard_def
      exact loop_nondet_exit_close_sa extendFactory (HasIdent.ident (P := P) g) m body' md σ
        oc ρ_src ρ' ρ_tgt h_eval_eq h_fail_eq h_agree hwf
        h_src_fresh h_tgt_fresh h_guard_def hrest
    · subst h_ent
      simp only [if_true] at h_guard_def
      -- Guard reads tt in target (via mkFvar / h_guard_def).
      have h_guard_tt : P.eval ρ_tgt.factory ρ_tgt.store (HasFvar.mkFvar (HasIdent.ident (P := P) g))
          = some HasBool.tt := by
        rw [h_eval_eq]
        exact eval_mkFvar_of_value ρ_src.factory ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt
          (HasBool.boolIsVal ρ_src.factory).1 h_guard_def hwf.var hwf.mono
      have hwf_var_t : WellFormedSemanticEvalVar ρ_tgt.factory := h_eval_eq ▸ hwf.var
      cases oc with
      | none =>
        simp only [Env.outcomeConfig] at hrest ⊢
        have hl : hrest.len ≤ n + 1 := hl
        have ⟨ρ_block, h_block_term, h_loop_stmts, hlen_seq⟩ :=
          seqT_reaches_terminal (extendFactory := extendFactory) hrest
        have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
          blockT_none_reaches_terminal (extendFactory := extendFactory) h_block_term
        have ⟨ρ_x, h_loop_T_T, h_nil, hlen_cons⟩ :=
          stmtsT_cons_terminal (extendFactory := extendFactory) h_loop_stmts
        have hρ_x_eq : ρ_x = ρ' := by
          match h_nil with
          | .step _ _ _ .step_stmts_nil hr2 =>
            match hr2 with
            | .refl _ => rfl
            | .step _ _ _ h _ => exact nomatch h
        subst hρ_x_eq
        have h_body_run : StepStmtStar P (EvalCmd P) extendFactory
            (.stmts body ρ_src) (Env.outcomeConfig none ρ_inner) :=
          reflTransT_to_prop h_inner_term
        obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner,
            h_eval_inner, h_fresh_inner⟩ :=
          h_body_sim none ρ_src ρ_inner ρ_tgt h_eval_eq h_fail_eq h_agree hwf
            h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef h_body_run
        have h_eval_inner_src : ρ_inner.factory = ρ_src.factory :=
          block_noFuncDecl_preserves_factory P (EvalCmd P) extendFactory body ρ_src ρ_inner h_nofd_body
            (by simpa only [Env.outcomeConfig] using h_body_run)
        have heq_ρ_block_full :
            ρ_block = ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store, factory := ρ_src.factory } : Env P) := by
          rw [heq_ρ_block]
        subst heq_ρ_block_full
        -- $g stays defined in ρ_inner_tgt (it was defined in ρ_tgt).
        have h_g_some_tgt : (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome = true := by
          rw [h_guard_def]; rfl
        have h_body_tgt_term : StepStmtStar P (EvalCmd P) extendFactory
            (.stmts body' ρ_tgt)
            (.terminal ρ_inner_tgt) := by
          simpa only [Env.outcomeConfig] using h_body_tgt
        have h_g_some_inner : (ρ_inner_tgt.store (HasIdent.ident (P := P) g)).isSome = true := by
          have := stmts_preserves_isSome (extendFactory := extendFactory) h_body_tgt_term
            (y := HasIdent.ident (P := P) g)
          exact this h_g_some_tgt
        obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp h_g_some_inner
        -- Invert the loop tail to learn the NEXT source decision.
        rcases loop_nondet_step_first_inv (extendFactory := extendFactory) (oc := none)
            h_loop_T_T with
          ⟨hrest_next, hlen_next⟩ | ⟨hrest_next, hlen_next⟩
        · -- NEXT = EXIT: re-havoc $g := ff.
          have hwf_var_inner : WellFormedSemanticEvalVar ρ_inner_tgt.factory := by
            rw [h_eval_inner, h_eval_inner_src]; exact hwf.var
          -- Build the per-iteration block run: body' to ρ_inner_tgt, then havoc $g := ff.
          have h_tail : StepStmtStar P (EvalCmd P) extendFactory
              (.stmt (.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)) ρ_inner_tgt)
              (.terminal ({ ρ_inner_tgt with store := SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.ff } : Env P)) :=
            step_havoc_set_to (extendFactory := extendFactory) (HasIdent.ident (P := P) g) HasBool.ff md ρ_inner_tgt v' hv'
              (HasBool.boolIsVal ρ_inner_tgt.factory).2 hwf_var_inner
          have h_body_tail : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt)
              (.terminal ({ ρ_inner_tgt with store := SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.ff } : Env P)) :=
            ReflTrans_Transitive _ _ _ _
              (stmts_prefix_terminal_append P (EvalCmd P) extendFactory _ _ _ ρ_inner_tgt h_body_tgt_term)
              (stmt_to_singleton_stmts (extendFactory := extendFactory) _ ρ_inner_tgt _ h_tail)
          let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store (SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.ff), factory := ρ_tgt.factory }
          let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store, factory := ρ_src.factory }
          -- $g slot in ρ_tgt_next.
          have h_guard_next : ρ_tgt_next.store (HasIdent.ident (P := P) g) = some HasBool.ff := by
            show (if (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome
                then SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.ff
                  (HasIdent.ident (P := P) g) else none) = some HasBool.ff
            rw [if_pos h_g_some_tgt]; simp [SemanticStore.update]
          -- WF facts and agreements at the projected envs.
          have h_eval_next : ρ_src_next.factory = ρ_src.factory := rfl
          have hwf_next : WellFormedSemanticEval ρ_src_next.factory := by rw [h_eval_next]; exact hwf
          have h_eval_eq_next : ρ_tgt_next.factory = ρ_src_next.factory := by
            show ρ_tgt.factory = ρ_src.factory; exact h_eval_eq
          have h_fail_eq_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
            show ρ_inner_tgt.hasFailure = ρ_inner.hasFailure; exact h_fail_inner
          have h_agree_next : StoreAgreement ρ_src_next.store ρ_tgt_next.store :=
            StoreAgreement.of_projectStore_parents h_agree
              (storeAgreement_storeWith _ _ _ _ h_off_inner (h_inner_fresh g h_g_gen))
          have h_src_fresh_next : ∀ t, Q t →
              ρ_src_next.store (HasIdent.ident (P := P) t) = none := by
            intro t h_suf
            show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
                then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
            by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
            · rw [if_pos hp]; exact h_inner_fresh t h_suf
            · rw [if_neg hp]
          have h_tgt_fresh_next : GenFreshStore Q σ ρ_tgt_next.store := by
            intro s h_suf h_notin
            show (if (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
                then SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.ff
                  (HasIdent.ident (P := P) s) else none) = none
            rw [h_tgt_fresh s h_suf h_notin]; rfl
          have h_tgt_init_undef_next : ∀ y ∈ Block.initVars body, ρ_tgt_next.store y = none := by
            intro y hy
            show projectStore ρ_tgt.store
                (SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) y = none
            show (if (ρ_tgt.store y).isSome
                then SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.ff y
                else none) = none
            rw [h_tgt_init_undef y hy]; rfl
          -- Recurse with entering = false (exit) at smaller fuel.  `h_loop_T_T.len`
          -- shares its atom across the cons/seq bounds (no cast), so bound it
          -- first; the inversion's `< h_loop_T_T.len` then chains by defeq.
          have h_bound : h_loop_T_T.len ≤ n := by omega
          have hlen_tail : hrest_next.len ≤ n :=
            Nat.le_of_lt (Nat.lt_of_lt_of_le hlen_next h_bound)
          obtain ⟨h_fresh', ρ_out, h_loop_tgt, h_off', h_fail', h_eval', h_fresh_out⟩ :=
            ih (oc := none) (ρ_src := ρ_src_next) (ρ' := ρ_x) (ρ_tgt := ρ_tgt_next)
              h_eval_eq_next h_fail_eq_next h_agree_next
              hwf_next
              h_src_fresh_next h_tgt_fresh_next h_tgt_init_undef_next false h_guard_next
              (.inl ⟨rfl, hrest_next, hlen_tail⟩)
          simp only [Env.outcomeConfig] at h_loop_tgt
          refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', h_fresh_out⟩
          -- Assemble: enter (guard tt), block runs body'++[havoc], step_seq_done, recurse.
          refine .step _ _ _ (StepStmt.step_loop_enter
            h_guard_tt (h_eval_eq ▸ hwf.bool)) ?_
          have h_block_run : StepStmtStar P (EvalCmd P) extendFactory
              (.block .none ρ_tgt.store ρ_tgt.factory (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt))
              (.terminal ρ_tgt_next) := by
            refine ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_tgt.store ρ_tgt.factory h_body_tail) ?_
            exact .step _ _ _ StepStmt.step_block_done (.refl _)
          refine ReflTrans_Transitive _ _ _ _
            (ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_block_run)
              (.step _ _ _ StepStmt.step_seq_done (.refl _)))
            (ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P (EvalCmd P) extendFactory _ _ ρ_tgt_next ρ_out h_loop_tgt)
              (.step _ _ _ StepStmt.step_stmts_nil (.refl _)))
        · -- NEXT = ENTER: re-havoc $g := tt.
          have hwf_var_inner : WellFormedSemanticEvalVar ρ_inner_tgt.factory := by
            rw [h_eval_inner, h_eval_inner_src]; exact hwf.var
          have h_tail : StepStmtStar P (EvalCmd P) extendFactory
              (.stmt (.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)) ρ_inner_tgt)
              (.terminal ({ ρ_inner_tgt with store := SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P)) :=
            step_havoc_set_to (extendFactory := extendFactory) (HasIdent.ident (P := P) g) HasBool.tt md ρ_inner_tgt v' hv'
              (HasBool.boolIsVal ρ_inner_tgt.factory).1 hwf_var_inner
          have h_body_tail : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt)
              (.terminal ({ ρ_inner_tgt with store := SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P)) :=
            ReflTrans_Transitive _ _ _ _
              (stmts_prefix_terminal_append P (EvalCmd P) extendFactory _ _ _ ρ_inner_tgt h_body_tgt_term)
              (stmt_to_singleton_stmts (extendFactory := extendFactory) _ ρ_inner_tgt _ h_tail)
          let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store (SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt), factory := ρ_tgt.factory }
          let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store, factory := ρ_src.factory }
          have h_guard_next : ρ_tgt_next.store (HasIdent.ident (P := P) g) = some HasBool.tt := by
            show (if (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome
                then SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt
                  (HasIdent.ident (P := P) g) else none) = some HasBool.tt
            rw [if_pos h_g_some_tgt]; simp [SemanticStore.update]
          have h_eval_next : ρ_src_next.factory = ρ_src.factory := rfl
          have hwf_next : WellFormedSemanticEval ρ_src_next.factory := by rw [h_eval_next]; exact hwf
          have h_eval_eq_next : ρ_tgt_next.factory = ρ_src_next.factory := by
            show ρ_tgt.factory = ρ_src.factory; exact h_eval_eq
          have h_fail_eq_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
            show ρ_inner_tgt.hasFailure = ρ_inner.hasFailure; exact h_fail_inner
          have h_agree_next : StoreAgreement ρ_src_next.store ρ_tgt_next.store :=
            StoreAgreement.of_projectStore_parents h_agree
              (storeAgreement_storeWith _ _ _ _ h_off_inner (h_inner_fresh g h_g_gen))
          have h_src_fresh_next : ∀ t, Q t →
              ρ_src_next.store (HasIdent.ident (P := P) t) = none := by
            intro t h_suf
            show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
                then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
            by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
            · rw [if_pos hp]; exact h_inner_fresh t h_suf
            · rw [if_neg hp]
          have h_tgt_fresh_next : GenFreshStore Q σ ρ_tgt_next.store := by
            intro s h_suf h_notin
            show (if (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
                then SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt
                  (HasIdent.ident (P := P) s) else none) = none
            rw [h_tgt_fresh s h_suf h_notin]; rfl
          have h_tgt_init_undef_next : ∀ y ∈ Block.initVars body, ρ_tgt_next.store y = none := by
            intro y hy
            show projectStore ρ_tgt.store
                (SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) y = none
            show (if (ρ_tgt.store y).isSome
                then SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt y
                else none) = none
            rw [h_tgt_init_undef y hy]; rfl
          have h_bound : h_loop_T_T.len ≤ n := by omega
          have hlen_tail : hrest_next.len ≤ n :=
            Nat.le_of_lt (Nat.lt_of_lt_of_le hlen_next h_bound)
          obtain ⟨h_fresh', ρ_out, h_loop_tgt, h_off', h_fail', h_eval', h_fresh_out⟩ :=
            ih (oc := none) (ρ_src := ρ_src_next) (ρ' := ρ_x) (ρ_tgt := ρ_tgt_next)
              h_eval_eq_next h_fail_eq_next h_agree_next
              hwf_next
              h_src_fresh_next h_tgt_fresh_next h_tgt_init_undef_next true h_guard_next
              (.inr ⟨rfl, hrest_next, hlen_tail⟩)
          simp only [Env.outcomeConfig] at h_loop_tgt
          refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', h_fresh_out⟩
          refine .step _ _ _ (StepStmt.step_loop_enter
            h_guard_tt (h_eval_eq ▸ hwf.bool)) ?_
          have h_block_run : StepStmtStar P (EvalCmd P) extendFactory
              (.block .none ρ_tgt.store ρ_tgt.factory (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt))
              (.terminal ρ_tgt_next) := by
            refine ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_tgt.store ρ_tgt.factory h_body_tail) ?_
            exact .step _ _ _ StepStmt.step_block_done (.refl _)
          refine ReflTrans_Transitive _ _ _ _
            (ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_block_run)
              (.step _ _ _ StepStmt.step_seq_done (.refl _)))
            (ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P (EvalCmd P) extendFactory _ _ ρ_tgt_next ρ_out h_loop_tgt)
              (.step _ _ _ StepStmt.step_stmts_nil (.refl _)))
      | some lbl =>
        simp only [Env.outcomeConfig] at hrest ⊢
        have hl : hrest.len ≤ n + 1 := hl
        rcases seqT_reaches_exiting (extendFactory := extendFactory) hrest with
          ⟨h_block_exit, hlen_be⟩ | ⟨ρ_block, h_block_term, h_loop_exit, hlen_te⟩
        · -- Body-block exits with lbl: the body exits, propagated past the loop.
          have ⟨ρ_inner, h_inner_exit, heq_ρ', hlen_inner⟩ :=
            blockT_none_reaches_exiting (extendFactory := extendFactory) h_block_exit
          have h_body_run : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts body ρ_src) (Env.outcomeConfig (some lbl) ρ_inner) :=
            reflTransT_to_prop h_inner_exit
          obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner,
              h_eval_inner, h_fresh_inner⟩ :=
            h_body_sim (some lbl) ρ_src ρ_inner ρ_tgt h_eval_eq h_fail_eq h_agree hwf
              h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef h_body_run
          subst heq_ρ'
          refine ⟨?_, ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store, factory := ρ_tgt.factory } : Env P),
            ?_, ?_, ?_, ?_, ?_⟩
          · intro t h_suf
            show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
                then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
            by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
            · rw [if_pos hp]; exact h_inner_fresh t h_suf
            · rw [if_neg hp]
          · -- Target: enter (guard tt), body' exits lbl inside the block; the
            -- trailing havoc is skipped (the body' exit propagates), block
            -- mismatch (.none), seq exit skips the loop tail.
            refine .step _ _ _ (StepStmt.step_loop_enter
              h_guard_tt (h_eval_eq ▸ hwf.bool)) ?_
            have h_body_tgt' : StepStmtStar P (EvalCmd P) extendFactory
                (.stmts body' ρ_tgt)
                (.exiting lbl ρ_inner_tgt) := by
              simpa only [Env.outcomeConfig] using h_body_tgt
            -- body' ++ [havoc] exits lbl (the prefix exits, suffix skipped).
            have h_body_tail_exit : StepStmtStar P (EvalCmd P) extendFactory
                (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                  ρ_tgt)
                (.exiting lbl ρ_inner_tgt) :=
              stmts_cons_head_exiting_append (extendFactory := extendFactory) _ _ _ ρ_inner_tgt lbl h_body_tgt'
            have h_block_tgt_exit : StepStmtStar P (EvalCmd P) extendFactory
                (.block .none ρ_tgt.store ρ_tgt.factory (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                  ρ_tgt))
                (.exiting lbl ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store, factory := ρ_tgt.factory } : Env P)) := by
              refine ReflTrans_Transitive _ _ _ _
                (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_tgt.store ρ_tgt.factory h_body_tail_exit) ?_
              exact .step _ _ _ (StepStmt.step_block_exit_mismatch (by simp)) (.refl _)
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_block_tgt_exit) ?_
            exact .step _ _ _ StepStmt.step_seq_exit (.refl _)
          · exact StoreAgreement.of_projectStore_parents h_agree h_off_inner
          · exact h_fail_inner
          · show ρ_tgt.factory = ρ_src.factory; exact h_eval_eq
          · intro s h_suf h_notin
            show (if (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
                then ρ_inner_tgt.store (HasIdent.ident (P := P) s) else none) = none
            rw [h_tgt_fresh s h_suf h_notin]; rfl
        · -- Body terminates, loop tail exits with lbl: recurse on the tail.
          have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
            blockT_none_reaches_terminal (extendFactory := extendFactory) h_block_term
          have ⟨h_loop_T_exit, hlen_cons⟩ :=
            stmtsT_singleton_exiting (extendFactory := extendFactory) h_loop_exit
          have h_body_run : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts body ρ_src) (Env.outcomeConfig none ρ_inner) :=
            reflTransT_to_prop h_inner_term
          obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner,
              h_eval_inner, h_fresh_inner⟩ :=
            h_body_sim none ρ_src ρ_inner ρ_tgt h_eval_eq h_fail_eq h_agree hwf
              h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef h_body_run
          have h_eval_inner_src : ρ_inner.factory = ρ_src.factory :=
            block_noFuncDecl_preserves_factory P (EvalCmd P) extendFactory body ρ_src ρ_inner h_nofd_body
              (by simpa only [Env.outcomeConfig] using h_body_run)
          have heq_ρ_block_full :
              ρ_block = ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store, factory := ρ_src.factory } : Env P) := by
            rw [heq_ρ_block]
          subst heq_ρ_block_full
          have h_g_some_tgt : (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome = true := by
            rw [h_guard_def]; rfl
          have h_body_tgt_term : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts body' ρ_tgt)
              (.terminal ρ_inner_tgt) := by
            simpa only [Env.outcomeConfig] using h_body_tgt
          have h_g_some_inner : (ρ_inner_tgt.store (HasIdent.ident (P := P) g)).isSome = true :=
            stmts_preserves_isSome (extendFactory := extendFactory) h_body_tgt_term (y := HasIdent.ident (P := P) g)
              h_g_some_tgt
          obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp h_g_some_inner
          have hwf_var_inner : WellFormedSemanticEvalVar ρ_inner_tgt.factory := by
            rw [h_eval_inner, h_eval_inner_src]; exact hwf.var
          let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store, factory := ρ_src.factory }
          -- Invert the loop tail (exiting lbl) to learn the next decision.  EXIT
          -- is impossible (`.terminal _ →* .exiting lbl`), so the next is ENTER:
          -- re-havoc $g := tt and recurse with entering = true.
          have hrest_enter :
              ∃ (hr : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
                (.seq (.block .none ρ_src_next.store ρ_src_next.factory (.stmts body ρ_src_next))
                  [.loop .nondet m inv body md])
                (Env.outcomeConfig (some lbl) ρ')), hr.len ≤ n := by
            rcases loop_nondet_step_first_inv (extendFactory := extendFactory) (oc := some lbl)
                h_loop_T_exit with
              ⟨hrest_next, _⟩ | ⟨hrest_next, hlen_next⟩
            · exfalso
              simp only [Env.outcomeConfig] at hrest_next
              match hrest_next with
              | .step _ _ _ h _ => exact nomatch h
            · have h_bound : h_loop_T_exit.len ≤ n := by omega
              exact ⟨hrest_next, Nat.le_of_lt (Nat.lt_of_lt_of_le hlen_next h_bound)⟩
          obtain ⟨hrest_next, hlen_tail⟩ := hrest_enter
          have h_tail : StepStmtStar P (EvalCmd P) extendFactory
              (.stmt (.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)) ρ_inner_tgt)
              (.terminal ({ ρ_inner_tgt with store := SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P)) :=
            step_havoc_set_to (extendFactory := extendFactory) (HasIdent.ident (P := P) g) HasBool.tt md ρ_inner_tgt v' hv'
              (HasBool.boolIsVal ρ_inner_tgt.factory).1 hwf_var_inner
          have h_body_tail : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt)
              (.terminal ({ ρ_inner_tgt with store := SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P)) :=
            ReflTrans_Transitive _ _ _ _
              (stmts_prefix_terminal_append P (EvalCmd P) extendFactory _ _ _ ρ_inner_tgt h_body_tgt_term)
              (stmt_to_singleton_stmts (extendFactory := extendFactory) _ ρ_inner_tgt _ h_tail)
          let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store (SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt), factory := ρ_tgt.factory }
          have h_guard_next : ρ_tgt_next.store (HasIdent.ident (P := P) g) = some HasBool.tt := by
            show (if (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome
                then SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt
                  (HasIdent.ident (P := P) g) else none) = some HasBool.tt
            rw [if_pos h_g_some_tgt]; simp [SemanticStore.update]
          have h_eval_next : ρ_src_next.factory = ρ_src.factory := rfl
          have hwf_next : WellFormedSemanticEval ρ_src_next.factory := by rw [h_eval_next]; exact hwf
          have h_eval_eq_next : ρ_tgt_next.factory = ρ_src_next.factory := by
            show ρ_tgt.factory = ρ_src.factory; exact h_eval_eq
          have h_fail_eq_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
            show ρ_inner_tgt.hasFailure = ρ_inner.hasFailure; exact h_fail_inner
          have h_agree_next : StoreAgreement ρ_src_next.store ρ_tgt_next.store :=
            StoreAgreement.of_projectStore_parents h_agree
              (storeAgreement_storeWith _ _ _ _ h_off_inner (h_inner_fresh g h_g_gen))
          have h_src_fresh_next : ∀ t, Q t →
              ρ_src_next.store (HasIdent.ident (P := P) t) = none := by
            intro t h_suf
            show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
                then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
            by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
            · rw [if_pos hp]; exact h_inner_fresh t h_suf
            · rw [if_neg hp]
          have h_tgt_fresh_next : GenFreshStore Q σ ρ_tgt_next.store := by
            intro s h_suf h_notin
            show (if (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
                then SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt
                  (HasIdent.ident (P := P) s) else none) = none
            rw [h_tgt_fresh s h_suf h_notin]; rfl
          have h_tgt_init_undef_next : ∀ y ∈ Block.initVars body, ρ_tgt_next.store y = none := by
            intro y hy
            show projectStore ρ_tgt.store
                (SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) y = none
            show (if (ρ_tgt.store y).isSome
                then SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt y
                else none) = none
            rw [h_tgt_init_undef y hy]; rfl
          obtain ⟨h_fresh', ρ_out, h_loop_tgt, h_off', h_fail', h_eval', h_fresh_out⟩ :=
            ih (oc := some lbl) (ρ_src := ρ_src_next) (ρ' := ρ') (ρ_tgt := ρ_tgt_next)
              h_eval_eq_next h_fail_eq_next h_agree_next
              hwf_next
              h_src_fresh_next h_tgt_fresh_next h_tgt_init_undef_next true h_guard_next
              (.inr ⟨rfl, hrest_next, hlen_tail⟩)
          simp only [Env.outcomeConfig] at h_loop_tgt
          refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', h_fresh_out⟩
          refine .step _ _ _ (StepStmt.step_loop_enter
            h_guard_tt (h_eval_eq ▸ hwf.bool)) ?_
          have h_block_run : StepStmtStar P (EvalCmd P) extendFactory
              (.block .none ρ_tgt.store ρ_tgt.factory (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt))
              (.terminal ρ_tgt_next) := by
            refine ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_tgt.store ρ_tgt.factory h_body_tail) ?_
            exact .step _ _ _ StepStmt.step_block_done (.refl _)
          have h_loop_stmts_exit : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts [.loop (.det (HasFvar.mkFvar (HasIdent.ident (P := P) g))) m
                inv
                (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md] ρ_tgt_next)
              (.exiting lbl ρ_out) := by
            refine .step _ _ _ StepStmt.step_stmts_cons ?_
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_loop_tgt) ?_
            exact .step _ _ _ StepStmt.step_seq_exit (.refl _)
          refine ReflTrans_Transitive _ _ _ _
            (ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_block_run)
              (.step _ _ _ StepStmt.step_seq_done (.refl _)))
            h_loop_stmts_exit
/-! ### `initVars` classification of the `nondetElim` output

Every init target of the rewritten output is either an original source init
target or a freshly-generated `Q`-guard (the `.ite .nondet`/`.loop .nondet` arms
emit `init $g := *` for a `Q`-kind `g`).  This is the `Q`-generic analogue of the
`ndelimKind`-keyed `nondetElimM_initVars_classified` below (proved here so the
cons-arm tail premise can be re-established without a forward import). -/

section InitVarsClassified

mutual
private theorem Stmt.nondetElimM_initVars_classified_Q {P : PureExpr}
    [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen ndelimItePrefix sg).1)
            ∧ (∀ sg, Q (StringGenState.gen ndelimLoopPrefix sg).1))
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    ∀ x ∈ Block.initVars (P := P) (Stmt.nondetElimM s σ).1,
      x ∈ Stmt.initVars s ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ Q str) := by
  match s with
  | .cmd c =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.definedVars, Stmt.definedVars, List.append_nil] at hx ⊢
      exact Or.inl hx
  | .block lbl bss md =>
      intro x hx
      rw [Stmt.nondetElimM_block_out] at hx
      simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ↓reduceIte,
        List.append_nil] at hx ⊢
      exact Block.nondetElimM_initVars_classified_Q hQgen bss σ x hx
  | .ite (.det e) tss ess md =>
      intro x hx
      rw [Stmt.nondetElimM_ite_det_out] at hx
      simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ↓reduceIte,
        List.append_nil, List.mem_append] at hx ⊢
      rcases hx with h | h
      · rcases Block.nondetElimM_initVars_classified_Q hQgen tss σ x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_initVars_classified_Q hQgen ess _ x h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .ite .nondet tss ess md =>
      intro x hx
      rw [Stmt.nondetElimM_ite_nondet_out] at hx
      simp only [HasInit.init, Block.definedVars, Stmt.definedVars, HasVarsImp.definedVars,
        Cmd.definedVars, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append,
        List.nil_append, List.mem_cons, List.mem_append] at hx ⊢
      rcases hx with h_g | h_t | h_e
      · exact Or.inr ⟨(StringGenState.gen ndelimItePrefix σ).1, h_g, hQgen.1 σ⟩
      · rcases Block.nondetElimM_initVars_classified_Q hQgen tss _ x h_t with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_initVars_classified_Q hQgen ess _ x h_e with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .loop (.det e) m inv body md =>
      intro x hx
      rw [Stmt.nondetElimM_loop_det_out] at hx
      simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ↓reduceIte,
        List.append_nil] at hx ⊢
      exact Block.nondetElimM_initVars_classified_Q hQgen body σ x hx
  | .loop .nondet m inv body md =>
      intro x hx
      rw [Stmt.nondetElimM_loop_nondet_out] at hx
      simp only [HasInit.init, HasHavoc.havoc, Block.definedVars, Stmt.definedVars,
        HasVarsImp.definedVars, Cmd.definedVars, Bool.false_eq_true, ↓reduceIte,
        Block.initVars_append, List.append_nil, List.cons_append, List.nil_append,
        List.mem_cons] at hx ⊢
      rcases hx with h_g | h_body
      · exact Or.inr ⟨(StringGenState.gen ndelimLoopPrefix σ).1, h_g, hQgen.2 σ⟩
      · rcases Block.nondetElimM_initVars_classified_Q hQgen body _ x h_body with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
  | .exit lbl md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.definedVars, Stmt.definedVars, List.append_nil,
        List.not_mem_nil] at hx
  | .funcDecl d md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.definedVars, Stmt.definedVars, List.append_nil,
        List.not_mem_nil] at hx
  | .typeDecl t md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.definedVars, Stmt.definedVars, List.append_nil,
        List.not_mem_nil] at hx
  termination_by sizeOf s

private theorem Block.nondetElimM_initVars_classified_Q {P : PureExpr}
    [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen ndelimItePrefix sg).1)
            ∧ (∀ sg, Q (StringGenState.gen ndelimLoopPrefix sg).1))
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ∀ x ∈ Block.initVars (P := P) (Block.nondetElimM ss σ).1,
      x ∈ Block.initVars ss ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ Q str) := by
  match ss with
  | [] =>
      intro x hx
      simp only [Block.nondetElimM, Block.definedVars, List.not_mem_nil] at hx
  | s :: rest =>
      intro x hx
      rw [Block.nondetElimM_cons_out, Block.initVars_append] at hx
      simp only [List.mem_append] at hx
      rw [Block.initVars_cons, List.mem_append]
      rcases hx with h | h
      · rcases Stmt.nondetElimM_initVars_classified_Q hQgen s σ x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_initVars_classified_Q hQgen rest _ x h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  termination_by sizeOf ss
end

end InitVarsClassified

/-! General forward simulation with **separate** source and target start stores
threading the generator state `σ`.  This is the inductive workhorse: a source
run from `ρ_src` is simulated by the rewritten block from any target store that
agrees with the source (`StoreAgreement`) and matches its evaluator and failure
flag.  The generated guard variables are hidden from the source by the
combination of `StoreAgreement` and `h_src_fresh` below.

Invariants threaded:
- `StoreAgreement ρ_src.store ρ_tgt.store`: wherever the source is defined, the
  target agrees (so a fresh user var stays fresh in the target — the `.cmd`/`init` arm);
- `GenFreshStore Q σ ρ_tgt.store`: the target store has no *ungenerated* gen-shaped
  slot defined (so each freshly-generated guard slot is `none` for the inserted
  `init`/`set`);
- `h_src_fresh`: the source store has *no* gen-shaped slot defined (so the
  generated guard is hidden from the source via `storeAgreement_storeWith`);
- `SrcNoGenWrites ss`: the source program never writes a gen-shaped variable
  (preserves `h_src_fresh` across sequencing);
- `WF σ`: the generator is well-formed (so generated names are genuinely fresh).

The conclusion re-establishes `StoreAgreement ρ'.store ρ_out.store` so the inductive
step composes. -/
mutual
/-- Per-statement engine (mutual with `nondetElim_simulation_gen_sa`). -/
private theorem nondetElim_stmt_gen_sa {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen ndelimItePrefix sg).1)
            ∧ (∀ sg, Q (StringGenState.gen ndelimLoopPrefix sg).1))
    (extendFactory : ExtendFactory P)
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (ρ_src ρ' ρ_tgt : Env P)
    (h_eval_eq : ρ_tgt.factory = ρ_src.factory)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : GenFreshStore Q σ ρ_tgt.store)
    (h_tgt_init_undef : ∀ y ∈ Stmt.initVars s, ρ_tgt.store y = none)
    (h_unique : (Stmt.initVars s).Nodup)
    (h_no_writes : (∀ t : String, Q t → HasIdent.ident (P := P) t ∉ (Stmt.definedVars s false ++ Stmt.modifiedVars s)))
    (h_nofd : Stmt.noFuncDecl s = true)
    (oc : Option String)
    (h_term : StepStmtStar P (EvalCmd P) extendFactory (.stmt s ρ_src) (Env.outcomeConfig oc ρ')) :
    (∀ t, Q t →
        ρ'.store (HasIdent.ident (P := P) t) = none)
      ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P) extendFactory
          (.stmts (Stmt.nondetElimM s σ).1 ρ_tgt) (Env.outcomeConfig oc ρ_out)
        ∧ StoreAgreement ρ'.store ρ_out.store
        ∧ ρ_out.hasFailure = ρ'.hasFailure
        ∧ ρ_out.factory = ρ'.factory
        ∧ GenFreshStore Q (Stmt.nondetElimM s σ).2 ρ_out.store := by
  match s, h_no_writes, h_nofd, h_tgt_init_undef, h_unique, oc, h_term with
  | .cmd c, h_no_writes, _, h_tgt_init_undef, _, oc, h_term =>
    -- A `.cmd` only ever reaches `.terminal`, so the exiting outcome is vacuous.
    match oc, h_term with
    | none, h_term =>
    -- Output is the same `.cmd c`; replay it under `StoreAgreement`.
    have h_no_writes_c : (∀ s : String, Q s → HasIdent.ident (P := P) s ∉ (Cmd.definedVars c ++ Cmd.modifiedVars c)) := by
      have h_dv : Stmt.definedVars (P := P) (.cmd c) false = Cmd.definedVars c := by
        with_unfolding_all rfl
      have h_mv : Stmt.modifiedVars (P := P) (.cmd c) = Cmd.modifiedVars c := by
        with_unfolding_all rfl
      rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
    -- The targeted init-undef arg for the StoreAgreement cmd replay:
    -- `Cmd.definedVars c = Stmt.initVars (.cmd c)` (both `[x]` for init, `[]` else).
    have h_tgt_init_undef_c : ∀ x ∈ Cmd.definedVars c, ρ_tgt.store x = none := by
      have h_dv : Cmd.definedVars c = Stmt.initVars (P := P) (.cmd c) := by
        with_unfolding_all rfl
      rw [h_dv]; exact h_tgt_init_undef
    -- Derive source post-store gen-freshness separately (the `_sa` cmd replay does
    -- not produce it), mirroring `cmd_replay_agreement_storeAgree`'s body.
    obtain ⟨σ', haf, h_cmd, h_eq⟩ := cmd_step_inv (extendFactory := extendFactory) c ρ_src ρ' h_term
    have h_src'_fresh : ∀ t, Q t →
        ρ'.store (HasIdent.ident (P := P) t) = none := by
      subst h_eq
      exact evalCmd_preserves_src_fresh h_cmd h_src_fresh h_no_writes_c
    obtain ⟨ρ_tgt', h_run, h_agree', h_fail', h_eval'⟩ :=
      cmd_replay_agreement_storeAgree extendFactory c ρ_src ρ' ρ_tgt
        h_eval_eq h_fail_eq h_agree hwf.mono h_tgt_init_undef_c h_term
    -- Invert the target replay run to recover the target's `EvalCmd`, which drives
    -- the GenFreshStore preservation step (the target writes no gen-shaped var).
    obtain ⟨σ_tgt', haf_t, h_cmd_tgt, h_eq_tgt⟩ :=
      cmd_step_inv (extendFactory := extendFactory) c ρ_tgt ρ_tgt' h_run
    refine ⟨h_src'_fresh, ρ_tgt', ?_, h_agree', h_fail', h_eval', ?_⟩
    · simp only [Stmt.nondetElimM, Env.outcomeConfig]
      exact stmt_to_singleton_stmts (extendFactory := extendFactory) (.cmd c) ρ_tgt ρ_tgt' h_run
    · simp only [Stmt.nondetElimM]
      intro t h_suf h_nin
      have h_none : ρ_tgt.store (HasIdent.ident (P := P) t) = none := h_tgt_fresh t h_suf h_nin
      subst h_eq_tgt
      refine evalCmd_preserves_none (P := P) h_cmd_tgt h_none ?_ ?_
      · intro h_mem; exact h_no_writes_c t h_suf (List.mem_append_left _ h_mem)
      · intro h_mem; exact h_no_writes_c t h_suf (List.mem_append_right _ h_mem)
    | some lbl, h_term =>
      -- `.cmd c` cannot reach `.exiting`: its only step is `step_cmd` to `.terminal`.
      exfalso
      obtain ⟨cfg, hstep, hrest⟩ :=
        stmt_step_first_inv_to (extendFactory := extendFactory) _ ρ_src (Env.outcomeConfig (some lbl) ρ')
          (by intro ρ'' h; simp only [Env.outcomeConfig] at h <;> cases h) h_term
      cases hstep with
      | step_cmd _ =>
        cases hrest with
        | step _ _ _ h _ => cases h
  | .block lbl bss md, h_no_writes, h_nofd, h_tgt_init_undef, h_unique, oc, h_term =>
    obtain ⟨c, hstep, hrest⟩ :=
      stmt_step_first_inv_to (extendFactory := extendFactory) _ ρ_src (Env.outcomeConfig oc ρ')
        (by intro ρ'' h; cases oc <;> simp only [Env.outcomeConfig] at h <;> cases h) h_term
    cases hstep with
    | step_block =>
      have h_dv : Stmt.definedVars (P := P) (.block lbl bss md) false = Block.definedVars bss false := by
        simp only [Stmt.definedVars, Bool.false_eq_true, if_false]
      have h_mv : Stmt.modifiedVars (P := P) (.block lbl bss md) = Block.modifiedVars bss := by
        with_unfolding_all rfl
      have h_no_writes_bss : SrcNoGenWrites (P := P) Q bss := by
        show (∀ s : String, Q s → HasIdent.ident (P := P) s ∉ (Block.definedVars bss false ++ Block.modifiedVars bss))
        rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
      have h_nofd_bss : Block.noFuncDecl bss = true := by
        simpa only [Stmt.noFuncDecl] using h_nofd
      -- `Stmt.initVars (.block lbl bss md) = Block.initVars bss`.
      have h_tgt_init_undef_bss : ∀ y ∈ Block.initVars bss, ρ_tgt.store y = none := by
        intro y hy; exact h_tgt_init_undef y (by rw [Stmt.initVars_block]; exact hy)
      have h_unique_bss : (Block.initVars bss).Nodup := by
        rw [Stmt.initVars_block] at h_unique; exact h_unique
      have wrap : ∀ (oc_inner : Option String) (ρ_inner : Env P),
          StepStmtStar P (EvalCmd P) extendFactory
            (.stmts bss ρ_src) (Env.outcomeConfig oc_inner ρ_inner) →
          (∀ (ρ_out_inner : Env P),
            StepStmtStar P (EvalCmd P) extendFactory
              (.stmts (Block.nondetElimM bss σ).1 ρ_tgt) (Env.outcomeConfig oc_inner ρ_out_inner) →
            StepStmtStar P (EvalCmd P) extendFactory
              (.stmts (Stmt.nondetElimM (.block lbl bss md) σ).1 ρ_tgt)
              (Env.outcomeConfig oc ({ ρ_out_inner with
                store := projectStore ρ_tgt.store ρ_out_inner.store, factory := ρ_tgt.factory } : Env P))) →
          ρ' = { ρ_inner with store := projectStore ρ_src.store ρ_inner.store, factory := ρ_src.factory } →
          (∀ t, Q t →
              ρ'.store (HasIdent.ident (P := P) t) = none)
            ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P) extendFactory
                (.stmts (Stmt.nondetElimM (.block lbl bss md) σ).1 ρ_tgt)
                (Env.outcomeConfig oc ρ_out)
              ∧ StoreAgreement ρ'.store ρ_out.store
              ∧ ρ_out.hasFailure = ρ'.hasFailure
              ∧ ρ_out.factory = ρ'.factory
              ∧ GenFreshStore Q (Stmt.nondetElimM (.block lbl bss md) σ).2 ρ_out.store := by
        intro oc_inner ρ_inner h_inner_run wrap_run h_ρ'_eq
        obtain ⟨h_fresh_inner, ρ_out_inner, h_run_inner, h_off_inner, h_fail_inner,
            h_eval_inner, h_fresh_out⟩ :=
          nondetElim_simulation_gen_sa hQgen extendFactory bss σ ρ_src ρ_inner ρ_tgt
            h_eval_eq h_fail_eq h_agree hwf
            h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef_bss h_unique_bss h_no_writes_bss h_nofd_bss
            oc_inner h_inner_run
        refine ⟨?_, ({ ρ_out_inner with
          store := projectStore ρ_tgt.store ρ_out_inner.store, factory := ρ_tgt.factory } : Env P),
          wrap_run ρ_out_inner h_run_inner, ?_, ?_, ?_, ?_⟩
        · subst h_ρ'_eq
          intro t h_suf
          show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
          show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
              then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
          by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
          · rw [if_pos hp]; exact h_fresh_inner t h_suf
          · rw [if_neg hp]
        · -- StoreAgreement survives projecting both stores through agreeing parents.
          subst h_ρ'_eq
          exact StoreAgreement.of_projectStore_parents h_agree h_off_inner
        · subst h_ρ'_eq; exact h_fail_inner
        · subst h_ρ'_eq; show ρ_tgt.factory = ρ_src.factory; exact h_eval_eq
        · have h_out_eq : (Stmt.nondetElimM (.block lbl bss md) σ).2
              = (Block.nondetElimM bss σ).2 := by
            rw [Stmt.nondetElimM]
            rcases hh : Block.nondetElimM bss σ with ⟨bss', σ'⟩
            simp only [hh]
          rw [h_out_eq]
          intro s h_suf h_notin
          show projectStore ρ_tgt.store ρ_out_inner.store (HasIdent.ident (P := P) s) = none
          show (if (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
              then ρ_out_inner.store (HasIdent.ident (P := P) s) else none) = none
          by_cases hp : (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
          · rw [if_pos hp]; exact h_fresh_out s h_suf h_notin
          · rw [if_neg hp]
      cases oc with
      | none =>
        rcases block_some_reaches_terminal P (EvalCmd P) extendFactory hrest with
          ⟨ρ_inner, h_inner_term, h_ρ'_eq⟩ | ⟨ρ_inner, h_inner_exit, h_ρ'_eq⟩
        · refine wrap none ρ_inner h_inner_term (fun ρ_out_inner h_run_inner => ?_) h_ρ'_eq
          rw [Stmt.nondetElimM_block_out]
          refine stmt_to_singleton_stmts (extendFactory := extendFactory) _ ρ_tgt _ ?_
          refine .step _ _ _ (StepStmt.step_block) ?_
          refine ReflTrans_Transitive _ _ _ _
            (block_inner_star P (EvalCmd P) extendFactory _ _ (.some lbl) ρ_tgt.store ρ_tgt.factory
              (show StepStmtStar P (EvalCmd P) extendFactory _ (.terminal ρ_out_inner) from
                h_run_inner)) ?_
          exact .step _ _ _ StepStmt.step_block_done (.refl _)
        · refine wrap (some lbl) ρ_inner h_inner_exit (fun ρ_out_inner h_run_inner => ?_) h_ρ'_eq
          rw [Stmt.nondetElimM_block_out]
          refine stmt_to_singleton_stmts (extendFactory := extendFactory) _ ρ_tgt _ ?_
          refine .step _ _ _ (StepStmt.step_block) ?_
          refine ReflTrans_Transitive _ _ _ _
            (block_inner_star P (EvalCmd P) extendFactory _ _ (.some lbl) ρ_tgt.store ρ_tgt.factory
              (show StepStmtStar P (EvalCmd P) extendFactory _ (.exiting lbl ρ_out_inner) from
                h_run_inner)) ?_
          exact .step _ _ _ (StepStmt.step_block_exit_match rfl) (.refl _)
      | some lbl' =>
        obtain ⟨h_ne, ρ_inner, h_inner_exit, h_ρ'_eq⟩ :=
          block_reaches_exiting_strong P (EvalCmd P) extendFactory hrest
        refine wrap (some lbl') ρ_inner h_inner_exit
          (fun ρ_out_inner h_run_inner => ?_) h_ρ'_eq
        rw [Stmt.nondetElimM_block_out]
        refine stmt_to_singleton_stmts_exiting (extendFactory := extendFactory) _ ρ_tgt _ lbl' ?_
        refine .step _ _ _ (StepStmt.step_block) ?_
        refine ReflTrans_Transitive _ _ _ _
          (block_inner_star P (EvalCmd P) extendFactory _ _ (.some lbl) ρ_tgt.store ρ_tgt.factory
            (show StepStmtStar P (EvalCmd P) extendFactory _ (.exiting lbl' ρ_out_inner) from
              h_run_inner)) ?_
        exact .step _ _ _ (StepStmt.step_block_exit_mismatch (fun h => h_ne (Option.some.inj h))) (.refl _)
  | .ite (.det e) tss ess md, h_no_writes, h_nofd, h_tgt_init_undef, h_unique, oc, h_term =>
    obtain ⟨cfg, hstep, hbranch⟩ :=
      stmt_step_first_inv_to (extendFactory := extendFactory) _ ρ_src (Env.outcomeConfig oc ρ')
        (by intro ρ'' h; cases oc <;> simp only [Env.outcomeConfig] at h <;> cases h) h_term
    have hwf_var_t : WellFormedSemanticEvalVar ρ_tgt.factory := h_eval_eq ▸ hwf.var
    have h_dv : Stmt.definedVars (P := P) (.ite (.det e) tss ess md) false
        = Block.definedVars tss false ++ Block.definedVars ess false := by
      simp only [Stmt.definedVars, Bool.false_eq_true, if_false]
    have h_mv : Stmt.modifiedVars (P := P) (.ite (.det e) tss ess md)
        = Block.modifiedVars tss ++ Block.modifiedVars ess := rfl
    have h_nofd' : Block.noFuncDecl tss = true ∧ Block.noFuncDecl ess = true := by
      have : (Block.noFuncDecl tss && Block.noFuncDecl ess) = true := by
        simpa only [Stmt.noFuncDecl] using h_nofd
      exact Bool.and_eq_true _ _ |>.mp this
    -- Init-undef splits across the two branches.
    have h_tgt_iu_t : ∀ y ∈ Block.initVars tss, ρ_tgt.store y = none := by
      intro y hy; exact h_tgt_init_undef y
        (by rw [Stmt.initVars_ite]; exact List.mem_append_left _ hy)
    have h_tgt_iu_e : ∀ y ∈ Block.initVars ess, ρ_tgt.store y = none := by
      intro y hy; exact h_tgt_init_undef y
        (by rw [Stmt.initVars_ite]; exact List.mem_append_right _ hy)
    -- Uniqueness splits across the two branches.
    have h_unique_pair : (Block.initVars tss ++ Block.initVars ess).Nodup := by
      rw [Stmt.initVars_ite] at h_unique; exact h_unique
    have h_unique_t : (Block.initVars tss).Nodup := (List.nodup_append.mp h_unique_pair).1
    have h_unique_e : (Block.initVars ess).Nodup := (List.nodup_append.mp h_unique_pair).2.1
    cases hstep with
    | step_ite_true h_cond hwfb_s =>
      obtain ⟨ρ_inner, hbranch_inner, h_ρ'_eq⟩ :=
        blockT_none_reaches_outcome (extendFactory := extendFactory) hbranch
      have h_no_writes_t : SrcNoGenWrites (P := P) Q tss := by
        intro t hQ hmem
        rcases List.mem_append.mp hmem with hd | hm
        · exact h_no_writes t hQ (by rw [h_dv]; exact List.mem_append_left _ (List.mem_append_left _ hd))
        · exact h_no_writes t hQ (by rw [h_mv]; exact List.mem_append_right _ (List.mem_append_left _ hm))
      obtain ⟨h_fresh', ρ_out, h_run, h_off', h_fail', h_eval', h_fresh_out⟩ :=
        nondetElim_simulation_gen_sa hQgen extendFactory tss σ ρ_src ρ_inner ρ_tgt
          h_eval_eq h_fail_eq h_agree hwf
          h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_t h_unique_t h_no_writes_t h_nofd'.1
          oc hbranch_inner
      subst h_ρ'_eq
      refine ⟨?_, ({ ρ_out with store := projectStore ρ_tgt.store ρ_out.store, factory := ρ_tgt.factory } : Env P),
        ?_, ?_, ?_, ?_, ?_⟩
      · intro t h_suf
        show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
        show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
        by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
        · rw [if_pos hp]; exact h_fresh' t h_suf
        · rw [if_neg hp]
      · rw [Stmt.nondetElimM_ite_det_out]
        have h_cond_t : P.eval ρ_tgt.factory ρ_tgt.store e = some HasBool.tt := by
          rw [h_eval_eq]
          exact hwf.mono e HasBool.tt ρ_src.store ρ_tgt.store
            (storeAgreement_supplies_mono_premise ρ_src.store ρ_tgt.store h_agree) h_cond
        refine stmt_to_singleton_stmts_outcome (extendFactory := extendFactory) _ ρ_tgt _ oc ?_
        refine .step _ _ _ (StepStmt.step_ite_true h_cond_t (h_eval_eq ▸ hwf.bool)) ?_
        exact blockT_none_build_outcome (extendFactory := extendFactory) _ ρ_tgt.store ρ_tgt.factory oc ρ_out h_run
      · exact StoreAgreement.of_projectStore_parents h_agree h_off'
      · exact h_fail'
      · show ρ_tgt.factory = ρ_src.factory; exact h_eval_eq
      · simp only [Stmt.nondetElimM]
        rcases h₁ : Block.nondetElimM tss σ with ⟨tss', σ₁⟩
        rcases h₂ : Block.nondetElimM ess σ₁ with ⟨ess', σ₂⟩
        simp only [h₂]
        have h_eq1 : σ₁ = (Block.nondetElimM tss σ).2 := by rw [h₁]
        have h_step12 : StringGenState.GenStep σ₁ σ₂ := by
          have := Block.nondetElimM_genStep ess σ₁; rw [h₂] at this; exact this
        intro s h_suf h_notin
        show projectStore ρ_tgt.store ρ_out.store (HasIdent.ident (P := P) s) = none
        show (if (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome then ρ_out.store (HasIdent.ident (P := P) s) else none) = none
        by_cases hp : (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
        · rw [if_pos hp]
          have h_fresh_σ₁ : GenFreshStore Q σ₁ ρ_out.store := by rw [h_eq1]; exact h_fresh_out
          exact (GenFreshStore_mono h_step12 h_fresh_σ₁) s h_suf h_notin
        · rw [if_neg hp]
    | step_ite_false h_cond hwfb_s =>
      obtain ⟨ρ_inner, hbranch_inner, h_ρ'_eq⟩ :=
        blockT_none_reaches_outcome (extendFactory := extendFactory) hbranch
      have h_no_writes_e : SrcNoGenWrites (P := P) Q ess := by
        intro t hQ hmem
        rcases List.mem_append.mp hmem with hd | hm
        · exact h_no_writes t hQ (by rw [h_dv]; exact List.mem_append_left _ (List.mem_append_right _ hd))
        · exact h_no_writes t hQ (by rw [h_mv]; exact List.mem_append_right _ (List.mem_append_right _ hm))
      have h_wf₁ : StringGenState.WF (Block.nondetElimM tss σ).2 :=
        (Block.nondetElimM_genStep tss σ).wf_mono h_wf_gen
      have h_tgt_fresh₁ : GenFreshStore Q (Block.nondetElimM tss σ).2 ρ_tgt.store :=
        GenFreshStore_mono (Block.nondetElimM_genStep tss σ) h_tgt_fresh
      obtain ⟨h_fresh', ρ_out, h_run, h_off', h_fail', h_eval', h_fresh_out⟩ :=
        nondetElim_simulation_gen_sa hQgen extendFactory ess (Block.nondetElimM tss σ).2 ρ_src ρ_inner ρ_tgt
          h_eval_eq h_fail_eq h_agree hwf
          h_wf₁ h_src_fresh h_tgt_fresh₁ h_tgt_iu_e h_unique_e h_no_writes_e h_nofd'.2
          oc hbranch_inner
      subst h_ρ'_eq
      refine ⟨?_, ({ ρ_out with store := projectStore ρ_tgt.store ρ_out.store, factory := ρ_tgt.factory } : Env P),
        ?_, ?_, ?_, ?_, ?_⟩
      · intro t h_suf
        show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
        show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
        by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
        · rw [if_pos hp]; exact h_fresh' t h_suf
        · rw [if_neg hp]
      · rw [Stmt.nondetElimM_ite_det_out]
        have h_cond_t : P.eval ρ_tgt.factory ρ_tgt.store e = some HasBool.ff := by
          rw [h_eval_eq]
          exact hwf.mono e HasBool.ff ρ_src.store ρ_tgt.store
            (storeAgreement_supplies_mono_premise ρ_src.store ρ_tgt.store h_agree) h_cond
        refine stmt_to_singleton_stmts_outcome (extendFactory := extendFactory) _ ρ_tgt _ oc ?_
        refine .step _ _ _ (StepStmt.step_ite_false h_cond_t (h_eval_eq ▸ hwf.bool)) ?_
        exact blockT_none_build_outcome (extendFactory := extendFactory) _ ρ_tgt.store ρ_tgt.factory oc ρ_out h_run
      · exact StoreAgreement.of_projectStore_parents h_agree h_off'
      · exact h_fail'
      · show ρ_tgt.factory = ρ_src.factory; exact h_eval_eq
      · simp only [Stmt.nondetElimM]
        rcases h₁ : Block.nondetElimM tss σ with ⟨tss', σ₁⟩
        rcases h₂ : Block.nondetElimM ess σ₁ with ⟨ess', σ₂⟩
        simp only [h₂]
        have h_eq2 : σ₂ = (Block.nondetElimM ess σ₁).2 := by rw [h₂]
        have h_eq1 : σ₁ = (Block.nondetElimM tss σ).2 := by rw [h₁]
        intro s h_suf h_notin
        show projectStore ρ_tgt.store ρ_out.store (HasIdent.ident (P := P) s) = none
        show (if (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome then ρ_out.store (HasIdent.ident (P := P) s) else none) = none
        by_cases hp : (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
        · rw [if_pos hp]
          rw [h_eq2, h_eq1] at *
          exact h_fresh_out s h_suf h_notin
        · rw [if_neg hp]
  | .ite .nondet tss ess md, h_no_writes, h_nofd, h_tgt_init_undef, h_unique, oc, h_term =>
    rcases hgen : StringGenState.gen ndelimItePrefix σ with ⟨g, σ₁⟩
    have h_g_gen : Q g := by
      have := hQgen.1 σ
      rw [hgen] at this; exact this
    have h_tgt_g_none : ρ_tgt.store (HasIdent.ident (P := P) g) = none := by
      have := GenFreshStore_gen_slot_none ndelimItePrefix h_tgt_fresh h_wf_gen (hQgen.1 σ)
      rw [hgen] at this; exact this
    have hwf_var_t : WellFormedSemanticEvalVar ρ_tgt.factory := h_eval_eq ▸ hwf.var
    have hwfb_t : WellFormedSemanticEvalBool ρ_tgt.factory := h_eval_eq ▸ hwf.bool
    have hwf_def_t : WellFormedSemanticEvalMono ρ_tgt.factory := h_eval_eq ▸ hwf.mono
    have h_step01 : StringGenState.GenStep σ σ₁ := by
      have := StringGenState.GenStep.of_gen ndelimItePrefix σ; rw [hgen] at this; exact this
    have h_wf₁ : StringGenState.WF σ₁ := h_step01.wf_mono h_wf_gen
    have h_dv : Stmt.definedVars (P := P) (.ite .nondet tss ess md) false
        = Block.definedVars tss false ++ Block.definedVars ess false := by
      simp only [Stmt.definedVars, Bool.false_eq_true, if_false]
    have h_mv : Stmt.modifiedVars (P := P) (.ite .nondet tss ess md)
        = Block.modifiedVars tss ++ Block.modifiedVars ess := rfl
    have h_nofd' : Block.noFuncDecl tss = true ∧ Block.noFuncDecl ess = true := by
      have : (Block.noFuncDecl tss && Block.noFuncDecl ess) = true := by
        simpa only [Stmt.noFuncDecl] using h_nofd
      exact Bool.and_eq_true _ _ |>.mp this
    have h_no_writes_t : SrcNoGenWrites (P := P) Q tss := by
      intro t hQ hmem
      rcases List.mem_append.mp hmem with hd | hm
      · exact h_no_writes t hQ (by rw [h_dv]; exact List.mem_append_left _ (List.mem_append_left _ hd))
      · exact h_no_writes t hQ (by rw [h_mv]; exact List.mem_append_right _ (List.mem_append_left _ hm))
    have h_no_writes_e : SrcNoGenWrites (P := P) Q ess := by
      intro t hQ hmem
      rcases List.mem_append.mp hmem with hd | hm
      · exact h_no_writes t hQ (by rw [h_dv]; exact List.mem_append_left _ (List.mem_append_right _ hd))
      · exact h_no_writes t hQ (by rw [h_mv]; exact List.mem_append_right _ (List.mem_append_right _ hm))
    -- Branch init-targets are source-shaped, hence distinct from the gen guard `g`;
    -- the guard SemanticStore.update leaves each branch init-target's slot untouched.
    have h_tgt_iu_t : ∀ (v : P.Expr) (y : P.Ident), y ∈ Block.initVars tss →
        (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) v) y = none := by
      intro v y hy
      have h_y_dv : y ∈ Stmt.definedVars (P := P) (.ite .nondet tss ess md) false := by
        rw [h_dv]; exact List.mem_append_left _ (hy)
      have h_y_ne : y ≠ HasIdent.ident (P := P) g := fun h_eq =>
        h_no_writes g h_g_gen (h_eq ▸ List.mem_append_left _ h_y_dv)
      have h_y_none : ρ_tgt.store y = none := h_tgt_init_undef y
        (by rw [Stmt.initVars_ite]; exact List.mem_append_left _ hy)
      simp only [SemanticStore.update, h_y_ne]; exact h_y_none
    have h_tgt_iu_e : ∀ (v : P.Expr) (y : P.Ident), y ∈ Block.initVars ess →
        (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) v) y = none := by
      intro v y hy
      have h_y_dv : y ∈ Stmt.definedVars (P := P) (.ite .nondet tss ess md) false := by
        rw [h_dv]; exact List.mem_append_right _ (hy)
      have h_y_ne : y ≠ HasIdent.ident (P := P) g := fun h_eq =>
        h_no_writes g h_g_gen (h_eq ▸ List.mem_append_left _ h_y_dv)
      have h_y_none : ρ_tgt.store y = none := h_tgt_init_undef y
        (by rw [Stmt.initVars_ite]; exact List.mem_append_right _ hy)
      simp only [SemanticStore.update, h_y_ne]; exact h_y_none
    have h_unique_pair : (Block.initVars tss ++ Block.initVars ess).Nodup := by
      rw [Stmt.initVars_ite] at h_unique; exact h_unique
    have h_unique_t : (Block.initVars tss).Nodup := (List.nodup_append.mp h_unique_pair).1
    have h_unique_e : (Block.initVars ess).Nodup := (List.nodup_append.mp h_unique_pair).2.1
    rcases ite_nondet_step_inv_outcome (extendFactory := extendFactory) tss ess md ρ_src ρ' oc h_term with h_br | h_br
    · have h_off_g : StoreAgreement ρ_src.store
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) :=
        storeAgreement_storeWith _ _ _ _ h_agree (h_src_fresh g h_g_gen)
      have h_fresh_g : GenFreshStore Q σ₁
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) := by
        have := GenFreshStore_storeWith_gen (P := P) ndelimItePrefix HasBool.tt h_tgt_fresh
        rw [hgen] at this; exact this
      obtain ⟨ρ_inner, h_br_inner, h_ρ'_eq⟩ := h_br
      let ρ_tgt_g : Env P := { ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt }
      obtain ⟨h_fresh', ρ_out, h_run, h_off', h_fail', h_eval', h_fresh_out⟩ :=
        nondetElim_simulation_gen_sa hQgen extendFactory tss σ₁
          ρ_src ρ_inner ρ_tgt_g
          h_eval_eq h_fail_eq h_off_g hwf
          h_wf₁ h_src_fresh h_fresh_g (h_tgt_iu_t HasBool.tt) h_unique_t h_no_writes_t h_nofd'.1
          oc h_br_inner
      subst h_ρ'_eq
      refine ⟨?_, ({ ρ_out with store := projectStore ρ_tgt_g.store ρ_out.store, factory := ρ_tgt.factory } : Env P),
        ?_, ?_, ?_, ?_, ?_⟩
      · intro t h_suf
        show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
        show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
        by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
        · rw [if_pos hp]; exact h_fresh' t h_suf
        · rw [if_neg hp]
      · rw [Stmt.nondetElimM_ite_nondet_out]
        simp only [hgen]
        have := step_ndelim_ite_prefix_outcome (extendFactory := extendFactory) true (HasIdent.ident (P := P) g)
          (Block.nondetElimM tss σ₁).1 (Block.nondetElimM ess (Block.nondetElimM tss σ₁).2).1 md
          ρ_tgt ρ_out oc h_tgt_g_none hwf_var_t hwf_def_t hwfb_t h_run
        simpa only [ρ_tgt_g] using this
      · exact StoreAgreement.of_projectStore_parents h_off_g h_off'
      · exact h_fail'
      · show ρ_tgt.factory = ρ_src.factory; exact h_eval_eq
      · simp only [Stmt.nondetElimM, hgen]
        rcases h₁ : Block.nondetElimM tss σ₁ with ⟨tss', σ₂⟩
        rcases h₂ : Block.nondetElimM ess σ₂ with ⟨ess', σ₃⟩
        simp only [h₂]
        have h_eq2 : σ₂ = (Block.nondetElimM tss σ₁).2 := by rw [h₁]
        have h_step23 : StringGenState.GenStep σ₂ σ₃ := by
          have := Block.nondetElimM_genStep ess σ₂; rw [h₂] at this; exact this
        have h_fresh_σ₂ : GenFreshStore Q σ₂ ρ_out.store := by rw [h_eq2]; exact h_fresh_out
        intro s h_suf h_notin
        show projectStore ρ_tgt_g.store ρ_out.store (HasIdent.ident (P := P) s) = none
        show (if (ρ_tgt_g.store (HasIdent.ident (P := P) s)).isSome then ρ_out.store (HasIdent.ident (P := P) s) else none) = none
        by_cases hp : (ρ_tgt_g.store (HasIdent.ident (P := P) s)).isSome
        · rw [if_pos hp]; exact (GenFreshStore_mono h_step23 h_fresh_σ₂) s h_suf h_notin
        · rw [if_neg hp]
    · have h_step12 : StringGenState.GenStep σ₁ (Block.nondetElimM tss σ₁).2 :=
        Block.nondetElimM_genStep tss σ₁
      have h_wf₂ : StringGenState.WF (Block.nondetElimM tss σ₁).2 := h_step12.wf_mono h_wf₁
      have h_off_g : StoreAgreement ρ_src.store
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) :=
        storeAgreement_storeWith _ _ _ _ h_agree (h_src_fresh g h_g_gen)
      have h_fresh_g1 : GenFreshStore Q σ₁
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) := by
        have := GenFreshStore_storeWith_gen (P := P) ndelimItePrefix HasBool.ff h_tgt_fresh
        rw [hgen] at this; exact this
      have h_fresh_g : GenFreshStore Q (Block.nondetElimM tss σ₁).2
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) :=
        GenFreshStore_mono h_step12 h_fresh_g1
      obtain ⟨ρ_inner, h_br_inner, h_ρ'_eq⟩ := h_br
      let ρ_tgt_g : Env P := { ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff }
      obtain ⟨h_fresh', ρ_out, h_run, h_off', h_fail', h_eval', h_fresh_out⟩ :=
        nondetElim_simulation_gen_sa hQgen extendFactory ess (Block.nondetElimM tss σ₁).2
          ρ_src ρ_inner ρ_tgt_g
          h_eval_eq h_fail_eq h_off_g hwf
          h_wf₂ h_src_fresh h_fresh_g (h_tgt_iu_e HasBool.ff) h_unique_e h_no_writes_e h_nofd'.2
          oc h_br_inner
      subst h_ρ'_eq
      refine ⟨?_, ({ ρ_out with store := projectStore ρ_tgt_g.store ρ_out.store, factory := ρ_tgt.factory } : Env P),
        ?_, ?_, ?_, ?_, ?_⟩
      · intro t h_suf
        show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
        show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
        by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
        · rw [if_pos hp]; exact h_fresh' t h_suf
        · rw [if_neg hp]
      · rw [Stmt.nondetElimM_ite_nondet_out]
        simp only [hgen]
        have := step_ndelim_ite_prefix_outcome (extendFactory := extendFactory) false (HasIdent.ident (P := P) g)
          (Block.nondetElimM tss σ₁).1 (Block.nondetElimM ess (Block.nondetElimM tss σ₁).2).1 md
          ρ_tgt ρ_out oc h_tgt_g_none hwf_var_t hwf_def_t hwfb_t h_run
        simpa only [ρ_tgt_g] using this
      · exact StoreAgreement.of_projectStore_parents h_off_g h_off'
      · exact h_fail'
      · show ρ_tgt.factory = ρ_src.factory; exact h_eval_eq
      · simp only [Stmt.nondetElimM, hgen]
        rcases h₁ : Block.nondetElimM tss σ₁ with ⟨tss', σ₂⟩
        rcases h₂ : Block.nondetElimM ess σ₂ with ⟨ess', σ₃⟩
        simp only [h₂]
        simp only [h₁, h₂] at h_fresh_out
        intro s h_suf h_notin
        show projectStore ρ_tgt_g.store ρ_out.store (HasIdent.ident (P := P) s) = none
        show (if (ρ_tgt_g.store (HasIdent.ident (P := P) s)).isSome then ρ_out.store (HasIdent.ident (P := P) s) else none) = none
        by_cases hp : (ρ_tgt_g.store (HasIdent.ident (P := P) s)).isSome
        · rw [if_pos hp]; exact h_fresh_out s h_suf h_notin
        · rw [if_neg hp]
  | .loop (.det e) m inv body md, h_no_writes, h_nofd, h_tgt_init_undef, h_unique, oc, h_term =>
    have h_nofd_body : Block.noFuncDecl body = true := by
      simpa only [Stmt.noFuncDecl] using h_nofd
    have h_no_writes_body : SrcNoGenWrites (P := P) Q body := by
      have h_dv : Stmt.definedVars (P := P) (.loop (.det e) m inv body md) false
          = Block.definedVars body false := by
        simp only [Stmt.definedVars, Bool.false_eq_true, if_false]
      have h_mv : Stmt.modifiedVars (P := P) (.loop (.det e) m inv body md)
          = Block.modifiedVars body := rfl
      show (∀ s : String, Q s → HasIdent.ident (P := P) s ∉ (Block.definedVars body false ++ Block.modifiedVars body))
      rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
    have h_tgt_iu_body : ∀ y ∈ Block.initVars body, ρ_tgt.store y = none := by
      intro y hy; exact h_tgt_init_undef y (by rw [Stmt.initVars_loop]; exact hy)
    have h_unique_body : (Block.initVars body).Nodup := by
      rw [Stmt.initVars_loop] at h_unique; exact h_unique
    have h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
        ρb_tgt.factory = ρb_src.factory →
        ρb_tgt.hasFailure = ρb_src.hasFailure →
        StoreAgreement ρb_src.store ρb_tgt.store →
        WellFormedSemanticEval ρb_src.factory →
        StringGenState.WF σ →
        (∀ t, Q t →
          ρb_src.store (HasIdent.ident (P := P) t) = none) →
        GenFreshStore Q σ ρb_tgt.store →
        (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
        StepStmtStar P (EvalCmd P) extendFactory (.stmts body ρb_src) (Env.outcomeConfig oc_b ρb') →
        (∀ t, Q t →
            ρb'.store (HasIdent.ident (P := P) t) = none)
          ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P) extendFactory
              (.stmts (Block.nondetElimM body σ).1 ρb_tgt) (Env.outcomeConfig oc_b ρb_out)
            ∧ StoreAgreement ρb'.store ρb_out.store
            ∧ ρb_out.hasFailure = ρb'.hasFailure
            ∧ ρb_out.factory = ρb'.factory
            ∧ GenFreshStore Q (Block.nondetElimM body σ).2 ρb_out.store :=
      fun oc_b ρb_src ρb' ρb_tgt h_ev h_fl h_ag hwf hwfg hsf htf htiu hrun =>
        nondetElim_simulation_gen_sa hQgen extendFactory body σ ρb_src ρb' ρb_tgt
          h_ev h_fl h_ag hwf hwfg hsf htf htiu h_unique_body
          h_no_writes_body h_nofd_body oc_b hrun
    have hstarT := reflTrans_to_T h_term
    obtain ⟨h_fresh', ρ_out, h_loop_run, h_off', h_fail', h_eval', h_fresh_out⟩ :=
      nondetElim_loop_det_sim_iteration_sa extendFactory e m body (Block.nondetElimM body σ).1 md σ
        h_body_sim h_nofd_body
        oc ρ_src ρ' ρ_tgt hstarT.len
        h_eval_eq h_fail_eq h_agree hwf
        h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_body hstarT (Nat.le_refl _)
    refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', ?_⟩
    · rw [Stmt.nondetElimM_loop_det_out]
      exact stmt_to_singleton_stmts_outcome (extendFactory := extendFactory) _ ρ_tgt ρ_out oc h_loop_run
    · have h_out_eq : (Stmt.nondetElimM (.loop (.det e) m inv body md) σ).2
          = (Block.nondetElimM body σ).2 := by
        rw [Stmt.nondetElimM]
        rcases hh : Block.nondetElimM body σ with ⟨body', σ'⟩
        simp only [hh]
      rw [h_out_eq]
      exact GenFreshStore_mono (Block.nondetElimM_genStep body σ) h_fresh_out
  | .loop .nondet m inv body md, h_no_writes, h_nofd, h_tgt_init_undef, h_unique, oc, h_term =>
    have h_nofd_body : Block.noFuncDecl body = true := by
      simpa only [Stmt.noFuncDecl] using h_nofd
    have h_no_writes_body : SrcNoGenWrites (P := P) Q body := by
      have h_dv : Stmt.definedVars (P := P) (.loop .nondet m inv body md) false
          = Block.definedVars body false := by
        simp only [Stmt.definedVars, Bool.false_eq_true, if_false]
      have h_mv : Stmt.modifiedVars (P := P) (.loop .nondet m inv body md)
          = Block.modifiedVars body := rfl
      show (∀ s : String, Q s → HasIdent.ident (P := P) s ∉ (Block.definedVars body false ++ Block.modifiedVars body))
      rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
    rcases hgen : StringGenState.gen ndelimLoopPrefix σ with ⟨g, σ₁⟩
    have h_g_gen : Q g := by
      have := hQgen.2 σ
      rw [hgen] at this; exact this
    have h_g_in : g ∈ σ₁.stringGens := by
      have h := StringGenState.stringGens_gen ndelimLoopPrefix σ
      rw [hgen] at h; rw [h]; exact List.mem_cons_self
    have h_step01 : StringGenState.GenStep σ σ₁ := by
      have := StringGenState.GenStep.of_gen ndelimLoopPrefix σ; rw [hgen] at this; exact this
    have h_wf₁ : StringGenState.WF σ₁ := h_step01.wf_mono h_wf_gen
    have h_tgt_g_none : ρ_tgt.store (HasIdent.ident (P := P) g) = none := by
      have := GenFreshStore_gen_slot_none ndelimLoopPrefix h_tgt_fresh h_wf_gen (hQgen.2 σ)
      rw [hgen] at this; exact this
    have hwf_var_t : WellFormedSemanticEvalVar ρ_tgt.factory := h_eval_eq ▸ hwf.var
    -- Body init-targets are source-shaped, distinct from gen guard `g`; the
    -- guard SemanticStore.update leaves each body init-target's slot untouched.
    have h_tgt_iu_body : ∀ (v : P.Expr) (y : P.Ident), y ∈ Block.initVars body →
        (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) v) y = none := by
      intro v y hy
      have h_y_dv : y ∈ Stmt.definedVars (P := P) (.loop .nondet m inv body md) false := by
        rw [Stmt.definedVars]; simp only [Bool.false_eq_true, if_false]
        exact hy
      have h_y_ne : y ≠ HasIdent.ident (P := P) g := fun h_eq =>
        h_no_writes g h_g_gen (h_eq ▸ List.mem_append_left _ h_y_dv)
      have h_y_none : ρ_tgt.store y = none := h_tgt_init_undef y
        (by rw [Stmt.initVars_loop]; exact hy)
      simp only [SemanticStore.update, h_y_ne]; exact h_y_none
    have h_unique_body : (Block.initVars body).Nodup := by
      rw [Stmt.initVars_loop] at h_unique; exact h_unique
    have h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
        ρb_tgt.factory = ρb_src.factory →
        ρb_tgt.hasFailure = ρb_src.hasFailure →
        StoreAgreement ρb_src.store ρb_tgt.store →
        WellFormedSemanticEval ρb_src.factory →
        StringGenState.WF σ₁ →
        (∀ t, Q t →
          ρb_src.store (HasIdent.ident (P := P) t) = none) →
        GenFreshStore Q σ₁ ρb_tgt.store →
        (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
        StepStmtStar P (EvalCmd P) extendFactory (.stmts body ρb_src) (Env.outcomeConfig oc_b ρb') →
        (∀ t, Q t →
            ρb'.store (HasIdent.ident (P := P) t) = none)
          ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P) extendFactory
              (.stmts (Block.nondetElimM body σ₁).1 ρb_tgt) (Env.outcomeConfig oc_b ρb_out)
            ∧ StoreAgreement ρb'.store ρb_out.store
            ∧ ρb_out.hasFailure = ρb'.hasFailure
            ∧ ρb_out.factory = ρb'.factory
            ∧ GenFreshStore Q (Block.nondetElimM body σ₁).2 ρb_out.store :=
      fun oc_b ρb_src ρb' ρb_tgt h_ev h_fl h_ag hwf hwfg hsf htf htiu hrun =>
        nondetElim_simulation_gen_sa hQgen extendFactory body σ₁ ρb_src ρb' ρb_tgt
          h_ev h_fl h_ag hwf hwfg hsf htf htiu h_unique_body
          h_no_writes_body h_nofd_body oc_b hrun
    have finish : ∀ (entering : Bool) (b : P.Expr)
        (h_b : b = (if entering then HasBool.tt else HasBool.ff)),
        ((∀ t, Q t →
            ρ'.store (HasIdent.ident (P := P) t) = none)
          ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P) extendFactory
              (.stmt (.loop (.det (HasFvar.mkFvar (HasIdent.ident (P := P) g))) m
                inv
                ((Block.nondetElimM body σ₁).1 ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md)
                ({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) b } : Env P))
              (Env.outcomeConfig oc ρ_out)
            ∧ StoreAgreement ρ'.store ρ_out.store
            ∧ ρ_out.hasFailure = ρ'.hasFailure
            ∧ ρ_out.factory = ρ'.factory
            ∧ GenFreshStore Q σ₁ ρ_out.store) →
        (∀ t, Q t →
            ρ'.store (HasIdent.ident (P := P) t) = none)
          ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P) extendFactory
              (.stmts (Stmt.nondetElimM (.loop .nondet m inv body md) σ).1 ρ_tgt)
              (Env.outcomeConfig oc ρ_out)
            ∧ StoreAgreement ρ'.store ρ_out.store
            ∧ ρ_out.hasFailure = ρ'.hasFailure
            ∧ ρ_out.factory = ρ'.factory
            ∧ GenFreshStore Q (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2 ρ_out.store := by
      intro entering b h_b ⟨h_fresh', ρ_out, h_loop_run, h_off', h_fail', h_eval', h_fresh_out⟩
      have hval_b : HasVal.value ρ_tgt.factory b := by
        rw [h_b]; split
        · exact (HasBool.boolIsVal ρ_tgt.factory).1
        · exact (HasBool.boolIsVal ρ_tgt.factory).2
      refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', ?_⟩
      · rw [Stmt.nondetElimM_loop_nondet_out]
        simp only [hgen]
        have h_init : StepStmtStar P (EvalCmd P) extendFactory
            (.stmt (.cmd (HasInit.init (HasIdent.ident (P := P) g) HasBool.boolTy .nondet md)) ρ_tgt)
            (.terminal ({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) b } : Env P)) :=
          step_init_havoc_to (extendFactory := extendFactory) (HasIdent.ident (P := P) g) HasBool.boolTy b md ρ_tgt
            h_tgt_g_none hval_b hwf_var_t
        refine ReflTrans_Transitive _ _ _ _
          (stmts_cons_step P (EvalCmd P) extendFactory _ _ ρ_tgt _ h_init) ?_
        exact stmt_to_singleton_stmts_outcome (extendFactory := extendFactory) _ _ ρ_out oc h_loop_run
      · have h_out_eq2 : (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2
            = (Block.nondetElimM body σ₁).2 := by
          rw [Stmt.nondetElimM]
          rcases hh : Block.nondetElimM body σ₁ with ⟨body', σ₂⟩
          simp only [hgen, hh]
        rw [h_out_eq2]
        exact GenFreshStore_mono (Block.nondetElimM_genStep body σ₁) h_fresh_out
    have hstarT := reflTrans_to_T h_term
    rcases loop_nondet_step_first_inv (extendFactory := extendFactory) hstarT with
      ⟨hrest, hl⟩ | ⟨hrest, hl⟩
    · have h_off_g : StoreAgreement ρ_src.store
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) :=
        storeAgreement_storeWith _ _ _ _ h_agree (h_src_fresh g h_g_gen)
      have h_fresh_g : GenFreshStore Q σ₁
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) := by
        have := GenFreshStore_storeWith_gen (P := P) ndelimLoopPrefix HasBool.ff h_tgt_fresh
        rw [hgen] at this; exact this
      have h_guard_def : (({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff } : Env P).store)
          (HasIdent.ident (P := P) g) = some (if false then HasBool.tt else HasBool.ff) := by
        simp [SemanticStore.update]
      exact finish false HasBool.ff (by simp)
        (nondetElim_loop_nondet_sim_iteration_sa extendFactory g m body (Block.nondetElimM body σ₁).1 md σ₁ (Block.nondetElimM body σ₁).2
          h_body_sim h_g_gen h_g_in h_nofd_body oc ρ_src ρ'
          ({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff } : Env P)
          hstarT.len h_eval_eq h_fail_eq h_off_g hwf
          h_wf₁ h_src_fresh h_fresh_g (h_tgt_iu_body HasBool.ff) false h_guard_def
          (.inl ⟨rfl, hrest, Nat.le_of_lt hl⟩))
    · have h_off_g : StoreAgreement ρ_src.store
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) :=
        storeAgreement_storeWith _ _ _ _ h_agree (h_src_fresh g h_g_gen)
      have h_fresh_g : GenFreshStore Q σ₁
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) := by
        have := GenFreshStore_storeWith_gen (P := P) ndelimLoopPrefix HasBool.tt h_tgt_fresh
        rw [hgen] at this; exact this
      have h_guard_def : (({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P).store)
          (HasIdent.ident (P := P) g) = some (if true then HasBool.tt else HasBool.ff) := by
        simp [SemanticStore.update]
      exact finish true HasBool.tt (by simp)
        (nondetElim_loop_nondet_sim_iteration_sa extendFactory g m body (Block.nondetElimM body σ₁).1 md σ₁ (Block.nondetElimM body σ₁).2
          h_body_sim h_g_gen h_g_in h_nofd_body oc ρ_src ρ'
          ({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P)
          hstarT.len h_eval_eq h_fail_eq h_off_g hwf
          h_wf₁ h_src_fresh h_fresh_g (h_tgt_iu_body HasBool.tt) true h_guard_def
          (.inr ⟨rfl, hrest, Nat.le_of_lt hl⟩))
  | .exit lbl md, _, _, _, _, oc, h_term =>
    cases oc with
    | none =>
      exfalso
      simp only [Env.outcomeConfig] at h_term
      obtain ⟨c, hstep, hrest⟩ := stmt_step_first_inv (extendFactory := extendFactory) _ ρ_src ρ' h_term
      cases hstep
      cases hrest with
      | step _ _ _ h _ => cases h
    | some lbl' =>
      simp only [Env.outcomeConfig] at h_term
      obtain ⟨c, hstep, hrest⟩ :=
        stmt_step_first_inv_to (extendFactory := extendFactory) _ ρ_src (.exiting lbl' ρ')
          (by intro ρ'' h; cases h) h_term
      cases hstep
      have h_eq : lbl' = lbl ∧ ρ' = ρ_src := by
        cases hrest with
        | refl => exact ⟨rfl, rfl⟩
        | step _ _ _ h _ => cases h
      obtain ⟨h_lbl_eq, h_ρ_eq⟩ := h_eq
      subst h_lbl_eq; subst h_ρ_eq
      refine ⟨h_src_fresh, ρ_tgt, ?_, h_agree, h_fail_eq, h_eval_eq, ?_⟩
      · simp only [Stmt.nondetElimM, Env.outcomeConfig]
        exact stmt_to_singleton_stmts_exiting (extendFactory := extendFactory) (.exit lbl' md) ρ_tgt ρ_tgt lbl'
          (.step _ _ _ StepStmt.step_exit (.refl _))
      · simp only [Stmt.nondetElimM]; exact h_tgt_fresh
  | .funcDecl d md, _, h_nofd, _, _, _, _ =>
    exact absurd h_nofd (by simp [Stmt.noFuncDecl])
  | .typeDecl t md, _, _, _, _, oc, h_term =>
    cases oc with
    | none =>
      simp only [Env.outcomeConfig] at h_term
      obtain ⟨c, hstep, hrest⟩ := stmt_step_first_inv (extendFactory := extendFactory) _ ρ_src ρ' h_term
      cases hstep
      have h_eq : ρ_src = ρ' := by
        cases hrest with
        | refl => rfl
        | step _ _ _ h _ => cases h
      subst h_eq
      refine ⟨h_src_fresh, ρ_tgt, ?_, h_agree, h_fail_eq, h_eval_eq, ?_⟩
      · simp only [Stmt.nondetElimM, Env.outcomeConfig]
        exact stmt_to_singleton_stmts (extendFactory := extendFactory) (.typeDecl t md) ρ_tgt ρ_tgt
          (.step _ _ _ StepStmt.step_typeDecl (.refl _))
      · simp only [Stmt.nondetElimM]; exact h_tgt_fresh
    | some lbl =>
      exfalso
      simp only [Env.outcomeConfig] at h_term
      obtain ⟨c, hstep, hrest⟩ :=
        stmt_step_first_inv_to (extendFactory := extendFactory) _ ρ_src (.exiting lbl ρ')
          (by intro ρ'' h; cases h) h_term
      cases hstep
      cases hrest with
      | step _ _ _ h _ => cases h
  termination_by sizeOf s

/-- The `StoreAgreement`-based general forward simulation (mutual with
`nondetElim_stmt_gen_sa`). -/
private theorem nondetElim_simulation_gen_sa {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen ndelimItePrefix sg).1)
            ∧ (∀ sg, Q (StringGenState.gen ndelimLoopPrefix sg).1))
    (extendFactory : ExtendFactory P)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (ρ_src ρ' ρ_tgt : Env P)
    (h_eval_eq : ρ_tgt.factory = ρ_src.factory)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : GenFreshStore Q σ ρ_tgt.store)
    (h_tgt_init_undef : ∀ y ∈ Block.initVars ss, ρ_tgt.store y = none)
    (h_unique : (Block.initVars ss).Nodup)
    (h_no_writes : SrcNoGenWrites (P := P) Q ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (oc : Option String)
    (h_term : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ_src) (Env.outcomeConfig oc ρ')) :
    (∀ t, Q t →
        ρ'.store (HasIdent.ident (P := P) t) = none)
      ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P) extendFactory
          (.stmts (Block.nondetElimM ss σ).1 ρ_tgt) (Env.outcomeConfig oc ρ_out)
        ∧ StoreAgreement ρ'.store ρ_out.store
        ∧ ρ_out.hasFailure = ρ'.hasFailure
        ∧ ρ_out.factory = ρ'.factory
        ∧ GenFreshStore Q (Block.nondetElimM ss σ).2 ρ_out.store := by
  match ss, h_no_writes, h_nofd, h_tgt_init_undef, h_unique, oc, h_term with
  | [], _, _, _, _, oc, h_term =>
    match oc, h_term with
    | none, h_term =>
      have h_eq : ρ_src = ρ' := stmts_nil_terminal_eq (extendFactory := extendFactory) ρ_src ρ' h_term
      subst h_eq
      refine ⟨h_src_fresh, ρ_tgt, ?_, h_agree, h_fail_eq, h_eval_eq, ?_⟩
      · simp only [Block.nondetElimM, Env.outcomeConfig]
        exact evalStmtsSmallNil P (EvalCmd P) extendFactory ρ_tgt
      · simp only [Block.nondetElimM]; exact h_tgt_fresh
    | some lbl, h_term =>
      exfalso
      simp only [Env.outcomeConfig] at h_term
      cases h_term with
      | step _ _ _ h h2 =>
        cases h with
        | step_stmts_nil =>
          cases h2 with
          | step _ _ _ h3 _ => cases h3
  | s :: rest, h_no_writes, h_nofd, h_tgt_init_undef, h_unique, oc, h_term =>
    rcases stmts_cons_outcome (extendFactory := extendFactory) s rest ρ_src ρ' oc h_term with
      ⟨lbl, h_oc_eq, h_s_exit⟩ | ⟨ρ_mid, h_s_run, h_rest_run⟩
    · subst h_oc_eq
      have h_no_writes_s_e : (∀ t : String, Q t → HasIdent.ident (P := P) t ∉ (Stmt.definedVars s false ++ Stmt.modifiedVars s)) := by
        intro t hQ hmem
        refine h_no_writes t hQ ?_
        rw [Block.definedVars, Block.modifiedVars]
        rcases List.mem_append.mp hmem with hd | hm
        · exact List.mem_append_left _ (List.mem_append_left _ hd)
        · exact List.mem_append_right _ (List.mem_append_left _ hm)
      have h_nofd_pair_e : Stmt.noFuncDecl s = true ∧ Block.noFuncDecl rest = true := by
        have : (Stmt.noFuncDecl s && Block.noFuncDecl rest) = true := by
          simpa only [Block.noFuncDecl] using h_nofd
        exact Bool.and_eq_true _ _ |>.mp this
      have h_tgt_iu_s : ∀ y ∈ Stmt.initVars s, ρ_tgt.store y = none := by
        intro y hy; exact h_tgt_init_undef y
          (by rw [Block.initVars_cons]; exact List.mem_append_left _ hy)
      have h_unique_pair_e : (Stmt.initVars s ++ Block.initVars rest).Nodup := by
        rw [Block.initVars_cons] at h_unique; exact h_unique
      have h_unique_s_e : (Stmt.initVars s).Nodup := (List.nodup_append.mp h_unique_pair_e).1
      obtain ⟨h_fresh', ρ_out, h_s_tgt, h_off', h_fail', h_eval', h_fresh_s⟩ :=
        nondetElim_stmt_gen_sa hQgen extendFactory s σ ρ_src ρ' ρ_tgt
          h_eval_eq h_fail_eq h_agree hwf
          h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_s h_unique_s_e h_no_writes_s_e h_nofd_pair_e.1
          (some lbl) h_s_exit
      refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', ?_⟩
      · rw [Block.nondetElimM_cons_out]
        refine stmts_cons_head_exiting_append (extendFactory := extendFactory) _ _ ρ_tgt ρ_out lbl ?_
        simpa only [Env.outcomeConfig] using h_s_tgt
      · have h_out_eq : (Block.nondetElimM (s :: rest) σ).2
            = (Block.nondetElimM rest (Stmt.nondetElimM s σ).2).2 := by
          rw [Block.nondetElimM]
          rcases hh : Stmt.nondetElimM s σ with ⟨ss_s, σ_s⟩
          rcases hk : Block.nondetElimM rest σ_s with ⟨ss_r, σ_r⟩
          simp only [hh, hk]
        rw [h_out_eq]
        exact GenFreshStore_mono (Block.nondetElimM_genStep rest (Stmt.nondetElimM s σ).2) h_fresh_s
    · have h_s_run' : StepStmtStar P (EvalCmd P) extendFactory (.stmt s ρ_src) (.terminal ρ_mid) :=
        h_s_run
      have h_no_writes_s : (∀ t : String, Q t → HasIdent.ident (P := P) t ∉ (Stmt.definedVars s false ++ Stmt.modifiedVars s)) := by
        intro t hQ hmem
        refine h_no_writes t hQ ?_
        rw [Block.definedVars, Block.modifiedVars]
        rcases List.mem_append.mp hmem with hd | hm
        · exact List.mem_append_left _ (List.mem_append_left _ hd)
        · exact List.mem_append_right _ (List.mem_append_left _ hm)
      have h_no_writes_rest : SrcNoGenWrites (P := P) Q rest := by
        intro t hQ hmem
        refine h_no_writes t hQ ?_
        rw [Block.definedVars, Block.modifiedVars]
        rcases List.mem_append.mp hmem with hd | hm
        · exact List.mem_append_left _ (List.mem_append_right _ hd)
        · exact List.mem_append_right _ (List.mem_append_right _ hm)
      have h_nofd_pair : Stmt.noFuncDecl s = true ∧ Block.noFuncDecl rest = true := by
        have : (Stmt.noFuncDecl s && Block.noFuncDecl rest) = true := by
          simpa only [Block.noFuncDecl] using h_nofd
        exact Bool.and_eq_true _ _ |>.mp this
      have h_nofd_s : Stmt.noFuncDecl s = true := h_nofd_pair.1
      have h_nofd_rest : Block.noFuncDecl rest = true := h_nofd_pair.2
      have h_tgt_iu_s : ∀ y ∈ Stmt.initVars s, ρ_tgt.store y = none := by
        intro y hy; exact h_tgt_init_undef y
          (by rw [Block.initVars_cons]; exact List.mem_append_left _ hy)
      -- Uniqueness splits into head/tail Nodup plus head–tail disjointness.
      have h_unique_pair : (Stmt.initVars s ++ Block.initVars rest).Nodup := by
        rw [Block.initVars_cons] at h_unique; exact h_unique
      have h_unique_s : (Stmt.initVars s).Nodup := (List.nodup_append.mp h_unique_pair).1
      have h_unique_rest : (Block.initVars rest).Nodup := (List.nodup_append.mp h_unique_pair).2.1
      have h_disjoint_s_rest : ∀ y ∈ Stmt.initVars s, y ∉ Block.initVars rest := by
        have h_disj := (List.nodup_append.mp h_unique_pair).2.2
        intro y hy_s hy_r; exact h_disj y hy_s y hy_r rfl
      obtain ⟨h_mid_fresh, ρ_mid_tgt, h_s_tgt, h_off_mid, h_fail_mid, h_eval_mid, h_fresh_mid⟩ :=
        nondetElim_stmt_gen_sa hQgen extendFactory s σ ρ_src ρ_mid ρ_tgt
          h_eval_eq h_fail_eq h_agree hwf
          h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_s h_unique_s h_no_writes_s h_nofd_s none h_s_run'
      have h_step_s : StringGenState.GenStep σ (Stmt.nondetElimM s σ).2 :=
        Stmt.nondetElimM_genStep s σ
      have h_wf₁ : StringGenState.WF (Stmt.nondetElimM s σ).2 := h_step_s.wf_mono h_wf_gen
      have h_eval_mid_src : ρ_mid.factory = ρ_src.factory :=
        smallStep_noFuncDecl_preserves_eval P (EvalCmd P) extendFactory s ρ_src ρ_mid h_nofd_s h_s_run'
      have hwf_mid : WellFormedSemanticEval ρ_mid.factory := h_eval_mid_src ▸ hwf
      have h_eval_eq' : ρ_mid_tgt.factory = ρ_mid.factory := h_eval_mid
      have h_fail_eq' : ρ_mid_tgt.hasFailure = ρ_mid.hasFailure := h_fail_mid
      -- Tail init-target undefinedness at the advanced TARGET env `ρ_mid_tgt`.  The
      -- rewritten head `(Stmt.nondetElimM s σ).1` runs `ρ_tgt → ρ_mid_tgt`.  A
      -- `y ∈ Block.initVars rest` was undefined in `ρ_tgt` (`h_tgt_init_undef`), is
      -- a source name disjoint from `s`'s inits (`h_disjoint_s_rest`, from uniqueness),
      -- and source names are non-`Q` (`h_no_writes_rest`).  By the output
      -- `initVars`-classification + `definedVars = initVars` (head is funcDecl-free),
      -- `y ∉ Block.definedVars (head)`, so its `none` slot survives the head's run.
      have h_tgt_iu_rest : ∀ y ∈ Block.initVars rest, ρ_mid_tgt.store y = none := by
        intro y hy
        have h_y_tgt_none : ρ_tgt.store y = none := h_tgt_init_undef y
          (by rw [Block.initVars_cons]; exact List.mem_append_right _ hy)
        have h_y_not_init_s : y ∉ Stmt.initVars s := fun hc => h_disjoint_s_rest y hc hy
        -- `y` is a source name, hence not a `Q`-kind generated guard.
        have h_y_not_def_head : y ∉ Block.definedVars (P := P) (C := Cmd P) (Stmt.nondetElimM s σ).1 false := by
          intro h_mem
          rcases Stmt.nondetElimM_initVars_classified_Q hQgen s σ y h_mem with h_orig | ⟨str, h_eq, h_Q⟩
          · exact h_y_not_init_s h_orig
          · -- `y = ident str` with `Q str`: but `y ∈ definedVars rest` is non-`Q`.
            have h_y_def_rest : y ∈ Block.definedVars (P := P) (C := Cmd P) rest false :=
              hy
            exact h_no_writes_rest str h_Q (h_eq ▸ List.mem_append_left _ h_y_def_rest)
        exact block_run_terminal_preserves_none_of_not_definedVars
          h_y_not_def_head h_y_tgt_none (by simpa only [Env.outcomeConfig] using h_s_tgt)
      obtain ⟨h_fresh', ρ_out, h_rest_tgt, h_off', h_fail', h_eval', h_fresh_out⟩ :=
        nondetElim_simulation_gen_sa hQgen extendFactory rest (Stmt.nondetElimM s σ).2 ρ_mid ρ' ρ_mid_tgt
          h_eval_eq' h_fail_eq' h_off_mid hwf_mid
          h_wf₁ h_mid_fresh h_fresh_mid h_tgt_iu_rest h_unique_rest h_no_writes_rest h_nofd_rest oc h_rest_run
      refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', ?_⟩
      · rw [Block.nondetElimM_cons_out]
        exact ReflTrans_Transitive _ _ _ _
          (stmts_prefix_terminal_append P (EvalCmd P) extendFactory _ _ ρ_tgt ρ_mid_tgt h_s_tgt)
          h_rest_tgt
      · have h_out_eq : (Block.nondetElimM (s :: rest) σ).2
            = (Block.nondetElimM rest (Stmt.nondetElimM s σ).2).2 := by
          rw [Block.nondetElimM]
          rcases hh : Stmt.nondetElimM s σ with ⟨ss_s, σ_s⟩
          rcases hk : Block.nondetElimM rest σ_s with ⟨ss_r, σ_r⟩
          simp only [hh, hk]
        rw [h_out_eq]; exact h_fresh_out
  termination_by sizeOf ss
end

/-- Forward simulation (per-constructor inductive lemma): every terminating
source execution of `ss` has a matching execution of `Block.nondetElim ss`
agreeing on the source's variables (`StoreAgreement`) and the failure flag. The
existential picks each guard's havoc value to match the source's
nondeterministic choice; `StoreAgreement`'s one-directionality hides the
generated guard variables.

This is the substantive simulation lemma; `nondetElim_sound` is its top-level
corollary.  It instantiates `nondetElim_simulation_gen_sa` at `ρ_tgt = ρ_src` and
the empty generator state. -/
private theorem nondetElim_simulation {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen ndelimItePrefix sg).1)
            ∧ (∀ sg, Q (StringGenState.gen ndelimLoopPrefix sg).1))
    (extendFactory : ExtendFactory P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_no_gen_suffix :
      ∀ s, Q s →
        ρ₀.store (HasIdent.ident (P := P) s) = none)
    (h_no_writes : SrcNoGenWrites (P := P) Q ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_store_inits : ∀ y ∈ Block.initVars ss, ρ₀.store y = none)
    (h_unique : Block.uniqueInits ss)
    (h_term : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ₀) (.terminal ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P) extendFactory
        (.stmts (Block.nondetElim ss) ρ₀) (.terminal ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure := by
  have h_tgt_fresh : GenFreshStore Q StringGenState.emp ρ₀.store := by
    intro s h_suf _; exact h_no_gen_suffix s h_suf
  obtain ⟨_, ρ_out, h_run, h_off, h_fl, _, _⟩ :=
    nondetElim_simulation_gen_sa hQgen extendFactory ss StringGenState.emp ρ₀ ρ' ρ₀
      rfl rfl (StoreAgreement.refl _) hwf
      StringGenState.wf_emp h_no_gen_suffix h_tgt_fresh h_store_inits h_unique h_no_writes h_nofd
      none h_term
  exact ⟨ρ_out, h_run, h_off, h_fl⟩

/-- Escaping sibling of `nondetElim_simulation`: surfaces the banked exiting
disjunct of `nondetElim_simulation_gen_sa`.  Every *escaping* source run of `ss`
(reaching `.exiting lbl ρ'`) is matched by an escaping run of `Block.nondetElim ss`
to the *same* label, agreeing on the source's variables and the failure flag.
Identical to the terminal `nondetElim_simulation` except it instantiates the
outcome selector at `some lbl`. -/
private theorem nondetElim_simulation_exit {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen ndelimItePrefix sg).1)
            ∧ (∀ sg, Q (StringGenState.gen ndelimLoopPrefix sg).1))
    (extendFactory : ExtendFactory P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_no_gen_suffix :
      ∀ s, Q s →
        ρ₀.store (HasIdent.ident (P := P) s) = none)
    (h_no_writes : SrcNoGenWrites (P := P) Q ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_store_inits : ∀ y ∈ Block.initVars ss, ρ₀.store y = none)
    (h_unique : Block.uniqueInits ss)
    (lbl : String)
    (h_exit : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ₀) (.exiting lbl ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P) extendFactory
        (.stmts (Block.nondetElim ss) ρ₀) (.exiting lbl ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure := by
  have h_tgt_fresh : GenFreshStore Q StringGenState.emp ρ₀.store := by
    intro s h_suf _; exact h_no_gen_suffix s h_suf
  obtain ⟨_, ρ_out, h_run, h_off, h_fl, _, _⟩ :=
    nondetElim_simulation_gen_sa hQgen extendFactory ss StringGenState.emp ρ₀ ρ' ρ₀
      rfl rfl (StoreAgreement.refl _) hwf
      StringGenState.wf_emp h_no_gen_suffix h_tgt_fresh h_store_inits h_unique h_no_writes h_nofd
      (some lbl) (by simpa only [Env.outcomeConfig] using h_exit)
  refine ⟨ρ_out, ?_, h_off, h_fl⟩
  simpa only [Env.outcomeConfig] using h_run

/-- Forward simulation: every terminating source execution of `ss` has a
matching execution of `Block.nondetElim ss` agreeing on the source's variables
(`StoreAgreement`) and the failure flag. The existential picks each guard's
havoc value to match the source's nondeterministic choice; `StoreAgreement`'s
one-directionality hides the generated guard variables.

The well-formedness of the evaluator is carried as a single
`WellFormedSemanticEval` bundle so this per-pass simulation shares the
initial-environment interface (WF-eval facts on `ρ₀.factory`, per-kind
freshness, and the source block-shape predicates) that the sibling pass
proofs are stated over. -/
theorem nondetElim_sound {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    (extendFactory : ExtendFactory P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_no_gen_suffix :
      ∀ s, String.HasUnderscoreDigitSuffix s →
        ρ₀.store (HasIdent.ident (P := P) s) = none)
    (h_no_writes : SrcNoGenWrites (P := P) String.HasUnderscoreDigitSuffix ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_store_inits : ∀ y ∈ Block.initVars ss, ρ₀.store y = none)
    (h_unique : Block.uniqueInits ss)
    (h_term : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ₀) (.terminal ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P) extendFactory
        (.stmts (Block.nondetElim ss) ρ₀) (.terminal ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure :=
  nondetElim_simulation
    (Q := String.HasUnderscoreDigitSuffix)
    ⟨fun sg => StringGenState.gen_hasUnderscoreDigitSuffix ndelimItePrefix sg,
     fun sg => StringGenState.gen_hasUnderscoreDigitSuffix ndelimLoopPrefix sg⟩
    extendFactory ss ρ₀ ρ'
    hwf h_no_gen_suffix h_no_writes h_nofd
    h_store_inits h_unique h_term

/-! ### The nondetElim label *kind*

`nondetElim` generates labels under exactly two prefixes: `ndelimItePrefix` and
`ndelimLoopPrefix`.  `ndelimKind s` is the precise predicate "`s` is a label this
pass could have generated": it carries the matching generator prefix and is equal to
some `gen`-output.  This is the per-kind `Q` to instantiate the kind-generalized
simulation at, replacing the blanket `HasUnderscoreDigitSuffix` (which would
overcommit a composition partner to keeping *every* gen-shaped name fresh). -/

/-- A label that `nondetElim` could have generated: it has the ite- or loop-prefix
and equals a corresponding `gen` output. -/
@[expose] def ndelimKind (s : String) : Prop :=
  (∃ sg, String.HasGenPrefix ndelimItePrefix s
      ∧ s = (StringGenState.gen ndelimItePrefix sg).1)
  ∨ (∃ sg, String.HasGenPrefix ndelimLoopPrefix s
      ∧ s = (StringGenState.gen ndelimLoopPrefix sg).1)

/-- The two prefixes `nondetElim` generates under both land inside `ndelimKind`:
this is exactly the `hQgen` conjunction at `Q := ndelimKind`. -/
theorem ndelimKind_gen :
    (∀ sg, ndelimKind (StringGenState.gen ndelimItePrefix sg).1)
  ∧ (∀ sg, ndelimKind (StringGenState.gen ndelimLoopPrefix sg).1) := by
  refine ⟨fun sg => ?_, fun sg => ?_⟩
  · exact Or.inl ⟨sg, StringGenState.gen_hasGenPrefix ndelimItePrefix sg, rfl⟩
  · exact Or.inr ⟨sg, StringGenState.gen_hasGenPrefix ndelimLoopPrefix sg, rfl⟩

section NondetElimStructural
variable {P : PureExpr}

theorem Stmt.nondetElimM_block_state [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P] (lbl : String) (bss : List (Stmt P (Cmd P)))
    (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.block lbl bss md) σ).2 = (Block.nondetElimM bss σ).2 := by
  rw [Stmt.nondetElimM]; rcases h : Block.nondetElimM bss σ with ⟨bss', σ'⟩; simp only [h]

theorem Stmt.nondetElimM_ite_det_state [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P] (e : P.Expr) (tss ess : List (Stmt P (Cmd P)))
    (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.ite (.det e) tss ess md) σ).2 =
      (Block.nondetElimM ess (Block.nondetElimM tss σ).2).2 := by
  rw [Stmt.nondetElimM]
  rcases h₁ : Block.nondetElimM tss σ with ⟨tss', σ₁⟩
  rcases h₂ : Block.nondetElimM ess σ₁ with ⟨ess', σ₂⟩
  simp only [h₁, h₂]

theorem Stmt.nondetElimM_ite_nondet_state [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P] (tss ess : List (Stmt P (Cmd P)))
    (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2 =
      (Block.nondetElimM ess (Block.nondetElimM tss (StringGenState.gen ndelimItePrefix σ).2).2).2 := by
  rw [Stmt.nondetElimM]
  rcases hg : StringGenState.gen ndelimItePrefix σ with ⟨g, σ₁⟩
  rcases h₁ : Block.nondetElimM tss σ₁ with ⟨tss', σ₂⟩
  rcases h₂ : Block.nondetElimM ess σ₂ with ⟨ess', σ₃⟩
  simp only [hg, h₁, h₂]

theorem Stmt.nondetElimM_loop_det_state [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P] (e : P.Expr) (m : Option P.Expr)
    (inv : List (String × P.Expr)) (body : List (Stmt P (Cmd P)))
    (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.loop (.det e) m inv body md) σ).2 = (Block.nondetElimM body σ).2 := by
  rw [Stmt.nondetElimM]; rcases h : Block.nondetElimM body σ with ⟨body', σ'⟩; simp only [h]

theorem Stmt.nondetElimM_loop_nondet_state [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P] (m : Option P.Expr) (inv : List (String × P.Expr))
    (body : List (Stmt P (Cmd P))) (md : MetaData P) (σ : StringGenState) :
    (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2 =
      (Block.nondetElimM body (StringGenState.gen ndelimLoopPrefix σ).2).2 := by
  rw [Stmt.nondetElimM]
  rcases hg : StringGenState.gen ndelimLoopPrefix σ with ⟨g, σ₁⟩
  rcases h : Block.nondetElimM body σ₁ with ⟨body', σ₂⟩
  simp only [hg, h]

theorem Block.nondetElimM_cons_state [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P] (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P)))
    (σ : StringGenState) :
    (Block.nondetElimM (s :: rest) σ).2 = (Block.nondetElimM rest (Stmt.nondetElimM s σ).2).2 := by
  rw [Block.nondetElimM]
  rcases h₁ : Stmt.nondetElimM s σ with ⟨ss_s, σ₁⟩
  rcases h₂ : Block.nondetElimM rest σ₁ with ⟨ss_r, σ₂⟩
  simp only [h₁, h₂]

/-- An `init` command modifies nothing (it *defines*, not modifies). -/
private theorem init_modVars (x : P.Ident) (ty : P.Ty) (e : ExprOrNondet P)
    (md : MetaData P) :
    HasVarsImp.modifiedVars (HasInit.init (CmdT := Cmd P) x ty e md) =
      ([] : List P.Ident) := by
  with_unfolding_all rfl

/-- A `havoc x` command modifies exactly `[x]`. -/
private theorem havoc_modVars (x : P.Ident) (md : MetaData P) :
    HasVarsImp.modifiedVars (HasHavoc.havoc (CmdT := Cmd P) x md) = [x] := by
  with_unfolding_all rfl

/-- Every `initVars` element of the `nondetElim` output of a statement is either
an original source `initVars` element or a freshly-generated `ndelimKind` guard. -/
theorem Stmt.nondetElimM_initVars_classified [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    ∀ x ∈ Block.initVars (P := P) (Stmt.nondetElimM s σ).1,
      x ∈ Stmt.initVars s ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ ndelimKind str) :=
  Stmt.nondetElimM_initVars_classified_Q ndelimKind_gen s σ

/-- Block-level `initVars` classification of the `nondetElim` output. -/
theorem Block.nondetElimM_initVars_classified [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ∀ x ∈ Block.initVars (P := P) (Block.nondetElimM ss σ).1,
      x ∈ Block.initVars ss ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ ndelimKind str) :=
  Block.nondetElimM_initVars_classified_Q ndelimKind_gen ss σ

mutual
/-- Every `modifiedVars` element of the `nondetElim` output of a statement is
either an original source `modifiedVars` element or a freshly-generated
`ndelimKind` guard (the loop re-havoc target). -/
theorem Stmt.nondetElimM_modVars_classified [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    ∀ x ∈ Block.modifiedVars (P := P) (Stmt.nondetElimM s σ).1,
      x ∈ Stmt.modifiedVars s ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ ndelimKind str) := by
  match s with
  | .cmd c =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.modifiedVars, List.append_nil] at hx
      exact Or.inl hx
  | .block lbl bss md =>
      intro x hx
      rw [Stmt.nondetElimM_block_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx ⊢
      exact Block.nondetElimM_modVars_classified bss σ x hx
  | .ite (.det e) tss ess md =>
      intro x hx
      rw [Stmt.nondetElimM_ite_det_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil, List.mem_append] at hx ⊢
      rcases hx with h | h
      · rcases Block.nondetElimM_modVars_classified tss σ x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_modVars_classified ess _ x h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .ite .nondet tss ess md =>
      intro x hx
      rw [Stmt.nondetElimM_ite_nondet_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, init_modVars, List.nil_append,
        List.append_nil, List.mem_append] at hx ⊢
      rcases hx with h | h
      · rcases Block.nondetElimM_modVars_classified tss _ x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_modVars_classified ess _ x h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .loop (.det e) m inv body md =>
      intro x hx
      rw [Stmt.nondetElimM_loop_det_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx ⊢
      exact Block.nondetElimM_modVars_classified body σ x hx
  | .loop .nondet m inv body md =>
      intro x hx
      rw [Stmt.nondetElimM_loop_nondet_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, init_modVars, List.nil_append,
        List.append_nil] at hx ⊢
      rw [Block.modifiedVars_append] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, havoc_modVars, List.append_nil,
        List.mem_append, List.mem_singleton] at hx ⊢
      rcases hx with h | h_g
      · rcases Block.nondetElimM_modVars_classified body _ x h with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
      · exact Or.inr ⟨(StringGenState.gen ndelimLoopPrefix σ).1, h_g, ndelimKind_gen.2 σ⟩
  | .exit lbl md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  | .funcDecl d md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  | .typeDecl t md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  termination_by sizeOf s

/-- Block-level `modifiedVars` classification of the `nondetElim` output. -/
theorem Block.nondetElimM_modVars_classified [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ∀ x ∈ Block.modifiedVars (P := P) (Block.nondetElimM ss σ).1,
      x ∈ Block.modifiedVars ss ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ ndelimKind str) := by
  match ss with
  | [] =>
      intro x hx
      simp only [Block.nondetElimM, Block.modifiedVars] at hx
      exact absurd hx List.not_mem_nil
  | s :: rest =>
      intro x hx
      rw [Block.nondetElimM_cons_out, Block.modifiedVars_append] at hx
      simp only [List.mem_append] at hx
      simp only [Block.modifiedVars, List.mem_append]
      rcases hx with h | h
      · rcases Stmt.nondetElimM_modVars_classified s σ x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_modVars_classified rest _ x h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  termination_by sizeOf ss
end

section NondetElimCoverage

variable [HasFvar P] [HasBoolOps P] [HasIdent P]

mutual
/-- `Stmt.nondetElimM` preserves exit coverage: the fresh guard `init`/`havoc`
commands it emits are `.cmd`s (trivially covered), and it never introduces or
relabels a `.block`/`.exit`. -/
theorem Stmt.nondetElimM_exitsCoveredByBlocks
    (labels : List String) (s : Stmt P (Cmd P)) (σ : StringGenState)
    (h : Stmt.exitsCoveredByBlocks labels s) :
    Block.exitsCoveredByBlocks labels
      (Stmt.nondetElimM s σ).1 := by
  match s with
  | .cmd c => simp only [Stmt.nondetElimM]; exact coveredBlock_singleton labels (.cmd c) trivial
  | .block lbl bss md =>
    rw [Stmt.nondetElimM_block_out]
    exact coveredBlock_singleton labels (.block lbl _ md)
      (Block.nondetElimM_exitsCoveredByBlocks (lbl :: labels) bss _
        (by simpa [Stmt.exitsCoveredByBlocks] using h))
  | .ite (.det e) tss ess md =>
    rw [Stmt.nondetElimM_ite_det_out]
    obtain ⟨ht, he⟩ := h
    exact coveredBlock_singleton labels (.ite (.det e) _ _ md)
      ⟨Block.nondetElimM_exitsCoveredByBlocks labels tss _ ht,
       Block.nondetElimM_exitsCoveredByBlocks labels ess _ he⟩
  | .ite .nondet tss ess md =>
    rw [Stmt.nondetElimM_ite_nondet_out]
    obtain ⟨ht, he⟩ := h
    refine ⟨trivial, ?_, trivial⟩
    exact ⟨Block.nondetElimM_exitsCoveredByBlocks labels tss _ ht,
      Block.nondetElimM_exitsCoveredByBlocks labels ess _ he⟩
  | .loop (.det e) m inv body md =>
    rw [Stmt.nondetElimM_loop_det_out]
    exact coveredBlock_singleton labels (.loop (.det e) m inv _ md)
      (Block.nondetElimM_exitsCoveredByBlocks labels body _
        (by simpa [Stmt.exitsCoveredByBlocks] using h))
  | .loop .nondet m inv body md =>
    rw [Stmt.nondetElimM_loop_nondet_out]
    refine ⟨trivial, ?_, trivial⟩
    exact block_exitsCoveredByBlocks_append labels _ _
      (Block.nondetElimM_exitsCoveredByBlocks labels body _
        (by simpa [Stmt.exitsCoveredByBlocks] using h))
      (⟨trivial, trivial⟩ :
        Block.exitsCoveredByBlocks labels
          [Stmt.cmd (HasHavoc.havoc (HasIdent.ident (P := P)
            (StringGenState.gen ndelimLoopPrefix σ).1) md)])
  | .exit lbl md =>
    simp only [Stmt.nondetElimM]
    exact coveredBlock_singleton labels (.exit lbl md) h
  | .funcDecl d md =>
    simp only [Stmt.nondetElimM]
    exact coveredBlock_singleton labels (.funcDecl d md) trivial
  | .typeDecl t md =>
    simp only [Stmt.nondetElimM]
    exact coveredBlock_singleton labels (.typeDecl t md) trivial
  termination_by sizeOf s

/-- `Block.nondetElimM` preserves exit coverage. -/
theorem Block.nondetElimM_exitsCoveredByBlocks
    (labels : List String) (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h : Block.exitsCoveredByBlocks labels ss) :
    Block.exitsCoveredByBlocks labels
      (Block.nondetElimM ss σ).1 := by
  match ss with
  | [] => simp only [Block.nondetElimM]; exact trivial
  | s :: rest =>
    rw [Block.nondetElimM_cons_out]
    exact block_exitsCoveredByBlocks_append labels _ _
      (Stmt.nondetElimM_exitsCoveredByBlocks labels s σ h.1)
      (Block.nondetElimM_exitsCoveredByBlocks labels rest _ h.2)
  termination_by sizeOf ss
end

/-- `Block.nondetElim` preserves exit coverage (top-level wrapper). -/
theorem Block.nondetElim_exitsCoveredByBlocks
    (ss : List (Stmt P (Cmd P)))
    (h : Block.exitsCoveredByBlocks [] ss) :
    Block.exitsCoveredByBlocks [] (Block.nondetElim ss) :=
  Block.nondetElimM_exitsCoveredByBlocks [] ss StringGenState.emp h

end NondetElimCoverage

end NondetElimStructural

/-- Kind-generalized soundness: `nondetElim` is sound for any source store whose
only `ndelimKind`-labelled slots are undefined, and any source block that never
writes an `ndelimKind` label.  Weaker entry precondition than `nondetElim_sound`
(it constrains only the labels this pass generates, not every gen-shaped name),
which is what lets a composition partner — e.g. one that generates under a disjoint
prefix — satisfy it vacuously. -/
theorem nondetElim_sound_kind {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    (extendFactory : ExtendFactory P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_no_gen_suffix : Env.varsUndefined (P := P) ndelimKind ρ₀)
    (h_no_writes : SrcNoGenWrites (P := P) ndelimKind ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_store_inits : ∀ y ∈ Block.initVars ss, ρ₀.store y = none)
    (h_unique : Block.uniqueInits ss)
    (h_term : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ₀) (.terminal ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P) extendFactory
        (.stmts (Block.nondetElim ss) ρ₀) (.terminal ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure :=
  nondetElim_simulation
    (Q := ndelimKind) ndelimKind_gen
    extendFactory ss ρ₀ ρ'
    hwf (Env.varsUndefined_iff.mp h_no_gen_suffix) h_no_writes h_nofd
    h_store_inits h_unique h_term

/-- Escaping companion of `nondetElim_sound_kind` (at `Q := ndelimKind`): every
escaping source run of `ss` reaching `.exiting lbl` is matched by an escaping run
of `Block.nondetElim ss` to the *same* label, agreeing on the source's variables
and the failure flag.  A thin forwarder to `nondetElim_simulation_exit`; the
`Env.varsUndefined` store precondition unfolds to the explicit per-kind
freshness fact the simulation consumes. -/
theorem nondetElim_sound_kind_exit {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    (extendFactory : ExtendFactory P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_no_gen_suffix : Env.varsUndefined (P := P) ndelimKind ρ₀)
    (h_no_writes : SrcNoGenWrites (P := P) ndelimKind ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_store_inits : ∀ y ∈ Block.initVars ss, ρ₀.store y = none)
    (h_unique : Block.uniqueInits ss)
    (lbl : String)
    (h_exit : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ₀) (.exiting lbl ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P) extendFactory
        (.stmts (Block.nondetElim ss) ρ₀) (.exiting lbl ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure :=
  nondetElim_simulation_exit
    (Q := ndelimKind) ndelimKind_gen
    extendFactory ss ρ₀ ρ'
    hwf (Env.varsUndefined_iff.mp h_no_gen_suffix) h_no_writes h_nofd
    h_store_inits h_unique lbl h_exit

/-! ### Compositional-input soundness (`nondetElim_sound_kind_compositional*`)

Unlike the diagonal kind wrappers above, these run the target from an arbitrary
`ρ_tgt` that store-agrees with the source `ρ₀` (an overapproximating target
store), as the up-to-relation overapproximation instance needs.  Thin forwarders
to the `_sa` engine at `σ := StringGenState.emp`, `Q := ndelimKind`. -/

/-- A terminating source run of `ss` from `ρ₀` is matched by a run of
`Block.nondetElim ss` from any store-agreeing target `ρ_tgt`, with the outputs
again store-agreeing (the `ndelimKind`-keyed compositional soundness the
overapproximation instance consumes). -/
theorem nondetElim_sound_kind_compositional {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    (extendFactory : ExtendFactory P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' ρ_tgt : Env P)
    (h_eval_eq : ρ_tgt.factory = ρ₀.factory)
    (h_fail_eq : ρ_tgt.hasFailure = ρ₀.hasFailure)
    (h_agree : StoreAgreement ρ₀.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_src_no_gen : Env.varsUndefined (P := P) ndelimKind ρ₀)
    (h_tgt_no_gen : Env.varsUndefined (P := P) ndelimKind ρ_tgt)
    (h_tgt_inits : ∀ y ∈ Block.initVars ss, ρ_tgt.store y = none)
    (h_no_writes : SrcNoGenWrites (P := P) ndelimKind ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_unique : Block.uniqueInits ss)
    (h_term : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ₀) (.terminal ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P) extendFactory
        (.stmts (Block.nondetElim ss) ρ_tgt) (.terminal ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure := by
  have h_tgt_fresh : GenFreshStore ndelimKind StringGenState.emp ρ_tgt.store := by
    intro s h_suf _; exact Env.varsUndefined_apply h_tgt_no_gen s h_suf
  obtain ⟨_, ρ_out, h_run, h_off, h_fl, _, _⟩ :=
    nondetElim_simulation_gen_sa ndelimKind_gen extendFactory ss StringGenState.emp ρ₀ ρ' ρ_tgt
      h_eval_eq h_fail_eq h_agree hwf
      StringGenState.wf_emp (Env.varsUndefined_iff.mp h_src_no_gen) h_tgt_fresh h_tgt_inits h_unique h_no_writes h_nofd
      none h_term
  exact ⟨ρ_out, h_run, h_off, h_fl⟩

/-- Escaping companion of `nondetElim_sound_kind_compositional`. -/
theorem nondetElim_sound_kind_exit_compositional {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    (extendFactory : ExtendFactory P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' ρ_tgt : Env P)
    (h_eval_eq : ρ_tgt.factory = ρ₀.factory)
    (h_fail_eq : ρ_tgt.hasFailure = ρ₀.hasFailure)
    (h_agree : StoreAgreement ρ₀.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_src_no_gen : Env.varsUndefined (P := P) ndelimKind ρ₀)
    (h_tgt_no_gen : Env.varsUndefined (P := P) ndelimKind ρ_tgt)
    (h_tgt_inits : ∀ y ∈ Block.initVars ss, ρ_tgt.store y = none)
    (h_no_writes : SrcNoGenWrites (P := P) ndelimKind ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_unique : Block.uniqueInits ss)
    (lbl : String)
    (h_exit : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ₀) (.exiting lbl ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P) extendFactory
        (.stmts (Block.nondetElim ss) ρ_tgt) (.exiting lbl ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure := by
  have h_tgt_fresh : GenFreshStore ndelimKind StringGenState.emp ρ_tgt.store := by
    intro s h_suf _; exact Env.varsUndefined_apply h_tgt_no_gen s h_suf
  obtain ⟨_, ρ_out, h_run, h_off, h_fl, _, _⟩ :=
    nondetElim_simulation_gen_sa ndelimKind_gen extendFactory ss StringGenState.emp ρ₀ ρ' ρ_tgt
      h_eval_eq h_fail_eq h_agree hwf
      StringGenState.wf_emp (Env.varsUndefined_iff.mp h_src_no_gen) h_tgt_fresh h_tgt_inits h_unique h_no_writes h_nofd
      (some lbl) (by simpa only [Env.outcomeConfig] using h_exit)
  refine ⟨ρ_out, ?_, h_off, h_fl⟩
  simpa only [Env.outcomeConfig] using h_run

/-! ## Failing-config forward simulation (`nondetElim_to_fail`)

`nondetElim_simulation` and its kind/exit wrappers are *endpoint*-keyed: each
consumes a source run reaching a terminal/exiting outcome.  A reachable *failing*
configuration need not lie on such a run (an `assert` only OR-s the cumulative
`hasFailure` flag and continues, so a failing run may diverge or get stuck).  The
`_to_fail` siblings below remove the endpoint demand: a reachable failing source
configuration is matched by a reachable failing configuration of
`Block.nondetElim ss`, running both from the same start.

The construction mirrors the terminal simulation but keys on the *failing
configuration* as the halting condition.  Each statement / loop iteration that
*completed before the failure* terminated, so the existing terminal simulation
applies to it verbatim and advances the store relation; only the single statement
/ iteration that *contains* the failure is transported by a bare failing-config
reach (no terminal demand).  The loop arms induct on a `Nat` fuel bounding the
*source* run length — finite because failure is monotone — never on the loop's
termination. -/

/-- Failing-config deterministic-loop iteration.  `to_fail` has no output
relation, so only the input side is re-threaded; `h_body_sim` is the `_sa`
terminal body simulation. -/
private theorem nondetElim_loop_det_to_fail_iteration_sa {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (extendFactory : ExtendFactory P)
    (e : P.Expr) (m : Option P.Expr) {inv : List (String × P.Expr)}
    (body body' : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ σ_out : StringGenState)
    (h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
      ρb_tgt.factory = ρb_src.factory →
      ρb_tgt.hasFailure = ρb_src.hasFailure →
      StoreAgreement ρb_src.store ρb_tgt.store →
      WellFormedSemanticEval ρb_src.factory →
      StringGenState.WF σ →
      (∀ t, Q t →
        ρb_src.store (HasIdent.ident (P := P) t) = none) →
      GenFreshStore Q σ ρb_tgt.store →
      (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
      StepStmtStar P (EvalCmd P) extendFactory (.stmts body ρb_src) (Env.outcomeConfig oc_b ρb') →
      (∀ t, Q t →
          ρb'.store (HasIdent.ident (P := P) t) = none)
        ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P) extendFactory
            (.stmts body' ρb_tgt) (Env.outcomeConfig oc_b ρb_out)
          ∧ StoreAgreement ρb'.store ρb_out.store
          ∧ ρb_out.hasFailure = ρb'.hasFailure
          ∧ ρb_out.factory = ρb'.factory
          ∧ GenFreshStore Q σ_out ρb_out.store)
    -- Failing per-iteration body simulation, used for the FAILING iteration.
    (h_body_sim_fail : ∀ (ρb_src ρb_tgt : Env P) (d : Config P (Cmd P)),
      ρb_tgt.factory = ρb_src.factory →
      ρb_tgt.hasFailure = ρb_src.hasFailure →
      StoreAgreement ρb_src.store ρb_tgt.store →
      WellFormedSemanticEval ρb_src.factory →
      StringGenState.WF σ →
      (∀ t, Q t →
        ρb_src.store (HasIdent.ident (P := P) t) = none) →
      GenFreshStore Q σ ρb_tgt.store →
      (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
      StepStmtStar P (EvalCmd P) extendFactory (.stmts body ρb_src) d →
      d.getEnv.hasFailure = true →
      ∃ d', StepStmtStar P (EvalCmd P) extendFactory (.stmts body' ρb_tgt) d'
        ∧ d'.getEnv.hasFailure = true)
    (h_nofd_body : Block.noFuncDecl body = true)
    (ρ_src ρ_tgt : Env P) (a' : Config P (Cmd P)) (n : Nat)
    (h_eval_eq : ρ_tgt.factory = ρ_src.factory)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : GenFreshStore Q σ ρ_tgt.store)
    (h_tgt_init_undef : ∀ y ∈ Block.initVars body, ρ_tgt.store y = none)
    (hT : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
      (.stmt (.loop (.det e) m inv body md) ρ_src) a')
    (h_a'_fail : a'.getEnv.hasFailure = true)
    (hlen : hT.len ≤ n) :
    ∃ d, StepStmtStar P (EvalCmd P) extendFactory
        (.stmt (.loop (.det e) m inv body' md) ρ_tgt) d
      ∧ d.getEnv.hasFailure = true := by
  induction n generalizing ρ_src ρ_tgt a' with
  | zero =>
    match hT, hlen with
    | .refl _, _ =>
      have : ρ_src.hasFailure = true := by simpa [Config.getEnv] using h_a'_fail
      exact ⟨.stmt (.loop (.det e) m inv body' md) ρ_tgt, .refl _,
        by simpa [Config.getEnv] using (h_fail_eq.trans this)⟩
    | .step _ _ _ _ _, hl => simp [ReflTransT.len] at hl
  | succ n ih =>
    match hT, hlen with
    | .refl _, _ =>
      have : ρ_src.hasFailure = true := by simpa [Config.getEnv] using h_a'_fail
      exact ⟨.stmt (.loop (.det e) m inv body' md) ρ_tgt, .refl _,
        by simpa [Config.getEnv] using (h_fail_eq.trans this)⟩
    | .step _ _ _ (StepStmt.step_loop_exit hg_false hwfb_step) hrest, hl_succ =>
      have ha''_eq : a' = .terminal ({ ρ_src with hasFailure := ρ_src.hasFailure || false } : Env P) :=
        reflTransT_from_terminal P extendFactory (by simpa only [Bool.or_false] using hrest)
      rw [ha''_eq] at h_a'_fail
      have : ρ_src.hasFailure = true := by simpa [Config.getEnv, Bool.or_false] using h_a'_fail
      exact ⟨.stmt (.loop (.det e) m inv body' md) ρ_tgt, .refl _,
        by simpa [Config.getEnv] using (h_fail_eq.trans this)⟩
    | .step _ _ _ (StepStmt.step_loop_enter hg_true hwfb_step) hrest, hl_succ =>
      have h_cond_t : P.eval ρ_tgt.factory ρ_tgt.store e = some HasBool.tt := by
        rw [h_eval_eq]
        exact hwf.mono e HasBool.tt ρ_src.store ρ_tgt.store
          (storeAgreement_supplies_mono_premise ρ_src.store ρ_tgt.store h_agree) hg_true
      have h_step_enter : StepStmtStar P (EvalCmd P) extendFactory
          (.stmt (.loop (.det e) m inv body' md) ρ_tgt)
          (.seq (.block .none ρ_tgt.store ρ_tgt.factory (.stmts body' ρ_tgt))
            [.loop (.det e) m inv body' md]) :=
        .step _ _ _ (StepStmt.step_loop_enter
          h_cond_t (h_eval_eq ▸ hwf.bool)) (.refl _)
      rcases seqT_reaches_failing' P extendFactory hrest h_a'_fail with hA | hB
      · -- CASE A: the failure is inside THIS iteration's body block.
        obtain ⟨d_blk, h_blk_run, hd_blk_fail, _⟩ := hA
        have ⟨d_body, h_body_run, hd_body_fail, _⟩ :=
          blockT_none_reaches_failing' P extendFactory h_blk_run hd_blk_fail
        have ⟨d', h_body_tgt, hd'_fail⟩ :=
          h_body_sim_fail ρ_src ρ_tgt d_body h_eval_eq h_fail_eq h_agree hwf
            h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef
            (reflTransT_to_prop h_body_run) hd_body_fail
        have h_blk_tgt : StepStmtStar P (EvalCmd P) extendFactory
            (.block .none ρ_tgt.store ρ_tgt.factory (.stmts body' ρ_tgt))
            (.block .none ρ_tgt.store ρ_tgt.factory d') :=
          block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_tgt.store ρ_tgt.factory h_body_tgt
        refine ⟨.seq (.block .none ρ_tgt.store ρ_tgt.factory d')
          [.loop (.det e) m inv body' md],
          ReflTrans_Transitive _ _ _ _ h_step_enter
            (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_blk_tgt), ?_⟩
        simpa [Config.getEnv] using hd'_fail
      · -- CASE B: this iteration's body terminated; recurse on the next iteration.
        obtain ⟨ρ_blk_inner, d_rest, h_blk_term, h_loop_rest, hd_rest_fail, hlen_rest⟩ := hB
        have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
          blockT_none_reaches_terminal (extendFactory := extendFactory) h_blk_term
        subst heq_ρ_block
        have h_body_run : StepStmtStar P (EvalCmd P) extendFactory
            (.stmts body ρ_src) (Env.outcomeConfig none ρ_inner) := reflTransT_to_prop h_inner_term
        obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner,
            h_eval_inner, h_fresh_inner⟩ :=
          h_body_sim none ρ_src ρ_inner ρ_tgt h_eval_eq h_fail_eq h_agree hwf
            h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef h_body_run
        have h_tgt_fac_eq : ρ_inner_tgt.factory = ρ_tgt.factory := by
          rw [h_eval_inner, h_eval_eq]
          exact block_noFuncDecl_preserves_factory P (EvalCmd P) extendFactory body ρ_src ρ_inner
            h_nofd_body (by simpa only [Env.outcomeConfig] using h_body_run)
        have h_blk_tgt_term : StepStmtStar P (EvalCmd P) extendFactory
            (.block .none ρ_tgt.store ρ_tgt.factory (.stmts body' ρ_tgt))
            (.terminal ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store } : Env P)) := by
          have h_body_tgt' : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts body' ρ_tgt)
              (.terminal ρ_inner_tgt) := by
            simpa only [Env.outcomeConfig] using h_body_tgt
          refine ReflTrans_Transitive _ _ _ _
            (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_tgt.store ρ_tgt.factory h_body_tgt') ?_
          have hcfg : ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store } : Env P)
              = ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store, factory := ρ_tgt.factory } : Env P) := by
            rw [← h_tgt_fac_eq]
          rw [hcfg]
          exact .step _ _ _ StepStmt.step_block_done (.refl _)
        have h_step_after_iter : StepStmtStar P (EvalCmd P) extendFactory
            (.stmt (.loop (.det e) m inv body' md) ρ_tgt)
            (.stmts [.loop (.det e) m inv body' md]
              ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store } : Env P)) :=
          ReflTrans_Transitive _ _ _ _ h_step_enter
            (ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_blk_tgt_term)
              (.step _ _ _ StepStmt.step_seq_done (.refl _)))
        have h_eval_inner_src : ρ_inner.factory = ρ_src.factory :=
          block_noFuncDecl_preserves_factory P (EvalCmd P) extendFactory body ρ_src ρ_inner h_nofd_body
            (by simpa only [Env.outcomeConfig] using h_body_run)
        let ρ_src_next : Env P :=
          { store := projectStore ρ_src.store ρ_inner.store, factory := ρ_src.factory,
            hasFailure := ρ_inner.hasFailure }
        let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store }
        have h_eval_next : ρ_src_next.factory = ρ_src.factory := rfl
        have hwf_next : WellFormedSemanticEval ρ_src_next.factory := by rw [h_eval_next]; exact hwf
        have h_eval_eq_next : ρ_tgt_next.factory = ρ_src_next.factory := by
          show ρ_inner_tgt.factory = ρ_src.factory; rw [h_eval_inner, h_eval_inner_src]
        have h_fail_eq_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
          show ρ_inner_tgt.hasFailure = ρ_inner.hasFailure; exact h_fail_inner
        have h_agree_next : StoreAgreement ρ_src_next.store ρ_tgt_next.store :=
          StoreAgreement.of_projectStore_parents h_agree h_off_inner
        have h_src_fresh_next : ∀ t, Q t →
            ρ_src_next.store (HasIdent.ident (P := P) t) = none := by
          intro t h_suf
          show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
          show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
              then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
          by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
          · rw [if_pos hp]; exact h_inner_fresh t h_suf
          · rw [if_neg hp]
        have h_tgt_fresh_next : GenFreshStore Q σ ρ_tgt_next.store := by
          intro s h_suf h_notin
          show projectStore ρ_tgt.store ρ_inner_tgt.store (HasIdent.ident (P := P) s) = none
          show (if (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
              then ρ_inner_tgt.store (HasIdent.ident (P := P) s) else none) = none
          rw [h_tgt_fresh s h_suf h_notin]; rfl
        have h_tgt_init_undef_next : ∀ y ∈ Block.initVars body, ρ_tgt_next.store y = none := by
          intro y hy
          show projectStore ρ_tgt.store ρ_inner_tgt.store y = none
          show (if (ρ_tgt.store y).isSome then ρ_inner_tgt.store y else none) = none
          rw [h_tgt_init_undef y hy]; rfl
        have ⟨d_loop, h_loop_stmt, hd_loop_fail, hlen_loop⟩ :=
          stmts_singleton_reaches_failing' P extendFactory h_loop_rest hd_rest_fail
        have h_inner_le_n : h_loop_stmt.len ≤ n := by
          simp only [ReflTransT.len] at hl_succ; omega
        obtain ⟨d, h_run_recurse, hd_fail⟩ :=
          ih ρ_src_next ρ_tgt_next d_loop h_eval_eq_next h_fail_eq_next h_agree_next
            hwf_next
            h_src_fresh_next h_tgt_fresh_next h_tgt_init_undef_next h_loop_stmt hd_loop_fail h_inner_le_n
        have h_run_recurse_stmts : StepStmtStar P (EvalCmd P) extendFactory
            (.stmts [.loop (.det e) m inv body' md] ρ_tgt_next)
            (.seq d ([] : List (Stmt P (Cmd P)))) :=
          .step _ _ _ StepStmt.step_stmts_cons
            (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_run_recurse)
        refine ⟨.seq d ([] : List (Stmt P (Cmd P))),
          ReflTrans_Transitive _ _ _ _ h_step_after_iter h_run_recurse_stmts, ?_⟩
        simpa [Config.getEnv] using hd_fail

/-- Failing-config nondeterministic-loop iteration.  The re-havoc next-iteration
agreement composes `StoreAgreement.of_projectStore_parents` with
`storeAgreement_storeWith` for the freshly-havoced gen guard slot. -/
private theorem nondetElim_loop_nondet_to_fail_iteration_sa {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (extendFactory : ExtendFactory P)
    (g : String) (m : Option P.Expr) {inv : List (String × P.Expr)}
    (body body' : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ σ_out : StringGenState)
    (h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
      ρb_tgt.factory = ρb_src.factory →
      ρb_tgt.hasFailure = ρb_src.hasFailure →
      StoreAgreement ρb_src.store ρb_tgt.store →
      WellFormedSemanticEval ρb_src.factory →
      StringGenState.WF σ →
      (∀ t, Q t →
        ρb_src.store (HasIdent.ident (P := P) t) = none) →
      GenFreshStore Q σ ρb_tgt.store →
      (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
      StepStmtStar P (EvalCmd P) extendFactory (.stmts body ρb_src) (Env.outcomeConfig oc_b ρb') →
      (∀ t, Q t →
          ρb'.store (HasIdent.ident (P := P) t) = none)
        ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P) extendFactory
            (.stmts body' ρb_tgt) (Env.outcomeConfig oc_b ρb_out)
          ∧ StoreAgreement ρb'.store ρb_out.store
          ∧ ρb_out.hasFailure = ρb'.hasFailure
          ∧ ρb_out.factory = ρb'.factory
          ∧ GenFreshStore Q σ_out ρb_out.store)
    (h_body_sim_fail : ∀ (ρb_src ρb_tgt : Env P) (d : Config P (Cmd P)),
      ρb_tgt.factory = ρb_src.factory →
      ρb_tgt.hasFailure = ρb_src.hasFailure →
      StoreAgreement ρb_src.store ρb_tgt.store →
      WellFormedSemanticEval ρb_src.factory →
      StringGenState.WF σ →
      (∀ t, Q t →
        ρb_src.store (HasIdent.ident (P := P) t) = none) →
      GenFreshStore Q σ ρb_tgt.store →
      (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
      StepStmtStar P (EvalCmd P) extendFactory (.stmts body ρb_src) d →
      d.getEnv.hasFailure = true →
      ∃ d', StepStmtStar P (EvalCmd P) extendFactory (.stmts body' ρb_tgt) d'
        ∧ d'.getEnv.hasFailure = true)
    (h_g_gen : Q g)
    (h_nofd_body : Block.noFuncDecl body = true)
    (ρ_src ρ_tgt : Env P) (a' : Config P (Cmd P)) (n : Nat)
    (h_eval_eq : ρ_tgt.factory = ρ_src.factory)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : GenFreshStore Q σ ρ_tgt.store)
    (h_tgt_init_undef : ∀ y ∈ Block.initVars body, ρ_tgt.store y = none)
    (entering : Bool)
    (h_guard_def : ρ_tgt.store (HasIdent.ident (P := P) g)
      = some (if entering then HasBool.tt else HasBool.ff))
    (h_a'_fail : a'.getEnv.hasFailure = true)
    (h_src_first :
      (entering = false ∧ ∃ (hrest : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
          (.terminal ρ_src) a'),
        hrest.len ≤ n) ∨
      (entering = true ∧ ∃ (hrest : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
          (.seq (.block .none ρ_src.store ρ_src.factory (.stmts body ρ_src))
            [.loop .nondet m inv body md]) a'),
        hrest.len ≤ n)) :
    ∃ d, StepStmtStar P (EvalCmd P) extendFactory
        (.stmt (.loop (.det (HasFvar.mkFvar (HasIdent.ident (P := P) g))) m
          inv
          (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md) ρ_tgt) d
      ∧ d.getEnv.hasFailure = true := by
  induction n generalizing ρ_src ρ_tgt a' entering with
  | zero =>
    rcases h_src_first with ⟨h_ent, hrest, hl⟩ | ⟨h_ent, hrest, hl⟩
    · have ha'_eq : a' = .terminal ρ_src :=
        reflTransT_from_terminal P extendFactory hrest
      rw [ha'_eq] at h_a'_fail
      have : ρ_src.hasFailure = true := by simpa [Config.getEnv, Bool.or_false] using h_a'_fail
      exact ⟨.stmt (.loop (.det (HasFvar.mkFvar (HasIdent.ident (P := P) g))) m
        inv
        (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md) ρ_tgt, .refl _,
        by simpa [Config.getEnv] using (h_fail_eq.trans this)⟩
    · subst h_ent
      have ha'_eq : a' = .seq (.block .none ρ_src.store ρ_src.factory (.stmts body ρ_src))
          [.loop .nondet m inv body md] := by
        match hrest, hl with
        | .refl _, _ => rfl
        | .step _ _ _ _ _, hl => simp only [ReflTransT.len] at hl; omega
      rw [ha'_eq] at h_a'_fail
      have : ρ_src.hasFailure = true := by
        simpa [Config.getEnv, Bool.or_false] using h_a'_fail
      exact ⟨.stmt (.loop (.det (HasFvar.mkFvar (HasIdent.ident (P := P) g))) m
        inv
        (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md) ρ_tgt, .refl _,
        by simpa [Config.getEnv] using (h_fail_eq.trans this)⟩
  | succ n ih =>
    rcases h_src_first with ⟨h_ent, hrest, hl⟩ | ⟨h_ent, hrest, hl⟩
    · have ha'_eq : a' = .terminal ρ_src :=
        reflTransT_from_terminal P extendFactory hrest
      rw [ha'_eq] at h_a'_fail
      have : ρ_src.hasFailure = true := by simpa [Config.getEnv, Bool.or_false] using h_a'_fail
      exact ⟨.stmt (.loop (.det (HasFvar.mkFvar (HasIdent.ident (P := P) g))) m
        inv
        (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md) ρ_tgt, .refl _,
        by simpa [Config.getEnv] using (h_fail_eq.trans this)⟩
    · subst h_ent
      simp only [if_true] at h_guard_def
      have h_guard_tt : P.eval ρ_tgt.factory ρ_tgt.store (HasFvar.mkFvar (HasIdent.ident (P := P) g))
          = some HasBool.tt := by
        rw [h_eval_eq]
        exact eval_mkFvar_of_value ρ_src.factory ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt
          (HasBool.boolIsVal ρ_src.factory).1 h_guard_def hwf.var hwf.mono
      have h_step_enter : StepStmtStar P (EvalCmd P) extendFactory
          (.stmt (.loop (.det (HasFvar.mkFvar (HasIdent.ident (P := P) g))) m
            inv
            (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md) ρ_tgt)
          (.seq (.block .none ρ_tgt.store ρ_tgt.factory (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
            ρ_tgt))
            [.loop (.det (HasFvar.mkFvar (HasIdent.ident (P := P) g))) m inv
              (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md]) :=
        .step _ _ _ (StepStmt.step_loop_enter
          h_guard_tt (h_eval_eq ▸ hwf.bool)) (.refl _)
      have h_g_some_tgt : (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome = true := by
        rw [h_guard_def]; rfl
      rcases seqT_reaches_failing' P extendFactory hrest h_a'_fail with hA | hB
      · -- CASE A: failure inside THIS iteration's body block (before the havoc).
        obtain ⟨d_blk, h_blk_run, hd_blk_fail, _⟩ := hA
        have ⟨d_body, h_body_run, hd_body_fail, _⟩ :=
          blockT_none_reaches_failing' P extendFactory h_blk_run hd_blk_fail
        have ⟨d', h_body_tgt, hd'_fail⟩ :=
          h_body_sim_fail ρ_src ρ_tgt d_body h_eval_eq h_fail_eq h_agree hwf
            h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef
            (reflTransT_to_prop h_body_run) hd_body_fail
        obtain ⟨d'', h_body_tail_fail, hd''_fail⟩ :=
          stmts_prefix_failing_append P extendFactory
            body' [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)] ρ_tgt d' h_body_tgt hd'_fail
        have h_blk_tgt : StepStmtStar P (EvalCmd P) extendFactory
            (.block .none ρ_tgt.store ρ_tgt.factory (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
              ρ_tgt))
            (.block .none ρ_tgt.store ρ_tgt.factory d'') :=
          block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_tgt.store ρ_tgt.factory h_body_tail_fail
        refine ⟨.seq (.block .none ρ_tgt.store ρ_tgt.factory d'')
          [.loop (.det (HasFvar.mkFvar (HasIdent.ident (P := P) g))) m inv
            (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md],
          ReflTrans_Transitive _ _ _ _ h_step_enter
            (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_blk_tgt), ?_⟩
        simpa [Config.getEnv] using hd''_fail
      · -- CASE B: this iteration's body terminated; recurse on the next iteration.
        obtain ⟨ρ_blk_inner, d_rest, h_blk_term, h_loop_rest, hd_rest_fail, hlen_rest⟩ := hB
        have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
          blockT_none_reaches_terminal (extendFactory := extendFactory) h_blk_term
        subst heq_ρ_block
        have h_body_run : StepStmtStar P (EvalCmd P) extendFactory
            (.stmts body ρ_src) (Env.outcomeConfig none ρ_inner) := reflTransT_to_prop h_inner_term
        obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner,
            h_eval_inner, h_fresh_inner⟩ :=
          h_body_sim none ρ_src ρ_inner ρ_tgt h_eval_eq h_fail_eq h_agree hwf
            h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef h_body_run
        have h_eval_inner_src : ρ_inner.factory = ρ_src.factory :=
          block_noFuncDecl_preserves_factory P (EvalCmd P) extendFactory body ρ_src ρ_inner h_nofd_body
            (by simpa only [Env.outcomeConfig] using h_body_run)
        have h_body_tgt_term : StepStmtStar P (EvalCmd P) extendFactory
            (.stmts body' ρ_tgt)
            (.terminal ρ_inner_tgt) := by
          simpa only [Env.outcomeConfig] using h_body_tgt
        have h_g_some_inner : (ρ_inner_tgt.store (HasIdent.ident (P := P) g)).isSome = true :=
          stmts_preserves_isSome (extendFactory := extendFactory) h_body_tgt_term
            (by simpa using h_g_some_tgt)
        obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp h_g_some_inner
        have hwf_var_inner : WellFormedSemanticEvalVar ρ_inner_tgt.factory := by
          rw [h_eval_inner, h_eval_inner_src]; exact hwf.var
        let ρ_src_next : Env P :=
          { store := projectStore ρ_src.store ρ_inner.store, factory := ρ_src.factory,
            hasFailure := ρ_inner.hasFailure }
        have ⟨d_loop, h_loop_stmt, hd_loop_fail, hlen_loop⟩ :=
          stmts_singleton_reaches_failing' P extendFactory h_loop_rest hd_rest_fail
        have step_assemble : ∀ (next_ent : Bool),
            (entering_next_src_first : (next_ent = false ∧ ∃ (hr : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
                  (.terminal ρ_src_next) d_loop),
                hr.len ≤ n) ∨
              (next_ent = true ∧ ∃ (hr : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
                  (.seq (.block .none ρ_src_next.store ρ_src_next.factory (.stmts body ρ_src_next))
                    [.loop .nondet m inv body md]) d_loop),
                hr.len ≤ n)) →
            ∃ d, StepStmtStar P (EvalCmd P) extendFactory
                (.stmt (.loop (.det (HasFvar.mkFvar (HasIdent.ident (P := P) g))) m
                  inv
                  (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md) ρ_tgt) d
              ∧ d.getEnv.hasFailure = true := by
          intro next_ent hsfirst_next
          let bval : P.Expr := if next_ent then HasBool.tt else HasBool.ff
          have hval_b : HasVal.value ρ_inner_tgt.factory bval := by
            simp only [bval]; split
            · exact (HasBool.boolIsVal ρ_inner_tgt.factory).1
            · exact (HasBool.boolIsVal ρ_inner_tgt.factory).2
          have h_tail : StepStmtStar P (EvalCmd P) extendFactory
              (.stmt (.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)) ρ_inner_tgt)
              (.terminal ({ ρ_inner_tgt with store := SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) bval } : Env P)) :=
            step_havoc_set_to (extendFactory := extendFactory) (HasIdent.ident (P := P) g) bval md ρ_inner_tgt v' hv'
              hval_b hwf_var_inner
          have h_body_tail : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt)
              (.terminal ({ ρ_inner_tgt with store := SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) bval } : Env P)) :=
            ReflTrans_Transitive _ _ _ _
              (stmts_prefix_terminal_append P (EvalCmd P) extendFactory _ _ _ ρ_inner_tgt h_body_tgt_term)
              (stmt_to_singleton_stmts (extendFactory := extendFactory) _ ρ_inner_tgt _ h_tail)
          let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store (SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) bval), factory := ρ_tgt.factory }
          have h_guard_next : ρ_tgt_next.store (HasIdent.ident (P := P) g)
              = some (if next_ent then HasBool.tt else HasBool.ff) := by
            show (if (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome
                then SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) bval
                  (HasIdent.ident (P := P) g) else none) = some (if next_ent then HasBool.tt else HasBool.ff)
            rw [if_pos h_g_some_tgt]; simp [SemanticStore.update, bval]
          have h_eval_next : ρ_src_next.factory = ρ_src.factory := rfl
          have hwf_next : WellFormedSemanticEval ρ_src_next.factory := by rw [h_eval_next]; exact hwf
          have h_eval_eq_next : ρ_tgt_next.factory = ρ_src_next.factory := by
            show ρ_tgt.factory = ρ_src.factory; exact h_eval_eq
          have h_fail_eq_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
            show ρ_inner_tgt.hasFailure = ρ_inner.hasFailure; exact h_fail_inner
          have h_agree_next : StoreAgreement ρ_src_next.store ρ_tgt_next.store :=
            StoreAgreement.of_projectStore_parents h_agree
              (storeAgreement_storeWith _ _ _ _ h_off_inner (h_inner_fresh g h_g_gen))
          have h_src_fresh_next : ∀ t, Q t →
              ρ_src_next.store (HasIdent.ident (P := P) t) = none := by
            intro t h_suf
            show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
                then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
            by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
            · rw [if_pos hp]; exact h_inner_fresh t h_suf
            · rw [if_neg hp]
          have h_tgt_fresh_next : GenFreshStore Q σ ρ_tgt_next.store := by
            intro s h_suf h_notin
            show (if (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
                then SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) bval
                  (HasIdent.ident (P := P) s) else none) = none
            rw [h_tgt_fresh s h_suf h_notin]; rfl
          have h_tgt_init_undef_next : ∀ y ∈ Block.initVars body, ρ_tgt_next.store y = none := by
            intro y hy
            show projectStore ρ_tgt.store
                (SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) bval) y = none
            show (if (ρ_tgt.store y).isSome
                then SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) bval y
                else none) = none
            rw [h_tgt_init_undef y hy]; rfl
          obtain ⟨d, h_run_recurse, hd_fail⟩ :=
            ih ρ_src_next ρ_tgt_next d_loop h_eval_eq_next h_fail_eq_next h_agree_next
              hwf_next
              h_src_fresh_next h_tgt_fresh_next h_tgt_init_undef_next next_ent h_guard_next hd_loop_fail hsfirst_next
          have h_block_run : StepStmtStar P (EvalCmd P) extendFactory
              (.block .none ρ_tgt.store ρ_tgt.factory (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt))
              (.terminal ρ_tgt_next) := by
            refine ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_tgt.store ρ_tgt.factory h_body_tail) ?_
            exact .step _ _ _ StepStmt.step_block_done (.refl _)
          have h_run_recurse_stmts : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts [.loop (.det (HasFvar.mkFvar (HasIdent.ident (P := P) g))) m
                inv
                (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md] ρ_tgt_next)
              (.seq d ([] : List (Stmt P (Cmd P)))) :=
            .step _ _ _ StepStmt.step_stmts_cons
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_run_recurse)
          refine ⟨.seq d ([] : List (Stmt P (Cmd P))),
            ReflTrans_Transitive _ _ _ _ h_step_enter
              (ReflTrans_Transitive _ _ _ _
                (ReflTrans_Transitive _ _ _ _
                  (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_block_run)
                  (.step _ _ _ StepStmt.step_seq_done (.refl _)))
                h_run_recurse_stmts), ?_⟩
          simpa [Config.getEnv] using hd_fail
        rcases loop_nondet_step_first_inv_fail (extendFactory := extendFactory)
            h_loop_stmt hd_loop_fail with
          h_refl | ⟨hrest_next, hlen_next⟩ | ⟨hrest_next, hlen_next⟩
        · have h_inner_fail : ρ_inner.hasFailure = true := by
            simpa [ρ_src_next, Config.getEnv] using h_refl
          have h_inner_tgt_fail : ρ_inner_tgt.hasFailure = true := by
            rw [h_fail_inner]; exact h_inner_fail
          obtain ⟨d'', h_body_tail_fail, hd''_fail⟩ :=
            stmts_prefix_failing_append P extendFactory
              body' [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]
              ρ_tgt
              (.terminal ρ_inner_tgt) h_body_tgt_term
              (by simpa [Config.getEnv] using h_inner_tgt_fail)
          have h_blk_tgt : StepStmtStar P (EvalCmd P) extendFactory
              (.block .none ρ_tgt.store ρ_tgt.factory (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt))
              (.block .none ρ_tgt.store ρ_tgt.factory d'') :=
            block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_tgt.store ρ_tgt.factory h_body_tail_fail
          refine ⟨.seq (.block .none ρ_tgt.store ρ_tgt.factory d'')
            [.loop (.det (HasFvar.mkFvar (HasIdent.ident (P := P) g))) m inv
              (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md],
            ReflTrans_Transitive _ _ _ _ h_step_enter
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_blk_tgt), ?_⟩
          simpa [Config.getEnv] using hd''_fail
        · exact step_assemble false (.inl ⟨rfl, hrest_next, by omega⟩)
        · exact step_assemble true (.inr ⟨rfl, hrest_next, by omega⟩)
mutual
/-- Per-statement failing-config engine.  `.cmd` arm replays via
`cmd_replay_agreement_storeAgree`; loop arms supply the `_sa` terminal body
simulation and the `_sa` failing-iteration engine. -/
private theorem nondetElim_stmt_to_fail_gen_sa {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen ndelimItePrefix sg).1)
            ∧ (∀ sg, Q (StringGenState.gen ndelimLoopPrefix sg).1))
    (extendFactory : ExtendFactory P)
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (ρ_src ρ_tgt : Env P) (c : Config P (Cmd P))
    (h_eval_eq : ρ_tgt.factory = ρ_src.factory)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : GenFreshStore Q σ ρ_tgt.store)
    (h_tgt_init_undef : ∀ y ∈ Stmt.initVars s, ρ_tgt.store y = none)
    (h_unique : (Stmt.initVars s).Nodup)
    (h_no_writes : (∀ t : String, Q t → HasIdent.ident (P := P) t ∉ (Stmt.definedVars s false ++ Stmt.modifiedVars s)))
    (h_nofd : Stmt.noFuncDecl s = true)
    (h_reach : StepStmtStar P (EvalCmd P) extendFactory (.stmt s ρ_src) c)
    (h_c_fail : c.getEnv.hasFailure = true) :
    ∃ d, StepStmtStar P (EvalCmd P) extendFactory
        (.stmts (Stmt.nondetElimM s σ).1 ρ_tgt) d
      ∧ d.getEnv.hasFailure = true := by
  by_cases h_ρsrc_fail : ρ_src.hasFailure = true
  · exact ⟨.stmts (Stmt.nondetElimM s σ).1 ρ_tgt, .refl _,
      by simpa [Config.getEnv] using (h_fail_eq.trans h_ρsrc_fail)⟩
  have h_ρsrc_nofail : ρ_src.hasFailure = false := by simpa using h_ρsrc_fail
  match s, h_no_writes, h_nofd, h_tgt_init_undef, h_unique, h_reach with
  | .cmd c0, h_no_writes, _, h_tgt_init_undef, _, h_reach =>
    have h_no_writes_c : (∀ s : String, Q s → HasIdent.ident (P := P) s ∉ (Cmd.definedVars c0 ++ Cmd.modifiedVars c0)) := by
      have h_dv : Stmt.definedVars (P := P) (.cmd c0) false = Cmd.definedVars c0 := by with_unfolding_all rfl
      have h_mv : Stmt.modifiedVars (P := P) (.cmd c0) = Cmd.modifiedVars c0 := by with_unfolding_all rfl
      rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
    -- `Cmd.definedVars c0 = Stmt.initVars (.cmd c0)`: the cmd replay's init-undef arg.
    have h_tgt_init_undef_c : ∀ x ∈ Cmd.definedVars c0, ρ_tgt.store x = none := by
      have h_dv : Cmd.definedVars c0 = Stmt.initVars (P := P) (.cmd c0) := by
        with_unfolding_all rfl
      rw [h_dv]; exact h_tgt_init_undef
    obtain ⟨cfg0, hstep, hrest⟩ := clean_stmt_first_step (extendFactory := extendFactory) h_reach h_c_fail h_ρsrc_nofail
    cases hstep with
    | step_cmd hcmd =>
      rename_i σ' hasAssertFailure
      have h_c_eq := reflTransT_from_terminal P extendFactory (reflTrans_to_T hrest)
      have h_mid_fail :
          ({ ρ_src with store := σ', hasFailure := ρ_src.hasFailure || hasAssertFailure } : Env P).hasFailure
          = true := by rw [h_c_eq] at h_c_fail; simpa [Config.getEnv] using h_c_fail
      have h_term_src : StepStmtStar P (EvalCmd P) extendFactory (.stmt (.cmd c0) ρ_src)
          (.terminal ({ ρ_src with store := σ', hasFailure := ρ_src.hasFailure || hasAssertFailure } : Env P)) :=
        .step _ _ _ (StepStmt.step_cmd hcmd) (.refl _)
      obtain ⟨ρ_tgt', h_run, _, h_fail', _⟩ :=
        cmd_replay_agreement_storeAgree extendFactory c0 ρ_src
          ({ ρ_src with store := σ', hasFailure := ρ_src.hasFailure || hasAssertFailure } : Env P) ρ_tgt
          h_eval_eq h_fail_eq h_agree hwf.mono h_tgt_init_undef_c h_term_src
      refine ⟨.terminal ρ_tgt', ?_, by simpa [Config.getEnv, h_fail'] using h_mid_fail⟩
      simp only [Stmt.nondetElimM]
      exact stmt_to_singleton_stmts (extendFactory := extendFactory) (.cmd c0) ρ_tgt ρ_tgt' h_run
  | .block lbl bss md, h_no_writes, h_nofd, h_tgt_init_undef, h_unique, h_reach =>
    have h_dv : Stmt.definedVars (P := P) (.block lbl bss md) false = Block.definedVars bss false := by
      rw [Stmt.definedVars]; rfl
    have h_mv : Stmt.modifiedVars (P := P) (.block lbl bss md) = Block.modifiedVars bss := by
      with_unfolding_all rfl
    have h_no_writes_bss : SrcNoGenWrites (P := P) Q bss := by
      show (∀ s : String, Q s → HasIdent.ident (P := P) s ∉ (Block.definedVars bss false ++ Block.modifiedVars bss))
      rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
    have h_nofd_bss : Block.noFuncDecl bss = true := by simpa only [Stmt.noFuncDecl] using h_nofd
    have h_tgt_iu_bss : ∀ y ∈ Block.initVars bss, ρ_tgt.store y = none := by
      intro y hy; exact h_tgt_init_undef y (by rw [Stmt.initVars_block]; exact hy)
    have h_unique_bss : (Block.initVars bss).Nodup := by
      rw [Stmt.initVars_block] at h_unique; exact h_unique
    obtain ⟨cfg0, hstep, hrest⟩ := clean_stmt_first_step (extendFactory := extendFactory) h_reach h_c_fail h_ρsrc_nofail
    cases hstep with
    | step_block =>
      have ⟨d_body, h_body_run, hd_body_fail⟩ :=
        block_reaches_failing' P extendFactory hrest h_c_fail
      obtain ⟨d_tgt, h_run_tgt, hd_tgt_fail⟩ :=
        nondetElim_to_fail_gen_sa hQgen extendFactory bss σ ρ_src ρ_tgt d_body
          h_eval_eq h_fail_eq h_agree hwf
          h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_bss h_unique_bss h_no_writes_bss h_nofd_bss
          h_body_run hd_body_fail
      rw [Stmt.nondetElimM_block_out]
      have h_block_stmt : StepStmtStar P (EvalCmd P) extendFactory
          (.stmt (.block lbl (Block.nondetElimM bss σ).1 md) ρ_tgt)
          (.block (some lbl) ρ_tgt.store ρ_tgt.factory d_tgt) :=
        .step _ _ _ StepStmt.step_block
          (block_inner_star P (EvalCmd P) extendFactory _ _ (some lbl) ρ_tgt.store ρ_tgt.factory h_run_tgt)
      exact stmt_to_singleton_stmts_fail (extendFactory := extendFactory)
        (.block lbl (Block.nondetElimM bss σ).1 md) ρ_tgt
        (.block (some lbl) ρ_tgt.store ρ_tgt.factory d_tgt) h_block_stmt
        (by simpa [Config.getEnv] using hd_tgt_fail)
  | .ite (.det e) tss ess md, h_no_writes, h_nofd, h_tgt_init_undef, h_unique, h_reach =>
    have h_dv : Stmt.definedVars (P := P) (.ite (.det e) tss ess md) false
        = Block.definedVars tss false ++ Block.definedVars ess false := by
      rw [Stmt.definedVars]; rfl
    have h_mv : Stmt.modifiedVars (P := P) (.ite (.det e) tss ess md)
        = Block.modifiedVars tss ++ Block.modifiedVars ess := rfl
    have h_nofd' : Block.noFuncDecl tss = true ∧ Block.noFuncDecl ess = true := by
      have : (Block.noFuncDecl tss && Block.noFuncDecl ess) = true := by
        simpa only [Stmt.noFuncDecl] using h_nofd
      exact Bool.and_eq_true _ _ |>.mp this
    have h_unique_pair : (Block.initVars tss ++ Block.initVars ess).Nodup := by
      rw [Stmt.initVars_ite] at h_unique; exact h_unique
    have h_unique_t : (Block.initVars tss).Nodup := (List.nodup_append.mp h_unique_pair).1
    have h_unique_e : (Block.initVars ess).Nodup := (List.nodup_append.mp h_unique_pair).2.1
    have h_tgt_iu_t : ∀ y ∈ Block.initVars tss, ρ_tgt.store y = none := by
      intro y hy; exact h_tgt_init_undef y
        (by rw [Stmt.initVars_ite]; exact List.mem_append_left _ hy)
    have h_tgt_iu_e : ∀ y ∈ Block.initVars ess, ρ_tgt.store y = none := by
      intro y hy; exact h_tgt_init_undef y
        (by rw [Stmt.initVars_ite]; exact List.mem_append_right _ hy)
    obtain ⟨cfg0, hstep, hrest⟩ := clean_stmt_first_step (extendFactory := extendFactory) h_reach h_c_fail h_ρsrc_nofail
    cases hstep with
    | step_ite_true h_cond hwfb_s =>
      have h_no_writes_t : SrcNoGenWrites (P := P) Q tss := by
        intro t hQ hmem
        rcases List.mem_append.mp hmem with hd | hm
        · exact h_no_writes t hQ (by rw [h_dv]; exact List.mem_append_left _ (List.mem_append_left _ hd))
        · exact h_no_writes t hQ (by rw [h_mv]; exact List.mem_append_right _ (List.mem_append_left _ hm))
      obtain ⟨d_inner, h_inner_fail, hd_inner_fail, _⟩ :=
        blockT_none_reaches_failing' P extendFactory (reflTrans_to_T hrest) h_c_fail
      obtain ⟨d_tgt, h_run_tgt, hd_tgt_fail⟩ :=
        nondetElim_to_fail_gen_sa hQgen extendFactory tss σ ρ_src ρ_tgt d_inner
          h_eval_eq h_fail_eq h_agree hwf
          h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_t h_unique_t h_no_writes_t h_nofd'.1
          (reflTransT_to_prop h_inner_fail) hd_inner_fail
      have h_cond_t : P.eval ρ_tgt.factory ρ_tgt.store e = some HasBool.tt := by
        rw [h_eval_eq]
        exact hwf.mono e HasBool.tt ρ_src.store ρ_tgt.store
          (storeAgreement_supplies_mono_premise ρ_src.store ρ_tgt.store h_agree) h_cond
      rw [Stmt.nondetElimM_ite_det_out]
      refine ⟨.seq (.block .none ρ_tgt.store ρ_tgt.factory d_tgt) [], ?_,
        by simpa [Config.getEnv] using hd_tgt_fail⟩
      refine .step _ _ _ StepStmt.step_stmts_cons ?_
      exact seq_inner_star P (EvalCmd P) extendFactory _ _ []
        (.step _ _ _ (StepStmt.step_ite_true h_cond_t (h_eval_eq ▸ hwf.bool))
          (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_tgt.store ρ_tgt.factory h_run_tgt))
    | step_ite_false h_cond hwfb_s =>
      have h_no_writes_e : SrcNoGenWrites (P := P) Q ess := by
        intro t hQ hmem
        rcases List.mem_append.mp hmem with hd | hm
        · exact h_no_writes t hQ (by rw [h_dv]; exact List.mem_append_left _ (List.mem_append_right _ hd))
        · exact h_no_writes t hQ (by rw [h_mv]; exact List.mem_append_right _ (List.mem_append_right _ hm))
      have h_wf₁ : StringGenState.WF (Block.nondetElimM tss σ).2 :=
        (Block.nondetElimM_genStep tss σ).wf_mono h_wf_gen
      have h_tgt_fresh₁ : GenFreshStore Q (Block.nondetElimM tss σ).2 ρ_tgt.store :=
        GenFreshStore_mono (Block.nondetElimM_genStep tss σ) h_tgt_fresh
      obtain ⟨d_inner, h_inner_fail, hd_inner_fail, _⟩ :=
        blockT_none_reaches_failing' P extendFactory (reflTrans_to_T hrest) h_c_fail
      obtain ⟨d_tgt, h_run_tgt, hd_tgt_fail⟩ :=
        nondetElim_to_fail_gen_sa hQgen extendFactory ess (Block.nondetElimM tss σ).2 ρ_src ρ_tgt d_inner
          h_eval_eq h_fail_eq h_agree hwf
          h_wf₁ h_src_fresh h_tgt_fresh₁ h_tgt_iu_e h_unique_e h_no_writes_e h_nofd'.2
          (reflTransT_to_prop h_inner_fail) hd_inner_fail
      have h_cond_t : P.eval ρ_tgt.factory ρ_tgt.store e = some HasBool.ff := by
        rw [h_eval_eq]
        exact hwf.mono e HasBool.ff ρ_src.store ρ_tgt.store
          (storeAgreement_supplies_mono_premise ρ_src.store ρ_tgt.store h_agree) h_cond
      rw [Stmt.nondetElimM_ite_det_out]
      refine ⟨.seq (.block .none ρ_tgt.store ρ_tgt.factory d_tgt) [], ?_,
        by simpa [Config.getEnv] using hd_tgt_fail⟩
      refine .step _ _ _ StepStmt.step_stmts_cons ?_
      exact seq_inner_star P (EvalCmd P) extendFactory _ _ []
        (.step _ _ _ (StepStmt.step_ite_false h_cond_t (h_eval_eq ▸ hwf.bool))
          (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_tgt.store ρ_tgt.factory h_run_tgt))
  | .ite .nondet tss ess md, h_no_writes, h_nofd, h_tgt_init_undef, h_unique, h_reach =>
    rcases hgen : StringGenState.gen ndelimItePrefix σ with ⟨g, σ₁⟩
    have h_g_gen : Q g := by have := hQgen.1 σ; rw [hgen] at this; exact this
    have h_tgt_g_none : ρ_tgt.store (HasIdent.ident (P := P) g) = none := by
      have := GenFreshStore_gen_slot_none ndelimItePrefix h_tgt_fresh h_wf_gen (hQgen.1 σ)
      rw [hgen] at this; exact this
    have hwf_var_t : WellFormedSemanticEvalVar ρ_tgt.factory := h_eval_eq ▸ hwf.var
    have hwfb_t : WellFormedSemanticEvalBool ρ_tgt.factory := h_eval_eq ▸ hwf.bool
    have hwf_def_t : WellFormedSemanticEvalMono ρ_tgt.factory := h_eval_eq ▸ hwf.mono
    have h_step01 : StringGenState.GenStep σ σ₁ := by
      have := StringGenState.GenStep.of_gen ndelimItePrefix σ; rw [hgen] at this; exact this
    have h_wf₁ : StringGenState.WF σ₁ := h_step01.wf_mono h_wf_gen
    have h_dv : Stmt.definedVars (P := P) (.ite .nondet tss ess md) false
        = Block.definedVars tss false ++ Block.definedVars ess false := by
      rw [Stmt.definedVars]; rfl
    have h_mv : Stmt.modifiedVars (P := P) (.ite .nondet tss ess md)
        = Block.modifiedVars tss ++ Block.modifiedVars ess := rfl
    have h_nofd' : Block.noFuncDecl tss = true ∧ Block.noFuncDecl ess = true := by
      have : (Block.noFuncDecl tss && Block.noFuncDecl ess) = true := by
        simpa only [Stmt.noFuncDecl] using h_nofd
      exact Bool.and_eq_true _ _ |>.mp this
    have h_no_writes_t : SrcNoGenWrites (P := P) Q tss := by
      intro t hQ hmem
      rcases List.mem_append.mp hmem with hd | hm
      · exact h_no_writes t hQ (by rw [h_dv]; exact List.mem_append_left _ (List.mem_append_left _ hd))
      · exact h_no_writes t hQ (by rw [h_mv]; exact List.mem_append_right _ (List.mem_append_left _ hm))
    have h_no_writes_e : SrcNoGenWrites (P := P) Q ess := by
      intro t hQ hmem
      rcases List.mem_append.mp hmem with hd | hm
      · exact h_no_writes t hQ (by rw [h_dv]; exact List.mem_append_left _ (List.mem_append_right _ hd))
      · exact h_no_writes t hQ (by rw [h_mv]; exact List.mem_append_right _ (List.mem_append_right _ hm))
    have h_unique_pair : (Block.initVars tss ++ Block.initVars ess).Nodup := by
      rw [Stmt.initVars_ite] at h_unique; exact h_unique
    have h_unique_t : (Block.initVars tss).Nodup := (List.nodup_append.mp h_unique_pair).1
    have h_unique_e : (Block.initVars ess).Nodup := (List.nodup_append.mp h_unique_pair).2.1
    -- Branch init-targets are source-shaped, hence distinct from the gen guard `g`;
    -- the guard SemanticStore.update leaves each branch init-target's slot untouched.
    have h_tgt_iu_t : ∀ (v : P.Expr) (y : P.Ident), y ∈ Block.initVars tss →
        (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) v) y = none := by
      intro v y hy
      have h_y_dv : y ∈ Stmt.definedVars (P := P) (.ite .nondet tss ess md) false := by
        rw [h_dv]; exact List.mem_append_left _ (hy)
      have h_y_ne : y ≠ HasIdent.ident (P := P) g := fun h_eq =>
        h_no_writes g h_g_gen (h_eq ▸ List.mem_append_left _ h_y_dv)
      have h_y_none : ρ_tgt.store y = none := h_tgt_init_undef y
        (by rw [Stmt.initVars_ite]; exact List.mem_append_left _ hy)
      simp only [SemanticStore.update, h_y_ne]; exact h_y_none
    have h_tgt_iu_e : ∀ (v : P.Expr) (y : P.Ident), y ∈ Block.initVars ess →
        (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) v) y = none := by
      intro v y hy
      have h_y_dv : y ∈ Stmt.definedVars (P := P) (.ite .nondet tss ess md) false := by
        rw [h_dv]; exact List.mem_append_right _ (hy)
      have h_y_ne : y ≠ HasIdent.ident (P := P) g := fun h_eq =>
        h_no_writes g h_g_gen (h_eq ▸ List.mem_append_left _ h_y_dv)
      have h_y_none : ρ_tgt.store y = none := h_tgt_init_undef y
        (by rw [Stmt.initVars_ite]; exact List.mem_append_right _ hy)
      simp only [SemanticStore.update, h_y_ne]; exact h_y_none
    obtain ⟨cfg0, hstep, hrest⟩ := clean_stmt_first_step (extendFactory := extendFactory) h_reach h_c_fail h_ρsrc_nofail
    cases hstep with
    | step_ite_nondet_true =>
      have h_off_g : StoreAgreement ρ_src.store
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) :=
        storeAgreement_storeWith _ _ _ _ h_agree (h_src_fresh g h_g_gen)
      have h_fresh_g : GenFreshStore Q σ₁
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) := by
        have := GenFreshStore_storeWith_gen (P := P) ndelimItePrefix HasBool.tt h_tgt_fresh
        rw [hgen] at this; exact this
      obtain ⟨d_inner, h_inner_fail, hd_inner_fail, _⟩ :=
        blockT_none_reaches_failing' P extendFactory (reflTrans_to_T hrest) h_c_fail
      obtain ⟨d_tgt, h_run_tgt, hd_tgt_fail⟩ :=
        nondetElim_to_fail_gen_sa hQgen extendFactory tss σ₁
          ρ_src ({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P) d_inner
          h_eval_eq h_fail_eq h_off_g hwf
          h_wf₁ h_src_fresh h_fresh_g (h_tgt_iu_t HasBool.tt) h_unique_t h_no_writes_t h_nofd'.1
          (reflTransT_to_prop h_inner_fail) hd_inner_fail
      rw [Stmt.nondetElimM_ite_nondet_out]; simp only [hgen]
      exact step_ndelim_ite_prefix_fail (extendFactory := extendFactory) true (HasIdent.ident (P := P) g)
        (Block.nondetElimM tss σ₁).1 (Block.nondetElimM ess (Block.nondetElimM tss σ₁).2).1 md
        ρ_tgt d_tgt h_tgt_g_none hwf_var_t (h_eval_eq ▸ hwf.mono) hwfb_t h_run_tgt hd_tgt_fail
    | step_ite_nondet_false =>
      have h_step12 : StringGenState.GenStep σ₁ (Block.nondetElimM tss σ₁).2 :=
        Block.nondetElimM_genStep tss σ₁
      have h_wf₂ : StringGenState.WF (Block.nondetElimM tss σ₁).2 := h_step12.wf_mono h_wf₁
      have h_off_g : StoreAgreement ρ_src.store
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) :=
        storeAgreement_storeWith _ _ _ _ h_agree (h_src_fresh g h_g_gen)
      have h_fresh_g1 : GenFreshStore Q σ₁
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) := by
        have := GenFreshStore_storeWith_gen (P := P) ndelimItePrefix HasBool.ff h_tgt_fresh
        rw [hgen] at this; exact this
      have h_fresh_g : GenFreshStore Q (Block.nondetElimM tss σ₁).2
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) :=
        GenFreshStore_mono h_step12 h_fresh_g1
      obtain ⟨d_inner, h_inner_fail, hd_inner_fail, _⟩ :=
        blockT_none_reaches_failing' P extendFactory (reflTrans_to_T hrest) h_c_fail
      obtain ⟨d_tgt, h_run_tgt, hd_tgt_fail⟩ :=
        nondetElim_to_fail_gen_sa hQgen extendFactory ess (Block.nondetElimM tss σ₁).2
          ρ_src ({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff } : Env P) d_inner
          h_eval_eq h_fail_eq h_off_g hwf
          h_wf₂ h_src_fresh h_fresh_g (h_tgt_iu_e HasBool.ff) h_unique_e h_no_writes_e h_nofd'.2
          (reflTransT_to_prop h_inner_fail) hd_inner_fail
      rw [Stmt.nondetElimM_ite_nondet_out]; simp only [hgen]
      exact step_ndelim_ite_prefix_fail (extendFactory := extendFactory) false (HasIdent.ident (P := P) g)
        (Block.nondetElimM tss σ₁).1 (Block.nondetElimM ess (Block.nondetElimM tss σ₁).2).1 md
        ρ_tgt d_tgt h_tgt_g_none hwf_var_t (h_eval_eq ▸ hwf.mono) hwfb_t h_run_tgt hd_tgt_fail
  | .loop (.det e) m inv body md, h_no_writes, h_nofd, h_tgt_init_undef, h_unique, h_reach =>
    have h_nofd_body : Block.noFuncDecl body = true := by simpa only [Stmt.noFuncDecl] using h_nofd
    have h_no_writes_body : SrcNoGenWrites (P := P) Q body := by
      have h_dv : Stmt.definedVars (P := P) (.loop (.det e) m inv body md) false
          = Block.definedVars body false := by
        simp only [Stmt.definedVars, Bool.false_eq_true, if_false]
      have h_mv : Stmt.modifiedVars (P := P) (.loop (.det e) m inv body md)
          = Block.modifiedVars body := rfl
      show (∀ s : String, Q s → HasIdent.ident (P := P) s ∉ (Block.definedVars body false ++ Block.modifiedVars body))
      rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
    have h_tgt_iu_body : ∀ y ∈ Block.initVars body, ρ_tgt.store y = none := by
      intro y hy; exact h_tgt_init_undef y (by rw [Stmt.initVars_loop]; exact hy)
    have h_unique_body : (Block.initVars body).Nodup := by
      rw [Stmt.initVars_loop] at h_unique; exact h_unique
    have h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
        ρb_tgt.factory = ρb_src.factory → ρb_tgt.hasFailure = ρb_src.hasFailure →
        StoreAgreement ρb_src.store ρb_tgt.store →
        WellFormedSemanticEval ρb_src.factory → StringGenState.WF σ →
        (∀ t, Q t → ρb_src.store (HasIdent.ident (P := P) t) = none) →
        GenFreshStore Q σ ρb_tgt.store →
        (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
        StepStmtStar P (EvalCmd P) extendFactory (.stmts body ρb_src) (Env.outcomeConfig oc_b ρb') →
        (∀ t, Q t → ρb'.store (HasIdent.ident (P := P) t) = none)
          ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P) extendFactory
              (.stmts (Block.nondetElimM body σ).1 ρb_tgt) (Env.outcomeConfig oc_b ρb_out)
            ∧ StoreAgreement ρb'.store ρb_out.store ∧ ρb_out.hasFailure = ρb'.hasFailure
            ∧ ρb_out.factory = ρb'.factory ∧ GenFreshStore Q (Block.nondetElimM body σ).2 ρb_out.store :=
      fun oc_b ρb_src ρb' ρb_tgt h_ev h_fl h_ag hwf hwfg hsf htf htiu hrun =>
        nondetElim_simulation_gen_sa hQgen extendFactory body σ ρb_src ρb' ρb_tgt
          h_ev h_fl h_ag hwf hwfg hsf htf htiu h_unique_body
          h_no_writes_body h_nofd_body oc_b hrun
    have h_body_sim_fail : ∀ (ρb_src ρb_tgt : Env P) (d : Config P (Cmd P)),
        ρb_tgt.factory = ρb_src.factory → ρb_tgt.hasFailure = ρb_src.hasFailure →
        StoreAgreement ρb_src.store ρb_tgt.store →
        WellFormedSemanticEval ρb_src.factory → StringGenState.WF σ →
        (∀ t, Q t → ρb_src.store (HasIdent.ident (P := P) t) = none) →
        GenFreshStore Q σ ρb_tgt.store →
        (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
        StepStmtStar P (EvalCmd P) extendFactory (.stmts body ρb_src) d → d.getEnv.hasFailure = true →
        ∃ d', StepStmtStar P (EvalCmd P) extendFactory (.stmts (Block.nondetElimM body σ).1 ρb_tgt) d'
          ∧ d'.getEnv.hasFailure = true :=
      fun ρb_src ρb_tgt d h_ev h_fl h_ag hwf hwfg hsf htf htiu hrun hdfail =>
        nondetElim_to_fail_gen_sa hQgen extendFactory body σ ρb_src ρb_tgt d
          h_ev h_fl h_ag hwf hwfg hsf htf htiu h_unique_body
          h_no_writes_body h_nofd_body hrun hdfail
    obtain ⟨d_tgt, h_run_tgt, hd_tgt_fail⟩ :=
      nondetElim_loop_det_to_fail_iteration_sa extendFactory e m body (Block.nondetElimM body σ).1 md σ
        (Block.nondetElimM body σ).2
        h_body_sim h_body_sim_fail h_nofd_body ρ_src ρ_tgt c (reflTrans_to_T h_reach).len
        h_eval_eq h_fail_eq h_agree hwf
        h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_body (reflTrans_to_T h_reach) h_c_fail (Nat.le_refl _)
    rw [Stmt.nondetElimM_loop_det_out]
    refine ⟨.seq d_tgt [], ?_, by simpa [Config.getEnv] using hd_tgt_fail⟩
    refine .step _ _ _ StepStmt.step_stmts_cons ?_
    exact seq_inner_star P (EvalCmd P) extendFactory _ _ [] h_run_tgt
  | .loop .nondet m inv body md, h_no_writes, h_nofd, h_tgt_init_undef, h_unique, h_reach =>
    have h_nofd_body : Block.noFuncDecl body = true := by simpa only [Stmt.noFuncDecl] using h_nofd
    have h_no_writes_body : SrcNoGenWrites (P := P) Q body := by
      have h_dv : Stmt.definedVars (P := P) (.loop .nondet m inv body md) false
          = Block.definedVars body false := by
        simp only [Stmt.definedVars, Bool.false_eq_true, if_false]
      have h_mv : Stmt.modifiedVars (P := P) (.loop .nondet m inv body md)
          = Block.modifiedVars body := rfl
      show (∀ s : String, Q s → HasIdent.ident (P := P) s ∉ (Block.definedVars body false ++ Block.modifiedVars body))
      rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
    rcases hgen : StringGenState.gen ndelimLoopPrefix σ with ⟨g, σ₁⟩
    have h_g_gen : Q g := by have := hQgen.2 σ; rw [hgen] at this; exact this
    have h_step01 : StringGenState.GenStep σ σ₁ := by
      have := StringGenState.GenStep.of_gen ndelimLoopPrefix σ; rw [hgen] at this; exact this
    have h_wf₁ : StringGenState.WF σ₁ := h_step01.wf_mono h_wf_gen
    have h_tgt_g_none : ρ_tgt.store (HasIdent.ident (P := P) g) = none := by
      have := GenFreshStore_gen_slot_none ndelimLoopPrefix h_tgt_fresh h_wf_gen (hQgen.2 σ)
      rw [hgen] at this; exact this
    have hwf_var_t : WellFormedSemanticEvalVar ρ_tgt.factory := h_eval_eq ▸ hwf.var
    have h_unique_body : (Block.initVars body).Nodup := by
      rw [Stmt.initVars_loop] at h_unique; exact h_unique
    -- Body init-targets are source-shaped, distinct from gen guard `g`; the
    -- guard SemanticStore.update leaves each body init-target's slot untouched.
    have h_tgt_iu_body : ∀ (v : P.Expr) (y : P.Ident), y ∈ Block.initVars body →
        (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) v) y = none := by
      intro v y hy
      have h_y_dv : y ∈ Stmt.definedVars (P := P) (.loop .nondet m inv body md) false := by
        rw [Stmt.definedVars]; simp only [Bool.false_eq_true, if_false]
        exact hy
      have h_y_ne : y ≠ HasIdent.ident (P := P) g := fun h_eq =>
        h_no_writes g h_g_gen (h_eq ▸ List.mem_append_left _ h_y_dv)
      have h_y_none : ρ_tgt.store y = none := h_tgt_init_undef y
        (by rw [Stmt.initVars_loop]; exact hy)
      simp only [SemanticStore.update, h_y_ne]; exact h_y_none
    have h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
        ρb_tgt.factory = ρb_src.factory → ρb_tgt.hasFailure = ρb_src.hasFailure →
        StoreAgreement ρb_src.store ρb_tgt.store →
        WellFormedSemanticEval ρb_src.factory → StringGenState.WF σ₁ →
        (∀ t, Q t → ρb_src.store (HasIdent.ident (P := P) t) = none) →
        GenFreshStore Q σ₁ ρb_tgt.store →
        (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
        StepStmtStar P (EvalCmd P) extendFactory (.stmts body ρb_src) (Env.outcomeConfig oc_b ρb') →
        (∀ t, Q t → ρb'.store (HasIdent.ident (P := P) t) = none)
          ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P) extendFactory
              (.stmts (Block.nondetElimM body σ₁).1 ρb_tgt) (Env.outcomeConfig oc_b ρb_out)
            ∧ StoreAgreement ρb'.store ρb_out.store ∧ ρb_out.hasFailure = ρb'.hasFailure
            ∧ ρb_out.factory = ρb'.factory ∧ GenFreshStore Q (Block.nondetElimM body σ₁).2 ρb_out.store :=
      fun oc_b ρb_src ρb' ρb_tgt h_ev h_fl h_ag hwf hwfg hsf htf htiu hrun =>
        nondetElim_simulation_gen_sa hQgen extendFactory body σ₁ ρb_src ρb' ρb_tgt
          h_ev h_fl h_ag hwf hwfg hsf htf htiu h_unique_body
          h_no_writes_body h_nofd_body oc_b hrun
    have h_body_sim_fail : ∀ (ρb_src ρb_tgt : Env P) (d : Config P (Cmd P)),
        ρb_tgt.factory = ρb_src.factory → ρb_tgt.hasFailure = ρb_src.hasFailure →
        StoreAgreement ρb_src.store ρb_tgt.store →
        WellFormedSemanticEval ρb_src.factory → StringGenState.WF σ₁ →
        (∀ t, Q t → ρb_src.store (HasIdent.ident (P := P) t) = none) →
        GenFreshStore Q σ₁ ρb_tgt.store →
        (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
        StepStmtStar P (EvalCmd P) extendFactory (.stmts body ρb_src) d → d.getEnv.hasFailure = true →
        ∃ d', StepStmtStar P (EvalCmd P) extendFactory (.stmts (Block.nondetElimM body σ₁).1 ρb_tgt) d'
          ∧ d'.getEnv.hasFailure = true :=
      fun ρb_src ρb_tgt d h_ev h_fl h_ag hwf hwfg hsf htf htiu hrun hdfail =>
        nondetElim_to_fail_gen_sa hQgen extendFactory body σ₁ ρb_src ρb_tgt d
          h_ev h_fl h_ag hwf hwfg hsf htf htiu h_unique_body
          h_no_writes_body h_nofd_body hrun hdfail
    have hstarT := reflTrans_to_T h_reach
    have h_finish : ∀ (entering : Bool) (b : P.Expr)
        (_h_b : b = (if entering then HasBool.tt else HasBool.ff))
        (h_first :
          (entering = false ∧ ∃ (hr : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
              (.terminal ρ_src) c),
            hr.len ≤ hstarT.len) ∨
          (entering = true ∧ ∃ (hr : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
              (.seq (.block .none ρ_src.store ρ_src.factory (.stmts body ρ_src))
                [.loop .nondet m inv body md]) c),
            hr.len ≤ hstarT.len)),
        ∃ d, StepStmtStar P (EvalCmd P) extendFactory
            (.stmts (Stmt.nondetElimM (.loop .nondet m inv body md) σ).1 ρ_tgt) d
          ∧ d.getEnv.hasFailure = true := by
      intro entering b h_b h_first
      have hval_b : HasVal.value ρ_tgt.factory b := by
        rw [h_b]; split
        · exact (HasBool.boolIsVal ρ_tgt.factory).1
        · exact (HasBool.boolIsVal ρ_tgt.factory).2
      have h_off_g : StoreAgreement ρ_src.store
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) b) :=
        storeAgreement_storeWith _ _ _ _ h_agree (h_src_fresh g h_g_gen)
      have h_fresh_g : GenFreshStore Q σ₁
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) b) := by
        have := GenFreshStore_storeWith_gen (P := P) ndelimLoopPrefix b h_tgt_fresh
        rw [hgen] at this; exact this
      have h_guard_def : (({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) b } : Env P).store)
          (HasIdent.ident (P := P) g) = some (if entering then HasBool.tt else HasBool.ff) := by
        subst h_b; simp [SemanticStore.update]
      obtain ⟨d_tgt, h_loop_run, hd_tgt_fail⟩ :=
        nondetElim_loop_nondet_to_fail_iteration_sa extendFactory g m body (Block.nondetElimM body σ₁).1 md σ₁
          (Block.nondetElimM body σ₁).2
          h_body_sim h_body_sim_fail h_g_gen h_nofd_body ρ_src
          ({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) b } : Env P)
          c hstarT.len h_eval_eq h_fail_eq h_off_g hwf
          h_wf₁ h_src_fresh h_fresh_g (h_tgt_iu_body b) entering h_guard_def h_c_fail h_first
      rw [Stmt.nondetElimM_loop_nondet_out]; simp only [hgen]
      have h_init : StepStmtStar P (EvalCmd P) extendFactory
          (.stmt (.cmd (HasInit.init (HasIdent.ident (P := P) g) HasBool.boolTy .nondet md)) ρ_tgt)
          (.terminal ({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) b } : Env P)) :=
        step_init_havoc_to (extendFactory := extendFactory) (HasIdent.ident (P := P) g) HasBool.boolTy b md ρ_tgt
          h_tgt_g_none hval_b hwf_var_t
      refine ⟨.seq d_tgt ([] : List (Stmt P (Cmd P))), ?_, by simpa [Config.getEnv] using hd_tgt_fail⟩
      refine ReflTrans_Transitive _ _ _ _
        (stmts_cons_step P (EvalCmd P) extendFactory _ _ ρ_tgt _ h_init) ?_
      exact .step _ _ _ StepStmt.step_stmts_cons (seq_inner_star P (EvalCmd P) extendFactory _ _ [] h_loop_run)
    rcases loop_nondet_step_first_inv_fail (extendFactory := extendFactory) hstarT h_c_fail with
      h_refl | ⟨hrest, hl⟩ | ⟨hrest, hl⟩
    · exact absurd h_refl h_ρsrc_fail
    · exact h_finish false HasBool.ff (by simp) (.inl ⟨rfl, hrest, Nat.le_of_lt hl⟩)
    · exact h_finish true HasBool.tt (by simp) (.inr ⟨rfl, hrest, Nat.le_of_lt hl⟩)
  | .exit lbl md, _, _, _, _, h_reach =>
    exfalso
    obtain ⟨cfg0, hstep, hrest⟩ := clean_stmt_first_step (extendFactory := extendFactory) h_reach h_c_fail h_ρsrc_nofail
    cases hstep with
    | step_exit =>
      have h_c_eq : c = .exiting lbl ρ_src :=
        reflTransT_from_exiting P extendFactory (reflTrans_to_T hrest)
      rw [h_c_eq] at h_c_fail
      exact absurd (by simpa [Config.getEnv] using h_c_fail) h_ρsrc_fail
  | .funcDecl d md, _, h_nofd, _, _, _ => exact absurd h_nofd (by simp [Stmt.noFuncDecl])
  | .typeDecl t md, _, _, _, _, h_reach =>
    exfalso
    obtain ⟨cfg0, hstep, hrest⟩ := clean_stmt_first_step (extendFactory := extendFactory) h_reach h_c_fail h_ρsrc_nofail
    cases hstep with
    | step_typeDecl =>
      have h_c_eq : c = .terminal ρ_src :=
        reflTransT_from_terminal P extendFactory (reflTrans_to_T hrest)
      rw [h_c_eq] at h_c_fail
      exact absurd (by simpa [Config.getEnv] using h_c_fail) h_ρsrc_fail
  termination_by sizeOf s

/-- Block failing-config engine.  Cons case B (head terminates, tail fails)
advances the relation through `nondetElim_stmt_gen_sa`, then re-establishes the
tail's init-target undefinedness at the advanced target via
`block_run_terminal_preserves_none_of_not_definedVars` + the `Q`-keyed output
`initVars`-classification + head/tail disjointness. -/
private theorem nondetElim_to_fail_gen_sa {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen ndelimItePrefix sg).1)
            ∧ (∀ sg, Q (StringGenState.gen ndelimLoopPrefix sg).1))
    (extendFactory : ExtendFactory P)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (ρ_src ρ_tgt : Env P) (c : Config P (Cmd P))
    (h_eval_eq : ρ_tgt.factory = ρ_src.factory)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : GenFreshStore Q σ ρ_tgt.store)
    (h_tgt_init_undef : ∀ y ∈ Block.initVars ss, ρ_tgt.store y = none)
    (h_unique : (Block.initVars ss).Nodup)
    (h_no_writes : SrcNoGenWrites (P := P) Q ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_reach : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ_src) c)
    (h_c_fail : c.getEnv.hasFailure = true) :
    ∃ d, StepStmtStar P (EvalCmd P) extendFactory
        (.stmts (Block.nondetElimM ss σ).1 ρ_tgt) d
      ∧ d.getEnv.hasFailure = true := by
  by_cases h_ρsrc_fail : ρ_src.hasFailure = true
  · exact ⟨.stmts (Block.nondetElimM ss σ).1 ρ_tgt, .refl _,
      by simpa [Config.getEnv] using (h_fail_eq.trans h_ρsrc_fail)⟩
  have h_ρsrc_nofail : ρ_src.hasFailure = false := by simpa using h_ρsrc_fail
  match ss, h_no_writes, h_nofd, h_tgt_init_undef, h_unique with
  | [], _, _, _, _ =>
    exfalso
    have h_c_env : c.getEnv = ρ_src := by
      match h_reach with
      | .refl _ => rfl
      | .step _ _ _ hstep hrest =>
        cases hstep with
        | step_stmts_nil =>
          have := reflTransT_from_terminal P extendFactory (reflTrans_to_T hrest)
          rw [this]; rfl
    rw [h_c_env] at h_c_fail
    exact absurd (by simpa [Config.getEnv] using h_c_fail) h_ρsrc_fail
  | s :: rest, h_no_writes, h_nofd, h_tgt_init_undef, h_unique =>
    have h_dv_cons : Block.definedVars (P := P) (C := Cmd P) (s :: rest) false
        = Stmt.definedVars s false ++ Block.definedVars rest false := by
      rw [Block.definedVars]
    have h_mv_cons : Block.modifiedVars (P := P) (C := Cmd P) (s :: rest)
        = Stmt.modifiedVars s ++ Block.modifiedVars rest := by
      rw [Block.modifiedVars]
    have h_no_writes_s : (∀ t : String, Q t → HasIdent.ident (P := P) t ∉ (Stmt.definedVars s false ++ Stmt.modifiedVars s)) := by
      intro t hQ hmem
      rcases List.mem_append.mp hmem with hd | hm
      · exact h_no_writes t hQ (by rw [h_dv_cons]; exact List.mem_append_left _ (List.mem_append_left _ hd))
      · exact h_no_writes t hQ (by rw [h_mv_cons]; exact List.mem_append_right _ (List.mem_append_left _ hm))
    have h_no_writes_rest : SrcNoGenWrites (P := P) Q rest := by
      intro t hQ hmem
      rcases List.mem_append.mp hmem with hd | hm
      · exact h_no_writes t hQ (by rw [h_dv_cons]; exact List.mem_append_left _ (List.mem_append_right _ hd))
      · exact h_no_writes t hQ (by rw [h_mv_cons]; exact List.mem_append_right _ (List.mem_append_right _ hm))
    have h_nofd_pair : Stmt.noFuncDecl s = true ∧ Block.noFuncDecl rest = true := by
      have : (Stmt.noFuncDecl s && Block.noFuncDecl rest) = true := by
        simpa only [Block.noFuncDecl] using h_nofd
      exact Bool.and_eq_true _ _ |>.mp this
    -- Uniqueness splits into head/tail Nodup plus head–tail disjointness.
    have h_unique_pair : (Stmt.initVars s ++ Block.initVars rest).Nodup := by
      rw [Block.initVars_cons] at h_unique; exact h_unique
    have h_unique_s : (Stmt.initVars s).Nodup := (List.nodup_append.mp h_unique_pair).1
    have h_unique_rest : (Block.initVars rest).Nodup := (List.nodup_append.mp h_unique_pair).2.1
    have h_disjoint_s_rest : ∀ y ∈ Stmt.initVars s, y ∉ Block.initVars rest := by
      have h_disj := (List.nodup_append.mp h_unique_pair).2.2
      intro y hy_s hy_r; exact h_disj y hy_s y hy_r rfl
    have h_tgt_iu_s : ∀ y ∈ Stmt.initVars s, ρ_tgt.store y = none := by
      intro y hy; exact h_tgt_init_undef y
        (by rw [Block.initVars_cons]; exact List.mem_append_left _ hy)
    have h_out_eq : (Block.nondetElimM (s :: rest) σ).1
        = (Stmt.nondetElimM s σ).1 ++ (Block.nondetElimM rest (Stmt.nondetElimM s σ).2).1 := by
      rw [Block.nondetElimM]
      rcases hh : Stmt.nondetElimM s σ with ⟨ss_s, σ_s⟩
      rcases hk : Block.nondetElimM rest σ_s with ⟨ss_r, σ_r⟩
      simp only [hh, hk]
    rw [h_out_eq]
    rcases stmts_cons_reaches_failing' P extendFactory (reflTrans_to_T h_reach) h_c_fail with
      hA | hB
    · -- CASE A: the head statement already fails.
      obtain ⟨d_head, h_head_run, hd_head_fail⟩ := hA
      obtain ⟨d_tgt, h_run_tgt, hd_tgt_fail⟩ :=
        nondetElim_stmt_to_fail_gen_sa hQgen extendFactory s σ ρ_src ρ_tgt d_head
          h_eval_eq h_fail_eq h_agree hwf
          h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_s h_unique_s h_no_writes_s h_nofd_pair.1
          h_head_run hd_head_fail
      exact stmts_prefix_failing_append P extendFactory
        (Stmt.nondetElimM s σ).1 (Block.nondetElimM rest (Stmt.nondetElimM s σ).2).1
        ρ_tgt d_tgt h_run_tgt hd_tgt_fail
    · -- CASE B: the head terminates at ρ_mid (clean), then `rest` fails.  Use the
      -- *terminal* head simulation to advance the relation, then recurse on `rest`.
      obtain ⟨ρ_mid, d_rest, h_head_term, h_rest_run, hd_rest_fail⟩ := hB
      obtain ⟨h_mid_fresh, ρ_mid_tgt, h_s_tgt, h_off_mid, h_fail_mid, h_eval_mid, h_fresh_mid⟩ :=
        nondetElim_stmt_gen_sa hQgen extendFactory s σ ρ_src ρ_mid ρ_tgt
          h_eval_eq h_fail_eq h_agree hwf
          h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_s h_unique_s h_no_writes_s h_nofd_pair.1 none h_head_term
      have h_wf₁ : StringGenState.WF (Stmt.nondetElimM s σ).2 :=
        (Stmt.nondetElimM_genStep s σ).wf_mono h_wf_gen
      have h_eval_mid_src : ρ_mid.factory = ρ_src.factory :=
        smallStep_noFuncDecl_preserves_eval P (EvalCmd P) extendFactory s ρ_src ρ_mid h_nofd_pair.1 h_head_term
      have hwf_mid : WellFormedSemanticEval ρ_mid.factory := h_eval_mid_src ▸ hwf
      -- Tail init-target undefinedness at the advanced TARGET env `ρ_mid_tgt`.
      have h_tgt_iu_rest : ∀ y ∈ Block.initVars rest, ρ_mid_tgt.store y = none := by
        intro y hy
        have h_y_tgt_none : ρ_tgt.store y = none := h_tgt_init_undef y
          (by rw [Block.initVars_cons]; exact List.mem_append_right _ hy)
        have h_y_not_init_s : y ∉ Stmt.initVars s := fun hc => h_disjoint_s_rest y hc hy
        have h_y_not_def_head : y ∉ Block.definedVars (P := P) (C := Cmd P) (Stmt.nondetElimM s σ).1 false := by
          intro h_mem
          rcases Stmt.nondetElimM_initVars_classified_Q hQgen s σ y h_mem with h_orig | ⟨str, h_eq, h_Q⟩
          · exact h_y_not_init_s h_orig
          · have h_y_def_rest : y ∈ Block.definedVars (P := P) (C := Cmd P) rest false :=
              hy
            exact h_no_writes_rest str h_Q (h_eq ▸ List.mem_append_left _ h_y_def_rest)
        exact block_run_terminal_preserves_none_of_not_definedVars
          h_y_not_def_head h_y_tgt_none (by simpa only [Env.outcomeConfig] using h_s_tgt)
      obtain ⟨d_tgt, h_run_tgt, hd_tgt_fail⟩ :=
        nondetElim_to_fail_gen_sa hQgen extendFactory rest (Stmt.nondetElimM s σ).2 ρ_mid ρ_mid_tgt d_rest
          h_eval_mid h_fail_mid h_off_mid hwf_mid
          h_wf₁ h_mid_fresh h_fresh_mid h_tgt_iu_rest h_unique_rest h_no_writes_rest h_nofd_pair.2
          h_rest_run hd_rest_fail
      exact ⟨d_tgt, ReflTrans_Transitive _ _ _ _
        (stmts_prefix_terminal_append P (EvalCmd P) extendFactory _ _ ρ_tgt ρ_mid_tgt h_s_tgt)
        h_run_tgt, hd_tgt_fail⟩
  termination_by sizeOf ss
end

/-- **Failing-config forward simulation (gen-parametric top form).** Every
reachable *failing* source configuration of `ss` is matched by a reachable
failing configuration of `Block.nondetElim ss` (same `ρ₀`, no endpoint demand).
Instantiates the gen-level `_to_fail` at `ρ_tgt = ρ₀` and the empty generator. -/
private theorem nondetElim_simulation_to_fail {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen ndelimItePrefix sg).1)
            ∧ (∀ sg, Q (StringGenState.gen ndelimLoopPrefix sg).1))
    (extendFactory : ExtendFactory P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ : Env P) (c : Config P (Cmd P))
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_no_gen_suffix : ∀ s, Q s → ρ₀.store (HasIdent.ident (P := P) s) = none)
    (h_no_writes : SrcNoGenWrites (P := P) Q ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_store_inits : ∀ y ∈ Block.initVars ss, ρ₀.store y = none)
    (h_unique : Block.uniqueInits ss)
    (h_reach : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ₀) c)
    (h_c_fail : c.getEnv.hasFailure = true) :
    ∃ d, StepStmtStar P (EvalCmd P) extendFactory
        (.stmts (Block.nondetElim ss) ρ₀) d
      ∧ d.getEnv.hasFailure = true := by
  have h_tgt_fresh : GenFreshStore Q StringGenState.emp ρ₀.store := by
    intro s h_suf _; exact h_no_gen_suffix s h_suf
  exact nondetElim_to_fail_gen_sa hQgen extendFactory ss StringGenState.emp ρ₀ ρ₀ c
    rfl rfl (StoreAgreement.refl _) hwf
    StringGenState.wf_emp h_no_gen_suffix h_tgt_fresh h_store_inits h_unique h_no_writes h_nofd h_reach h_c_fail

/-- **`Block.nondetElim` failing-config preservation (at `Q := ndelimKind`).**  A
reachable failing source configuration of `ss` is matched by a reachable failing
configuration of `Block.nondetElim ss`, with no terminal/exiting endpoint
required.  This is the `_to_fail` sibling of `nondetElim_sound_kind`; the
`Env.varsUndefined`/`SrcNoGenWrites` preconditions are exactly those the
terminal soundness theorems already consume, so it composes into the
structured-pass failing bridge identically. -/
theorem nondetElim_to_fail {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    (extendFactory : ExtendFactory P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ : Env P) (c : Config P (Cmd P))
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_no_gen_suffix : Env.varsUndefined (P := P) ndelimKind ρ₀)
    (h_no_writes : SrcNoGenWrites (P := P) ndelimKind ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_store_inits : ∀ y ∈ Block.initVars ss, ρ₀.store y = none)
    (h_unique : Block.uniqueInits ss)
    (h_reach : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ₀) c)
    (h_c_fail : c.getEnv.hasFailure = true) :
    ∃ d, StepStmtStar P (EvalCmd P) extendFactory
        (.stmts (Block.nondetElim ss) ρ₀) d
      ∧ d.getEnv.hasFailure = true :=
  nondetElim_simulation_to_fail (Q := ndelimKind) ndelimKind_gen
    extendFactory ss ρ₀ c hwf
    (Env.varsUndefined_iff.mp h_no_gen_suffix) h_no_writes h_nofd h_store_inits h_unique h_reach h_c_fail

/-- Compositional-input failing-config simulation: a reachable failing source
config of `ss` (run from `ρ₀`) is matched by a reachable failing config of
`Block.nondetElim ss` run from an *overapproximating* target env `ρ_tgt`
(`StoreAgreement ρ₀.store ρ_tgt.store`).  Thin forwarder to
`nondetElim_to_fail_gen_sa` at `σ := .emp`, `Q := ndelimKind`. -/
theorem nondetElim_to_fail_compositional {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    (extendFactory : ExtendFactory P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ_tgt : Env P) (c : Config P (Cmd P))
    (h_eval_eq : ρ_tgt.factory = ρ₀.factory)
    (h_fail_eq : ρ_tgt.hasFailure = ρ₀.hasFailure)
    (h_agree : StoreAgreement ρ₀.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_src_no_gen : Env.varsUndefined (P := P) ndelimKind ρ₀)
    (h_tgt_no_gen : Env.varsUndefined (P := P) ndelimKind ρ_tgt)
    (h_tgt_inits : ∀ y ∈ Block.initVars ss, ρ_tgt.store y = none)
    (h_no_writes : SrcNoGenWrites (P := P) ndelimKind ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_unique : Block.uniqueInits ss)
    (h_reach : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ₀) c)
    (h_c_fail : c.getEnv.hasFailure = true) :
    ∃ d, StepStmtStar P (EvalCmd P) extendFactory
        (.stmts (Block.nondetElim ss) ρ_tgt) d
      ∧ d.getEnv.hasFailure = true := by
  have h_tgt_fresh : GenFreshStore ndelimKind StringGenState.emp ρ_tgt.store := by
    intro s h_suf _; exact Env.varsUndefined_apply h_tgt_no_gen s h_suf
  exact nondetElim_to_fail_gen_sa ndelimKind_gen extendFactory ss StringGenState.emp ρ₀ ρ_tgt c
    h_eval_eq h_fail_eq h_agree hwf
    StringGenState.wf_emp (Env.varsUndefined_iff.mp h_src_no_gen) h_tgt_fresh h_tgt_inits h_unique h_no_writes h_nofd
    h_reach h_c_fail


/-! ## `nondetElim` preserves `getBlockLabels`

Template (from `NondetElimProps`): `Stmt/Block.nondetElimM_loopHasNoInvariants`. The pass keeps every
`.block` label, recurses into sub-bodies, and the only generated statements (the
`init $g := *` havoc and, for nondet loops, the body-tail re-havoc of `$g`) are
`.cmd`s. -/

mutual
/-- `Stmt.nondetElimM` preserves `getBlockLabels` at any threaded state. -/
theorem Stmt.nondetElimM_getBlockLabels {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.getBlockLabels (Stmt.nondetElimM s σ).1 = Block.getBlockLabels [s] := by
  match s with
  | .cmd c =>
      rw [Stmt.nondetElimM]
  | .block lbl bss md =>
      rw [Stmt.nondetElimM_block_out,
          show ([Stmt.block lbl (Block.nondetElimM bss σ).1 md] : List (Stmt P (Cmd P)))
            = Stmt.block lbl (Block.nondetElimM bss σ).1 md :: [] from rfl,
          Block.getBlockLabels_block_cons,
          show ([Stmt.block lbl bss md] : List (Stmt P (Cmd P)))
            = Stmt.block lbl bss md :: [] from rfl,
          Block.getBlockLabels_block_cons,
          Block.nondetElimM_getBlockLabels bss σ]
  | .ite (.det e) tss ess md =>
      rw [Stmt.nondetElimM_ite_det_out,
          show ([Stmt.ite (.det e) (Block.nondetElimM tss σ).1
                  (Block.nondetElimM ess (Block.nondetElimM tss σ).2).1 md]
              : List (Stmt P (Cmd P)))
            = Stmt.ite (.det e) (Block.nondetElimM tss σ).1
                (Block.nondetElimM ess (Block.nondetElimM tss σ).2).1 md :: [] from rfl,
          Block.getBlockLabels_ite_cons,
          show ([Stmt.ite (.det e) tss ess md] : List (Stmt P (Cmd P)))
            = Stmt.ite (.det e) tss ess md :: [] from rfl,
          Block.getBlockLabels_ite_cons,
          Block.nondetElimM_getBlockLabels tss σ,
          Block.nondetElimM_getBlockLabels ess _]
  | .ite .nondet tss ess md =>
      rw [Stmt.nondetElimM_ite_nondet_out]
      -- The output is `[init $g, ite (.det $g) tss' ess']`; the prelude `init`
      -- is a `.cmd` (label-free), and both branches recurse. Finish by the
      -- structural cons lemmas + the branch IHs.
      simp only [Block.getBlockLabels_cmd_cons,
                 Block.nondetElimM_getBlockLabels tss,
                 Block.nondetElimM_getBlockLabels ess, Block.getBlockLabels_nil,
                 Block.getBlockLabels_ite_cons]
  | .loop (.det e) m inv body md =>
      rw [Stmt.nondetElimM_loop_det_out,
          show ([Stmt.loop (.det e) m inv (Block.nondetElimM body σ).1 md]
              : List (Stmt P (Cmd P)))
            = Stmt.loop (.det e) m inv (Block.nondetElimM body σ).1 md :: [] from rfl,
          Block.getBlockLabels_loop_cons,
          show ([Stmt.loop (.det e) m inv body md] : List (Stmt P (Cmd P)))
            = Stmt.loop (.det e) m inv body md :: [] from rfl,
          Block.getBlockLabels_loop_cons,
          Block.nondetElimM_getBlockLabels body σ]
  | .loop .nondet m inv body md =>
      rw [Stmt.nondetElimM_loop_nondet_out]
      -- The output is `[init $g, loop (body' ++ [havoc $g])]`; the prelude
      -- `init` and the body-tail `havoc` are `.cmd`s (label-free), and the loop
      -- body recurses. Generalise the generated name/state and finish by the
      -- structural cons/append lemmas + the body IH.
      simp only [Block.getBlockLabels_cmd_cons, Block.getBlockLabels_append,
                 Block.nondetElimM_getBlockLabels body, Block.getBlockLabels_nil,
                 Block.getBlockLabels_loop_cons, List.append_nil]
  | .exit lbl md =>
      rw [Stmt.nondetElimM]
  | .funcDecl d md =>
      rw [Stmt.nondetElimM]
  | .typeDecl t md =>
      rw [Stmt.nondetElimM]
  termination_by sizeOf s

/-- `Block.nondetElimM` preserves `getBlockLabels` at any threaded state. -/
theorem Block.nondetElimM_getBlockLabels {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.getBlockLabels (Block.nondetElimM ss σ).1 = Block.getBlockLabels ss := by
  match ss with
  | [] => simp [Block.nondetElimM, Block.getBlockLabels]
  | s :: rest =>
      rw [Block.nondetElimM_cons_out, Block.getBlockLabels_append,
          show (s :: rest) = [s] ++ rest from rfl, Block.getBlockLabels_append,
          Stmt.nondetElimM_getBlockLabels s σ,
          Block.nondetElimM_getBlockLabels rest _]
  termination_by sizeOf ss
end

/-- Pure-wrapper corollary: `Block.nondetElim` preserves `getBlockLabels`. -/
theorem Block.nondetElim_getBlockLabels {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) :
    Block.getBlockLabels (Block.nondetElim ss) = Block.getBlockLabels ss := by
  rw [Block.nondetElim, Block.nondetElimM_getBlockLabels]

/-! ## `nondetElim` per-pass overapproximation instance

The pass's own `OverapproximatesUptoWhen` instance, over pass-local neutral
languages whose `initEnvWF` mentions only the pass's own generated-name kind
`ndelimKind`.  The output relation is the store-agreement / failure-flag /
factory triple (the shared `EnvStoreAgree`).  Terminal / exiting reuse the
`nondetElim_sound_kind*_compositional` sims and `CanFail` reuses
`nondetElim_to_fail_compositional`, at the diagonal `ρ_tgt := ρ₀`. -/
section NondetElimOverapprox
open Specification Specification.Transform

/-- `Block.nondetElim` overapproximates its source up to `EnvStoreAgree`: for a
block that is func-decl-free, has unique inits, and never writes an `ndelimKind`
name, every terminating, exiting, or failing source run is matched by a run of the
rewritten block ending in a store-agreeing, failure-matching, factory-preserving
target state.  Terminal / exiting cases discharge via the
`nondetElim_sound_kind*_compositional` sims and `CanFail` via
`nondetElim_to_fail_compositional`, at the diagonal `ρ_tgt := ρ₀` (the evaluator is
preserved since `nondetElim` keeps `noFuncDecl`); the target `initEnvWF` classifies
the output `initVars` via `nondetElimM_initVars_classified_Q`. -/
theorem nondetElim_overapproximates_upto_local {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P] (extendFactory : ExtendFactory P) :
    Specification.Transform.OverapproximatesUptoWhen
      (· = ·)
      (Specification.Transform.EnvStoreAgree (P := P))
      (Lang.imperativeBlock (EvalCmd P) extendFactory (isAtAssert P))
      (Lang.imperativeBlock (EvalCmd P) extendFactory (isAtAssert P))
      (fun ss => some (Block.nondetElim ss))
      (fun ss =>
        Block.noFuncDecl ss = true
        ∧ Block.uniqueInits ss
        ∧ SrcNoGenWrites (P := P) ndelimKind ss)
      ndelimKind ndelimKind := by
  intro ss ss' ht hpre ρ₀ ρ₀' hEq hwf
  subst hEq
  simp only [Option.some.injEq] at ht
  subst ht
  obtain ⟨h_nofd, h_unique, h_writes⟩ := hpre
  obtain ⟨hwf_full, h_inits, h_gens⟩ := hwf
  refine ⟨fun ρ' => ⟨fun hstar => ?_, fun lbl hstar => ?_⟩, ?_, ?_⟩
  · -- ===== TERMINAL ARM =====
    have h_term : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ₀) (.terminal ρ') := by
      simpa [Lang.imperativeBlock] using hstar
    obtain ⟨ρ_out, h_run, h_off, h_fl⟩ :=
      nondetElim_sound_kind_compositional extendFactory ss ρ₀ ρ' ρ₀
        rfl rfl (StoreAgreement.refl _)
        hwf_full
        h_gens h_gens h_inits h_writes h_nofd h_unique h_term
    have h_src_eval : ρ'.factory = ρ₀.factory :=
      block_noFuncDecl_preserves_factory P (EvalCmd P) extendFactory ss ρ₀ ρ' h_nofd h_term
    have h_tgt_eval : ρ_out.factory = ρ₀.factory :=
      block_noFuncDecl_preserves_factory P (EvalCmd P) extendFactory (Block.nondetElim ss) ρ₀ ρ_out
        (nondetElim_noFuncDecl ss h_nofd) h_run
    refine ⟨ρ_out, ⟨h_off, h_fl.symm, ?_⟩, ?_⟩
    · rw [h_tgt_eval, h_src_eval]
    · simpa [Lang.imperativeBlock] using h_run
  · -- ===== EXITING ARM =====
    have h_exit : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ₀) (.exiting lbl ρ') := by
      simpa [Lang.imperativeBlock] using hstar
    obtain ⟨ρ_out, h_run, h_off, h_fl⟩ :=
      nondetElim_sound_kind_exit_compositional extendFactory ss ρ₀ ρ' ρ₀
        rfl rfl (StoreAgreement.refl _)
        hwf_full
        h_gens h_gens h_inits h_writes h_nofd h_unique lbl h_exit
    have h_src_eval : ρ'.factory = ρ₀.factory :=
      block_noFuncDecl_preserves_factory_exiting ss ρ₀ ρ' lbl h_nofd h_exit
    have h_tgt_eval : ρ_out.factory = ρ₀.factory :=
      block_noFuncDecl_preserves_factory_exiting
        (Block.nondetElim ss) ρ₀ ρ_out lbl (nondetElim_noFuncDecl ss h_nofd) h_run
    refine ⟨ρ_out, ⟨h_off, h_fl.symm, ?_⟩, ?_⟩
    · rw [h_tgt_eval, h_src_eval]
    · simpa [Lang.imperativeBlock] using h_run
  · -- ===== CanFail ARM =====
    intro h_src
    by_cases h_ρ₀_fail : ρ₀.hasFailure = true
    · refine ⟨(Config.stmts (Block.nondetElim ss) ρ₀ : Config P (Cmd P)), ?_, ?_⟩
      · simpa [Lang.imperativeBlock, Config.getEnv] using h_ρ₀_fail
      · simpa [Lang.imperativeBlock] using
          (ReflTrans.refl (Config.stmts (Block.nondetElim ss) ρ₀ : Config P (Cmd P)))
    · obtain ⟨cfg_s, h_cfg_fail, h_cfg_reach⟩ := h_src
      have h_reach : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ₀) cfg_s := by
        simpa [Lang.imperativeBlock] using h_cfg_reach
      have h_fail : cfg_s.getEnv.hasFailure = true := by
        simpa [Lang.imperativeBlock] using h_cfg_fail
      obtain ⟨d, hd_run, hd_fail⟩ :=
        nondetElim_to_fail_compositional extendFactory ss ρ₀ ρ₀ cfg_s
          rfl rfl (StoreAgreement.refl _)
          hwf_full
          h_gens h_gens h_inits h_writes h_nofd h_unique h_reach h_fail
      exact ⟨d, by simpa [Lang.imperativeBlock] using hd_fail,
        by simpa [Lang.imperativeBlock] using hd_run⟩
  · -- ===== target initEnvWF conjunct (ndelim-only) =====
    refine ⟨hwf_full, ?_, h_gens⟩
    intro x hx
    rcases Block.nondetElimM_initVars_classified_Q ndelimKind_gen ss StringGenState.emp x hx with
      h_src | ⟨str, h_eq, h_nd⟩
    · exact h_inits x h_src
    · rw [h_eq]; exact Env.varsUndefined_apply h_gens str h_nd

end NondetElimOverapprox

end Imperative
