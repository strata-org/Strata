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
public import Strata.DL.Imperative.Logic.TraceRelations
import Strata.DL.Imperative.Logic.TraceRelationsProps
import all Strata.DL.Imperative.StmtSemanticsProps
import all Strata.DL.Util.StringGen
import all Strata.Util.Relations
import all Strata.Util.RelationsProps

/-! # Nondeterminism elimination correctness

This module proves the base-command simulation used by the Core-specific result
in `NondetElimCoreCorrect`. Generated guard commands are event-silent, source
commands replay one-for-one, and final environments extend the source only with
generated guard registers.

The module also retains the failure-flag overapproximation used by
`StructuredToUnstructuredPipelineCorrect`. -/

public section

namespace Imperative

/-! ## Structural postcondition: the pass output has no nondeterministic control

`Block.noNondetGuards` holds of every output of `Block.nondetElim` (spec guarantee
2): the rewrite replaces each nondeterministic `.ite`/`.loop` guard with a
deterministic read, so no `.ite .nondet`/`.loop .nondet` survives. The generic
mutual `Stmt.nondetElimM_noNondetGuards` / `Block.nondetElimM_noNondetGuards` and
the top-level `nondetElim_noNondetGuards` are proved (over an arbitrary command
type) in `NondetElimProps`; the corollary below specialises them. -/

/-- `nondetElim` removes nondeterministic loops, so its output satisfies
`containsNondetLoop = false` (via the `noNondetGuards` postcondition). -/
theorem nondetElim_containsNondetLoop {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) :
    Block.containsNondetLoop (Block.nondetElim ss) = false :=
  Block.not_containsNondetLoop_of_noNondetGuards _ (nondetElim_noNondetGuards ss)

/-! ## Foundation lemmas for the simulation proof

These are fully-proved building blocks for `nondetElim_simulation`, reused
arm-by-arm.  They live outside the main inductive lemma so that each can be
verified independently. -/

section Foundation

/-- Outcome-generic `.ite .nondet` prefix replay (then side): the chosen branch
`tss` reaching `Env.outcomeConfig oc ρt'` drives the emitted prefix to the same
outcome at the block-projected env (the ite branch runs in a `.block .none`
scope, so the guard `ident` — defined by the `init` prefix — is projected away). -/
theorem step_ndelim_ite_prefix_outcome {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [DecidableEq P.Ident] [LawfulHasFvar P]
    (b : Bool) (ident : P.Ident) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (ρ ρt' : Env P) (oc : Option String)
    (h_none : ρ.store ident = none)
    (hwf_var : WellFormedSemanticEvalVar ρ.factory)
    (hwf_mono : WellFormedSemanticEvalMono ρ.factory)
    (h_branch : StepStmtStar P (EvalCmd P)
      (.stmts (if b then tss else ess)
        ({ ρ with store := SemanticStore.update ρ.store ident (if b then HasBool.tt else HasBool.ff) } : Env P))
      (Env.outcomeConfig oc ρt')) :
    StepStmtStar P (EvalCmd P)
      (.stmts [.cmd (HasInit.init ident HasBool.boolTy (.nondet) md),
               .ite (.det (HasFvar.mkTypedFvar ident HasBool.boolTy)) tss ess md] ρ)
      (Env.outcomeConfig oc ({ ρt' with
        store := projectStore (SemanticStore.update ρ.store ident (if b then HasBool.tt else HasBool.ff)) ρt'.store } : Env P)) := by
  let v : P.Expr := if b then HasBool.tt else HasBool.ff
  have hval : HasVal.valueOfTy ρ.factory v HasBool.boolTy := by
    simp only [v]; split
    · exact (HasBool.boolIsValOfTy ρ.factory).1
    · exact (HasBool.boolIsValOfTy ρ.factory).2
  let ρg : Env P := { ρ with store := SemanticStore.update ρ.store ident v }
  have h1 : StepStmtStar P (EvalCmd P)
      (.stmts [.cmd (HasInit.init ident HasBool.boolTy (.nondet) md),
               .ite (.det (HasFvar.mkTypedFvar ident HasBool.boolTy)) tss ess md] ρ)
      (.stmts [.ite (.det (HasFvar.mkTypedFvar ident HasBool.boolTy)) tss ess md] ρg) :=
    stmts_cons_step P (EvalCmd P) _ _ ρ ρg
      (step_init_havoc_to ident HasBool.boolTy v md ρ h_none hval hwf_var)
  have h_guard : P.eval ρ.factory ρg.store (HasFvar.mkTypedFvar ident HasBool.boolTy) = some v :=
    eval_mkTypedFvar_storeWith ρ.factory ρ.store ident v (LawfulHasVal.valueOfTy_isVal _ _ _ hval) hwf_var hwf_mono
  have h_blk : StepStmtStar P (EvalCmd P)
      (.block .none ρg.store (.stmts (if b then tss else ess) ρg))
      (Env.outcomeConfig oc ({ ρt' with store := projectStore ρg.store ρt'.store } : Env P)) :=
    blockT_none_build_outcome _ ρg.store oc ρt' h_branch
  have h2 : StepStmtStar P (EvalCmd P)
      (.stmts [.ite (.det (HasFvar.mkTypedFvar ident HasBool.boolTy)) tss ess md] ρg)
      (Env.outcomeConfig oc ({ ρt' with store := projectStore ρg.store ρt'.store } : Env P)) := by
    refine .step _ _ _ .step_stmts_cons ?_
    cases b with
    | true =>
      exact .step _ _ _ (.step_seq_inner (.step_ite_true h_guard))
        (seq_nil_outcome _ _ oc h_blk)
    | false =>
      exact .step _ _ _ (.step_seq_inner (.step_ite_false h_guard))
        (seq_nil_outcome _ _ oc h_blk)
  exact ReflTrans_Transitive _ _ _ _ h1 h2

/-- Failing `.ite .nondet` prefix replay (then side): the chosen branch `tss`
reaching a *failing* config drives the emitted `init $g; ite $g` prefix to a
failing config (havoc value `tt`). -/
theorem step_ndelim_ite_prefix_fail {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [DecidableEq P.Ident] [LawfulHasFvar P]
    (b : Bool) (ident : P.Ident) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (ρ : Env P) (d : Config P (Cmd P))
    (h_none : ρ.store ident = none)
    (hwf_var : WellFormedSemanticEvalVar ρ.factory)
    (hwf_mono : WellFormedSemanticEvalMono ρ.factory)
    (h_branch : StepStmtStar P (EvalCmd P)
      (.stmts (if b then tss else ess)
        ({ ρ with store := SemanticStore.update ρ.store ident (if b then HasBool.tt else HasBool.ff) } : Env P)) d)
    (hd : d.getEnv.hasFailure = true) :
    ∃ d', StepStmtStar P (EvalCmd P)
      (.stmts [.cmd (HasInit.init ident HasBool.boolTy (.nondet) md),
               .ite (.det (HasFvar.mkTypedFvar ident HasBool.boolTy)) tss ess md] ρ) d'
      ∧ d'.getEnv.hasFailure = true := by
  let v : P.Expr := if b then HasBool.tt else HasBool.ff
  have hval : HasVal.valueOfTy ρ.factory v HasBool.boolTy := by
    simp only [v]; split
    · exact (HasBool.boolIsValOfTy ρ.factory).1
    · exact (HasBool.boolIsValOfTy ρ.factory).2
  let ρg : Env P := { ρ with store := SemanticStore.update ρ.store ident v }
  have h1 : StepStmtStar P (EvalCmd P)
      (.stmts [.cmd (HasInit.init ident HasBool.boolTy (.nondet) md),
               .ite (.det (HasFvar.mkTypedFvar ident HasBool.boolTy)) tss ess md] ρ)
      (.stmts [.ite (.det (HasFvar.mkTypedFvar ident HasBool.boolTy)) tss ess md] ρg) :=
    stmts_cons_step P (EvalCmd P) _ _ ρ ρg
      (step_init_havoc_to ident HasBool.boolTy v md ρ h_none hval hwf_var)
  have h_guard : P.eval ρ.factory ρg.store (HasFvar.mkTypedFvar ident HasBool.boolTy) = some v :=
    eval_mkTypedFvar_storeWith ρ.factory ρ.store ident v (LawfulHasVal.valueOfTy_isVal _ _ _ hval) hwf_var hwf_mono
  -- The single-statement `.ite` scopes the chosen branch in a `.block .none`; run
  -- the branch inside that scope to the failing config `.block none ρg.store d`
  -- (a `.block`'s `getEnv` is its inner config's, so the failure flag is preserved).
  let dblk : Config P (Cmd P) := .block .none ρg.store d
  have h_blk_run : StepStmtStar P (EvalCmd P)
      (.block .none ρg.store (.stmts (if b then tss else ess) ρg)) dblk :=
    block_inner_star P (EvalCmd P) _ _ .none ρg.store h_branch
  have hdblk : dblk.getEnv.hasFailure = true := by simpa only [dblk, Config.getEnv] using hd
  have h_ite : StepStmtStar P (EvalCmd P)
      (.stmt (.ite (.det (HasFvar.mkTypedFvar ident HasBool.boolTy)) tss ess md) ρg) dblk := by
    cases b with
    | true => exact .step _ _ _ (.step_ite_true h_guard) h_blk_run
    | false => exact .step _ _ _ (.step_ite_false h_guard) h_blk_run
  obtain ⟨d', h2, hd'⟩ :=
    stmt_to_singleton_stmts_fail
      (.ite (.det (HasFvar.mkTypedFvar ident HasBool.boolTy)) tss ess md) ρg dblk h_ite hdblk
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
residual run from `.seq (.block .none ρ.store (.stmts body (ρ + false))) [loop]`).
The invariant list `inv` is threaded verbatim and plays no role in the
enter/exit inversion; the residual carries a strict len-decrease.  Casing `oc` makes the outcome target a
constructor, so the `.refl` case (which would require `Env.outcomeConfig oc ρ' =
.stmt (.loop …)`) is ruled out by constructor mismatch. -/
theorem loop_det_step_first_inv {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    {e : P.Expr} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {ρ ρ' : Env P} {oc : Option String}
    (hstar : ReflTransT (StepStmt P (EvalCmd P))
      (.stmt (.loop (.det e) m inv body md) ρ) (Env.outcomeConfig oc ρ')) :
    (P.eval ρ.factory ρ.store e = some HasBool.ff ∧
        ∃ (hrest : ReflTransT (StepStmt P (EvalCmd P))
            (.terminal ρ)
            (Env.outcomeConfig oc ρ')),
          hrest.len < hstar.len) ∨
    (P.eval ρ.factory ρ.store e = some HasBool.tt ∧
        ∃ (hrest : ReflTransT (StepStmt P (EvalCmd P))
            (.seq (.block .none ρ.store (.stmts body ρ))
              [.loop (.det e) m inv body md])
            (Env.outcomeConfig oc ρ')),
          hrest.len < hstar.len) := by
  cases oc with
  | none =>
    simp only [Env.outcomeConfig] at hstar ⊢
    match hstar with
    | .step _ _ _ (StepStmt.step_loop_exit h_cond) hrest =>
      exact .inl ⟨h_cond, hrest, by simp only [ReflTransT.len]; omega⟩
    | .step _ _ _ (StepStmt.step_loop_enter h_cond) hrest =>
      exact .inr ⟨h_cond, hrest, by simp only [ReflTransT.len]; omega⟩
  | some lbl =>
    simp only [Env.outcomeConfig] at hstar ⊢
    match hstar with
    | .step _ _ _ (StepStmt.step_loop_exit h_cond) hrest =>
      exact .inl ⟨h_cond, hrest, by simp only [ReflTransT.len]; omega⟩
    | .step _ _ _ (StepStmt.step_loop_enter h_cond) hrest =>
      exact .inr ⟨h_cond, hrest, by simp only [ReflTransT.len]; omega⟩

/-- First-step inversion of a *nondeterministic* loop run reaching an outcome
(`Env.outcomeConfig oc ρ'`).  The first step is either `step_loop_nondet_exit`
(residual run from `.terminal (ρ + false)`) or `step_loop_nondet_enter`
(residual run from `.seq (.block .none ρ.store (.stmts body (ρ + false))) [loop]`).
The invariant list `inv` is threaded verbatim and plays no role in the
enter/exit inversion; the residual carries a strict len-decrease.  Unlike the deterministic variant there is *no*
guard read: the enter/exit choice is genuinely nondeterministic. -/
theorem loop_nondet_step_first_inv {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {ρ ρ' : Env P} {oc : Option String}
    (hstar : ReflTransT (StepStmt P (EvalCmd P))
      (.stmt (.loop .nondet m inv body md) ρ) (Env.outcomeConfig oc ρ')) :
    (∃ (hrest : ReflTransT (StepStmt P (EvalCmd P))
        (.terminal ρ)
        (Env.outcomeConfig oc ρ')),
      hrest.len < hstar.len) ∨
    (∃ (hrest : ReflTransT (StepStmt P (EvalCmd P))
        (.seq (.block .none ρ.store (.stmts body ρ))
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
`.seq (.block .none ρ.store (.stmts body (ρ + false))) [loop]`), with the
residual carrying the failing config and a strict len-decrease. -/
theorem loop_nondet_step_first_inv_fail {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {ρ : Env P} {c : Config P (Cmd P)}
    (hstar : ReflTransT (StepStmt P (EvalCmd P))
      (.stmt (.loop .nondet m inv body md) ρ) c)
    (hc : c.getEnv.hasFailure = true) :
    ρ.hasFailure = true ∨
    (∃ (hrest : ReflTransT (StepStmt P (EvalCmd P))
        (.terminal ρ) c),
      hrest.len < hstar.len) ∨
    (∃ (hrest : ReflTransT (StepStmt P (EvalCmd P))
        (.seq (.block .none ρ.store (.stmts body ρ))
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
`SemanticStore.isReserved`/`h_src_fresh` machinery quarantines the generated guard slots,
orthogonal to the source-var relation.  Each docstring below notes only what is
distinctive to that lemma. -/

/-- Deterministic-loop iteration. -/
private theorem nondetElim_loop_det_sim_iteration_sa {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (e : P.Expr) (m : Option P.Expr) {inv : List (String × P.Expr)}
    (body body' : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ : StringGenState)
    (h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
      ρb_tgt.hasFailure = ρb_src.hasFailure →
      ρb_tgt.factory = ρb_src.factory →
      StoreAgreement ρb_src.store ρb_tgt.store →
      WellFormedSemanticEval ρb_src.factory →
      StringGenState.WF σ →
      (∀ t, Q t →
        ρb_src.store (HasIdent.ident (P := P) t) = none) →
      SemanticStore.isReserved Q σ ρb_tgt.store →
      (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
      StepStmtStar P (EvalCmd P) (.stmts body ρb_src) (Env.outcomeConfig oc_b ρb') →
      (∀ t, Q t →
          ρb'.store (HasIdent.ident (P := P) t) = none)
        ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P)
            (.stmts body' ρb_tgt) (Env.outcomeConfig oc_b ρb_out)
          ∧ StoreAgreement ρb'.store ρb_out.store
          ∧ ρb_out.hasFailure = ρb'.hasFailure
          ∧ SemanticStore.isReserved Q σ_out ρb_out.store)
    (oc : Option String)
    (ρ_src ρ' ρ_tgt : Env P) (n : Nat)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_fac_eq : ρ_tgt.factory = ρ_src.factory)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : SemanticStore.isReserved Q σ ρ_tgt.store)
    (h_tgt_init_undef : ∀ y ∈ Block.initVars body, ρ_tgt.store y = none)
    (hstarT : ReflTransT (StepStmt P (EvalCmd P))
      (.stmt (.loop (.det e) m inv body md) ρ_src) (Env.outcomeConfig oc ρ'))
    (hlen : hstarT.len ≤ n) :
    (∀ t, Q t →
        ρ'.store (HasIdent.ident (P := P) t) = none)
      ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P)
          (.stmt (.loop (.det e) m inv body' md) ρ_tgt)
          (Env.outcomeConfig oc ρ_out)
        ∧ StoreAgreement ρ'.store ρ_out.store
        ∧ ρ_out.hasFailure = ρ'.hasFailure
        ∧ SemanticStore.isReserved Q σ ρ_out.store := by
  induction n generalizing oc ρ_src ρ_tgt ρ' with
  | zero =>
    rcases loop_det_step_first_inv hstarT with
      ⟨_, _, hl⟩ | ⟨_, _, hl⟩
    · exact absurd (Nat.lt_of_lt_of_le hl hlen) (Nat.not_lt_zero _)
    · exact absurd (Nat.lt_of_lt_of_le hl hlen) (Nat.not_lt_zero _)
  | succ n ih =>
    rcases loop_det_step_first_inv hstarT with
      ⟨h_cond, hrest, hl⟩ | ⟨h_cond, hrest, hl⟩
    · have hlen : hstarT.len ≤ n + 1 := hlen
      cases oc with
      | none =>
        simp only [Env.outcomeConfig] at hrest ⊢
        have hρ'_eq : ρ' = ρ_src := by
          match hrest with
          | .refl _ => rfl
          | .step _ _ _ h _ => exact nomatch h
        have h_cond_t : P.eval ρ_tgt.factory ρ_tgt.store e = some HasBool.ff := by
          rw [h_fac_eq]
          exact hwf.mono e HasBool.ff ρ_src.store ρ_tgt.store
            (storeAgreement_supplies_mono_premise ρ_src.store ρ_tgt.store h_agree) h_cond
        subst hρ'_eq
        refine ⟨h_src_fresh, ρ_tgt, ?_, ?_, ?_, ?_⟩
        · exact .step _ _ _ (StepStmt.step_loop_exit
            h_cond_t) (.refl _)
        · simpa using h_agree
        · simp [h_fail_eq]
        · simpa using h_tgt_fresh
      | some lbl =>
        exfalso
        simp only [Env.outcomeConfig] at hrest
        match hrest with
        | .step _ _ _ h _ => exact nomatch h
    · have hlen : hstarT.len ≤ n + 1 := hlen
      have h_cond_t : P.eval ρ_tgt.factory ρ_tgt.store e = some HasBool.tt := by
        rw [h_fac_eq]
        exact hwf.mono e HasBool.tt ρ_src.store ρ_tgt.store
          (storeAgreement_supplies_mono_premise ρ_src.store ρ_tgt.store h_agree) h_cond
      have h_block_tgt_to : ∀ (ρb_tgt : Env P),
          StepStmtStar P (EvalCmd P)
            (.stmts body' ρ_tgt)
            (.terminal ρb_tgt) →
          StepStmtStar P (EvalCmd P)
            (.block .none ρ_tgt.store (.stmts body' ρ_tgt))
            (.terminal ({ ρb_tgt with store := projectStore ρ_tgt.store ρb_tgt.store } : Env P)) := by
        intro ρb_tgt h_run
        refine ReflTrans_Transitive _ _ _ _
          (block_inner_star P (EvalCmd P) _ _ .none ρ_tgt.store h_run) ?_
        exact .step _ _ _ StepStmt.step_block_done (.refl _)
      cases oc with
      | none =>
        simp only [Env.outcomeConfig] at hrest ⊢
        have hl : hrest.len < hstarT.len := hl
        have ⟨ρ_block, h_block_term, h_loop_stmts, hlen_seq⟩ :=
          seqT_reaches_terminal hrest
        have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
          blockT_none_reaches_terminal h_block_term
        have ⟨ρ_x, h_loop_T_T, h_nil, hlen_cons⟩ :=
          stmtsT_cons_terminal h_loop_stmts
        have hρ_x_eq : ρ_x = ρ' := by
          match h_nil with
          | .step _ _ _ .step_stmts_nil hr2 =>
            match hr2 with
            | .refl _ => rfl
            | .step _ _ _ h _ => exact nomatch h
        subst hρ_x_eq
        have h_body_run : StepStmtStar P (EvalCmd P)
            (.stmts body ρ_src) (Env.outcomeConfig none ρ_inner) :=
          reflTransT_to_prop h_inner_term
        obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner, h_fresh_inner⟩ :=
          h_body_sim none ρ_src ρ_inner ρ_tgt h_fail_eq h_fac_eq h_agree hwf
            h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef h_body_run
        have heq_ρ_block_full :
            ρ_block = ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P) := by
          rw [heq_ρ_block]
        subst heq_ρ_block_full
        let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store }
        let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store }
        have hwf_next : WellFormedSemanticEval ρ_src_next.factory := by
          show WellFormedSemanticEval ρ_inner.factory
          have h1 : ρ_src.factory = ρ_inner.factory := by
            have := star_preserves_factory P (EvalCmd P) h_body_run
            simpa [Config.getEnv, Env.outcomeConfig] using this
          rw [← h1]; exact hwf
        have h_fail_eq_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
          show ρ_inner_tgt.hasFailure = ρ_inner.hasFailure; exact h_fail_inner
        have h_fac_eq_next : ρ_tgt_next.factory = ρ_src_next.factory := by
          have h1 : ρ_src.factory = ρ_inner.factory := by
            have := star_preserves_factory P (EvalCmd P) h_body_run
            simpa [Config.getEnv, Env.outcomeConfig] using this
          have h2 : ρ_tgt.factory = ρ_inner_tgt.factory := by
            have := star_preserves_factory P (EvalCmd P) h_body_tgt
            simpa [Config.getEnv, Env.outcomeConfig] using this
          show ρ_inner_tgt.factory = ρ_inner.factory
          rw [← h2, h_fac_eq]; exact h1
        have h_agree_next : StoreAgreement ρ_src_next.store ρ_tgt_next.store :=
          StoreAgreement.of_projectStore_parents h_agree h_off_inner
        have h_src_fresh_next : ∀ t, Q t →
            ρ_src_next.store (HasIdent.ident (P := P) t) = none := by
          intro t h_suf
          show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
          show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
              then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
          by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
          · rw [ite_eq_left hp]; exact h_inner_fresh t h_suf
          · rw [ite_eq_right hp]
        have h_tgt_fresh_next : SemanticStore.isReserved Q σ ρ_tgt_next.store := by
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
        obtain ⟨h_fresh', ρ_out, h_loop_tgt, h_off', h_fail', h_fresh_out⟩ :=
          ih (oc := none) (ρ_src := ρ_src_next) (ρ' := ρ_x) (ρ_tgt := ρ_tgt_next)
            h_fail_eq_next h_fac_eq_next h_agree_next hwf_next
            h_src_fresh_next h_tgt_fresh_next h_tgt_init_undef_next h_loop_T_T hlen_tail
        simp only [Env.outcomeConfig] at h_loop_tgt
        refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_fresh_out⟩
        refine .step _ _ _ (StepStmt.step_loop_enter
          h_cond_t) ?_
        have h_body_tgt' : StepStmtStar P (EvalCmd P)
            (.stmts body' ρ_tgt)
            (.terminal ρ_inner_tgt) := by
          simpa only [Env.outcomeConfig] using h_body_tgt
        refine ReflTrans_Transitive _ _ _ _
          (ReflTrans_Transitive _ _ _ _
            (seq_inner_star P (EvalCmd P) _ _ _ (h_block_tgt_to ρ_inner_tgt h_body_tgt'))
            (.step _ _ _ StepStmt.step_seq_done (.refl _)))
          (ReflTrans_Transitive _ _ _ _
            (stmts_cons_step P (EvalCmd P) _ _ ρ_tgt_next ρ_out h_loop_tgt)
            (.step _ _ _ StepStmt.step_stmts_nil (.refl _)))
      | some lbl =>
        simp only [Env.outcomeConfig] at hrest ⊢
        have hl : hrest.len < hstarT.len := hl
        rcases seqT_reaches_exiting hrest with
          ⟨h_block_exit, hlen_be⟩ | ⟨ρ_block, h_block_term, h_loop_exit, hlen_te⟩
        · have ⟨ρ_inner, h_inner_exit, heq_ρ', hlen_inner⟩ :=
            blockT_none_reaches_exiting h_block_exit
          have h_body_run : StepStmtStar P (EvalCmd P)
              (.stmts body ρ_src) (Env.outcomeConfig (some lbl) ρ_inner) :=
            reflTransT_to_prop h_inner_exit
          obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner, h_fresh_inner⟩ :=
            h_body_sim (some lbl) ρ_src ρ_inner ρ_tgt h_fail_eq h_fac_eq h_agree hwf
              h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef h_body_run
          subst heq_ρ'
          refine ⟨?_, ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store } : Env P),
            ?_, ?_, ?_, ?_⟩
          · intro t h_suf
            show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
            show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
                then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
            by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
            · rw [ite_eq_left hp]; exact h_inner_fresh t h_suf
            · rw [ite_eq_right hp]
          · refine .step _ _ _ (StepStmt.step_loop_enter
              h_cond_t) ?_
            have h_body_tgt' : StepStmtStar P (EvalCmd P)
                (.stmts body' ρ_tgt)
                (.exiting lbl ρ_inner_tgt) := by
              simpa only [Env.outcomeConfig] using h_body_tgt
            have h_block_tgt_exit : StepStmtStar P (EvalCmd P)
                (.block .none ρ_tgt.store (.stmts body' ρ_tgt))
                (.exiting lbl ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store } : Env P)) := by
              refine ReflTrans_Transitive _ _ _ _
                (block_inner_star P (EvalCmd P) _ _ .none ρ_tgt.store h_body_tgt') ?_
              exact .step _ _ _ (StepStmt.step_block_exit_mismatch (by simp)) (.refl _)
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) _ _ _ h_block_tgt_exit) ?_
            exact .step _ _ _ StepStmt.step_seq_exit (.refl _)
          · exact StoreAgreement.of_projectStore_parents h_agree h_off_inner
          · exact h_fail_inner
          · intro s h_suf h_notin
            show projectStore ρ_tgt.store ρ_inner_tgt.store (HasIdent.ident (P := P) s) = none
            show (if (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
                then ρ_inner_tgt.store (HasIdent.ident (P := P) s) else none) = none
            rw [h_tgt_fresh s h_suf h_notin]; rfl
        · have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
            blockT_none_reaches_terminal h_block_term
          have ⟨h_loop_T_exit, hlen_cons⟩ :=
            stmtsT_singleton_exiting h_loop_exit
          have h_body_run : StepStmtStar P (EvalCmd P)
              (.stmts body ρ_src) (Env.outcomeConfig none ρ_inner) :=
            reflTransT_to_prop h_inner_term
          obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner, h_fresh_inner⟩ :=
            h_body_sim none ρ_src ρ_inner ρ_tgt h_fail_eq h_fac_eq h_agree hwf
              h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef h_body_run
          have heq_ρ_block_full :
              ρ_block = ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P) := by
            rw [heq_ρ_block]
          subst heq_ρ_block_full
          let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store }
          let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store }
          have hwf_next : WellFormedSemanticEval ρ_src_next.factory := by
            show WellFormedSemanticEval ρ_inner.factory
            have h1 : ρ_src.factory = ρ_inner.factory := by
              have := star_preserves_factory P (EvalCmd P) h_body_run
              simpa [Config.getEnv, Env.outcomeConfig] using this
            rw [← h1]; exact hwf
          have h_fail_eq_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
            show ρ_inner_tgt.hasFailure = ρ_inner.hasFailure; exact h_fail_inner
          have h_fac_eq_next : ρ_tgt_next.factory = ρ_src_next.factory := by
            have h1 : ρ_src.factory = ρ_inner.factory := by
              have := star_preserves_factory P (EvalCmd P) h_body_run
              simpa [Config.getEnv, Env.outcomeConfig] using this
            have h2 : ρ_tgt.factory = ρ_inner_tgt.factory := by
              have := star_preserves_factory P (EvalCmd P) h_body_tgt
              simpa [Config.getEnv, Env.outcomeConfig] using this
            show ρ_inner_tgt.factory = ρ_inner.factory
            rw [← h2, h_fac_eq]; exact h1
          have h_agree_next : StoreAgreement ρ_src_next.store ρ_tgt_next.store :=
            StoreAgreement.of_projectStore_parents h_agree h_off_inner
          have h_src_fresh_next : ∀ t, Q t →
              ρ_src_next.store (HasIdent.ident (P := P) t) = none := by
            intro t h_suf
            show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
            show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
                then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
            by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
            · rw [ite_eq_left hp]; exact h_inner_fresh t h_suf
            · rw [ite_eq_right hp]
          have h_tgt_fresh_next : SemanticStore.isReserved Q σ ρ_tgt_next.store := by
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
          obtain ⟨h_fresh', ρ_out, h_loop_tgt, h_off', h_fail', h_fresh_out⟩ :=
            ih (oc := some lbl) (ρ_src := ρ_src_next) (ρ' := ρ') (ρ_tgt := ρ_tgt_next)
              h_fail_eq_next h_fac_eq_next h_agree_next hwf_next
              h_src_fresh_next h_tgt_fresh_next h_tgt_init_undef_next h_loop_T_exit hlen_tail
          simp only [Env.outcomeConfig] at h_loop_tgt
          refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_fresh_out⟩
          refine .step _ _ _ (StepStmt.step_loop_enter
            h_cond_t) ?_
          have h_body_tgt' : StepStmtStar P (EvalCmd P)
              (.stmts body' ρ_tgt)
              (.terminal ρ_inner_tgt) := by
            simpa only [Env.outcomeConfig] using h_body_tgt
          have h_loop_stmts_exit : StepStmtStar P (EvalCmd P)
              (.stmts [.loop (.det e) m inv body' md] ρ_tgt_next)
              (.exiting lbl ρ_out) := by
            refine .step _ _ _ StepStmt.step_stmts_cons ?_
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) _ _ _ h_loop_tgt) ?_
            exact .step _ _ _ StepStmt.step_seq_exit (.refl _)
          refine ReflTrans_Transitive _ _ _ _
            (ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) _ _ _ (h_block_tgt_to ρ_inner_tgt h_body_tgt'))
              (.step _ _ _ StepStmt.step_seq_done (.refl _)))
            h_loop_stmts_exit

/-- When the rewritten loop's fresh guard is already `ff`, a terminating source
run of the loop is matched by the target det-loop taking its exit branch
immediately: the resulting stores still agree and every `Q`-name stays fresh.
(The nondet-loop EXIT case; used by both fuel cases of the iteration lemma.) -/
private theorem loop_nondet_exit_close_sa {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (ident : P.Ident) (m : Option P.Expr) {inv : List (String × P.Expr)}
    (body' : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ : StringGenState)
    (oc : Option String)
    (ρ_src ρ' ρ_tgt : Env P)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_fac_eq : ρ_tgt.factory = ρ_src.factory)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : SemanticStore.isReserved Q σ ρ_tgt.store)
    (h_guard_def : ρ_tgt.store ident = some HasBool.ff)
    (hrest : ReflTransT (StepStmt P (EvalCmd P))
      (.terminal ρ_src)
      (Env.outcomeConfig oc ρ')) :
    (∀ t, Q t →
        ρ'.store (HasIdent.ident (P := P) t) = none)
      ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P)
          (.stmt (.loop (.det (HasFvar.mkTypedFvar ident HasBool.boolTy)) m inv
            (body' ++ [.cmd (HasHavoc.havoc ident md)]) md) ρ_tgt)
          (Env.outcomeConfig oc ρ_out)
        ∧ StoreAgreement ρ'.store ρ_out.store
        ∧ ρ_out.hasFailure = ρ'.hasFailure
        ∧ SemanticStore.isReserved Q σ ρ_out.store := by
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
    have h_guard_ff : P.eval ρ_tgt.factory ρ_tgt.store (HasFvar.mkTypedFvar ident HasBool.boolTy) = some HasBool.ff := by
      rw [h_fac_eq]
      exact eval_mkTypedFvar_of_value ρ_src.factory ρ_tgt.store ident HasBool.ff
        (HasBool.boolIsVal ρ_src.factory).2 h_guard_def hwf.var hwf.mono
    subst hρ'_eq
    refine ⟨h_src_fresh, ρ_tgt, ?_, ?_, ?_, ?_⟩
    · exact .step _ _ _ (StepStmt.step_loop_exit
        h_guard_ff) (.refl _)
    · exact h_agree
    · exact h_fail_eq
    · exact h_tgt_fresh

/-- Nondeterministic-loop iteration (fuel-bounded induction on the source run). -/
private theorem nondetElim_loop_nondet_sim_iteration_sa {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (g : String) (m : Option P.Expr) {inv : List (String × P.Expr)}
    (body body' : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ σ_out : StringGenState)
    (h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
      ρb_tgt.hasFailure = ρb_src.hasFailure →
      ρb_tgt.factory = ρb_src.factory →
      StoreAgreement ρb_src.store ρb_tgt.store →
      WellFormedSemanticEval ρb_src.factory →
      StringGenState.WF σ →
      (∀ t, Q t →
        ρb_src.store (HasIdent.ident (P := P) t) = none) →
      SemanticStore.isReserved Q σ ρb_tgt.store →
      (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
      StepStmtStar P (EvalCmd P) (.stmts body ρb_src) (Env.outcomeConfig oc_b ρb') →
      (∀ t, Q t →
          ρb'.store (HasIdent.ident (P := P) t) = none)
        ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P)
            (.stmts body' ρb_tgt) (Env.outcomeConfig oc_b ρb_out)
          ∧ StoreAgreement ρb'.store ρb_out.store
          ∧ ρb_out.hasFailure = ρb'.hasFailure
          ∧ SemanticStore.isReserved Q σ_out ρb_out.store)
    (h_g_gen : Q g)
    (_h_g_in : g ∈ σ.stringGens)
    (h_g_ndef : HasIdent.ident (P := P) g ∉ Block.definedVars (P := P) (C := Cmd P) body' false)
    (h_g_nmod : HasIdent.ident (P := P) g ∉ Block.modifiedVars (P := P) (C := Cmd P) body')
    (oc : Option String)
    (ρ_src ρ' ρ_tgt : Env P) (n : Nat)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_fac_eq : ρ_tgt.factory = ρ_src.factory)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : SemanticStore.isReserved Q σ ρ_tgt.store)
    (h_tgt_init_undef : ∀ y ∈ Block.initVars body, ρ_tgt.store y = none)
    (entering : Bool)
    (h_guard_def : ρ_tgt.store (HasIdent.ident (P := P) g)
      = some (if entering then HasBool.tt else HasBool.ff))
    (h_src_first :
      (entering = false ∧ ∃ (hrest : ReflTransT (StepStmt P (EvalCmd P))
          (.terminal ρ_src)
          (Env.outcomeConfig oc ρ')), hrest.len ≤ n) ∨
      (entering = true ∧ ∃ (hrest : ReflTransT (StepStmt P (EvalCmd P))
          (.seq (.block .none ρ_src.store (.stmts body ρ_src))
            [.loop .nondet m inv body md])
          (Env.outcomeConfig oc ρ')), hrest.len ≤ n)) :
    (∀ t, Q t →
        ρ'.store (HasIdent.ident (P := P) t) = none)
      ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P)
          (.stmt (.loop (.det (HasFvar.mkTypedFvar (HasIdent.ident (P := P) g) HasBool.boolTy)) m
            inv
            (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md) ρ_tgt)
          (Env.outcomeConfig oc ρ_out)
        ∧ StoreAgreement ρ'.store ρ_out.store
        ∧ ρ_out.hasFailure = ρ'.hasFailure
        ∧ SemanticStore.isReserved Q σ ρ_out.store := by
  induction n generalizing oc ρ_src ρ_tgt ρ' entering with
  | zero =>
    rcases h_src_first with ⟨h_ent, hrest, hl⟩ | ⟨h_ent, hrest, hl⟩
    · subst h_ent
      simp only [Bool.false_eq_true, ite_false] at h_guard_def
      exact loop_nondet_exit_close_sa (HasIdent.ident (P := P) g) m body' md σ
        oc ρ_src ρ' ρ_tgt h_fail_eq h_fac_eq h_agree hwf
        h_src_fresh h_tgt_fresh h_guard_def hrest
    · exfalso
      subst h_ent
      cases oc <;> simp only [Env.outcomeConfig] at hrest <;>
        (match hrest with
         | .step _ _ _ _ _ => simp only [ReflTransT.len] at hl; omega)
  | succ n ih =>
    rcases h_src_first with ⟨h_ent, hrest, hl⟩ | ⟨h_ent, hrest, hl⟩
    · subst h_ent
      simp only [Bool.false_eq_true, ite_false] at h_guard_def
      exact loop_nondet_exit_close_sa (HasIdent.ident (P := P) g) m body' md σ
        oc ρ_src ρ' ρ_tgt h_fail_eq h_fac_eq h_agree hwf
        h_src_fresh h_tgt_fresh h_guard_def hrest
    · subst h_ent
      simp only [ite_true] at h_guard_def
      -- Guard reads tt in target (via mkTypedFvar / h_guard_def).
      have h_guard_tt : P.eval ρ_tgt.factory ρ_tgt.store (HasFvar.mkTypedFvar (HasIdent.ident (P := P) g) HasBool.boolTy)
          = some HasBool.tt := by
        rw [h_fac_eq]
        exact eval_mkTypedFvar_of_value ρ_src.factory ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt
          (HasBool.boolIsVal ρ_src.factory).1 h_guard_def hwf.var hwf.mono
      have hwf_var_t : WellFormedSemanticEvalVar ρ_src.factory := hwf.var
      cases oc with
      | none =>
        simp only [Env.outcomeConfig] at hrest ⊢
        have hl : hrest.len ≤ n + 1 := hl
        have ⟨ρ_block, h_block_term, h_loop_stmts, hlen_seq⟩ :=
          seqT_reaches_terminal hrest
        have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
          blockT_none_reaches_terminal h_block_term
        have ⟨ρ_x, h_loop_T_T, h_nil, hlen_cons⟩ :=
          stmtsT_cons_terminal h_loop_stmts
        have hρ_x_eq : ρ_x = ρ' := by
          match h_nil with
          | .step _ _ _ .step_stmts_nil hr2 =>
            match hr2 with
            | .refl _ => rfl
            | .step _ _ _ h _ => exact nomatch h
        subst hρ_x_eq
        have h_body_run : StepStmtStar P (EvalCmd P)
            (.stmts body ρ_src) (Env.outcomeConfig none ρ_inner) :=
          reflTransT_to_prop h_inner_term
        obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner, h_fresh_inner⟩ :=
          h_body_sim none ρ_src ρ_inner ρ_tgt h_fail_eq h_fac_eq h_agree hwf
            h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef h_body_run
        have heq_ρ_block_full :
            ρ_block = ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P) := by
          rw [heq_ρ_block]
        subst heq_ρ_block_full
        -- $g stays defined in ρ_inner_tgt (it was defined in ρ_tgt).
        have h_g_some_tgt : (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome = true := by
          rw [h_guard_def]; rfl
        have h_body_tgt_term : StepStmtStar P (EvalCmd P)
            (.stmts body' ρ_tgt)
            (.terminal ρ_inner_tgt) := by
          simpa only [Env.outcomeConfig] using h_body_tgt
        have h_g_some_inner : (ρ_inner_tgt.store (HasIdent.ident (P := P) g)).isSome = true := by
          have := stmts_preserves_isSome h_body_tgt_term
            (y := HasIdent.ident (P := P) g)
          exact this h_g_some_tgt
        obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp h_g_some_inner
        -- Invert the loop tail to learn the NEXT source decision.
        rcases loop_nondet_step_first_inv (oc := none)
            h_loop_T_T with
          ⟨hrest_next, hlen_next⟩ | ⟨hrest_next, hlen_next⟩
        · -- NEXT = EXIT: re-havoc $g := ff.
          have hwf_var_inner : WellFormedSemanticEvalVar ρ_inner_tgt.factory := by
            have h_fac_it : ρ_inner_tgt.factory = ρ_src.factory := by
              have h2 : ρ_tgt.factory = ρ_inner_tgt.factory := by
                have := star_preserves_factory P (EvalCmd P) h_body_tgt_term
                simpa [Config.getEnv, Env.outcomeConfig] using this
              rw [← h2, h_fac_eq]
            rw [h_fac_it]; exact hwf.var
          -- Build the per-iteration block run: body' to ρ_inner_tgt, then havoc $g := ff.
          have h_tail : StepStmtStar P (EvalCmd P)
              (.stmt (.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)) ρ_inner_tgt)
              (.terminal ({ ρ_inner_tgt with store := SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.ff } : Env P)) :=
            step_havoc_set_to (HasIdent.ident (P := P) g) HasBool.ff md ρ_inner_tgt v' hv'
              HasBool.boolTy
              (by
                have h_g_pres : ρ_inner_tgt.store (HasIdent.ident (P := P) g)
                    = ρ_tgt.store (HasIdent.ident (P := P) g) :=
                  block_run_terminal_preserves_eq_of_not_written h_g_ndef h_g_nmod h_body_tgt_term
                have hv'_tt : v' = HasBool.tt :=
                  Option.some.inj (hv'.symm.trans (h_g_pres.trans h_guard_def))
                rw [hv'_tt]; exact (HasBool.boolIsValOfTy ρ_inner_tgt.factory).1)
              (HasBool.boolIsValOfTy ρ_inner_tgt.factory).2 hwf_var_inner
          have h_body_tail : StepStmtStar P (EvalCmd P)
              (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt)
              (.terminal ({ ρ_inner_tgt with store := SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.ff } : Env P)) :=
            ReflTrans_Transitive _ _ _ _
              (stmts_prefix_terminal_append P (EvalCmd P) _ _ _ ρ_inner_tgt h_body_tgt_term)
              (stmt_to_singleton_stmts _ ρ_inner_tgt _ h_tail)
          let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store (SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) }
          let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store }
          -- $g slot in ρ_tgt_next.
          have h_guard_next : ρ_tgt_next.store (HasIdent.ident (P := P) g) = some HasBool.ff := by
            show (if (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome
                then SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.ff
                  (HasIdent.ident (P := P) g) else none) = some HasBool.ff
            rw [ite_eq_left h_g_some_tgt]; simp [SemanticStore.update]
          -- WF facts and agreements at the projected envs.
          have hwf_next : WellFormedSemanticEval ρ_src_next.factory := by
            show WellFormedSemanticEval ρ_inner.factory
            have h1 : ρ_src.factory = ρ_inner.factory := by
              have := star_preserves_factory P (EvalCmd P) h_body_run
              simpa [Config.getEnv, Env.outcomeConfig] using this
            rw [← h1]; exact hwf
          have h_fac_eq_next : ρ_tgt_next.factory = ρ_src_next.factory := by
            show ρ_inner_tgt.factory = ρ_inner.factory
            have h1 : ρ_src.factory = ρ_inner.factory := by
              have := star_preserves_factory P (EvalCmd P) h_body_run
              simpa [Config.getEnv, Env.outcomeConfig] using this
            have h2 : ρ_tgt.factory = ρ_inner_tgt.factory := by
              have := star_preserves_factory P (EvalCmd P) h_body_tgt
              simpa [Config.getEnv, Env.outcomeConfig] using this
            rw [← h2, h_fac_eq]; exact h1
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
            · rw [ite_eq_left hp]; exact h_inner_fresh t h_suf
            · rw [ite_eq_right hp]
          have h_tgt_fresh_next : SemanticStore.isReserved Q σ ρ_tgt_next.store := by
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
          obtain ⟨h_fresh', ρ_out, h_loop_tgt, h_off', h_fail', h_fresh_out⟩ :=
            ih (oc := none) (ρ_src := ρ_src_next) (ρ' := ρ_x) (ρ_tgt := ρ_tgt_next)
              h_fail_eq_next h_fac_eq_next h_agree_next hwf_next
              h_src_fresh_next h_tgt_fresh_next h_tgt_init_undef_next false h_guard_next
              (.inl ⟨rfl, hrest_next, hlen_tail⟩)
          simp only [Env.outcomeConfig] at h_loop_tgt
          refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_fresh_out⟩
          -- Assemble: enter (guard tt), block runs body'++[havoc], step_seq_done, recurse.
          refine .step _ _ _ (StepStmt.step_loop_enter
            h_guard_tt) ?_
          have h_block_run : StepStmtStar P (EvalCmd P)
              (.block .none ρ_tgt.store (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt))
              (.terminal ρ_tgt_next) := by
            refine ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) _ _ .none ρ_tgt.store h_body_tail) ?_
            exact .step _ _ _ StepStmt.step_block_done (.refl _)
          refine ReflTrans_Transitive _ _ _ _
            (ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) _ _ _ h_block_run)
              (.step _ _ _ StepStmt.step_seq_done (.refl _)))
            (ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P (EvalCmd P) _ _ ρ_tgt_next ρ_out h_loop_tgt)
              (.step _ _ _ StepStmt.step_stmts_nil (.refl _)))
        · -- NEXT = ENTER: re-havoc $g := tt.
          have hwf_var_inner : WellFormedSemanticEvalVar ρ_inner_tgt.factory := by
            have h_fac_it : ρ_inner_tgt.factory = ρ_src.factory := by
              have h2 : ρ_tgt.factory = ρ_inner_tgt.factory := by
                have := star_preserves_factory P (EvalCmd P) h_body_tgt_term
                simpa [Config.getEnv, Env.outcomeConfig] using this
              rw [← h2, h_fac_eq]
            rw [h_fac_it]; exact hwf.var
          have h_tail : StepStmtStar P (EvalCmd P)
              (.stmt (.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)) ρ_inner_tgt)
              (.terminal ({ ρ_inner_tgt with store := SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P)) :=
            step_havoc_set_to (HasIdent.ident (P := P) g) HasBool.tt md ρ_inner_tgt v' hv'
              HasBool.boolTy
              (by
                have h_g_pres : ρ_inner_tgt.store (HasIdent.ident (P := P) g)
                    = ρ_tgt.store (HasIdent.ident (P := P) g) :=
                  block_run_terminal_preserves_eq_of_not_written h_g_ndef h_g_nmod h_body_tgt_term
                have hv'_tt : v' = HasBool.tt :=
                  Option.some.inj (hv'.symm.trans (h_g_pres.trans h_guard_def))
                rw [hv'_tt]; exact (HasBool.boolIsValOfTy ρ_inner_tgt.factory).1)
              (HasBool.boolIsValOfTy ρ_inner_tgt.factory).1 hwf_var_inner
          have h_body_tail : StepStmtStar P (EvalCmd P)
              (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt)
              (.terminal ({ ρ_inner_tgt with store := SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P)) :=
            ReflTrans_Transitive _ _ _ _
              (stmts_prefix_terminal_append P (EvalCmd P) _ _ _ ρ_inner_tgt h_body_tgt_term)
              (stmt_to_singleton_stmts _ ρ_inner_tgt _ h_tail)
          let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store (SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) }
          let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store }
          have h_guard_next : ρ_tgt_next.store (HasIdent.ident (P := P) g) = some HasBool.tt := by
            show (if (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome
                then SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt
                  (HasIdent.ident (P := P) g) else none) = some HasBool.tt
            rw [ite_eq_left h_g_some_tgt]; simp [SemanticStore.update]
          have hwf_next : WellFormedSemanticEval ρ_src_next.factory := by
            show WellFormedSemanticEval ρ_inner.factory
            have h1 : ρ_src.factory = ρ_inner.factory := by
              have := star_preserves_factory P (EvalCmd P) h_body_run
              simpa [Config.getEnv, Env.outcomeConfig] using this
            rw [← h1]; exact hwf
          have h_fac_eq_next : ρ_tgt_next.factory = ρ_src_next.factory := by
            show ρ_inner_tgt.factory = ρ_inner.factory
            have h1 : ρ_src.factory = ρ_inner.factory := by
              have := star_preserves_factory P (EvalCmd P) h_body_run
              simpa [Config.getEnv, Env.outcomeConfig] using this
            have h2 : ρ_tgt.factory = ρ_inner_tgt.factory := by
              have := star_preserves_factory P (EvalCmd P) h_body_tgt
              simpa [Config.getEnv, Env.outcomeConfig] using this
            rw [← h2, h_fac_eq]; exact h1
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
            · rw [ite_eq_left hp]; exact h_inner_fresh t h_suf
            · rw [ite_eq_right hp]
          have h_tgt_fresh_next : SemanticStore.isReserved Q σ ρ_tgt_next.store := by
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
          obtain ⟨h_fresh', ρ_out, h_loop_tgt, h_off', h_fail', h_fresh_out⟩ :=
            ih (oc := none) (ρ_src := ρ_src_next) (ρ' := ρ_x) (ρ_tgt := ρ_tgt_next)
              h_fail_eq_next h_fac_eq_next h_agree_next hwf_next
              h_src_fresh_next h_tgt_fresh_next h_tgt_init_undef_next true h_guard_next
              (.inr ⟨rfl, hrest_next, hlen_tail⟩)
          simp only [Env.outcomeConfig] at h_loop_tgt
          refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_fresh_out⟩
          refine .step _ _ _ (StepStmt.step_loop_enter
            h_guard_tt) ?_
          have h_block_run : StepStmtStar P (EvalCmd P)
              (.block .none ρ_tgt.store (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt))
              (.terminal ρ_tgt_next) := by
            refine ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) _ _ .none ρ_tgt.store h_body_tail) ?_
            exact .step _ _ _ StepStmt.step_block_done (.refl _)
          refine ReflTrans_Transitive _ _ _ _
            (ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) _ _ _ h_block_run)
              (.step _ _ _ StepStmt.step_seq_done (.refl _)))
            (ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P (EvalCmd P) _ _ ρ_tgt_next ρ_out h_loop_tgt)
              (.step _ _ _ StepStmt.step_stmts_nil (.refl _)))
      | some lbl =>
        simp only [Env.outcomeConfig] at hrest ⊢
        have hl : hrest.len ≤ n + 1 := hl
        rcases seqT_reaches_exiting hrest with
          ⟨h_block_exit, hlen_be⟩ | ⟨ρ_block, h_block_term, h_loop_exit, hlen_te⟩
        · -- Body-block exits with lbl: the body exits, propagated past the loop.
          have ⟨ρ_inner, h_inner_exit, heq_ρ', hlen_inner⟩ :=
            blockT_none_reaches_exiting h_block_exit
          have h_body_run : StepStmtStar P (EvalCmd P)
              (.stmts body ρ_src) (Env.outcomeConfig (some lbl) ρ_inner) :=
            reflTransT_to_prop h_inner_exit
          obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner, h_fresh_inner⟩ :=
            h_body_sim (some lbl) ρ_src ρ_inner ρ_tgt h_fail_eq h_fac_eq h_agree hwf
              h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef h_body_run
          subst heq_ρ'
          refine ⟨?_, ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store } : Env P),
            ?_, ?_, ?_, ?_⟩
          · intro t h_suf
            show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
                then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
            by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
            · rw [ite_eq_left hp]; exact h_inner_fresh t h_suf
            · rw [ite_eq_right hp]
          · -- Target: enter (guard tt), body' exits lbl inside the block; the
            -- trailing havoc is skipped (the body' exit propagates), block
            -- mismatch (.none), seq exit skips the loop tail.
            refine .step _ _ _ (StepStmt.step_loop_enter
              h_guard_tt) ?_
            have h_body_tgt' : StepStmtStar P (EvalCmd P)
                (.stmts body' ρ_tgt)
                (.exiting lbl ρ_inner_tgt) := by
              simpa only [Env.outcomeConfig] using h_body_tgt
            -- body' ++ [havoc] exits lbl (the prefix exits, suffix skipped).
            have h_body_tail_exit : StepStmtStar P (EvalCmd P)
                (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                  ρ_tgt)
                (.exiting lbl ρ_inner_tgt) :=
              stmts_cons_head_exiting_append _ _ _ ρ_inner_tgt lbl h_body_tgt'
            have h_block_tgt_exit : StepStmtStar P (EvalCmd P)
                (.block .none ρ_tgt.store (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                  ρ_tgt))
                (.exiting lbl ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store } : Env P)) := by
              refine ReflTrans_Transitive _ _ _ _
                (block_inner_star P (EvalCmd P) _ _ .none ρ_tgt.store h_body_tail_exit) ?_
              exact .step _ _ _ (StepStmt.step_block_exit_mismatch (by simp)) (.refl _)
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) _ _ _ h_block_tgt_exit) ?_
            exact .step _ _ _ StepStmt.step_seq_exit (.refl _)
          · exact StoreAgreement.of_projectStore_parents h_agree h_off_inner
          · exact h_fail_inner
          · intro s h_suf h_notin
            show (if (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
                then ρ_inner_tgt.store (HasIdent.ident (P := P) s) else none) = none
            rw [h_tgt_fresh s h_suf h_notin]; rfl
        · -- Body terminates, loop tail exits with lbl: recurse on the tail.
          have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
            blockT_none_reaches_terminal h_block_term
          have ⟨h_loop_T_exit, hlen_cons⟩ :=
            stmtsT_singleton_exiting h_loop_exit
          have h_body_run : StepStmtStar P (EvalCmd P)
              (.stmts body ρ_src) (Env.outcomeConfig none ρ_inner) :=
            reflTransT_to_prop h_inner_term
          obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner, h_fresh_inner⟩ :=
            h_body_sim none ρ_src ρ_inner ρ_tgt h_fail_eq h_fac_eq h_agree hwf
              h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef h_body_run
          have heq_ρ_block_full :
              ρ_block = ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P) := by
            rw [heq_ρ_block]
          subst heq_ρ_block_full
          have h_g_some_tgt : (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome = true := by
            rw [h_guard_def]; rfl
          have h_body_tgt_term : StepStmtStar P (EvalCmd P)
              (.stmts body' ρ_tgt)
              (.terminal ρ_inner_tgt) := by
            simpa only [Env.outcomeConfig] using h_body_tgt
          have h_g_some_inner : (ρ_inner_tgt.store (HasIdent.ident (P := P) g)).isSome = true :=
            stmts_preserves_isSome h_body_tgt_term (y := HasIdent.ident (P := P) g)
              h_g_some_tgt
          obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp h_g_some_inner
          have hwf_var_inner : WellFormedSemanticEvalVar ρ_inner_tgt.factory := by
            have h_fac_it : ρ_inner_tgt.factory = ρ_src.factory := by
              have h2 : ρ_tgt.factory = ρ_inner_tgt.factory := by
                have := star_preserves_factory P (EvalCmd P) h_body_tgt_term
                simpa [Config.getEnv, Env.outcomeConfig] using this
              rw [← h2, h_fac_eq]
            rw [h_fac_it]; exact hwf.var
          let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store }
          -- Invert the loop tail (exiting lbl) to learn the next decision.  EXIT
          -- is impossible (`.terminal _ →* .exiting lbl`), so the next is ENTER:
          -- re-havoc $g := tt and recurse with entering = true.
          have hrest_enter :
              ∃ (hr : ReflTransT (StepStmt P (EvalCmd P))
                (.seq (.block .none ρ_src_next.store (.stmts body ρ_src_next))
                  [.loop .nondet m inv body md])
                (Env.outcomeConfig (some lbl) ρ')), hr.len ≤ n := by
            rcases loop_nondet_step_first_inv (oc := some lbl)
                h_loop_T_exit with
              ⟨hrest_next, _⟩ | ⟨hrest_next, hlen_next⟩
            · exfalso
              simp only [Env.outcomeConfig] at hrest_next
              match hrest_next with
              | .step _ _ _ h _ => exact nomatch h
            · have h_bound : h_loop_T_exit.len ≤ n := by omega
              exact ⟨hrest_next, Nat.le_of_lt (Nat.lt_of_lt_of_le hlen_next h_bound)⟩
          obtain ⟨hrest_next, hlen_tail⟩ := hrest_enter
          have h_tail : StepStmtStar P (EvalCmd P)
              (.stmt (.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)) ρ_inner_tgt)
              (.terminal ({ ρ_inner_tgt with store := SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P)) :=
            step_havoc_set_to (HasIdent.ident (P := P) g) HasBool.tt md ρ_inner_tgt v' hv'
              HasBool.boolTy
              (by
                have h_g_pres : ρ_inner_tgt.store (HasIdent.ident (P := P) g)
                    = ρ_tgt.store (HasIdent.ident (P := P) g) :=
                  block_run_terminal_preserves_eq_of_not_written h_g_ndef h_g_nmod h_body_tgt_term
                have hv'_tt : v' = HasBool.tt :=
                  Option.some.inj (hv'.symm.trans (h_g_pres.trans h_guard_def))
                rw [hv'_tt]; exact (HasBool.boolIsValOfTy ρ_inner_tgt.factory).1)
              (HasBool.boolIsValOfTy ρ_inner_tgt.factory).1 hwf_var_inner
          have h_body_tail : StepStmtStar P (EvalCmd P)
              (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt)
              (.terminal ({ ρ_inner_tgt with store := SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P)) :=
            ReflTrans_Transitive _ _ _ _
              (stmts_prefix_terminal_append P (EvalCmd P) _ _ _ ρ_inner_tgt h_body_tgt_term)
              (stmt_to_singleton_stmts _ ρ_inner_tgt _ h_tail)
          let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store (SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) }
          have h_guard_next : ρ_tgt_next.store (HasIdent.ident (P := P) g) = some HasBool.tt := by
            show (if (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome
                then SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt
                  (HasIdent.ident (P := P) g) else none) = some HasBool.tt
            rw [ite_eq_left h_g_some_tgt]; simp [SemanticStore.update]
          have hwf_next : WellFormedSemanticEval ρ_src_next.factory := by
            show WellFormedSemanticEval ρ_inner.factory
            have h1 : ρ_src.factory = ρ_inner.factory := by
              have := star_preserves_factory P (EvalCmd P) h_body_run
              simpa [Config.getEnv, Env.outcomeConfig] using this
            rw [← h1]; exact hwf
          have h_fac_eq_next : ρ_tgt_next.factory = ρ_src_next.factory := by
            show ρ_inner_tgt.factory = ρ_inner.factory
            have h1 : ρ_src.factory = ρ_inner.factory := by
              have := star_preserves_factory P (EvalCmd P) h_body_run
              simpa [Config.getEnv, Env.outcomeConfig] using this
            have h2 : ρ_tgt.factory = ρ_inner_tgt.factory := by
              have := star_preserves_factory P (EvalCmd P) h_body_tgt
              simpa [Config.getEnv, Env.outcomeConfig] using this
            rw [← h2, h_fac_eq]; exact h1
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
            · rw [ite_eq_left hp]; exact h_inner_fresh t h_suf
            · rw [ite_eq_right hp]
          have h_tgt_fresh_next : SemanticStore.isReserved Q σ ρ_tgt_next.store := by
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
          obtain ⟨h_fresh', ρ_out, h_loop_tgt, h_off', h_fail', h_fresh_out⟩ :=
            ih (oc := some lbl) (ρ_src := ρ_src_next) (ρ' := ρ') (ρ_tgt := ρ_tgt_next)
              h_fail_eq_next h_fac_eq_next h_agree_next hwf_next
              h_src_fresh_next h_tgt_fresh_next h_tgt_init_undef_next true h_guard_next
              (.inr ⟨rfl, hrest_next, hlen_tail⟩)
          simp only [Env.outcomeConfig] at h_loop_tgt
          refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_fresh_out⟩
          refine .step _ _ _ (StepStmt.step_loop_enter
            h_guard_tt) ?_
          have h_block_run : StepStmtStar P (EvalCmd P)
              (.block .none ρ_tgt.store (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt))
              (.terminal ρ_tgt_next) := by
            refine ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) _ _ .none ρ_tgt.store h_body_tail) ?_
            exact .step _ _ _ StepStmt.step_block_done (.refl _)
          have h_loop_stmts_exit : StepStmtStar P (EvalCmd P)
              (.stmts [.loop (.det (HasFvar.mkTypedFvar (HasIdent.ident (P := P) g) HasBool.boolTy)) m
                inv
                (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md] ρ_tgt_next)
              (.exiting lbl ρ_out) := by
            refine .step _ _ _ StepStmt.step_stmts_cons ?_
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) _ _ _ h_loop_tgt) ?_
            exact .step _ _ _ StepStmt.step_seq_exit (.refl _)
          refine ReflTrans_Transitive _ _ _ _
            (ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) _ _ _ h_block_run)
              (.step _ _ _ StepStmt.step_seq_done (.refl _)))
            h_loop_stmts_exit
/-! ### `initVars` classification of the `nondetElim` output

Every init target of the rewritten output is either an original source init
target or a freshly-generated `Q`-guard (the `.ite .nondet`/`.loop .nondet` arms
emit `init $g := *` for a `Q`-kind `g`).  This is the `Q`-generic analogue of the
`NondetElim.isGeneratedName`-keyed `nondetElimM_initVars_classified` below (proved here so the
cons-arm tail premise can be re-established without a forward import). -/

section InitVarsClassified

mutual
private theorem Stmt.nondetElimM_initVars_classified_Q {P : PureExpr}
    [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen NondetElim.prefixIte sg).1)
            ∧ (∀ sg, Q (StringGenState.gen NondetElim.prefixLoop sg).1))
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
      · exact Or.inr ⟨(StringGenState.gen NondetElim.prefixIte σ).1, h_g, hQgen.1 σ⟩
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
      · exact Or.inr ⟨(StringGenState.gen NondetElim.prefixLoop σ).1, h_g, hQgen.2 σ⟩
      · rcases Block.nondetElimM_initVars_classified_Q hQgen body _ x h_body with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
  | .exit lbl md =>
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
    (hQgen : (∀ sg, Q (StringGenState.gen NondetElim.prefixIte sg).1)
            ∧ (∀ sg, Q (StringGenState.gen NondetElim.prefixLoop sg).1))
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

/-! ### Generation-freshness of the `nondetElim` output write-set

Refinement of the `initVars`/`modVars` classification: every variable the
rewritten output writes is either an original source write, or a string the pass
generated *freshly* w.r.t. the input generator state `σ` (`∉ σ.stringGens`).
Threads `WF σ`; each recursive sub-block's freshness (w.r.t. its advanced input
state) is lifted back to freshness w.r.t. `σ` by `GenStep.subset`, and each
freshly generated guard `(gen pf σ).1` is `∉ σ.stringGens` by
`StringGenState.stringGens_gen_not_in`.  Together these show a guard already
generated by `σ` (`g ∈ σ.stringGens`) is never written by a block the pass
produced from `σ` — the frame precondition for guard-value preservation. -/

section WriteVarsFresh

mutual
/-- With a well-formed generator state, every init-variable in a rewritten
statement comes from the source statement or has a name fresh for that state. -/
private theorem Stmt.nondetElimM_initVars_fresh {P : PureExpr}
    [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) (hwf : StringGenState.WF σ) :
    ∀ x ∈ Block.initVars (P := P) (Stmt.nondetElimM s σ).1,
      x ∈ Stmt.initVars s ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ str ∉ σ.stringGens) := by
  match s with
  | .cmd c =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.definedVars, Stmt.definedVars, List.append_nil] at hx ⊢
      exact Or.inl hx
  | .block lbl bss md =>
      intro x hx
      rw [Stmt.nondetElimM_block_out] at hx
      simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hx ⊢
      exact Block.nondetElimM_initVars_fresh bss σ hwf x hx
  | .ite (.det e) tss ess md =>
      intro x hx
      rw [Stmt.nondetElimM_ite_det_out] at hx
      simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ↓reduceIte,
        List.append_nil, List.mem_append] at hx ⊢
      have hstep : StringGenState.GenStep σ (Block.nondetElimM tss σ).2 := Block.nondetElimM_genStep tss σ
      rcases hx with h | h
      · rcases Block.nondetElimM_initVars_fresh tss σ hwf x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_initVars_fresh ess (Block.nondetElimM tss σ).2 (hstep.wf_mono hwf) x h with h' | ⟨str, heq, hfr⟩
        · exact Or.inl (Or.inr h')
        · exact Or.inr ⟨str, heq, fun hc => hfr (hstep.subset hc)⟩
  | .ite .nondet tss ess md =>
      intro x hx
      rw [Stmt.nondetElimM_ite_nondet_out] at hx
      simp only [HasInit.init, Block.definedVars, Stmt.definedVars, HasVarsImp.definedVars,
        Cmd.definedVars, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append,
        List.nil_append, List.mem_cons, List.mem_append] at hx ⊢
      have hstep0 : StringGenState.GenStep σ (StringGenState.gen NondetElim.prefixIte σ).2 :=
        StringGenState.GenStep.of_gen NondetElim.prefixIte σ
      have hwf1 : StringGenState.WF
          (StringGenState.gen NondetElim.prefixIte σ).2 :=
        hstep0.wf_mono hwf
      have hstep1 : StringGenState.GenStep (StringGenState.gen NondetElim.prefixIte σ).2
          (Block.nondetElimM tss (StringGenState.gen NondetElim.prefixIte σ).2).2 :=
        Block.nondetElimM_genStep tss _
      rcases hx with h_g | h_t | h_e
      · exact Or.inr ⟨(StringGenState.gen NondetElim.prefixIte σ).1, h_g,
          StringGenState.stringGens_gen_not_in NondetElim.prefixIte σ hwf⟩
      · rcases Block.nondetElimM_initVars_fresh tss
          (StringGenState.gen NondetElim.prefixIte σ).2 hwf1 x h_t with
          h' | ⟨str, heq, hfr⟩
        · exact Or.inl (Or.inl h')
        · exact Or.inr ⟨str, heq, fun hc => hfr (hstep0.subset hc)⟩
      · rcases Block.nondetElimM_initVars_fresh ess
          (Block.nondetElimM tss
            (StringGenState.gen NondetElim.prefixIte σ).2).2
          (hstep1.wf_mono hwf1) x h_e with h' | ⟨str, heq, hfr⟩
        · exact Or.inl (Or.inr h')
        · exact Or.inr ⟨str, heq, fun hc => hfr (hstep1.subset (hstep0.subset hc))⟩
  | .loop (.det e) m inv body md =>
      intro x hx
      rw [Stmt.nondetElimM_loop_det_out] at hx
      simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hx ⊢
      exact Block.nondetElimM_initVars_fresh body σ hwf x hx
  | .loop .nondet m inv body md =>
      intro x hx
      rw [Stmt.nondetElimM_loop_nondet_out] at hx
      simp only [HasInit.init, HasHavoc.havoc, Block.definedVars, Stmt.definedVars,
        HasVarsImp.definedVars, Cmd.definedVars, Bool.false_eq_true, ↓reduceIte,
        Block.initVars_append, List.append_nil, List.cons_append, List.nil_append,
        List.mem_cons] at hx ⊢
      have hstep0 : StringGenState.GenStep σ (StringGenState.gen NondetElim.prefixLoop σ).2 :=
        StringGenState.GenStep.of_gen NondetElim.prefixLoop σ
      rcases hx with h_g | h_body
      · exact Or.inr ⟨(StringGenState.gen NondetElim.prefixLoop σ).1, h_g,
          StringGenState.stringGens_gen_not_in NondetElim.prefixLoop σ hwf⟩
      · rcases Block.nondetElimM_initVars_fresh body
          (StringGenState.gen NondetElim.prefixLoop σ).2
          (hstep0.wf_mono hwf) x h_body with h' | ⟨str, heq, hfr⟩
        · exact Or.inl h'
        · exact Or.inr ⟨str, heq, fun hc => hfr (hstep0.subset hc)⟩
  | .exit lbl md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.definedVars, Stmt.definedVars, List.append_nil, List.not_mem_nil] at hx
  | .typeDecl t md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.definedVars, Stmt.definedVars, List.append_nil, List.not_mem_nil] at hx
  termination_by sizeOf s

/-- With a well-formed generator state, every init-variable in a rewritten block
comes from the source block or has a name fresh for that state. -/
private theorem Block.nondetElimM_initVars_fresh {P : PureExpr}
    [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) (hwf : StringGenState.WF σ) :
    ∀ x ∈ Block.initVars (P := P) (Block.nondetElimM ss σ).1,
      x ∈ Block.initVars ss ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ str ∉ σ.stringGens) := by
  match ss with
  | [] =>
      intro x hx
      simp only [Block.nondetElimM, Block.definedVars, List.not_mem_nil] at hx
  | s :: rest =>
      intro x hx
      rw [Block.nondetElimM_cons_out, Block.initVars_append] at hx
      simp only [List.mem_append] at hx
      rw [Block.initVars_cons, List.mem_append]
      have hstep : StringGenState.GenStep σ (Stmt.nondetElimM s σ).2 := Stmt.nondetElimM_genStep s σ
      rcases hx with h | h
      · rcases Stmt.nondetElimM_initVars_fresh s σ hwf x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_initVars_fresh rest (Stmt.nondetElimM s σ).2 (hstep.wf_mono hwf) x h with h' | ⟨str, heq, hfr⟩
        · exact Or.inl (Or.inr h')
        · exact Or.inr ⟨str, heq, fun hc => hfr (hstep.subset hc)⟩
  termination_by sizeOf ss
end

mutual
/-- With a well-formed generator state, every modified variable in a rewritten
statement comes from the source statement or has a name fresh for that state. -/
private theorem Stmt.nondetElimM_modVars_fresh {P : PureExpr}
    [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) (hwf : StringGenState.WF σ) :
    ∀ x ∈ Block.modifiedVars (P := P) (Stmt.nondetElimM s σ).1,
      x ∈ Stmt.modifiedVars s ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ str ∉ σ.stringGens) := by
  match s with
  | .cmd c =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.modifiedVars, List.append_nil] at hx
      exact Or.inl hx
  | .block lbl bss md =>
      intro x hx
      rw [Stmt.nondetElimM_block_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx ⊢
      exact Block.nondetElimM_modVars_fresh bss σ hwf x hx
  | .ite (.det e) tss ess md =>
      intro x hx
      rw [Stmt.nondetElimM_ite_det_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil, List.mem_append] at hx ⊢
      have hstep : StringGenState.GenStep σ (Block.nondetElimM tss σ).2 := Block.nondetElimM_genStep tss σ
      rcases hx with h | h
      · rcases Block.nondetElimM_modVars_fresh tss σ hwf x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_modVars_fresh ess (Block.nondetElimM tss σ).2 (hstep.wf_mono hwf) x h with h' | ⟨str, heq, hfr⟩
        · exact Or.inl (Or.inr h')
        · exact Or.inr ⟨str, heq, fun hc => hfr (hstep.subset hc)⟩
  | .ite .nondet tss ess md =>
      intro x hx
      rw [Stmt.nondetElimM_ite_nondet_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, init_modVars, List.nil_append,
        List.append_nil, List.mem_append] at hx ⊢
      have hstep0 : StringGenState.GenStep σ (StringGenState.gen NondetElim.prefixIte σ).2 :=
        StringGenState.GenStep.of_gen NondetElim.prefixIte σ
      have hwf1 : StringGenState.WF
          (StringGenState.gen NondetElim.prefixIte σ).2 :=
        hstep0.wf_mono hwf
      have hstep1 : StringGenState.GenStep (StringGenState.gen NondetElim.prefixIte σ).2
          (Block.nondetElimM tss (StringGenState.gen NondetElim.prefixIte σ).2).2 :=
        Block.nondetElimM_genStep tss _
      rcases hx with h | h
      · rcases Block.nondetElimM_modVars_fresh tss
          (StringGenState.gen NondetElim.prefixIte σ).2 hwf1 x h with
          h' | ⟨str, heq, hfr⟩
        · exact Or.inl (Or.inl h')
        · exact Or.inr ⟨str, heq, fun hc => hfr (hstep0.subset hc)⟩
      · rcases Block.nondetElimM_modVars_fresh ess
          (Block.nondetElimM tss
            (StringGenState.gen NondetElim.prefixIte σ).2).2
          (hstep1.wf_mono hwf1) x h with h' | ⟨str, heq, hfr⟩
        · exact Or.inl (Or.inr h')
        · exact Or.inr ⟨str, heq, fun hc => hfr (hstep1.subset (hstep0.subset hc))⟩
  | .loop (.det e) m inv body md =>
      intro x hx
      rw [Stmt.nondetElimM_loop_det_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx ⊢
      exact Block.nondetElimM_modVars_fresh body σ hwf x hx
  | .loop .nondet m inv body md =>
      intro x hx
      rw [Stmt.nondetElimM_loop_nondet_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, init_modVars, List.nil_append,
        List.append_nil] at hx ⊢
      rw [Block.modifiedVars_append] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, havoc_modVars, List.append_nil,
        List.mem_append, List.mem_singleton] at hx ⊢
      have hstep0 : StringGenState.GenStep σ (StringGenState.gen NondetElim.prefixLoop σ).2 :=
        StringGenState.GenStep.of_gen NondetElim.prefixLoop σ
      rcases hx with h | h_g
      · rcases Block.nondetElimM_modVars_fresh body
          (StringGenState.gen NondetElim.prefixLoop σ).2
          (hstep0.wf_mono hwf) x h with h' | ⟨str, heq, hfr⟩
        · exact Or.inl h'
        · exact Or.inr ⟨str, heq, fun hc => hfr (hstep0.subset hc)⟩
      · exact Or.inr ⟨(StringGenState.gen NondetElim.prefixLoop σ).1, h_g,
          StringGenState.stringGens_gen_not_in NondetElim.prefixLoop σ hwf⟩
  | .exit lbl md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  | .typeDecl t md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  termination_by sizeOf s

/-- With a well-formed generator state, every modified variable in a rewritten
block comes from the source block or has a name fresh for that state. -/
private theorem Block.nondetElimM_modVars_fresh {P : PureExpr}
    [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) (hwf : StringGenState.WF σ) :
    ∀ x ∈ Block.modifiedVars (P := P) (Block.nondetElimM ss σ).1,
      x ∈ Block.modifiedVars ss ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ str ∉ σ.stringGens) := by
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
      have hstep : StringGenState.GenStep σ (Stmt.nondetElimM s σ).2 := Stmt.nondetElimM_genStep s σ
      rcases hx with h | h
      · rcases Stmt.nondetElimM_modVars_fresh s σ hwf x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_modVars_fresh rest (Stmt.nondetElimM s σ).2 (hstep.wf_mono hwf) x h with h' | ⟨str, heq, hfr⟩
        · exact Or.inl (Or.inr h')
        · exact Or.inr ⟨str, heq, fun hc => hfr (hstep.subset hc)⟩
  termination_by sizeOf ss
end

/-- A `Q`-guard already generated by `σ` (`g ∈ σ.stringGens`) that the *source*
block never writes is not written by the rewritten block either — neither
`init`ed nor modified.  Combines the write-set freshness classifications with
source-write exclusion: a source write is excluded by `h_src`; a generated write
would be fresh (`∉ σ.stringGens`), contradicting `g ∈ σ.stringGens`. -/
private theorem nondetElimM_not_writes_gen {P : PureExpr}
    [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P] [LawfulHasIdent P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) (hwf : StringGenState.WF σ)
    (g : String) (h_g_in : g ∈ σ.stringGens)
    (h_src_def : HasIdent.ident (P := P) g ∉ Block.definedVars (P := P) (C := Cmd P) ss false)
    (h_src_mod : HasIdent.ident (P := P) g ∉ Block.modifiedVars (P := P) (C := Cmd P) ss) :
    HasIdent.ident (P := P) g ∉ Block.definedVars (P := P) (C := Cmd P) (Block.nondetElimM ss σ).1 false
    ∧ HasIdent.ident (P := P) g ∉ Block.modifiedVars (P := P) (C := Cmd P) (Block.nondetElimM ss σ).1 := by
  refine ⟨fun hmem => ?_, fun hmem => ?_⟩
  · rcases Block.nondetElimM_initVars_fresh ss σ hwf _ hmem with h_src | ⟨str, heq, hfr⟩
    · exact h_src_def h_src
    · exact hfr (LawfulHasIdent.ident_inj heq ▸ h_g_in)
  · rcases Block.nondetElimM_modVars_fresh ss σ hwf _ hmem with h_src | ⟨str, heq, hfr⟩
    · exact h_src_mod h_src
    · exact hfr (LawfulHasIdent.ident_inj heq ▸ h_g_in)

end WriteVarsFresh

/-! General forward simulation with **separate** source and target start stores
threading the generator state `σ`.  This is the inductive workhorse: a source
run from `ρ_src` is simulated by the rewritten block from any target store that
agrees with the source (`StoreAgreement`) and matches its evaluator and failure
flag.  The generated guard variables are hidden from the source by the
combination of `StoreAgreement` and `h_src_fresh` below.

Invariants threaded:
- `StoreAgreement ρ_src.store ρ_tgt.store`: wherever the source is defined, the
  target agrees (so a fresh user var stays fresh in the target — the `.cmd`/`init` arm);
- `SemanticStore.isReserved Q σ ρ_tgt.store`: the target store has no *ungenerated* gen-shaped
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
private theorem nondetElim_stmt_gen_sa {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen NondetElim.prefixIte sg).1)
            ∧ (∀ sg, Q (StringGenState.gen NondetElim.prefixLoop sg).1))
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (ρ_src ρ' ρ_tgt : Env P)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_fac_eq : ρ_tgt.factory = ρ_src.factory)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : SemanticStore.isReserved Q σ ρ_tgt.store)
    (h_tgt_init_undef : ∀ y ∈ Stmt.initVars s, ρ_tgt.store y = none)
    (h_unique : (Stmt.initVars s).Nodup)
    (h_no_writes : (∀ t : String, Q t → HasIdent.ident (P := P) t ∉ (Stmt.definedVars s false ++ Stmt.modifiedVars s)))
    (oc : Option String)
    (h_term : StepStmtStar P (EvalCmd P) (.stmt s ρ_src) (Env.outcomeConfig oc ρ')) :
    (∀ t, Q t →
        ρ'.store (HasIdent.ident (P := P) t) = none)
      ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P)
          (.stmts (Stmt.nondetElimM s σ).1 ρ_tgt) (Env.outcomeConfig oc ρ_out)
        ∧ StoreAgreement ρ'.store ρ_out.store
        ∧ ρ_out.hasFailure = ρ'.hasFailure
        ∧ SemanticStore.isReserved Q (Stmt.nondetElimM s σ).2 ρ_out.store := by
  match s, h_no_writes, h_tgt_init_undef, h_unique, oc, h_term with
  | .cmd c, h_no_writes, h_tgt_init_undef, _, oc, h_term =>
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
    obtain ⟨σ', haf, h_cmd, h_eq⟩ := cmd_step_inv c ρ_src ρ' h_term
    have h_src'_fresh : ∀ t, Q t →
        ρ'.store (HasIdent.ident (P := P) t) = none := by
      subst h_eq
      exact evalCmd_preserves_src_fresh h_cmd h_src_fresh h_no_writes_c
    obtain ⟨ρ_tgt', h_run, h_agree', h_fail'⟩ :=
      cmd_replay_agreement_storeAgree c ρ_src ρ' ρ_tgt
        h_fail_eq h_fac_eq h_agree hwf.mono h_tgt_init_undef_c h_term
    -- Invert the target replay run to recover the target's `EvalCmd`, which drives
    -- the SemanticStore.isReserved preservation step (the target writes no gen-shaped var).
    obtain ⟨σ_tgt', haf_t, h_cmd_tgt, h_eq_tgt⟩ :=
      cmd_step_inv c ρ_tgt ρ_tgt' h_run
    refine ⟨h_src'_fresh, ρ_tgt', ?_, h_agree', h_fail', ?_⟩
    · simp only [Stmt.nondetElimM, Env.outcomeConfig]
      exact stmt_to_singleton_stmts (.cmd c) ρ_tgt ρ_tgt' h_run
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
        stmt_step_first_inv_to _ ρ_src (Env.outcomeConfig (some lbl) ρ')
          (by intro ρ'' h; simp only [Env.outcomeConfig] at h <;> cases h) h_term
      cases hstep with
      | step_cmd _ =>
        cases hrest with
        | step _ _ _ h _ => cases h
  | .block lbl bss md, h_no_writes, h_tgt_init_undef, h_unique, oc, h_term =>
    obtain ⟨c, hstep, hrest⟩ :=
      stmt_step_first_inv_to _ ρ_src (Env.outcomeConfig oc ρ')
        (by intro ρ'' h; cases oc <;> simp only [Env.outcomeConfig] at h <;> cases h) h_term
    cases hstep with
    | step_block =>
      have h_dv : Stmt.definedVars (P := P) (.block lbl bss md) false = Block.definedVars bss false := by
        simp only [Stmt.definedVars, Bool.false_eq_true, ite_false]
      have h_mv : Stmt.modifiedVars (P := P) (.block lbl bss md) = Block.modifiedVars bss := by
        with_unfolding_all rfl
      have h_no_writes_bss : SrcNoGenWrites (P := P) Q bss := by
        show (∀ s : String, Q s → HasIdent.ident (P := P) s ∉ (Block.definedVars bss false ++ Block.modifiedVars bss))
        rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
      -- `Stmt.initVars (.block lbl bss md) = Block.initVars bss`.
      have h_tgt_init_undef_bss : ∀ y ∈ Block.initVars bss, ρ_tgt.store y = none := by
        intro y hy; exact h_tgt_init_undef y (by rw [Stmt.initVars_block]; exact hy)
      have h_unique_bss : (Block.initVars bss).Nodup := by
        rw [Stmt.initVars_block] at h_unique; exact h_unique
      have wrap : ∀ (oc_inner : Option String) (ρ_inner : Env P),
          StepStmtStar P (EvalCmd P)
            (.stmts bss ρ_src) (Env.outcomeConfig oc_inner ρ_inner) →
          (∀ (ρ_out_inner : Env P),
            StepStmtStar P (EvalCmd P)
              (.stmts (Block.nondetElimM bss σ).1 ρ_tgt) (Env.outcomeConfig oc_inner ρ_out_inner) →
            StepStmtStar P (EvalCmd P)
              (.stmts (Stmt.nondetElimM (.block lbl bss md) σ).1 ρ_tgt)
              (Env.outcomeConfig oc ({ ρ_out_inner with
                store := projectStore ρ_tgt.store ρ_out_inner.store } : Env P))) →
          ρ' = { ρ_inner with store := projectStore ρ_src.store ρ_inner.store } →
          (∀ t, Q t →
              ρ'.store (HasIdent.ident (P := P) t) = none)
            ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P)
                (.stmts (Stmt.nondetElimM (.block lbl bss md) σ).1 ρ_tgt)
                (Env.outcomeConfig oc ρ_out)
              ∧ StoreAgreement ρ'.store ρ_out.store
              ∧ ρ_out.hasFailure = ρ'.hasFailure
              ∧ SemanticStore.isReserved Q
                (Stmt.nondetElimM (.block lbl bss md) σ).2 ρ_out.store := by
        intro oc_inner ρ_inner h_inner_run wrap_run h_ρ'_eq
        obtain ⟨h_fresh_inner, ρ_out_inner, h_run_inner, h_off_inner, h_fail_inner, h_fresh_out⟩ :=
          nondetElim_simulation_gen_sa hQgen bss σ ρ_src ρ_inner ρ_tgt
            h_fail_eq h_fac_eq h_agree hwf
            h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef_bss h_unique_bss h_no_writes_bss
            oc_inner h_inner_run
        refine ⟨?_, ({ ρ_out_inner with
          store := projectStore ρ_tgt.store ρ_out_inner.store } : Env P),
          wrap_run ρ_out_inner h_run_inner, ?_, ?_, ?_⟩
        · subst h_ρ'_eq
          intro t h_suf
          show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
          show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
              then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
          by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
          · rw [ite_eq_left hp]; exact h_fresh_inner t h_suf
          · rw [ite_eq_right hp]
        · -- StoreAgreement survives projecting both stores through agreeing parents.
          subst h_ρ'_eq
          exact StoreAgreement.of_projectStore_parents h_agree h_off_inner
        · subst h_ρ'_eq; exact h_fail_inner
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
          · rw [ite_eq_left hp]; exact h_fresh_out s h_suf h_notin
          · rw [ite_eq_right hp]
      cases oc with
      | none =>
        rcases block_some_reaches_terminal P (EvalCmd P) hrest with
          ⟨ρ_inner, h_inner_term, h_ρ'_eq⟩ | ⟨ρ_inner, h_inner_exit, h_ρ'_eq⟩
        · refine wrap none ρ_inner h_inner_term (fun ρ_out_inner h_run_inner => ?_) h_ρ'_eq
          rw [Stmt.nondetElimM_block_out]
          refine stmt_to_singleton_stmts _ ρ_tgt _ ?_
          refine .step _ _ _ (StepStmt.step_block) ?_
          refine ReflTrans_Transitive _ _ _ _
            (block_inner_star P (EvalCmd P) _ _ (.some lbl) ρ_tgt.store
              (show StepStmtStar P (EvalCmd P) _ (.terminal ρ_out_inner) from
                h_run_inner)) ?_
          exact .step _ _ _ StepStmt.step_block_done (.refl _)
        · refine wrap (some lbl) ρ_inner h_inner_exit (fun ρ_out_inner h_run_inner => ?_) h_ρ'_eq
          rw [Stmt.nondetElimM_block_out]
          refine stmt_to_singleton_stmts _ ρ_tgt _ ?_
          refine .step _ _ _ (StepStmt.step_block) ?_
          refine ReflTrans_Transitive _ _ _ _
            (block_inner_star P (EvalCmd P) _ _ (.some lbl) ρ_tgt.store
              (show StepStmtStar P (EvalCmd P) _ (.exiting lbl ρ_out_inner) from
                h_run_inner)) ?_
          exact .step _ _ _ (StepStmt.step_block_exit_match rfl) (.refl _)
      | some lbl' =>
        obtain ⟨h_ne, ρ_inner, h_inner_exit, h_ρ'_eq⟩ :=
          block_reaches_exiting_strong P (EvalCmd P) hrest
        refine wrap (some lbl') ρ_inner h_inner_exit
          (fun ρ_out_inner h_run_inner => ?_) h_ρ'_eq
        rw [Stmt.nondetElimM_block_out]
        refine stmt_to_singleton_stmts_exiting _ ρ_tgt _ lbl' ?_
        refine .step _ _ _ (StepStmt.step_block) ?_
        refine ReflTrans_Transitive _ _ _ _
          (block_inner_star P (EvalCmd P) _ _ (.some lbl) ρ_tgt.store
            (show StepStmtStar P (EvalCmd P) _ (.exiting lbl' ρ_out_inner) from
              h_run_inner)) ?_
        exact .step _ _ _ (StepStmt.step_block_exit_mismatch (fun h => h_ne (Option.some.inj h))) (.refl _)
  | .ite (.det e) tss ess md, h_no_writes, h_tgt_init_undef, h_unique, oc, h_term =>
    obtain ⟨cfg, hstep, hbranch⟩ :=
      stmt_step_first_inv_to _ ρ_src (Env.outcomeConfig oc ρ')
        (by intro ρ'' h; cases oc <;> simp only [Env.outcomeConfig] at h <;> cases h) h_term
    have hwf_var_t : WellFormedSemanticEvalVar ρ_tgt.factory := h_fac_eq ▸ hwf.var
    have h_dv : Stmt.definedVars (P := P) (.ite (.det e) tss ess md) false
        = Block.definedVars tss false ++ Block.definedVars ess false := by
      simp only [Stmt.definedVars, Bool.false_eq_true, ite_false]
    have h_mv : Stmt.modifiedVars (P := P) (.ite (.det e) tss ess md)
        = Block.modifiedVars tss ++ Block.modifiedVars ess := rfl
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
    | step_ite_true h_cond =>
      obtain ⟨ρ_inner, hbranch_inner, h_ρ'_eq⟩ :=
        blockT_none_reaches_outcome hbranch
      have h_no_writes_t : SrcNoGenWrites (P := P) Q tss := by
        intro t hQ hmem
        rcases List.mem_append.mp hmem with hd | hm
        · exact h_no_writes t hQ (by rw [h_dv]; exact List.mem_append_left _ (List.mem_append_left _ hd))
        · exact h_no_writes t hQ (by rw [h_mv]; exact List.mem_append_right _ (List.mem_append_left _ hm))
      obtain ⟨h_fresh', ρ_out, h_run, h_off', h_fail', h_fresh_out⟩ :=
        nondetElim_simulation_gen_sa hQgen tss σ ρ_src ρ_inner ρ_tgt
          h_fail_eq h_fac_eq h_agree hwf
          h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_t h_unique_t h_no_writes_t
          oc hbranch_inner
      subst h_ρ'_eq
      refine ⟨?_, ({ ρ_out with store := projectStore ρ_tgt.store ρ_out.store } : Env P),
        ?_, ?_, ?_, ?_⟩
      · intro t h_suf
        show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
        show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
        by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
        · rw [ite_eq_left hp]; exact h_fresh' t h_suf
        · rw [ite_eq_right hp]
      · rw [Stmt.nondetElimM_ite_det_out]
        have h_cond_t : P.eval ρ_tgt.factory ρ_tgt.store e = some HasBool.tt := by
          rw [h_fac_eq]
          exact hwf.mono e HasBool.tt ρ_src.store ρ_tgt.store
            (storeAgreement_supplies_mono_premise ρ_src.store ρ_tgt.store h_agree) h_cond
        refine stmt_to_singleton_stmts_outcome _ ρ_tgt _ oc ?_
        refine .step _ _ _ (StepStmt.step_ite_true h_cond_t) ?_
        exact blockT_none_build_outcome _ ρ_tgt.store oc ρ_out h_run
      · exact StoreAgreement.of_projectStore_parents h_agree h_off'
      · exact h_fail'
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
        · rw [ite_eq_left hp]
          have h_fresh_σ₁ : SemanticStore.isReserved Q σ₁ ρ_out.store := by
            rw [h_eq1]
            exact h_fresh_out
          exact (SemanticStore.isReserved.mono h_step12 h_fresh_σ₁) s h_suf h_notin
        · rw [ite_eq_right hp]
    | step_ite_false h_cond =>
      obtain ⟨ρ_inner, hbranch_inner, h_ρ'_eq⟩ :=
        blockT_none_reaches_outcome hbranch
      have h_no_writes_e : SrcNoGenWrites (P := P) Q ess := by
        intro t hQ hmem
        rcases List.mem_append.mp hmem with hd | hm
        · exact h_no_writes t hQ (by rw [h_dv]; exact List.mem_append_left _ (List.mem_append_right _ hd))
        · exact h_no_writes t hQ (by rw [h_mv]; exact List.mem_append_right _ (List.mem_append_right _ hm))
      have h_wf₁ : StringGenState.WF (Block.nondetElimM tss σ).2 :=
        (Block.nondetElimM_genStep tss σ).wf_mono h_wf_gen
      have h_tgt_fresh₁ : SemanticStore.isReserved Q (Block.nondetElimM tss σ).2 ρ_tgt.store :=
        SemanticStore.isReserved.mono (Block.nondetElimM_genStep tss σ) h_tgt_fresh
      obtain ⟨h_fresh', ρ_out, h_run, h_off', h_fail', h_fresh_out⟩ :=
        nondetElim_simulation_gen_sa hQgen ess (Block.nondetElimM tss σ).2 ρ_src ρ_inner ρ_tgt
          h_fail_eq h_fac_eq h_agree hwf
          h_wf₁ h_src_fresh h_tgt_fresh₁ h_tgt_iu_e h_unique_e h_no_writes_e
          oc hbranch_inner
      subst h_ρ'_eq
      refine ⟨?_, ({ ρ_out with store := projectStore ρ_tgt.store ρ_out.store } : Env P),
        ?_, ?_, ?_, ?_⟩
      · intro t h_suf
        show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
        show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
        by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
        · rw [ite_eq_left hp]; exact h_fresh' t h_suf
        · rw [ite_eq_right hp]
      · rw [Stmt.nondetElimM_ite_det_out]
        have h_cond_t : P.eval ρ_tgt.factory ρ_tgt.store e = some HasBool.ff := by
          rw [h_fac_eq]
          exact hwf.mono e HasBool.ff ρ_src.store ρ_tgt.store
            (storeAgreement_supplies_mono_premise ρ_src.store ρ_tgt.store h_agree) h_cond
        refine stmt_to_singleton_stmts_outcome _ ρ_tgt _ oc ?_
        refine .step _ _ _ (StepStmt.step_ite_false h_cond_t) ?_
        exact blockT_none_build_outcome _ ρ_tgt.store oc ρ_out h_run
      · exact StoreAgreement.of_projectStore_parents h_agree h_off'
      · exact h_fail'
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
        · rw [ite_eq_left hp]
          rw [h_eq2, h_eq1] at *
          exact h_fresh_out s h_suf h_notin
        · rw [ite_eq_right hp]
  | .ite .nondet tss ess md, h_no_writes, h_tgt_init_undef, h_unique, oc, h_term =>
    rcases hgen : StringGenState.gen NondetElim.prefixIte σ with ⟨g, σ₁⟩
    have h_g_gen : Q g := by
      have := hQgen.1 σ
      rw [hgen] at this; exact this
    have h_tgt_g_none : ρ_tgt.store (HasIdent.ident (P := P) g) = none := by
      have := SemanticStore.isReserved.gen_slot_none NondetElim.prefixIte
        h_tgt_fresh h_wf_gen (hQgen.1 σ)
      rw [hgen] at this; exact this
    have hwf_var_t : WellFormedSemanticEvalVar ρ_tgt.factory := h_fac_eq ▸ hwf.var
    have hwf_def_t : WellFormedSemanticEvalMono ρ_tgt.factory := h_fac_eq ▸ hwf.mono
    have h_step01 : StringGenState.GenStep σ σ₁ := by
      have := StringGenState.GenStep.of_gen NondetElim.prefixIte σ; rw [hgen] at this; exact this
    have h_wf₁ : StringGenState.WF σ₁ := h_step01.wf_mono h_wf_gen
    have h_dv : Stmt.definedVars (P := P) (.ite .nondet tss ess md) false
        = Block.definedVars tss false ++ Block.definedVars ess false := by
      simp only [Stmt.definedVars, Bool.false_eq_true, ite_false]
    have h_mv : Stmt.modifiedVars (P := P) (.ite .nondet tss ess md)
        = Block.modifiedVars tss ++ Block.modifiedVars ess := rfl
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
    rcases ite_nondet_step_inv_outcome tss ess md ρ_src ρ' oc h_term with h_br | h_br
    · have h_off_g : StoreAgreement ρ_src.store
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) :=
        storeAgreement_storeWith _ _ _ _ h_agree (h_src_fresh g h_g_gen)
      have h_fresh_g : SemanticStore.isReserved Q σ₁
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) := by
        have := SemanticStore.isReserved.storeWith_gen (P := P)
          NondetElim.prefixIte HasBool.tt h_tgt_fresh
        rw [hgen] at this; exact this
      obtain ⟨ρ_inner, h_br_inner, h_ρ'_eq⟩ := h_br
      let ρ_tgt_g : Env P := { ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt }
      obtain ⟨h_fresh', ρ_out, h_run, h_off', h_fail', h_fresh_out⟩ :=
        nondetElim_simulation_gen_sa hQgen tss σ₁
          ρ_src ρ_inner ρ_tgt_g
          h_fail_eq h_fac_eq h_off_g hwf
          h_wf₁ h_src_fresh h_fresh_g (h_tgt_iu_t HasBool.tt) h_unique_t h_no_writes_t
          oc h_br_inner
      subst h_ρ'_eq
      refine ⟨?_, ({ ρ_out with store := projectStore ρ_tgt_g.store ρ_out.store } : Env P),
        ?_, ?_, ?_, ?_⟩
      · intro t h_suf
        show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
        show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
        by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
        · rw [ite_eq_left hp]; exact h_fresh' t h_suf
        · rw [ite_eq_right hp]
      · rw [Stmt.nondetElimM_ite_nondet_out]
        simp only [hgen]
        have := step_ndelim_ite_prefix_outcome true (HasIdent.ident (P := P) g)
          (Block.nondetElimM tss σ₁).1 (Block.nondetElimM ess (Block.nondetElimM tss σ₁).2).1 md
          ρ_tgt ρ_out oc h_tgt_g_none hwf_var_t hwf_def_t h_run
        simpa [ρ_tgt_g] using this
      · exact StoreAgreement.of_projectStore_parents h_off_g h_off'
      · exact h_fail'
      · simp only [Stmt.nondetElimM, hgen]
        rcases h₁ : Block.nondetElimM tss σ₁ with ⟨tss', σ₂⟩
        rcases h₂ : Block.nondetElimM ess σ₂ with ⟨ess', σ₃⟩
        simp only [h₂]
        have h_eq2 : σ₂ = (Block.nondetElimM tss σ₁).2 := by rw [h₁]
        have h_step23 : StringGenState.GenStep σ₂ σ₃ := by
          have := Block.nondetElimM_genStep ess σ₂; rw [h₂] at this; exact this
        have h_fresh_σ₂ : SemanticStore.isReserved Q σ₂ ρ_out.store := by
          rw [h_eq2]
          exact h_fresh_out
        intro s h_suf h_notin
        show projectStore ρ_tgt_g.store ρ_out.store (HasIdent.ident (P := P) s) = none
        show (if (ρ_tgt_g.store (HasIdent.ident (P := P) s)).isSome then ρ_out.store (HasIdent.ident (P := P) s) else none) = none
        by_cases hp : (ρ_tgt_g.store (HasIdent.ident (P := P) s)).isSome
        · rw [ite_eq_left hp]
          exact (SemanticStore.isReserved.mono h_step23 h_fresh_σ₂)
            s h_suf h_notin
        · rw [ite_eq_right hp]
    · have h_step12 : StringGenState.GenStep σ₁ (Block.nondetElimM tss σ₁).2 :=
        Block.nondetElimM_genStep tss σ₁
      have h_wf₂ : StringGenState.WF (Block.nondetElimM tss σ₁).2 := h_step12.wf_mono h_wf₁
      have h_off_g : StoreAgreement ρ_src.store
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) :=
        storeAgreement_storeWith _ _ _ _ h_agree (h_src_fresh g h_g_gen)
      have h_fresh_g1 : SemanticStore.isReserved Q σ₁
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) := by
        have := SemanticStore.isReserved.storeWith_gen (P := P)
          NondetElim.prefixIte HasBool.ff h_tgt_fresh
        rw [hgen] at this; exact this
      have h_fresh_g : SemanticStore.isReserved Q (Block.nondetElimM tss σ₁).2
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) :=
        SemanticStore.isReserved.mono h_step12 h_fresh_g1
      obtain ⟨ρ_inner, h_br_inner, h_ρ'_eq⟩ := h_br
      let ρ_tgt_g : Env P := { ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff }
      obtain ⟨h_fresh', ρ_out, h_run, h_off', h_fail', h_fresh_out⟩ :=
        nondetElim_simulation_gen_sa hQgen ess (Block.nondetElimM tss σ₁).2
          ρ_src ρ_inner ρ_tgt_g
          h_fail_eq h_fac_eq h_off_g hwf
          h_wf₂ h_src_fresh h_fresh_g (h_tgt_iu_e HasBool.ff) h_unique_e h_no_writes_e
          oc h_br_inner
      subst h_ρ'_eq
      refine ⟨?_, ({ ρ_out with store := projectStore ρ_tgt_g.store ρ_out.store } : Env P),
        ?_, ?_, ?_, ?_⟩
      · intro t h_suf
        show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
        show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
        by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
        · rw [ite_eq_left hp]; exact h_fresh' t h_suf
        · rw [ite_eq_right hp]
      · rw [Stmt.nondetElimM_ite_nondet_out]
        simp only [hgen]
        have := step_ndelim_ite_prefix_outcome false (HasIdent.ident (P := P) g)
          (Block.nondetElimM tss σ₁).1 (Block.nondetElimM ess (Block.nondetElimM tss σ₁).2).1 md
          ρ_tgt ρ_out oc h_tgt_g_none hwf_var_t hwf_def_t h_run
        simpa [ρ_tgt_g] using this
      · exact StoreAgreement.of_projectStore_parents h_off_g h_off'
      · exact h_fail'
      · simp only [Stmt.nondetElimM, hgen]
        rcases h₁ : Block.nondetElimM tss σ₁ with ⟨tss', σ₂⟩
        rcases h₂ : Block.nondetElimM ess σ₂ with ⟨ess', σ₃⟩
        simp only [h₂]
        simp only [h₁, h₂] at h_fresh_out
        intro s h_suf h_notin
        show projectStore ρ_tgt_g.store ρ_out.store (HasIdent.ident (P := P) s) = none
        show (if (ρ_tgt_g.store (HasIdent.ident (P := P) s)).isSome then ρ_out.store (HasIdent.ident (P := P) s) else none) = none
        by_cases hp : (ρ_tgt_g.store (HasIdent.ident (P := P) s)).isSome
        · rw [ite_eq_left hp]; exact h_fresh_out s h_suf h_notin
        · rw [ite_eq_right hp]
  | .loop (.det e) m inv body md, h_no_writes, h_tgt_init_undef, h_unique, oc, h_term =>
    have h_no_writes_body : SrcNoGenWrites (P := P) Q body := by
      have h_dv : Stmt.definedVars (P := P) (.loop (.det e) m inv body md) false
          = Block.definedVars body false := by
        simp only [Stmt.definedVars, Bool.false_eq_true, ite_false]
      have h_mv : Stmt.modifiedVars (P := P) (.loop (.det e) m inv body md)
          = Block.modifiedVars body := rfl
      show (∀ s : String, Q s → HasIdent.ident (P := P) s ∉ (Block.definedVars body false ++ Block.modifiedVars body))
      rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
    have h_tgt_iu_body : ∀ y ∈ Block.initVars body, ρ_tgt.store y = none := by
      intro y hy; exact h_tgt_init_undef y (by rw [Stmt.initVars_loop]; exact hy)
    have h_unique_body : (Block.initVars body).Nodup := by
      rw [Stmt.initVars_loop] at h_unique; exact h_unique
    have h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
        ρb_tgt.hasFailure = ρb_src.hasFailure →
        ρb_tgt.factory = ρb_src.factory →
        StoreAgreement ρb_src.store ρb_tgt.store →
        WellFormedSemanticEval ρb_src.factory →
        StringGenState.WF σ →
        (∀ t, Q t →
          ρb_src.store (HasIdent.ident (P := P) t) = none) →
        SemanticStore.isReserved Q σ ρb_tgt.store →
        (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
        StepStmtStar P (EvalCmd P) (.stmts body ρb_src) (Env.outcomeConfig oc_b ρb') →
        (∀ t, Q t →
            ρb'.store (HasIdent.ident (P := P) t) = none)
          ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P)
              (.stmts (Block.nondetElimM body σ).1 ρb_tgt) (Env.outcomeConfig oc_b ρb_out)
            ∧ StoreAgreement ρb'.store ρb_out.store
            ∧ ρb_out.hasFailure = ρb'.hasFailure
            ∧ SemanticStore.isReserved Q (Block.nondetElimM body σ).2 ρb_out.store :=
      fun oc_b ρb_src ρb' ρb_tgt h_fl h_fac_b h_ag hwf hwfg hsf htf htiu hrun =>
        nondetElim_simulation_gen_sa hQgen body σ ρb_src ρb' ρb_tgt
          h_fl h_fac_b h_ag hwf hwfg hsf htf htiu h_unique_body
          h_no_writes_body oc_b hrun
    have hstarT := reflTrans_to_T h_term
    obtain ⟨h_fresh', ρ_out, h_loop_run, h_off', h_fail', h_fresh_out⟩ :=
      nondetElim_loop_det_sim_iteration_sa e m body (Block.nondetElimM body σ).1 md σ
        h_body_sim
        oc ρ_src ρ' ρ_tgt hstarT.len
        h_fail_eq h_fac_eq h_agree hwf
        h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_body hstarT (Nat.le_refl _)
    refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', ?_⟩
    · rw [Stmt.nondetElimM_loop_det_out]
      exact stmt_to_singleton_stmts_outcome _ ρ_tgt ρ_out oc h_loop_run
    · have h_out_eq : (Stmt.nondetElimM (.loop (.det e) m inv body md) σ).2
          = (Block.nondetElimM body σ).2 := by
        rw [Stmt.nondetElimM]
        rcases hh : Block.nondetElimM body σ with ⟨body', σ'⟩
        simp only [hh]
      rw [h_out_eq]
      exact SemanticStore.isReserved.mono (Block.nondetElimM_genStep body σ) h_fresh_out
  | .loop .nondet m inv body md, h_no_writes, h_tgt_init_undef, h_unique, oc, h_term =>
    have h_no_writes_body : SrcNoGenWrites (P := P) Q body := by
      have h_dv : Stmt.definedVars (P := P) (.loop .nondet m inv body md) false
          = Block.definedVars body false := by
        simp only [Stmt.definedVars, Bool.false_eq_true, ite_false]
      have h_mv : Stmt.modifiedVars (P := P) (.loop .nondet m inv body md)
          = Block.modifiedVars body := rfl
      show (∀ s : String, Q s → HasIdent.ident (P := P) s ∉ (Block.definedVars body false ++ Block.modifiedVars body))
      rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
    rcases hgen : StringGenState.gen NondetElim.prefixLoop σ with ⟨g, σ₁⟩
    have h_g_gen : Q g := by
      have := hQgen.2 σ
      rw [hgen] at this; exact this
    have h_g_in : g ∈ σ₁.stringGens := by
      have h := StringGenState.stringGens_gen NondetElim.prefixLoop σ
      rw [hgen] at h; rw [h]; exact List.mem_cons_self
    have h_step01 : StringGenState.GenStep σ σ₁ := by
      have := StringGenState.GenStep.of_gen NondetElim.prefixLoop σ; rw [hgen] at this; exact this
    have h_wf₁ : StringGenState.WF σ₁ := h_step01.wf_mono h_wf_gen
    have h_tgt_g_none : ρ_tgt.store (HasIdent.ident (P := P) g) = none := by
      have := SemanticStore.isReserved.gen_slot_none NondetElim.prefixLoop
        h_tgt_fresh h_wf_gen (hQgen.2 σ)
      rw [hgen] at this; exact this
    have hwf_var_t : WellFormedSemanticEvalVar ρ_tgt.factory := h_fac_eq ▸ hwf.var
    -- Body init-targets are source-shaped, distinct from gen guard `g`; the
    -- guard SemanticStore.update leaves each body init-target's slot untouched.
    have h_tgt_iu_body : ∀ (v : P.Expr) (y : P.Ident), y ∈ Block.initVars body →
        (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) v) y = none := by
      intro v y hy
      have h_y_dv : y ∈ Stmt.definedVars (P := P) (.loop .nondet m inv body md) false := by
        rw [Stmt.definedVars]; simp only [Bool.false_eq_true, ite_false]
        exact hy
      have h_y_ne : y ≠ HasIdent.ident (P := P) g := fun h_eq =>
        h_no_writes g h_g_gen (h_eq ▸ List.mem_append_left _ h_y_dv)
      have h_y_none : ρ_tgt.store y = none := h_tgt_init_undef y
        (by rw [Stmt.initVars_loop]; exact hy)
      simp only [SemanticStore.update, h_y_ne]; exact h_y_none
    have h_unique_body : (Block.initVars body).Nodup := by
      rw [Stmt.initVars_loop] at h_unique; exact h_unique
    have h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
        ρb_tgt.hasFailure = ρb_src.hasFailure →
        ρb_tgt.factory = ρb_src.factory →
        StoreAgreement ρb_src.store ρb_tgt.store →
        WellFormedSemanticEval ρb_src.factory →
        StringGenState.WF σ₁ →
        (∀ t, Q t →
          ρb_src.store (HasIdent.ident (P := P) t) = none) →
        SemanticStore.isReserved Q σ₁ ρb_tgt.store →
        (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
        StepStmtStar P (EvalCmd P) (.stmts body ρb_src) (Env.outcomeConfig oc_b ρb') →
        (∀ t, Q t →
            ρb'.store (HasIdent.ident (P := P) t) = none)
          ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P)
              (.stmts (Block.nondetElimM body σ₁).1 ρb_tgt) (Env.outcomeConfig oc_b ρb_out)
            ∧ StoreAgreement ρb'.store ρb_out.store
            ∧ ρb_out.hasFailure = ρb'.hasFailure
            ∧ SemanticStore.isReserved Q (Block.nondetElimM body σ₁).2 ρb_out.store :=
      fun oc_b ρb_src ρb' ρb_tgt h_fl h_fac_b h_ag hwf hwfg hsf htf htiu hrun =>
        nondetElim_simulation_gen_sa hQgen body σ₁ ρb_src ρb' ρb_tgt
          h_fl h_fac_b h_ag hwf hwfg hsf htf htiu h_unique_body
          h_no_writes_body oc_b hrun
    have finish : ∀ (entering : Bool) (b : P.Expr)
        (h_b : b = (if entering then HasBool.tt else HasBool.ff)),
        ((∀ t, Q t →
            ρ'.store (HasIdent.ident (P := P) t) = none)
          ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P)
              (.stmt (.loop (.det (HasFvar.mkTypedFvar (HasIdent.ident (P := P) g) HasBool.boolTy)) m
                inv
                ((Block.nondetElimM body σ₁).1 ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md)
                ({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) b } : Env P))
              (Env.outcomeConfig oc ρ_out)
            ∧ StoreAgreement ρ'.store ρ_out.store
            ∧ ρ_out.hasFailure = ρ'.hasFailure
            ∧ SemanticStore.isReserved Q σ₁ ρ_out.store) →
        (∀ t, Q t →
            ρ'.store (HasIdent.ident (P := P) t) = none)
          ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P)
              (.stmts (Stmt.nondetElimM (.loop .nondet m inv body md) σ).1 ρ_tgt)
              (Env.outcomeConfig oc ρ_out)
            ∧ StoreAgreement ρ'.store ρ_out.store
            ∧ ρ_out.hasFailure = ρ'.hasFailure
            ∧ SemanticStore.isReserved Q
              (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2
              ρ_out.store := by
      intro entering b h_b ⟨h_fresh', ρ_out, h_loop_run, h_off', h_fail', h_fresh_out⟩
      have hval_b : HasVal.valueOfTy ρ_tgt.factory b HasBool.boolTy := by
        rw [h_b]; split
        · exact (HasBool.boolIsValOfTy ρ_tgt.factory).1
        · exact (HasBool.boolIsValOfTy ρ_tgt.factory).2
      refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', ?_⟩
      · rw [Stmt.nondetElimM_loop_nondet_out]
        simp only [hgen]
        have h_init : StepStmtStar P (EvalCmd P)
            (.stmt (.cmd (HasInit.init (HasIdent.ident (P := P) g) HasBool.boolTy .nondet md)) ρ_tgt)
            (.terminal ({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) b } : Env P)) :=
          step_init_havoc_to (HasIdent.ident (P := P) g) HasBool.boolTy b md ρ_tgt
            h_tgt_g_none hval_b hwf_var_t
        refine ReflTrans_Transitive _ _ _ _
          (stmts_cons_step P (EvalCmd P) _ _ ρ_tgt _ h_init) ?_
        exact stmt_to_singleton_stmts_outcome _ _ ρ_out oc h_loop_run
      · have h_out_eq2 : (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2
            = (Block.nondetElimM body σ₁).2 := by
          rw [Stmt.nondetElimM]
          rcases hh : Block.nondetElimM body σ₁ with ⟨body', σ₂⟩
          simp only [hgen, hh]
        rw [h_out_eq2]
        exact SemanticStore.isReserved.mono (Block.nondetElimM_genStep body σ₁) h_fresh_out
    have h_g_nowrite := nondetElimM_not_writes_gen body σ₁ h_wf₁ g h_g_in
      (fun hc => h_no_writes_body g h_g_gen (List.mem_append_left _ hc))
      (fun hc => h_no_writes_body g h_g_gen (List.mem_append_right _ hc))
    have hstarT := reflTrans_to_T h_term
    rcases loop_nondet_step_first_inv hstarT with
      ⟨hrest, hl⟩ | ⟨hrest, hl⟩
    · have h_off_g : StoreAgreement ρ_src.store
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) :=
        storeAgreement_storeWith _ _ _ _ h_agree (h_src_fresh g h_g_gen)
      have h_fresh_g : SemanticStore.isReserved Q σ₁
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) := by
        have := SemanticStore.isReserved.storeWith_gen (P := P)
          NondetElim.prefixLoop HasBool.ff h_tgt_fresh
        rw [hgen] at this; exact this
      have h_guard_def : (({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff } : Env P).store)
          (HasIdent.ident (P := P) g) = some (if false then HasBool.tt else HasBool.ff) := by
        simp [SemanticStore.update]
      exact finish false HasBool.ff (by simp)
        (nondetElim_loop_nondet_sim_iteration_sa g m body (Block.nondetElimM body σ₁).1 md σ₁ (Block.nondetElimM body σ₁).2
          h_body_sim h_g_gen h_g_in h_g_nowrite.1 h_g_nowrite.2 oc ρ_src ρ'
          ({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff } : Env P)
          hstarT.len h_fail_eq h_fac_eq h_off_g hwf
          h_wf₁ h_src_fresh h_fresh_g (h_tgt_iu_body HasBool.ff) false h_guard_def
          (.inl ⟨rfl, hrest, Nat.le_of_lt hl⟩))
    · have h_off_g : StoreAgreement ρ_src.store
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) :=
        storeAgreement_storeWith _ _ _ _ h_agree (h_src_fresh g h_g_gen)
      have h_fresh_g : SemanticStore.isReserved Q σ₁
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) := by
        have := SemanticStore.isReserved.storeWith_gen (P := P)
          NondetElim.prefixLoop HasBool.tt h_tgt_fresh
        rw [hgen] at this; exact this
      have h_guard_def : (({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P).store)
          (HasIdent.ident (P := P) g) = some (if true then HasBool.tt else HasBool.ff) := by
        simp [SemanticStore.update]
      exact finish true HasBool.tt (by simp)
        (nondetElim_loop_nondet_sim_iteration_sa g m body (Block.nondetElimM body σ₁).1 md σ₁ (Block.nondetElimM body σ₁).2
          h_body_sim h_g_gen h_g_in h_g_nowrite.1 h_g_nowrite.2 oc ρ_src ρ'
          ({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P)
          hstarT.len h_fail_eq h_fac_eq h_off_g hwf
          h_wf₁ h_src_fresh h_fresh_g (h_tgt_iu_body HasBool.tt) true h_guard_def
          (.inr ⟨rfl, hrest, Nat.le_of_lt hl⟩))
  | .exit lbl md, _, _, _, oc, h_term =>
    cases oc with
    | none =>
      exfalso
      simp only [Env.outcomeConfig] at h_term
      obtain ⟨c, hstep, hrest⟩ := stmt_step_first_inv _ ρ_src ρ' h_term
      cases hstep
      cases hrest with
      | step _ _ _ h _ => cases h
    | some lbl' =>
      simp only [Env.outcomeConfig] at h_term
      obtain ⟨c, hstep, hrest⟩ :=
        stmt_step_first_inv_to _ ρ_src (.exiting lbl' ρ')
          (by intro ρ'' h; cases h) h_term
      cases hstep
      have h_eq : lbl' = lbl ∧ ρ' = ρ_src := by
        cases hrest with
        | refl => exact ⟨rfl, rfl⟩
        | step _ _ _ h _ => cases h
      obtain ⟨h_lbl_eq, h_ρ_eq⟩ := h_eq
      subst h_lbl_eq; subst h_ρ_eq
      refine ⟨h_src_fresh, ρ_tgt, ?_, h_agree, h_fail_eq, ?_⟩
      · simp only [Stmt.nondetElimM, Env.outcomeConfig]
        exact stmt_to_singleton_stmts_exiting (.exit lbl' md) ρ_tgt ρ_tgt lbl'
          (.step _ _ _ StepStmt.step_exit (.refl _))
      · simp only [Stmt.nondetElimM]; exact h_tgt_fresh
  | .typeDecl t md, _, _, _, oc, h_term =>
    cases oc with
    | none =>
      simp only [Env.outcomeConfig] at h_term
      obtain ⟨c, hstep, hrest⟩ := stmt_step_first_inv _ ρ_src ρ' h_term
      cases hstep
      have h_eq : ρ_src = ρ' := by
        cases hrest with
        | refl => rfl
        | step _ _ _ h _ => cases h
      subst h_eq
      refine ⟨h_src_fresh, ρ_tgt, ?_, h_agree, h_fail_eq, ?_⟩
      · simp only [Stmt.nondetElimM, Env.outcomeConfig]
        exact stmt_to_singleton_stmts (.typeDecl t md) ρ_tgt ρ_tgt
          (.step _ _ _ StepStmt.step_typeDecl (.refl _))
      · simp only [Stmt.nondetElimM]; exact h_tgt_fresh
    | some lbl =>
      exfalso
      simp only [Env.outcomeConfig] at h_term
      obtain ⟨c, hstep, hrest⟩ :=
        stmt_step_first_inv_to _ ρ_src (.exiting lbl ρ')
          (by intro ρ'' h; cases h) h_term
      cases hstep
      cases hrest with
      | step _ _ _ h _ => cases h
  termination_by sizeOf s

/-- The `StoreAgreement`-based general forward simulation (mutual with
`nondetElim_stmt_gen_sa`). -/
private theorem nondetElim_simulation_gen_sa {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen NondetElim.prefixIte sg).1)
            ∧ (∀ sg, Q (StringGenState.gen NondetElim.prefixLoop sg).1))
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (ρ_src ρ' ρ_tgt : Env P)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_fac_eq : ρ_tgt.factory = ρ_src.factory)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : SemanticStore.isReserved Q σ ρ_tgt.store)
    (h_tgt_init_undef : ∀ y ∈ Block.initVars ss, ρ_tgt.store y = none)
    (h_unique : (Block.initVars ss).Nodup)
    (h_no_writes : SrcNoGenWrites (P := P) Q ss)
    (oc : Option String)
    (h_term : StepStmtStar P (EvalCmd P) (.stmts ss ρ_src) (Env.outcomeConfig oc ρ')) :
    (∀ t, Q t →
        ρ'.store (HasIdent.ident (P := P) t) = none)
      ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P)
          (.stmts (Block.nondetElimM ss σ).1 ρ_tgt) (Env.outcomeConfig oc ρ_out)
        ∧ StoreAgreement ρ'.store ρ_out.store
        ∧ ρ_out.hasFailure = ρ'.hasFailure
        ∧ SemanticStore.isReserved Q (Block.nondetElimM ss σ).2 ρ_out.store := by
  match ss, h_no_writes, h_tgt_init_undef, h_unique, oc, h_term with
  | [], _, _, _, oc, h_term =>
    match oc, h_term with
    | none, h_term =>
      have h_eq : ρ_src = ρ' := stmts_nil_terminal_eq ρ_src ρ' h_term
      subst h_eq
      refine ⟨h_src_fresh, ρ_tgt, ?_, h_agree, h_fail_eq, ?_⟩
      · simp only [Block.nondetElimM, Env.outcomeConfig]
        exact evalStmtsSmallNil P (EvalCmd P) ρ_tgt
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
  | s :: rest, h_no_writes, h_tgt_init_undef, h_unique, oc, h_term =>
    rcases stmts_cons_outcome s rest ρ_src ρ' oc h_term with
      ⟨lbl, h_oc_eq, h_s_exit⟩ | ⟨ρ_mid, h_s_run, h_rest_run⟩
    · subst h_oc_eq
      have h_no_writes_s_e : (∀ t : String, Q t → HasIdent.ident (P := P) t ∉ (Stmt.definedVars s false ++ Stmt.modifiedVars s)) := by
        intro t hQ hmem
        refine h_no_writes t hQ ?_
        rw [Block.definedVars, Block.modifiedVars]
        rcases List.mem_append.mp hmem with hd | hm
        · exact List.mem_append_left _ (List.mem_append_left _ hd)
        · exact List.mem_append_right _ (List.mem_append_left _ hm)
      have h_tgt_iu_s : ∀ y ∈ Stmt.initVars s, ρ_tgt.store y = none := by
        intro y hy; exact h_tgt_init_undef y
          (by rw [Block.initVars_cons]; exact List.mem_append_left _ hy)
      have h_unique_pair_e : (Stmt.initVars s ++ Block.initVars rest).Nodup := by
        rw [Block.initVars_cons] at h_unique; exact h_unique
      have h_unique_s_e : (Stmt.initVars s).Nodup := (List.nodup_append.mp h_unique_pair_e).1
      obtain ⟨h_fresh', ρ_out, h_s_tgt, h_off', h_fail', h_fresh_s⟩ :=
        nondetElim_stmt_gen_sa hQgen s σ ρ_src ρ' ρ_tgt
          h_fail_eq h_fac_eq h_agree hwf
          h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_s h_unique_s_e h_no_writes_s_e
          (some lbl) h_s_exit
      refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', ?_⟩
      · rw [Block.nondetElimM_cons_out]
        refine stmts_cons_head_exiting_append _ _ ρ_tgt ρ_out lbl ?_
        simpa only [Env.outcomeConfig] using h_s_tgt
      · have h_out_eq : (Block.nondetElimM (s :: rest) σ).2
            = (Block.nondetElimM rest (Stmt.nondetElimM s σ).2).2 := by
          rw [Block.nondetElimM]
          rcases hh : Stmt.nondetElimM s σ with ⟨ss_s, σ_s⟩
          rcases hk : Block.nondetElimM rest σ_s with ⟨ss_r, σ_r⟩
          simp only [hh, hk]
        rw [h_out_eq]
        exact SemanticStore.isReserved.mono
          (Block.nondetElimM_genStep rest (Stmt.nondetElimM s σ).2)
          h_fresh_s
    · have h_s_run' : StepStmtStar P (EvalCmd P) (.stmt s ρ_src) (.terminal ρ_mid) :=
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
      obtain ⟨h_mid_fresh, ρ_mid_tgt, h_s_tgt, h_off_mid, h_fail_mid, h_fresh_mid⟩ :=
        nondetElim_stmt_gen_sa hQgen s σ ρ_src ρ_mid ρ_tgt
          h_fail_eq h_fac_eq h_agree hwf
          h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_s h_unique_s h_no_writes_s none h_s_run'
      have h_step_s : StringGenState.GenStep σ (Stmt.nondetElimM s σ).2 :=
        Stmt.nondetElimM_genStep s σ
      have h_wf₁ : StringGenState.WF (Stmt.nondetElimM s σ).2 := h_step_s.wf_mono h_wf_gen
      have hwf_mid : WellFormedSemanticEval ρ_mid.factory := by
        have h1 : ρ_src.factory = ρ_mid.factory := by
          have := star_preserves_factory P (EvalCmd P) h_s_run'
          simpa [Config.getEnv, Env.outcomeConfig] using this
        rw [← h1]; exact hwf
      have h_fac_eq' : ρ_mid_tgt.factory = ρ_mid.factory := by
        have h1 : ρ_src.factory = ρ_mid.factory := by
          have := star_preserves_factory P (EvalCmd P) h_s_run'
          simpa [Config.getEnv, Env.outcomeConfig] using this
        have h2 : ρ_tgt.factory = ρ_mid_tgt.factory := by
          have := star_preserves_factory P (EvalCmd P) h_s_tgt
          simpa [Config.getEnv, Env.outcomeConfig] using this
        rw [← h2, h_fac_eq]; exact h1
      have h_fail_eq' : ρ_mid_tgt.hasFailure = ρ_mid.hasFailure := h_fail_mid
      -- Tail init-target undefinedness at the advanced TARGET env `ρ_mid_tgt`.  The
      -- rewritten head `(Stmt.nondetElimM s σ).1` runs `ρ_tgt → ρ_mid_tgt`.  A
      -- `y ∈ Block.initVars rest` was undefined in `ρ_tgt` (`h_tgt_init_undef`), is
      -- a source name disjoint from `s`'s inits (`h_disjoint_s_rest`, from uniqueness),
      -- and source names are non-`Q` (`h_no_writes_rest`).  By the output
      -- `initVars`-classification + `definedVars = initVars`,
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
      obtain ⟨h_fresh', ρ_out, h_rest_tgt, h_off', h_fail', h_fresh_out⟩ :=
        nondetElim_simulation_gen_sa hQgen rest (Stmt.nondetElimM s σ).2 ρ_mid ρ' ρ_mid_tgt
          h_fail_eq' h_fac_eq' h_off_mid hwf_mid
          h_wf₁ h_mid_fresh h_fresh_mid h_tgt_iu_rest h_unique_rest h_no_writes_rest oc h_rest_run
      refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', ?_⟩
      · rw [Block.nondetElimM_cons_out]
        exact ReflTrans_Transitive _ _ _ _
          (stmts_prefix_terminal_append P (EvalCmd P) _ _ ρ_tgt ρ_mid_tgt h_s_tgt)
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
private theorem nondetElim_simulation {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen NondetElim.prefixIte sg).1)
            ∧ (∀ sg, Q (StringGenState.gen NondetElim.prefixLoop sg).1))
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_no_gen_suffix :
      ∀ s, Q s →
        ρ₀.store (HasIdent.ident (P := P) s) = none)
    (h_no_writes : SrcNoGenWrites (P := P) Q ss)
    (h_store_inits : ∀ y ∈ Block.initVars ss, ρ₀.store y = none)
    (h_unique : Block.uniqueInits ss)
    (h_term : StepStmtStar P (EvalCmd P) (.stmts ss ρ₀) (.terminal ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P)
        (.stmts (Block.nondetElim ss) ρ₀) (.terminal ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure := by
  have h_tgt_fresh : SemanticStore.isReserved Q StringGenState.emp ρ₀.store := by
    intro s h_suf _; exact h_no_gen_suffix s h_suf
  obtain ⟨_, ρ_out, h_run, h_off, h_fl, _⟩ :=
    nondetElim_simulation_gen_sa hQgen ss StringGenState.emp ρ₀ ρ' ρ₀
      rfl rfl (StoreAgreement.refl _) hwf
      StringGenState.wf_emp h_no_gen_suffix h_tgt_fresh h_store_inits h_unique h_no_writes
      none h_term
  exact ⟨ρ_out, h_run, h_off, h_fl⟩

/-- Escaping sibling of `nondetElim_simulation`: surfaces the banked exiting
disjunct of `nondetElim_simulation_gen_sa`.  Every *escaping* source run of `ss`
(reaching `.exiting lbl ρ'`) is matched by an escaping run of `Block.nondetElim ss`
to the *same* label, agreeing on the source's variables and the failure flag.
Identical to the terminal `nondetElim_simulation` except it instantiates the
outcome selector at `some lbl`. -/
private theorem nondetElim_simulation_exit {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen NondetElim.prefixIte sg).1)
            ∧ (∀ sg, Q (StringGenState.gen NondetElim.prefixLoop sg).1))
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_no_gen_suffix :
      ∀ s, Q s →
        ρ₀.store (HasIdent.ident (P := P) s) = none)
    (h_no_writes : SrcNoGenWrites (P := P) Q ss)
    (h_store_inits : ∀ y ∈ Block.initVars ss, ρ₀.store y = none)
    (h_unique : Block.uniqueInits ss)
    (lbl : String)
    (h_exit : StepStmtStar P (EvalCmd P) (.stmts ss ρ₀) (.exiting lbl ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P)
        (.stmts (Block.nondetElim ss) ρ₀) (.exiting lbl ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure := by
  have h_tgt_fresh : SemanticStore.isReserved Q StringGenState.emp ρ₀.store := by
    intro s h_suf _; exact h_no_gen_suffix s h_suf
  obtain ⟨_, ρ_out, h_run, h_off, h_fl, _⟩ :=
    nondetElim_simulation_gen_sa hQgen ss StringGenState.emp ρ₀ ρ' ρ₀
      rfl rfl (StoreAgreement.refl _) hwf
      StringGenState.wf_emp h_no_gen_suffix h_tgt_fresh h_store_inits h_unique h_no_writes
      (some lbl) (by simpa only [Env.outcomeConfig] using h_exit)
  refine ⟨ρ_out, ?_, h_off, h_fl⟩
  simpa only [Env.outcomeConfig, Block.nondetElim] using h_run

/-- Forward simulation: every terminating source execution of `ss` has a
matching execution of `Block.nondetElim ss` agreeing on the source's variables
(`StoreAgreement`) and the failure flag. The existential picks each guard's
havoc value to match the source's nondeterministic choice; `StoreAgreement`'s
one-directionality hides the generated guard variables.

The well-formedness of the evaluator is carried as a single
`WellFormedSemanticEval` bundle so this per-pass simulation shares the
initial-environment interface (WF-eval facts on fac`, per-kind
freshness, and the source block-shape predicates) that the sibling pass
proofs are stated over. -/
theorem nondetElim_sound {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_no_gen_suffix :
      ∀ s, String.HasUnderscoreDigitSuffix s →
        ρ₀.store (HasIdent.ident (P := P) s) = none)
    (h_no_writes : SrcNoGenWrites (P := P) String.HasUnderscoreDigitSuffix ss)
    (h_store_inits : ∀ y ∈ Block.initVars ss, ρ₀.store y = none)
    (h_unique : Block.uniqueInits ss)
    (h_term : StepStmtStar P (EvalCmd P) (.stmts ss ρ₀) (.terminal ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P)
        (.stmts (Block.nondetElim ss) ρ₀) (.terminal ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure :=
  nondetElim_simulation
    (Q := String.HasUnderscoreDigitSuffix)
    ⟨fun sg => StringGenState.gen_hasUnderscoreDigitSuffix NondetElim.prefixIte sg,
     fun sg => StringGenState.gen_hasUnderscoreDigitSuffix NondetElim.prefixLoop sg⟩
    ss ρ₀ ρ'
    hwf h_no_gen_suffix h_no_writes
    h_store_inits h_unique h_term

/-! ### The nondetElim label *kind*

`nondetElim` generates labels under exactly two prefixes: `NondetElim.prefixIte` and
`NondetElim.prefixLoop`. `NondetElim.isGeneratedName s` is the precise predicate
"`s` is a name this pass could have generated": it equals a `gen` output for one
of those prefixes. This is the per-kind `Q` to instantiate the kind-generalized
simulation at, replacing the blanket `HasUnderscoreDigitSuffix` (which would
overcommit a composition partner to keeping *every* gen-shaped name fresh). -/


section NondetElimStructural
variable {P : PureExpr}

/-- Every `initVars` element of the `nondetElim` output of a statement is either
an original source `initVars` element or a freshly-generated `NondetElim.isGeneratedName` guard. -/
theorem Stmt.nondetElimM_initVars_classified [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    ∀ x ∈ Block.initVars (P := P) (Stmt.nondetElimM s σ).1,
      x ∈ Stmt.initVars s ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ NondetElim.isGeneratedName str) :=
  Stmt.nondetElimM_initVars_classified_Q NondetElim.isGeneratedName_gen s σ

/-- Block-level `initVars` classification of the `nondetElim` output. -/
theorem Block.nondetElimM_initVars_classified [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ∀ x ∈ Block.initVars (P := P) (Block.nondetElimM ss σ).1,
      x ∈ Block.initVars ss ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ NondetElim.isGeneratedName str) :=
  Block.nondetElimM_initVars_classified_Q NondetElim.isGeneratedName_gen ss σ

mutual
/-- Every `initTypes` element of the `nondetElim` output of a statement is either
an original source `initTypes` element or the Boolean type of a freshly-generated
guard havoc. -/
theorem Stmt.nondetElimM_initTypes_classified [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    ∀ ty ∈ Block.initTypes (P := P) (Stmt.nondetElimM s σ).1,
      ty ∈ Stmt.initTypes s ∨ ty = HasBool.boolTy := by
  match s with
  | .cmd c =>
      intro ty hty
      simp only [Stmt.nondetElimM, Block.initTypes, Stmt.initTypes, List.append_nil] at hty ⊢
      exact Or.inl hty
  | .block lbl bss md =>
      intro ty hty
      rw [Stmt.nondetElimM_block_out] at hty
      simp only [Block.initTypes, Stmt.initTypes, List.append_nil] at hty ⊢
      exact Block.nondetElimM_initTypes_classified bss σ ty hty
  | .ite (.det e) tss ess md =>
      intro ty hty
      rw [Stmt.nondetElimM_ite_det_out] at hty
      simp only [Block.initTypes, Stmt.initTypes, List.append_nil, List.mem_append] at hty ⊢
      rcases hty with h | h
      · rcases Block.nondetElimM_initTypes_classified tss σ ty h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_initTypes_classified ess _ ty h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .ite .nondet tss ess md =>
      intro ty hty
      rw [Stmt.nondetElimM_ite_nondet_out] at hty
      simp [HasInit.init, Block.initTypes, Stmt.initTypes,
        HasInitTypesImp.initTypes, Cmd.initTypes] at hty ⊢
      rcases hty with h_g | h_t | h_e
      · exact Or.inr h_g
      · rcases Block.nondetElimM_initTypes_classified tss _ ty h_t with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_initTypes_classified ess _ ty h_e with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .loop (.det e) m inv body md =>
      intro ty hty
      rw [Stmt.nondetElimM_loop_det_out] at hty
      simp only [Block.initTypes, Stmt.initTypes, List.append_nil] at hty ⊢
      exact Block.nondetElimM_initTypes_classified body σ ty hty
  | .loop .nondet m inv body md =>
      intro ty hty
      rw [Stmt.nondetElimM_loop_nondet_out] at hty
      simp [HasInit.init, HasHavoc.havoc, Block.initTypes, Stmt.initTypes,
        HasInitTypesImp.initTypes, Cmd.initTypes, Block.initTypes_append] at hty ⊢
      rcases hty with h_g | h_body
      · exact Or.inr h_g
      · rcases Block.nondetElimM_initTypes_classified body _ ty h_body with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
  | .exit lbl md =>
      intro ty hty
      simp only [Stmt.nondetElimM, Block.initTypes, Stmt.initTypes, List.append_nil,
        List.not_mem_nil] at hty
  | .typeDecl t md =>
      intro ty hty
      simp only [Stmt.nondetElimM, Block.initTypes, Stmt.initTypes, List.append_nil,
        List.not_mem_nil] at hty
  termination_by sizeOf s

/-- Block-level `initTypes` classification of the `nondetElim` output. -/
theorem Block.nondetElimM_initTypes_classified [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ∀ ty ∈ Block.initTypes (P := P) (Block.nondetElimM ss σ).1,
      ty ∈ Block.initTypes ss ∨ ty = HasBool.boolTy := by
  match ss with
  | [] =>
      intro ty hty
      simp only [Block.nondetElimM, Block.initTypes, List.not_mem_nil] at hty
  | s :: rest =>
      intro ty hty
      rw [Block.nondetElimM_cons_out, Block.initTypes_append] at hty
      simp only [List.mem_append] at hty
      rw [Block.initTypes, List.mem_append]
      rcases hty with h | h
      · rcases Stmt.nondetElimM_initTypes_classified s σ ty h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_initTypes_classified rest _ ty h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  termination_by sizeOf ss
end

/-- NondetElim preserves initial-variable undefinedness and init-type
inhabitance, accounting for its fresh Boolean guard initializers. -/
theorem Block.nondetElim_initsUndefinedAndInhabited
    {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (ρ : Env P)
    (hdefs : ∀ x ∈ Block.initVars ss, ρ.store x = none)
    (hgens : Env.varsUndefined (P := P) NondetElim.isGeneratedName ρ)
    (hinhab : Block.InitTypesInhabited (P := P) ρ.factory ss) :
    (∀ x ∈ Block.initVars (Block.nondetElim ss), ρ.store x = none)
    ∧ Block.InitTypesInhabited (P := P) ρ.factory (Block.nondetElim ss) := by
  constructor
  · intro x hx
    rcases Block.nondetElimM_initVars_classified ss StringGenState.emp x hx with
      hsource | ⟨name, rfl, hname⟩
    · exact hdefs x hsource
    · exact Env.varsUndefined_apply hgens name hname
  · intro ty hty
    rcases Block.nondetElimM_initTypes_classified ss StringGenState.emp ty hty with
      hsource | rfl
    · exact hinhab ty hsource
    · exact ⟨HasBool.tt, (HasBool.boolIsValOfTy ρ.factory).1⟩


mutual
/-- Every `modifiedVars` element of the `nondetElim` output of a statement is
either an original source `modifiedVars` element or a freshly-generated
`NondetElim.isGeneratedName` guard (the loop re-havoc target). -/
theorem Stmt.nondetElimM_modVars_classified [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    ∀ x ∈ Block.modifiedVars (P := P) (Stmt.nondetElimM s σ).1,
      x ∈ Stmt.modifiedVars s ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ NondetElim.isGeneratedName str) := by
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
      · exact Or.inr
          ⟨(StringGenState.gen NondetElim.prefixLoop σ).1, h_g,
            NondetElim.isGeneratedName_gen.2 σ⟩
  | .exit lbl md =>
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
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ NondetElim.isGeneratedName str) := by
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
            (StringGenState.gen NondetElim.prefixLoop σ).1) md)])
  | .exit lbl md =>
    simp only [Stmt.nondetElimM]
    exact coveredBlock_singleton labels (.exit lbl md) h
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
only `NondetElim.isGeneratedName`-labelled slots are undefined, and any source block that never
writes an `NondetElim.isGeneratedName` label.  Weaker entry precondition than `nondetElim_sound`
(it constrains only the labels this pass generates, not every gen-shaped name),
which is what lets a composition partner — e.g. one that generates under a disjoint
prefix — satisfy it vacuously. -/
theorem nondetElim_sound_kind {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_no_gen_suffix : Env.varsUndefined (P := P) NondetElim.isGeneratedName ρ₀)
    (h_no_writes : SrcNoGenWrites (P := P) NondetElim.isGeneratedName ss)
    (h_store_inits : ∀ y ∈ Block.initVars ss, ρ₀.store y = none)
    (h_unique : Block.uniqueInits ss)
    (h_term : StepStmtStar P (EvalCmd P) (.stmts ss ρ₀) (.terminal ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P)
        (.stmts (Block.nondetElim ss) ρ₀) (.terminal ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure :=
  nondetElim_simulation
    (Q := NondetElim.isGeneratedName) NondetElim.isGeneratedName_gen
    ss ρ₀ ρ'
    hwf (Env.varsUndefined_iff.mp h_no_gen_suffix) h_no_writes
    h_store_inits h_unique h_term

/-- Escaping companion of `nondetElim_sound_kind` (at `Q := NondetElim.isGeneratedName`): every
escaping source run of `ss` reaching `.exiting lbl` is matched by an escaping run
of `Block.nondetElim ss` to the *same* label, agreeing on the source's variables
and the failure flag.  A thin forwarder to `nondetElim_simulation_exit`; the
`Env.varsUndefined` store precondition unfolds to the explicit per-kind
freshness fact the simulation consumes. -/
theorem nondetElim_sound_kind_exit {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_no_gen_suffix : Env.varsUndefined (P := P) NondetElim.isGeneratedName ρ₀)
    (h_no_writes : SrcNoGenWrites (P := P) NondetElim.isGeneratedName ss)
    (h_store_inits : ∀ y ∈ Block.initVars ss, ρ₀.store y = none)
    (h_unique : Block.uniqueInits ss)
    (lbl : String)
    (h_exit : StepStmtStar P (EvalCmd P) (.stmts ss ρ₀) (.exiting lbl ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P)
        (.stmts (Block.nondetElim ss) ρ₀) (.exiting lbl ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure :=
  nondetElim_simulation_exit
    (Q := NondetElim.isGeneratedName) NondetElim.isGeneratedName_gen
    ss ρ₀ ρ'
    hwf (Env.varsUndefined_iff.mp h_no_gen_suffix) h_no_writes
    h_store_inits h_unique lbl h_exit

/-! ### Compositional-input soundness (`nondetElim_sound_kind_compositional*`)

Unlike the diagonal kind wrappers above, these run the target from an arbitrary
`ρ_tgt` that store-agrees with the source `ρ₀` (an overapproximating target
store), as the up-to-relation overapproximation instance needs.  Thin forwarders
to the `_sa` engine at `σ := StringGenState.emp`, `Q := NondetElim.isGeneratedName`. -/

/-- A terminating source run of `ss` from `ρ₀` is matched by a run of
`Block.nondetElim ss` from any store-agreeing target `ρ_tgt`, with the outputs
again store-agreeing (the `NondetElim.isGeneratedName`-keyed compositional soundness the
overapproximation instance consumes). -/
theorem nondetElim_sound_kind_compositional {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' ρ_tgt : Env P)
    (h_fail_eq : ρ_tgt.hasFailure = ρ₀.hasFailure)
    (h_fac_eq : ρ_tgt.factory = ρ₀.factory)
    (h_agree : StoreAgreement ρ₀.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_src_no_gen : Env.varsUndefined (P := P) NondetElim.isGeneratedName ρ₀)
    (h_tgt_no_gen : Env.varsUndefined (P := P) NondetElim.isGeneratedName ρ_tgt)
    (h_tgt_inits : ∀ y ∈ Block.initVars ss, ρ_tgt.store y = none)
    (h_no_writes : SrcNoGenWrites (P := P) NondetElim.isGeneratedName ss)
    (h_unique : Block.uniqueInits ss)
    (h_term : StepStmtStar P (EvalCmd P) (.stmts ss ρ₀) (.terminal ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P)
        (.stmts (Block.nondetElim ss) ρ_tgt) (.terminal ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure := by
  have h_tgt_fresh : SemanticStore.isReserved NondetElim.isGeneratedName
      StringGenState.emp ρ_tgt.store := by
    intro s h_suf _; exact Env.varsUndefined_apply h_tgt_no_gen s h_suf
  obtain ⟨_, ρ_out, h_run, h_off, h_fl, _⟩ :=
    nondetElim_simulation_gen_sa NondetElim.isGeneratedName_gen ss StringGenState.emp ρ₀ ρ' ρ_tgt
      h_fail_eq h_fac_eq h_agree hwf
      StringGenState.wf_emp (Env.varsUndefined_iff.mp h_src_no_gen) h_tgt_fresh h_tgt_inits h_unique h_no_writes
      none h_term
  exact ⟨ρ_out, h_run, h_off, h_fl⟩

/-- Escaping companion of `nondetElim_sound_kind_compositional`. -/
theorem nondetElim_sound_kind_exit_compositional {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' ρ_tgt : Env P)
    (h_fail_eq : ρ_tgt.hasFailure = ρ₀.hasFailure)
    (h_fac_eq : ρ_tgt.factory = ρ₀.factory)
    (h_agree : StoreAgreement ρ₀.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_src_no_gen : Env.varsUndefined (P := P) NondetElim.isGeneratedName ρ₀)
    (h_tgt_no_gen : Env.varsUndefined (P := P) NondetElim.isGeneratedName ρ_tgt)
    (h_tgt_inits : ∀ y ∈ Block.initVars ss, ρ_tgt.store y = none)
    (h_no_writes : SrcNoGenWrites (P := P) NondetElim.isGeneratedName ss)
    (h_unique : Block.uniqueInits ss)
    (lbl : String)
    (h_exit : StepStmtStar P (EvalCmd P) (.stmts ss ρ₀) (.exiting lbl ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P)
        (.stmts (Block.nondetElim ss) ρ_tgt) (.exiting lbl ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure := by
  have h_tgt_fresh : SemanticStore.isReserved NondetElim.isGeneratedName
      StringGenState.emp ρ_tgt.store := by
    intro s h_suf _; exact Env.varsUndefined_apply h_tgt_no_gen s h_suf
  obtain ⟨_, ρ_out, h_run, h_off, h_fl, _⟩ :=
    nondetElim_simulation_gen_sa NondetElim.isGeneratedName_gen ss StringGenState.emp ρ₀ ρ' ρ_tgt
      h_fail_eq h_fac_eq h_agree hwf
      StringGenState.wf_emp (Env.varsUndefined_iff.mp h_src_no_gen) h_tgt_fresh h_tgt_inits h_unique h_no_writes
      (some lbl) (by simpa only [Env.outcomeConfig] using h_exit)
  refine ⟨ρ_out, ?_, h_off, h_fl⟩
  simpa only [Env.outcomeConfig, Block.nondetElim] using h_run

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
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (e : P.Expr) (m : Option P.Expr) {inv : List (String × P.Expr)}
    (body body' : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ σ_out : StringGenState)
    (h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
      ρb_tgt.hasFailure = ρb_src.hasFailure →
      ρb_tgt.factory = ρb_src.factory →
      StoreAgreement ρb_src.store ρb_tgt.store →
      WellFormedSemanticEval ρb_src.factory →
      StringGenState.WF σ →
      (∀ t, Q t →
        ρb_src.store (HasIdent.ident (P := P) t) = none) →
      SemanticStore.isReserved Q σ ρb_tgt.store →
      (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
      StepStmtStar P (EvalCmd P) (.stmts body ρb_src) (Env.outcomeConfig oc_b ρb') →
      (∀ t, Q t →
          ρb'.store (HasIdent.ident (P := P) t) = none)
        ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P)
            (.stmts body' ρb_tgt) (Env.outcomeConfig oc_b ρb_out)
          ∧ StoreAgreement ρb'.store ρb_out.store
          ∧ ρb_out.hasFailure = ρb'.hasFailure
          ∧ SemanticStore.isReserved Q σ_out ρb_out.store)
    -- Failing per-iteration body simulation, used for the FAILING iteration.
    (h_body_sim_fail : ∀ (ρb_src ρb_tgt : Env P) (d : Config P (Cmd P)),
      ρb_tgt.hasFailure = ρb_src.hasFailure →
      ρb_tgt.factory = ρb_src.factory →
      StoreAgreement ρb_src.store ρb_tgt.store →
      WellFormedSemanticEval ρb_src.factory →
      StringGenState.WF σ →
      (∀ t, Q t →
        ρb_src.store (HasIdent.ident (P := P) t) = none) →
      SemanticStore.isReserved Q σ ρb_tgt.store →
      (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
      StepStmtStar P (EvalCmd P) (.stmts body ρb_src) d →
      d.getEnv.hasFailure = true →
      ∃ d', StepStmtStar P (EvalCmd P) (.stmts body' ρb_tgt) d'
        ∧ d'.getEnv.hasFailure = true)
    (ρ_src ρ_tgt : Env P) (a' : Config P (Cmd P)) (n : Nat)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_fac_eq : ρ_tgt.factory = ρ_src.factory)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : SemanticStore.isReserved Q σ ρ_tgt.store)
    (h_tgt_init_undef : ∀ y ∈ Block.initVars body, ρ_tgt.store y = none)
    (hT : ReflTransT (StepStmt P (EvalCmd P))
      (.stmt (.loop (.det e) m inv body md) ρ_src) a')
    (h_a'_fail : a'.getEnv.hasFailure = true)
    (hlen : hT.len ≤ n) :
    ∃ d, StepStmtStar P (EvalCmd P)
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
    | .step _ _ _ (StepStmt.step_loop_exit hg_false) hrest, hl_succ =>
      have ha''_eq : a' = .terminal ({ ρ_src with hasFailure := ρ_src.hasFailure || false } : Env P) :=
        reflTransT_from_terminal P (by simpa only [Bool.or_false] using hrest)
      rw [ha''_eq] at h_a'_fail
      have : ρ_src.hasFailure = true := by simpa [Config.getEnv, Bool.or_false] using h_a'_fail
      exact ⟨.stmt (.loop (.det e) m inv body' md) ρ_tgt, .refl _,
        by simpa [Config.getEnv] using (h_fail_eq.trans this)⟩
    | .step _ _ _ (StepStmt.step_loop_enter hg_true) hrest, hl_succ =>
      have h_cond_t : P.eval ρ_tgt.factory ρ_tgt.store e = some HasBool.tt := by
        rw [h_fac_eq]
        exact hwf.mono e HasBool.tt ρ_src.store ρ_tgt.store
          (storeAgreement_supplies_mono_premise ρ_src.store ρ_tgt.store h_agree) hg_true
      have h_step_enter : StepStmtStar P (EvalCmd P)
          (.stmt (.loop (.det e) m inv body' md) ρ_tgt)
          (.seq (.block .none ρ_tgt.store (.stmts body' ρ_tgt))
            [.loop (.det e) m inv body' md]) :=
        .step _ _ _ (StepStmt.step_loop_enter
          h_cond_t) (.refl _)
      rcases seqT_reaches_failing' P hrest h_a'_fail with hA | hB
      · -- CASE A: the failure is inside THIS iteration's body block.
        obtain ⟨d_blk, h_blk_run, hd_blk_fail, _⟩ := hA
        have ⟨d_body, h_body_run, hd_body_fail, _⟩ :=
          blockT_none_reaches_failing' P h_blk_run hd_blk_fail
        have ⟨d', h_body_tgt, hd'_fail⟩ :=
          h_body_sim_fail ρ_src ρ_tgt d_body h_fail_eq h_fac_eq h_agree hwf
            h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef
            (reflTransT_to_prop h_body_run) hd_body_fail
        have h_blk_tgt : StepStmtStar P (EvalCmd P)
            (.block .none ρ_tgt.store (.stmts body' ρ_tgt))
            (.block .none ρ_tgt.store d') :=
          block_inner_star P (EvalCmd P) _ _ .none ρ_tgt.store h_body_tgt
        refine ⟨.seq (.block .none ρ_tgt.store d')
          [.loop (.det e) m inv body' md],
          ReflTrans_Transitive _ _ _ _ h_step_enter
            (seq_inner_star P (EvalCmd P) _ _ _ h_blk_tgt), ?_⟩
        simpa [Config.getEnv] using hd'_fail
      · -- CASE B: this iteration's body terminated; recurse on the next iteration.
        obtain ⟨ρ_blk_inner, d_rest, h_blk_term, h_loop_rest, hd_rest_fail, hlen_rest⟩ := hB
        have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
          blockT_none_reaches_terminal h_blk_term
        subst heq_ρ_block
        have h_body_run : StepStmtStar P (EvalCmd P)
            (.stmts body ρ_src) (Env.outcomeConfig none ρ_inner) := reflTransT_to_prop h_inner_term
        obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner, h_fresh_inner⟩ :=
          h_body_sim none ρ_src ρ_inner ρ_tgt h_fail_eq h_fac_eq h_agree hwf
            h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef h_body_run
        have h_blk_tgt_term : StepStmtStar P (EvalCmd P)
            (.block .none ρ_tgt.store (.stmts body' ρ_tgt))
            (.terminal ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store } : Env P)) := by
          have h_body_tgt' : StepStmtStar P (EvalCmd P)
              (.stmts body' ρ_tgt)
              (.terminal ρ_inner_tgt) := by
            simpa only [Env.outcomeConfig] using h_body_tgt
          refine ReflTrans_Transitive _ _ _ _
            (block_inner_star P (EvalCmd P) _ _ .none ρ_tgt.store h_body_tgt') ?_
          exact .step _ _ _ StepStmt.step_block_done (.refl _)
        have h_step_after_iter : StepStmtStar P (EvalCmd P)
            (.stmt (.loop (.det e) m inv body' md) ρ_tgt)
            (.stmts [.loop (.det e) m inv body' md]
              ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store } : Env P)) :=
          ReflTrans_Transitive _ _ _ _ h_step_enter
            (ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) _ _ _ h_blk_tgt_term)
              (.step _ _ _ StepStmt.step_seq_done (.refl _)))
        let ρ_src_next : Env P :=
          { store := projectStore ρ_src.store ρ_inner.store,
            factory := ρ_inner.factory,
            hasFailure := ρ_inner.hasFailure }
        let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store }
        have hwf_next : WellFormedSemanticEval ρ_src_next.factory := by
          show WellFormedSemanticEval ρ_inner.factory
          have h1 : ρ_src.factory = ρ_inner.factory := by
            have := star_preserves_factory P (EvalCmd P) h_body_run
            simpa [Config.getEnv, Env.outcomeConfig] using this
          rw [← h1]; exact hwf
        have h_fac_eq_next : ρ_tgt_next.factory = ρ_src_next.factory := by
          show ρ_inner_tgt.factory = ρ_inner.factory
          have h1 : ρ_src.factory = ρ_inner.factory := by
            have := star_preserves_factory P (EvalCmd P) h_body_run
            simpa [Config.getEnv, Env.outcomeConfig] using this
          have h2 : ρ_tgt.factory = ρ_inner_tgt.factory := by
            have := star_preserves_factory P (EvalCmd P) h_body_tgt
            simpa [Config.getEnv, Env.outcomeConfig] using this
          rw [← h2, h_fac_eq]; exact h1
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
          · rw [ite_eq_left hp]; exact h_inner_fresh t h_suf
          · rw [ite_eq_right hp]
        have h_tgt_fresh_next : SemanticStore.isReserved Q σ ρ_tgt_next.store := by
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
          stmts_singleton_reaches_failing' P h_loop_rest hd_rest_fail
        have h_inner_le_n : h_loop_stmt.len ≤ n := by
          simp only [ReflTransT.len] at hl_succ; omega
        obtain ⟨d, h_run_recurse, hd_fail⟩ :=
          ih ρ_src_next ρ_tgt_next d_loop h_fail_eq_next h_fac_eq_next h_agree_next hwf_next
            h_src_fresh_next h_tgt_fresh_next h_tgt_init_undef_next h_loop_stmt hd_loop_fail h_inner_le_n
        have h_run_recurse_stmts : StepStmtStar P (EvalCmd P)
            (.stmts [.loop (.det e) m inv body' md] ρ_tgt_next)
            (.seq d ([] : List (Stmt P (Cmd P)))) :=
          .step _ _ _ StepStmt.step_stmts_cons
            (seq_inner_star P (EvalCmd P) _ _ _ h_run_recurse)
        refine ⟨.seq d ([] : List (Stmt P (Cmd P))),
          ReflTrans_Transitive _ _ _ _ h_step_after_iter h_run_recurse_stmts, ?_⟩
        simpa [Config.getEnv] using hd_fail

/-- Failing-config nondeterministic-loop iteration.  The re-havoc next-iteration
agreement composes `StoreAgreement.of_projectStore_parents` with
`storeAgreement_storeWith` for the freshly-havoced gen guard slot. -/
private theorem nondetElim_loop_nondet_to_fail_iteration_sa {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (g : String) (m : Option P.Expr) {inv : List (String × P.Expr)}
    (body body' : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ σ_out : StringGenState)
    (h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
      ρb_tgt.hasFailure = ρb_src.hasFailure →
      ρb_tgt.factory = ρb_src.factory →
      StoreAgreement ρb_src.store ρb_tgt.store →
      WellFormedSemanticEval ρb_src.factory →
      StringGenState.WF σ →
      (∀ t, Q t →
        ρb_src.store (HasIdent.ident (P := P) t) = none) →
      SemanticStore.isReserved Q σ ρb_tgt.store →
      (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
      StepStmtStar P (EvalCmd P) (.stmts body ρb_src) (Env.outcomeConfig oc_b ρb') →
      (∀ t, Q t →
          ρb'.store (HasIdent.ident (P := P) t) = none)
        ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P)
            (.stmts body' ρb_tgt) (Env.outcomeConfig oc_b ρb_out)
          ∧ StoreAgreement ρb'.store ρb_out.store
          ∧ ρb_out.hasFailure = ρb'.hasFailure
          ∧ SemanticStore.isReserved Q σ_out ρb_out.store)
    (h_body_sim_fail : ∀ (ρb_src ρb_tgt : Env P) (d : Config P (Cmd P)),
      ρb_tgt.hasFailure = ρb_src.hasFailure →
      ρb_tgt.factory = ρb_src.factory →
      StoreAgreement ρb_src.store ρb_tgt.store →
      WellFormedSemanticEval ρb_src.factory →
      StringGenState.WF σ →
      (∀ t, Q t →
        ρb_src.store (HasIdent.ident (P := P) t) = none) →
      SemanticStore.isReserved Q σ ρb_tgt.store →
      (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
      StepStmtStar P (EvalCmd P) (.stmts body ρb_src) d →
      d.getEnv.hasFailure = true →
      ∃ d', StepStmtStar P (EvalCmd P) (.stmts body' ρb_tgt) d'
        ∧ d'.getEnv.hasFailure = true)
    (h_g_gen : Q g)
    (h_g_ndef : HasIdent.ident (P := P) g ∉ Block.definedVars (P := P) (C := Cmd P) body' false)
    (h_g_nmod : HasIdent.ident (P := P) g ∉ Block.modifiedVars (P := P) (C := Cmd P) body')
    (ρ_src ρ_tgt : Env P) (a' : Config P (Cmd P)) (n : Nat)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_fac_eq : ρ_tgt.factory = ρ_src.factory)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : SemanticStore.isReserved Q σ ρ_tgt.store)
    (h_tgt_init_undef : ∀ y ∈ Block.initVars body, ρ_tgt.store y = none)
    (entering : Bool)
    (h_guard_def : ρ_tgt.store (HasIdent.ident (P := P) g)
      = some (if entering then HasBool.tt else HasBool.ff))
    (h_a'_fail : a'.getEnv.hasFailure = true)
    (h_src_first :
      (entering = false ∧ ∃ (hrest : ReflTransT (StepStmt P (EvalCmd P))
          (.terminal ρ_src) a'),
        hrest.len ≤ n) ∨
      (entering = true ∧ ∃ (hrest : ReflTransT (StepStmt P (EvalCmd P))
          (.seq (.block .none ρ_src.store (.stmts body ρ_src))
            [.loop .nondet m inv body md]) a'),
        hrest.len ≤ n)) :
    ∃ d, StepStmtStar P (EvalCmd P)
        (.stmt (.loop (.det (HasFvar.mkTypedFvar (HasIdent.ident (P := P) g) HasBool.boolTy)) m
          inv
          (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md) ρ_tgt) d
      ∧ d.getEnv.hasFailure = true := by
  induction n generalizing ρ_src ρ_tgt a' entering with
  | zero =>
    rcases h_src_first with ⟨h_ent, hrest, hl⟩ | ⟨h_ent, hrest, hl⟩
    · have ha'_eq : a' = .terminal ρ_src :=
        reflTransT_from_terminal P hrest
      rw [ha'_eq] at h_a'_fail
      have : ρ_src.hasFailure = true := by simpa [Config.getEnv, Bool.or_false] using h_a'_fail
      exact ⟨.stmt (.loop (.det (HasFvar.mkTypedFvar (HasIdent.ident (P := P) g) HasBool.boolTy)) m
        inv
        (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md) ρ_tgt, .refl _,
        by simpa [Config.getEnv] using (h_fail_eq.trans this)⟩
    · subst h_ent
      have ha'_eq : a' = .seq (.block .none ρ_src.store (.stmts body ρ_src))
          [.loop .nondet m inv body md] := by
        match hrest, hl with
        | .refl _, _ => rfl
        | .step _ _ _ _ _, hl => simp only [ReflTransT.len] at hl; omega
      rw [ha'_eq] at h_a'_fail
      have : ρ_src.hasFailure = true := by
        simpa [Config.getEnv, Bool.or_false] using h_a'_fail
      exact ⟨.stmt (.loop (.det (HasFvar.mkTypedFvar (HasIdent.ident (P := P) g) HasBool.boolTy)) m
        inv
        (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md) ρ_tgt, .refl _,
        by simpa [Config.getEnv] using (h_fail_eq.trans this)⟩
  | succ n ih =>
    rcases h_src_first with ⟨h_ent, hrest, hl⟩ | ⟨h_ent, hrest, hl⟩
    · have ha'_eq : a' = .terminal ρ_src :=
        reflTransT_from_terminal P hrest
      rw [ha'_eq] at h_a'_fail
      have : ρ_src.hasFailure = true := by simpa [Config.getEnv, Bool.or_false] using h_a'_fail
      exact ⟨.stmt (.loop (.det (HasFvar.mkTypedFvar (HasIdent.ident (P := P) g) HasBool.boolTy)) m
        inv
        (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md) ρ_tgt, .refl _,
        by simpa [Config.getEnv] using (h_fail_eq.trans this)⟩
    · subst h_ent
      simp only [ite_true] at h_guard_def
      have h_guard_tt : P.eval ρ_tgt.factory ρ_tgt.store (HasFvar.mkTypedFvar (HasIdent.ident (P := P) g) HasBool.boolTy)
          = some HasBool.tt := by
        rw [h_fac_eq]
        exact eval_mkTypedFvar_of_value ρ_src.factory ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt
          (HasBool.boolIsVal ρ_src.factory).1 h_guard_def hwf.var hwf.mono
      have h_step_enter : StepStmtStar P (EvalCmd P)
          (.stmt (.loop (.det (HasFvar.mkTypedFvar (HasIdent.ident (P := P) g) HasBool.boolTy)) m
            inv
            (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md) ρ_tgt)
          (.seq (.block .none ρ_tgt.store (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
            ρ_tgt))
            [.loop (.det (HasFvar.mkTypedFvar (HasIdent.ident (P := P) g) HasBool.boolTy)) m inv
              (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md]) :=
        .step _ _ _ (StepStmt.step_loop_enter
          h_guard_tt) (.refl _)
      have h_g_some_tgt : (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome = true := by
        rw [h_guard_def]; rfl
      rcases seqT_reaches_failing' P hrest h_a'_fail with hA | hB
      · -- CASE A: failure inside THIS iteration's body block (before the havoc).
        obtain ⟨d_blk, h_blk_run, hd_blk_fail, _⟩ := hA
        have ⟨d_body, h_body_run, hd_body_fail, _⟩ :=
          blockT_none_reaches_failing' P h_blk_run hd_blk_fail
        have ⟨d', h_body_tgt, hd'_fail⟩ :=
          h_body_sim_fail ρ_src ρ_tgt d_body h_fail_eq h_fac_eq h_agree hwf
            h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef
            (reflTransT_to_prop h_body_run) hd_body_fail
        obtain ⟨d'', h_body_tail_fail, hd''_fail⟩ :=
          stmts_prefix_failing_append P
            body' [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)] ρ_tgt d' h_body_tgt hd'_fail
        have h_blk_tgt : StepStmtStar P (EvalCmd P)
            (.block .none ρ_tgt.store (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
              ρ_tgt))
            (.block .none ρ_tgt.store d'') :=
          block_inner_star P (EvalCmd P) _ _ .none ρ_tgt.store h_body_tail_fail
        refine ⟨.seq (.block .none ρ_tgt.store d'')
          [.loop (.det (HasFvar.mkTypedFvar (HasIdent.ident (P := P) g) HasBool.boolTy)) m inv
            (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md],
          ReflTrans_Transitive _ _ _ _ h_step_enter
            (seq_inner_star P (EvalCmd P) _ _ _ h_blk_tgt), ?_⟩
        simpa [Config.getEnv] using hd''_fail
      · -- CASE B: this iteration's body terminated; recurse on the next iteration.
        obtain ⟨ρ_blk_inner, d_rest, h_blk_term, h_loop_rest, hd_rest_fail, hlen_rest⟩ := hB
        have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
          blockT_none_reaches_terminal h_blk_term
        subst heq_ρ_block
        have h_body_run : StepStmtStar P (EvalCmd P)
            (.stmts body ρ_src) (Env.outcomeConfig none ρ_inner) := reflTransT_to_prop h_inner_term
        obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner, h_fresh_inner⟩ :=
          h_body_sim none ρ_src ρ_inner ρ_tgt h_fail_eq h_fac_eq h_agree hwf
            h_wf_gen h_src_fresh h_tgt_fresh h_tgt_init_undef h_body_run
        have h_body_tgt_term : StepStmtStar P (EvalCmd P)
            (.stmts body' ρ_tgt)
            (.terminal ρ_inner_tgt) := by
          simpa only [Env.outcomeConfig] using h_body_tgt
        have h_g_some_inner : (ρ_inner_tgt.store (HasIdent.ident (P := P) g)).isSome = true :=
          stmts_preserves_isSome h_body_tgt_term
            (by simpa using h_g_some_tgt)
        obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp h_g_some_inner
        have hwf_var_inner : WellFormedSemanticEvalVar ρ_inner_tgt.factory := by
          have h_fac_it : ρ_inner_tgt.factory = ρ_src.factory := by
            have h2 : ρ_tgt.factory = ρ_inner_tgt.factory := by
              have := star_preserves_factory P (EvalCmd P) h_body_tgt_term
              simpa [Config.getEnv, Env.outcomeConfig] using this
            rw [← h2, h_fac_eq]
          rw [h_fac_it]; exact hwf.var
        let ρ_src_next : Env P :=
          { store := projectStore ρ_src.store ρ_inner.store,
            factory := ρ_inner.factory,
            hasFailure := ρ_inner.hasFailure }
        have ⟨d_loop, h_loop_stmt, hd_loop_fail, hlen_loop⟩ :=
          stmts_singleton_reaches_failing' P h_loop_rest hd_rest_fail
        have step_assemble : ∀ (next_ent : Bool),
            (entering_next_src_first : (next_ent = false ∧ ∃ (hr : ReflTransT (StepStmt P (EvalCmd P))
                  (.terminal ρ_src_next) d_loop),
                hr.len ≤ n) ∨
              (next_ent = true ∧ ∃ (hr : ReflTransT (StepStmt P (EvalCmd P))
                  (.seq (.block .none ρ_src_next.store (.stmts body ρ_src_next))
                    [.loop .nondet m inv body md]) d_loop),
                hr.len ≤ n)) →
            ∃ d, StepStmtStar P (EvalCmd P)
                (.stmt (.loop (.det (HasFvar.mkTypedFvar (HasIdent.ident (P := P) g) HasBool.boolTy)) m
                  inv
                  (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md) ρ_tgt) d
              ∧ d.getEnv.hasFailure = true := by
          intro next_ent hsfirst_next
          let bval : P.Expr := if next_ent then HasBool.tt else HasBool.ff
          have hval_b : HasVal.valueOfTy ρ_inner_tgt.factory bval HasBool.boolTy := by
            simp only [bval]; split
            · exact (HasBool.boolIsValOfTy ρ_inner_tgt.factory).1
            · exact (HasBool.boolIsValOfTy ρ_inner_tgt.factory).2
          have h_tail : StepStmtStar P (EvalCmd P)
              (.stmt (.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)) ρ_inner_tgt)
              (.terminal ({ ρ_inner_tgt with store := SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) bval } : Env P)) :=
            step_havoc_set_to (HasIdent.ident (P := P) g) bval md ρ_inner_tgt v' hv'
              HasBool.boolTy
              (by
                have h_g_pres : ρ_inner_tgt.store (HasIdent.ident (P := P) g)
                    = ρ_tgt.store (HasIdent.ident (P := P) g) :=
                  block_run_terminal_preserves_eq_of_not_written h_g_ndef h_g_nmod h_body_tgt_term
                have hv'_tt : v' = HasBool.tt :=
                  Option.some.inj (hv'.symm.trans (h_g_pres.trans h_guard_def))
                rw [hv'_tt]; exact (HasBool.boolIsValOfTy ρ_inner_tgt.factory).1)
              hval_b hwf_var_inner
          have h_body_tail : StepStmtStar P (EvalCmd P)
              (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt)
              (.terminal ({ ρ_inner_tgt with store := SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) bval } : Env P)) :=
            ReflTrans_Transitive _ _ _ _
              (stmts_prefix_terminal_append P (EvalCmd P) _ _ _ ρ_inner_tgt h_body_tgt_term)
              (stmt_to_singleton_stmts _ ρ_inner_tgt _ h_tail)
          let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store (SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) bval) }
          have h_guard_next : ρ_tgt_next.store (HasIdent.ident (P := P) g)
              = some (if next_ent then HasBool.tt else HasBool.ff) := by
            show (if (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome
                then SemanticStore.update ρ_inner_tgt.store (HasIdent.ident (P := P) g) bval
                  (HasIdent.ident (P := P) g) else none) = some (if next_ent then HasBool.tt else HasBool.ff)
            rw [ite_eq_left h_g_some_tgt]; simp [SemanticStore.update, bval]
          have hwf_next : WellFormedSemanticEval ρ_src_next.factory := by
            show WellFormedSemanticEval ρ_inner.factory
            have h1 : ρ_src.factory = ρ_inner.factory := by
              have := star_preserves_factory P (EvalCmd P) h_body_run
              simpa [Config.getEnv, Env.outcomeConfig] using this
            rw [← h1]; exact hwf
          have h_fac_eq_next : ρ_tgt_next.factory = ρ_src_next.factory := by
            show ρ_inner_tgt.factory = ρ_inner.factory
            have h1 : ρ_src.factory = ρ_inner.factory := by
              have := star_preserves_factory P (EvalCmd P) h_body_run
              simpa [Config.getEnv, Env.outcomeConfig] using this
            have h2 : ρ_tgt.factory = ρ_inner_tgt.factory := by
              have := star_preserves_factory P (EvalCmd P) h_body_tgt
              simpa [Config.getEnv, Env.outcomeConfig] using this
            rw [← h2, h_fac_eq]; exact h1
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
            · rw [ite_eq_left hp]; exact h_inner_fresh t h_suf
            · rw [ite_eq_right hp]
          have h_tgt_fresh_next : SemanticStore.isReserved Q σ ρ_tgt_next.store := by
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
            ih ρ_src_next ρ_tgt_next d_loop h_fail_eq_next h_fac_eq_next h_agree_next hwf_next
              h_src_fresh_next h_tgt_fresh_next h_tgt_init_undef_next next_ent h_guard_next hd_loop_fail hsfirst_next
          have h_block_run : StepStmtStar P (EvalCmd P)
              (.block .none ρ_tgt.store (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt))
              (.terminal ρ_tgt_next) := by
            refine ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) _ _ .none ρ_tgt.store h_body_tail) ?_
            exact .step _ _ _ StepStmt.step_block_done (.refl _)
          have h_run_recurse_stmts : StepStmtStar P (EvalCmd P)
              (.stmts [.loop (.det (HasFvar.mkTypedFvar (HasIdent.ident (P := P) g) HasBool.boolTy)) m
                inv
                (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md] ρ_tgt_next)
              (.seq d ([] : List (Stmt P (Cmd P)))) :=
            .step _ _ _ StepStmt.step_stmts_cons
              (seq_inner_star P (EvalCmd P) _ _ _ h_run_recurse)
          refine ⟨.seq d ([] : List (Stmt P (Cmd P))),
            ReflTrans_Transitive _ _ _ _ h_step_enter
              (ReflTrans_Transitive _ _ _ _
                (ReflTrans_Transitive _ _ _ _
                  (seq_inner_star P (EvalCmd P) _ _ _ h_block_run)
                  (.step _ _ _ StepStmt.step_seq_done (.refl _)))
                h_run_recurse_stmts), ?_⟩
          simpa [Config.getEnv] using hd_fail
        rcases loop_nondet_step_first_inv_fail
            h_loop_stmt hd_loop_fail with
          h_refl | ⟨hrest_next, hlen_next⟩ | ⟨hrest_next, hlen_next⟩
        · have h_inner_fail : ρ_inner.hasFailure = true := by
            simpa [ρ_src_next, Config.getEnv] using h_refl
          have h_inner_tgt_fail : ρ_inner_tgt.hasFailure = true := by
            rw [h_fail_inner]; exact h_inner_fail
          obtain ⟨d'', h_body_tail_fail, hd''_fail⟩ :=
            stmts_prefix_failing_append P
              body' [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]
              ρ_tgt
              (.terminal ρ_inner_tgt) h_body_tgt_term
              (by simpa [Config.getEnv] using h_inner_tgt_fail)
          have h_blk_tgt : StepStmtStar P (EvalCmd P)
              (.block .none ρ_tgt.store (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ρ_tgt))
              (.block .none ρ_tgt.store d'') :=
            block_inner_star P (EvalCmd P) _ _ .none ρ_tgt.store h_body_tail_fail
          refine ⟨.seq (.block .none ρ_tgt.store d'')
            [.loop (.det (HasFvar.mkTypedFvar (HasIdent.ident (P := P) g) HasBool.boolTy)) m inv
              (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md],
            ReflTrans_Transitive _ _ _ _ h_step_enter
              (seq_inner_star P (EvalCmd P) _ _ _ h_blk_tgt), ?_⟩
          simpa [Config.getEnv] using hd''_fail
        · exact step_assemble false (.inl ⟨rfl, hrest_next, by omega⟩)
        · exact step_assemble true (.inr ⟨rfl, hrest_next, by omega⟩)
mutual
/-- Per-statement failing-config engine.  `.cmd` arm replays via
`cmd_replay_agreement_storeAgree`; loop arms supply the `_sa` terminal body
simulation and the `_sa` failing-iteration engine. -/
private theorem nondetElim_stmt_to_fail_gen_sa {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen NondetElim.prefixIte sg).1)
            ∧ (∀ sg, Q (StringGenState.gen NondetElim.prefixLoop sg).1))
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (ρ_src ρ_tgt : Env P) (c : Config P (Cmd P))
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_fac_eq : ρ_tgt.factory = ρ_src.factory)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : SemanticStore.isReserved Q σ ρ_tgt.store)
    (h_tgt_init_undef : ∀ y ∈ Stmt.initVars s, ρ_tgt.store y = none)
    (h_unique : (Stmt.initVars s).Nodup)
    (h_no_writes : (∀ t : String, Q t → HasIdent.ident (P := P) t ∉ (Stmt.definedVars s false ++ Stmt.modifiedVars s)))
    (h_reach : StepStmtStar P (EvalCmd P) (.stmt s ρ_src) c)
    (h_c_fail : c.getEnv.hasFailure = true) :
    ∃ d, StepStmtStar P (EvalCmd P)
        (.stmts (Stmt.nondetElimM s σ).1 ρ_tgt) d
      ∧ d.getEnv.hasFailure = true := by
  by_cases h_ρsrc_fail : ρ_src.hasFailure = true
  · exact ⟨.stmts (Stmt.nondetElimM s σ).1 ρ_tgt, .refl _,
      by simpa [Config.getEnv] using (h_fail_eq.trans h_ρsrc_fail)⟩
  have h_ρsrc_nofail : ρ_src.hasFailure = false := by simpa using h_ρsrc_fail
  match s, h_no_writes, h_tgt_init_undef, h_unique, h_reach with
  | .cmd c0, h_no_writes, h_tgt_init_undef, _, h_reach =>
    have h_no_writes_c : (∀ s : String, Q s → HasIdent.ident (P := P) s ∉ (Cmd.definedVars c0 ++ Cmd.modifiedVars c0)) := by
      have h_dv : Stmt.definedVars (P := P) (.cmd c0) false = Cmd.definedVars c0 := by with_unfolding_all rfl
      have h_mv : Stmt.modifiedVars (P := P) (.cmd c0) = Cmd.modifiedVars c0 := by with_unfolding_all rfl
      rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
    -- `Cmd.definedVars c0 = Stmt.initVars (.cmd c0)`: the cmd replay's init-undef arg.
    have h_tgt_init_undef_c : ∀ x ∈ Cmd.definedVars c0, ρ_tgt.store x = none := by
      have h_dv : Cmd.definedVars c0 = Stmt.initVars (P := P) (.cmd c0) := by
        with_unfolding_all rfl
      rw [h_dv]; exact h_tgt_init_undef
    obtain ⟨cfg0, hstep, hrest⟩ := clean_stmt_first_step h_reach h_c_fail h_ρsrc_nofail
    cases hstep with
    | step_cmd hcmd =>
      rename_i σ' hasAssertFailure
      have h_c_eq := reflTransT_from_terminal P (reflTrans_to_T hrest)
      have h_mid_fail :
          ({ ρ_src with store := σ', hasFailure := ρ_src.hasFailure || hasAssertFailure } : Env P).hasFailure
          = true := by rw [h_c_eq] at h_c_fail; simpa [Config.getEnv] using h_c_fail
      have h_term_src : StepStmtStar P (EvalCmd P) (.stmt (.cmd c0) ρ_src)
          (.terminal ({ ρ_src with store := σ', hasFailure := ρ_src.hasFailure || hasAssertFailure } : Env P)) :=
        .step _ _ _ (StepStmt.step_cmd hcmd) (.refl _)
      obtain ⟨ρ_tgt', h_run, _, h_fail'⟩ :=
        cmd_replay_agreement_storeAgree c0 ρ_src
          ({ ρ_src with store := σ', hasFailure := ρ_src.hasFailure || hasAssertFailure } : Env P) ρ_tgt
          h_fail_eq h_fac_eq h_agree hwf.mono h_tgt_init_undef_c h_term_src
      refine ⟨.terminal ρ_tgt', ?_, by simpa [Config.getEnv, h_fail'] using h_mid_fail⟩
      simp only [Stmt.nondetElimM]
      exact stmt_to_singleton_stmts (.cmd c0) ρ_tgt ρ_tgt' h_run
  | .block lbl bss md, h_no_writes, h_tgt_init_undef, h_unique, h_reach =>
    have h_dv : Stmt.definedVars (P := P) (.block lbl bss md) false = Block.definedVars bss false := by
      rw [Stmt.definedVars]; rfl
    have h_mv : Stmt.modifiedVars (P := P) (.block lbl bss md) = Block.modifiedVars bss := by
      with_unfolding_all rfl
    have h_no_writes_bss : SrcNoGenWrites (P := P) Q bss := by
      show (∀ s : String, Q s → HasIdent.ident (P := P) s ∉ (Block.definedVars bss false ++ Block.modifiedVars bss))
      rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
    have h_tgt_iu_bss : ∀ y ∈ Block.initVars bss, ρ_tgt.store y = none := by
      intro y hy; exact h_tgt_init_undef y (by rw [Stmt.initVars_block]; exact hy)
    have h_unique_bss : (Block.initVars bss).Nodup := by
      rw [Stmt.initVars_block] at h_unique; exact h_unique
    obtain ⟨cfg0, hstep, hrest⟩ := clean_stmt_first_step h_reach h_c_fail h_ρsrc_nofail
    cases hstep with
    | step_block =>
      have ⟨d_body, h_body_run, hd_body_fail⟩ :=
        block_reaches_failing' P hrest h_c_fail
      obtain ⟨d_tgt, h_run_tgt, hd_tgt_fail⟩ :=
        nondetElim_to_fail_gen_sa hQgen bss σ ρ_src ρ_tgt d_body
          h_fail_eq h_fac_eq h_agree hwf
          h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_bss h_unique_bss h_no_writes_bss
          h_body_run hd_body_fail
      rw [Stmt.nondetElimM_block_out]
      have h_block_stmt : StepStmtStar P (EvalCmd P)
          (.stmt (.block lbl (Block.nondetElimM bss σ).1 md) ρ_tgt)
          (.block (some lbl) ρ_tgt.store d_tgt) :=
        .step _ _ _ StepStmt.step_block
          (block_inner_star P (EvalCmd P) _ _ (some lbl) ρ_tgt.store h_run_tgt)
      exact stmt_to_singleton_stmts_fail
        (.block lbl (Block.nondetElimM bss σ).1 md) ρ_tgt
        (.block (some lbl) ρ_tgt.store d_tgt) h_block_stmt
        (by simpa [Config.getEnv] using hd_tgt_fail)
  | .ite (.det e) tss ess md, h_no_writes, h_tgt_init_undef, h_unique, h_reach =>
    have h_dv : Stmt.definedVars (P := P) (.ite (.det e) tss ess md) false
        = Block.definedVars tss false ++ Block.definedVars ess false := by
      rw [Stmt.definedVars]; rfl
    have h_mv : Stmt.modifiedVars (P := P) (.ite (.det e) tss ess md)
        = Block.modifiedVars tss ++ Block.modifiedVars ess := rfl
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
    obtain ⟨cfg0, hstep, hrest⟩ := clean_stmt_first_step h_reach h_c_fail h_ρsrc_nofail
    cases hstep with
    | step_ite_true h_cond =>
      have h_no_writes_t : SrcNoGenWrites (P := P) Q tss := by
        intro t hQ hmem
        rcases List.mem_append.mp hmem with hd | hm
        · exact h_no_writes t hQ (by rw [h_dv]; exact List.mem_append_left _ (List.mem_append_left _ hd))
        · exact h_no_writes t hQ (by rw [h_mv]; exact List.mem_append_right _ (List.mem_append_left _ hm))
      obtain ⟨d_inner, h_inner_fail, hd_inner_fail, _⟩ :=
        blockT_none_reaches_failing' P (reflTrans_to_T hrest) h_c_fail
      obtain ⟨d_tgt, h_run_tgt, hd_tgt_fail⟩ :=
        nondetElim_to_fail_gen_sa hQgen tss σ ρ_src ρ_tgt d_inner
          h_fail_eq h_fac_eq h_agree hwf
          h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_t h_unique_t h_no_writes_t
          (reflTransT_to_prop h_inner_fail) hd_inner_fail
      have h_cond_t : P.eval ρ_tgt.factory ρ_tgt.store e = some HasBool.tt := by
        rw [h_fac_eq]
        exact hwf.mono e HasBool.tt ρ_src.store ρ_tgt.store
          (storeAgreement_supplies_mono_premise ρ_src.store ρ_tgt.store h_agree) h_cond
      rw [Stmt.nondetElimM_ite_det_out]
      refine ⟨.seq (.block .none ρ_tgt.store d_tgt) [], ?_,
        by simpa [Config.getEnv] using hd_tgt_fail⟩
      refine .step _ _ _ StepStmt.step_stmts_cons ?_
      exact seq_inner_star P (EvalCmd P) _ _ []
        (.step _ _ _ (StepStmt.step_ite_true h_cond_t)
          (block_inner_star P (EvalCmd P) _ _ .none ρ_tgt.store h_run_tgt))
    | step_ite_false h_cond =>
      have h_no_writes_e : SrcNoGenWrites (P := P) Q ess := by
        intro t hQ hmem
        rcases List.mem_append.mp hmem with hd | hm
        · exact h_no_writes t hQ (by rw [h_dv]; exact List.mem_append_left _ (List.mem_append_right _ hd))
        · exact h_no_writes t hQ (by rw [h_mv]; exact List.mem_append_right _ (List.mem_append_right _ hm))
      have h_wf₁ : StringGenState.WF (Block.nondetElimM tss σ).2 :=
        (Block.nondetElimM_genStep tss σ).wf_mono h_wf_gen
      have h_tgt_fresh₁ : SemanticStore.isReserved Q (Block.nondetElimM tss σ).2 ρ_tgt.store :=
        SemanticStore.isReserved.mono (Block.nondetElimM_genStep tss σ) h_tgt_fresh
      obtain ⟨d_inner, h_inner_fail, hd_inner_fail, _⟩ :=
        blockT_none_reaches_failing' P (reflTrans_to_T hrest) h_c_fail
      obtain ⟨d_tgt, h_run_tgt, hd_tgt_fail⟩ :=
        nondetElim_to_fail_gen_sa hQgen ess (Block.nondetElimM tss σ).2 ρ_src ρ_tgt d_inner
          h_fail_eq h_fac_eq h_agree hwf
          h_wf₁ h_src_fresh h_tgt_fresh₁ h_tgt_iu_e h_unique_e h_no_writes_e
          (reflTransT_to_prop h_inner_fail) hd_inner_fail
      have h_cond_t : P.eval ρ_tgt.factory ρ_tgt.store e = some HasBool.ff := by
        rw [h_fac_eq]
        exact hwf.mono e HasBool.ff ρ_src.store ρ_tgt.store
          (storeAgreement_supplies_mono_premise ρ_src.store ρ_tgt.store h_agree) h_cond
      rw [Stmt.nondetElimM_ite_det_out]
      refine ⟨.seq (.block .none ρ_tgt.store d_tgt) [], ?_,
        by simpa [Config.getEnv] using hd_tgt_fail⟩
      refine .step _ _ _ StepStmt.step_stmts_cons ?_
      exact seq_inner_star P (EvalCmd P) _ _ []
        (.step _ _ _ (StepStmt.step_ite_false h_cond_t)
          (block_inner_star P (EvalCmd P) _ _ .none ρ_tgt.store h_run_tgt))
  | .ite .nondet tss ess md, h_no_writes, h_tgt_init_undef, h_unique, h_reach =>
    rcases hgen : StringGenState.gen NondetElim.prefixIte σ with ⟨g, σ₁⟩
    have h_g_gen : Q g := by have := hQgen.1 σ; rw [hgen] at this; exact this
    have h_tgt_g_none : ρ_tgt.store (HasIdent.ident (P := P) g) = none := by
      have := SemanticStore.isReserved.gen_slot_none NondetElim.prefixIte
        h_tgt_fresh h_wf_gen (hQgen.1 σ)
      rw [hgen] at this; exact this
    have hwf_var_t : WellFormedSemanticEvalVar ρ_tgt.factory := h_fac_eq ▸ hwf.var
    have hwf_def_t : WellFormedSemanticEvalMono ρ_tgt.factory := h_fac_eq ▸ hwf.mono
    have h_step01 : StringGenState.GenStep σ σ₁ := by
      have := StringGenState.GenStep.of_gen NondetElim.prefixIte σ; rw [hgen] at this; exact this
    have h_wf₁ : StringGenState.WF σ₁ := h_step01.wf_mono h_wf_gen
    have h_dv : Stmt.definedVars (P := P) (.ite .nondet tss ess md) false
        = Block.definedVars tss false ++ Block.definedVars ess false := by
      rw [Stmt.definedVars]; rfl
    have h_mv : Stmt.modifiedVars (P := P) (.ite .nondet tss ess md)
        = Block.modifiedVars tss ++ Block.modifiedVars ess := rfl
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
    obtain ⟨cfg0, hstep, hrest⟩ := clean_stmt_first_step h_reach h_c_fail h_ρsrc_nofail
    cases hstep with
    | step_ite_nondet_true =>
      have h_off_g : StoreAgreement ρ_src.store
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) :=
        storeAgreement_storeWith _ _ _ _ h_agree (h_src_fresh g h_g_gen)
      have h_fresh_g : SemanticStore.isReserved Q σ₁
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) := by
        have := SemanticStore.isReserved.storeWith_gen (P := P)
          NondetElim.prefixIte HasBool.tt h_tgt_fresh
        rw [hgen] at this; exact this
      obtain ⟨d_inner, h_inner_fail, hd_inner_fail, _⟩ :=
        blockT_none_reaches_failing' P (reflTrans_to_T hrest) h_c_fail
      obtain ⟨d_tgt, h_run_tgt, hd_tgt_fail⟩ :=
        nondetElim_to_fail_gen_sa hQgen tss σ₁
          ρ_src ({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P) d_inner
          h_fail_eq h_fac_eq h_off_g hwf
          h_wf₁ h_src_fresh h_fresh_g (h_tgt_iu_t HasBool.tt) h_unique_t h_no_writes_t
          (reflTransT_to_prop h_inner_fail) hd_inner_fail
      rw [Stmt.nondetElimM_ite_nondet_out]; simp only [hgen]
      exact step_ndelim_ite_prefix_fail true (HasIdent.ident (P := P) g)
        (Block.nondetElimM tss σ₁).1 (Block.nondetElimM ess (Block.nondetElimM tss σ₁).2).1 md
        ρ_tgt d_tgt h_tgt_g_none hwf_var_t hwf_def_t h_run_tgt hd_tgt_fail
    | step_ite_nondet_false =>
      have h_step12 : StringGenState.GenStep σ₁ (Block.nondetElimM tss σ₁).2 :=
        Block.nondetElimM_genStep tss σ₁
      have h_wf₂ : StringGenState.WF (Block.nondetElimM tss σ₁).2 := h_step12.wf_mono h_wf₁
      have h_off_g : StoreAgreement ρ_src.store
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) :=
        storeAgreement_storeWith _ _ _ _ h_agree (h_src_fresh g h_g_gen)
      have h_fresh_g1 : SemanticStore.isReserved Q σ₁
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) := by
        have := SemanticStore.isReserved.storeWith_gen (P := P)
          NondetElim.prefixIte HasBool.ff h_tgt_fresh
        rw [hgen] at this; exact this
      have h_fresh_g : SemanticStore.isReserved Q (Block.nondetElimM tss σ₁).2
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) :=
        SemanticStore.isReserved.mono h_step12 h_fresh_g1
      obtain ⟨d_inner, h_inner_fail, hd_inner_fail, _⟩ :=
        blockT_none_reaches_failing' P (reflTrans_to_T hrest) h_c_fail
      obtain ⟨d_tgt, h_run_tgt, hd_tgt_fail⟩ :=
        nondetElim_to_fail_gen_sa hQgen ess (Block.nondetElimM tss σ₁).2
          ρ_src ({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff } : Env P) d_inner
          h_fail_eq h_fac_eq h_off_g hwf
          h_wf₂ h_src_fresh h_fresh_g (h_tgt_iu_e HasBool.ff) h_unique_e h_no_writes_e
          (reflTransT_to_prop h_inner_fail) hd_inner_fail
      rw [Stmt.nondetElimM_ite_nondet_out]; simp only [hgen]
      exact step_ndelim_ite_prefix_fail false (HasIdent.ident (P := P) g)
        (Block.nondetElimM tss σ₁).1 (Block.nondetElimM ess (Block.nondetElimM tss σ₁).2).1 md
        ρ_tgt d_tgt h_tgt_g_none hwf_var_t hwf_def_t h_run_tgt hd_tgt_fail
  | .loop (.det e) m inv body md, h_no_writes, h_tgt_init_undef, h_unique, h_reach =>
    have h_no_writes_body : SrcNoGenWrites (P := P) Q body := by
      have h_dv : Stmt.definedVars (P := P) (.loop (.det e) m inv body md) false
          = Block.definedVars body false := by
        simp only [Stmt.definedVars, Bool.false_eq_true, ite_false]
      have h_mv : Stmt.modifiedVars (P := P) (.loop (.det e) m inv body md)
          = Block.modifiedVars body := rfl
      show (∀ s : String, Q s → HasIdent.ident (P := P) s ∉ (Block.definedVars body false ++ Block.modifiedVars body))
      rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
    have h_tgt_iu_body : ∀ y ∈ Block.initVars body, ρ_tgt.store y = none := by
      intro y hy; exact h_tgt_init_undef y (by rw [Stmt.initVars_loop]; exact hy)
    have h_unique_body : (Block.initVars body).Nodup := by
      rw [Stmt.initVars_loop] at h_unique; exact h_unique
    have h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
        ρb_tgt.hasFailure = ρb_src.hasFailure →
        ρb_tgt.factory = ρb_src.factory →
        StoreAgreement ρb_src.store ρb_tgt.store →
        WellFormedSemanticEval ρb_src.factory → StringGenState.WF σ →
        (∀ t, Q t → ρb_src.store (HasIdent.ident (P := P) t) = none) →
        SemanticStore.isReserved Q σ ρb_tgt.store →
        (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
        StepStmtStar P (EvalCmd P) (.stmts body ρb_src) (Env.outcomeConfig oc_b ρb') →
        (∀ t, Q t → ρb'.store (HasIdent.ident (P := P) t) = none)
          ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P)
              (.stmts (Block.nondetElimM body σ).1 ρb_tgt) (Env.outcomeConfig oc_b ρb_out)
            ∧ StoreAgreement ρb'.store ρb_out.store ∧ ρb_out.hasFailure = ρb'.hasFailure
            ∧ SemanticStore.isReserved Q (Block.nondetElimM body σ).2 ρb_out.store :=
      fun oc_b ρb_src ρb' ρb_tgt h_fl h_fac_b h_ag hwf hwfg hsf htf htiu hrun =>
        nondetElim_simulation_gen_sa hQgen body σ ρb_src ρb' ρb_tgt
          h_fl h_fac_b h_ag hwf hwfg hsf htf htiu h_unique_body
          h_no_writes_body oc_b hrun
    have h_body_sim_fail : ∀ (ρb_src ρb_tgt : Env P) (d : Config P (Cmd P)),
        ρb_tgt.hasFailure = ρb_src.hasFailure →
        ρb_tgt.factory = ρb_src.factory →
        StoreAgreement ρb_src.store ρb_tgt.store →
        WellFormedSemanticEval ρb_src.factory → StringGenState.WF σ →
        (∀ t, Q t → ρb_src.store (HasIdent.ident (P := P) t) = none) →
        SemanticStore.isReserved Q σ ρb_tgt.store →
        (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
        StepStmtStar P (EvalCmd P) (.stmts body ρb_src) d → d.getEnv.hasFailure = true →
        ∃ d', StepStmtStar P (EvalCmd P) (.stmts (Block.nondetElimM body σ).1 ρb_tgt) d'
          ∧ d'.getEnv.hasFailure = true :=
      fun ρb_src ρb_tgt d h_fl h_fac_b h_ag hwf hwfg hsf htf htiu hrun hdfail =>
        nondetElim_to_fail_gen_sa hQgen body σ ρb_src ρb_tgt d
          h_fl h_fac_b h_ag hwf hwfg hsf htf htiu h_unique_body
          h_no_writes_body hrun hdfail
    obtain ⟨d_tgt, h_run_tgt, hd_tgt_fail⟩ :=
      nondetElim_loop_det_to_fail_iteration_sa e m body (Block.nondetElimM body σ).1 md σ
        (Block.nondetElimM body σ).2
        h_body_sim h_body_sim_fail ρ_src ρ_tgt c (reflTrans_to_T h_reach).len
        h_fail_eq h_fac_eq h_agree hwf
        h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_body (reflTrans_to_T h_reach) h_c_fail (Nat.le_refl _)
    rw [Stmt.nondetElimM_loop_det_out]
    refine ⟨.seq d_tgt [], ?_, by simpa [Config.getEnv] using hd_tgt_fail⟩
    refine .step _ _ _ StepStmt.step_stmts_cons ?_
    exact seq_inner_star P (EvalCmd P) _ _ [] h_run_tgt
  | .loop .nondet m inv body md, h_no_writes, h_tgt_init_undef, h_unique, h_reach =>
    have h_no_writes_body : SrcNoGenWrites (P := P) Q body := by
      have h_dv : Stmt.definedVars (P := P) (.loop .nondet m inv body md) false
          = Block.definedVars body false := by
        simp only [Stmt.definedVars, Bool.false_eq_true, ite_false]
      have h_mv : Stmt.modifiedVars (P := P) (.loop .nondet m inv body md)
          = Block.modifiedVars body := rfl
      show (∀ s : String, Q s → HasIdent.ident (P := P) s ∉ (Block.definedVars body false ++ Block.modifiedVars body))
      rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
    rcases hgen : StringGenState.gen NondetElim.prefixLoop σ with ⟨g, σ₁⟩
    have h_g_gen : Q g := by have := hQgen.2 σ; rw [hgen] at this; exact this
    have h_step01 : StringGenState.GenStep σ σ₁ := by
      have := StringGenState.GenStep.of_gen NondetElim.prefixLoop σ; rw [hgen] at this; exact this
    have h_wf₁ : StringGenState.WF σ₁ := h_step01.wf_mono h_wf_gen
    have h_g_in : g ∈ σ₁.stringGens := by
      have h := StringGenState.stringGens_gen NondetElim.prefixLoop σ
      rw [hgen] at h; rw [h]; exact List.mem_cons_self
    have h_g_nowrite := nondetElimM_not_writes_gen body σ₁ h_wf₁ g h_g_in
      (fun hc => h_no_writes_body g h_g_gen (List.mem_append_left _ hc))
      (fun hc => h_no_writes_body g h_g_gen (List.mem_append_right _ hc))
    have h_tgt_g_none : ρ_tgt.store (HasIdent.ident (P := P) g) = none := by
      have := SemanticStore.isReserved.gen_slot_none NondetElim.prefixLoop
        h_tgt_fresh h_wf_gen (hQgen.2 σ)
      rw [hgen] at this; exact this
    have hwf_var_t : WellFormedSemanticEvalVar ρ_tgt.factory := h_fac_eq ▸ hwf.var
    have h_unique_body : (Block.initVars body).Nodup := by
      rw [Stmt.initVars_loop] at h_unique; exact h_unique
    -- Body init-targets are source-shaped, distinct from gen guard `g`; the
    -- guard SemanticStore.update leaves each body init-target's slot untouched.
    have h_tgt_iu_body : ∀ (v : P.Expr) (y : P.Ident), y ∈ Block.initVars body →
        (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) v) y = none := by
      intro v y hy
      have h_y_dv : y ∈ Stmt.definedVars (P := P) (.loop .nondet m inv body md) false := by
        rw [Stmt.definedVars]; simp only [Bool.false_eq_true, ite_false]
        exact hy
      have h_y_ne : y ≠ HasIdent.ident (P := P) g := fun h_eq =>
        h_no_writes g h_g_gen (h_eq ▸ List.mem_append_left _ h_y_dv)
      have h_y_none : ρ_tgt.store y = none := h_tgt_init_undef y
        (by rw [Stmt.initVars_loop]; exact hy)
      simp only [SemanticStore.update, h_y_ne]; exact h_y_none
    have h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
        ρb_tgt.hasFailure = ρb_src.hasFailure →
        ρb_tgt.factory = ρb_src.factory →
        StoreAgreement ρb_src.store ρb_tgt.store →
        WellFormedSemanticEval ρb_src.factory → StringGenState.WF σ₁ →
        (∀ t, Q t → ρb_src.store (HasIdent.ident (P := P) t) = none) →
        SemanticStore.isReserved Q σ₁ ρb_tgt.store →
        (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
        StepStmtStar P (EvalCmd P) (.stmts body ρb_src) (Env.outcomeConfig oc_b ρb') →
        (∀ t, Q t → ρb'.store (HasIdent.ident (P := P) t) = none)
          ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P)
              (.stmts (Block.nondetElimM body σ₁).1 ρb_tgt) (Env.outcomeConfig oc_b ρb_out)
            ∧ StoreAgreement ρb'.store ρb_out.store ∧ ρb_out.hasFailure = ρb'.hasFailure
            ∧ SemanticStore.isReserved Q (Block.nondetElimM body σ₁).2 ρb_out.store :=
      fun oc_b ρb_src ρb' ρb_tgt h_fl h_fac_b h_ag hwf hwfg hsf htf htiu hrun =>
        nondetElim_simulation_gen_sa hQgen body σ₁ ρb_src ρb' ρb_tgt
          h_fl h_fac_b h_ag hwf hwfg hsf htf htiu h_unique_body
          h_no_writes_body oc_b hrun
    have h_body_sim_fail : ∀ (ρb_src ρb_tgt : Env P) (d : Config P (Cmd P)),
        ρb_tgt.hasFailure = ρb_src.hasFailure →
        ρb_tgt.factory = ρb_src.factory →
        StoreAgreement ρb_src.store ρb_tgt.store →
        WellFormedSemanticEval ρb_src.factory → StringGenState.WF σ₁ →
        (∀ t, Q t → ρb_src.store (HasIdent.ident (P := P) t) = none) →
        SemanticStore.isReserved Q σ₁ ρb_tgt.store →
        (∀ y ∈ Block.initVars body, ρb_tgt.store y = none) →
        StepStmtStar P (EvalCmd P) (.stmts body ρb_src) d → d.getEnv.hasFailure = true →
        ∃ d', StepStmtStar P (EvalCmd P) (.stmts (Block.nondetElimM body σ₁).1 ρb_tgt) d'
          ∧ d'.getEnv.hasFailure = true :=
      fun ρb_src ρb_tgt d h_fl h_fac_b h_ag hwf hwfg hsf htf htiu hrun hdfail =>
        nondetElim_to_fail_gen_sa hQgen body σ₁ ρb_src ρb_tgt d
          h_fl h_fac_b h_ag hwf hwfg hsf htf htiu h_unique_body
          h_no_writes_body hrun hdfail
    have hstarT := reflTrans_to_T h_reach
    have h_finish : ∀ (entering : Bool) (b : P.Expr)
        (_h_b : b = (if entering then HasBool.tt else HasBool.ff))
        (h_first :
          (entering = false ∧ ∃ (hr : ReflTransT (StepStmt P (EvalCmd P))
              (.terminal ρ_src) c),
            hr.len ≤ hstarT.len) ∨
          (entering = true ∧ ∃ (hr : ReflTransT (StepStmt P (EvalCmd P))
              (.seq (.block .none ρ_src.store (.stmts body ρ_src))
                [.loop .nondet m inv body md]) c),
            hr.len ≤ hstarT.len)),
        ∃ d, StepStmtStar P (EvalCmd P)
            (.stmts (Stmt.nondetElimM (.loop .nondet m inv body md) σ).1 ρ_tgt) d
          ∧ d.getEnv.hasFailure = true := by
      intro entering b h_b h_first
      have hval_b : HasVal.valueOfTy ρ_tgt.factory b HasBool.boolTy := by
        rw [h_b]; split
        · exact (HasBool.boolIsValOfTy ρ_tgt.factory).1
        · exact (HasBool.boolIsValOfTy ρ_tgt.factory).2
      have h_off_g : StoreAgreement ρ_src.store
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) b) :=
        storeAgreement_storeWith _ _ _ _ h_agree (h_src_fresh g h_g_gen)
      have h_fresh_g : SemanticStore.isReserved Q σ₁
          (SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) b) := by
        have := SemanticStore.isReserved.storeWith_gen (P := P) NondetElim.prefixLoop b h_tgt_fresh
        rw [hgen] at this; exact this
      have h_guard_def : (({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) b } : Env P).store)
          (HasIdent.ident (P := P) g) = some (if entering then HasBool.tt else HasBool.ff) := by
        subst h_b; simp [SemanticStore.update]
      obtain ⟨d_tgt, h_loop_run, hd_tgt_fail⟩ :=
        nondetElim_loop_nondet_to_fail_iteration_sa g m body (Block.nondetElimM body σ₁).1 md σ₁
          (Block.nondetElimM body σ₁).2
          h_body_sim h_body_sim_fail h_g_gen h_g_nowrite.1 h_g_nowrite.2 ρ_src
          ({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) b } : Env P)
          c hstarT.len h_fail_eq h_fac_eq h_off_g hwf
          h_wf₁ h_src_fresh h_fresh_g (h_tgt_iu_body b) entering h_guard_def h_c_fail h_first
      rw [Stmt.nondetElimM_loop_nondet_out]; simp only [hgen]
      have h_init : StepStmtStar P (EvalCmd P)
          (.stmt (.cmd (HasInit.init (HasIdent.ident (P := P) g) HasBool.boolTy .nondet md)) ρ_tgt)
          (.terminal ({ ρ_tgt with store := SemanticStore.update ρ_tgt.store (HasIdent.ident (P := P) g) b } : Env P)) :=
        step_init_havoc_to (HasIdent.ident (P := P) g) HasBool.boolTy b md ρ_tgt
          h_tgt_g_none hval_b hwf_var_t
      refine ⟨.seq d_tgt ([] : List (Stmt P (Cmd P))), ?_, by simpa [Config.getEnv] using hd_tgt_fail⟩
      refine ReflTrans_Transitive _ _ _ _
        (stmts_cons_step P (EvalCmd P) _ _ ρ_tgt _ h_init) ?_
      exact .step _ _ _ StepStmt.step_stmts_cons (seq_inner_star P (EvalCmd P) _ _ [] h_loop_run)
    rcases loop_nondet_step_first_inv_fail hstarT h_c_fail with
      h_refl | ⟨hrest, hl⟩ | ⟨hrest, hl⟩
    · exact absurd h_refl h_ρsrc_fail
    · exact h_finish false HasBool.ff (by simp) (.inl ⟨rfl, hrest, Nat.le_of_lt hl⟩)
    · exact h_finish true HasBool.tt (by simp) (.inr ⟨rfl, hrest, Nat.le_of_lt hl⟩)
  | .exit lbl md, _, _, _, h_reach =>
    exfalso
    obtain ⟨cfg0, hstep, hrest⟩ := clean_stmt_first_step h_reach h_c_fail h_ρsrc_nofail
    cases hstep with
    | step_exit =>
      have h_c_eq : c = .exiting lbl ρ_src :=
        reflTransT_from_exiting P (reflTrans_to_T hrest)
      rw [h_c_eq] at h_c_fail
      exact absurd (by simpa [Config.getEnv] using h_c_fail) h_ρsrc_fail
  | .typeDecl t md, _, _, _, h_reach =>
    exfalso
    obtain ⟨cfg0, hstep, hrest⟩ := clean_stmt_first_step h_reach h_c_fail h_ρsrc_nofail
    cases hstep with
    | step_typeDecl =>
      have h_c_eq : c = .terminal ρ_src :=
        reflTransT_from_terminal P (reflTrans_to_T hrest)
      rw [h_c_eq] at h_c_fail
      exact absurd (by simpa [Config.getEnv] using h_c_fail) h_ρsrc_fail
  termination_by sizeOf s

/-- Block failing-config engine.  Cons case B (head terminates, tail fails)
advances the relation through `nondetElim_stmt_gen_sa`, then re-establishes the
tail's init-target undefinedness at the advanced target via
`block_run_terminal_preserves_none_of_not_definedVars` + the `Q`-keyed output
`initVars`-classification + head/tail disjointness. -/
private theorem nondetElim_to_fail_gen_sa {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen NondetElim.prefixIte sg).1)
            ∧ (∀ sg, Q (StringGenState.gen NondetElim.prefixLoop sg).1))
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (ρ_src ρ_tgt : Env P) (c : Config P (Cmd P))
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_fac_eq : ρ_tgt.factory = ρ_src.factory)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ_src.factory)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : SemanticStore.isReserved Q σ ρ_tgt.store)
    (h_tgt_init_undef : ∀ y ∈ Block.initVars ss, ρ_tgt.store y = none)
    (h_unique : (Block.initVars ss).Nodup)
    (h_no_writes : SrcNoGenWrites (P := P) Q ss)
    (h_reach : StepStmtStar P (EvalCmd P) (.stmts ss ρ_src) c)
    (h_c_fail : c.getEnv.hasFailure = true) :
    ∃ d, StepStmtStar P (EvalCmd P)
        (.stmts (Block.nondetElimM ss σ).1 ρ_tgt) d
      ∧ d.getEnv.hasFailure = true := by
  by_cases h_ρsrc_fail : ρ_src.hasFailure = true
  · exact ⟨.stmts (Block.nondetElimM ss σ).1 ρ_tgt, .refl _,
      by simpa [Config.getEnv] using (h_fail_eq.trans h_ρsrc_fail)⟩
  have h_ρsrc_nofail : ρ_src.hasFailure = false := by simpa using h_ρsrc_fail
  match ss, h_no_writes, h_tgt_init_undef, h_unique with
  | [], _, _, _ =>
    exfalso
    have h_c_env : c.getEnv = ρ_src := by
      match h_reach with
      | .refl _ => rfl
      | .step _ _ _ hstep hrest =>
        cases hstep with
        | step_stmts_nil =>
          have := reflTransT_from_terminal P (reflTrans_to_T hrest)
          rw [this]; rfl
    rw [h_c_env] at h_c_fail
    exact absurd (by simpa [Config.getEnv] using h_c_fail) h_ρsrc_fail
  | s :: rest, h_no_writes, h_tgt_init_undef, h_unique =>
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
    rcases stmts_cons_reaches_failing' P (reflTrans_to_T h_reach) h_c_fail with
      hA | hB
    · -- CASE A: the head statement already fails.
      obtain ⟨d_head, h_head_run, hd_head_fail⟩ := hA
      obtain ⟨d_tgt, h_run_tgt, hd_tgt_fail⟩ :=
        nondetElim_stmt_to_fail_gen_sa hQgen s σ ρ_src ρ_tgt d_head
          h_fail_eq h_fac_eq h_agree hwf
          h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_s h_unique_s h_no_writes_s
          h_head_run hd_head_fail
      exact stmts_prefix_failing_append P
        (Stmt.nondetElimM s σ).1 (Block.nondetElimM rest (Stmt.nondetElimM s σ).2).1
        ρ_tgt d_tgt h_run_tgt hd_tgt_fail
    · -- CASE B: the head terminates at ρ_mid (clean), then `rest` fails.  Use the
      -- *terminal* head simulation to advance the relation, then recurse on `rest`.
      obtain ⟨ρ_mid, d_rest, h_head_term, h_rest_run, hd_rest_fail⟩ := hB
      obtain ⟨h_mid_fresh, ρ_mid_tgt, h_s_tgt, h_off_mid, h_fail_mid, h_fresh_mid⟩ :=
        nondetElim_stmt_gen_sa hQgen s σ ρ_src ρ_mid ρ_tgt
          h_fail_eq h_fac_eq h_agree hwf
          h_wf_gen h_src_fresh h_tgt_fresh h_tgt_iu_s h_unique_s h_no_writes_s none h_head_term
      have h_wf₁ : StringGenState.WF (Stmt.nondetElimM s σ).2 :=
        (Stmt.nondetElimM_genStep s σ).wf_mono h_wf_gen
      have hwf_mid : WellFormedSemanticEval ρ_mid.factory := by
        have h1 : ρ_src.factory = ρ_mid.factory := by
          have := star_preserves_factory P (EvalCmd P) h_head_term
          simpa [Config.getEnv, Env.outcomeConfig] using this
        rw [← h1]; exact hwf
      have h_fac_eq_mid : ρ_mid_tgt.factory = ρ_mid.factory := by
        have h1 : ρ_src.factory = ρ_mid.factory := by
          have := star_preserves_factory P (EvalCmd P) h_head_term
          simpa [Config.getEnv, Env.outcomeConfig] using this
        have h2 : ρ_tgt.factory = ρ_mid_tgt.factory := by
          have := star_preserves_factory P (EvalCmd P) h_s_tgt
          simpa [Config.getEnv, Env.outcomeConfig] using this
        rw [← h2, h_fac_eq]; exact h1
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
        nondetElim_to_fail_gen_sa hQgen rest (Stmt.nondetElimM s σ).2 ρ_mid ρ_mid_tgt d_rest
          h_fail_mid h_fac_eq_mid h_off_mid hwf_mid
          h_wf₁ h_mid_fresh h_fresh_mid h_tgt_iu_rest h_unique_rest h_no_writes_rest
          h_rest_run hd_rest_fail
      exact ⟨d_tgt, ReflTrans_Transitive _ _ _ _
        (stmts_prefix_terminal_append P (EvalCmd P) _ _ ρ_tgt ρ_mid_tgt h_s_tgt)
        h_run_tgt, hd_tgt_fail⟩
  termination_by sizeOf ss
end

/-- **Failing-config forward simulation (gen-parametric top form).** Every
reachable *failing* source configuration of `ss` is matched by a reachable
failing configuration of `Block.nondetElim ss` (same `ρ₀`, no endpoint demand).
Instantiates the gen-level `_to_fail` at `ρ_tgt = ρ₀` and the empty generator. -/
private theorem nondetElim_simulation_to_fail {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen NondetElim.prefixIte sg).1)
            ∧ (∀ sg, Q (StringGenState.gen NondetElim.prefixLoop sg).1))
    (ss : List (Stmt P (Cmd P))) (ρ₀ : Env P) (c : Config P (Cmd P))
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_no_gen_suffix : ∀ s, Q s → ρ₀.store (HasIdent.ident (P := P) s) = none)
    (h_no_writes : SrcNoGenWrites (P := P) Q ss)
    (h_store_inits : ∀ y ∈ Block.initVars ss, ρ₀.store y = none)
    (h_unique : Block.uniqueInits ss)
    (h_reach : StepStmtStar P (EvalCmd P) (.stmts ss ρ₀) c)
    (h_c_fail : c.getEnv.hasFailure = true) :
    ∃ d, StepStmtStar P (EvalCmd P)
        (.stmts (Block.nondetElim ss) ρ₀) d
      ∧ d.getEnv.hasFailure = true := by
  have h_tgt_fresh : SemanticStore.isReserved Q StringGenState.emp ρ₀.store := by
    intro s h_suf _; exact h_no_gen_suffix s h_suf
  exact nondetElim_to_fail_gen_sa hQgen ss StringGenState.emp ρ₀ ρ₀ c
    rfl rfl (StoreAgreement.refl _) hwf
    StringGenState.wf_emp h_no_gen_suffix h_tgt_fresh h_store_inits h_unique h_no_writes h_reach h_c_fail

/-- **`Block.nondetElim` failing-config preservation (at `Q := NondetElim.isGeneratedName`).**  A
reachable failing source configuration of `ss` is matched by a reachable failing
configuration of `Block.nondetElim ss`, with no terminal/exiting endpoint
required.  This is the `_to_fail` sibling of `nondetElim_sound_kind`; the
`Env.varsUndefined`/`SrcNoGenWrites` preconditions are exactly those the
terminal soundness theorems already consume, so it composes into the
structured-pass failing bridge identically. -/
theorem nondetElim_to_fail {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    (ss : List (Stmt P (Cmd P))) (ρ₀ : Env P) (c : Config P (Cmd P))
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_no_gen_suffix : Env.varsUndefined (P := P) NondetElim.isGeneratedName ρ₀)
    (h_no_writes : SrcNoGenWrites (P := P) NondetElim.isGeneratedName ss)
    (h_store_inits : ∀ y ∈ Block.initVars ss, ρ₀.store y = none)
    (h_unique : Block.uniqueInits ss)
    (h_reach : StepStmtStar P (EvalCmd P) (.stmts ss ρ₀) c)
    (h_c_fail : c.getEnv.hasFailure = true) :
    ∃ d, StepStmtStar P (EvalCmd P)
        (.stmts (Block.nondetElim ss) ρ₀) d
      ∧ d.getEnv.hasFailure = true :=
  nondetElim_simulation_to_fail (Q := NondetElim.isGeneratedName) NondetElim.isGeneratedName_gen
    ss ρ₀ c hwf
    (Env.varsUndefined_iff.mp h_no_gen_suffix) h_no_writes h_store_inits h_unique h_reach h_c_fail

/-- Compositional-input failing-config simulation: a reachable failing source
config of `ss` (run from `ρ₀`) is matched by a reachable failing config of
`Block.nondetElim ss` run from an *overapproximating* target env `ρ_tgt`
(`StoreAgreement ρ₀.store ρ_tgt.store`).  Thin forwarder to
`nondetElim_to_fail_gen_sa` at `σ := .emp`, `Q := NondetElim.isGeneratedName`. -/
theorem nondetElim_to_fail_compositional {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P]
    [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P]
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ_tgt : Env P) (c : Config P (Cmd P))
    (h_fail_eq : ρ_tgt.hasFailure = ρ₀.hasFailure)
    (h_fac_eq : ρ_tgt.factory = ρ₀.factory)
    (h_agree : StoreAgreement ρ₀.store ρ_tgt.store)
    (hwf : WellFormedSemanticEval ρ₀.factory)
    (h_src_no_gen : Env.varsUndefined (P := P) NondetElim.isGeneratedName ρ₀)
    (h_tgt_no_gen : Env.varsUndefined (P := P) NondetElim.isGeneratedName ρ_tgt)
    (h_tgt_inits : ∀ y ∈ Block.initVars ss, ρ_tgt.store y = none)
    (h_no_writes : SrcNoGenWrites (P := P) NondetElim.isGeneratedName ss)
    (h_unique : Block.uniqueInits ss)
    (h_reach : StepStmtStar P (EvalCmd P) (.stmts ss ρ₀) c)
    (h_c_fail : c.getEnv.hasFailure = true) :
    ∃ d, StepStmtStar P (EvalCmd P)
        (.stmts (Block.nondetElim ss) ρ_tgt) d
      ∧ d.getEnv.hasFailure = true := by
  have h_tgt_fresh : SemanticStore.isReserved NondetElim.isGeneratedName
      StringGenState.emp ρ_tgt.store := by
    intro s h_suf _; exact Env.varsUndefined_apply h_tgt_no_gen s h_suf
  exact nondetElim_to_fail_gen_sa NondetElim.isGeneratedName_gen ss StringGenState.emp ρ₀ ρ_tgt c
    h_fail_eq h_fac_eq h_agree hwf
    StringGenState.wf_emp (Env.varsUndefined_iff.mp h_src_no_gen) h_tgt_fresh h_tgt_inits h_unique h_no_writes
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

/-! ## `nondetElim` per-pass event-trace overapproximation instance

The pass's `OverapproximatesTracesUptoWhen` instance uses the event-trace block
language with `EvalCmdE P`. Target-only registers are generated guards;
`NETraceRel` relates same-kind event snapshots with environment extension,
free-variable store agreement, and evaluator well-formedness. Its
`toExtendsEnv` theorem recovers the weaker `TraceExtendsEnv` relation.
`Env.ExtendsWith` relates final environments. Nondeterministic loops are
represented by separate preheader, body, and latch states so the source loop
choice selects the corresponding silent target guard update. -/
section NondetElimOverapprox
open Specification Specification.Transform Imperative.Logic

namespace NondetElimTrace

/-! ### Classified registers and leaf invariants -/

/-- Target-only registers introduced by `nondetElim`: the identifiers of the
generated guard names. -/
abbrev NdExtra {P : PureExpr} [HasIdent P] : P.Ident → Prop :=
  IdentOfStringKind (P := P) NondetElim.isGeneratedName

/-- Event arguments matched by nondeterminism elimination. Besides the
classified environment extension, the stores agree on the captured condition's
free variables and carry the well-formedness evidence needed by evaluator
congruence. -/
structure NEArgRel {P : PureExpr} [HasVal P] [HasFvars P] [HasIdent P]
    (source target : EventArg P) : Prop where
  envExtends : source.ExtendsEnv (NdExtra (P := P)) target
  store_fv : StoreAgreesOnFvars source.store target.store source.expr
  sourceStoreWF : WellFormedStore source.store source.factory
  targetStoreWF : WellFormedStore target.store target.factory
  exprCongr : WellFormedSemanticEvalExprCongr source.factory

/-- Same-kind event matching induced by `NEArgRel`. -/
abbrev NEEventRel {P : PureExpr} [HasVal P] [HasFvars P] [HasIdent P] :
    Event P → Event P → Prop :=
  Event.Matches (NEArgRel (P := P))

/-- Pointwise NondetElim event matching for traces. -/
abbrev NETraceRel {P : PureExpr} [HasVal P] [HasFvars P] [HasIdent P] :
    Trace P → Trace P → Prop :=
  List.Rel₂ (NEEventRel (P := P))

/-- Forgetting semantic evidence recovers ordinary event-environment extension. -/
theorem NEEventRel.toExtendsEnv {P : PureExpr} [HasVal P] [HasFvars P] [HasIdent P]
    {source target : Event P} (h : NEEventRel (P := P) source target) :
    Event.ExtendsEnv (NdExtra (P := P)) source target := by
  cases source <;> cases target <;>
    simp_all only [NEEventRel, Event.Matches, Event.ExtendsEnv]
  all_goals exact h.envExtends

/-- Forgetting semantic evidence pointwise recovers `TraceExtendsEnv`. -/
theorem NETraceRel.toExtendsEnv {P : PureExpr} [HasVal P] [HasFvars P] [HasIdent P]
    {source target : Trace P} (h : NETraceRel (P := P) source target) :
    TraceExtendsEnv (NdExtra (P := P)) source target :=
  h.imp fun _ _ => NEEventRel.toExtendsEnv

/-- Leaf invariant relating a source environment to its target counterpart at
generator position `σ`: the target extends the source with generated guards
only, the source holds no generated guard, every generated name not yet
produced by `σ` is undefined in the target, and every generated guard bound in
the target holds a Boolean value. -/
structure NdLeaf {P : PureExpr} [HasBool P] [HasIdent P]
    (σ : StringGenState) (ρs ρt : Env P) : Prop where
  ext : Env.ExtendsWith (NdExtra (P := P)) ρs ρt
  srcFresh : ∀ x, NdExtra (P := P) x → ρs.store x = none
  fresh : SemanticStore.isReserved (P := P) NondetElim.isGeneratedName σ ρt.store
  typed : ∀ x v, NdExtra (P := P) x → ρt.store x = some v →
    HasVal.valueOfTy ρt.factory v HasBool.boolTy

/-- The trailing target statements of a statement list: none, or the pending
latch havoc of an enclosing rewritten nondeterministic loop. -/
@[expose] def ndTail {P : PureExpr} : Option (P.Ident × MetaData P) → List (Stmt P (Cmd P))
  | none => []
  | some (g, md) => [.cmd (HasHavoc.havoc g md)]

/-- The latch guard of the trailing tail (if any) is defined in a store. -/
@[expose] def NdTailDef {P : PureExpr} (tail : Option (P.Ident × MetaData P))
    (σ : SemanticStore P) : Prop :=
  ∀ g md, tail = some (g, md) → (σ g).isSome = true

/-- The latch guard of the trailing tail (if any) is defined throughout a
configuration (operative store and every enclosing parent store). -/
@[expose] def NdTailCfg {P : PureExpr} (tail : Option (P.Ident × MetaData P))
    (c : Config P (Cmd P)) : Prop :=
  ∀ g md, tail = some (g, md) → Config.varsDefined (· = g) c

/-- Guard generated for a nondeterministic `ite` at generator state `σ`. -/
abbrev ndIteGuard {P : PureExpr} [HasIdent P] (σ : StringGenState) : P.Ident :=
  HasIdent.ident (P := P) (StringGenState.gen NondetElim.prefixIte σ).1

/-- Guard generated for a nondeterministic loop at generator state `σ`. -/
abbrev ndLoopGuard {P : PureExpr} [HasIdent P] (σ : StringGenState) : P.Ident :=
  HasIdent.ident (P := P) (StringGenState.gen NondetElim.prefixLoop σ).1

/-- The rewritten deterministic `ite` emitted for a nondeterministic `ite`. -/
abbrev ndIteTgt {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (tss ess : List (Stmt P (Cmd P))) (md : MetaData P) (σ : StringGenState) :
    Stmt P (Cmd P) :=
  .ite (.det (HasFvar.mkTypedFvar (ndIteGuard (P := P) σ) HasBool.boolTy))
    (Block.nondetElimM tss (StringGenState.gen NondetElim.prefixIte σ).2).1
    (Block.nondetElimM ess
      (Block.nondetElimM tss (StringGenState.gen NondetElim.prefixIte σ).2).2).1 md

/-- The rewritten deterministic loop emitted for a nondeterministic loop: its
body is the rewritten source body followed by the latch havoc. -/
abbrev ndLoopTgt {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (m : Option P.Expr) (inv : List (String × P.Expr)) (body : List (Stmt P (Cmd P)))
    (md : MetaData P) (σ : StringGenState) : Stmt P (Cmd P) :=
  .loop (.det (HasFvar.mkTypedFvar (ndLoopGuard (P := P) σ) HasBool.boolTy)) m inv
    ((Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2).1 ++
      [.cmd (HasHavoc.havoc (ndLoopGuard (P := P) σ) md)]) md

/-- Shared invariant of the nondeterministic-loop head states: the source has
finished one body iteration (and possibly left its scope), while the target
sits before its latch havoc inside the iteration scope. -/
structure NdHeadInv {P : PureExpr} [HasFvars P] [HasBool P] [HasIdent P]
    (σ σb : StringGenState) (body : List (Stmt P (Cmd P)))
    (σps σpt : SemanticStore P) (ρsb ρtb : Env P) : Prop where
  wf : StringGenState.WF (StringGenState.gen NondetElim.prefixLoop σ).2
  noGen : SrcNoGenWrites (P := P) NondetElim.isGeneratedName body
  noRead : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName body
  parent : StoreExtendsWith (NdExtra (P := P)) σps σpt
  parentFresh : SemanticStore.isReserved (P := P)
    NondetElim.isGeneratedName
    (StringGenState.gen NondetElim.prefixLoop σ).2 σpt
  parentGuard : (σpt (ndLoopGuard (P := P) σ)).isSome = true
  leaf : NdLeaf σb ρsb ρtb
  guard : (ρtb.store (ndLoopGuard (P := P) σ)).isSome = true

/-! ### Generator-indexed configuration simulation

`NdSim tail σe cs ct` relates an in-flight source configuration `cs` to a
target configuration `ct` of the rewritten program.  `σe` is the generator
state reached once the source configuration's pending code has been
rewritten; the continuation of an enclosing sequence was generated from it.
`tail` records whether the enclosing statement list is the body of a rewritten
nondeterministic loop, whose target list carries the trailing latch havoc. -/
inductive NdSim {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] :
    Option (P.Ident × MetaData P) → StringGenState →
    Config P (Cmd P) → Config P (Cmd P) → Prop where
  /-- A source statement list and its rewrite (plus the tail). -/
  | stmts {tail : Option (P.Ident × MetaData P)} {σ : StringGenState}
      {ss : List (Stmt P (Cmd P))} {ρs ρt : Env P} :
      StringGenState.WF σ → NdLeaf σ ρs ρt →
      SrcNoGenWrites (P := P) NondetElim.isGeneratedName ss →
      Block.exprsShapeFree (P := P) NondetElim.isGeneratedName ss →
      NdTailDef tail ρt.store →
      NdSim tail (Block.nondetElimM ss σ).2 (.stmts ss ρs)
        (.stmts ((Block.nondetElimM ss σ).1 ++ ndTail tail) ρt)
  /-- A source statement whose rewrite is a single statement. -/
  | stmt {σ : StringGenState} {s s' : Stmt P (Cmd P)} {ρs ρt : Env P} :
      StringGenState.WF σ → NdLeaf σ ρs ρt →
      SrcNoGenWrites (P := P) NondetElim.isGeneratedName [s] →
      Block.exprsShapeFree (P := P) NondetElim.isGeneratedName [s] →
      (Stmt.nondetElimM s σ).1 = [s'] →
      NdSim none (Stmt.nondetElimM s σ).2 (.stmt s ρs) (.stmt s' ρt)
  /-- Terminated configurations. -/
  | terminal {σe : StringGenState} {ρs ρt : Env P} :
      NdLeaf σe ρs ρt → NdSim none σe (.terminal ρs) (.terminal ρt)
  /-- A finished loop body: the target still has to run the latch havoc. -/
  | pendingHavoc {σe : StringGenState} {g : P.Ident} {md : MetaData P} {ρs ρt : Env P} :
      NdLeaf σe ρs ρt → (ρt.store g).isSome = true →
      NdSim (some (g, md)) σe (.terminal ρs) (.stmts [.cmd (HasHavoc.havoc g md)] ρt)
  /-- Exiting configurations. -/
  | exiting {tail : Option (P.Ident × MetaData P)} {σe : StringGenState} {l : String}
      {ρs ρt : Env P} :
      NdLeaf σe ρs ρt → NdSim tail σe (.exiting l ρs) (.exiting l ρt)
  /-- A sequence frame whose continuation was rewritten from `σr`. -/
  | seq {tail : Option (P.Ident × MetaData P)} {σr : StringGenState}
      {inner inner' : Config P (Cmd P)} {rest : List (Stmt P (Cmd P))} :
      NdSim none σr inner inner' → StringGenState.WF σr →
      SrcNoGenWrites (P := P) NondetElim.isGeneratedName rest →
      Block.exprsShapeFree (P := P) NondetElim.isGeneratedName rest →
      NdTailCfg tail inner' →
      NdSim tail (Block.nondetElimM rest σr).2 (.seq inner rest)
        (.seq inner' ((Block.nondetElimM rest σr).1 ++ ndTail tail))
  /-- A block frame; projection through the parents restores freshness at `σe`. -/
  | block {σi σe : StringGenState} {l : Option String} {σps σpt : SemanticStore P}
      {inner inner' : Config P (Cmd P)} :
      NdSim none σi inner inner' → StoreExtendsWith (NdExtra (P := P)) σps σpt →
      SemanticStore.isReserved (P := P) NondetElim.isGeneratedName σe σpt →
      NdSim none σe (.block l σps inner) (.block l σpt inner')
  /-- Preheader of a nondeterministic `ite`: the target has not yet chosen its
  guard; the source's branch choice will drive the guard's initial value. -/
  | seqIte {tail : Option (P.Ident × MetaData P)} {σ : StringGenState}
      {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
      {rest : List (Stmt P (Cmd P))} {ρs ρt : Env P} :
      StringGenState.WF σ → NdLeaf σ ρs ρt →
      SrcNoGenWrites (P := P) NondetElim.isGeneratedName [.ite .nondet tss ess md] →
      Block.exprsShapeFree (P := P) NondetElim.isGeneratedName
        [.ite .nondet tss ess md] →
      SrcNoGenWrites (P := P) NondetElim.isGeneratedName rest →
      Block.exprsShapeFree (P := P) NondetElim.isGeneratedName rest →
      NdTailDef tail ρt.store →
      NdSim tail (Block.nondetElimM rest (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2).2
        (.seq (.stmt (.ite .nondet tss ess md) ρs) rest)
        (.seq (.stmt (.cmd (HasInit.init (ndIteGuard (P := P) σ) HasBool.boolTy .nondet md)) ρt)
          (ndIteTgt tss ess md σ ::
            ((Block.nondetElimM rest (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2).1 ++
              ndTail tail)))
  /-- Preheader of a nondeterministic loop: the source's first enter/exit choice
  will drive the guard's initial value. -/
  | seqLoop {tail : Option (P.Ident × MetaData P)} {σ : StringGenState}
      {m : Option P.Expr} {inv : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
      {md : MetaData P} {rest : List (Stmt P (Cmd P))} {ρs ρt : Env P} :
      StringGenState.WF σ → NdLeaf σ ρs ρt →
      SrcNoGenWrites (P := P) NondetElim.isGeneratedName [.loop .nondet m inv body md] →
      Block.exprsShapeFree (P := P) NondetElim.isGeneratedName
        [.loop .nondet m inv body md] →
      SrcNoGenWrites (P := P) NondetElim.isGeneratedName rest →
      Block.exprsShapeFree (P := P) NondetElim.isGeneratedName rest →
      NdTailDef tail ρt.store →
      NdSim tail (Block.nondetElimM rest (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2).2
        (.seq (.stmt (.loop .nondet m inv body md) ρs) rest)
        (.seq (.stmt (.cmd (HasInit.init (ndLoopGuard (P := P) σ) HasBool.boolTy .nondet md)) ρt)
          (ndLoopTgt m inv body md σ ::
            ((Block.nondetElimM rest (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2).1 ++
              ndTail tail)))
  /-- One running iteration of a nondeterministic loop: the body runs under the
  latch-havoc tail. -/
  | iter {σ σb : StringGenState} {m : Option P.Expr} {inv : List (String × P.Expr)}
      {body : List (Stmt P (Cmd P))} {md : MetaData P} {σps σpt : SemanticStore P}
      {cs ct : Config P (Cmd P)} :
      StringGenState.WF (StringGenState.gen NondetElim.prefixLoop σ).2 →
      SrcNoGenWrites (P := P) NondetElim.isGeneratedName body →
      Block.exprsShapeFree (P := P) NondetElim.isGeneratedName body →
      StoreExtendsWith (NdExtra (P := P)) σps σpt →
      SemanticStore.isReserved (P := P) NondetElim.isGeneratedName
        (StringGenState.gen NondetElim.prefixLoop σ).2 σpt →
      (σpt (ndLoopGuard (P := P) σ)).isSome = true →
      NdSim (some (ndLoopGuard (P := P) σ, md)) σb cs ct →
      NdSim none (Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2).2
        (.seq (.block none σps cs) [.loop .nondet m inv body md])
        (.seq (.block none σpt ct) [ndLoopTgt m inv body md σ])
  /-- Loop head, source left the iteration scope. -/
  | headTerm {σ σb : StringGenState} {m : Option P.Expr} {inv : List (String × P.Expr)}
      {body : List (Stmt P (Cmd P))} {md : MetaData P} {σps σpt : SemanticStore P}
      {ρsb ρtb : Env P} :
      NdHeadInv σ σb body σps σpt ρsb ρtb →
      NdSim none (Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2).2
        (.seq (.terminal { ρsb with store := projectStore σps ρsb.store })
          [.loop .nondet m inv body md])
        (.seq (.block none σpt (.stmts [.cmd (HasHavoc.havoc (ndLoopGuard (P := P) σ) md)] ρtb))
          [ndLoopTgt m inv body md σ])
  /-- Loop head, source resumed its loop continuation. -/
  | headStmts {σ σb : StringGenState} {m : Option P.Expr} {inv : List (String × P.Expr)}
      {body : List (Stmt P (Cmd P))} {md : MetaData P} {σps σpt : SemanticStore P}
      {ρsb ρtb : Env P} :
      NdHeadInv σ σb body σps σpt ρsb ρtb →
      NdSim none (Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2).2
        (.stmts [.loop .nondet m inv body md] { ρsb with store := projectStore σps ρsb.store })
        (.seq (.block none σpt (.stmts [.cmd (HasHavoc.havoc (ndLoopGuard (P := P) σ) md)] ρtb))
          [ndLoopTgt m inv body md σ])
  /-- Loop head, source about to choose enter/exit. -/
  | headStmt {σ σb : StringGenState} {m : Option P.Expr} {inv : List (String × P.Expr)}
      {body : List (Stmt P (Cmd P))} {md : MetaData P} {σps σpt : SemanticStore P}
      {ρsb ρtb : Env P} :
      NdHeadInv σ σb body σps σpt ρsb ρtb →
      NdSim none (Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2).2
        (.seq (.stmt (.loop .nondet m inv body md)
          { ρsb with store := projectStore σps ρsb.store }) [])
        (.seq (.block none σpt (.stmts [.cmd (HasHavoc.havoc (ndLoopGuard (P := P) σ) md)] ρtb))
          [ndLoopTgt m inv body md σ])
  /-- An exit escaping a loop iteration scope, before the sequence propagates it. -/
  | seqExit {σe : StringGenState} {l : String} {ρs ρt : Env P}
      {ss ss' : List (Stmt P (Cmd P))} :
      NdLeaf σe ρs ρt → NdSim none σe (.seq (.exiting l ρs) ss) (.seq (.exiting l ρt) ss')


/-! ### Source write-set decomposition -/

/-- The empty source block has an empty write set, so it vacuously writes no
name of kind `Q`. -/
private theorem noGen_nil {P : PureExpr} [HasFvars P] [HasIdent P] {Q : String → Prop} :
    SrcNoGenWrites (P := P) Q [] := by
  intro s _ hmem
  simp [Block.definedVars, Block.modifiedVars] at hmem

/-- If a cons block writes no name of kind `Q`, neither does its head statement
taken on its own. -/
private theorem noGen_head {P : PureExpr} [HasFvars P] [HasIdent P] {Q : String → Prop}
    {s : Stmt P (Cmd P)} {ss : List (Stmt P (Cmd P))}
    (h : SrcNoGenWrites (P := P) Q (s :: ss)) : SrcNoGenWrites (P := P) Q [s] := by
  intro name hq hmem
  apply h name hq
  simp only [Block.definedVars, Block.modifiedVars, List.append_nil, List.mem_append] at hmem ⊢
  rcases hmem with h | h
  · exact .inl (.inl h)
  · exact .inr (.inl h)

/-- If a cons block writes no name of kind `Q`, neither does its tail. -/
private theorem noGen_tail {P : PureExpr} [HasFvars P] [HasIdent P] {Q : String → Prop}
    {s : Stmt P (Cmd P)} {ss : List (Stmt P (Cmd P))}
    (h : SrcNoGenWrites (P := P) Q (s :: ss)) : SrcNoGenWrites (P := P) Q ss := by
  intro name hq hmem
  apply h name hq
  simp only [Block.definedVars, Block.modifiedVars, List.mem_append] at hmem ⊢
  rcases hmem with h | h
  · exact .inl (.inr h)
  · exact .inr (.inr h)

/-- If a singleton `.block` statement writes no name of kind `Q`, neither does
its inner body. -/
private theorem noGen_block {P : PureExpr} [HasFvars P] [HasIdent P] {Q : String → Prop}
    {l : String} {bss : List (Stmt P (Cmd P))} {md : MetaData P}
    (h : SrcNoGenWrites (P := P) Q [.block l bss md]) : SrcNoGenWrites (P := P) Q bss := by
  intro name hq hmem
  apply h name hq
  simp only [Block.definedVars, Block.modifiedVars, Stmt.definedVars, Stmt.modifiedVars,
    Bool.false_eq_true, ite_false, List.append_nil, List.mem_append] at hmem ⊢
  exact hmem

/-- If a singleton `.ite` statement writes no name of kind `Q`, neither does its
then branch. -/
private theorem noGen_ite_then {P : PureExpr} [HasFvars P] [HasIdent P] {Q : String → Prop}
    {c : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    (h : SrcNoGenWrites (P := P) Q [.ite c tss ess md]) : SrcNoGenWrites (P := P) Q tss := by
  intro name hq hmem
  apply h name hq
  simp only [Block.definedVars, Block.modifiedVars, Stmt.definedVars, Stmt.modifiedVars,
    Bool.false_eq_true, ite_false, List.append_nil, List.mem_append] at hmem ⊢
  rcases hmem with h | h
  · exact .inl (.inl h)
  · exact .inr (.inl h)

/-- If a singleton `.ite` statement writes no name of kind `Q`, neither does its
else branch. -/
private theorem noGen_ite_else {P : PureExpr} [HasFvars P] [HasIdent P] {Q : String → Prop}
    {c : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    (h : SrcNoGenWrites (P := P) Q [.ite c tss ess md]) : SrcNoGenWrites (P := P) Q ess := by
  intro name hq hmem
  apply h name hq
  simp only [Block.definedVars, Block.modifiedVars, Stmt.definedVars, Stmt.modifiedVars,
    Bool.false_eq_true, ite_false, List.append_nil, List.mem_append] at hmem ⊢
  rcases hmem with h | h
  · exact .inl (.inr h)
  · exact .inr (.inr h)

/-- If a singleton `.loop` statement writes no name of kind `Q`, neither does its
body. -/
private theorem noGen_loop {P : PureExpr} [HasFvars P] [HasIdent P] {Q : String → Prop}
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P}
    (h : SrcNoGenWrites (P := P) Q [.loop g m inv body md]) : SrcNoGenWrites (P := P) Q body := by
  intro name hq hmem
  apply h name hq
  simp only [Block.definedVars, Block.modifiedVars, Stmt.definedVars, Stmt.modifiedVars,
    Bool.false_eq_true, ite_false, List.append_nil, List.mem_append] at hmem ⊢
  exact hmem

/-- If a singleton command writes no name of kind `Q`, then no identifier of kind
`Q` lies among the command's defined or modified variables. -/
private theorem noGen_cmd {P : PureExpr} [HasFvars P] [HasIdent P]
    {Q : String → Prop} {c : Cmd P}
    (h : SrcNoGenWrites (P := P) Q [.cmd c]) {x : P.Ident}
    (hx : IdentOfStringKind (P := P) Q x) :
    x ∉ Cmd.definedVars c ∧ x ∉ Cmd.modifiedVars c := by
  obtain ⟨name, hq, rfl⟩ := hx
  have h' := h name hq
  simp only [Block.definedVars, Block.modifiedVars, Stmt.definedVars, Stmt.modifiedVars,
    HasVarsImp.definedVars, HasVarsImp.modifiedVars, List.append_nil, List.mem_append,
    not_or] at h'
  exact h'

/-- Canonical events emitted by replaying a read-fresh command carry the
NondetElim argument relation. -/
private theorem cmd_emitted_neTraceRel {P : PureExpr} [HasFvar P] [HasFvars P]
    [HasBool P] [HasVal P] [HasIdent P]
    {c : Cmd P} {fs ft : P.Factory} {σs σt : SemanticStore P}
    (hread : ∀ name, NondetElim.isGeneratedName name →
      HasIdent.ident (P := P) name ∉ Cmd.getVars c)
    (hfactory : fs = ft)
    (hext : StoreExtendsWith (NdExtra (P := P)) σs σt)
    (hsourceWF : WellFormedStore σs fs) (htargetWF : WellFormedStore σt ft)
    (hcongr : WellFormedSemanticEvalExprCongr fs) :
    NETraceRel (P := P) (Cmd.emittedEvents P c fs σs) (Cmd.emittedEvents P c ft σt) := by
  have hfv : ∀ x ∈ Cmd.getVars c, σs x = σt x := by
    intro x hx
    apply hext.lookup_eq_of_not_extra
    rintro ⟨name, hname, rfl⟩
    exact hread name hname hx
  cases c with
  | init | set => exact .nil
  | assert label expr metadata =>
      exact .cons
        ⟨⟨hfactory, hext, rfl, rfl, rfl⟩,
          (fun x hx => hfv x (by simpa [Cmd.getVars] using hx)),
          hsourceWF, htargetWF, hcongr⟩ .nil
  | assume label expr metadata =>
      exact .cons
        ⟨⟨hfactory, hext, rfl, rfl, rfl⟩,
          (fun x hx => hfv x (by simpa [Cmd.getVars] using hx)),
          hsourceWF, htargetWF, hcongr⟩ .nil
  | cover label expr metadata =>
      exact .cons
        ⟨⟨hfactory, hext, rfl, rfl, rfl⟩,
          (fun x hx => hfv x (by simpa [Cmd.getVars] using hx)),
          hsourceWF, htargetWF, hcongr⟩ .nil


/-! ### Event command frame facts -/

/-- A command leaves a register's value unchanged when the register is neither
defined nor modified by the command. -/
private theorem evalCmdE_eq_of_not_written {P : PureExpr} [HasFvar P] [HasBool P]
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {emitted : Trace P} {y : P.Ident}
    (h : EvalCmdE P f σ c σ' emitted)
    (hd : y ∉ Cmd.definedVars c) (hm : y ∉ Cmd.modifiedVars c) : σ' y = σ y := by
  cases h with
  | eval_init _ hinit _ _ =>
    cases hinit with
    | init _ _ h_other =>
      exact h_other y (by intro heq; subst heq; exact hd (by simp [Cmd.definedVars]))
  | eval_init_unconstrained hinit _ _ =>
    cases hinit with
    | init _ _ h_other =>
      exact h_other y (by intro heq; subst heq; exact hd (by simp [Cmd.definedVars]))
  | eval_set _ hupd _ _ =>
    cases hupd with
    | update _ _ h_other =>
      exact h_other y (by intro heq; subst heq; exact hm (by simp [Cmd.modifiedVars]))
  | eval_set_nondet hupd _ _ =>
    cases hupd with
    | update _ _ h_other =>
      exact h_other y (by intro heq; subst heq; exact hm (by simp [Cmd.modifiedVars]))
  | eval_assert => rfl
  | eval_assume => rfl
  | eval_cover => rfl

/-- A register that the command defines (via `init`) must have been undefined in
the pre-state. -/
private theorem evalCmdE_defined_none {P : PureExpr} [HasFvar P] [HasBool P]
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {emitted : Trace P} {x : P.Ident}
    (h : EvalCmdE P f σ c σ' emitted) (hx : x ∈ Cmd.definedVars c) : σ x = none := by
  cases h with
  | eval_init _ hinit _ _ =>
    simp only [Cmd.definedVars, List.mem_singleton] at hx
    subst hx
    cases hinit with
    | init hnone _ _ => exact hnone
  | eval_init_unconstrained hinit _ _ =>
    simp only [Cmd.definedVars, List.mem_singleton] at hx
    subst hx
    cases hinit with
    | init hnone _ _ => exact hnone
  | eval_set => simp [Cmd.definedVars] at hx
  | eval_set_nondet => simp [Cmd.definedVars] at hx
  | eval_assert => simp [Cmd.definedVars] at hx
  | eval_assume => simp [Cmd.definedVars] at hx
  | eval_cover => simp [Cmd.definedVars] at hx

/-! ### Leaf-invariant transport -/

/-- The leaf invariant is preserved when the generator state advances by one
generation step; only the freshness component weakens. -/
private theorem NdLeaf.mono {P : PureExpr} [HasBool P] [HasIdent P]
    {σ σ' : StringGenState} {ρs ρt : Env P}
    (hstep : StringGenState.GenStep σ σ') (h : NdLeaf σ ρs ρt) : NdLeaf σ' ρs ρt :=
  { h with fresh := SemanticStore.isReserved.mono hstep h.fresh }

/-- Replaying a user command keeps the leaf invariant and relates the emitted
snapshots. -/
private theorem NdLeaf.cmd_step {P : PureExpr} [HasFvar P] [HasFvars P]
    [HasBoolOps P] [HasVal P] [HasIdent P] [DecidableEq P.Ident]
    {σ : StringGenState} {ρs ρt : Env P} {c : Cmd P} {σs' : SemanticStore P}
    {e : Trace P}
    (hl : NdLeaf σ ρs ρt)
    (hng : SrcNoGenWrites (P := P) NondetElim.isGeneratedName [.cmd c])
    (hread : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName [.cmd c])
    (hsourceWF : WellFormedStore ρs.store ρs.factory)
    (htargetWF : WellFormedStore ρt.store ρt.factory)
    (hcongr : WellFormedSemanticEvalExprCongr ρs.factory)
    (hmono : WellFormedSemanticEvalMono ρs.factory)
    (heval : EvalCmdE P ρs.factory ρs.store c σs' e) :
    ∃ σt', EvalCmdE P ρt.factory ρt.store c σt'
        (Cmd.emittedEvents P c ρt.factory ρt.store) ∧
      NETraceRel (P := P) e (Cmd.emittedEvents P c ρt.factory ρt.store) ∧
      NdLeaf σ { ρs with store := σs' } { ρt with store := σt' } := by
  obtain ⟨hfac, hfail, hstore⟩ := hl.ext
  have htrace : NETraceRel (P := P) e
      (Cmd.emittedEvents P c ρt.factory ρt.store) := by
    rw [heval.emitted_eq]
    exact cmd_emitted_neTraceRel
      (Stmt.exprsShapeFree_cmd.mp (Block.exprsShapeFree_singleton.mp hread))
      hfac hstore hsourceWF htargetWF hcongr
  have hinit : ∀ x ∈ Cmd.definedVars c, ρt.store x = none := by
    intro x hx
    have hsrc : ρs.store x = none := evalCmdE_defined_none heval hx
    cases hxt : ρt.store x with
    | none => rfl
    | some w =>
      exfalso
      rcases hstore.2 x (by simp [hxt]) with hs | hextra
      · simp [hsrc] at hs
      · exact (noGen_cmd hng hextra).1 hx
  obtain ⟨σt', hevt, hext', _⟩ :=
    evalCmdE_replay_extends (NdExtra (P := P)) ρs.factory ρs.store ρt.store σs' c e
      hstore heval hmono hinit
  rw [hfac] at hevt
  refine ⟨σt', hevt, htrace, ⟨⟨hfac, hfail, hext'⟩, ?_, ?_, ?_⟩⟩
  · intro x hx
    show σs' x = none
    rw [evalCmdE_eq_of_not_written heval (noGen_cmd hng hx).1 (noGen_cmd hng hx).2]
    exact hl.srcFresh x hx
  · intro s hs hnin
    have hx : NdExtra (P := P) (HasIdent.ident s) := ⟨s, hs, rfl⟩
    show σt' (HasIdent.ident s) = none
    rw [evalCmdE_eq_of_not_written hevt (noGen_cmd hng hx).1 (noGen_cmd hng hx).2]
    exact hl.fresh s hs hnin
  · intro x v hx hv
    have hv' : ρt.store x = some v := by
      rw [← evalCmdE_eq_of_not_written hevt (noGen_cmd hng hx).1 (noGen_cmd hng hx).2]
      exact hv
    exact hl.typed x v hx hv'

/-- Leaving a block scope projects both sides through related parent stores. -/
private theorem ndLeaf_project {P : PureExpr} [HasBool P] [HasIdent P]
    {σe : StringGenState} {ρs ρt : Env P} {σps σpt : SemanticStore P}
    (hext : Env.ExtendsWith (NdExtra (P := P)) ρs ρt)
    (hsrc : ∀ x, NdExtra (P := P) x → ρs.store x = none)
    (htyped : ∀ x v, NdExtra (P := P) x → ρt.store x = some v →
      HasVal.valueOfTy ρt.factory v HasBool.boolTy)
    (hp : StoreExtendsWith (NdExtra (P := P)) σps σpt)
    (hf : SemanticStore.isReserved (P := P) NondetElim.isGeneratedName σe σpt) :
    NdLeaf σe { ρs with store := projectStore σps ρs.store }
      { ρt with store := projectStore σpt ρt.store } := by
  refine ⟨⟨hext.1, hext.2.1, StoreExtendsWith.projectStore hp hext.2.2⟩, ?_, ?_, ?_⟩
  · intro x hx
    show projectStore σps ρs.store x = none
    simp only [projectStore, hsrc x hx]
    split <;> rfl
  · intro s hs hnin
    show projectStore σpt ρt.store (HasIdent.ident s) = none
    simp only [projectStore, hf s hs hnin]
    simp
  · intro x v hx hv
    change projectStore σpt ρt.store x = some v at hv
    simp only [projectStore] at hv
    split at hv
    · exact htyped x v hx hv
    · simp at hv

/-- Leaving a block scope preserves the leaf invariant: it projects the source
and target stores through related parent stores, with the exit generator state
fresh for the projected target store. -/
private theorem NdLeaf.project {P : PureExpr} [HasBool P] [HasIdent P]
    {σi σe : StringGenState} {ρs ρt : Env P} {σps σpt : SemanticStore P}
    (hl : NdLeaf σi ρs ρt) (hp : StoreExtendsWith (NdExtra (P := P)) σps σpt)
    (hf : SemanticStore.isReserved (P := P) NondetElim.isGeneratedName σe σpt) :
    NdLeaf σe { ρs with store := projectStore σps ρs.store }
      { ρt with store := projectStore σpt ρt.store } :=
  ndLeaf_project hl.ext hl.srcFresh hl.typed hp hf

/-- Initializing a freshly generated guard with a Boolean value. -/
private theorem NdLeaf.init_guard {P : PureExpr} [HasBool P] [HasIdent P] [DecidableEq P.Ident]
    [LawfulHasIdent P]
    {σ : StringGenState} {ρs ρt : Env P} {pf : String}
    (hwf : StringGenState.WF σ) (hQ : NondetElim.isGeneratedName (StringGenState.gen pf σ).1)
    (hl : NdLeaf σ ρs ρt) {v : P.Expr} (hv : HasVal.valueOfTy ρt.factory v HasBool.boolTy) :
    ρt.store (HasIdent.ident (StringGenState.gen pf σ).1) = none ∧
    NdLeaf (StringGenState.gen pf σ).2 ρs
      { ρt with
        store := SemanticStore.update ρt.store
          (HasIdent.ident (StringGenState.gen pf σ).1) v } := by
  have hg : NdExtra (P := P) (HasIdent.ident (StringGenState.gen pf σ).1) := ⟨_, hQ, rfl⟩
  have hnone := SemanticStore.isReserved.gen_slot_none pf hl.fresh hwf hQ
  refine ⟨hnone, ⟨⟨hl.ext.1, hl.ext.2.1,
    StoreExtendsWith.update_target hl.ext.2.2 (hl.srcFresh _ hg) hg⟩,
    hl.srcFresh, SemanticStore.isReserved.storeWith_gen pf v hl.fresh, ?_⟩⟩
  intro x w hx hw
  change SemanticStore.update ρt.store _ v x = some w at hw
  by_cases hxg : x = HasIdent.ident (StringGenState.gen pf σ).1
  · subst hxg
    simp [SemanticStore.update] at hw
    subst hw
    exact hv
  · simp only [SemanticStore.update, ite_eq_right hxg] at hw
    exact hl.typed x w hx hw

/-- Re-havocking a defined guard at the latch and leaving the iteration scope. -/
private theorem NdLeaf.latch {P : PureExpr} [HasBool P] [HasIdent P] [DecidableEq P.Ident]
    {σb σe : StringGenState} {ρsb ρtb : Env P} {σps σpt : SemanticStore P}
    {g : P.Ident} {v : P.Expr}
    (hl : NdLeaf σb ρsb ρtb) (hg : NdExtra (P := P) g)
    (hv : HasVal.valueOfTy ρtb.factory v HasBool.boolTy)
    (hp : StoreExtendsWith (NdExtra (P := P)) σps σpt)
    (hf : SemanticStore.isReserved (P := P) NondetElim.isGeneratedName σe σpt) :
    NdLeaf σe { ρsb with store := projectStore σps ρsb.store }
      { ρtb with store := projectStore σpt (SemanticStore.update ρtb.store g v) } := by
  have htyped : ∀ x w, NdExtra (P := P) x → SemanticStore.update ρtb.store g v x = some w →
      HasVal.valueOfTy ρtb.factory w HasBool.boolTy := by
    intro x w hx hw
    by_cases hxg : x = g
    · subst hxg
      simp [SemanticStore.update] at hw
      subst hw
      exact hv
    · simp only [SemanticStore.update, ite_eq_right hxg] at hw
      exact hl.typed x w hx hw
  exact ndLeaf_project (ρt := { ρtb with store := SemanticStore.update ρtb.store g v })
    ⟨hl.ext.1, hl.ext.2.1, StoreExtendsWith.update_target hl.ext.2.2 (hl.srcFresh g hg) hg⟩
    hl.srcFresh htyped hp hf

/-! ### Guard evaluation -/

/-- Reading a guard register immediately after writing it returns the written
boolean value. -/
private theorem eval_guard_update {P : PureExpr} [HasBool P] [HasFvar P]
    [HasFvars P] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasVal P]
    {f : P.Factory} {σ : SemanticStore P} {g : P.Ident} {v : P.Expr}
    (hv : HasVal.valueOfTy f v HasBool.boolTy)
    (hvar : WellFormedSemanticEvalVar f) (hmono : WellFormedSemanticEvalMono f) :
    P.eval f (SemanticStore.update σ g v) (HasFvar.mkTypedFvar g HasBool.boolTy) = some v :=
  eval_mkTypedFvar_storeWith f σ g v (LawfulHasVal.valueOfTy_isVal _ _ _ hv) hvar hmono

/-- Reading a guard register after a latch havoc and a block-store projection
returns the written boolean value, provided the parent store keeps the guard
defined. -/
private theorem eval_guard_latch {P : PureExpr} [HasBool P] [HasFvar P] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasVal P]
    {f : P.Factory} {σpt σ : SemanticStore P} {g : P.Ident} {v : P.Expr}
    (hpg : (σpt g).isSome = true)
    (hv : HasVal.valueOfTy f v HasBool.boolTy)
    (hvar : WellFormedSemanticEvalVar f) (hmono : WellFormedSemanticEvalMono f) :
    P.eval f (projectStore σpt (SemanticStore.update σ g v))
      (HasFvar.mkTypedFvar g HasBool.boolTy) = some v :=
  eval_mkTypedFvar_of_value f _ g v (LawfulHasVal.valueOfTy_isVal _ _ _ hv)
    (by simp [projectStore, hpg, SemanticStore.update]) hvar hmono

/-! ### Target run builders -/

/-- Prepend a silent (empty-trace) event step to a target run, leaving the run's
trace unchanged. -/
private theorem starE_cons_nil {P : PureExpr} [HasFvar P] [HasBoolOps P]
    {c c' c'' : Config P (Cmd P)} {tr : Trace P}
    (h : StepStmtE P (EvalCmdE P) c [] c') (hr : StepStmtStarE P (EvalCmdE P) c' tr c'') :
    StepStmtStarE P (EvalCmdE P) c tr c'' :=
  .step _ [] _ tr _ h hr

/-- Initialize a guard and enter the statement it guards. -/
private theorem tgt_init_then {P : PureExpr} [HasFvar P] [HasBoolOps P] [DecidableEq P.Ident]
    {g : P.Ident} {md : MetaData P} {X : Stmt P (Cmd P)} {R : List (Stmt P (Cmd P))}
    {ρt : Env P} {v : P.Expr}
    (hnone : ρt.store g = none) (hv : HasVal.valueOfTy ρt.factory v HasBool.boolTy)
    (hvar : WellFormedSemanticEvalVar ρt.factory) :
    StepStmtStarE P (EvalCmdE P)
      (.seq (.stmt (.cmd (HasInit.init g HasBool.boolTy .nondet md)) ρt) (X :: R)) []
      (.seq (.stmt X { ρt with store := SemanticStore.update ρt.store g v }) R) := by
  have hinit : InitState P ρt.store g v (SemanticStore.update ρt.store g v) :=
    InitState.init hnone (by simp [SemanticStore.update])
      (by intro y hy; simp [SemanticStore.update, Ne.symm hy])
  have hcmd : EvalCmdE P ρt.factory ρt.store (HasInit.init g HasBool.boolTy .nondet md)
      (SemanticStore.update ρt.store g v) [] :=
    EvalCmdE.eval_init_unconstrained hinit hv hvar
  refine starE_cons_nil (.step_seq_inner (.step_cmd hcmd)) ?_
  refine starE_cons_nil (.step_admin .step_seq_done) ?_
  exact starE_cons_nil (.step_admin .step_stmts_cons) (.refl _)

/-- Run the pending latch havoc, leave the iteration scope, and resume the loop. -/
private theorem tgt_latch {P : PureExpr} [HasFvar P] [HasBoolOps P] [DecidableEq P.Ident]
    {g : P.Ident} {md : MetaData P} {σpt : SemanticStore P} {ρtb : Env P}
    {L' : Stmt P (Cmd P)} {prev v : P.Expr}
    (hprev : ρtb.store g = some prev)
    (hprevTy : HasVal.valueOfTy ρtb.factory prev HasBool.boolTy)
    (hv : HasVal.valueOfTy ρtb.factory v HasBool.boolTy)
    (hvar : WellFormedSemanticEvalVar ρtb.factory) :
    StepStmtStarE P (EvalCmdE P)
      (.seq (.block none σpt (.stmts [.cmd (HasHavoc.havoc g md)] ρtb)) [L']) []
      (.seq (.stmt L'
        { ρtb with store := projectStore σpt (SemanticStore.update ρtb.store g v) }) []) := by
  have hupd : UpdateState P ρtb.store g v (SemanticStore.update ρtb.store g v) :=
    UpdateState.update hprev (by simp [SemanticStore.update])
      (by intro y hy; simp [SemanticStore.update, Ne.symm hy])
  have hcmd : EvalCmdE P ρtb.factory ρtb.store (HasHavoc.havoc g md)
      (SemanticStore.update ρtb.store g v) [] :=
    EvalCmdE.eval_set_nondet hupd ⟨prev, HasBool.boolTy, hprev, hprevTy, hv⟩ hvar
  refine starE_cons_nil (.step_admin (.step_seq_inner (.step_block_body .step_stmts_cons))) ?_
  refine starE_cons_nil
    (.step_seq_inner (.step_block_body (.step_seq_inner (.step_cmd hcmd)))) ?_
  refine starE_cons_nil (.step_admin (.step_seq_inner (.step_block_body .step_seq_done))) ?_
  refine starE_cons_nil (.step_admin (.step_seq_inner (.step_block_body .step_stmts_nil))) ?_
  refine starE_cons_nil (.step_admin (.step_seq_inner .step_block_done)) ?_
  refine starE_cons_nil (.step_admin .step_seq_done) ?_
  exact starE_cons_nil (.step_admin .step_stmts_cons) (.refl _)


/-! ### Source step inversion -/

/-- Case analysis on one event step of a `.seq` configuration: either the inner
configuration steps, or it was terminal (and the sequence advances to its
continuation), or it was exiting (and the exit propagates). -/
private theorem stepE_seq_cases {P : PureExpr} [HasFvar P] [HasBoolOps P]
    {inner : Config P (Cmd P)} {ss : List (Stmt P (Cmd P))} {e : Trace P}
    {c' : Config P (Cmd P)}
    (h : StepStmtE P (EvalCmdE P) (.seq inner ss) e c') :
    (∃ inner', StepStmtE P (EvalCmdE P) inner e inner' ∧ c' = .seq inner' ss) ∨
    (∃ ρ, inner = .terminal ρ ∧ e = [] ∧ c' = .stmts ss ρ) ∨
    (∃ l ρ, inner = .exiting l ρ ∧ e = [] ∧ c' = .exiting l ρ) := by
  cases h with
  | step_seq_inner h => exact .inl ⟨_, h, rfl⟩
  | step_admin h =>
    cases h with
    | step_seq_inner h => exact .inl ⟨_, .step_admin h, rfl⟩
    | step_seq_done => exact .inr (.inl ⟨_, rfl, rfl, rfl⟩)
    | step_seq_exit => exact .inr (.inr ⟨_, _, rfl, rfl, rfl⟩)

/-- A `.stmts` configuration steps silently (empty trace), either to a terminal
when the list is empty or to a `.seq` of its head statement with the remaining
list. -/
private theorem stepE_stmts_cases {P : PureExpr} [HasFvar P] [HasBoolOps P]
    {ss : List (Stmt P (Cmd P))} {ρ : Env P} {e : Trace P} {c' : Config P (Cmd P)}
    (h : StepStmtE P (EvalCmdE P) (.stmts ss ρ) e c') :
    e = [] ∧ ((ss = [] ∧ c' = .terminal ρ) ∨
      (∃ s rest, ss = s :: rest ∧ c' = .seq (.stmt s ρ) rest)) := by
  cases h with
  | step_admin h =>
    cases h with
    | step_stmts_nil => exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
    | step_stmts_cons => exact ⟨rfl, .inr ⟨_, _, rfl, rfl⟩⟩

/-- A terminal configuration takes no event step. -/
private theorem stepE_terminal_false {P : PureExpr} [HasFvar P] [HasBoolOps P]
    {ρ : Env P} {e : Trace P} {c' : Config P (Cmd P)}
    (h : StepStmtE P (EvalCmdE P) (.terminal ρ) e c') : False := by
  cases h with
  | step_admin h => cases h

/-- A non-command statement configuration steps silently by a command-free
(administrative) control-flow step. -/
private theorem stepE_stmt_admin {P : PureExpr} [HasFvar P] [HasBoolOps P]
    {s : Stmt P (Cmd P)} {ρ : Env P} {e : Trace P} {c' : Config P (Cmd P)}
    (hs : ∀ c, s ≠ .cmd c)
    (h : StepStmtE P (EvalCmdE P) (.stmt s ρ) e c') :
    e = [] ∧ StepStmt P (noCommandEvalE P (Cmd P)) (.stmt s ρ) c' := by
  cases h with
  | step_cmd _ => exact absurd rfl (hs _)
  | step_admin h => exact ⟨rfl, h⟩

/-! ### Rewrite shapes -/

/-- Normal form: the pass maps the empty block to the empty block and leaves the
generator state unchanged. -/
private theorem nondetElimM_nil {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (σ : StringGenState) :
    Block.nondetElimM (P := P) (CmdT := Cmd P) [] σ = ([], σ) := by
  simp [Block.nondetElimM]

/-- Normal form: a singleton block rewrites to the same output statements as its
single statement. -/
private theorem nondetElimM_singleton_out {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    (Block.nondetElimM [s] σ).1 = (Stmt.nondetElimM s σ).1 := by
  rw [Block.nondetElimM_cons_out, nondetElimM_nil, List.append_nil]

/-- Normal form: a singleton block advances the generator state exactly as its
single statement does. -/
private theorem nondetElimM_singleton_state {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P]
    [HasBool P] (s : Stmt P (Cmd P)) (σ : StringGenState) :
    (Block.nondetElimM [s] σ).2 = (Stmt.nondetElimM s σ).2 := by
  rw [Block.nondetElimM_cons_state, nondetElimM_nil]

/-- Normal form: the pass leaves a command statement and the generator state
unchanged. -/
private theorem nondetElimM_cmd {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (c : Cmd P) (σ : StringGenState) :
    Stmt.nondetElimM (P := P) (.cmd c) σ = ([.cmd c], σ) := by
  simp [Stmt.nondetElimM]

/-- Normal form: the pass leaves an `.exit` statement and the generator state
unchanged. -/
private theorem nondetElimM_exit {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (l : String) (md : MetaData P) (σ : StringGenState) :
    Stmt.nondetElimM (P := P) (CmdT := Cmd P) (.exit l md) σ = ([.exit l md], σ) := by
  simp [Stmt.nondetElimM]

/-- Normal form: the pass leaves a `.typeDecl` statement and the generator state
unchanged. -/
private theorem nondetElimM_typeDecl {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (t : TypeConstructor) (md : MetaData P) (σ : StringGenState) :
    Stmt.nondetElimM (P := P) (CmdT := Cmd P) (.typeDecl t md) σ = ([.typeDecl t md], σ) := by
  simp [Stmt.nondetElimM]

/-- Every statement rewrites to a single statement, except nondeterministic
conditionals and loops, which gain a guard preheader. -/
private theorem stmt_nondetElimM_shape {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    (∃ s', (Stmt.nondetElimM s σ).1 = [s']) ∨
    (∃ tss ess md, s = .ite .nondet tss ess md) ∨
    (∃ m inv body md, s = .loop .nondet m inv body md) := by
  cases s with
  | cmd c => exact .inl ⟨.cmd c, by rw [nondetElimM_cmd]⟩
  | block l bss md => exact .inl ⟨_, Stmt.nondetElimM_block_out l bss md σ⟩
  | ite c tss ess md =>
    cases c with
    | det e => exact .inl ⟨_, Stmt.nondetElimM_ite_det_out e tss ess md σ⟩
    | nondet => exact .inr (.inl ⟨tss, ess, md, rfl⟩)
  | loop g m inv body md =>
    cases g with
    | det e => exact .inl ⟨_, Stmt.nondetElimM_loop_det_out e m inv body md σ⟩
    | nondet => exact .inr (.inr ⟨m, inv, body, md, rfl⟩)
  | exit l md => exact .inl ⟨.exit l md, by rw [nondetElimM_exit]⟩
  | typeDecl t md => exact .inl ⟨.typeDecl t md, by rw [nondetElimM_typeDecl]⟩

/-! ### Tail-guard definedness transport -/

/-- The pending-latch tail-definedness condition on a configuration is preserved
by any target run: a generated guard register, once defined, stays defined. -/
private theorem NdTailCfg.run {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [DecidableEq P.Ident]
    {tail : Option (P.Ident × MetaData P)} {c c' : Config P (Cmd P)} {tr : Trace P}
    (h : NdTailCfg tail c) (hrun : StepStmtStarE P (EvalCmdE P) c tr c') :
    NdTailCfg tail c' :=
  fun g md ht =>
    Config.varsDefined_star_ofE (fun he hs => evalCmdE_preserves_isSome he hs) hrun (h g md ht)

/-- A statement configuration satisfies the tail-definedness condition whenever
its store does. -/
private theorem NdTailCfg.of_def {P : PureExpr} {tail : Option (P.Ident × MetaData P)}
    {ρ : Env P} (s : Stmt P (Cmd P)) (h : NdTailDef tail ρ.store) :
    NdTailCfg tail (.stmt s ρ) :=
  fun g md ht _ hy => hy ▸ h g md ht

/-- The tail-definedness condition transfers from a configuration to the `.seq`
built on it; both read the same environment. -/
private theorem NdTailCfg.seq_of {P : PureExpr} {tail : Option (P.Ident × MetaData P)}
    {c : Config P (Cmd P)} {R : List (Stmt P (Cmd P))} (h : NdTailCfg tail c) :
    NdTailCfg tail (.seq c R) := h

/-- The tail-definedness condition transfers from a `.seq` configuration to its
inner configuration. -/
private theorem NdTailCfg.seq_inner {P : PureExpr} {tail : Option (P.Ident × MetaData P)}
    {c : Config P (Cmd P)} {R : List (Stmt P (Cmd P))} (h : NdTailCfg tail (.seq c R)) :
    NdTailCfg tail c := h

/-- Extract the tail-definedness condition on a terminal configuration's store. -/
private theorem NdTailDef.of_terminal {P : PureExpr} {tail : Option (P.Ident × MetaData P)}
    {ρ : Env P} (h : NdTailCfg tail (.terminal ρ)) : NdTailDef tail ρ.store :=
  fun g md ht => h g md ht g rfl

/-- With no pending latch guard, the tail-definedness condition holds of every
store vacuously. -/
private theorem NdTailDef.none' {P : PureExpr} (σ : SemanticStore P) :
    NdTailDef (none : Option (P.Ident × MetaData P)) σ :=
  fun _ _ h => by cases h

/-- With no pending latch guard, the tail-definedness condition holds of every
configuration vacuously. -/
private theorem NdTailCfg.none' {P : PureExpr} (c : Config P (Cmd P)) :
    NdTailCfg (none : Option (P.Ident × MetaData P)) c :=
  fun _ _ h => by cases h

/-! ### Derived constructors -/

/-- Derived `NdSim.stmts` constructor with no pending latch guard: from a leaf
state, a rewritten statement list simulates its source list. -/
private theorem NdSim.stmts_none {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    {σ : StringGenState} {ss : List (Stmt P (Cmd P))} {ρs ρt : Env P}
    (hwf : StringGenState.WF σ) (hl : NdLeaf σ ρs ρt)
    (hng : SrcNoGenWrites (P := P) NondetElim.isGeneratedName ss)
    (hread : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName ss) :
    NdSim none (Block.nondetElimM ss σ).2 (.stmts ss ρs)
      (.stmts (Block.nondetElimM ss σ).1 ρt) := by
  have h := NdSim.stmts (tail := none) hwf hl hng hread (NdTailDef.none' _)
  simpa [ndTail] using h

/-- Derived constructor: a simulation of inner configurations lifts to a
simulation of the two `.seq`s that have an empty continuation. -/
private theorem NdSim.seq_nil {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    {σe : StringGenState} {inner inner' : Config P (Cmd P)}
    (h : NdSim none σe inner inner') (hwf : StringGenState.WF σe) :
    NdSim none σe (.seq inner []) (.seq inner' []) := by
  have h' := NdSim.seq (tail := none) (rest := []) h hwf noGen_nil
    Block.exprsShapeFree_nil (NdTailCfg.none' _)
  rw [nondetElimM_nil] at h'
  simpa [ndTail] using h'


/-! ### One-step simulation of leaf configurations -/

/-- A single-statement rewrite simulates one source statement step. -/
private theorem step_stmt {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident]
    {σ : StringGenState} {s s' : Stmt P (Cmd P)} {ρs ρt : Env P} {e : Trace P}
    {cs' : Config P (Cmd P)}
    (hwf : StringGenState.WF σ) (hl : NdLeaf σ ρs ρt)
    (hng : SrcNoGenWrites (P := P) NondetElim.isGeneratedName [s])
    (hread : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName [s])
    (hout : (Stmt.nondetElimM s σ).1 = [s'])
    (hsourceWF : WellFormedStore ρs.store ρs.factory)
    (htargetWF : WellFormedStore ρt.store ρt.factory)
    (hcongr : WellFormedSemanticEvalExprCongr ρs.factory)
    (hmono : WellFormedSemanticEvalMono ρs.factory)
    (hstep : StepStmtE P (EvalCmdE P) (.stmt s ρs) e cs') :
    ∃ ct' e', StepStmtStarE P (EvalCmdE P) (.stmt s' ρt) e' ct' ∧
      NETraceRel (P := P) e e' ∧
      NdSim none (Stmt.nondetElimM s σ).2 cs' ct' := by
  have hfac : ρs.factory = ρt.factory := hl.ext.1
  have hguard : ∀ {c b : P.Expr}, P.eval ρs.factory ρs.store c = some b →
      P.eval ρt.factory ρt.store c = some b := by
    intro c b hc
    rw [← hfac]
    exact hmono c b ρs.store ρt.store
      (storeAgreement_supplies_mono_premise _ _ hl.ext.2.2.1) hc
  have hreadStmt : Stmt.exprsShapeFree (P := P)
      NondetElim.isGeneratedName s :=
    Block.exprsShapeFree_singleton.mp hread
  cases s with
  | cmd c =>
    simp only [nondetElimM_cmd] at hout ⊢
    obtain rfl := (List.singleton_inj.mp hout).symm
    obtain ⟨σs', heval, rfl⟩ := StepStmtE.cmd_cases hstep
    obtain ⟨σt', hevt, htr, hl'⟩ :=
      hl.cmd_step hng hread hsourceWF htargetWF hcongr hmono heval
    exact ⟨_, _, StepStmtStarE.single (.step_cmd hevt), htr, .terminal hl'⟩
  | block l bss md =>
    rw [Stmt.nondetElimM_block_out] at hout
    obtain rfl := (List.singleton_inj.mp hout).symm
    obtain ⟨rfl, hadmin⟩ := stepE_stmt_admin (fun _ h => by cases h) hstep
    cases hadmin
    rw [Stmt.nondetElimM_block_state]
    exact ⟨_, [], StepStmtStarE.single (.step_admin .step_block), .nil,
      .block (NdSim.stmts_none hwf hl (noGen_block hng)
          (Stmt.exprsShapeFree_block.mp hreadStmt)) hl.ext.2.2
        (SemanticStore.isReserved.mono (Block.nondetElimM_genStep bss σ) hl.fresh)⟩
  | ite c tss ess md =>
    cases c with
    | det c =>
      rw [Stmt.nondetElimM_ite_det_out] at hout
      obtain rfl := (List.singleton_inj.mp hout).symm
      obtain ⟨rfl, hadmin⟩ := stepE_stmt_admin (fun _ h => by cases h) hstep
      rw [Stmt.nondetElimM_ite_det_state]
      have hstepT : StringGenState.GenStep σ
          (Block.nondetElimM ess (Block.nondetElimM tss σ).2).2 :=
        (Block.nondetElimM_genStep tss σ).trans (Block.nondetElimM_genStep ess _)
      have hfresh := SemanticStore.isReserved.mono hstepT hl.fresh
      cases hadmin with
      | step_ite_true hc =>
        exact ⟨_, [], StepStmtStarE.single (.step_admin (.step_ite_true (hguard hc))), .nil,
          .block (NdSim.stmts_none hwf hl (noGen_ite_then hng)
            (Stmt.exprsShapeFree_ite.mp hreadStmt).2.1) hl.ext.2.2 hfresh⟩
      | step_ite_false hc =>
        have hstep₁ := Block.nondetElimM_genStep tss σ
        exact ⟨_, [], StepStmtStarE.single (.step_admin (.step_ite_false (hguard hc))), .nil,
          .block (NdSim.stmts_none (hstep₁.wf_mono hwf) (hl.mono hstep₁)
            (noGen_ite_else hng) (Stmt.exprsShapeFree_ite.mp hreadStmt).2.2) hl.ext.2.2 hfresh⟩
    | nondet =>
      rw [Stmt.nondetElimM_ite_nondet_out] at hout
      simp at hout
  | loop g m inv body md =>
    cases g with
    | det c =>
      rw [Stmt.nondetElimM_loop_det_out] at hout
      obtain rfl := (List.singleton_inj.mp hout).symm
      obtain ⟨rfl, hadmin⟩ := stepE_stmt_admin (fun _ h => by cases h) hstep
      cases hadmin with
      | step_loop_enter hc =>
        refine ⟨_, [], StepStmtStarE.single (.step_admin (.step_loop_enter (hguard hc))), .nil, ?_⟩
        have hinner : NdSim none σ (.block none ρs.store (.stmts body ρs))
            (.block none ρt.store (.stmts (Block.nondetElimM body σ).1 ρt)) :=
          .block (NdSim.stmts_none hwf hl (noGen_loop hng)
            (Stmt.exprsShapeFree_loop.mp hreadStmt).2.2.2) hl.ext.2.2 hl.fresh
        have h := NdSim.seq (tail := none) (rest := [.loop (.det c) m inv body md])
          hinner hwf hng hread (NdTailCfg.none' _)
        rw [nondetElimM_singleton_state, nondetElimM_singleton_out,
          Stmt.nondetElimM_loop_det_out] at h
        simpa [ndTail] using h
      | step_loop_exit hc =>
        exact ⟨_, [], StepStmtStarE.single (.step_admin (.step_loop_exit (hguard hc))), .nil,
          .terminal (hl.mono (Stmt.nondetElimM_genStep _ σ))⟩
    | nondet =>
      rw [Stmt.nondetElimM_loop_nondet_out] at hout
      simp at hout
  | exit l md =>
    simp only [nondetElimM_exit] at hout ⊢
    obtain rfl := (List.singleton_inj.mp hout).symm
    obtain ⟨rfl, hadmin⟩ := stepE_stmt_admin (fun _ h => by cases h) hstep
    cases hadmin
    exact ⟨_, [], StepStmtStarE.single (.step_admin .step_exit), .nil, .exiting hl⟩
  | typeDecl t md =>
    simp only [nondetElimM_typeDecl] at hout ⊢
    obtain rfl := (List.singleton_inj.mp hout).symm
    obtain ⟨rfl, hadmin⟩ := stepE_stmt_admin (fun _ h => by cases h) hstep
    cases hadmin
    exact ⟨_, [], StepStmtStarE.single (.step_admin .step_typeDecl), .nil, .terminal hl⟩

/-- A statement-list leaf simulates one source step; a nondeterministic head
statement moves to its preheader state without consuming a target command. -/
private theorem step_stmts {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    {tail : Option (P.Ident × MetaData P)} {σ : StringGenState}
    {ss : List (Stmt P (Cmd P))} {ρs ρt : Env P} {e : Trace P} {cs' : Config P (Cmd P)}
    (hwf : StringGenState.WF σ) (hl : NdLeaf σ ρs ρt)
    (hng : SrcNoGenWrites (P := P) NondetElim.isGeneratedName ss)
    (hread : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName ss)
    (htail : NdTailDef tail ρt.store)
    (hstep : StepStmtE P (EvalCmdE P) (.stmts ss ρs) e cs') :
    ∃ ct' e', StepStmtStarE P (EvalCmdE P)
        (.stmts ((Block.nondetElimM ss σ).1 ++ ndTail tail) ρt) e' ct' ∧
      NETraceRel (P := P) e e' ∧
      NdSim tail (Block.nondetElimM ss σ).2 cs' ct' := by
  obtain ⟨rfl, hcases⟩ := stepE_stmts_cases hstep
  rcases hcases with ⟨rfl, rfl⟩ | ⟨s, rest, rfl, rfl⟩
  · simp only [nondetElimM_nil, List.nil_append]
    cases tail with
    | none => exact ⟨_, [], StepStmtStarE.single (.step_admin .step_stmts_nil), .nil, .terminal hl⟩
    | some gm =>
      obtain ⟨g, md⟩ := gm
      exact ⟨_, [], .refl _, .nil, .pendingHavoc hl (htail g md rfl)⟩
  · have hng₁ := noGen_head hng
    have hngr := noGen_tail hng
    have ⟨hread₁, hreadr⟩ := Block.exprsShapeFree_cons_iff.mp hread
    have hreadHead : Block.exprsShapeFree (P := P)
        NondetElim.isGeneratedName [s] :=
      Block.exprsShapeFree_singleton.mpr hread₁
    have hwf₁ : StringGenState.WF (Stmt.nondetElimM s σ).2 :=
      (Stmt.nondetElimM_genStep s σ).wf_mono hwf
    rw [Block.nondetElimM_cons_out, Block.nondetElimM_cons_state]
    rcases stmt_nondetElimM_shape s σ with
      ⟨s', hs'⟩ | ⟨tss, ess, md, rfl⟩ | ⟨m, inv, body, md, rfl⟩
    · rw [hs', List.singleton_append, List.cons_append]
      exact ⟨_, [], StepStmtStarE.single (.step_admin .step_stmts_cons), .nil,
        .seq (.stmt hwf hl hng₁ hreadHead hs') hwf₁ hngr hreadr
          (NdTailCfg.of_def _ htail)⟩
    · rw [Stmt.nondetElimM_ite_nondet_out]
      dsimp only
      simp only [List.cons_append, List.nil_append]
      exact ⟨_, [], StepStmtStarE.single (.step_admin .step_stmts_cons), .nil,
        .seqIte hwf hl hng₁ hreadHead hngr hreadr htail⟩
    · rw [Stmt.nondetElimM_loop_nondet_out]
      dsimp only
      simp only [List.cons_append, List.nil_append]
      exact ⟨_, [], StepStmtStarE.single (.step_admin .step_stmts_cons), .nil,
        .seqLoop hwf hl hng₁ hreadHead hngr hreadr htail⟩


/-- Preheader of a nondeterministic `ite`: the source branch choice drives the
target guard initialization, and the target then enters the matching branch
of the rewritten deterministic `ite`, emitting no events. -/
private theorem step_seqIte {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident] [LawfulHasIdent P] [LawfulHasFvar P] [LawfulHasVal P]
    {tail : Option (P.Ident × MetaData P)} {σ : StringGenState}
    {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} {rest : List (Stmt P (Cmd P))}
    {ρs ρt : Env P} {e : Trace P} {cs' : Config P (Cmd P)}
    (hwf : StringGenState.WF σ) (hl : NdLeaf σ ρs ρt)
    (hng : SrcNoGenWrites (P := P) NondetElim.isGeneratedName [.ite .nondet tss ess md])
    (hread : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName
      [.ite .nondet tss ess md])
    (hngr : SrcNoGenWrites (P := P) NondetElim.isGeneratedName rest)
    (hreadr : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName rest)
    (htail : NdTailDef tail ρt.store)
    (hvar : WellFormedSemanticEvalVar ρs.factory) (hmono : WellFormedSemanticEvalMono ρs.factory)
    (hstep : StepStmtE P (EvalCmdE P) (.seq (.stmt (.ite .nondet tss ess md) ρs) rest) e cs') :
    ∃ ct' e', StepStmtStarE P (EvalCmdE P)
        (.seq (.stmt (.cmd (HasInit.init (ndIteGuard (P := P) σ) HasBool.boolTy .nondet md)) ρt)
          (ndIteTgt tss ess md σ ::
            ((Block.nondetElimM rest (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2).1 ++
              ndTail tail))) e' ct' ∧
      NETraceRel (P := P) e e' ∧
      NdSim tail (Block.nondetElimM rest (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2).2
        cs' ct' := by
  have hfac : ρs.factory = ρt.factory := hl.ext.1
  have hvarT : WellFormedSemanticEvalVar ρt.factory := hfac ▸ hvar
  have hmonoT : WellFormedSemanticEvalMono ρt.factory := hfac ▸ hmono
  have hstep₁ := StringGenState.GenStep.of_gen NondetElim.prefixIte σ
  have hwf₁ := hstep₁.wf_mono hwf
  have hstepR : StringGenState.GenStep (StringGenState.gen NondetElim.prefixIte σ).2
      (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2 := by
    rw [Stmt.nondetElimM_ite_nondet_state]
    exact (Block.nondetElimM_genStep tss _).trans (Block.nondetElimM_genStep ess _)
  have hwfR : StringGenState.WF (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2 :=
    (Stmt.nondetElimM_genStep _ σ).wf_mono hwf
  have htc : NdTailCfg tail
      (.seq (.stmt (.cmd (HasInit.init (ndIteGuard (P := P) σ) HasBool.boolTy .nondet md)) ρt)
        (ndIteTgt tss ess md σ ::
          ((Block.nondetElimM rest (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2).1 ++
            ndTail tail))) :=
    NdTailCfg.seq_of (NdTailCfg.of_def _ htail)
  have hreadIte := Stmt.exprsShapeFree_ite.mp
    (Block.exprsShapeFree_singleton.mp hread)
  rcases stepE_seq_cases hstep with ⟨inner', hinner, rfl⟩ | ⟨_, h, _, _⟩ | ⟨_, _, h, _, _⟩
  · obtain ⟨rfl, hadmin⟩ := stepE_stmt_admin (fun _ h => by cases h) hinner
    cases hadmin with
    | step_ite_nondet_true =>
      have hv := (HasBool.boolIsValOfTy ρt.factory).1
      obtain ⟨hnone, hl₁⟩ := hl.init_guard hwf (NondetElim.isGeneratedName_gen.1 σ) hv
      have hg := eval_guard_update (σ := ρt.store) (g := ndIteGuard (P := P) σ) hv hvarT hmonoT
      have hrun := ReflTransTrace.trans _ (tgt_init_then (md := md) (X := ndIteTgt tss ess md σ)
          (R := (Block.nondetElimM rest (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2).1 ++
            ndTail tail) hnone hv hvarT)
        (StepStmtStarE.single (.step_seq_inner (.step_admin (.step_ite_true hg))))
      exact ⟨_, _, hrun, .nil,
        .seq (.block (NdSim.stmts_none hwf₁ hl₁ (noGen_ite_then hng) hreadIte.2.1)
          hl₁.ext.2.2
          (SemanticStore.isReserved.mono hstepR hl₁.fresh)) hwfR hngr hreadr
          (htc.run hrun).seq_inner⟩
    | step_ite_nondet_false =>
      have hv := (HasBool.boolIsValOfTy ρt.factory).2
      obtain ⟨hnone, hl₁⟩ := hl.init_guard hwf (NondetElim.isGeneratedName_gen.1 σ) hv
      have hg := eval_guard_update (σ := ρt.store) (g := ndIteGuard (P := P) σ) hv hvarT hmonoT
      have hrun := ReflTransTrace.trans _ (tgt_init_then (md := md) (X := ndIteTgt tss ess md σ)
          (R := (Block.nondetElimM rest (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2).1 ++
            ndTail tail) hnone hv hvarT)
        (StepStmtStarE.single (.step_seq_inner (.step_admin (.step_ite_false hg))))
      have hstep₂ := Block.nondetElimM_genStep tss (StringGenState.gen NondetElim.prefixIte σ).2
      exact ⟨_, _, hrun, .nil,
        .seq (.block (NdSim.stmts_none (hstep₂.wf_mono hwf₁) (hl₁.mono hstep₂)
            (noGen_ite_else hng) hreadIte.2.2) hl₁.ext.2.2
          (SemanticStore.isReserved.mono hstepR hl₁.fresh)) hwfR hngr hreadr
          (htc.run hrun).seq_inner⟩
  · cases h
  · cases h

/-- Preheader of a nondeterministic loop: the source's first enter/exit choice
drives the target guard initialization, after which the rewritten
deterministic loop takes the same decision, emitting no events. -/
private theorem step_seqLoop {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident] [LawfulHasIdent P] [LawfulHasFvar P] [LawfulHasVal P]
    {tail : Option (P.Ident × MetaData P)} {σ : StringGenState}
    {m : Option P.Expr} {inv : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
    {md : MetaData P} {rest : List (Stmt P (Cmd P))}
    {ρs ρt : Env P} {e : Trace P} {cs' : Config P (Cmd P)}
    (hwf : StringGenState.WF σ) (hl : NdLeaf σ ρs ρt)
    (hng : SrcNoGenWrites (P := P) NondetElim.isGeneratedName [.loop .nondet m inv body md])
    (hread : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName
      [.loop .nondet m inv body md])
    (hngr : SrcNoGenWrites (P := P) NondetElim.isGeneratedName rest)
    (hreadr : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName rest)
    (htail : NdTailDef tail ρt.store)
    (hvar : WellFormedSemanticEvalVar ρs.factory) (hmono : WellFormedSemanticEvalMono ρs.factory)
    (hstep : StepStmtE P (EvalCmdE P)
      (.seq (.stmt (.loop .nondet m inv body md) ρs) rest) e cs') :
    ∃ ct' e', StepStmtStarE P (EvalCmdE P)
        (.seq (.stmt (.cmd (HasInit.init (ndLoopGuard (P := P) σ) HasBool.boolTy .nondet md)) ρt)
          (ndLoopTgt m inv body md σ ::
            ((Block.nondetElimM rest (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2).1 ++
              ndTail tail))) e' ct' ∧
      NETraceRel (P := P) e e' ∧
      NdSim tail (Block.nondetElimM rest (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2).2
        cs' ct' := by
  have hfac : ρs.factory = ρt.factory := hl.ext.1
  have hvarT : WellFormedSemanticEvalVar ρt.factory := hfac ▸ hvar
  have hmonoT : WellFormedSemanticEvalMono ρt.factory := hfac ▸ hmono
  have hstep₁ := StringGenState.GenStep.of_gen NondetElim.prefixLoop σ
  have hwf₁ := hstep₁.wf_mono hwf
  have hσr : (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2 =
      (Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2).2 :=
    Stmt.nondetElimM_loop_nondet_state m inv body md σ
  have hstepR : StringGenState.GenStep (StringGenState.gen NondetElim.prefixLoop σ).2
      (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2 := by
    rw [hσr]
    exact Block.nondetElimM_genStep body _
  have hwfR : StringGenState.WF (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2 :=
    (Stmt.nondetElimM_genStep _ σ).wf_mono hwf
  have htc : NdTailCfg tail
      (.seq (.stmt (.cmd (HasInit.init (ndLoopGuard (P := P) σ) HasBool.boolTy .nondet md)) ρt)
        (ndLoopTgt m inv body md σ ::
          ((Block.nondetElimM rest (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2).1 ++
            ndTail tail))) :=
    NdTailCfg.seq_of (NdTailCfg.of_def _ htail)
  have hreadLoop := Stmt.exprsShapeFree_loop.mp
    (Block.exprsShapeFree_singleton.mp hread)
  rcases stepE_seq_cases hstep with ⟨inner', hinner, rfl⟩ | ⟨_, h, _, _⟩ | ⟨_, _, h, _, _⟩
  · obtain ⟨rfl, hadmin⟩ := stepE_stmt_admin (fun _ h => by cases h) hinner
    cases hadmin with
    | step_loop_nondet_enter =>
      have hv := (HasBool.boolIsValOfTy ρt.factory).1
      obtain ⟨hnone, hl₁⟩ := hl.init_guard hwf (NondetElim.isGeneratedName_gen.2 σ) hv
      have hg := eval_guard_update (σ := ρt.store) (g := ndLoopGuard (P := P) σ) hv hvarT hmonoT
      have hrun := ReflTransTrace.trans _
        (tgt_init_then (md := md) (X := ndLoopTgt m inv body md σ)
          (R := (Block.nondetElimM rest (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2).1 ++
            ndTail tail) hnone hv hvarT)
        (StepStmtStarE.single (.step_seq_inner (.step_admin (.step_loop_enter hg))))
      have hgdef : (SemanticStore.update ρt.store (ndLoopGuard (P := P) σ) HasBool.tt
          (ndLoopGuard (P := P) σ)).isSome = true := by
        simp [SemanticStore.update]
      have hbody := NdSim.stmts (tail := some (ndLoopGuard (P := P) σ, md)) hwf₁ hl₁
        (noGen_loop hng) hreadLoop.2.2.2 (fun g' md' h => by cases h; exact hgdef)
      have hiter := NdSim.iter (m := m) (inv := inv) hwf₁ (noGen_loop hng)
        hreadLoop.2.2.2 hl₁.ext.2.2 hl₁.fresh hgdef hbody
      rw [← hσr] at hiter
      exact ⟨_, _, hrun, .nil,
        .seq hiter hwfR hngr hreadr (htc.run hrun).seq_inner⟩
    | step_loop_nondet_exit =>
      have hv := (HasBool.boolIsValOfTy ρt.factory).2
      obtain ⟨hnone, hl₁⟩ := hl.init_guard hwf (NondetElim.isGeneratedName_gen.2 σ) hv
      have hg := eval_guard_update (σ := ρt.store) (g := ndLoopGuard (P := P) σ) hv hvarT hmonoT
      have hrun := ReflTransTrace.trans _
        (tgt_init_then (md := md) (X := ndLoopTgt m inv body md σ)
          (R := (Block.nondetElimM rest (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2).1 ++
            ndTail tail) hnone hv hvarT)
        (StepStmtStarE.single (.step_seq_inner (.step_admin (.step_loop_exit hg))))
      exact ⟨_, _, hrun, .nil,
        .seq (.terminal (hl₁.mono hstepR)) hwfR hngr hreadr
          (htc.run hrun).seq_inner⟩
  · cases h
  · cases h

/-- Loop latch: the source's enter/exit choice at the loop head drives the
pending target latch havoc; the target leaves the iteration scope and its
rewritten loop takes the same decision, realigning silently. -/
private theorem step_headStmt {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident] [LawfulHasFvar P] [LawfulHasVal P]
    {σ σb : StringGenState} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P} {σps σpt : SemanticStore P}
    {ρsb ρtb : Env P} {e : Trace P} {cs' : Config P (Cmd P)}
    (hinv : NdHeadInv σ σb body σps σpt ρsb ρtb)
    (hvar : WellFormedSemanticEvalVar ρsb.factory) (hmono : WellFormedSemanticEvalMono ρsb.factory)
    (hstep : StepStmtE P (EvalCmdE P)
      (.seq (.stmt (.loop .nondet m inv body md)
        { ρsb with store := projectStore σps ρsb.store }) []) e cs') :
    ∃ ct' e', StepStmtStarE P (EvalCmdE P)
        (.seq (.block none σpt (.stmts [.cmd (HasHavoc.havoc (ndLoopGuard (P := P) σ) md)] ρtb))
          [ndLoopTgt m inv body md σ]) e' ct' ∧
      NETraceRel (P := P) e e' ∧
      NdSim none
        (Block.nondetElimM body
          (StringGenState.gen NondetElim.prefixLoop σ).2).2 cs' ct' := by
  have hfac : ρsb.factory = ρtb.factory := hinv.leaf.ext.1
  have hvarT : WellFormedSemanticEvalVar ρtb.factory := hfac ▸ hvar
  have hmonoT : WellFormedSemanticEvalMono ρtb.factory := hfac ▸ hmono
  have hgx : NdExtra (P := P) (ndLoopGuard (P := P) σ) :=
    ⟨_, NondetElim.isGeneratedName_gen.2 σ, rfl⟩
  obtain ⟨prev, hprev⟩ := Option.isSome_iff_exists.mp hinv.guard
  have hprevTy := hinv.leaf.typed _ prev hgx hprev
  have hwfE : StringGenState.WF
      (Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2).2 :=
    (Block.nondetElimM_genStep body _).wf_mono hinv.wf
  rcases stepE_seq_cases hstep with ⟨inner', hinner, rfl⟩ | ⟨_, h, _, _⟩ | ⟨_, _, h, _, _⟩
  · obtain ⟨rfl, hadmin⟩ := stepE_stmt_admin (fun _ h => by cases h) hinner
    cases hadmin with
    | step_loop_nondet_enter =>
      have hv := (HasBool.boolIsValOfTy ρtb.factory).1
      have hl' := hinv.leaf.latch hgx hv hinv.parent hinv.parentFresh
      have hg := eval_guard_latch (σ := ρtb.store) hinv.parentGuard hv hvarT hmonoT
      have hrun := ReflTransTrace.trans _
        (tgt_latch (md := md) (σpt := σpt) (L' := ndLoopTgt m inv body md σ) hprev hprevTy hv hvarT)
        (StepStmtStarE.single (.step_seq_inner (.step_admin (.step_loop_enter hg))))
      have hgdef : (projectStore σpt (SemanticStore.update ρtb.store (ndLoopGuard (P := P) σ)
          HasBool.tt) (ndLoopGuard (P := P) σ)).isSome = true := by
        simp [projectStore, hinv.parentGuard, SemanticStore.update]
      have hbody := NdSim.stmts (tail := some (ndLoopGuard (P := P) σ, md)) hinv.wf hl'
        hinv.noGen hinv.noRead (fun g' md' h => by cases h; exact hgdef)
      have hiter := NdSim.iter (m := m) (inv := inv) hinv.wf hinv.noGen hinv.noRead
        hl'.ext.2.2 hl'.fresh hgdef hbody
      exact ⟨_, _, hrun, .nil, NdSim.seq_nil hiter hwfE⟩
    | step_loop_nondet_exit =>
      have hv := (HasBool.boolIsValOfTy ρtb.factory).2
      have hl' := hinv.leaf.latch hgx hv hinv.parent hinv.parentFresh
      have hg := eval_guard_latch (σ := ρtb.store) hinv.parentGuard hv hvarT hmonoT
      have hrun := ReflTransTrace.trans _
        (tgt_latch (md := md) (σpt := σpt) (L' := ndLoopTgt m inv body md σ) hprev hprevTy hv hvarT)
        (StepStmtStarE.single (.step_seq_inner (.step_admin (.step_loop_exit hg))))
      exact ⟨_, _, hrun, .nil,
        NdSim.seq_nil (.terminal (hl'.mono (Block.nondetElimM_genStep body _))) hwfE⟩
  · cases h
  · cases h


/-! ### Forward simulation -/

/-- One source event step is matched by a finite target run under
`NETraceRel`; user commands replay in lockstep and all generated guard steps are
silent. -/
private theorem NdSim.step {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident] [LawfulHasIdent P] [LawfulHasFvar P] [LawfulHasVal P]
    {tail : Option (P.Ident × MetaData P)} {σe : StringGenState}
    {cs ct : Config P (Cmd P)} (h : NdSim tail σe cs ct) :
    ∀ {e : Trace P} {cs' : Config P (Cmd P)},
      Config.storeWellDefined cs →
      Config.storeWellDefined ct →
      WellFormedSemanticEvalExprCongr cs.getEnv.factory →
      WellFormedSemanticEvalVar cs.getEnv.factory →
      WellFormedSemanticEvalMono cs.getEnv.factory →
      StepStmtE P (EvalCmdE P) cs e cs' →
      ∃ ct' e', StepStmtStarE P (EvalCmdE P) ct e' ct' ∧
        NETraceRel (P := P) e e' ∧ NdSim tail σe cs' ct' := by
  induction h with
  | stmts hwf hl hng hread htail =>
    intro e cs' _ _ _ _ _ hstep
    exact step_stmts hwf hl hng hread htail hstep
  | stmt hwf hl hng hread hout =>
    intro e cs' hsourceWF htargetWF hcongr _ hmono hstep
    exact step_stmt hwf hl hng hread hout hsourceWF htargetWF hcongr hmono hstep
  | terminal _ =>
    intro e cs' _ _ _ _ _ hstep
    exact (stepE_terminal_false hstep).elim
  | pendingHavoc _ _ =>
    intro e cs' _ _ _ _ _ hstep
    exact (stepE_terminal_false hstep).elim
  | exiting _ =>
    intro e cs' _ _ _ _ _ hstep
    exact (StepStmtE.exiting_false hstep).elim
  | seq hinner hwf hng hread htail ih =>
    intro e cs' hsourceWF htargetWF hcongr hvar hmono hstep
    rcases stepE_seq_cases hstep with
      ⟨inner'', hinnerStep, rfl⟩ | ⟨ρ, rfl, rfl, rfl⟩ | ⟨l, ρ, rfl, rfl, rfl⟩
    · obtain ⟨ct', e', hrun, htr, hsim⟩ :=
        ih hsourceWF htargetWF hcongr hvar hmono hinnerStep
      exact ⟨_, e', seq_inner_starE _ hrun, htr,
        .seq hsim hwf hng hread (htail.run hrun)⟩
    · cases hinner with
      | terminal hl =>
        exact ⟨_, [], StepStmtStarE.single (.step_admin .step_seq_done), .nil,
          .stmts hwf hl hng hread (NdTailDef.of_terminal htail)⟩
    · cases hinner with
      | exiting hl =>
        exact ⟨_, [], StepStmtStarE.single (.step_admin .step_seq_exit), .nil,
          .exiting (hl.mono (Block.nondetElimM_genStep _ _))⟩
  | block hinner hp hf ih =>
    intro e cs' hsourceWF htargetWF hcongr hvar hmono hstep
    rcases StepStmtE.block_cases hstep with
      ⟨inner'', hinnerStep, rfl⟩ | ⟨ρ, rfl, rfl, rfl⟩ | ⟨l', ρ, rfl, rfl, hlbl, rfl⟩ |
        ⟨l', ρ, rfl, rfl, hlbl, rfl⟩
    · obtain ⟨ct', e', hrun, htr, hsim⟩ :=
        ih hsourceWF.2 htargetWF.2 hcongr hvar hmono hinnerStep
      exact ⟨_, e', block_inner_starE hrun, htr, .block hsim hp hf⟩
    · cases hinner with
      | terminal hl =>
        exact ⟨_, [], StepStmtStarE.single (.step_admin .step_block_done), .nil,
          .terminal (hl.project hp hf)⟩
    · cases hinner with
      | exiting hl =>
        exact ⟨_, [], StepStmtStarE.single (.step_admin (.step_block_exit_match hlbl)), .nil,
          .terminal (hl.project hp hf)⟩
    · cases hinner with
      | exiting hl =>
        exact ⟨_, [], StepStmtStarE.single (.step_admin (.step_block_exit_mismatch hlbl)), .nil,
          .exiting (hl.project hp hf)⟩
  | seqIte hwf hl hng hread hngr hreadr htail =>
    intro e cs' _ _ _ hvar hmono hstep
    exact step_seqIte hwf hl hng hread hngr hreadr htail hvar hmono hstep
  | seqLoop hwf hl hng hread hngr hreadr htail =>
    intro e cs' _ _ _ hvar hmono hstep
    exact step_seqLoop hwf hl hng hread hngr hreadr htail hvar hmono hstep
  | iter hwf hng hread hp hf hg hbody ih =>
    intro e cs' hsourceWF htargetWF hcongr hvar hmono hstep
    rcases stepE_seq_cases hstep with ⟨inner'', hinnerStep, rfl⟩ | ⟨_, h, _, _⟩ | ⟨_, _, h, _, _⟩
    · rcases StepStmtE.block_cases hinnerStep with
        ⟨cs'', hbodyStep, rfl⟩ | ⟨ρ, rfl, rfl, rfl⟩ | ⟨l', ρ, rfl, rfl, hlbl, rfl⟩ |
          ⟨l', ρ, rfl, rfl, hlbl, rfl⟩
      · obtain ⟨ct', e', hrun, htr, hsim⟩ :=
          ih hsourceWF.2 htargetWF.2 hcongr hvar hmono hbodyStep
        exact ⟨_, e', seq_inner_starE _ (block_inner_starE hrun), htr,
          .iter hwf hng hread hp hf hg hsim⟩
      · cases hbody with
        | pendingHavoc hl hgdef =>
          exact ⟨_, [], .refl _, .nil, .headTerm ⟨hwf, hng, hread, hp, hf, hg, hl, hgdef⟩⟩
      · cases hlbl
      · cases hbody with
        | exiting hl =>
          exact ⟨_, [], StepStmtStarE.single (.step_admin (.step_seq_inner
              (.step_block_exit_mismatch hlbl))), .nil,
            .seqExit
              (hl.project hp
                (SemanticStore.isReserved.mono
                  (Block.nondetElimM_genStep _ _) hf))⟩
    · cases h
    · cases h
  | headTerm hinv =>
    intro e cs' _ _ _ _ _ hstep
    rcases stepE_seq_cases hstep with ⟨_, hinnerStep, rfl⟩ | ⟨_, h, rfl, rfl⟩ | ⟨_, _, h, _, _⟩
    · exact (stepE_terminal_false hinnerStep).elim
    · cases h
      exact ⟨_, [], .refl _, .nil, .headStmts hinv⟩
    · cases h
  | headStmts hinv =>
    intro e cs' _ _ _ _ _ hstep
    obtain ⟨rfl, hcases⟩ := stepE_stmts_cases hstep
    rcases hcases with ⟨h, _⟩ | ⟨_, _, h, rfl⟩
    · cases h
    · cases h
      exact ⟨_, [], .refl _, .nil, .headStmt hinv⟩
  | headStmt hinv =>
    intro e cs' _ _ _ hvar hmono hstep
    exact step_headStmt hinv hvar hmono hstep
  | seqExit hl =>
    intro e cs' _ _ _ _ _ hstep
    rcases stepE_seq_cases hstep with ⟨_, hinnerStep, rfl⟩ | ⟨_, h, _, _⟩ | ⟨_, _, h, rfl, rfl⟩
    · exact (StepStmtE.exiting_false hinnerStep).elim
    · cases h
    · cases h
      exact ⟨_, [], StepStmtStarE.single (.step_admin .step_seq_exit), .nil, .exiting hl⟩

/-- Every finite source trace prefix is matched by a target trace prefix
reaching a related configuration. -/
private theorem NdSim.trace {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident] [LawfulHasIdent P] [LawfulHasFvar P] [LawfulHasVal P]
    {tail : Option (P.Ident × MetaData P)} {σe : StringGenState}
    {cs ct cs' : Config P (Cmd P)} {tr : Trace P}
    (h : NdSim tail σe cs ct)
    (hcongr : WellFormedSemanticEvalExprCongr cs.getEnv.factory)
    (hsourceWF : Config.storeWellDefined cs)
    (htargetWF : Config.storeWellDefined ct)
    (hsourceVal : WellFormedSemanticEvalVal (P := P) cs.getEnv.factory)
    (htargetVal : WellFormedSemanticEvalVal (P := P) ct.getEnv.factory)
    (hvar : WellFormedSemanticEvalVar cs.getEnv.factory)
    (hmono : WellFormedSemanticEvalMono cs.getEnv.factory)
    (hrun : StepStmtStarE P (EvalCmdE P) cs tr cs') :
    ∃ ct' tr', StepStmtStarE P (EvalCmdE P) ct tr' ct' ∧
      NETraceRel (P := P) tr tr' ∧ NdSim tail σe cs' ct' := by
  induction hrun generalizing ct with
  | refl => exact ⟨ct, [], .refl _, .nil, h⟩
  | step c e c₁ rest c₂ hstep _ ih =>
    obtain ⟨ct₁, e', hrun₁, htr₁, h₁⟩ :=
      h.step hsourceWF htargetWF hcongr hvar hmono hstep
    have hsourceWF₁ : Config.storeWellDefined c₁ :=
      Config.storeWellDefined_step_evalCmdE hsourceVal hstep hsourceWF
    have htargetWF₁ : Config.storeWellDefined ct₁ :=
      Config.storeWellDefined_star_evalCmdE htargetVal hrun₁ htargetWF
    have hfac : c.getEnv.factory = c₁.getEnv.factory := stepE_preserves_factory hstep
    have htargetFac : ct.getEnv.factory = ct₁.getEnv.factory :=
      starE_preserves_factory hrun₁
    obtain ⟨ct₂, tr', hrun₂, htr₂, h₂⟩ :=
      ih h₁ (hfac ▸ hcongr) hsourceWF₁ htargetWF₁
        (hfac ▸ hsourceVal) (htargetFac ▸ htargetVal)
        (hfac ▸ hvar) (hfac ▸ hmono)
    exact ⟨ct₂, e' ++ tr', ReflTransTrace.trans _ hrun₁ hrun₂,
      htr₁.append htr₂, h₂⟩

end NondetElimTrace

open NondetElimTrace in
/-- `Block.nondetElim` overapproximates its source on event traces. For a
block that never writes or reads an `NondetElim.isGeneratedName` name, every
finite source trace prefix is matched by a target prefix under `NETraceRel`.
generated guard commands are event-silent and the source commands replay
one-for-one, so no event is inserted or dropped on either side.
Terminating and exiting runs preserve their outcome shape and end in an
environment extended only by generated guard registers. -/
theorem NondetElim.Internal.overapproximates_upto_base {P : PureExpr} [HasFvar P] [HasFvars P]
    [HasBoolOps P] [LawfulHasVal P] [HasIdent P] [HasInt P] [HasIntOps P] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasIdent P] [HasSubstFvar P] :
    Specification.Transform.OverapproximatesTracesUptoWhen
      (NondetElimTrace.NETraceRel (P := P))
      (fun x y => x = y)
      (Env.ExtendsWith (IdentOfStringKind NondetElim.isGeneratedName))
      (EventLang.imperativeBlockE P (Cmd P) (EvalCmdE P) ⟨String → Prop, BlockInitEnvWF⟩)
      (EventLang.imperativeBlockE P (Cmd P) (EvalCmdE P) ⟨String → Prop, BlockInitEnvWF⟩)
      (fun ss => some (Block.nondetElim ss))
      (fun ss => SrcNoGenWrites NondetElim.isGeneratedName ss
        ∧ Block.exprsShapeFree NondetElim.isGeneratedName ss)
      NondetElim.isGeneratedName NondetElim.isGeneratedName := by
  intro ss ss' ht hpre ρ₀ ρ₀' hEq hwf
  subst hEq
  simp only [Option.some.injEq] at ht
  subst ht
  obtain ⟨hng, hread⟩ := hpre
  change BlockInitEnvWF NondetElim.isGeneratedName ss ρ₀ at hwf
  have hsrc : ∀ x, NdExtra (P := P) x → ρ₀.store x = none :=
    fun x hx => hwf.definedVarsNotReserved x hx
  have hleaf : NdLeaf StringGenState.emp ρ₀ ρ₀ :=
    ⟨Env.ExtendsWith.refl _ _, hsrc, fun s hs _ => hsrc _ ⟨s, hs, rfl⟩,
      fun x v hx hv => by rw [hsrc x hx] at hv; cases hv⟩
  obtain ⟨σe, hsim₀⟩ : ∃ σe, NdSim none σe (.stmts ss ρ₀) (.stmts (Block.nondetElim ss) ρ₀) :=
    ⟨_, NdSim.stmts_none StringGenState.wf_emp hleaf hng hread⟩
  have hvar : WellFormedSemanticEvalVar (Config.stmts ss ρ₀).getEnv.factory := hwf.var
  have hmono : WellFormedSemanticEvalMono (Config.stmts ss ρ₀).getEnv.factory := hwf.mono
  have hcongr : WellFormedSemanticEvalExprCongr (Config.stmts ss ρ₀).getEnv.factory :=
    hwf.exprCongr
  have hstoreWF : Config.storeWellDefined (Config.stmts ss ρ₀) := hwf.storeWellDefined
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cfg trace hrun
    obtain ⟨ct', tr', hrun', htr, _⟩ := hsim₀.trace hcongr hstoreWF
      hstoreWF hwf.val hwf.val hvar hmono hrun
    exact ⟨ct', tr', hrun', htr⟩
  · intro ρ' trace hrun
    obtain ⟨ct', tr', hrun', htr, hsim⟩ := hsim₀.trace hcongr hstoreWF
      hstoreWF hwf.val hwf.val hvar hmono hrun
    cases hsim with
    | terminal hl => exact ⟨_, tr', hrun', hl.ext, htr⟩
  · intro lbl ρ' trace hrun
    obtain ⟨ct', tr', hrun', htr, hsim⟩ := hsim₀.trace hcongr hstoreWF
      hstoreWF hwf.val hwf.val hvar hmono hrun
    cases hsim with
    | exiting hl => exact ⟨_, tr', hrun', hl.ext, htr⟩
  · change BlockInitEnvWF NondetElim.isGeneratedName (Block.nondetElim ss) ρ₀
    have hinits := Block.nondetElim_initsUndefinedAndInhabited ss ρ₀
      hwf.defsUndefined hwf.definedVarsNotReserved hwf.initTypesInhabited
    exact ⟨hwf.toWellFormedSemanticEval, hwf.storeWellDefined, hinits.1,
      hwf.definedVarsNotReserved, hinits.2⟩

/-- Failure-flag overapproximation used by the
`StructuredToUnstructuredPipelineCorrect` composition. -/
theorem nondetElim_overapproximates_upto_local {P : PureExpr} [HasFvar P]
    [HasFvars P] [HasBoolOps P] [LawfulHasVal P] [HasIdent P] [HasInt P]
    [HasIntOps P] [DecidableEq P.Ident] [LawfulHasFvar P] [LawfulHasIdent P]
    [HasSubstFvar P] :
    Specification.Transform.OverapproximatesUptoWhen
      (· = ·)
      (Specification.Transform.EnvStoreAgree (P := P))
      (Lang.imperativeBlock (EvalCmd P) (isAtAssert P))
      (Lang.imperativeBlock (EvalCmd P) (isAtAssert P))
      (fun ss => some (Block.nondetElim ss))
      (fun ss => Block.uniqueInits ss ∧ SrcNoGenWrites (P := P) NondetElim.isGeneratedName ss)
      NondetElim.isGeneratedName NondetElim.isGeneratedName := by
  intro ss ss' ht hpre ρ₀ ρ₀' hEq hwf
  subst hEq
  simp only [Option.some.injEq] at ht
  subst ht
  obtain ⟨h_unique, h_writes⟩ := hpre
  obtain ⟨hwf_full, hstoreWF, h_inits, h_gens, h_src_inhab⟩ := hwf
  refine ⟨fun ρ' => ⟨fun hstar => ?_, fun lbl hstar => ?_⟩, ?_, ?_⟩
  · have h_term : StepStmtStar P (EvalCmd P) (.stmts ss ρ₀) (.terminal ρ') := by
      simpa [Lang.imperativeBlock] using hstar
    obtain ⟨ρ_out, h_run, h_off, h_fl⟩ :=
      nondetElim_sound_kind_compositional ss ρ₀ ρ' ρ₀
        rfl rfl (StoreAgreement.refl _) hwf_full h_gens h_gens h_inits
        h_writes h_unique h_term
    exact ⟨ρ_out, ⟨h_off, h_fl.symm⟩, by
      simpa [Lang.imperativeBlock] using h_run⟩
  · have h_exit : StepStmtStar P (EvalCmd P) (.stmts ss ρ₀) (.exiting lbl ρ') := by
      simpa [Lang.imperativeBlock] using hstar
    obtain ⟨ρ_out, h_run, h_off, h_fl⟩ :=
      nondetElim_sound_kind_exit_compositional ss ρ₀ ρ' ρ₀
        rfl rfl (StoreAgreement.refl _) hwf_full h_gens h_gens h_inits
        h_writes h_unique lbl h_exit
    exact ⟨ρ_out, ⟨h_off, h_fl.symm⟩, by
      simpa [Lang.imperativeBlock] using h_run⟩
  · intro h_src
    by_cases h_ρ₀_fail : ρ₀.hasFailure = true
    · refine ⟨(Config.stmts (Block.nondetElim ss) ρ₀ : Config P (Cmd P)), ?_, ?_⟩
      · simpa [Lang.imperativeBlock, Config.getEnv] using h_ρ₀_fail
      · simpa [Lang.imperativeBlock] using
          (ReflTrans.refl (Config.stmts (Block.nondetElim ss) ρ₀ : Config P (Cmd P)))
    · obtain ⟨cfg_s, h_cfg_fail, h_cfg_reach⟩ := h_src
      have h_reach : StepStmtStar P (EvalCmd P) (.stmts ss ρ₀) cfg_s := by
        simpa [Lang.imperativeBlock] using h_cfg_reach
      have h_fail : cfg_s.getEnv.hasFailure = true := by
        simpa [Lang.imperativeBlock] using h_cfg_fail
      obtain ⟨d, hd_run, hd_fail⟩ :=
        nondetElim_to_fail_compositional ss ρ₀ ρ₀ cfg_s
          rfl rfl (StoreAgreement.refl _) hwf_full h_gens h_gens h_inits
          h_writes h_unique h_reach h_fail
      exact ⟨d, by simpa [Lang.imperativeBlock] using hd_fail,
        by simpa [Lang.imperativeBlock] using hd_run⟩
  · have hinits := Block.nondetElim_initsUndefinedAndInhabited ss ρ₀
      h_inits h_gens h_src_inhab
    exact ⟨hwf_full, hstoreWF, hinits.1, h_gens, hinits.2⟩

end NondetElimOverapprox

end Imperative

end -- public section
