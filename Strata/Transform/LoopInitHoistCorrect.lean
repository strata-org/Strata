/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CmdSemantics
public import Strata.Transform.LoopInitHoist
public import Strata.Transform.DetToKleeneCorrect
public import Strata.Transform.NondetElimCorrect
public import Strata.Transform.StructuredToUnstructuredCorrect
public import Strata.Transform.CoreTransformProps

import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.Cmd
import all Strata.DL.Util.ListUtils
import all Strata.DL.Util.List
import all Strata.Transform.LoopInitHoist
import all Strata.Transform.DetToKleeneCorrect
import all Strata.Transform.NondetElimCorrect
import all Strata.Transform.StructuredToUnstructuredCorrect

/-! # Loop-init hoist: infrastructure + correctness

The complete correctness development for the loop-init hoist pass
(`Block.hoistLoopPrefixInits`), the MIDDLE stage of the structured-to-unstructured
pipeline (`nondetElim` → **`hoistLoopPrefixInits`** → `stmtsToCFG`).  Organised in
three parts:

1. the `.loop`-arm driver library (namespace `LoopInitHoistLoopDriver`), which turns
   a body simulation into the loop forward-simulation the capstone consumes;
2. the pass-output facts (namespace `LoopInitHoistProducerProps`), the
   `hoistP_*`/`liftP_*` shape-preservation lemmas;
3. the capstone forward-simulation theorems `hoistLoopPrefixInits_preserves_sa`
   / `_exit_sa` / `_to_fail_sa`.

The whole-pipeline soundness capstone chains this stage's simulation with the
other two passes' up to the store-agreement output relation.  Generic,
transformation-agnostic store/run helpers live in `CoreTransformProps`. -/

public section

namespace Imperative

/-- Nil-decomposition of `Block.initVars` (definitional; complements the
`_cons`/`_block`/`_ite`/`_loop` structural equations). -/
@[simp] theorem Block.initVars_nil {P : PureExpr} :
    Block.initVars ([] : List (Stmt P (Cmd P))) = [] := by
  simp [Block.initVars]

/-! The `namesFreshInExprs`/`namesFreshInRhsExprs`/`exprsShapeFree` predicate
property lemmas (`_of_namesFreshInExprs`, `_subset`, `_append`, `_nil`,
`_cons_names`, `_of_forall_mem`, `_of_exprsShapeFree'`) are proved upstream in
`Strata.DL.Imperative.StmtProps`. -/

namespace LoopInitHoistLoopDriver

/-! ## Iteration build helper. -/

/-- Per-iteration construction for a determinised loop with no measure and no
invariants: given the guard true at `ρ_pre`, well-formed Bool evaluation, and a
body run reaching `.terminal ρ_body`, the loop steps from `ρ_pre` to the residual
`.loop` stmts at `ρ_body`, with the loop-locals projected back out via
`projectStore` and the factory restored to `ρ_pre.factory`. -/
private theorem buildLoopIterationDet {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P]
    [HasVarsPure P P.Expr]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {ρ_pre ρ_body : Env P}
    (h_guard : P.eval ρ_pre.factory ρ_pre.store g = .some HasBool.tt)
    (h_wfb : WellFormedSemanticEvalBool ρ_pre.factory)
    (h_body_run : StepStmtStar P (EvalCmd P) extendFactory
        (.stmts body ρ_pre) (.terminal ρ_body)) :
    StepStmtStar P (EvalCmd P) extendFactory
      (.stmt (.loop (.det g) none [] body md) ρ_pre)
      (.stmts [.loop (.det g) none [] body md]
        { ρ_body with store := projectStore ρ_pre.store ρ_body.store,
                      factory := ρ_pre.factory }) := by
  have h_enter : StepStmt P (EvalCmd P) extendFactory
      (.stmt (.loop (.det g) none [] body md) ρ_pre)
      (.seq (.block .none ρ_pre.store ρ_pre.factory
              (.stmts body ρ_pre))
            [.loop (.det g) none [] body md]) :=
    .step_loop_enter h_guard h_wfb
  have h_block_run : StepStmtStar P (EvalCmd P) extendFactory
      (.block .none ρ_pre.store ρ_pre.factory (.stmts body ρ_pre))
      (.terminal { ρ_body with store := projectStore ρ_pre.store ρ_body.store,
                               factory := ρ_pre.factory }) :=
    ReflTrans_Transitive _ _ _ _
      (block_inner_star P (EvalCmd P) extendFactory _ _ (none : Option String) ρ_pre.store
          ρ_pre.factory h_body_run)
      (.step _ _ _ .step_block_done (.refl _))
  have h_seq_run : StepStmtStar P (EvalCmd P) extendFactory
      (.seq (.block .none ρ_pre.store ρ_pre.factory (.stmts body ρ_pre))
            [.loop (.det g) none [] body md])
      (.stmts [.loop (.det g) none [] body md]
        { ρ_body with store := projectStore ρ_pre.store ρ_body.store,
                      factory := ρ_pre.factory }) :=
    ReflTrans_Transitive _ _ _ _
      (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_block_run)
      (.step _ _ _ .step_seq_done (.refl _))
  exact ReflTrans.step _ _ _ h_enter h_seq_run

/-! ## Exiting-trace decompositions for determinised loops.

These `*'`-suffixed `ReflTransT` exiting-trace decompositions invert a run that
reaches a labeled `.exiting` through a `.seq` / `.none`-block / `.stmts`-cons
context.  They live here (rather than being imported from the equivalence proof)
so this driver library sits strictly upstream of that proof, and are self-contained
against the iteration machinery in `DetToKleeneCorrect` and the store/relation
helpers. -/

/-- Fuel-indexed none-preservation for a determinised, invariant-free loop: if `x`
is undefined before the loop and the loop runs to `.terminal ρ_post`, then `x` is
still undefined at `ρ_post`.

Structure of the recursion (fuel `n` on the source run length):
* `step_loop_exit`: the loop exits with the store unchanged, so `ρ_post = ρ` and
  `x` stays `none`.
* `step_loop_enter`: the body of this iteration runs inside a `.block .none`; the
  `projectStore` at the block boundary re-caps `x` to `none` (it was `none` in the
  parent), so the invariant is re-established at the inner env and the recursion
  closes via `ih` on the residual loop. -/
public theorem loopDet_preserves_none_terminal_fuel {P : PureExpr} [HasFvar P] [HasFvars P]
    [HasBoolOps P] [HasVarsPure P P.Expr]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {x : P.Ident} :
    ∀ (n : Nat) {ρ ρ_post : Env P},
      ρ.store x = none →
      (h_run : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
        (.stmt (.loop (.det g) none [] body md) ρ) (.terminal ρ_post)) →
      h_run.len ≤ n →
      ρ_post.store x = none := by
  intro n
  induction n with
  | zero =>
    intro ρ ρ_post _ h_run hlen
    match h_run with
    | .step _ _ _ _ _ => simp [ReflTransT.len] at hlen
  | succ n ih =>
    intro ρ ρ_post h_none h_run hlen
    match h_run with
    | .step _ _ _ step hrest =>
      cases step with
      | step_loop_exit ht hwf =>
        have h_ρ_post_eq : ρ_post = ρ := by
          match hrest with
          | .refl _ => rfl
          | .step _ _ _ hd _ => exact nomatch hd
        subst h_ρ_post_eq
        exact h_none
      | step_loop_enter ht hwf =>
        -- Peel one iteration WITHOUT a no-exit hypothesis: the seq decomposes to a
        -- `.block .none` reaching `.terminal`, which forces an inner `.terminal`.
        obtain ⟨ρ_block, h_block_term, h_loop_stmts, _⟩ :=
          seqT_reaches_terminal hrest
        obtain ⟨ρ_inner, _, h_ρ_block_eq, _⟩ := blockT_none_reaches_terminal h_block_term
        subst h_ρ_block_eq
        obtain ⟨ρ_x, h_loop_T, h_nil, _⟩ :=
          stmtsT_cons_terminal h_loop_stmts
        have hρ_x_eq : ρ_x = ρ_post := by
          match h_nil with
          | .step _ _ _ .step_stmts_nil hr2 =>
            match hr2 with
            | .refl _ => rfl
            | .step _ _ _ h _ => exact nomatch h
        subst hρ_x_eq
        have h_none_inner :
            ({ ρ_inner with store := projectStore ρ.store ρ_inner.store,
                            factory := ρ.factory } : Env P).store x = none := by
          show projectStore ρ.store ρ_inner.store x = none
          exact projectStore_undef_at h_none
        exact ih h_none_inner h_loop_T (by simp only [ReflTransT.len] at hlen; omega)

/-- Prop-level corollary of `loopDet_preserves_none_terminal_fuel`. -/
public theorem loopDet_preserves_none_terminal {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps
    P] [HasVarsPure P P.Expr]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {x : P.Ident} {ρ ρ_post : Env P}
    (h_none : ρ.store x = none)
    (h_run : StepStmtStar P (EvalCmd P) extendFactory
      (.stmt (.loop (.det g) none [] body md) ρ) (.terminal ρ_post)) :
    ρ_post.store x = none :=
  loopDet_preserves_none_terminal_fuel (reflTrans_to_T h_run).len h_none
    (reflTrans_to_T h_run) (Nat.le_refl _)

/-! ## Same-name loop driver on `StoreAgreement`.

The same-name loop-init hoist reuses the source body-local name `y`: the prelude
runs `init y := *` once before the loop, and the body's `init y := e` becomes
`set y := e`.  No fresh name is generated and no rename is applied, so the source
and hoist guards/bodies share every name and the relation is plain
`StoreAgreement` (source-on-left).  `StoreAgreement` constrains only
source-*defined* slots, so it ignores the post-iteration divergence (where the
source body-local `y` is `none` but the hoist's prelude-defined `y` persists).

The per-iteration obligations close on `StoreAgreement` re-established across each
iteration's `projectStore` boundary by `StoreAgreement.of_projectStore_parents`,
with guard transport by `storeAgreement_pointwise_on_expr_vars`. -/

/-- The same-name `StoreAgreement` body simulation: a body run that TERMINATES is
matched by a terminating hoist run, and a body run that EXITS with label `l` is
matched by a hoist run that exits with the SAME label `l`, re-establishing
`StoreAgreement` at the body-exit stores together with `eval` / `hasFailure`
agreement and the target-definedness invariant `D` (the prelude-defined slots,
which the prelude keeps defined across iterations).  This is the same-name
`StoreAgreement` analogue of `BodySimSum`, and the slot the same-name driver
consumes. -/
public def BodySimSumSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    (D : List P.Ident) (bsrc bh : List (Stmt P (Cmd P))) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    ρ_h.factory = ρ_s.factory → ρ_h.hasFailure = ρ_s.hasFailure →
    StoreAgreement ρ_s.store ρ_h.store →
    WellFormedSemanticEvalBool ρ_s.factory → WellFormedSemanticEvalVal ρ_s.factory →
    WellFormedSemanticEvalMono ρ_s.factory → WellFormedSemanticEvalExprCongr ρ_s.factory →
    WellFormedSemanticEvalVar ρ_s.factory →
    (∀ y ∈ D, (ρ_h.store y).isSome = true) →
    -- TERMINAL clause:
    (∀ (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendFactory (.stmts bsrc ρ_s) (.terminal ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendFactory (.stmts bh ρ_h) (.terminal ρ_h') ∧
        StoreAgreement ρ_s'.store ρ_h'.store ∧
        ρ_h'.hasFailure = ρ_s'.hasFailure ∧ ρ_h'.factory = ρ_s'.factory ∧
        (∀ y ∈ D, (ρ_h'.store y).isSome = true))
    ∧
    -- EXITING clause:
    (∀ (l : String) (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendFactory (.stmts bsrc ρ_s) (.exiting l ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendFactory (.stmts bh ρ_h) (.exiting l ρ_h') ∧
        StoreAgreement ρ_s'.store ρ_h'.store ∧
        ρ_h'.hasFailure = ρ_s'.hasFailure ∧ ρ_h'.factory = ρ_s'.factory ∧
        (∀ y ∈ D, (ρ_h'.store y).isSome = true))

/-- A `.det`-rhs source `init y` step is simulated by a hoist `set y` step,
maintaining `StoreAgreement`.  The hoist `set` requires `y` already defined in the
target (`h_tgt_y_def`), supplied by the prelude.  Source pre: `y = none`; both
post-stores land `y ↦ v` for the SAME `v` (`e`'s reads are source-defined so the
values agree), and every other slot is unchanged on both sides — so
`StoreAgreement` is re-established with no rename. -/
public theorem initToSetStepSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    {extendFactory : ExtendFactory P}
    (y : P.Ident) (ty : P.Ty) (e : P.Expr) (md : MetaData P)
    (ρ_src ρ_src' ρ_tgt : Env P)
    (h_eval_eq : ρ_tgt.factory = ρ_src.factory)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (h_wf_def : WellFormedSemanticEvalMono ρ_src.factory)
    (h_tgt_y_def : (ρ_tgt.store y).isSome = true)
    (h_step : StepStmt P (EvalCmd P) extendFactory
        (.stmt (.cmd (.init y ty (.det e) md)) ρ_src) (.terminal ρ_src')) :
    ∃ ρ_tgt', StepStmt P (EvalCmd P) extendFactory
          (.stmt (.cmd (.set y (.det e) md)) ρ_tgt) (.terminal ρ_tgt')
        ∧ StoreAgreement ρ_src'.store ρ_tgt'.store
        ∧ ρ_tgt'.hasFailure = ρ_src'.hasFailure
        ∧ ρ_tgt'.factory = ρ_src'.factory
        ∧ (ρ_tgt'.store y).isSome = true
        ∧ (∀ z, y ≠ z → ρ_tgt'.store z = ρ_tgt.store z) := by
  cases h_step with
  | step_cmd h_eval =>
    rename_i σ' haf
    cases h_eval with
    | eval_init heval hinit hwfvar =>
      rename_i v
      have h_eval_tgt : P.eval ρ_tgt.factory ρ_tgt.store e = .some v := by
        rw [h_eval_eq]
        exact h_wf_def e v ρ_src.store ρ_tgt.store
          (storeAgreement_supplies_mono_premise ρ_src.store ρ_tgt.store h_agree) heval
      cases hinit with
      | init h_yn h_yv h_other =>
        obtain ⟨v', h_tgt_y_old⟩ : ∃ v', ρ_tgt.store y = some v' := by
          cases h : ρ_tgt.store y with
          | none => rw [h] at h_tgt_y_def; simp at h_tgt_y_def
          | some v' => exact ⟨v', rfl⟩
        let σ_tgt' : SemanticStore P := fun z => if z = y then some v else ρ_tgt.store z
        have h_tgt_y : σ_tgt' y = some v := by show (if y = y then _ else _) = _; simp
        have h_tgt_oth : ∀ z, y ≠ z → σ_tgt' z = ρ_tgt.store z := by
          intro z hyz; show (if z = y then _ else _) = _; rw [if_neg (fun h => hyz h.symm)]
        refine ⟨{ ρ_tgt with store := σ_tgt', hasFailure := ρ_tgt.hasFailure || false },
          .step_cmd (EvalCmd.eval_set h_eval_tgt
            (UpdateState.update h_tgt_y_old h_tgt_y h_tgt_oth)
            (h_eval_eq ▸ hwfvar)),
          ?_, ?_, ?_, ?_, ?_⟩
        · intro z h_def_z
          show σ' z = σ_tgt' z
          have h_z_some : (σ' z).isSome = true := h_def_z z (List.mem_singleton.mpr rfl)
          by_cases hzy : z = y
          · subst hzy; rw [h_yv, h_tgt_y]
          · rw [h_other z (fun h => hzy h.symm)]
            rw [h_other z (fun h => hzy h.symm)] at h_z_some
            rw [h_tgt_oth z (fun h => hzy h.symm)]
            exact h_agree z (fun w hw => by simpa [List.mem_singleton.mp hw] using h_z_some)
        · show (ρ_tgt.hasFailure || false) = (ρ_src.hasFailure || false); simp [h_fail_eq]
        · exact h_eval_eq
        · show (σ_tgt' y).isSome = true; rw [h_tgt_y]; rfl
        · exact h_tgt_oth

/-- The minimal same-name body simulation: source body `[.cmd (.init y ty e md)]`
simulated by hoist body `[.cmd (.set y e md)]`, in the `BodySimSumSA` body-sim
shape the driver consumes.  A single `.cmd` can only TERMINATE (never `.exit`s);
the per-step transport is `initToSetStepSA`. -/
public theorem samenameBodySimInitSet {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    {extendFactory : ExtendFactory P}
    (y : P.Ident) (ty : P.Ty) (e : P.Expr) (md : MetaData P) :
    BodySimSumSA (extendFactory := extendFactory) [y]
      [.cmd (.init y ty (.det e) md)] [.cmd (.set y (.det e) md)] := by
  intro ρb_src ρb_tgt h_eval_eq h_fail_eq h_agree _ _ h_wf_def h_congr _ h_dy
  have h_tgt_y_def : (ρb_tgt.store y).isSome = true := h_dy y (List.mem_singleton.mpr rfl)
  refine ⟨?_, ?_⟩
  · -- TERMINAL clause.
    intro ρb' h_run
    -- Peel `.stmts [cmd] →* .terminal`: stmts_cons → seq(cmd) terminal → seq_done → stmts_nil.
    match h_run with
    | .step _ _ _ .step_stmts_cons hrest =>
      obtain ⟨ρ_mid, h_cmd_T, h_after⟩ := seq_reaches_terminal P (EvalCmd P) extendFactory hrest
      have h_cmd_step : StepStmt P (EvalCmd P) extendFactory
          (.stmt (.cmd (.init y ty (.det e) md)) ρb_src) (.terminal ρ_mid) := by
        match h_cmd_T with
        | .step _ _ _ (.step_cmd hev) hr =>
          match hr with
          | .refl _ => exact .step_cmd hev
          | .step _ _ _ hd _ => exact nomatch hd
      have h_ρb'_eq : ρb' = ρ_mid := by
        match h_after with
        | .step _ _ _ .step_stmts_nil hr =>
          match hr with
          | .refl _ => rfl
          | .step _ _ _ hd _ => exact nomatch hd
      rw [h_ρb'_eq]
      obtain ⟨ρ_tgt', h_set_step, h_agree', h_fail', h_eval', h_ydef', _⟩ :=
        initToSetStepSA y ty e md ρb_src ρ_mid ρb_tgt
          h_eval_eq h_fail_eq h_agree h_wf_def h_tgt_y_def h_cmd_step
      refine ⟨ρ_tgt', ?_, h_agree', h_fail', h_eval', ?_⟩
      · refine .step _ _ _ .step_stmts_cons ?_
        refine .step _ _ _ (.step_seq_inner h_set_step) ?_
        exact .step _ _ _ .step_seq_done (.step _ _ _ .step_stmts_nil (.refl _))
      · intro z hz; rw [List.mem_singleton.mp hz]; exact h_ydef'
  · -- EXITING clause: a single `.cmd` cannot reach `.exiting`.
    intro l ρb' h_run
    exfalso
    match h_run with
    | .step _ _ _ .step_stmts_cons hrest =>
      rcases seq_reaches_exiting P (EvalCmd P) extendFactory hrest with
        h_cmd_exit | ⟨ρ₁, _, h_nil_exit⟩
      · match h_cmd_exit with
        | .step _ _ _ (.step_cmd _) hr =>
          match hr with
          | .step _ _ _ hd _ => exact nomatch hd
      · match h_nil_exit with
        | .step _ _ _ .step_stmts_nil hr =>
          match hr with
          | .step _ _ _ hd _ => exact nomatch hd

/-- **Same-name `StoreAgreement` TERMINAL-target fuel recursion.**

The terminal analogue of `loopDet_lift_2g_TE_fuel`, re-threaded on `StoreAgreement`
+ a definedness invariant `D` (the prelude-defined slots): consumes a `BodySimSumSA`
body sim (terminal clause used per-completed-iteration) and a source loop run
reaching `.terminal ρ_post`.  Each iteration peels through the same driver-local
inversions (`seqT_reaches_terminal`, `blockT_none_reaches_terminal`,
`stmtsT_cons_terminal`); the iteration boundary re-establishes `StoreAgreement` via
`StoreAgreement.of_projectStore_parents` and keeps `D` defined because parent-defined
keys are kept under `projectStore`. -/
private theorem samenameLoopDetSA_TE_fuel {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {D : List P.Ident}
    (body_sim : BodySimSumSA (extendFactory := extendFactory) D body_src body_h)
    (h_src_body_nofd : Block.noFuncDecl body_src = true) :
    ∀ (n : Nat) {ρ_src ρ_hoist ρ_post : Env P},
      StoreAgreement ρ_src.store ρ_hoist.store →
      ρ_hoist.factory = ρ_src.factory → ρ_hoist.hasFailure = ρ_src.hasFailure →
      WellFormedSemanticEvalBool ρ_src.factory → WellFormedSemanticEvalVal ρ_src.factory →
      WellFormedSemanticEvalMono ρ_src.factory → WellFormedSemanticEvalExprCongr ρ_src.factory →
      WellFormedSemanticEvalVar ρ_src.factory →
      (∀ y ∈ D, (ρ_hoist.store y).isSome = true) →
      (h_run : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
        (.stmt (.loop (.det g) none [] body_src md_s) ρ_src) (.terminal ρ_post)) →
      h_run.len ≤ n →
      ∃ ρ_post_h : Env P,
        StepStmtStar P (EvalCmd P) extendFactory
          (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist) (.terminal ρ_post_h) ∧
        StoreAgreement ρ_post.store ρ_post_h.store ∧
        ρ_post_h.hasFailure = ρ_post.hasFailure ∧ ρ_post_h.factory = ρ_post.factory ∧
        (∀ y ∈ D, (ρ_post_h.store y).isSome = true) := by
  intro n
  induction n with
  | zero =>
    intro ρ_src ρ_hoist ρ_post _ _ _ _ _ _ _ _ _ h_run hlen
    match h_run with
    | .step _ _ _ _ _ => simp [ReflTransT.len] at hlen
  | succ n ih =>
    intro ρ_src ρ_hoist ρ_post h_agree h_eval h_hf hwfb hwfv hwf_def hwf_congr hwf_var
      h_def h_run hlen
    match h_run with
    | .step _ _ _ step hrest =>
      cases step with
      | step_loop_exit ht hwf =>
        have h_ρ_post_eq : ρ_post = ρ_src := by
          match hrest with
          | .refl _ => rfl
          | .step _ _ _ hd _ => exact nomatch hd
        subst ρ_post
        have h_cond_h : P.eval ρ_hoist.factory ρ_hoist.store g = .some HasBool.ff := by
          rw [h_eval]
          exact hwf_def g HasBool.ff ρ_src.store ρ_hoist.store
            (storeAgreement_supplies_mono_premise ρ_src.store ρ_hoist.store h_agree) ht
        refine ⟨ρ_hoist, ?_, ?_, ?_, ?_, ?_⟩
        · exact .step _ _ _
            (.step_loop_exit h_cond_h (h_eval ▸ hwfb))
            (.refl _)
        · exact h_agree
        · exact h_hf
        · exact h_eval
        · intro y hy; exact h_def y hy
      | step_loop_enter ht hwf =>
        have h_cond_h : P.eval ρ_hoist.factory ρ_hoist.store g = .some HasBool.tt := by
          rw [h_eval]
          exact hwf_def g HasBool.tt ρ_src.store ρ_hoist.store
            (storeAgreement_supplies_mono_premise ρ_src.store ρ_hoist.store h_agree) ht
        -- Peel one iteration: seq decomposes to a `.none`-block reaching `.terminal`.
        obtain ⟨ρ_block, h_block_term, h_loop_stmts, hlen_seq⟩ :=
          seqT_reaches_terminal hrest
        obtain ⟨ρ_inner, h_body_src_T, h_ρ_block_eq, hlen_block⟩ :=
          blockT_none_reaches_terminal h_block_term
        subst h_ρ_block_eq
        obtain ⟨ρ_x, h_loop_T, h_nil, hlen_cons⟩ :=
          stmtsT_cons_terminal h_loop_stmts
        have hρ_x_eq : ρ_x = ρ_post := by
          match h_nil with
          | .step _ _ _ .step_stmts_nil hr2 =>
            match hr2 with
            | .refl _ => rfl
            | .step _ _ _ h _ => exact nomatch h
        subst hρ_x_eq
        let ρ_src_body : Env P := ρ_src
        let ρ_h_body : Env P := ρ_hoist
        have h_agree_body : StoreAgreement ρ_src_body.store ρ_h_body.store := h_agree
        have h_eval_body : ρ_h_body.factory = ρ_src_body.factory := h_eval
        have h_hf_body : ρ_h_body.hasFailure = ρ_src_body.hasFailure := h_hf
        have h_def_body : ∀ y ∈ D, (ρ_h_body.store y).isSome = true := h_def
        obtain ⟨ρ_h_inner, h_body_h_run, h_agree_inner, h_hf_inner, h_eval_inner, h_def_inner⟩ :=
          (body_sim ρ_src_body ρ_h_body h_eval_body h_hf_body h_agree_body
            hwfb hwfv hwf_def hwf_congr hwf_var h_def_body).1
            ρ_inner (reflTransT_to_prop h_body_src_T)
        -- One hoist iteration.
        have h_hoist_iter : StepStmtStar P (EvalCmd P) extendFactory
            (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist)
            (.stmts [.loop (.det g) none [] body_h md_h]
              { ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store,
                               factory := ρ_hoist.factory }) := by
          have hb : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts body_h ρ_h_body) (.terminal ρ_h_inner) := h_body_h_run
          have := buildLoopIterationDet (g := g) (body := body_h) (md := md_h)
            (ρ_pre := ρ_h_body) (ρ_body := ρ_h_inner) ?_ ?_ hb
          · simpa [ρ_h_body] using this
          · show P.eval ρ_h_body.factory ρ_h_body.store g = .some HasBool.tt
            show P.eval ρ_hoist.factory ρ_hoist.store g = .some HasBool.tt; exact h_cond_h
          · show WellFormedSemanticEvalBool ρ_h_body.factory
            show WellFormedSemanticEvalBool ρ_hoist.factory; rw [h_eval]; exact hwfb
        -- Next-iteration projected envs.
        let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store,
                                                 factory := ρ_src.factory }
        let ρ_tgt_next : Env P :=
          { ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store,
                           factory := ρ_hoist.factory }
        have h_eval_inner_src : ρ_inner.factory = ρ_src.factory :=
          block_noFuncDecl_preserves_factory P (EvalCmd P) extendFactory body_src ρ_src ρ_inner
            h_src_body_nofd
            (by have := reflTransT_to_prop h_body_src_T;
                simpa [ρ_src_body, Bool.or_false] using this)
        have h_agree_next : StoreAgreement ρ_src_next.store ρ_tgt_next.store :=
          StoreAgreement.of_projectStore_parents h_agree h_agree_inner
        have h_eval_next : ρ_tgt_next.factory = ρ_src_next.factory := by
          show ρ_hoist.factory = ρ_src.factory; exact h_eval
        have h_hf_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
          show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf_inner
        have h_eval_src_next : ρ_src_next.factory = ρ_src.factory := rfl
        have h_def_next : ∀ y ∈ D, (ρ_tgt_next.store y).isSome = true := by
          intro y hy
          show (projectStore ρ_hoist.store ρ_h_inner.store y).isSome = true
          show ((if (ρ_hoist.store y).isSome then ρ_h_inner.store y else none)).isSome = true
          rw [if_pos (h_def y hy)]; exact h_def_inner y hy
        obtain ⟨ρ_post_h, h_post_h_run, h_agree_post, h_hf_post, h_eval_post, h_def_post⟩ :=
          ih (ρ_src := ρ_src_next) (ρ_hoist := ρ_tgt_next)
            h_agree_next h_eval_next h_hf_next
            (by rw [h_eval_src_next]; exact hwfb) (by rw [h_eval_src_next]; exact hwfv)
            (by rw [h_eval_src_next]; exact hwf_def) (by rw [h_eval_src_next]; exact hwf_congr)
            (by rw [h_eval_src_next]; exact hwf_var)
            h_def_next h_loop_T (by simp only [ReflTransT.len] at hlen; omega)
        refine ⟨ρ_post_h, ?_, h_agree_post, h_hf_post, h_eval_post, h_def_post⟩
        refine ReflTrans_Transitive _ _ _ _ h_hoist_iter ?_
        refine ReflTrans.step _ _ _ .step_stmts_cons ?_
        refine ReflTrans_Transitive _ _ _ _
          (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_post_h_run) ?_
        exact ReflTrans.step _ _ _ .step_seq_done
          (ReflTrans.step _ _ _ .step_stmts_nil (.refl _))

/-- **Same-name `StoreAgreement` EXITING-target fuel recursion.**

The exiting analogue of `loopDet_lift_2g_E_fuel`, re-threaded on `StoreAgreement` +
`D`.  A source loop run reaching `.exiting label ρ_post` is matched by a hoist loop
run reaching `.exiting label ρ_post_h`.  Either this iteration's body exits (feed the
exiting clause, build the early `.none`-block-mismatch exit) or it terminates and the
recursive loop exits (feed the terminal clause, recurse via `ih`). -/
private theorem samenameLoopDetSA_E_fuel {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {D : List P.Ident}
    (body_sim : BodySimSumSA (extendFactory := extendFactory) D body_src body_h)
    (h_src_body_nofd : Block.noFuncDecl body_src = true) :
    ∀ (n : Nat) {ρ_src ρ_hoist ρ_post : Env P} {label : String},
      StoreAgreement ρ_src.store ρ_hoist.store →
      ρ_hoist.factory = ρ_src.factory → ρ_hoist.hasFailure = ρ_src.hasFailure →
      WellFormedSemanticEvalBool ρ_src.factory → WellFormedSemanticEvalVal ρ_src.factory →
      WellFormedSemanticEvalMono ρ_src.factory → WellFormedSemanticEvalExprCongr ρ_src.factory →
      WellFormedSemanticEvalVar ρ_src.factory →
      (∀ y ∈ D, (ρ_hoist.store y).isSome = true) →
      (h_run : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
        (.stmt (.loop (.det g) none [] body_src md_s) ρ_src) (.exiting label ρ_post)) →
      h_run.len ≤ n →
      ∃ ρ_post_h : Env P,
        StepStmtStar P (EvalCmd P) extendFactory
          (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist) (.exiting label ρ_post_h) ∧
        StoreAgreement ρ_post.store ρ_post_h.store ∧
        ρ_post_h.hasFailure = ρ_post.hasFailure ∧ ρ_post_h.factory = ρ_post.factory ∧
        (∀ y ∈ D, (ρ_post_h.store y).isSome = true) := by
  intro n
  induction n with
  | zero =>
    intro ρ_src ρ_hoist ρ_post label _ _ _ _ _ _ _ _ _ h_run hlen
    match h_run with
    | .step _ _ _ _ _ => simp [ReflTransT.len] at hlen
  | succ n ih =>
    intro ρ_src ρ_hoist ρ_post label h_agree h_eval h_hf hwfb hwfv hwf_def hwf_congr hwf_var
      h_def h_run hlen
    match h_run with
    | .step _ _ _ step hrest =>
      cases step with
      | step_loop_exit ht hwf =>
        match hrest with
        | .step _ _ _ hd _ => exact nomatch hd
      | step_loop_enter ht hwf =>
        have h_cond_h : P.eval ρ_hoist.factory ρ_hoist.store g = .some HasBool.tt := by
          rw [h_eval]
          exact hwf_def g HasBool.tt ρ_src.store ρ_hoist.store
            (storeAgreement_supplies_mono_premise ρ_src.store ρ_hoist.store h_agree) ht
        let ρ_src_body : Env P := ρ_src
        let ρ_h_body : Env P := ρ_hoist
        have h_agree_body : StoreAgreement ρ_src_body.store ρ_h_body.store := h_agree
        have h_eval_body : ρ_h_body.factory = ρ_src_body.factory := h_eval
        have h_hf_body : ρ_h_body.hasFailure = ρ_src_body.hasFailure := h_hf
        have h_def_body : ∀ y ∈ D, (ρ_h_body.store y).isSome = true := h_def
        have h_wfb_h : WellFormedSemanticEvalBool ρ_hoist.factory := by rw [h_eval]; exact hwfb
        rcases seqT_reaches_exiting hrest with ⟨h_block_exit, hl⟩ | ⟨ρ₁, h_block_term, h_loop_stmts,
            hl⟩
        · -- inl: this iteration's body exits with `label`.
          obtain ⟨ρ_inner, h_body_exit_T, h_ρpost_eq, hl2⟩ := blockT_none_reaches_exiting
              h_block_exit
          obtain ⟨ρ_h_inner, h_body_h_exit, h_agree_inner, h_hf_inner, h_eval_inner, h_def_inner⟩ :=
            (body_sim ρ_src_body ρ_h_body h_eval_body h_hf_body h_agree_body
              hwfb hwfv hwf_def hwf_congr hwf_var h_def_body).2
              label ρ_inner (reflTransT_to_prop h_body_exit_T)
          refine ⟨{ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store,
                                   factory := ρ_hoist.factory }, ?_, ?_, ?_, ?_, ?_⟩
          · refine ReflTrans.step _ _ _
              (.step_loop_enter
                h_cond_h h_wfb_h) ?_
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _
                (block_inner_star P (EvalCmd P) extendFactory _ _ (none : Option String)
                    ρ_hoist.store ρ_hoist.factory
                  (show StepStmtStar P (EvalCmd P) extendFactory
                      (.stmts body_h ρ_hoist)
                      (.exiting label ρ_h_inner) from h_body_h_exit))) ?_
            refine ReflTrans.step _ _ _ (.step_seq_inner (.step_block_exit_mismatch ?_)) ?_
            · exact (by simp)
            · exact ReflTrans.step _ _ _ .step_seq_exit (.refl _)
          · subst h_ρpost_eq; exact StoreAgreement.of_projectStore_parents h_agree h_agree_inner
          · subst h_ρpost_eq; show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf_inner
          · subst h_ρpost_eq; show ρ_hoist.factory = ρ_src.factory; exact h_eval
          · intro y hy
            show (projectStore ρ_hoist.store ρ_h_inner.store y).isSome = true
            show ((if (ρ_hoist.store y).isSome then ρ_h_inner.store y else none)).isSome = true
            rw [if_pos (h_def y hy)]; exact h_def_inner y hy
        · -- inr: this iteration's body terminates; recurse on the inner loop.
          obtain ⟨ρ_inner, h_body_term_T, h_ρ_block_eq, hl_blk⟩ := blockT_none_reaches_terminal
              h_block_term
          subst h_ρ_block_eq
          obtain ⟨ρ_h_inner, h_body_h_run, h_agree_inner, h_hf_inner, h_eval_inner, h_def_inner⟩ :=
            (body_sim ρ_src_body ρ_h_body h_eval_body h_hf_body h_agree_body
              hwfb hwfv hwf_def hwf_congr hwf_var h_def_body).1
              ρ_inner (reflTransT_to_prop h_body_term_T)
          have h_hoist_iter : StepStmtStar P (EvalCmd P) extendFactory
              (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist)
              (.stmts [.loop (.det g) none [] body_h md_h]
                { ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store,
                                 factory := ρ_hoist.factory }) := by
            have hb : StepStmtStar P (EvalCmd P) extendFactory
                (.stmts body_h ρ_h_body) (.terminal ρ_h_inner) := h_body_h_run
            have := buildLoopIterationDet (g := g) (body := body_h) (md := md_h)
              (ρ_pre := ρ_h_body) (ρ_body := ρ_h_inner) ?_ ?_ hb
            · simpa [ρ_h_body] using this
            · show P.eval ρ_h_body.factory ρ_h_body.store g = .some HasBool.tt
              show P.eval ρ_hoist.factory ρ_hoist.store g = .some HasBool.tt; exact h_cond_h
            · show WellFormedSemanticEvalBool ρ_h_body.factory
              show WellFormedSemanticEvalBool ρ_hoist.factory; exact h_wfb_h
          let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store,
                                                   factory := ρ_src.factory }
          let ρ_tgt_next : Env P :=
            { ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store,
                             factory := ρ_hoist.factory }
          have h_eval_inner_src : ρ_inner.factory = ρ_src.factory :=
            block_noFuncDecl_preserves_factory P (EvalCmd P) extendFactory body_src ρ_src ρ_inner
              h_src_body_nofd
              (by have := reflTransT_to_prop h_body_term_T;
                  simpa [ρ_src_body, Bool.or_false] using this)
          have h_agree_next : StoreAgreement ρ_src_next.store ρ_tgt_next.store :=
            StoreAgreement.of_projectStore_parents h_agree h_agree_inner
          have h_eval_next : ρ_tgt_next.factory = ρ_src_next.factory := by
            show ρ_hoist.factory = ρ_src.factory; exact h_eval
          have h_hf_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
            show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf_inner
          have h_eval_src_next : ρ_src_next.factory = ρ_src.factory := rfl
          have h_def_next : ∀ y ∈ D, (ρ_tgt_next.store y).isSome = true := by
            intro y hy
            show (projectStore ρ_hoist.store ρ_h_inner.store y).isSome = true
            show ((if (ρ_hoist.store y).isSome then ρ_h_inner.store y else none)).isSome = true
            rw [if_pos (h_def y hy)]; exact h_def_inner y hy
          rcases stmtsT_cons_exiting h_loop_stmts with ⟨h_inner_loop_T, _⟩ | ⟨ρ₂, _, h_nil, _⟩
          · obtain ⟨ρ_post_h, h_post_h_run, h_agree_post, h_hf_post, h_eval_post, h_def_post⟩ :=
              ih (ρ_src := ρ_src_next) (ρ_hoist := ρ_tgt_next) (ρ_post := ρ_post) (label := label)
                h_agree_next h_eval_next h_hf_next
                (by rw [h_eval_src_next]; exact hwfb) (by rw [h_eval_src_next]; exact hwfv)
                (by rw [h_eval_src_next]; exact hwf_def) (by rw [h_eval_src_next]; exact hwf_congr)
                (by rw [h_eval_src_next]; exact hwf_var)
                h_def_next h_inner_loop_T (by simp only [ReflTransT.len] at hlen; omega)
            refine ⟨ρ_post_h, ?_, h_agree_post, h_hf_post, h_eval_post, h_def_post⟩
            refine ReflTrans_Transitive _ _ _ _ h_hoist_iter ?_
            refine ReflTrans.step _ _ _ .step_stmts_cons ?_
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_post_h_run) ?_
            exact ReflTrans.step _ _ _ .step_seq_exit (.refl _)
          · match h_nil with
            | .step _ _ _ .step_stmts_nil hr2 =>
              match hr2 with
              | .step _ _ _ hd _ => exact nomatch hd

/-- Prop-level wrapper of `samenameLoopDetSA_TE_fuel`: the same-name `StoreAgreement`
TERMINAL-target driver. -/
public theorem samenameLoopDetSA_TE {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {D : List P.Ident}
    (body_sim : BodySimSumSA (extendFactory := extendFactory) D body_src body_h)
    (h_src_body_nofd : Block.noFuncDecl body_src = true)
    {ρ_src ρ_hoist ρ_post : Env P}
    (h_agree : StoreAgreement ρ_src.store ρ_hoist.store)
    (h_eval : ρ_hoist.factory = ρ_src.factory) (h_hf : ρ_hoist.hasFailure = ρ_src.hasFailure)
    (hwfb : WellFormedSemanticEvalBool ρ_src.factory) (hwfv : WellFormedSemanticEvalVal
        ρ_src.factory)
    (hwf_def : WellFormedSemanticEvalMono ρ_src.factory)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ_src.factory)
    (hwf_var : WellFormedSemanticEvalVar ρ_src.factory)
    (h_def : ∀ y ∈ D, (ρ_hoist.store y).isSome = true)
    (h_run : StepStmtStar P (EvalCmd P) extendFactory
        (.stmt (.loop (.det g) none [] body_src md_s) ρ_src) (.terminal ρ_post)) :
    ∃ ρ_post_h : Env P,
      StepStmtStar P (EvalCmd P) extendFactory
        (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist) (.terminal ρ_post_h) ∧
      StoreAgreement ρ_post.store ρ_post_h.store ∧
      ρ_post_h.hasFailure = ρ_post.hasFailure ∧ ρ_post_h.factory = ρ_post.factory ∧
      (∀ y ∈ D, (ρ_post_h.store y).isSome = true) :=
  samenameLoopDetSA_TE_fuel body_sim h_src_body_nofd
    (reflTrans_to_T h_run).len h_agree h_eval h_hf hwfb hwfv hwf_def hwf_congr hwf_var h_def
    (reflTrans_to_T h_run) (Nat.le_refl _)

/-- Prop-level wrapper of `samenameLoopDetSA_E_fuel`: the same-name `StoreAgreement`
EXITING-target driver. -/
public theorem samenameLoopDetSA_E {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {D : List P.Ident}
    (body_sim : BodySimSumSA (extendFactory := extendFactory) D body_src body_h)
    (h_src_body_nofd : Block.noFuncDecl body_src = true)
    {ρ_src ρ_hoist ρ_post : Env P} {label : String}
    (h_agree : StoreAgreement ρ_src.store ρ_hoist.store)
    (h_eval : ρ_hoist.factory = ρ_src.factory) (h_hf : ρ_hoist.hasFailure = ρ_src.hasFailure)
    (hwfb : WellFormedSemanticEvalBool ρ_src.factory) (hwfv : WellFormedSemanticEvalVal
        ρ_src.factory)
    (hwf_def : WellFormedSemanticEvalMono ρ_src.factory)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ_src.factory)
    (hwf_var : WellFormedSemanticEvalVar ρ_src.factory)
    (h_def : ∀ y ∈ D, (ρ_hoist.store y).isSome = true)
    (h_run : StepStmtStar P (EvalCmd P) extendFactory
        (.stmt (.loop (.det g) none [] body_src md_s) ρ_src) (.exiting label ρ_post)) :
    ∃ ρ_post_h : Env P,
      StepStmtStar P (EvalCmd P) extendFactory
        (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist) (.exiting label ρ_post_h) ∧
      StoreAgreement ρ_post.store ρ_post_h.store ∧
      ρ_post_h.hasFailure = ρ_post.hasFailure ∧ ρ_post_h.factory = ρ_post.factory ∧
      (∀ y ∈ D, (ρ_post_h.store y).isSome = true) :=
  samenameLoopDetSA_E_fuel body_sim h_src_body_nofd
    (reflTrans_to_T h_run).len h_agree h_eval h_hf hwfb hwfv hwf_def hwf_congr hwf_var h_def
    (reflTrans_to_T h_run) (Nat.le_refl _)

/-! ## Dual-undefinedness `StoreAgreement` loop driver (NO prelude).

The same-name top-level hoist recursively hoists a loop's body BEFORE lifting its
prefix inits, so the source loop body `body_src` and the recursively-hoisted body
`body_h` differ in their nested loops (each nested loop's inits move to a prelude
inside `body_h`).  Relating `.loop … body_src` to `.loop … body_h` cannot keep a
set of names DEFINED across iterations (the post-order recursion has not yet lifted
the outer inits): both bodies run their own inits per iteration and pop them at
iteration end.  The right invariant is therefore DUAL-UNDEFINEDNESS of the names
`U` at every iteration entry on BOTH sides, re-established after each iteration's
`projectStore` by `projectStore_undef_at`.

`BodyDualUndefSA U body_src body_h` is the body-sim slot this driver consumes: a
source body run from a store where `U` is source-AND-target-undefined is matched by
a hoist body run preserving `StoreAgreement` / `eval` / `hasFailure`.  No
definedness invariant is reported (the outer iteration restores undefinedness from
the parent store, not from the body output). -/
public def BodyDualUndefSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    (U : List P.Ident) (bsrc bh : List (Stmt P (Cmd P))) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    ρ_h.factory = ρ_s.factory → ρ_h.hasFailure = ρ_s.hasFailure →
    StoreAgreement ρ_s.store ρ_h.store →
    WellFormedSemanticEvalBool ρ_s.factory → WellFormedSemanticEvalVal ρ_s.factory →
    WellFormedSemanticEvalMono ρ_s.factory → WellFormedSemanticEvalExprCongr ρ_s.factory →
    WellFormedSemanticEvalVar ρ_s.factory →
    (∀ y ∈ U, ρ_s.store y = none) →
    (∀ y ∈ U, ρ_h.store y = none) →
    (∀ (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendFactory (.stmts bsrc ρ_s) (.terminal ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendFactory (.stmts bh ρ_h) (.terminal ρ_h') ∧
        StoreAgreement ρ_s'.store ρ_h'.store ∧
        ρ_h'.hasFailure = ρ_s'.hasFailure ∧ ρ_h'.factory = ρ_s'.factory)
    ∧
    (∀ (l : String) (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendFactory (.stmts bsrc ρ_s) (.exiting l ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendFactory (.stmts bh ρ_h) (.exiting l ρ_h') ∧
        StoreAgreement ρ_s'.store ρ_h'.store ∧
        ρ_h'.hasFailure = ρ_s'.hasFailure ∧ ρ_h'.factory = ρ_s'.factory)

/-- **Dual-undef `StoreAgreement` TERMINAL-target fuel recursion.**

The dual-undefinedness analogue of `samenameLoopDetSA_TE_fuel`: instead of keeping
`D` defined, it keeps `U` UNDEFINED on both sides at every iteration entry,
re-established after each iteration's `projectStore` by `projectStore_undef_at`. -/
private theorem dualUndefLoopDetSA_TE_fuel {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {U : List P.Ident}
    (body_sim : BodyDualUndefSA (extendFactory := extendFactory) U body_src body_h)
    (h_src_body_nofd : Block.noFuncDecl body_src = true) :
    ∀ (n : Nat) {ρ_src ρ_hoist ρ_post : Env P},
      StoreAgreement ρ_src.store ρ_hoist.store →
      ρ_hoist.factory = ρ_src.factory → ρ_hoist.hasFailure = ρ_src.hasFailure →
      WellFormedSemanticEvalBool ρ_src.factory → WellFormedSemanticEvalVal ρ_src.factory →
      WellFormedSemanticEvalMono ρ_src.factory → WellFormedSemanticEvalExprCongr ρ_src.factory →
      WellFormedSemanticEvalVar ρ_src.factory →
      (∀ y ∈ U, ρ_src.store y = none) →
      (∀ y ∈ U, ρ_hoist.store y = none) →
      (h_run : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
        (.stmt (.loop (.det g) none [] body_src md_s) ρ_src) (.terminal ρ_post)) →
      h_run.len ≤ n →
      ∃ ρ_post_h : Env P,
        StepStmtStar P (EvalCmd P) extendFactory
          (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist) (.terminal ρ_post_h) ∧
        StoreAgreement ρ_post.store ρ_post_h.store ∧
        ρ_post_h.hasFailure = ρ_post.hasFailure ∧ ρ_post_h.factory = ρ_post.factory ∧
        (∀ y ∈ U, ρ_post.store y = none) ∧ (∀ y ∈ U, ρ_post_h.store y = none) := by
  intro n
  induction n with
  | zero =>
    intro ρ_src ρ_hoist ρ_post _ _ _ _ _ _ _ _ _ _ h_run hlen
    match h_run with
    | .step _ _ _ _ _ => simp [ReflTransT.len] at hlen
  | succ n ih =>
    intro ρ_src ρ_hoist ρ_post h_agree h_eval h_hf hwfb hwfv hwf_def hwf_congr hwf_var
      h_src_none h_tgt_none h_run hlen
    match h_run with
    | .step _ _ _ step hrest =>
      cases step with
      | step_loop_exit ht hwf =>
        have h_ρ_post_eq : ρ_post = ρ_src := by
          match hrest with
          | .refl _ => rfl
          | .step _ _ _ hd _ => exact nomatch hd
        subst ρ_post
        have h_cond_h : P.eval ρ_hoist.factory ρ_hoist.store g = .some HasBool.ff := by
          rw [h_eval]
          exact hwf_def g HasBool.ff ρ_src.store ρ_hoist.store
            (storeAgreement_supplies_mono_premise ρ_src.store ρ_hoist.store h_agree) ht
        refine ⟨ρ_hoist, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact .step _ _ _
            (.step_loop_exit h_cond_h (h_eval ▸ hwfb))
            (.refl _)
        · exact h_agree
        · exact h_hf
        · exact h_eval
        · intro y hy; exact h_src_none y hy
        · intro y hy; exact h_tgt_none y hy
      | step_loop_enter ht hwf =>
        have h_cond_h : P.eval ρ_hoist.factory ρ_hoist.store g = .some HasBool.tt := by
          rw [h_eval]
          exact hwf_def g HasBool.tt ρ_src.store ρ_hoist.store
            (storeAgreement_supplies_mono_premise ρ_src.store ρ_hoist.store h_agree) ht
        obtain ⟨ρ_block, h_block_term, h_loop_stmts, hlen_seq⟩ :=
          seqT_reaches_terminal hrest
        obtain ⟨ρ_inner, h_body_src_T, h_ρ_block_eq, hlen_block⟩ :=
          blockT_none_reaches_terminal h_block_term
        subst h_ρ_block_eq
        obtain ⟨ρ_x, h_loop_T, h_nil, hlen_cons⟩ :=
          stmtsT_cons_terminal h_loop_stmts
        have hρ_x_eq : ρ_x = ρ_post := by
          match h_nil with
          | .step _ _ _ .step_stmts_nil hr2 =>
            match hr2 with
            | .refl _ => rfl
            | .step _ _ _ h _ => exact nomatch h
        subst hρ_x_eq
        let ρ_src_body : Env P := ρ_src
        let ρ_h_body : Env P := ρ_hoist
        have h_agree_body : StoreAgreement ρ_src_body.store ρ_h_body.store := h_agree
        have h_eval_body : ρ_h_body.factory = ρ_src_body.factory := h_eval
        have h_hf_body : ρ_h_body.hasFailure = ρ_src_body.hasFailure := h_hf
        have h_src_none_body : ∀ y ∈ U, ρ_src_body.store y = none := h_src_none
        have h_tgt_none_body : ∀ y ∈ U, ρ_h_body.store y = none := h_tgt_none
        obtain ⟨ρ_h_inner, h_body_h_run, h_agree_inner, h_hf_inner, h_eval_inner⟩ :=
          (body_sim ρ_src_body ρ_h_body h_eval_body h_hf_body h_agree_body
            hwfb hwfv hwf_def hwf_congr hwf_var h_src_none_body h_tgt_none_body).1
            ρ_inner (reflTransT_to_prop h_body_src_T)
        have h_hoist_iter : StepStmtStar P (EvalCmd P) extendFactory
            (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist)
            (.stmts [.loop (.det g) none [] body_h md_h]
              { ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store,
                               factory := ρ_hoist.factory }) := by
          have hb : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts body_h ρ_h_body) (.terminal ρ_h_inner) := h_body_h_run
          have := buildLoopIterationDet (g := g) (body := body_h) (md := md_h)
            (ρ_pre := ρ_h_body) (ρ_body := ρ_h_inner) ?_ ?_ hb
          · simpa [ρ_h_body] using this
          · show P.eval ρ_h_body.factory ρ_h_body.store g = .some HasBool.tt
            show P.eval ρ_hoist.factory ρ_hoist.store g = .some HasBool.tt; exact h_cond_h
          · show WellFormedSemanticEvalBool ρ_h_body.factory
            show WellFormedSemanticEvalBool ρ_hoist.factory; rw [h_eval]; exact hwfb
        let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store,
                                                 factory := ρ_src.factory }
        let ρ_tgt_next : Env P :=
          { ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store,
                           factory := ρ_hoist.factory }
        have h_eval_inner_src : ρ_inner.factory = ρ_src.factory :=
          block_noFuncDecl_preserves_factory P (EvalCmd P) extendFactory body_src ρ_src ρ_inner
            h_src_body_nofd
            (by have := reflTransT_to_prop h_body_src_T;
                simpa [ρ_src_body, Bool.or_false] using this)
        have h_agree_next : StoreAgreement ρ_src_next.store ρ_tgt_next.store :=
          StoreAgreement.of_projectStore_parents h_agree h_agree_inner
        have h_eval_next : ρ_tgt_next.factory = ρ_src_next.factory := by
          show ρ_hoist.factory = ρ_src.factory; exact h_eval
        have h_hf_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
          show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf_inner
        have h_eval_src_next : ρ_src_next.factory = ρ_src.factory := rfl
        have h_src_none_next : ∀ y ∈ U, ρ_src_next.store y = none := by
          intro y hy; show projectStore ρ_src.store ρ_inner.store y = none
          exact projectStore_undef_at (h_src_none y hy)
        have h_tgt_none_next : ∀ y ∈ U, ρ_tgt_next.store y = none := by
          intro y hy; show projectStore ρ_hoist.store ρ_h_inner.store y = none
          exact projectStore_undef_at (h_tgt_none y hy)
        obtain ⟨ρ_post_h, h_post_h_run, h_agree_post, h_hf_post, h_eval_post, h_src_post,
            h_tgt_post⟩ :=
          ih (ρ_src := ρ_src_next) (ρ_hoist := ρ_tgt_next)
            h_agree_next h_eval_next h_hf_next
            (by rw [h_eval_src_next]; exact hwfb) (by rw [h_eval_src_next]; exact hwfv)
            (by rw [h_eval_src_next]; exact hwf_def) (by rw [h_eval_src_next]; exact hwf_congr)
            (by rw [h_eval_src_next]; exact hwf_var)
            h_src_none_next h_tgt_none_next h_loop_T (by simp only [ReflTransT.len] at hlen; omega)
        refine ⟨ρ_post_h, ?_, h_agree_post, h_hf_post, h_eval_post, ?_, h_tgt_post⟩
        · refine ReflTrans_Transitive _ _ _ _ h_hoist_iter ?_
          refine ReflTrans.step _ _ _ .step_stmts_cons ?_
          refine ReflTrans_Transitive _ _ _ _
            (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_post_h_run) ?_
          exact ReflTrans.step _ _ _ .step_seq_done
            (ReflTrans.step _ _ _ .step_stmts_nil (.refl _))
        · -- source post-undefinedness: the whole source loop preserves `U`-undefinedness.
          intro y hy
          exact loopDet_preserves_none_terminal (h_src_none y hy) (reflTransT_to_prop
            (ReflTransT.step _ _ _ (StepStmt.step_loop_enter
              ht hwf) hrest))

/-- Prop-level wrapper of `dualUndefLoopDetSA_TE_fuel`. -/
public theorem dualUndefLoopDetSA_TE {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {U : List P.Ident}
    (body_sim : BodyDualUndefSA (extendFactory := extendFactory) U body_src body_h)
    (h_src_body_nofd : Block.noFuncDecl body_src = true)
    {ρ_src ρ_hoist ρ_post : Env P}
    (h_agree : StoreAgreement ρ_src.store ρ_hoist.store)
    (h_eval : ρ_hoist.factory = ρ_src.factory) (h_hf : ρ_hoist.hasFailure = ρ_src.hasFailure)
    (hwfb : WellFormedSemanticEvalBool ρ_src.factory) (hwfv : WellFormedSemanticEvalVal
        ρ_src.factory)
    (hwf_def : WellFormedSemanticEvalMono ρ_src.factory)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ_src.factory)
    (hwf_var : WellFormedSemanticEvalVar ρ_src.factory)
    (h_src_none : ∀ y ∈ U, ρ_src.store y = none)
    (h_tgt_none : ∀ y ∈ U, ρ_hoist.store y = none)
    (h_run : StepStmtStar P (EvalCmd P) extendFactory
        (.stmt (.loop (.det g) none [] body_src md_s) ρ_src) (.terminal ρ_post)) :
    ∃ ρ_post_h : Env P,
      StepStmtStar P (EvalCmd P) extendFactory
        (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist) (.terminal ρ_post_h) ∧
      StoreAgreement ρ_post.store ρ_post_h.store ∧
      ρ_post_h.hasFailure = ρ_post.hasFailure ∧ ρ_post_h.factory = ρ_post.factory := by
  obtain ⟨ρ_post_h, h, ha, hf, he, _, _⟩ :=
    dualUndefLoopDetSA_TE_fuel body_sim h_src_body_nofd
      (reflTrans_to_T h_run).len h_agree h_eval h_hf hwfb hwfv hwf_def hwf_congr hwf_var
      h_src_none h_tgt_none (reflTrans_to_T h_run) (Nat.le_refl _)
  exact ⟨ρ_post_h, h, ha, hf, he⟩

/-- **Dual-undef `StoreAgreement` EXITING-target fuel recursion.** -/
private theorem dualUndefLoopDetSA_E_fuel {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {U : List P.Ident}
    (body_sim : BodyDualUndefSA (extendFactory := extendFactory) U body_src body_h)
    (h_src_body_nofd : Block.noFuncDecl body_src = true) :
    ∀ (n : Nat) {ρ_src ρ_hoist ρ_post : Env P} {label : String},
      StoreAgreement ρ_src.store ρ_hoist.store →
      ρ_hoist.factory = ρ_src.factory → ρ_hoist.hasFailure = ρ_src.hasFailure →
      WellFormedSemanticEvalBool ρ_src.factory → WellFormedSemanticEvalVal ρ_src.factory →
      WellFormedSemanticEvalMono ρ_src.factory → WellFormedSemanticEvalExprCongr ρ_src.factory →
      WellFormedSemanticEvalVar ρ_src.factory →
      (∀ y ∈ U, ρ_src.store y = none) →
      (∀ y ∈ U, ρ_hoist.store y = none) →
      (h_run : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
        (.stmt (.loop (.det g) none [] body_src md_s) ρ_src) (.exiting label ρ_post)) →
      h_run.len ≤ n →
      ∃ ρ_post_h : Env P,
        StepStmtStar P (EvalCmd P) extendFactory
          (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist) (.exiting label ρ_post_h) ∧
        StoreAgreement ρ_post.store ρ_post_h.store ∧
        ρ_post_h.hasFailure = ρ_post.hasFailure ∧ ρ_post_h.factory = ρ_post.factory := by
  intro n
  induction n with
  | zero =>
    intro ρ_src ρ_hoist ρ_post label _ _ _ _ _ _ _ _ _ _ h_run hlen
    match h_run with
    | .step _ _ _ _ _ => simp [ReflTransT.len] at hlen
  | succ n ih =>
    intro ρ_src ρ_hoist ρ_post label h_agree h_eval h_hf hwfb hwfv hwf_def hwf_congr hwf_var
      h_src_none h_tgt_none h_run hlen
    match h_run with
    | .step _ _ _ step hrest =>
      cases step with
      | step_loop_exit ht hwf =>
        match hrest with
        | .step _ _ _ hd _ => exact nomatch hd
      | step_loop_enter ht hwf =>
        have h_cond_h : P.eval ρ_hoist.factory ρ_hoist.store g = .some HasBool.tt := by
          rw [h_eval]
          exact hwf_def g HasBool.tt ρ_src.store ρ_hoist.store
            (storeAgreement_supplies_mono_premise ρ_src.store ρ_hoist.store h_agree) ht
        let ρ_src_body : Env P := ρ_src
        let ρ_h_body : Env P := ρ_hoist
        have h_agree_body : StoreAgreement ρ_src_body.store ρ_h_body.store := h_agree
        have h_eval_body : ρ_h_body.factory = ρ_src_body.factory := h_eval
        have h_hf_body : ρ_h_body.hasFailure = ρ_src_body.hasFailure := h_hf
        have h_src_none_body : ∀ y ∈ U, ρ_src_body.store y = none := h_src_none
        have h_tgt_none_body : ∀ y ∈ U, ρ_h_body.store y = none := h_tgt_none
        have h_wfb_h : WellFormedSemanticEvalBool ρ_hoist.factory := by rw [h_eval]; exact hwfb
        rcases seqT_reaches_exiting hrest with ⟨h_block_exit, hl⟩ | ⟨ρ₁, h_block_term, h_loop_stmts,
            hl⟩
        · obtain ⟨ρ_inner, h_body_exit_T, h_ρpost_eq, hl2⟩ := blockT_none_reaches_exiting
            h_block_exit
          obtain ⟨ρ_h_inner, h_body_h_exit, h_agree_inner, h_hf_inner, h_eval_inner⟩ :=
            (body_sim ρ_src_body ρ_h_body h_eval_body h_hf_body h_agree_body
              hwfb hwfv hwf_def hwf_congr hwf_var h_src_none_body h_tgt_none_body).2
              label ρ_inner (reflTransT_to_prop h_body_exit_T)
          refine ⟨{ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store,
                                   factory := ρ_hoist.factory }, ?_, ?_, ?_, ?_⟩
          · refine ReflTrans.step _ _ _
              (.step_loop_enter
                h_cond_h h_wfb_h) ?_
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _
                (block_inner_star P (EvalCmd P) extendFactory _ _ (none : Option String)
                    ρ_hoist.store ρ_hoist.factory
                  (show StepStmtStar P (EvalCmd P) extendFactory
                      (.stmts body_h ρ_hoist)
                      (.exiting label ρ_h_inner) from h_body_h_exit))) ?_
            refine ReflTrans.step _ _ _ (.step_seq_inner (.step_block_exit_mismatch ?_)) ?_
            · exact (by simp)
            · exact ReflTrans.step _ _ _ .step_seq_exit (.refl _)
          · subst h_ρpost_eq; exact StoreAgreement.of_projectStore_parents h_agree h_agree_inner
          · subst h_ρpost_eq; show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf_inner
          · subst h_ρpost_eq; show ρ_hoist.factory = ρ_src.factory; exact h_eval
        · obtain ⟨ρ_inner, h_body_term_T, h_ρ_block_eq, hl_blk⟩ := blockT_none_reaches_terminal
            h_block_term
          subst h_ρ_block_eq
          obtain ⟨ρ_h_inner, h_body_h_run, h_agree_inner, h_hf_inner, h_eval_inner⟩ :=
            (body_sim ρ_src_body ρ_h_body h_eval_body h_hf_body h_agree_body
              hwfb hwfv hwf_def hwf_congr hwf_var h_src_none_body h_tgt_none_body).1
              ρ_inner (reflTransT_to_prop h_body_term_T)
          have h_hoist_iter : StepStmtStar P (EvalCmd P) extendFactory
              (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist)
              (.stmts [.loop (.det g) none [] body_h md_h]
                { ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store,
                                 factory := ρ_hoist.factory }) := by
            have hb : StepStmtStar P (EvalCmd P) extendFactory
                (.stmts body_h ρ_h_body) (.terminal ρ_h_inner) := h_body_h_run
            have := buildLoopIterationDet (g := g) (body := body_h) (md := md_h)
              (ρ_pre := ρ_h_body) (ρ_body := ρ_h_inner) ?_ ?_ hb
            · simpa [ρ_h_body] using this
            · show P.eval ρ_h_body.factory ρ_h_body.store g = .some HasBool.tt
              show P.eval ρ_hoist.factory ρ_hoist.store g = .some HasBool.tt; exact h_cond_h
            · show WellFormedSemanticEvalBool ρ_h_body.factory
              show WellFormedSemanticEvalBool ρ_hoist.factory; exact h_wfb_h
          let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store,
                                                   factory := ρ_src.factory }
          let ρ_tgt_next : Env P :=
            { ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store,
                             factory := ρ_hoist.factory }
          have h_eval_inner_src : ρ_inner.factory = ρ_src.factory :=
            block_noFuncDecl_preserves_factory P (EvalCmd P) extendFactory body_src ρ_src ρ_inner
              h_src_body_nofd
              (by have := reflTransT_to_prop h_body_term_T;
                  simpa [ρ_src_body, Bool.or_false] using this)
          have h_agree_next : StoreAgreement ρ_src_next.store ρ_tgt_next.store :=
            StoreAgreement.of_projectStore_parents h_agree h_agree_inner
          have h_eval_next : ρ_tgt_next.factory = ρ_src_next.factory := by
            show ρ_hoist.factory = ρ_src.factory; exact h_eval
          have h_hf_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
            show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf_inner
          have h_eval_src_next : ρ_src_next.factory = ρ_src.factory := rfl
          have h_src_none_next : ∀ y ∈ U, ρ_src_next.store y = none := by
            intro y hy; show projectStore ρ_src.store ρ_inner.store y = none
            exact projectStore_undef_at (h_src_none y hy)
          have h_tgt_none_next : ∀ y ∈ U, ρ_tgt_next.store y = none := by
            intro y hy; show projectStore ρ_hoist.store ρ_h_inner.store y = none
            exact projectStore_undef_at (h_tgt_none y hy)
          rcases stmtsT_cons_exiting h_loop_stmts with ⟨h_inner_loop_T, _⟩ | ⟨ρ₂, _, h_nil, _⟩
          · obtain ⟨ρ_post_h, h_post_h_run, h_agree_post, h_hf_post, h_eval_post⟩ :=
              ih (ρ_src := ρ_src_next) (ρ_hoist := ρ_tgt_next) (ρ_post := ρ_post) (label := label)
                h_agree_next h_eval_next h_hf_next
                (by rw [h_eval_src_next]; exact hwfb) (by rw [h_eval_src_next]; exact hwfv)
                (by rw [h_eval_src_next]; exact hwf_def) (by rw [h_eval_src_next]; exact hwf_congr)
                (by rw [h_eval_src_next]; exact hwf_var)
                h_src_none_next h_tgt_none_next h_inner_loop_T
                    (by simp only [ReflTransT.len] at hlen; omega)
            refine ⟨ρ_post_h, ?_, h_agree_post, h_hf_post, h_eval_post⟩
            refine ReflTrans_Transitive _ _ _ _ h_hoist_iter ?_
            refine ReflTrans.step _ _ _ .step_stmts_cons ?_
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_post_h_run) ?_
            exact ReflTrans.step _ _ _ .step_seq_exit (.refl _)
          · match h_nil with
            | .step _ _ _ .step_stmts_nil hr2 =>
              match hr2 with
              | .step _ _ _ hd _ => exact nomatch hd

/-- Prop-level wrapper of `dualUndefLoopDetSA_E_fuel`. -/
public theorem dualUndefLoopDetSA_E {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {U : List P.Ident}
    (body_sim : BodyDualUndefSA (extendFactory := extendFactory) U body_src body_h)
    (h_src_body_nofd : Block.noFuncDecl body_src = true)
    {ρ_src ρ_hoist ρ_post : Env P} {label : String}
    (h_agree : StoreAgreement ρ_src.store ρ_hoist.store)
    (h_eval : ρ_hoist.factory = ρ_src.factory) (h_hf : ρ_hoist.hasFailure = ρ_src.hasFailure)
    (hwfb : WellFormedSemanticEvalBool ρ_src.factory) (hwfv : WellFormedSemanticEvalVal
        ρ_src.factory)
    (hwf_def : WellFormedSemanticEvalMono ρ_src.factory)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ_src.factory)
    (hwf_var : WellFormedSemanticEvalVar ρ_src.factory)
    (h_src_none : ∀ y ∈ U, ρ_src.store y = none)
    (h_tgt_none : ∀ y ∈ U, ρ_hoist.store y = none)
    (h_run : StepStmtStar P (EvalCmd P) extendFactory
        (.stmt (.loop (.det g) none [] body_src md_s) ρ_src) (.exiting label ρ_post)) :
    ∃ ρ_post_h : Env P,
      StepStmtStar P (EvalCmd P) extendFactory
        (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist) (.exiting label ρ_post_h) ∧
      StoreAgreement ρ_post.store ρ_post_h.store ∧
      ρ_post_h.hasFailure = ρ_post.hasFailure ∧ ρ_post_h.factory = ρ_post.factory :=
  dualUndefLoopDetSA_E_fuel body_sim h_src_body_nofd
    (reflTrans_to_T h_run).len h_agree h_eval h_hf hwfb hwfv hwf_def hwf_congr hwf_var
    h_src_none h_tgt_none (reflTrans_to_T h_run) (Nat.le_refl _)

/-- **Dual-undef FAILING-body simulation slot.**

The failing-config sibling of `BodyDualUndefSA`'s terminal clause: a source body
run from a dual-undef store that reaches a *failing* config is matched by a hoist
body run that reaches a failing config too.  No `StoreAgreement`/eval/hf
re-establishment at the failing point (the loop is abandoned there). -/
public def BodyDualUndefFailSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    (U : List P.Ident) (bsrc bh : List (Stmt P (Cmd P))) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    ρ_h.factory = ρ_s.factory → ρ_h.hasFailure = ρ_s.hasFailure →
    StoreAgreement ρ_s.store ρ_h.store →
    WellFormedSemanticEvalBool ρ_s.factory → WellFormedSemanticEvalVal ρ_s.factory →
    WellFormedSemanticEvalMono ρ_s.factory → WellFormedSemanticEvalExprCongr ρ_s.factory →
    WellFormedSemanticEvalVar ρ_s.factory →
    (∀ y ∈ U, ρ_s.store y = none) →
    (∀ y ∈ U, ρ_h.store y = none) →
    ∀ (d : Config P (Cmd P)),
      StepStmtStar P (EvalCmd P) extendFactory (.stmts bsrc ρ_s) d →
      d.getEnv.hasFailure = true →
      ∃ d', StepStmtStar P (EvalCmd P) extendFactory (.stmts bh ρ_h) d'
        ∧ d'.getEnv.hasFailure = true

/-- **Dual-undef `StoreAgreement` FAILING-target fuel recursion.**

The failing-config sibling of `dualUndefLoopDetSA_TE_fuel`: a source loop run that
reaches an intermediate *failing* config (possibly on a never-terminating loop) is
matched by a hoist loop run that reaches a failing config too.  Inducts on a `Nat`
fuel bounding the source run length (finite by failure monotonicity).

* `refl` / `step_loop_exit`: the loop-head env IS the failing config, so
  `ρ_src.hasFailure = true`; by `h_hf` the hoist loop head fails too (`refl`).
* `step_loop_enter`: peel one iteration via `seqT_reaches_failing'`:
  - **inl** the failure is inside THIS iteration's body → `BodyDualUndefFailSA`
    supplies a failing hoist body run, lifted into the hoist loop's body block.
  - **inr** this iteration's block terminated, the residual loop fails →
    `BodyDualUndefSA`'s terminal clause drives one hoist iteration and the
    recursion (`ih`) handles the residual loop at strictly smaller fuel (the `U`
    undefinedness re-established per iteration by `projectStore_undef_at`). -/
public theorem dualUndefLoopDetSA_F_fuel {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {U : List P.Ident}
    (body_sim : BodyDualUndefSA (extendFactory := extendFactory) U body_src body_h)
    (body_sim_fail : BodyDualUndefFailSA (extendFactory := extendFactory) U body_src body_h)
    (h_src_body_nofd : Block.noFuncDecl body_src = true) :
    ∀ (n : Nat) {ρ_src ρ_hoist : Env P} {a' : Config P (Cmd P)},
      StoreAgreement ρ_src.store ρ_hoist.store →
      ρ_hoist.factory = ρ_src.factory → ρ_hoist.hasFailure = ρ_src.hasFailure →
      WellFormedSemanticEvalBool ρ_src.factory → WellFormedSemanticEvalVal ρ_src.factory →
      WellFormedSemanticEvalMono ρ_src.factory → WellFormedSemanticEvalExprCongr ρ_src.factory →
      WellFormedSemanticEvalVar ρ_src.factory →
      (∀ y ∈ U, ρ_src.store y = none) →
      (∀ y ∈ U, ρ_hoist.store y = none) →
      (h_run : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
        (.stmt (.loop (.det g) none [] body_src md_s) ρ_src) a') →
      a'.getEnv.hasFailure = true →
      h_run.len ≤ n →
      ∃ d, StepStmtStar P (EvalCmd P) extendFactory
          (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist) d
        ∧ d.getEnv.hasFailure = true := by
  intro n
  induction n with
  | zero =>
    intro ρ_src ρ_hoist a' h_agree h_eval h_hf _ _ _ _ _ _ _ h_run h_a'_fail hlen
    match h_run, hlen with
    | .refl _, _ =>
      have : ρ_src.hasFailure = true := by simpa [Config.getEnv] using h_a'_fail
      exact ⟨.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist, .refl _,
        by simpa [Config.getEnv] using (h_hf ▸ this)⟩
    | .step _ _ _ _ _, hl => simp [ReflTransT.len] at hl
  | succ n ih =>
    intro ρ_src ρ_hoist a' h_agree h_eval h_hf hwfb hwfv hwf_def hwf_congr hwf_var
      h_src_none h_tgt_none h_run h_a'_fail hlen
    match h_run, hlen with
    | .refl _, _ =>
      have : ρ_src.hasFailure = true := by simpa [Config.getEnv] using h_a'_fail
      exact ⟨.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist, .refl _,
        by simpa [Config.getEnv] using (h_hf ▸ this)⟩
    | .step _ _ _ step hrest, hl_succ =>
      cases step with
      | step_loop_exit ht hwf =>
        have ha'_eq : a' = .terminal ρ_src := by
          match hrest with
          | .refl _ => rfl
          | .step _ _ _ hd _ => exact nomatch hd
        rw [ha'_eq] at h_a'_fail
        have : ρ_src.hasFailure = true := by simpa [Config.getEnv, Bool.or_false] using h_a'_fail
        exact ⟨.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist, .refl _,
          by simpa [Config.getEnv] using (h_hf ▸ this)⟩
      | step_loop_enter ht hwf =>
        have h_cond_h : P.eval ρ_hoist.factory ρ_hoist.store g = .some HasBool.tt := by
          rw [h_eval]
          exact hwf_def g HasBool.tt ρ_src.store ρ_hoist.store
            (storeAgreement_supplies_mono_premise ρ_src.store ρ_hoist.store h_agree) ht
        have h_wfb_h : WellFormedSemanticEvalBool ρ_hoist.factory := by rw [h_eval]; exact hwfb
        let ρ_src_body : Env P := ρ_src
        let ρ_h_body : Env P := ρ_hoist
        have h_agree_body : StoreAgreement ρ_src_body.store ρ_h_body.store := h_agree
        have h_eval_body : ρ_h_body.factory = ρ_src_body.factory := h_eval
        have h_hf_body : ρ_h_body.hasFailure = ρ_src_body.hasFailure := h_hf
        have h_src_none_body : ∀ y ∈ U, ρ_src_body.store y = none := h_src_none
        have h_tgt_none_body : ∀ y ∈ U, ρ_h_body.store y = none := h_tgt_none
        have h_step_enter : StepStmtStar P (EvalCmd P) extendFactory
            (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist)
            (.seq (.block .none ρ_hoist.store ρ_hoist.factory (.stmts body_h ρ_h_body))
              [.loop (.det g) none [] body_h md_h]) :=
          .step _ _ _ (StepStmt.step_loop_enter
            h_cond_h h_wfb_h) (.refl _)
        rcases seqT_reaches_failing' P extendFactory hrest h_a'_fail with hA | hB
        · -- CASE A: the failure is inside THIS iteration's body block.
          obtain ⟨d_blk, h_blk_run, hd_blk_fail, _⟩ := hA
          obtain ⟨d_body, h_body_run, hd_body_fail, _⟩ :=
            blockT_none_reaches_failing' P extendFactory h_blk_run hd_blk_fail
          obtain ⟨d', h_body_tgt, hd'_fail⟩ :=
            body_sim_fail ρ_src_body ρ_h_body h_eval_body h_hf_body h_agree_body
              hwfb hwfv hwf_def hwf_congr hwf_var h_src_none_body h_tgt_none_body d_body
              (reflTransT_to_prop h_body_run) hd_body_fail
          have h_blk_tgt : StepStmtStar P (EvalCmd P) extendFactory
              (.block .none ρ_hoist.store ρ_hoist.factory (.stmts body_h ρ_h_body))
              (.block .none ρ_hoist.store ρ_hoist.factory d') :=
            block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_hoist.store ρ_hoist.factory
                h_body_tgt
          refine ⟨.seq (.block .none ρ_hoist.store ρ_hoist.factory d')
            [.loop (.det g) none [] body_h md_h],
            ReflTrans_Transitive _ _ _ _ h_step_enter
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_blk_tgt), ?_⟩
          simpa [Config.getEnv] using hd'_fail
        · -- CASE B: this iteration's body terminated; recurse on the next iteration.
          obtain ⟨ρ_block, d_rest, h_blk_term, h_loop_rest, hd_rest_fail, hlen_rest⟩ := hB
          obtain ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
            blockT_none_reaches_terminal (extendFactory := extendFactory) h_blk_term
          subst heq_ρ_block
          have h_body_run : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts body_src ρ_src_body) (.terminal ρ_inner) := reflTransT_to_prop h_inner_term
          obtain ⟨ρ_h_inner, h_body_h_run, h_agree_inner, h_hf_inner, h_eval_inner⟩ :=
            (body_sim ρ_src_body ρ_h_body h_eval_body h_hf_body h_agree_body
              hwfb hwfv hwf_def hwf_congr hwf_var h_src_none_body h_tgt_none_body).1
              ρ_inner h_body_run
          have h_hoist_iter : StepStmtStar P (EvalCmd P) extendFactory
              (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist)
              (.stmts [.loop (.det g) none [] body_h md_h]
                { ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store,
                                 factory := ρ_hoist.factory }) := by
            have hb : StepStmtStar P (EvalCmd P) extendFactory
                (.stmts body_h ρ_h_body) (.terminal ρ_h_inner) := h_body_h_run
            have := buildLoopIterationDet (g := g) (body := body_h) (md := md_h)
              (ρ_pre := ρ_h_body) (ρ_body := ρ_h_inner) ?_ ?_ hb
            · simpa [ρ_h_body] using this
            · show P.eval ρ_h_body.factory ρ_h_body.store g = .some HasBool.tt
              show P.eval ρ_hoist.factory ρ_hoist.store g = .some HasBool.tt; exact h_cond_h
            · show WellFormedSemanticEvalBool ρ_h_body.factory
              show WellFormedSemanticEvalBool ρ_hoist.factory; exact h_wfb_h
          let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store,
                                                   factory := ρ_src.factory }
          let ρ_tgt_next : Env P :=
            { ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store,
                             factory := ρ_hoist.factory }
          have h_eval_inner_src : ρ_inner.factory = ρ_src.factory :=
            block_noFuncDecl_preserves_factory P (EvalCmd P) extendFactory body_src ρ_src ρ_inner
              h_src_body_nofd
              (by have := h_body_run; simpa [ρ_src_body, Bool.or_false] using this)
          have h_agree_next : StoreAgreement ρ_src_next.store ρ_tgt_next.store :=
            StoreAgreement.of_projectStore_parents h_agree h_agree_inner
          have h_eval_next : ρ_tgt_next.factory = ρ_src_next.factory := by
            show ρ_hoist.factory = ρ_src.factory; exact h_eval
          have h_hf_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
            show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf_inner
          have h_eval_src_next : ρ_src_next.factory = ρ_src.factory := rfl
          have h_src_none_next : ∀ y ∈ U, ρ_src_next.store y = none := by
            intro y hy; show projectStore ρ_src.store ρ_inner.store y = none
            exact projectStore_undef_at (h_src_none y hy)
          have h_tgt_none_next : ∀ y ∈ U, ρ_tgt_next.store y = none := by
            intro y hy; show projectStore ρ_hoist.store ρ_h_inner.store y = none
            exact projectStore_undef_at (h_tgt_none y hy)
          obtain ⟨d_loop, h_loop_stmt, hd_loop_fail, hlen_loop⟩ :=
            stmts_singleton_reaches_failing' P extendFactory h_loop_rest hd_rest_fail
          have h_inner_le_n : h_loop_stmt.len ≤ n := by
            simp only [ReflTransT.len] at hl_succ; omega
          obtain ⟨d, h_run_recurse, hd_fail⟩ :=
            ih (ρ_src := ρ_src_next) (ρ_hoist := ρ_tgt_next)
              h_agree_next h_eval_next h_hf_next
              (by rw [h_eval_src_next]; exact hwfb) (by rw [h_eval_src_next]; exact hwfv)
              (by rw [h_eval_src_next]; exact hwf_def) (by rw [h_eval_src_next]; exact hwf_congr)
              (by rw [h_eval_src_next]; exact hwf_var)
              h_src_none_next h_tgt_none_next h_loop_stmt hd_loop_fail h_inner_le_n
          have h_run_recurse_stmts : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts [.loop (.det g) none [] body_h md_h] ρ_tgt_next)
              (.seq d ([] : List (Stmt P (Cmd P)))) :=
            .step _ _ _ StepStmt.step_stmts_cons
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_run_recurse)
          refine ⟨.seq d ([] : List (Stmt P (Cmd P))),
            ReflTrans_Transitive _ _ _ _ h_hoist_iter h_run_recurse_stmts, ?_⟩
          simpa [Config.getEnv] using hd_fail

/-- **Same-name `StoreAgreement` FAILING-body simulation slot.**

The failing-config sibling of `BodySimSumSA`'s terminal clause, carrying the SAME
`D`-definedness invariant (`∀ y∈D, isSome`) at entry that the same-name driver
threads (target slots stay defined; source slots may be undefined under the
`StoreAgreement`).  A source body run from such a store that reaches a *failing*
config is matched by a hoist body run that reaches a failing config too.  No
`StoreAgreement`/eval/hf re-establishment at the failing point (the loop is
abandoned there). -/
public def BodySimSumFailSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    (D : List P.Ident) (bsrc bh : List (Stmt P (Cmd P))) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    ρ_h.factory = ρ_s.factory → ρ_h.hasFailure = ρ_s.hasFailure →
    StoreAgreement ρ_s.store ρ_h.store →
    WellFormedSemanticEvalBool ρ_s.factory → WellFormedSemanticEvalVal ρ_s.factory →
    WellFormedSemanticEvalMono ρ_s.factory → WellFormedSemanticEvalExprCongr ρ_s.factory →
    WellFormedSemanticEvalVar ρ_s.factory →
    (∀ y ∈ D, (ρ_h.store y).isSome = true) →
    ∀ (d : Config P (Cmd P)),
      StepStmtStar P (EvalCmd P) extendFactory (.stmts bsrc ρ_s) d →
      d.getEnv.hasFailure = true →
      ∃ d', StepStmtStar P (EvalCmd P) extendFactory (.stmts bh ρ_h) d'
        ∧ d'.getEnv.hasFailure = true

/-- **Same-name `StoreAgreement` FAILING-target fuel recursion.**

The asymmetric (target-defined) sibling of `dualUndefLoopDetSA_F_fuel`: instead of
carrying both-none undefinedness it threads the `StoreAgreement` + the
`D`-definedness invariant (the prelude-defined target slots stay `isSome`).  A
source loop run reaching an intermediate *failing* config is matched by a hoist
loop run that reaches a failing config too.  Inducts on a `Nat` fuel bounding the
source run length.

* `refl` / `step_loop_exit`: the loop-head env IS the failing config, so by `h_hf`
  the hoist loop head fails too (`refl`).
* `step_loop_enter`: peel one iteration via `seqT_reaches_failing'`:
  - **inl** the failure is inside THIS iteration's body → `BodySimSumFailSA`
    supplies a failing hoist body run, lifted into the hoist loop's body block.
  - **inr** this iteration's body terminated, the residual loop fails →
    `BodySimSumSA`'s terminal clause drives one hoist iteration and the recursion
    (`ih`) handles the residual loop at strictly smaller fuel; the `D`-definedness
    is re-established per iteration because `projectStore` keeps parent-defined
    keys (exactly as in `samenameLoopDetSA_TE_fuel`). -/
private theorem samenameLoopDetSA_F_fuel {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {D : List P.Ident}
    (body_sim : BodySimSumSA (extendFactory := extendFactory) D body_src body_h)
    (body_sim_fail : BodySimSumFailSA (extendFactory := extendFactory) D body_src body_h)
    (h_src_body_nofd : Block.noFuncDecl body_src = true) :
    ∀ (n : Nat) {ρ_src ρ_hoist : Env P} {a' : Config P (Cmd P)},
      StoreAgreement ρ_src.store ρ_hoist.store →
      ρ_hoist.factory = ρ_src.factory → ρ_hoist.hasFailure = ρ_src.hasFailure →
      WellFormedSemanticEvalBool ρ_src.factory → WellFormedSemanticEvalVal ρ_src.factory →
      WellFormedSemanticEvalMono ρ_src.factory → WellFormedSemanticEvalExprCongr ρ_src.factory →
      WellFormedSemanticEvalVar ρ_src.factory →
      (∀ y ∈ D, (ρ_hoist.store y).isSome = true) →
      (h_run : ReflTransT (StepStmt P (EvalCmd P) extendFactory)
        (.stmt (.loop (.det g) none [] body_src md_s) ρ_src) a') →
      a'.getEnv.hasFailure = true →
      h_run.len ≤ n →
      ∃ d, StepStmtStar P (EvalCmd P) extendFactory
          (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist) d
        ∧ d.getEnv.hasFailure = true := by
  intro n
  induction n with
  | zero =>
    intro ρ_src ρ_hoist a' h_agree h_eval h_hf _ _ _ _ _ _ h_run h_a'_fail hlen
    match h_run, hlen with
    | .refl _, _ =>
      have : ρ_src.hasFailure = true := by simpa [Config.getEnv] using h_a'_fail
      exact ⟨.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist, .refl _,
        by simpa [Config.getEnv] using (h_hf ▸ this)⟩
    | .step _ _ _ _ _, hl => simp [ReflTransT.len] at hl
  | succ n ih =>
    intro ρ_src ρ_hoist a' h_agree h_eval h_hf hwfb hwfv hwf_def hwf_congr hwf_var
      h_def h_run h_a'_fail hlen
    match h_run, hlen with
    | .refl _, _ =>
      have : ρ_src.hasFailure = true := by simpa [Config.getEnv] using h_a'_fail
      exact ⟨.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist, .refl _,
        by simpa [Config.getEnv] using (h_hf ▸ this)⟩
    | .step _ _ _ step hrest, hl_succ =>
      cases step with
      | step_loop_exit ht hwf =>
        have ha'_eq : a' = .terminal ρ_src := by
          match hrest with
          | .refl _ => rfl
          | .step _ _ _ hd _ => exact nomatch hd
        rw [ha'_eq] at h_a'_fail
        have : ρ_src.hasFailure = true := by simpa [Config.getEnv, Bool.or_false] using h_a'_fail
        exact ⟨.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist, .refl _,
          by simpa [Config.getEnv] using (h_hf ▸ this)⟩
      | step_loop_enter ht hwf =>
        have h_cond_h : P.eval ρ_hoist.factory ρ_hoist.store g = .some HasBool.tt := by
          rw [h_eval]
          exact hwf_def g HasBool.tt ρ_src.store ρ_hoist.store
            (storeAgreement_supplies_mono_premise ρ_src.store ρ_hoist.store h_agree) ht
        have h_wfb_h : WellFormedSemanticEvalBool ρ_hoist.factory := by rw [h_eval]; exact hwfb
        let ρ_src_body : Env P := ρ_src
        let ρ_h_body : Env P := ρ_hoist
        have h_agree_body : StoreAgreement ρ_src_body.store ρ_h_body.store := h_agree
        have h_eval_body : ρ_h_body.factory = ρ_src_body.factory := h_eval
        have h_hf_body : ρ_h_body.hasFailure = ρ_src_body.hasFailure := h_hf
        have h_def_body : ∀ y ∈ D, (ρ_h_body.store y).isSome = true := h_def
        have h_step_enter : StepStmtStar P (EvalCmd P) extendFactory
            (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist)
            (.seq (.block .none ρ_hoist.store ρ_hoist.factory (.stmts body_h ρ_h_body))
              [.loop (.det g) none [] body_h md_h]) :=
          .step _ _ _ (StepStmt.step_loop_enter
            h_cond_h h_wfb_h) (.refl _)
        rcases seqT_reaches_failing' P extendFactory hrest h_a'_fail with hA | hB
        · -- CASE A: the failure is inside THIS iteration's body block.
          obtain ⟨d_blk, h_blk_run, hd_blk_fail, _⟩ := hA
          obtain ⟨d_body, h_body_run, hd_body_fail, _⟩ :=
            blockT_none_reaches_failing' P extendFactory h_blk_run hd_blk_fail
          obtain ⟨d', h_body_tgt, hd'_fail⟩ :=
            body_sim_fail ρ_src_body ρ_h_body h_eval_body h_hf_body h_agree_body
              hwfb hwfv hwf_def hwf_congr hwf_var h_def_body d_body
              (reflTransT_to_prop h_body_run) hd_body_fail
          have h_blk_tgt : StepStmtStar P (EvalCmd P) extendFactory
              (.block .none ρ_hoist.store ρ_hoist.factory (.stmts body_h ρ_h_body))
              (.block .none ρ_hoist.store ρ_hoist.factory d') :=
            block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_hoist.store ρ_hoist.factory
                h_body_tgt
          refine ⟨.seq (.block .none ρ_hoist.store ρ_hoist.factory d')
            [.loop (.det g) none [] body_h md_h],
            ReflTrans_Transitive _ _ _ _ h_step_enter
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_blk_tgt), ?_⟩
          simpa [Config.getEnv] using hd'_fail
        · -- CASE B: this iteration's body terminated; recurse on the next iteration.
          obtain ⟨ρ_block, d_rest, h_blk_term, h_loop_rest, hd_rest_fail, hlen_rest⟩ := hB
          obtain ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
            blockT_none_reaches_terminal (extendFactory := extendFactory) h_blk_term
          subst heq_ρ_block
          have h_body_run : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts body_src ρ_src_body) (.terminal ρ_inner) := reflTransT_to_prop h_inner_term
          obtain ⟨ρ_h_inner, h_body_h_run, h_agree_inner, h_hf_inner, h_eval_inner, h_def_inner⟩ :=
            (body_sim ρ_src_body ρ_h_body h_eval_body h_hf_body h_agree_body
              hwfb hwfv hwf_def hwf_congr hwf_var h_def_body).1
              ρ_inner h_body_run
          have h_hoist_iter : StepStmtStar P (EvalCmd P) extendFactory
              (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist)
              (.stmts [.loop (.det g) none [] body_h md_h]
                { ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store,
                                 factory := ρ_hoist.factory }) := by
            have hb : StepStmtStar P (EvalCmd P) extendFactory
                (.stmts body_h ρ_h_body) (.terminal ρ_h_inner) := h_body_h_run
            have := buildLoopIterationDet (g := g) (body := body_h) (md := md_h)
              (ρ_pre := ρ_h_body) (ρ_body := ρ_h_inner) ?_ ?_ hb
            · simpa [ρ_h_body] using this
            · show P.eval ρ_h_body.factory ρ_h_body.store g = .some HasBool.tt
              show P.eval ρ_hoist.factory ρ_hoist.store g = .some HasBool.tt; exact h_cond_h
            · show WellFormedSemanticEvalBool ρ_h_body.factory
              show WellFormedSemanticEvalBool ρ_hoist.factory; exact h_wfb_h
          let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store,
                                                   factory := ρ_src.factory }
          let ρ_tgt_next : Env P :=
            { ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store,
                             factory := ρ_hoist.factory }
          have h_eval_inner_src : ρ_inner.factory = ρ_src.factory :=
            block_noFuncDecl_preserves_factory P (EvalCmd P) extendFactory body_src ρ_src ρ_inner
              h_src_body_nofd
              (by have := h_body_run; simpa [ρ_src_body, Bool.or_false] using this)
          have h_agree_next : StoreAgreement ρ_src_next.store ρ_tgt_next.store :=
            StoreAgreement.of_projectStore_parents h_agree h_agree_inner
          have h_eval_next : ρ_tgt_next.factory = ρ_src_next.factory := by
            show ρ_hoist.factory = ρ_src.factory; exact h_eval
          have h_hf_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
            show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf_inner
          have h_eval_src_next : ρ_src_next.factory = ρ_src.factory := rfl
          have h_def_next : ∀ y ∈ D, (ρ_tgt_next.store y).isSome = true := by
            intro y hy
            show (projectStore ρ_hoist.store ρ_h_inner.store y).isSome = true
            show ((if (ρ_hoist.store y).isSome then ρ_h_inner.store y else none)).isSome = true
            rw [if_pos (h_def y hy)]; exact h_def_inner y hy
          obtain ⟨d_loop, h_loop_stmt, hd_loop_fail, hlen_loop⟩ :=
            stmts_singleton_reaches_failing' P extendFactory h_loop_rest hd_rest_fail
          have h_inner_le_n : h_loop_stmt.len ≤ n := by
            simp only [ReflTransT.len] at hl_succ; omega
          obtain ⟨d, h_run_recurse, hd_fail⟩ :=
            ih (ρ_src := ρ_src_next) (ρ_hoist := ρ_tgt_next)
              h_agree_next h_eval_next h_hf_next
              (by rw [h_eval_src_next]; exact hwfb) (by rw [h_eval_src_next]; exact hwfv)
              (by rw [h_eval_src_next]; exact hwf_def) (by rw [h_eval_src_next]; exact hwf_congr)
              (by rw [h_eval_src_next]; exact hwf_var)
              h_def_next h_loop_stmt hd_loop_fail h_inner_le_n
          have h_run_recurse_stmts : StepStmtStar P (EvalCmd P) extendFactory
              (.stmts [.loop (.det g) none [] body_h md_h] ρ_tgt_next)
              (.seq d ([] : List (Stmt P (Cmd P)))) :=
            .step _ _ _ StepStmt.step_stmts_cons
              (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_run_recurse)
          refine ⟨.seq d ([] : List (Stmt P (Cmd P))),
            ReflTrans_Transitive _ _ _ _ h_hoist_iter h_run_recurse_stmts, ?_⟩
          simpa [Config.getEnv] using hd_fail

/-- Prop-level wrapper of `samenameLoopDetSA_F_fuel`: the same-name `StoreAgreement`
FAILING-target driver, instantiating the fuel at the source run length. -/
public theorem samenameLoopDetSA_F {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {D : List P.Ident}
    (body_sim : BodySimSumSA (extendFactory := extendFactory) D body_src body_h)
    (body_sim_fail : BodySimSumFailSA (extendFactory := extendFactory) D body_src body_h)
    (h_src_body_nofd : Block.noFuncDecl body_src = true)
    {ρ_src ρ_hoist : Env P} {a' : Config P (Cmd P)}
    (h_agree : StoreAgreement ρ_src.store ρ_hoist.store)
    (h_eval : ρ_hoist.factory = ρ_src.factory) (h_hf : ρ_hoist.hasFailure = ρ_src.hasFailure)
    (hwfb : WellFormedSemanticEvalBool ρ_src.factory) (hwfv : WellFormedSemanticEvalVal
        ρ_src.factory)
    (hwf_def : WellFormedSemanticEvalMono ρ_src.factory)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ_src.factory)
    (hwf_var : WellFormedSemanticEvalVar ρ_src.factory)
    (h_def : ∀ y ∈ D, (ρ_hoist.store y).isSome = true)
    (h_run : StepStmtStar P (EvalCmd P) extendFactory
        (.stmt (.loop (.det g) none [] body_src md_s) ρ_src) a')
    (h_a'_fail : a'.getEnv.hasFailure = true) :
    ∃ d, StepStmtStar P (EvalCmd P) extendFactory
        (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist) d
      ∧ d.getEnv.hasFailure = true :=
  samenameLoopDetSA_F_fuel body_sim body_sim_fail h_src_body_nofd
    (reflTrans_to_T h_run).len h_agree h_eval h_hf hwfb hwfv hwf_def hwf_congr hwf_var h_def
    (reflTrans_to_T h_run) h_a'_fail (Nat.le_refl _)

/-! ## Coverage of the canonical asymmetric-failing example.

The same-name hoist takes the source `loop g { init x := e; assert Q }` to
`init x := *; loop g { set x := e; assert Q }`.  We exhibit the two body slots the
failing driver consumes for the loop body `[init x := e, assert Q]` vs
`[set x := e, assert Q]` at `D = [x]`:

* `BodySimSumSA [x]` (terminal/exiting) — the source body, when it TERMINATES (the
  assert passed), is matched by the hoist body terminating, keeping `x` defined.
* `BodySimSumFailSA [x]` — when the source body reaches a FAILING config (the
  assert failed; `init`/`set` never fail), the hoist body fails too.

The asymmetric invariant `D = [x]` is satisfiable here: the target keeps `x`
persistently defined (the prelude seeds it, `set x := e` keeps it `isSome`), while
the source `x` may be `none` at the loop head (it is a body-local `init`).  No
hidden side-condition forces the source `x` defined — `assert Q` only reads `x`
after the body's `init x := e` has run (so `x` is source-defined at the assert),
and the per-cmd transport (`initToSetStepSA`) re-establishes `StoreAgreement`
before the assert.  These witness that `samenameLoopDetSA_F` is non-vacuously
applicable to the canonical example. -/

/-- The same-name body sim for `[init x := e, assert lbl Q md]` vs
`[set x := e, assert lbl Q md]` at `D = [x]`: a TERMINATING source body run (the
assert passed) is matched by a terminating hoist body run; the EXITING clause is
vacuous (neither `.cmd` exits).  The per-step transport is `initToSetStepSA` for
the `init→set`, then assert-pass replay (stores agree, so the predicate evaluates
to the same `tt`). -/
public theorem samenameBodySimInitSetAssert {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    {extendFactory : ExtendFactory P}
    (x : P.Ident) (ty : P.Ty) (e : P.Expr) (lbl : String) (Q : P.Expr) (md : MetaData P) :
    BodySimSumSA (extendFactory := extendFactory) [x]
      [.cmd (.init x ty (.det e) md), .cmd (.assert lbl Q md)]
      [.cmd (.set x (.det e) md), .cmd (.assert lbl Q md)] := by
  intro ρ_s ρ_h h_eval_eq h_fail_eq h_agree hwfb hwfv h_wf_def h_congr hwfvar h_dx
  have h_tgt_x_def : (ρ_h.store x).isSome = true := h_dx x (List.mem_singleton.mpr rfl)
  refine ⟨?_, ?_⟩
  · -- TERMINAL: peel the cons, head `init` terminates, tail `[assert]` terminates (pass).
    intro ρ_s' h_run
    match h_run with
    | .step _ _ _ .step_stmts_cons hrest =>
      obtain ⟨ρ_mid, h_init_T, h_after⟩ := seq_reaches_terminal P (EvalCmd P) extendFactory hrest
      -- invert the head `init` step.
      have h_init_step : StepStmt P (EvalCmd P) extendFactory
          (.stmt (.cmd (.init x ty (.det e) md)) ρ_s) (.terminal ρ_mid) := by
        match h_init_T with
        | .step _ _ _ (.step_cmd hev) hr =>
          match hr with
          | .refl _ => exact .step_cmd hev
          | .step _ _ _ hd _ => exact nomatch hd
      -- transport `init → set`.
      obtain ⟨ρ_h_mid, h_set_step, h_agree_mid, h_fail_mid, h_eval_mid, h_xdef_mid, _⟩ :=
        initToSetStepSA x ty e md ρ_s ρ_mid ρ_h
          h_eval_eq h_fail_eq h_agree h_wf_def h_tgt_x_def h_init_step
      -- `init` preserves `eval`.
      have h_eval_mid_src : ρ_mid.factory = ρ_s.factory := by
        cases h_init_step with
        | step_cmd hev => cases hev with
          | eval_init _ _ _ => rfl
      -- now the tail `[assert Q]` from `ρ_mid` (src) / `ρ_h_mid` (tgt).
      -- invert the source assert run to `.terminal ρ_s'`.
      match h_after with
      | .step _ _ _ .step_stmts_cons h_tail =>
        obtain ⟨ρ_a, h_assert_T, h_nil⟩ := seq_reaches_terminal P (EvalCmd P) extendFactory h_tail
        have h_assert_step : StepStmt P (EvalCmd P) extendFactory
            (.stmt (.cmd (.assert lbl Q md)) ρ_mid) (.terminal ρ_a) := by
          match h_assert_T with
          | .step _ _ _ (.step_cmd hev) hr =>
            match hr with
            | .refl _ => exact .step_cmd hev
            | .step _ _ _ hd _ => exact nomatch hd
        have h_ρs'_eq : ρ_s' = ρ_a := by
          match h_nil with
          | .step _ _ _ .step_stmts_nil hr =>
            match hr with
            | .refl _ => rfl
            | .step _ _ _ hd _ => exact nomatch hd
        subst h_ρs'_eq
        -- a terminating assert can only have PASSED (fail would set hasFailure, still terminal,
        -- but the store is unchanged and we replay on the hoist side identically).
        cases h_assert_step with
        | step_cmd hev =>
          rename_i σ' haf
          cases hev with
          | eval_assert_pass htt hwfb_a =>
            -- source: ρ_a = ρ_mid with hasFailure := ρ_mid.hasFailure || false; store unchanged.
            -- hoist assert: predicate Q evaluates to tt too (stores agree on Q's source-defined
            -- vars).
            have h_eval_Q_h : P.eval ρ_h_mid.factory ρ_h_mid.store Q = .some HasBool.tt := by
              rw [h_eval_mid]
              exact (h_eval_mid_src ▸ h_wf_def) Q HasBool.tt ρ_mid.store ρ_h_mid.store
                (storeAgreement_supplies_mono_premise ρ_mid.store ρ_h_mid.store h_agree_mid) htt
            refine ⟨{ ρ_h_mid with hasFailure := ρ_h_mid.hasFailure || false }, ?_, ?_, ?_, ?_, ?_⟩
            · -- hoist run: stmts_cons → set step → stmts_cons → assert-pass step → nil.
              refine .step _ _ _ .step_stmts_cons ?_
              refine .step _ _ _ (.step_seq_inner h_set_step) ?_
              refine .step _ _ _ .step_seq_done ?_
              refine .step _ _ _ .step_stmts_cons ?_
              refine .step _ _ _ (.step_seq_inner (.step_cmd
                (.eval_assert_pass h_eval_Q_h (h_eval_mid ▸ hwfb_a)))) ?_
              exact .step _ _ _ .step_seq_done (.step _ _ _ .step_stmts_nil (.refl _))
            · -- StoreAgreement: assert leaves stores unchanged on both sides.
              show StoreAgreement ρ_mid.store ρ_h_mid.store; exact h_agree_mid
            · show (ρ_h_mid.hasFailure || false) = (ρ_mid.hasFailure || false); simp [h_fail_mid]
            · show ρ_h_mid.factory = ρ_mid.factory; exact h_eval_mid
            · intro z hz; rw [List.mem_singleton.mp hz]
              show (ρ_h_mid.store x).isSome = true; exact h_xdef_mid
          | eval_assert_fail hff hwfb_a =>
            -- source assert FAILED: ρ_a = ρ_mid with hasFailure := ρ_mid.hasFailure || true.
            -- The hoist assert fails the same way; the resulting config still terminal.
            have h_eval_Q_h : P.eval ρ_h_mid.factory ρ_h_mid.store Q = .some HasBool.ff := by
              rw [h_eval_mid]
              exact (h_eval_mid_src ▸ h_wf_def) Q HasBool.ff ρ_mid.store ρ_h_mid.store
                (storeAgreement_supplies_mono_premise ρ_mid.store ρ_h_mid.store h_agree_mid) hff
            refine ⟨{ ρ_h_mid with hasFailure := ρ_h_mid.hasFailure || true }, ?_, ?_, ?_, ?_, ?_⟩
            · refine .step _ _ _ .step_stmts_cons ?_
              refine .step _ _ _ (.step_seq_inner h_set_step) ?_
              refine .step _ _ _ .step_seq_done ?_
              refine .step _ _ _ .step_stmts_cons ?_
              refine .step _ _ _ (.step_seq_inner (.step_cmd
                (.eval_assert_fail h_eval_Q_h (h_eval_mid ▸ hwfb_a)))) ?_
              exact .step _ _ _ .step_seq_done (.step _ _ _ .step_stmts_nil (.refl _))
            · show StoreAgreement ρ_mid.store ρ_h_mid.store; exact h_agree_mid
            · show (ρ_h_mid.hasFailure || true) = (ρ_mid.hasFailure || true); simp [h_fail_mid]
            · show ρ_h_mid.factory = ρ_mid.factory; exact h_eval_mid
            · intro z hz; rw [List.mem_singleton.mp hz]
              show (ρ_h_mid.store x).isSome = true; exact h_xdef_mid
  · -- EXITING clause: vacuous, the body is two `.cmd`s, neither exits.
    intro l ρ_s' h_run
    exfalso
    match h_run with
    | .step _ _ _ .step_stmts_cons hrest =>
      rcases seq_reaches_exiting P (EvalCmd P) extendFactory hrest with
        h_init_exit | ⟨ρ₁, _, h_tail_exit⟩
      · match h_init_exit with
        | .step _ _ _ (.step_cmd _) hr =>
          match hr with
          | .step _ _ _ hd _ => exact nomatch hd
      · match h_tail_exit with
        | .step _ _ _ .step_stmts_cons h2 =>
          rcases seq_reaches_exiting P (EvalCmd P) extendFactory h2 with
            h_a_exit | ⟨ρ₂, _, h_nil_exit⟩
          · match h_a_exit with
            | .step _ _ _ (.step_cmd _) hr =>
              match hr with
              | .step _ _ _ hd _ => exact nomatch hd
          · match h_nil_exit with
            | .step _ _ _ .step_stmts_nil hr =>
              match hr with
              | .step _ _ _ hd _ => exact nomatch hd

/-- The same-name FAILING body sim for the canonical loop body at `D = [x]`: a
failing source `[init x := e, assert lbl Q md]` run is matched by a failing hoist
`[set x := e, assert lbl Q md]` run.  Since `init`/`set` never set `hasFailure`,
the failure is the `assert Q` (the head `init` must have terminated first); the
hoist `set` re-establishes `StoreAgreement` so the hoist `assert Q` fails too. -/
public theorem samenameBodySimInitSetAssertFail {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps
    P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    {extendFactory : ExtendFactory P}
    (x : P.Ident) (ty : P.Ty) (e : P.Expr) (lbl : String) (Q : P.Expr) (md : MetaData P) :
    BodySimSumFailSA (extendFactory := extendFactory) [x]
      [.cmd (.init x ty (.det e) md), .cmd (.assert lbl Q md)]
      [.cmd (.set x (.det e) md), .cmd (.assert lbl Q md)] := by
  intro ρ_s ρ_h h_eval_eq h_fail_eq h_agree hwfb hwfv h_wf_def h_congr hwfvar h_dx d h_run hd
  have h_tgt_x_def : (ρ_h.store x).isSome = true := h_dx x (List.mem_singleton.mpr rfl)
  -- If the source ALREADY fails at entry, the hoist body's start env fails too (h_fail_eq).
  by_cases h_s_entry : ρ_s.hasFailure = true
  · exact ⟨.stmts [.cmd (.set x (.det e) md), .cmd (.assert lbl Q md)] ρ_h, .refl _,
      by simpa [Config.getEnv] using (h_fail_eq ▸ h_s_entry)⟩
  -- Otherwise, peel the cons.  The head `init` never fails, so the failure is in the tail.
  rcases stmts_cons_reaches_failing' P extendFactory (reflTrans_to_T h_run) hd with
    hA | ⟨ρ_mid, d_rest, h_init_term, h_rest_run, hd_rest⟩
  · -- HEAD `init x := e` reaches a failing config: `init` keeps `hasFailure`, so ρ_s fails.
    exfalso
    obtain ⟨d_head, h_head_run, hd_head⟩ := hA
    have h_ρs_fail : ρ_s.hasFailure = true := by
      cases h_head_run with
      | refl => simpa [Config.getEnv] using hd_head
      | step _ _ _ h1 hr1 =>
        cases h1 with
        | step_cmd hev =>
          -- the `init` step yields `.terminal {hasFailure := ρ_s.hasFailure || false}`;
          -- the residual run cannot step further from a terminal config.
          cases hr1 with
          | refl =>
            -- for `.det` rhs only `eval_init` applies; its failure flag is `false`.
            cases hev with
            | eval_init _ _ _ => simpa [Config.getEnv, Bool.or_false] using hd_head
          | step _ _ _ hd' _ => exact nomatch hd'
    exact h_s_entry h_ρs_fail
  · -- HEAD `init` terminated at ρ_mid; transport to a hoist `set` reaching ρ_h_mid.
    have h_init_step : StepStmt P (EvalCmd P) extendFactory
        (.stmt (.cmd (.init x ty (.det e) md)) ρ_s) (.terminal ρ_mid) := by
      match h_init_term with
      | .step _ _ _ (.step_cmd hev) hr =>
        match hr with
        | .refl _ => exact .step_cmd hev
        | .step _ _ _ hd' _ => exact nomatch hd'
    obtain ⟨ρ_h_mid, h_set_step, h_agree_mid, h_fail_mid, h_eval_mid, h_xdef_mid, _⟩ :=
      initToSetStepSA x ty e md ρ_s ρ_mid ρ_h
        h_eval_eq h_fail_eq h_agree h_wf_def h_tgt_x_def h_init_step
    -- the hoist `set` reaches `ρ_h_mid` (terminal); chain its run prefix.
    have h_set_prefix : StepStmtStar P (EvalCmd P) extendFactory
        (.stmts [.cmd (.set x (.det e) md), .cmd (.assert lbl Q md)] ρ_h)
        (.stmts [.cmd (.assert lbl Q md)] ρ_h_mid) := by
      refine .step _ _ _ .step_stmts_cons ?_
      refine .step _ _ _ (.step_seq_inner h_set_step) ?_
      exact .step _ _ _ .step_seq_done (.refl _)
    -- the tail `[assert Q]` run reaches a failing config from ρ_mid.
    obtain ⟨d_a, h_assert_run, hd_a_fail, _⟩ :=
      stmts_singleton_reaches_failing' P extendFactory (reflTrans_to_T h_rest_run) hd_rest
    -- If ρ_mid already fails, so does ρ_h_mid; answer at the post-set config.
    by_cases h_mid_entry : ρ_mid.hasFailure = true
    · exact ⟨.stmts [.cmd (.assert lbl Q md)] ρ_h_mid, h_set_prefix,
        by simpa [Config.getEnv] using (h_fail_mid ▸ h_mid_entry)⟩
    · -- ρ_mid does not fail at the assert entry, so the assert itself FAILS.
      have h_assert_fail : P.eval ρ_mid.factory ρ_mid.store Q = .some HasBool.ff
          ∧ WellFormedSemanticEvalBool ρ_mid.factory := by
        cases h_assert_run with
        | refl => exact absurd (by simpa [Config.getEnv] using hd_a_fail) h_mid_entry
        | step _ _ _ h1 hr1 =>
          cases h1 with
          | step_cmd hev =>
            cases hev with
            | eval_assert_pass htt hwfb_a =>
              exfalso
              cases hr1 with
              | refl => exact h_mid_entry (by simpa [Config.getEnv, Bool.or_false] using hd_a_fail)
              | step _ _ _ hd' _ => exact nomatch hd'
            | eval_assert_fail hff hwfb_a => exact ⟨hff, hwfb_a⟩
      obtain ⟨hff, hwfb_a⟩ := h_assert_fail
      -- the hoist assert at ρ_h_mid fails too: Q's vars are source-defined (assert-fail ⇒ defined),
      -- stores agree there, so the hoist eval gives `ff` as well.  `init` preserves `eval`.
      have h_eval_mid_src : ρ_mid.factory = ρ_s.factory := by
        cases h_init_step with
        | step_cmd hev => cases hev with
          | eval_init _ _ _ => rfl
      have h_eval_Q_h : P.eval ρ_h_mid.factory ρ_h_mid.store Q = .some HasBool.ff := by
        rw [h_eval_mid]
        exact (h_eval_mid_src ▸ h_wf_def) Q HasBool.ff ρ_mid.store ρ_h_mid.store
          (storeAgreement_supplies_mono_premise ρ_mid.store ρ_h_mid.store h_agree_mid) hff
      refine ⟨.stmts [] { ρ_h_mid with hasFailure := ρ_h_mid.hasFailure || true }, ?_, ?_⟩
      · refine ReflTrans_Transitive _ _ _ _ h_set_prefix ?_
        refine .step _ _ _ .step_stmts_cons ?_
        refine .step _ _ _ (.step_seq_inner (.step_cmd
          (.eval_assert_fail h_eval_Q_h (h_eval_mid ▸ hwfb_a)))) ?_
        exact .step _ _ _ .step_seq_done (.refl _)
      · simp [Config.getEnv]

/-- **Coverage of the canonical asymmetric-failing example.**  The same-name
failing driver `samenameLoopDetSA_F` applies, NON-VACUOUSLY, to the source loop
`loop g { init x := e; assert lbl Q }` vs the hoisted loop body
`{ set x := e; assert lbl Q }` at `D = [x]`: a source run reaching a failing config
is matched by a hoist run reaching a failing config, given the prelude has defined
`x` once before the loop (`h_tgt_x_def`).  This discharges the failing-driver's two
body slots from the build-verified witnesses `samenameBodySimInitSetAssert`
(terminal/exiting) and `samenameBodySimInitSetAssertFail` (failing) — establishing
that the asymmetric `D = [x]` invariant (target `x` persistently defined, source `x`
possibly `none`) is satisfiable on the canonical example with no hidden side
condition. -/
public theorem samenameLoopDetSA_F_initSetAssert {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps
    P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {x : P.Ident} {ty : P.Ty} {e : P.Expr} {lbl : String} {Q : P.Expr}
    {md md_s md_h : MetaData P}
    {ρ_src ρ_hoist : Env P} {a' : Config P (Cmd P)}
    (h_agree : StoreAgreement ρ_src.store ρ_hoist.store)
    (h_eval : ρ_hoist.factory = ρ_src.factory) (h_hf : ρ_hoist.hasFailure = ρ_src.hasFailure)
    (hwfb : WellFormedSemanticEvalBool ρ_src.factory) (hwfv : WellFormedSemanticEvalVal
        ρ_src.factory)
    (hwf_def : WellFormedSemanticEvalMono ρ_src.factory)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ_src.factory)
    (hwf_var : WellFormedSemanticEvalVar ρ_src.factory)
    (h_tgt_x_def : (ρ_hoist.store x).isSome = true)
    (h_run : StepStmtStar P (EvalCmd P) extendFactory
        (.stmt (.loop (.det g) none []
          [.cmd (.init x ty (.det e) md), .cmd (.assert lbl Q md)] md_s) ρ_src) a')
    (h_a'_fail : a'.getEnv.hasFailure = true) :
    ∃ d, StepStmtStar P (EvalCmd P) extendFactory
        (.stmt (.loop (.det g) none []
          [.cmd (.set x (.det e) md), .cmd (.assert lbl Q md)] md_h) ρ_hoist) d
      ∧ d.getEnv.hasFailure = true :=
  samenameLoopDetSA_F (D := [x])
    (samenameBodySimInitSetAssert x ty e lbl Q md)
    (samenameBodySimInitSetAssertFail x ty e lbl Q md)
    (by simp [Block.noFuncDecl, Stmt.noFuncDecl])
    h_agree h_eval h_hf hwfb hwfv hwf_def hwf_congr hwf_var
    (by intro z hz; rw [List.mem_singleton.mp hz]; exact h_tgt_x_def) h_run h_a'_fail

/-! ## End-to-end same-name loop transport (driver ∘ minimal body sim).

The make-or-break composition for the same-name hoist: a body-local `init y` loop
is simulated by the prelude-init + body-`set y` loop.  The per-step
(`initToSetStepSA`), the body simulation (`samenameBodySimInitSet`), and the driver
assembly (`samenameLoopDetSA_TE` / `_E`) all close on `StoreAgreement`.  These
witness that the StoreAgreement path is non-vacuous on the minimal non-trivial body
the hoist actually produces. -/

/-- End-to-end TERMINAL same-name loop transport: source loop with body
`[init y := rhs]` simulated by hoist loop with body `[set y := rhs]`, given the
prelude defined `y` once before the loop (`h_tgt_y_def`). -/
public theorem samenameLoopDetSA_TE_initSet {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {y : P.Ident} {ty : P.Ty} {rhs : P.Expr} {md md_s md_h : MetaData P}
    {ρ_src ρ_hoist ρ_post : Env P}
    (h_agree : StoreAgreement ρ_src.store ρ_hoist.store)
    (h_eval : ρ_hoist.factory = ρ_src.factory) (h_hf : ρ_hoist.hasFailure = ρ_src.hasFailure)
    (hwfb : WellFormedSemanticEvalBool ρ_src.factory) (hwfv : WellFormedSemanticEvalVal
        ρ_src.factory)
    (hwf_def : WellFormedSemanticEvalMono ρ_src.factory)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ_src.factory)
    (hwf_var : WellFormedSemanticEvalVar ρ_src.factory)
    (h_tgt_y_def : (ρ_hoist.store y).isSome = true)
    (h_run : StepStmtStar P (EvalCmd P) extendFactory
        (.stmt (.loop (.det g) none []
          [.cmd (.init y ty (.det rhs) md)] md_s) ρ_src) (.terminal ρ_post)) :
    ∃ ρ_post_h : Env P,
      StepStmtStar P (EvalCmd P) extendFactory
        (.stmt (.loop (.det g) none []
          [.cmd (.set y (.det rhs) md)] md_h) ρ_hoist) (.terminal ρ_post_h) ∧
      StoreAgreement ρ_post.store ρ_post_h.store ∧
      ρ_post_h.hasFailure = ρ_post.hasFailure ∧ ρ_post_h.factory = ρ_post.factory ∧
      (ρ_post_h.store y).isSome = true := by
  obtain ⟨ρ_post_h, h_run_h, h_agree', h_hf', h_eval', h_def'⟩ :=
    samenameLoopDetSA_TE (D := [y])
      (samenameBodySimInitSet y ty rhs md)
      (by simp [Block.noFuncDecl, Stmt.noFuncDecl])
      h_agree h_eval h_hf hwfb hwfv hwf_def hwf_congr hwf_var
      (by intro z hz; rw [List.mem_singleton.mp hz]; exact h_tgt_y_def) h_run
  exact ⟨ρ_post_h, h_run_h, h_agree', h_hf', h_eval', h_def' y (List.mem_singleton.mpr rfl)⟩

end LoopInitHoistLoopDriver

namespace LoopInitHoistProducerProps

/-!
# Loop-init hoist producer: same-name body-simulation output facts.

The same-name loop-init hoist (`Block.liftInitsInLoopBody`) lifts each body-local
`init y := e` to a same-name prelude havoc `init y := *` and rewrites the body's
`init y` to `set y` — no fresh name and no rename.  This namespace proves the
pass-output facts the `.loop` arm of the hoist correctness proof consumes: the
`hoistP_*`/`liftP_*` shape-preservation lemmas and the same-name `StoreAgreement`
StepB provider (`bodySimSA_*`) that assembles a body simulation over the lifted body.
-/

/-! ## `loopBodyNoInits` peel helpers. -/

theorem initfree_loop_noinits {P : PureExpr}
    {g : ExprOrNondet P} {body : List (Stmt P (Cmd P))} {md : MetaData P}
    (h : Stmt.loopBodyNoInits (.loop g none [] body md) = true) :
    Block.noInitsAnywhere body = true ∧ Block.loopBodyNoInits body = true := by
  simp only [Stmt.loopBodyNoInits, Bool.and_eq_true, List.isEmpty_iff] at h
  exact ⟨Block.noInitsAnywhere_of_initVars_nil body h.1, h.2⟩


/-! ## The transport-expressible structural fragment.

The fragment the hoist body simulation covers: `.det`-rhs `init`, `.nondet`-rhs
`init`, `.det`-rhs `set`, `.nondet`-rhs `set`, `assert`/`assume`/`cover`,
`.block`, `.det`-guard `.ite`, `.nondet`-guard `.ite`, `.typeDecl`, an `.exit`,
and a measure-free, invariant-free, `.det`-guard nested `.loop`.  It excludes a
measured / invariant-bearing / `.nondet`-guard `.loop` and a `.funcDecl`.

`Stmt.transportShape`/`Block.transportShape` (defined in `Strata.DL.Imperative.Stmt`,
alongside `simpleShape`) are the Bool walkers that assert a body lies in this
fragment.  Via `Stmt/Block.transportShape_of_arm_preconds` (proved upstream in
`StmtProps`), `transportShape` FOLLOWS FROM the genuine `.loop` arm Bool
preconditions ALONE (`containsNondetLoop = false`, `noFuncDecl = true`,
`loopHasNoInvariants = true`, `noMeasureLoops = true`).  An `.exit` is admitted, so
a `.block` whose inner body breaks (and the loop early-exit pattern) is handled by
the banked exiting arms — no `noExit` residual is needed. -/

/-! # Same-name StepB provider on `StoreAgreement`.

The same-name loop-init hoist (`Block.liftInitsInLoopBody`) lifts each body-local
`init y := e` to a SAME-name prelude havoc `init y := *` and rewrites the body's
`init y` to `set y` — no fresh name, no rename.  So the source body `body₁` and the
hoist residual `(Block.liftInitsInLoopBody body₁).2` share every name, and the
relation is plain `StoreAgreement` (source-on-left) plus a definedness invariant
`D` (the prelude-defined slots, which the prelude keeps defined across iterations).

This section is the `StoreAgreement`-based StepB provider vocabulary:
a per-statement same-name simulation `StmtSimSA`, the empty/cons body sequencers
(`bodySimSA_nil` / `bodySimSA_cons`), the per-arm producers (init→set det/nondet
via the driver's `initToSetStepSA`; identity `.cmd` via `cmd_replay_agreement_storeAgree`;
`.block` / `.ite` / nested-`.loop` via `StoreAgreement.of_projectStore_parents` and the
same-name loop drivers `samenameLoopDetSA_TE` / `_E`).  The structural producer
that assembles a `BodySimSumSA` (paired with its failing `BodySimSumFailSA`) over
the whole lifted body is `bodySimBothSA_of_lift`, defined once the failing
per-statement sims are in scope.  `D`-definedness is preserved uniformly because no
`EvalCmd` step ever undefines a slot (`Config.varsDefined_star`). -/

open LoopInitHoistLoopDriver (BodySimSumSA initToSetStepSA samenameLoopDetSA_TE samenameLoopDetSA_E
  BodyDualUndefSA dualUndefLoopDetSA_TE dualUndefLoopDetSA_E
  BodySimSumFailSA samenameLoopDetSA_F BodyDualUndefFailSA dualUndefLoopDetSA_F_fuel)

/-! ## Per-statement same-name sim with the D-definedness invariant.

A `StmtSimSA D s s'` is the single-statement (eval-carrying) terminal-OR-exiting
StoreAgreement simulation, the head shape `bodySimSA_cons` stitches. -/
private def StmtSimSA [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    (D : List P.Ident) (s s' : Stmt P (Cmd P)) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    ρ_h.factory = ρ_s.factory → ρ_h.hasFailure = ρ_s.hasFailure →
    StoreAgreement ρ_s.store ρ_h.store →
    WellFormedSemanticEvalBool ρ_s.factory → WellFormedSemanticEvalVal ρ_s.factory →
    WellFormedSemanticEvalMono ρ_s.factory → WellFormedSemanticEvalExprCongr ρ_s.factory →
    WellFormedSemanticEvalVar ρ_s.factory →
    (∀ y ∈ D, (ρ_h.store y).isSome = true) →
    (∀ (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendFactory (.stmt s ρ_s) (.terminal ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendFactory (.stmt s' ρ_h) (.terminal ρ_h') ∧
        StoreAgreement ρ_s'.store ρ_h'.store ∧
        ρ_h'.hasFailure = ρ_s'.hasFailure ∧ ρ_h'.factory = ρ_s'.factory ∧
        (∀ y ∈ D, (ρ_h'.store y).isSome = true))
    ∧
    (∀ (l : String) (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendFactory (.stmt s ρ_s) (.exiting l ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendFactory (.stmt s' ρ_h) (.exiting l ρ_h') ∧
        StoreAgreement ρ_s'.store ρ_h'.store ∧
        ρ_h'.hasFailure = ρ_s'.hasFailure ∧ ρ_h'.factory = ρ_s'.factory ∧
        (∀ y ∈ D, (ρ_h'.store y).isSome = true))

/-- The empty body is a `BodySimSumSA`. -/
theorem bodySimSA_nil {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    (D : List P.Ident) :
    BodySimSumSA (extendFactory := extendFactory) D [] [] := by
  intro ρ_s ρ_h h_eval h_hf h_agree _ _ _ _ _ h_def
  refine ⟨?_, ?_⟩
  · intro ρ_s' h_run
    have h_eq : ρ_s' = ρ_s := by
      cases h_run with
      | step _ _ _ h1 hr1 =>
        cases h1
        cases hr1 with
        | refl => rfl
        | step _ _ _ hd _ => exact nomatch hd
    subst h_eq
    exact ⟨ρ_h, ReflTrans.step _ _ _ StepStmt.step_stmts_nil (ReflTrans.refl _),
      h_agree, h_hf, h_eval, h_def⟩
  · intro l ρ_s' h_run
    exfalso
    cases h_run with
    | step _ _ _ h1 hr1 =>
      cases h1
      cases hr1 with
      | step _ _ _ hd _ => exact nomatch hd

/-- A head `StmtSimSA` (with source `noFuncDecl` to transport eval-wfness to the
mid env) and tail `BodySimSumSA` compose to a cons `BodySimSumSA`. -/
private theorem bodySimSA_cons {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {D : List P.Ident} {s s' : Stmt P (Cmd P)} {rest rest' : List (Stmt P (Cmd P))}
    (h_nofd_s : Stmt.noFuncDecl s = true)
    (hhead : StmtSimSA (extendFactory := extendFactory) D s s')
    (htail : BodySimSumSA (extendFactory := extendFactory) D rest rest') :
    BodySimSumSA (extendFactory := extendFactory) D (s :: rest) (s' :: rest') := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def
  refine ⟨?_, ?_⟩
  · intro ρ_s' h_run
    obtain ⟨ρ_mid, h_head_run, h_rest_run⟩ :=
      stmts_cons_terminal_inv (extendFactory := extendFactory) h_run
    obtain ⟨ρ_h_mid, h_head_h_run, h_agree_mid, h_hf_mid, h_eval_mid, h_def_mid⟩ :=
      (hhead ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def).1 ρ_mid h_head_run
    -- recover wfness at ρ_mid via noFuncDecl eval-preservation.
    have h_eval_mid_src : ρ_mid.factory = ρ_s.factory :=
      smallStep_noFuncDecl_preserves_eval P (EvalCmd P) extendFactory s ρ_s ρ_mid h_nofd_s
          h_head_run
    obtain ⟨ρ_h', h_rest_h_run, h_agree', h_hf', h_eval', h_def'⟩ :=
      (htail ρ_mid ρ_h_mid h_eval_mid h_hf_mid h_agree_mid
        (by rw [h_eval_mid_src]; exact hwfb) (by rw [h_eval_mid_src]; exact hwfv)
        (by rw [h_eval_mid_src]; exact hwfd) (by rw [h_eval_mid_src]; exact hwfc)
        (by rw [h_eval_mid_src]; exact hwfvar) h_def_mid).1 ρ_s' h_rest_run
    refine ⟨ρ_h', ?_, h_agree', h_hf', h_eval', h_def'⟩
    exact ReflTrans_Transitive _ _ _ _
      (stmts_cons_step P (EvalCmd P) extendFactory s' rest' ρ_h ρ_h_mid h_head_h_run)
      h_rest_h_run
  · intro l ρ_s' h_run
    have h_seq : StepStmtStar P (EvalCmd P) extendFactory
        (.seq (.stmt s ρ_s) rest) (.exiting l ρ_s') := by
      cases h_run with
      | step _ _ _ h1 hr1 => cases h1; exact hr1
    rcases seq_reaches_exiting P (EvalCmd P) extendFactory h_seq with
      h_head_exit | ⟨ρ_mid, h_head_term, h_tail_exit⟩
    · obtain ⟨ρ_h', h_head_h_exit, h_agree', h_hf', h_eval', h_def'⟩ :=
        (hhead ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def).2 l ρ_s' h_head_exit
      refine ⟨ρ_h', ?_, h_agree', h_hf', h_eval', h_def'⟩
      refine ReflTrans.step _ _ _ StepStmt.step_stmts_cons ?_
      refine ReflTrans_Transitive _ _ _ _
        (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_head_h_exit) ?_
      exact ReflTrans.step _ _ _ StepStmt.step_seq_exit (ReflTrans.refl _)
    · obtain ⟨ρ_h_mid, h_head_h_run, h_agree_mid, h_hf_mid, h_eval_mid, h_def_mid⟩ :=
        (hhead ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def).1 ρ_mid h_head_term
      have h_eval_mid_src : ρ_mid.factory = ρ_s.factory :=
        smallStep_noFuncDecl_preserves_eval P (EvalCmd P) extendFactory s ρ_s ρ_mid h_nofd_s
            h_head_term
      obtain ⟨ρ_h', h_tail_h_exit, h_agree', h_hf', h_eval', h_def'⟩ :=
        (htail ρ_mid ρ_h_mid h_eval_mid h_hf_mid h_agree_mid
          (by rw [h_eval_mid_src]; exact hwfb) (by rw [h_eval_mid_src]; exact hwfv)
          (by rw [h_eval_mid_src]; exact hwfd) (by rw [h_eval_mid_src]; exact hwfc)
          (by rw [h_eval_mid_src]; exact hwfvar) h_def_mid).2 l ρ_s' h_tail_exit
      refine ⟨ρ_h', ?_, h_agree', h_hf', h_eval', h_def'⟩
      exact ReflTrans_Transitive _ _ _ _
        (stmts_cons_step P (EvalCmd P) extendFactory s' rest' ρ_h ρ_h_mid h_head_h_run)
        h_tail_h_exit

/-! ## The init→set arm: `StmtSimSA D (.cmd (.init y ty (.det e) md)) (.cmd (.set y (.det e) md))`.

Requires `y ∈ D` (the prelude defined it). A `.cmd` never reaches `.exiting`. -/
private theorem initSet_stmtSimSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    {extendFactory : ExtendFactory P}
    {D : List P.Ident} (y : P.Ident) (ty : P.Ty) (e : P.Expr) (md : MetaData P)
    (h_y_D : y ∈ D) :
    StmtSimSA (extendFactory := extendFactory) D
      (.cmd (.init y ty (.det e) md)) (.cmd (.set y (.det e) md)) := by
  intro ρ_s ρ_h h_eval h_hf h_agree _ _ hwfd _ _ h_def
  have h_tgt_y_def : (ρ_h.store y).isSome = true := h_def y h_y_D
  refine ⟨?_, ?_⟩
  · intro ρ_s' h_run
    -- a single `.cmd` runs `step_cmd` to `.terminal`, then is stuck.
    have h_cmd_step : StepStmt P (EvalCmd P) extendFactory
        (.stmt (.cmd (.init y ty (.det e) md)) ρ_s) (.terminal ρ_s') := by
      cases h_run with
      | step _ _ _ h1 hr1 =>
        cases h1 with
        | step_cmd hev =>
          cases hr1 with
          | refl => exact .step_cmd hev
          | step _ _ _ hd _ => exact nomatch hd
    obtain ⟨ρ_tgt', h_set_step, h_agree', h_fail', h_eval', h_ydef', h_oth'⟩ :=
      initToSetStepSA y ty e md ρ_s ρ_s' ρ_h h_eval h_hf h_agree hwfd h_tgt_y_def h_cmd_step
    refine ⟨ρ_tgt', ReflTrans.step _ _ _ h_set_step (ReflTrans.refl _),
      h_agree', h_fail', h_eval', ?_⟩
    intro z hz
    by_cases hzy : z = y
    · subst hzy; exact h_ydef'
    · rw [h_oth' z (fun h => hzy h.symm)]; exact h_def z hz
  · intro l ρ_s' h_run
    exfalso
    cases h_run with
    | step _ _ _ h1 hr1 =>
      cases h1
      cases hr1 with
      | step _ _ _ hd _ => exact nomatch hd

/-! ## The nondet init→set arm. -/

/-- A `.nondet`-rhs source `init y` step is simulated by a hoist `set y .nondet`
step picking the SAME arbitrary value, maintaining StoreAgreement. -/
theorem initToSetStepSA_nondet {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    {extendFactory : ExtendFactory P}
    (y : P.Ident) (ty : P.Ty) (md : MetaData P)
    (ρ_src ρ_src' ρ_tgt : Env P)
    (h_eval_eq : ρ_tgt.factory = ρ_src.factory)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree : StoreAgreement ρ_src.store ρ_tgt.store)
    (h_tgt_y_def : (ρ_tgt.store y).isSome = true)
    (h_step : StepStmt P (EvalCmd P) extendFactory
        (.stmt (.cmd (.init y ty .nondet md)) ρ_src) (.terminal ρ_src')) :
    ∃ ρ_tgt', StepStmt P (EvalCmd P) extendFactory
          (.stmt (.cmd (.set y .nondet md)) ρ_tgt) (.terminal ρ_tgt')
        ∧ StoreAgreement ρ_src'.store ρ_tgt'.store
        ∧ ρ_tgt'.hasFailure = ρ_src'.hasFailure
        ∧ ρ_tgt'.factory = ρ_src'.factory
        ∧ (ρ_tgt'.store y).isSome = true
        ∧ (∀ z, y ≠ z → ρ_tgt'.store z = ρ_tgt.store z) := by
  cases h_step with
  | step_cmd h_eval =>
    rename_i σ' haf
    cases h_eval with
    | eval_init_unconstrained hinit hval hwfvar =>
      rename_i v
      cases hinit with
      | init h_yn h_yv h_other =>
        obtain ⟨v', h_tgt_y_old⟩ : ∃ v', ρ_tgt.store y = some v' := by
          cases h : ρ_tgt.store y with
          | none => rw [h] at h_tgt_y_def; simp at h_tgt_y_def
          | some v' => exact ⟨v', rfl⟩
        let σ_tgt' : SemanticStore P := fun z => if z = y then some v else ρ_tgt.store z
        have h_tgt_y : σ_tgt' y = some v := by show (if y = y then _ else _) = _; simp
        have h_tgt_oth : ∀ z, y ≠ z → σ_tgt' z = ρ_tgt.store z := by
          intro z hyz; show (if z = y then _ else _) = _; rw [if_neg (fun h => hyz h.symm)]
        refine ⟨{ ρ_tgt with store := σ_tgt', hasFailure := ρ_tgt.hasFailure || false },
          .step_cmd (EvalCmd.eval_set_nondet
            (UpdateState.update h_tgt_y_old h_tgt_y h_tgt_oth)
            (h_eval_eq ▸ hval)
            (h_eval_eq ▸ hwfvar)),
          ?_, ?_, ?_, ?_, ?_⟩
        · intro z h_def_z
          show σ' z = σ_tgt' z
          have h_z_some : (σ' z).isSome = true := h_def_z z (List.mem_singleton.mpr rfl)
          by_cases hzy : z = y
          · subst hzy; rw [h_yv, h_tgt_y]
          · rw [h_other z (fun h => hzy h.symm)]
            rw [h_other z (fun h => hzy h.symm)] at h_z_some
            rw [h_tgt_oth z (fun h => hzy h.symm)]
            exact h_agree z (fun w hw => by simpa [List.mem_singleton.mp hw] using h_z_some)
        · show (ρ_tgt.hasFailure || false) = (ρ_src.hasFailure || false); simp [h_fail_eq]
        · exact h_eval_eq
        · show (σ_tgt' y).isSome = true; rw [h_tgt_y]; rfl
        · exact h_tgt_oth

/-- The hoist rewrite of a nondet `init` into a `set` is a store-agreeing simulation:
`init y ty .nondet` on the source is matched by `set y .nondet` on the hoisted side under
`StmtSimSA D`, provided `y` is already in the tracked defined set `D`. -/
private theorem initSet_nondet_stmtSimSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    {extendFactory : ExtendFactory P}
    {D : List P.Ident} (y : P.Ident) (ty : P.Ty) (md : MetaData P)
    (h_y_D : y ∈ D) :
    StmtSimSA (extendFactory := extendFactory) D
      (.cmd (.init y ty .nondet md)) (.cmd (.set y .nondet md)) := by
  intro ρ_s ρ_h h_eval h_hf h_agree _ _ _ _ _ h_def
  have h_tgt_y_def : (ρ_h.store y).isSome = true := h_def y h_y_D
  refine ⟨?_, ?_⟩
  · intro ρ_s' h_run
    have h_cmd_step : StepStmt P (EvalCmd P) extendFactory
        (.stmt (.cmd (.init y ty .nondet md)) ρ_s) (.terminal ρ_s') := by
      cases h_run with
      | step _ _ _ h1 hr1 =>
        cases h1 with
        | step_cmd hev =>
          cases hr1 with
          | refl => exact .step_cmd hev
          | step _ _ _ hd _ => exact nomatch hd
    obtain ⟨ρ_tgt', h_set_step, h_agree', h_fail', h_eval', h_ydef', h_oth'⟩ :=
      initToSetStepSA_nondet y ty md ρ_s ρ_s' ρ_h h_eval h_hf h_agree h_tgt_y_def h_cmd_step
    refine ⟨ρ_tgt', ReflTrans.step _ _ _ h_set_step (ReflTrans.refl _),
      h_agree', h_fail', h_eval', ?_⟩
    intro z hz
    by_cases hzy : z = y
    · subst hzy; exact h_ydef'
    · rw [h_oth' z (fun h => hzy h.symm)]; exact h_def z hz
  · intro l ρ_s' h_run
    exfalso
    cases h_run with
    | step _ _ _ h1 hr1 =>
      cases h1
      cases hr1 with
      | step _ _ _ hd _ => exact nomatch hd

/-! ## The identity `.cmd c` (non-init) arm. -/

/-- A non-init `.cmd c` simulates itself under StoreAgreement: `cmd_replay`
delivers the StoreAgreement/eval/hf, and `D`-definedness is preserved uniformly
because no `EvalCmd` step undefines a slot (`Config.varsDefined_star`). The
`h_no_init` premise (`Cmd.definedVars c = []`) discharges the cmd-replay's
init-undefinedness side-condition vacuously. -/
private theorem cmd_id_stmtSimSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    {extendFactory : ExtendFactory P}
    {D : List P.Ident} (c : Cmd P)
    (h_no_init : Cmd.definedVars c = []) :
    StmtSimSA (extendFactory := extendFactory) D (.cmd c) (.cmd c) := by
  intro ρ_s ρ_h h_eval h_hf h_agree _ _ hwfd _ _ h_def
  refine ⟨?_, ?_⟩
  · intro ρ_s' h_run
    obtain ⟨ρ_h', h_h_run, h_agree', h_hf', h_eval'⟩ :=
      cmd_replay_agreement_storeAgree (extendFactory := extendFactory) c ρ_s ρ_s' ρ_h
        h_eval h_hf h_agree hwfd
        (by intro x hx; rw [h_no_init] at hx; exact absurd hx List.not_mem_nil) h_run
    refine ⟨ρ_h', h_h_run, h_agree', h_hf', h_eval', ?_⟩
    intro z hz
    exact Config.varsDefined_star (extendFactory := extendFactory) h_h_run
      (show Config.varDefined z (.stmt (.cmd c) ρ_h) from fun _ hw => hw ▸ h_def z hz) z rfl
  · intro l ρ_s' h_run
    exfalso
    cases h_run with
    | step _ _ _ h1 hr1 =>
      cases h1
      cases hr1 with
      | step _ _ _ hd _ => exact nomatch hd

/-! ## The `.block` arm. -/

private theorem block_stmtSimSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {D : List P.Ident} {lbl : String} {inner inner_h : List (Stmt P (Cmd P))} {md : MetaData P}
    (inner_sim : BodySimSumSA (extendFactory := extendFactory) D inner inner_h) :
    StmtSimSA (extendFactory := extendFactory) D (.block lbl inner md) (.block lbl inner_h md) := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def
  -- D-definedness survives the projection: parent-defined keys are kept.
  have proj_def : ∀ (ρ_inner : Env P), (∀ y ∈ D, (ρ_inner.store y).isSome = true) →
      ∀ y ∈ D, (projectStore ρ_h.store ρ_inner.store y).isSome = true := by
    intro ρ_inner h_def_inner y hy
    show ((if (ρ_h.store y).isSome then ρ_inner.store y else none)).isSome = true
    rw [if_pos (h_def y hy)]; exact h_def_inner y hy
  have peel_term : ∀ (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendFactory (.stmt (.block lbl inner md) ρ_s) (.terminal ρ_s') →
      StepStmtStar P (EvalCmd P) extendFactory
        (.block (.some lbl) ρ_s.store ρ_s.factory (.stmts inner ρ_s)) (.terminal ρ_s') := by
    intro ρ_s' h_run
    cases h_run with
    | step _ _ _ h1 hr1 => cases h1; exact hr1
  have peel_exit : ∀ (l : String) (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendFactory (.stmt (.block lbl inner md) ρ_s) (.exiting l ρ_s') →
      StepStmtStar P (EvalCmd P) extendFactory
        (.block (.some lbl) ρ_s.store ρ_s.factory (.stmts inner ρ_s)) (.exiting l ρ_s') := by
    intro l ρ_s' h_run
    cases h_run with
    | step _ _ _ h1 hr1 => cases h1; exact hr1
  refine ⟨?_, ?_⟩
  · intro ρ_s' h_run0
    have h_run := peel_term ρ_s' h_run0
    rcases block_some_reaches_terminal P (EvalCmd P) extendFactory h_run with
      ⟨ρ_inner, h_inner_term, h_eq⟩ | ⟨ρ_inner, h_inner_exit, h_eq⟩
    · obtain ⟨ρ_h_inner, h_inner_h_run, h_agree_inner, h_hf_inner, h_eval_inner, h_def_inner⟩ :=
        (inner_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def).1 ρ_inner
            h_inner_term
      refine ⟨{ ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store,
                               factory := ρ_h.factory }, ?_, ?_, ?_, ?_, ?_⟩
      · refine ReflTrans.step _ _ _ StepStmt.step_block ?_
        refine ReflTrans_Transitive _ _ _ _
          (block_inner_star P (EvalCmd P) extendFactory _ _ (some lbl) ρ_h.store ρ_h.factory
              h_inner_h_run) ?_
        exact ReflTrans.step _ _ _ StepStmt.step_block_done (ReflTrans.refl _)
      · subst h_eq; exact StoreAgreement.of_projectStore_parents h_agree h_agree_inner
      · subst h_eq; show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf_inner
      · subst h_eq; show ρ_h.factory = ρ_s.factory; exact h_eval
      · subst h_eq; exact proj_def ρ_h_inner h_def_inner
    · obtain ⟨ρ_h_inner, h_inner_h_run, h_agree_inner, h_hf_inner, h_eval_inner, h_def_inner⟩ :=
        (inner_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def).2 lbl ρ_inner
            h_inner_exit
      refine ⟨{ ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store,
                               factory := ρ_h.factory }, ?_, ?_, ?_, ?_, ?_⟩
      · refine ReflTrans.step _ _ _ StepStmt.step_block ?_
        refine ReflTrans_Transitive _ _ _ _
          (block_inner_star P (EvalCmd P) extendFactory _ _ (some lbl) ρ_h.store ρ_h.factory
              h_inner_h_run) ?_
        exact ReflTrans.step _ _ _ (StepStmt.step_block_exit_match rfl) (ReflTrans.refl _)
      · subst h_eq; exact StoreAgreement.of_projectStore_parents h_agree h_agree_inner
      · subst h_eq; show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf_inner
      · subst h_eq; show ρ_h.factory = ρ_s.factory; exact h_eval
      · subst h_eq; exact proj_def ρ_h_inner h_def_inner
  · intro l ρ_s' h_run0
    have h_run := peel_exit l ρ_s' h_run0
    obtain ⟨h_ne, ρ_inner, h_inner_exit, h_eq⟩ :=
      block_reaches_exiting_strong P (EvalCmd P) extendFactory h_run
    obtain ⟨ρ_h_inner, h_inner_h_run, h_agree_inner, h_hf_inner, h_eval_inner, h_def_inner⟩ :=
      (inner_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def).2 l ρ_inner
          h_inner_exit
    refine ⟨{ ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store,
                             factory := ρ_h.factory }, ?_, ?_, ?_, ?_, ?_⟩
    · refine ReflTrans.step _ _ _ StepStmt.step_block ?_
      refine ReflTrans_Transitive _ _ _ _
        (block_inner_star P (EvalCmd P) extendFactory _ _ (some lbl) ρ_h.store ρ_h.factory
            h_inner_h_run) ?_
      exact ReflTrans.step _ _ _ (StepStmt.step_block_exit_mismatch (fun h => h_ne (Option.some.inj
          h))) (ReflTrans.refl _)
    · subst h_eq; exact StoreAgreement.of_projectStore_parents h_agree h_agree_inner
    · subst h_eq; show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf_inner
    · subst h_eq; show ρ_h.factory = ρ_s.factory; exact h_eval
    · subst h_eq; exact proj_def ρ_h_inner h_def_inner

/-! ## The `.ite` arms (same guard, no rename). -/

private theorem ite_stmtSimSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {D : List P.Ident} {g : P.Expr} {tss_s tss_h ess_s ess_h : List (Stmt P (Cmd P))} {md : MetaData
        P}
    (then_sim : BodySimSumSA (extendFactory := extendFactory) D tss_s tss_h)
    (else_sim : BodySimSumSA (extendFactory := extendFactory) D ess_s ess_h) :
    StmtSimSA (extendFactory := extendFactory) D
      (.ite (.det g) tss_s ess_s md) (.ite (.det g) tss_h ess_h md) := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def
  -- transport the guard: source-defined reads pin the values, so hoist guard = source value.
  have guard_h : ∀ {bv : P.Expr}, P.eval ρ_s.factory ρ_s.store g = .some bv →
      P.eval ρ_h.factory ρ_h.store g = .some bv := by
    intro bv hg
    rw [h_eval]
    exact hwfd g bv ρ_s.store ρ_h.store
      (storeAgreement_supplies_mono_premise ρ_s.store ρ_h.store h_agree) hg
  -- projected D-definedness on the hoist side after the block cap.
  have proj_def_h : ∀ (ρ_h_inner : Env P), (∀ y ∈ D, (ρ_h_inner.store y).isSome = true) →
      ∀ y ∈ D, (projectStore ρ_h.store ρ_h_inner.store y).isSome = true := by
    intro ρ_h_inner h_def_inner y hy
    show ((if (ρ_h.store y).isSome then ρ_h_inner.store y else none)).isSome = true
    rw [if_pos (h_def y hy)]; exact h_def_inner y hy
  refine ⟨?_, ?_⟩
  · intro ρ_s' h_run
    -- Invert the source ite: it steps to a scoped `.block .none`; recover the guard + block run.
    match h_run with
    | .step _ _ _ h1 hr1 =>
      cases h1 with
      | step_ite_true hg hwf =>
        obtain ⟨ρ_inner, h_branch, h_eq, _⟩ :=
          blockT_none_reaches_terminal (extendFactory := extendFactory) (reflTrans_to_T hr1)
        obtain ⟨ρ_h_inner, h_branch_h, h_agree', h_hf', h_eval', h_def'⟩ :=
          (then_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def).1 ρ_inner
            (reflTransT_to_prop h_branch)
        subst h_eq
        refine ⟨{ ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store,
                                 factory := ρ_h.factory },
          ReflTrans.step _ _ _ (StepStmt.step_ite_true (guard_h hg) (h_eval ▸ hwf))
            (ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_h.store ρ_h.factory
                  h_branch_h)
              (.step _ _ _ .step_block_done (.refl _))),
          StoreAgreement.of_projectStore_parents h_agree h_agree', ?_, ?_, proj_def_h ρ_h_inner
              h_def'⟩
        · show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf'
        · show ρ_h.factory = ρ_s.factory; exact h_eval
      | step_ite_false hg hwf =>
        obtain ⟨ρ_inner, h_branch, h_eq, _⟩ :=
          blockT_none_reaches_terminal (extendFactory := extendFactory) (reflTrans_to_T hr1)
        obtain ⟨ρ_h_inner, h_branch_h, h_agree', h_hf', h_eval', h_def'⟩ :=
          (else_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def).1 ρ_inner
            (reflTransT_to_prop h_branch)
        subst h_eq
        refine ⟨{ ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store,
                                 factory := ρ_h.factory },
          ReflTrans.step _ _ _ (StepStmt.step_ite_false (guard_h hg) (h_eval ▸ hwf))
            (ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_h.store ρ_h.factory
                  h_branch_h)
              (.step _ _ _ .step_block_done (.refl _))),
          StoreAgreement.of_projectStore_parents h_agree h_agree', ?_, ?_, proj_def_h ρ_h_inner
              h_def'⟩
        · show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf'
        · show ρ_h.factory = ρ_s.factory; exact h_eval
  · intro l ρ_s' h_run
    match h_run with
    | .step _ _ _ h1 hr1 =>
      cases h1 with
      | step_ite_true hg hwf =>
        obtain ⟨ρ_inner, h_branch, h_eq, _⟩ :=
          blockT_none_reaches_exiting (extendFactory := extendFactory) (reflTrans_to_T hr1)
        obtain ⟨ρ_h_inner, h_branch_h, h_agree', h_hf', h_eval', h_def'⟩ :=
          (then_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def).2 l ρ_inner
            (reflTransT_to_prop h_branch)
        subst h_eq
        refine ⟨{ ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store,
                                 factory := ρ_h.factory },
          ReflTrans.step _ _ _ (StepStmt.step_ite_true (guard_h hg) (h_eval ▸ hwf))
            (ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_h.store ρ_h.factory
                  h_branch_h)
              (.step _ _ _ (.step_block_exit_mismatch (by simp)) (.refl _))),
          StoreAgreement.of_projectStore_parents h_agree h_agree', ?_, ?_, proj_def_h ρ_h_inner
              h_def'⟩
        · show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf'
        · show ρ_h.factory = ρ_s.factory; exact h_eval
      | step_ite_false hg hwf =>
        obtain ⟨ρ_inner, h_branch, h_eq, _⟩ :=
          blockT_none_reaches_exiting (extendFactory := extendFactory) (reflTrans_to_T hr1)
        obtain ⟨ρ_h_inner, h_branch_h, h_agree', h_hf', h_eval', h_def'⟩ :=
          (else_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def).2 l ρ_inner
            (reflTransT_to_prop h_branch)
        subst h_eq
        refine ⟨{ ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store,
                                 factory := ρ_h.factory },
          ReflTrans.step _ _ _ (StepStmt.step_ite_false (guard_h hg) (h_eval ▸ hwf))
            (ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_h.store ρ_h.factory
                  h_branch_h)
              (.step _ _ _ (.step_block_exit_mismatch (by simp)) (.refl _))),
          StoreAgreement.of_projectStore_parents h_agree h_agree', ?_, ?_, proj_def_h ρ_h_inner
              h_def'⟩
        · show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf'
        · show ρ_h.factory = ρ_s.factory; exact h_eval

/-- A nondeterministic `ite` simulates under `StmtSimSA D` given store-agreeing
simulations of each branch: from `then`/`else` body simulations, the whole
`.ite .nondet` statement's hoisted form matches the source. -/
private theorem ite_nondet_stmtSimSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {D : List P.Ident} {tss_s tss_h ess_s ess_h : List (Stmt P (Cmd P))} {md : MetaData P}
    (then_sim : BodySimSumSA (extendFactory := extendFactory) D tss_s tss_h)
    (else_sim : BodySimSumSA (extendFactory := extendFactory) D ess_s ess_h) :
    StmtSimSA (extendFactory := extendFactory) D
      (.ite .nondet tss_s ess_s md) (.ite .nondet tss_h ess_h md) := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def
  have proj_def_h : ∀ (ρ_h_inner : Env P), (∀ y ∈ D, (ρ_h_inner.store y).isSome = true) →
      ∀ y ∈ D, (projectStore ρ_h.store ρ_h_inner.store y).isSome = true := by
    intro ρ_h_inner h_def_inner y hy
    show ((if (ρ_h.store y).isSome then ρ_h_inner.store y else none)).isSome = true
    rw [if_pos (h_def y hy)]; exact h_def_inner y hy
  refine ⟨?_, ?_⟩
  · intro ρ_s' h_run
    match h_run with
    | .step _ _ _ h1 hr1 =>
      cases h1 with
      | step_ite_nondet_true =>
        obtain ⟨ρ_inner, h_branch, h_eq, _⟩ :=
          blockT_none_reaches_terminal (extendFactory := extendFactory) (reflTrans_to_T hr1)
        obtain ⟨ρ_h_inner, h_branch_h, h_agree', h_hf', h_eval', h_def'⟩ :=
          (then_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def).1 ρ_inner
            (reflTransT_to_prop h_branch)
        subst h_eq
        refine ⟨{ ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store,
                                 factory := ρ_h.factory },
          ReflTrans.step _ _ _ StepStmt.step_ite_nondet_true
            (ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_h.store ρ_h.factory
                  h_branch_h)
              (.step _ _ _ .step_block_done (.refl _))),
          StoreAgreement.of_projectStore_parents h_agree h_agree', ?_, ?_, proj_def_h ρ_h_inner
              h_def'⟩
        · show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf'
        · show ρ_h.factory = ρ_s.factory; exact h_eval
      | step_ite_nondet_false =>
        obtain ⟨ρ_inner, h_branch, h_eq, _⟩ :=
          blockT_none_reaches_terminal (extendFactory := extendFactory) (reflTrans_to_T hr1)
        obtain ⟨ρ_h_inner, h_branch_h, h_agree', h_hf', h_eval', h_def'⟩ :=
          (else_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def).1 ρ_inner
            (reflTransT_to_prop h_branch)
        subst h_eq
        refine ⟨{ ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store,
                                 factory := ρ_h.factory },
          ReflTrans.step _ _ _ StepStmt.step_ite_nondet_false
            (ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_h.store ρ_h.factory
                  h_branch_h)
              (.step _ _ _ .step_block_done (.refl _))),
          StoreAgreement.of_projectStore_parents h_agree h_agree', ?_, ?_, proj_def_h ρ_h_inner
              h_def'⟩
        · show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf'
        · show ρ_h.factory = ρ_s.factory; exact h_eval
  · intro l ρ_s' h_run
    match h_run with
    | .step _ _ _ h1 hr1 =>
      cases h1 with
      | step_ite_nondet_true =>
        obtain ⟨ρ_inner, h_branch, h_eq, _⟩ :=
          blockT_none_reaches_exiting (extendFactory := extendFactory) (reflTrans_to_T hr1)
        obtain ⟨ρ_h_inner, h_branch_h, h_agree', h_hf', h_eval', h_def'⟩ :=
          (then_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def).2 l ρ_inner
            (reflTransT_to_prop h_branch)
        subst h_eq
        refine ⟨{ ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store,
                                 factory := ρ_h.factory },
          ReflTrans.step _ _ _ StepStmt.step_ite_nondet_true
            (ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_h.store ρ_h.factory
                  h_branch_h)
              (.step _ _ _ (.step_block_exit_mismatch (by simp)) (.refl _))),
          StoreAgreement.of_projectStore_parents h_agree h_agree', ?_, ?_, proj_def_h ρ_h_inner
              h_def'⟩
        · show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf'
        · show ρ_h.factory = ρ_s.factory; exact h_eval
      | step_ite_nondet_false =>
        obtain ⟨ρ_inner, h_branch, h_eq, _⟩ :=
          blockT_none_reaches_exiting (extendFactory := extendFactory) (reflTrans_to_T hr1)
        obtain ⟨ρ_h_inner, h_branch_h, h_agree', h_hf', h_eval', h_def'⟩ :=
          (else_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def).2 l ρ_inner
            (reflTransT_to_prop h_branch)
        subst h_eq
        refine ⟨{ ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store,
                                 factory := ρ_h.factory },
          ReflTrans.step _ _ _ StepStmt.step_ite_nondet_false
            (ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_h.store ρ_h.factory
                  h_branch_h)
              (.step _ _ _ (.step_block_exit_mismatch (by simp)) (.refl _))),
          StoreAgreement.of_projectStore_parents h_agree h_agree', ?_, ?_, proj_def_h ρ_h_inner
              h_def'⟩
        · show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf'
        · show ρ_h.factory = ρ_s.factory; exact h_eval

/-! ## The nested `.loop` arm (verbatim body, same guard). -/

private theorem nestedLoop_stmtSimSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {D : List P.Ident} {g2 : P.Expr} {inner inner_h : List (Stmt P (Cmd P))} {md2_s md2_h : MetaData
        P}
    (inner_sim : BodySimSumSA (extendFactory := extendFactory) D inner inner_h)
    (h_nofd_src : Block.noFuncDecl inner = true) :
    StmtSimSA (extendFactory := extendFactory) D
      (.loop (.det g2) none [] inner md2_s)
      (.loop (.det g2) none [] inner_h md2_h) := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def
  refine ⟨?_, ?_⟩
  · intro ρ_s' h_run
    obtain ⟨ρ_h', h_loop_h_run, h_agree', h_hf', h_eval', h_def'⟩ :=
      samenameLoopDetSA_TE (D := D) inner_sim h_nofd_src
        h_agree h_eval h_hf hwfb hwfv hwfd hwfc hwfvar h_def h_run
    exact ⟨ρ_h', h_loop_h_run, h_agree', h_hf', h_eval', h_def'⟩
  · intro l ρ_s' h_run
    obtain ⟨ρ_h', h_loop_h_run, h_agree', h_hf', h_eval', h_def'⟩ :=
      samenameLoopDetSA_E (D := D) inner_sim h_nofd_src
        h_agree h_eval h_hf hwfb hwfv hwfd hwfc hwfvar h_def h_run
    exact ⟨ρ_h', h_loop_h_run, h_agree', h_hf', h_eval', h_def'⟩

/-! ## The `.exit` and `.typeDecl` identity arms. -/

private theorem exit_stmtSimSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {D : List P.Ident} (lbl : String) (md : MetaData P) :
    StmtSimSA (extendFactory := extendFactory) D (.exit lbl md) (.exit lbl md) := by
  intro ρ_s ρ_h h_eval h_hf h_agree _ _ _ _ _ h_def
  refine ⟨?_, ?_⟩
  · intro ρ_s' h_run
    exfalso
    cases h_run with
    | step _ _ _ h1 hr1 =>
      cases h1
      cases hr1 with
      | step _ _ _ hd _ => exact nomatch hd
  · intro l ρ_s' h_run
    have h_inv : l = lbl ∧ ρ_s' = ρ_s := by
      cases h_run with
      | step _ _ _ h1 hr1 =>
        cases h1
        cases hr1 with
        | refl => exact ⟨rfl, rfl⟩
        | step _ _ _ hd _ => exact nomatch hd
    obtain ⟨h_l, h_ρ⟩ := h_inv
    subst h_l; subst h_ρ
    exact ⟨ρ_h, ReflTrans.step _ _ _ StepStmt.step_exit (ReflTrans.refl _),
      h_agree, h_hf, h_eval, h_def⟩

/-- A `typeDecl` is left unchanged by hoisting and simulates itself under `StmtSimSA D`
(it neither reads nor writes the store). -/
private theorem typeDecl_stmtSimSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {D : List P.Ident} (tc : TypeConstructor) (md : MetaData P) :
    StmtSimSA (extendFactory := extendFactory) D (.typeDecl tc md) (.typeDecl tc md) := by
  intro ρ_s ρ_h h_eval h_hf h_agree _ _ _ _ _ h_def
  refine ⟨?_, ?_⟩
  · intro ρ_s' h_run
    have h_eq : ρ_s' = ρ_s := by
      cases h_run with
      | step _ _ _ h1 hr1 =>
        cases h1
        cases hr1 with
        | refl => rfl
        | step _ _ _ hd _ => exact nomatch hd
    subst h_eq
    exact ⟨ρ_h, ReflTrans.step _ _ _ StepStmt.step_typeDecl (ReflTrans.refl _),
      h_agree, h_hf, h_eval, h_def⟩
  · intro l ρ_s' h_run
    exfalso
    cases h_run with
    | step _ _ _ h1 hr1 =>
      cases h1
      cases hr1 with
      | step _ _ _ hd _ => exact nomatch hd

/-! ## Residual peel lemmas for the same-name lift. -/

theorem liftP_cons_residual {P : PureExpr} (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) :
    (Block.liftInitsInLoopBody (s :: rest)).2
      = (Stmt.liftInitsInLoopBody s).2 ++ (Block.liftInitsInLoopBody rest).2 := by
  rw [Block.liftInitsInLoopBody]

theorem liftP_block_residual {P : PureExpr} (lbl : String) (bss : List (Stmt P (Cmd P))) (md :
    MetaData P) :
    (Stmt.liftInitsInLoopBody (.block lbl bss md)).2 = [.block lbl (Block.liftInitsInLoopBody bss).2
        md] := by
  rw [Stmt.liftInitsInLoopBody]

theorem liftP_ite_residual {P : PureExpr} (g : ExprOrNondet P) (tss ess : List (Stmt P (Cmd P))) (md
    : MetaData P) :
    (Stmt.liftInitsInLoopBody (.ite g tss ess md)).2
      = [.ite g (Block.liftInitsInLoopBody tss).2 (Block.liftInitsInLoopBody ess).2 md] := by
  rw [Stmt.liftInitsInLoopBody]

mutual
/-- An init-free statement's same-name lift residual is the statement verbatim. -/
theorem liftP_stmt_residual_no_inits {P : PureExpr} (s : Stmt P (Cmd P)) (h : Stmt.noInitsAnywhere s
    = true) :
    (Stmt.liftInitsInLoopBody s).2 = [s] := by
  match s with
  | .cmd (.init _ _ _ _) => exact absurd h (by simp [Stmt.noInitsAnywhere])
  | .cmd (.set _ _ _) => simp [Stmt.liftInitsInLoopBody]
  | .cmd (.assert _ _ _) => simp [Stmt.liftInitsInLoopBody]
  | .cmd (.assume _ _ _) => simp [Stmt.liftInitsInLoopBody]
  | .cmd (.cover _ _ _) => simp [Stmt.liftInitsInLoopBody]
  | .block lbl bss md =>
      rw [liftP_block_residual]
      rw [liftP_body_residual_no_inits bss (by simpa [Stmt.noInitsAnywhere] using h)]
  | .ite g tss ess md =>
      rw [liftP_ite_residual]
      simp only [Stmt.noInitsAnywhere, Bool.and_eq_true] at h
      rw [liftP_body_residual_no_inits tss h.1, liftP_body_residual_no_inits ess h.2]
  | .loop g m inv body md => simp [Stmt.liftInitsInLoopBody]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody]
  | .funcDecl d md => simp [Stmt.liftInitsInLoopBody]
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBody]
  termination_by sizeOf s

/-- An init-free body's same-name lift residual is the body verbatim. -/
theorem liftP_body_residual_no_inits {P : PureExpr} (body : List (Stmt P (Cmd P))) (h :
    Block.noInitsAnywhere body = true) :
    (Block.liftInitsInLoopBody body).2 = body := by
  match body with
  | [] => rw [Block.liftInitsInLoopBody]
  | s :: rest =>
      rw [liftP_cons_residual]
      simp only [Block.noInitsAnywhere, Bool.and_eq_true] at h
      rw [liftP_stmt_residual_no_inits s h.1, liftP_body_residual_no_inits rest h.2]
      rfl
  termination_by sizeOf body
end

/-! ## Single-outcome reachability classifiers (used by the FAILING per-arm producers). -/

theorem cmd_run_outcome {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {c : Cmd P} {ρ : Env P} {d : Config P (Cmd P)}
    (h_run : StepStmtStar P (EvalCmd P) extendFactory (.stmt (.cmd c) ρ) d) :
    (∃ ρ', d = .terminal ρ') ∨ (∃ l ρ', d = .exiting l ρ') ∨ d = .stmt (.cmd c) ρ := by
  cases h_run with
  | refl => exact Or.inr (Or.inr rfl)
  | step _ _ _ h1 hr1 =>
    cases h1 with
    | step_cmd hev =>
      cases hr1 with
      | refl => exact Or.inl ⟨_, rfl⟩
      | step _ _ _ hd _ => exact nomatch hd

/-- Inversion of a small-step run started from an `.exit lbl` config: it is either still
at the start config, or has taken the single exit step to an `.exiting lbl` config
(a terminal config is also admitted by the disjunction). -/
theorem exit_run_outcome {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {lbl : String} {md : MetaData P} {ρ : Env P} {d : Config P (Cmd P)}
    (h_run : StepStmtStar P (EvalCmd P) extendFactory (.stmt (.exit lbl md) ρ) d) :
    (∃ ρ', d = .terminal ρ') ∨ (∃ l ρ', d = .exiting l ρ') ∨ d = .stmt (.exit lbl md) ρ := by
  cases h_run with
  | refl => exact Or.inr (Or.inr rfl)
  | step _ _ _ h1 hr1 =>
    cases h1
    cases hr1 with
    | refl => exact Or.inr (Or.inl ⟨_, _, rfl⟩)
    | step _ _ _ hd _ => exact nomatch hd

/-- Inversion of a small-step run started from a `.typeDecl` config: it is either still
at the start config or has stepped to a terminal config (`.typeDecl` performs no exit). -/
theorem typeDecl_run_outcome {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {tc : TypeConstructor} {md : MetaData P} {ρ : Env P} {d : Config P (Cmd P)}
    (h_run : StepStmtStar P (EvalCmd P) extendFactory (.stmt (.typeDecl tc md) ρ) d) :
    (∃ ρ', d = .terminal ρ') ∨ (∃ l ρ', d = .exiting l ρ') ∨ d = .stmt (.typeDecl tc md) ρ := by
  cases h_run with
  | refl => exact Or.inr (Or.inr rfl)
  | step _ _ _ h1 hr1 =>
    cases h1
    cases hr1 with
    | refl => exact Or.inl ⟨_, rfl⟩
    | step _ _ _ hd _ => exact nomatch hd

/-! ## The FAILING statement-level simulation `StmtSimFailSA`.

`StmtSimFailSA D s s'` is the failing-config sibling of the terminal/exiting
`StmtSimSA D s s'`: a source statement run from a `D`-defined-target store that
reaches a *failing* config is matched by a target statement run reaching a failing
config too.  These per-statement failing sims feed the combined lift producer
`bodySimBothSA_of_lift`, which threads both the terminal `StmtSimSA`/`BodySimSumSA`
sims (for completed head statements) and the failing ones (for the failure) in a
single walk over the body. -/
private def StmtSimFailSA [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    (D : List P.Ident) (s s' : Stmt P (Cmd P)) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    ρ_h.factory = ρ_s.factory → ρ_h.hasFailure = ρ_s.hasFailure →
    StoreAgreement ρ_s.store ρ_h.store →
    WellFormedSemanticEvalBool ρ_s.factory → WellFormedSemanticEvalVal ρ_s.factory →
    WellFormedSemanticEvalMono ρ_s.factory → WellFormedSemanticEvalExprCongr ρ_s.factory →
    WellFormedSemanticEvalVar ρ_s.factory →
    (∀ y ∈ D, (ρ_h.store y).isSome = true) →
    ∀ (d : Config P (Cmd P)),
      StepStmtStar P (EvalCmd P) extendFactory (.stmt s ρ_s) d →
      d.getEnv.hasFailure = true →
      ∃ d', StepStmtStar P (EvalCmd P) extendFactory (.stmt s' ρ_h) d'
        ∧ d'.getEnv.hasFailure = true

/-- The empty body cannot fail mid-run. -/
theorem bodySimFailSA_nil {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    (D : List P.Ident) :
    BodySimSumFailSA (extendFactory := extendFactory) D [] [] := by
  intro ρ_s ρ_h h_eval h_hf h_agree _ _ _ _ _ h_def d h_run hd_fail
  have h_d_env : d.getEnv = ρ_s := by
    cases h_run with
    | refl => rfl
    | step _ _ _ h_step h_rest =>
      cases h_step with
      | step_stmts_nil =>
        have := reflTransT_from_terminal P extendFactory (reflTrans_to_T h_rest)
        rw [this]; rfl
  have hρ : ρ_s.hasFailure = true := by rw [h_d_env] at hd_fail; simpa [Config.getEnv] using hd_fail
  exact ⟨.terminal ρ_h, evalStmtsSmallNil P (EvalCmd P) extendFactory ρ_h,
    by simpa [Config.getEnv] using (h_hf ▸ hρ)⟩

/-- The cons sequencer for failing body sims. -/
private theorem bodySimFailSA_cons {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {D : List P.Ident} {s s' : Stmt P (Cmd P)} {rest rest' : List (Stmt P (Cmd P))}
    (h_nofd_s : Stmt.noFuncDecl s = true)
    (hhead_term : StmtSimSA (extendFactory := extendFactory) D s s')
    (hhead_fail : StmtSimFailSA (extendFactory := extendFactory) D s s')
    (htail_fail : BodySimSumFailSA (extendFactory := extendFactory) D rest rest') :
    BodySimSumFailSA (extendFactory := extendFactory) D (s :: rest) (s' :: rest') := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def d h_run hd_fail
  rcases stmts_cons_reaches_failing' P extendFactory (reflTrans_to_T h_run) hd_fail with
    ⟨d_head, h_head_run, hd_head⟩ | ⟨ρ_mid, d_rest, h_head_term, h_rest_run, hd_rest⟩
  · obtain ⟨d', h_head_h_run, hd'_fail⟩ :=
      hhead_fail ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def d_head h_head_run
          hd_head
    refine ⟨.seq d' rest', .step _ _ _ StepStmt.step_stmts_cons
      (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_head_h_run), ?_⟩
    simpa [Config.getEnv] using hd'_fail
  · obtain ⟨ρ_h_mid, h_head_h_run, h_agree_mid, h_hf_mid, h_eval_mid, h_def_mid⟩ :=
      (hhead_term ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def).1 ρ_mid h_head_term
    have h_eval_mid_src : ρ_mid.factory = ρ_s.factory :=
      smallStep_noFuncDecl_preserves_eval P (EvalCmd P) extendFactory s ρ_s ρ_mid h_nofd_s
          h_head_term
    obtain ⟨d', h_rest_h_run, hd'_fail⟩ :=
      htail_fail ρ_mid ρ_h_mid h_eval_mid h_hf_mid h_agree_mid
        (by rw [h_eval_mid_src]; exact hwfb) (by rw [h_eval_mid_src]; exact hwfv)
        (by rw [h_eval_mid_src]; exact hwfd) (by rw [h_eval_mid_src]; exact hwfc)
        (by rw [h_eval_mid_src]; exact hwfvar) h_def_mid d_rest h_rest_run hd_rest
    refine ⟨d', ReflTrans_Transitive _ _ _ _
      (stmts_cons_step P (EvalCmd P) extendFactory s' rest' ρ_h ρ_h_mid h_head_h_run)
      h_rest_h_run, hd'_fail⟩

/-- A single-outcome statement's failing sim follows from its terminal+exiting
`StmtSimSA`. -/
private theorem stmtSimFailSA_of_singleOutcome {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {D : List P.Ident} {s s' : Stmt P (Cmd P)}
    (h_outcome : ∀ {ρ : Env P} {d : Config P (Cmd P)},
      StepStmtStar P (EvalCmd P) extendFactory (.stmt s ρ) d →
      (∃ ρ', d = .terminal ρ') ∨ (∃ l ρ', d = .exiting l ρ') ∨ d = .stmt s ρ)
    (h_term : StmtSimSA (extendFactory := extendFactory) D s s') :
    StmtSimFailSA (extendFactory := extendFactory) D s s' := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def d h_run hd_fail
  rcases h_outcome h_run with ⟨ρ', h_eq⟩ | ⟨l, ρ', h_eq⟩ | h_eq
  · subst h_eq
    have hρ'_fail : ρ'.hasFailure = true := by simpa [Config.getEnv] using hd_fail
    obtain ⟨ρ_h', h_run_h, _, h_hf', _, _⟩ :=
      (h_term ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def).1 ρ' h_run
    exact ⟨.terminal ρ_h', h_run_h, by simpa [Config.getEnv] using (h_hf' ▸ hρ'_fail)⟩
  · subst h_eq
    have hρ'_fail : ρ'.hasFailure = true := by simpa [Config.getEnv] using hd_fail
    obtain ⟨ρ_h', h_run_h, _, h_hf', _, _⟩ :=
      (h_term ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def).2 l ρ' h_run
    exact ⟨.exiting l ρ_h', h_run_h, by simpa [Config.getEnv] using (h_hf' ▸ hρ'_fail)⟩
  · subst h_eq
    have hρ_s_fail : ρ_s.hasFailure = true := by simpa [Config.getEnv] using hd_fail
    exact ⟨.stmt s' ρ_h, .refl _, by simpa [Config.getEnv] using (h_hf ▸ hρ_s_fail)⟩

/-! ## Per-arm FAILING sim producers (block / ite / nested-loop route the inner failure). -/

/-- The `.block` failing arm. -/
private theorem block_stmtSimFailSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {D : List P.Ident} {lbl : String} {inner inner_h : List (Stmt P (Cmd P))} {md : MetaData P}
    (inner_fail : BodySimSumFailSA (extendFactory := extendFactory) D inner inner_h) :
    StmtSimFailSA (extendFactory := extendFactory) D (.block lbl inner md) (.block lbl inner_h md)
        := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def d h_run hd_fail
  rcases h_run with _ | ⟨_, _, _, h1, hr1⟩
  · have hρ_s_fail : ρ_s.hasFailure = true := by simpa [Config.getEnv] using hd_fail
    exact ⟨.stmt (.block lbl inner_h md) ρ_h, .refl _,
      by simpa [Config.getEnv] using (h_hf ▸ hρ_s_fail)⟩
  · cases h1
    obtain ⟨d_inner, h_inner_run, hd_inner_fail⟩ :=      block_reaches_failing' P extendFactory hr1
        hd_fail
    obtain ⟨d', h_inner_h_run, hd'_fail⟩ :=
      inner_fail ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def d_inner
        h_inner_run hd_inner_fail
    refine ⟨.block (.some lbl) ρ_h.store ρ_h.factory d', ?_, by simpa [Config.getEnv] using
        hd'_fail⟩
    refine ReflTrans.step _ _ _ StepStmt.step_block ?_
    exact block_inner_star P (EvalCmd P) extendFactory _ _ (some lbl) ρ_h.store ρ_h.factory
        h_inner_h_run

/-- The `.ite (.det g)` failing arm. -/
private theorem ite_stmtSimFailSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {D : List P.Ident} {g : P.Expr} {tss_s tss_h ess_s ess_h : List (Stmt P (Cmd P))} {md : MetaData
        P}
    (then_fail : BodySimSumFailSA (extendFactory := extendFactory) D tss_s tss_h)
    (else_fail : BodySimSumFailSA (extendFactory := extendFactory) D ess_s ess_h) :
    StmtSimFailSA (extendFactory := extendFactory) D
      (.ite (.det g) tss_s ess_s md) (.ite (.det g) tss_h ess_h md) := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def d h_run hd_fail
  have guard_h : ∀ {bv : P.Expr}, P.eval ρ_s.factory ρ_s.store g = .some bv →
      P.eval ρ_h.factory ρ_h.store g = .some bv := by
    intro bv hg
    rw [h_eval]
    exact hwfd g bv ρ_s.store ρ_h.store
      (storeAgreement_supplies_mono_premise ρ_s.store ρ_h.store h_agree) hg
  rcases h_run with _ | ⟨_, _, _, h1, hr1⟩
  · have hρ_s_fail : ρ_s.hasFailure = true := by simpa [Config.getEnv] using hd_fail
    exact ⟨.stmt (.ite (.det g) tss_h ess_h md) ρ_h, .refl _,
      by simpa [Config.getEnv] using (h_hf ▸ hρ_s_fail)⟩
  · cases h1 with
    | step_ite_true hg hwf =>
      obtain ⟨d_inner, h_inner_run, hd_inner_fail, _⟩ :=        blockT_none_reaches_failing' P
          extendFactory (reflTrans_to_T hr1) hd_fail
      obtain ⟨d', h_branch_h, hd'_fail⟩ :=
        then_fail ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def d_inner
          (reflTransT_to_prop h_inner_run) hd_inner_fail
      refine ⟨.block .none ρ_h.store ρ_h.factory d',
        ReflTrans.step _ _ _ (StepStmt.step_ite_true (guard_h hg) (h_eval ▸ hwf))
          (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_h.store ρ_h.factory h_branch_h),
        by simpa [Config.getEnv] using hd'_fail⟩
    | step_ite_false hg hwf =>
      obtain ⟨d_inner, h_inner_run, hd_inner_fail, _⟩ :=        blockT_none_reaches_failing' P
          extendFactory (reflTrans_to_T hr1) hd_fail
      obtain ⟨d', h_branch_h, hd'_fail⟩ :=
        else_fail ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def d_inner
          (reflTransT_to_prop h_inner_run) hd_inner_fail
      refine ⟨.block .none ρ_h.store ρ_h.factory d',
        ReflTrans.step _ _ _ (StepStmt.step_ite_false (guard_h hg) (h_eval ▸ hwf))
          (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_h.store ρ_h.factory h_branch_h),
        by simpa [Config.getEnv] using hd'_fail⟩

/-- The `.ite .nondet` failing arm. -/
private theorem ite_nondet_stmtSimFailSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {D : List P.Ident} {tss_s tss_h ess_s ess_h : List (Stmt P (Cmd P))} {md : MetaData P}
    (then_fail : BodySimSumFailSA (extendFactory := extendFactory) D tss_s tss_h)
    (else_fail : BodySimSumFailSA (extendFactory := extendFactory) D ess_s ess_h) :
    StmtSimFailSA (extendFactory := extendFactory) D
      (.ite .nondet tss_s ess_s md) (.ite .nondet tss_h ess_h md) := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def d h_run hd_fail
  rcases h_run with _ | ⟨_, _, _, h1, hr1⟩
  · have hρ_s_fail : ρ_s.hasFailure = true := by simpa [Config.getEnv] using hd_fail
    exact ⟨.stmt (.ite .nondet tss_h ess_h md) ρ_h, .refl _,
      by simpa [Config.getEnv] using (h_hf ▸ hρ_s_fail)⟩
  · cases h1 with
    | step_ite_nondet_true =>
      obtain ⟨d_inner, h_inner_run, hd_inner_fail, _⟩ :=        blockT_none_reaches_failing' P
          extendFactory (reflTrans_to_T hr1) hd_fail
      obtain ⟨d', h_branch_h, hd'_fail⟩ :=
        then_fail ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def d_inner
          (reflTransT_to_prop h_inner_run) hd_inner_fail
      refine ⟨.block .none ρ_h.store ρ_h.factory d',
        ReflTrans.step _ _ _ StepStmt.step_ite_nondet_true
          (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_h.store ρ_h.factory h_branch_h),
        by simpa [Config.getEnv] using hd'_fail⟩
    | step_ite_nondet_false =>
      obtain ⟨d_inner, h_inner_run, hd_inner_fail, _⟩ :=        blockT_none_reaches_failing' P
          extendFactory (reflTrans_to_T hr1) hd_fail
      obtain ⟨d', h_branch_h, hd'_fail⟩ :=
        else_fail ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def d_inner
          (reflTransT_to_prop h_inner_run) hd_inner_fail
      refine ⟨.block .none ρ_h.store ρ_h.factory d',
        ReflTrans.step _ _ _ StepStmt.step_ite_nondet_false
          (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_h.store ρ_h.factory h_branch_h),
        by simpa [Config.getEnv] using hd'_fail⟩

/-- The nested `.loop` failing arm. -/
private theorem nestedLoop_stmtSimFailSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {D : List P.Ident} {g2 : P.Expr} {inner inner_h : List (Stmt P (Cmd P))} {md2_s md2_h : MetaData
        P}
    (inner_sim : BodySimSumSA (extendFactory := extendFactory) D inner inner_h)
    (inner_fail : BodySimSumFailSA (extendFactory := extendFactory) D inner inner_h)
    (h_nofd_src : Block.noFuncDecl inner = true) :
    StmtSimFailSA (extendFactory := extendFactory) D
      (.loop (.det g2) none [] inner md2_s)
      (.loop (.det g2) none [] inner_h md2_h) := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def d h_run hd_fail
  exact samenameLoopDetSA_F (D := D) (g := g2) (md_s := md2_s) (md_h := md2_h)
    inner_sim inner_fail h_nofd_src
    h_agree h_eval h_hf hwfb hwfv hwfd hwfc hwfvar h_def h_run hd_fail

/-- The combined cons sequencer: a head `StmtSimSA` + `StmtSimFailSA` (with source
`noFuncDecl`) and a combined tail sim stitch onto a combined cons sim. -/
private theorem bodySimBothSA_cons {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {D : List P.Ident} {s s' : Stmt P (Cmd P)} {rest rest' : List (Stmt P (Cmd P))}
    (h_nofd_s : Stmt.noFuncDecl s = true)
    (hhead_term : StmtSimSA (extendFactory := extendFactory) D s s')
    (hhead_fail : StmtSimFailSA (extendFactory := extendFactory) D s s')
    (htail : BodySimSumSA (extendFactory := extendFactory) D rest rest'
        ∧ BodySimSumFailSA (extendFactory := extendFactory) D rest rest') :
    BodySimSumSA (extendFactory := extendFactory) D (s :: rest) (s' :: rest')
      ∧ BodySimSumFailSA (extendFactory := extendFactory) D (s :: rest) (s' :: rest') :=
  ⟨bodySimSA_cons h_nofd_s hhead_term htail.1,
   bodySimFailSA_cons h_nofd_s hhead_term hhead_fail htail.2⟩

/-! ## The combined structural lift producer (KEEPS `h_if`).

Structural induction over `body₁`, mirroring `Block.liftInitsInLoopBody`'s
recursion.  Each statement maps to a SINGLETON residual, so the combined
`bodySimBothSA_cons` sequencer drives the recursion one head-statement at a time,
producing BOTH the terminal/exiting `BodySimSumSA` and the failing
`BodySimSumFailSA` in a single walk.  The carrier `D` holds every init name
reachable in `body₁` (`Block.definedVars body₁ ⊆ D`); the nested `.loop` arm
supplies that the prelude havocs (whose names are exactly `Block.definedVars
body₁`) are all defined in the target store before the loop. -/
private theorem bodySimBothSA_of_lift {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    {extendFactory : ExtendFactory P} {D : List P.Ident}
    (body₁ : List (Stmt P (Cmd P)))
    (h_if : Block.loopBodyNoInits body₁ = true)
    (h_shape : Block.transportShape body₁ = true)
    (h_nofd : Block.noFuncDecl body₁ = true)
    (h_defD : ∀ y ∈ Block.definedVars body₁ false, y ∈ D) :
    BodySimSumSA (extendFactory := extendFactory) D body₁ (Block.liftInitsInLoopBody body₁).2
      ∧ BodySimSumFailSA (extendFactory := extendFactory) D body₁
          (Block.liftInitsInLoopBody body₁).2 := by
  match body₁ with
  | [] =>
      rw [show (Block.liftInitsInLoopBody ([] : List (Stmt P (Cmd P)))).2 = [] by
        rw [Block.liftInitsInLoopBody]]
      exact ⟨bodySimSA_nil D, bodySimFailSA_nil D⟩
  | s :: rest =>
      rw [liftP_cons_residual]
      obtain ⟨h_if_s, h_if_rest⟩ := initfree_cons h_if
      obtain ⟨h_shape_s, h_shape_rest⟩ :
          Stmt.transportShape s = true ∧ Block.transportShape rest = true := by
        simpa only [Block.transportShape, Bool.and_eq_true] using h_shape
      obtain ⟨h_nofd_s, h_nofd_rest⟩ :
          Stmt.noFuncDecl s = true ∧ Block.noFuncDecl rest = true := by
        simpa [Block.noFuncDecl, Bool.and_eq_true] using h_nofd
      have h_defD_rest : ∀ y ∈ Block.definedVars rest false, y ∈ D := fun y hy =>
        h_defD y (by simp only [Block.definedVars, List.mem_append]; exact Or.inr hy)
      have h_defD_s : ∀ y ∈ Stmt.definedVars s false, y ∈ D := fun y hy =>
        h_defD y (by simp only [Block.definedVars, List.mem_append]; exact Or.inl hy)
      have h_tail := bodySimBothSA_of_lift (extendFactory := extendFactory) rest h_if_rest
        h_shape_rest h_nofd_rest h_defD_rest
      -- Case on the head statement, restricted by `transportShape` to the
      -- expressible fragment.  Each head residual is a singleton, so
      -- `bodySimBothSA_cons` stitches it onto the combined tail.
      match s, h_if_s, h_shape_s, h_nofd_s, h_defD_s with
      | .cmd (.init a ty (.det rhs) md), _, _, _, h_defD_s =>
          have h_sres : (Stmt.liftInitsInLoopBody (.cmd (.init a ty (.det rhs) md))).2
              = [.cmd (.set a (.det rhs) md)] := by rw [Stmt.liftInitsInLoopBody]
          rw [h_sres, List.cons_append, List.nil_append]
          have h_a_D : a ∈ D := h_defD_s a (by
            show a ∈ (Stmt.cmd (Cmd.init a ty (ExprOrNondet.det rhs) md)).definedVars false
            with_unfolding_all exact List.mem_singleton.mpr rfl)
          exact bodySimBothSA_cons (by simp [Stmt.noFuncDecl])
            (initSet_stmtSimSA a ty rhs md h_a_D)
            (stmtSimFailSA_of_singleOutcome cmd_run_outcome (initSet_stmtSimSA a ty rhs md h_a_D))
                h_tail
      | .cmd (.init a ty .nondet md), _, _, _, h_defD_s =>
          have h_sres : (Stmt.liftInitsInLoopBody (.cmd (.init a ty .nondet md))).2
              = [.cmd (.set a .nondet md)] := by rw [Stmt.liftInitsInLoopBody]
          rw [h_sres, List.cons_append, List.nil_append]
          have h_a_D : a ∈ D := h_defD_s a (by
            show a ∈ (Stmt.cmd (Cmd.init a ty ExprOrNondet.nondet md)).definedVars false
            with_unfolding_all exact List.mem_singleton.mpr rfl)
          exact bodySimBothSA_cons (by simp [Stmt.noFuncDecl])
            (initSet_nondet_stmtSimSA a ty md h_a_D)
            (stmtSimFailSA_of_singleOutcome cmd_run_outcome (initSet_nondet_stmtSimSA a ty md
                h_a_D)) h_tail
      | .cmd (.set name rhs md), _, _, _, _ =>
          have h_sres : (Stmt.liftInitsInLoopBody (.cmd (.set name rhs md))).2
              = [.cmd (.set name rhs md)] := by simp [Stmt.liftInitsInLoopBody]
          rw [h_sres, List.cons_append, List.nil_append]
          exact bodySimBothSA_cons (by simp [Stmt.noFuncDecl])
            (cmd_id_stmtSimSA (.set name rhs md) (by simp [Cmd.definedVars]))
            (stmtSimFailSA_of_singleOutcome cmd_run_outcome (cmd_id_stmtSimSA (.set name rhs md)
                (by simp [Cmd.definedVars]))) h_tail
      | .cmd (.assert lbl e md), _, _, _, _ =>
          have h_sres : (Stmt.liftInitsInLoopBody (.cmd (.assert lbl e md))).2
              = [.cmd (.assert lbl e md)] := by simp [Stmt.liftInitsInLoopBody]
          rw [h_sres, List.cons_append, List.nil_append]
          exact bodySimBothSA_cons (by simp [Stmt.noFuncDecl])
            (cmd_id_stmtSimSA (.assert lbl e md) (by simp [Cmd.definedVars]))
            (stmtSimFailSA_of_singleOutcome cmd_run_outcome (cmd_id_stmtSimSA (.assert lbl e md)
                (by simp [Cmd.definedVars]))) h_tail
      | .cmd (.assume lbl e md), _, _, _, _ =>
          have h_sres : (Stmt.liftInitsInLoopBody (.cmd (.assume lbl e md))).2
              = [.cmd (.assume lbl e md)] := by simp [Stmt.liftInitsInLoopBody]
          rw [h_sres, List.cons_append, List.nil_append]
          exact bodySimBothSA_cons (by simp [Stmt.noFuncDecl])
            (cmd_id_stmtSimSA (.assume lbl e md) (by simp [Cmd.definedVars]))
            (stmtSimFailSA_of_singleOutcome cmd_run_outcome (cmd_id_stmtSimSA (.assume lbl e md)
                (by simp [Cmd.definedVars]))) h_tail
      | .cmd (.cover lbl e md), _, _, _, _ =>
          have h_sres : (Stmt.liftInitsInLoopBody (.cmd (.cover lbl e md))).2
              = [.cmd (.cover lbl e md)] := by simp [Stmt.liftInitsInLoopBody]
          rw [h_sres, List.cons_append, List.nil_append]
          exact bodySimBothSA_cons (by simp [Stmt.noFuncDecl])
            (cmd_id_stmtSimSA (.cover lbl e md) (by simp [Cmd.definedVars]))
            (stmtSimFailSA_of_singleOutcome cmd_run_outcome (cmd_id_stmtSimSA (.cover lbl e md)
                (by simp [Cmd.definedVars]))) h_tail
      | .typeDecl tc md, _, _, _, _ =>
          have h_sres : (Stmt.liftInitsInLoopBody (.typeDecl tc md)).2
              = [.typeDecl tc md] := by rw [Stmt.liftInitsInLoopBody]
          rw [h_sres, List.cons_append, List.nil_append]
          exact bodySimBothSA_cons (by simp [Stmt.noFuncDecl])
            (typeDecl_stmtSimSA tc md)
            (stmtSimFailSA_of_singleOutcome typeDecl_run_outcome (typeDecl_stmtSimSA tc md))
                h_tail
      | .exit lbl md, _, _, _, _ =>
          have h_sres : (Stmt.liftInitsInLoopBody (.exit lbl md)).2
              = [.exit lbl md] := by rw [Stmt.liftInitsInLoopBody]
          rw [h_sres, List.cons_append, List.nil_append]
          exact bodySimBothSA_cons (by simp [Stmt.noFuncDecl])
            (exit_stmtSimSA lbl md)
            (stmtSimFailSA_of_singleOutcome exit_run_outcome (exit_stmtSimSA lbl md)) h_tail
      | .block lbl bss md, h_if_s, h_shape_s, h_nofd_s, h_defD_s =>
          rw [liftP_block_residual, List.cons_append, List.nil_append]
          have h_if_bss := initfree_block h_if_s
          have h_shape_bss : Block.transportShape bss = true := by
            simpa only [Stmt.transportShape] using h_shape_s
          have h_nofd_bss : Block.noFuncDecl bss = true := by
            simpa [Stmt.noFuncDecl] using h_nofd_s
          have h_defD_bss : ∀ y ∈ Block.definedVars bss false, y ∈ D := fun y hy =>
            h_defD_s y (by rw [Stmt.definedVars]; exact hy)
          have h_inner :=
            bodySimBothSA_of_lift (extendFactory := extendFactory) bss h_if_bss h_shape_bss
                h_nofd_bss h_defD_bss
          exact bodySimBothSA_cons h_nofd_s (block_stmtSimSA h_inner.1)
            (block_stmtSimFailSA h_inner.2) h_tail
      | .ite (.det g) tss ess md, h_if_s, h_shape_s, h_nofd_s, h_defD_s =>
          rw [liftP_ite_residual, List.cons_append, List.nil_append]
          obtain ⟨h_if_tss, h_if_ess⟩ := initfree_ite h_if_s
          obtain ⟨h_shape_tss, h_shape_ess⟩ :
              Block.transportShape tss = true ∧ Block.transportShape ess = true := by
            simpa only [Stmt.transportShape, Bool.and_eq_true] using h_shape_s
          obtain ⟨h_nofd_tss, h_nofd_ess⟩ :
              Block.noFuncDecl tss = true ∧ Block.noFuncDecl ess = true := by
            simpa [Stmt.noFuncDecl, Bool.and_eq_true] using h_nofd_s
          have h_defD_tss : ∀ y ∈ Block.definedVars tss false, y ∈ D := fun y hy =>
            h_defD_s y (by rw [Stmt.definedVars]; exact List.mem_append.mpr (Or.inl hy))
          have h_defD_ess : ∀ y ∈ Block.definedVars ess false, y ∈ D := fun y hy =>
            h_defD_s y (by rw [Stmt.definedVars]; exact List.mem_append.mpr (Or.inr hy))
          have h_then := bodySimBothSA_of_lift (extendFactory := extendFactory) tss h_if_tss
              h_shape_tss h_nofd_tss h_defD_tss
          have h_else := bodySimBothSA_of_lift (extendFactory := extendFactory) ess h_if_ess
              h_shape_ess h_nofd_ess h_defD_ess
          exact bodySimBothSA_cons h_nofd_s (ite_stmtSimSA h_then.1 h_else.1)
            (ite_stmtSimFailSA h_then.2 h_else.2) h_tail
      | .ite .nondet tss ess md, h_if_s, h_shape_s, h_nofd_s, h_defD_s =>
          rw [liftP_ite_residual, List.cons_append, List.nil_append]
          obtain ⟨h_if_tss, h_if_ess⟩ := initfree_ite h_if_s
          obtain ⟨h_shape_tss, h_shape_ess⟩ :
              Block.transportShape tss = true ∧ Block.transportShape ess = true := by
            simpa only [Stmt.transportShape, Bool.and_eq_true] using h_shape_s
          obtain ⟨h_nofd_tss, h_nofd_ess⟩ :
              Block.noFuncDecl tss = true ∧ Block.noFuncDecl ess = true := by
            simpa [Stmt.noFuncDecl, Bool.and_eq_true] using h_nofd_s
          have h_defD_tss : ∀ y ∈ Block.definedVars tss false, y ∈ D := fun y hy =>
            h_defD_s y (by rw [Stmt.definedVars]; exact List.mem_append.mpr (Or.inl hy))
          have h_defD_ess : ∀ y ∈ Block.definedVars ess false, y ∈ D := fun y hy =>
            h_defD_s y (by rw [Stmt.definedVars]; exact List.mem_append.mpr (Or.inr hy))
          have h_then := bodySimBothSA_of_lift (extendFactory := extendFactory) tss h_if_tss
              h_shape_tss h_nofd_tss h_defD_tss
          have h_else := bodySimBothSA_of_lift (extendFactory := extendFactory) ess h_if_ess
              h_shape_ess h_nofd_ess h_defD_ess
          exact bodySimBothSA_cons h_nofd_s (ite_nondet_stmtSimSA h_then.1 h_else.1)
            (ite_nondet_stmtSimFailSA h_then.2 h_else.2) h_tail
      | .loop (.det g) none [] lbody md, h_if_s, h_shape_s, h_nofd_s, _ =>
          have h_sres : (Stmt.liftInitsInLoopBody (.loop (.det g) none [] lbody md)).2
              = [.loop (.det g) none [] lbody md] := by rw [Stmt.liftInitsInLoopBody]
          rw [h_sres, List.cons_append, List.nil_append]
          obtain ⟨h_noinits, h_if_lbody⟩ := initfree_loop_noinits h_if_s
          have h_nofd_lbody : Block.noFuncDecl lbody = true := by
            simpa [Stmt.noFuncDecl] using h_nofd_s
          have h_shape_lbody : Block.transportShape lbody = true := by
            simpa only [Stmt.transportShape] using h_shape_s
          -- the loop body's lift residual is itself (init-free), and it self-simulates
          -- at any D (its definedVars are empty).
          have h_inner : BodySimSumSA (extendFactory := extendFactory) D lbody lbody
              ∧ BodySimSumFailSA (extendFactory := extendFactory) D lbody lbody := by
            have := bodySimBothSA_of_lift (extendFactory := extendFactory) (D := D) lbody h_if_lbody
                h_shape_lbody h_nofd_lbody
              (by intro y hy
                  rw [block_definedVars_nil_of_noInits_noFuncDecl lbody h_noinits h_nofd_lbody]
                      at hy
                  exact absurd hy List.not_mem_nil)
            rwa [liftP_body_residual_no_inits lbody h_noinits] at this
          exact bodySimBothSA_cons h_nofd_s
            (nestedLoop_stmtSimSA h_inner.1 h_nofd_lbody)
            (nestedLoop_stmtSimFailSA h_inner.1 h_inner.2 h_nofd_lbody) h_tail
      | .loop (.det g) (some me) inv lbody md, _, h_shape_s, _, _ =>
          exact absurd h_shape_s (by simp [Stmt.transportShape])
      | .loop (.det g) none (i :: inv) lbody md, _, h_shape_s, _, _ =>
          exact absurd h_shape_s (by simp [Stmt.transportShape])
      | .loop .nondet m inv lbody md, _, h_shape_s, _, _ =>
          exact absurd h_shape_s (by simp [Stmt.transportShape])
      | .funcDecl d md, _, _, h_nofd_s, _ =>
          exact absurd h_nofd_s (by simp [Stmt.noFuncDecl])
  termination_by sizeOf body₁

/-! # Same-name hoist top-level sequencer: prelude FIRST, then the loop driver.

The same-name `.loop` arm of the hoist lifts a body-local `init y := e` to a
SAME-name prelude havoc `init y := *` *before* the loop and rewrites the body
init to `set y := e`.  The hoist of a single loop is therefore
`havocs.map Stmt.cmd ++ [.loop g m inv body₂ md]` where `havocs` are the lifted
prelude inits.

The naive "transport a body sim THROUGH the loop directly" plan is UNSOUND when
the body has a nested loop with inits (the leading body `set` would require the
target slot UNDEFINED while the driver's `D`-invariant hands it DEFINED — opposite
polarities).  The sound architecture runs the prelude FIRST: this establishes the
hoisted names target-DEFINED (`D`), after which the loop driver's `D`-definedness
invariant is exactly satisfied and the body sim transports cleanly.

This section lands:
* `preludeHavocs` / `preludeNames` — the prelude statement list and its names;
* `prelude_runner` — running the prelude from a store-agreeing env, with every
  prelude name source-AND-target-undefined and the names `Nodup`, lands
  `StoreAgreement`-preserved + every prelude name target-defined (the run picks an
  arbitrary havoc value at each slot — the source never reads it);
* `HoistSimSA` — the top-level same-name `StoreAgreement` simulation of a source
  loop by its hoist (prelude ++ rewritten loop), carrying the DUAL-undefinedness of
  the prelude names at entry;
* `hoistSimSA_of_sequence` — the sequencer that inhabits `HoistSimSA` from a body
  sim, composing `prelude_runner` (step 1) with the loop drivers
  `samenameLoopDetSA_TE` / `_E` (steps 2-3) and stitching prelude ++ loop via
  `stmts_prefix_terminal_append` (step 4).  No pivot env, no `bodySimSA_trans`. -/

/-- The prelude havoc statements built from a `(name, ty, md)` triple list: each
triple `(y, ty, md)` becomes a havoc `Stmt.cmd (Cmd.init y ty .nondet md)`. -/
def preludeHavocs (hs : List (P.Ident × P.Ty × MetaData P)) :
    List (Stmt P (Cmd P)) :=
  hs.map (fun t => .cmd (Cmd.init t.1 t.2.1 .nondet t.2.2))

/-- The names introduced by a prelude triple list. -/
def preludeNames (hs : List (P.Ident × P.Ty × MetaData P)) : List P.Ident :=
  hs.map Prod.fst

/-- **The prelude-runner over a havoc LIST.**  Running the prelude
`preludeHavocs hs` from a target env `ρ_h` that agrees with the source `ρ_s`, where
every prelude name is source-AND-target-undefined and the names are `Nodup`, lands a
terminal target env `ρ_h'` with: `StoreAgreement` preserved (each name is
source-undefined, so the chosen havoc value stays hidden from the source), the
eval/hasFailure fields unchanged, and every prelude name target-defined.  This is the
list generalisation of `step_init_havoc_to`; the per-step `StoreAgreement` transport
is `storeAgreement_storeWith` and the definedness carry-through is
`stmts_preserves_isSome`. -/
theorem prelude_runner {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasVarsPure P P.Expr]
    [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    (hs : List (P.Ident × P.Ty × MetaData P))
    (ρ_s ρ_h : Env P)
    (h_agree : StoreAgreement ρ_s.store ρ_h.store)
    (h_src_none : ∀ y ∈ preludeNames hs, ρ_s.store y = none)
    (h_tgt_none : ∀ y ∈ preludeNames hs, ρ_h.store y = none)
    (h_nodup : (preludeNames hs).Nodup)
    (hwf_var : WellFormedSemanticEvalVar ρ_h.factory) :
    ∃ ρ_h' : Env P,
      StepStmtStar P (EvalCmd P) extendFactory
        (.stmts (preludeHavocs hs) ρ_h) (.terminal ρ_h') ∧
      StoreAgreement ρ_s.store ρ_h'.store ∧
      ρ_h'.hasFailure = ρ_h.hasFailure ∧ ρ_h'.factory = ρ_h.factory ∧
      (∀ y ∈ preludeNames hs, (ρ_h'.store y).isSome = true) := by
  induction hs generalizing ρ_h with
  | nil =>
    refine ⟨ρ_h, ReflTrans.step _ _ _ StepStmt.step_stmts_nil (ReflTrans.refl _),
      h_agree, rfl, rfl, ?_⟩
    intro y hy; simp [preludeNames] at hy
  | cons t rest ih =>
    obtain ⟨y, ty, md⟩ := t
    have h_nodup' : y ∉ preludeNames rest ∧ (preludeNames rest).Nodup := by
      have h_eq : (preludeNames ((y, ty, md) :: rest)) = y :: preludeNames rest := rfl
      rw [h_eq, List.nodup_cons] at h_nodup; exact h_nodup
    obtain ⟨h_y_notin, h_nodup_rest⟩ := h_nodup'
    have h_y_mem : y ∈ preludeNames ((y, ty, md) :: rest) := by simp [preludeNames]
    have h_y_src_none : ρ_s.store y = none := h_src_none y h_y_mem
    have h_y_tgt_none : ρ_h.store y = none := h_tgt_none y h_y_mem
    -- run the head havoc to terminal, picking value `HasBool.tt` (any value works).
    have h_head_step :=
      step_init_havoc_to (extendFactory := extendFactory) y ty HasBool.tt md ρ_h h_y_tgt_none
        (HasBool.boolIsVal ρ_h.factory).1 hwf_var
    let ρ_mid : Env P := { ρ_h with store := SemanticStore.update ρ_h.store y HasBool.tt }
    have h_agree_mid : StoreAgreement ρ_s.store ρ_mid.store :=
      storeAgreement_storeWith _ _ _ _ h_agree h_y_src_none
    have h_src_none_rest : ∀ z ∈ preludeNames rest, ρ_s.store z = none := fun z hz =>
      h_src_none z (by simp [preludeNames] at hz ⊢; exact Or.inr hz)
    have h_tgt_none_rest : ∀ z ∈ preludeNames rest, ρ_mid.store z = none := by
      intro z hz
      have h_zy : z ≠ y := fun h => h_y_notin (h ▸ hz)
      show SemanticStore.update ρ_h.store y HasBool.tt z = none
      simp only [SemanticStore.update, if_neg h_zy]
      exact h_tgt_none z (by simp [preludeNames] at hz ⊢; exact Or.inr hz)
    obtain ⟨ρ_h', h_rest_run, h_agree', h_hf', h_eval', h_def'⟩ :=
      ih ρ_mid h_agree_mid h_src_none_rest h_tgt_none_rest h_nodup_rest hwf_var
    refine ⟨ρ_h', ?_, h_agree', h_hf', h_eval', ?_⟩
    · -- prelude = (head .cmd init) :: tail havocs; chain head terminal then tail run.
      rw [show preludeHavocs ((y, ty, md) :: rest)
          = (.cmd (Cmd.init y ty .nondet md)) :: preludeHavocs rest by rfl]
      exact ReflTrans_Transitive _ _ _ _
        (stmts_cons_step P (EvalCmd P) extendFactory _ _ ρ_h ρ_mid h_head_step)
        h_rest_run
    · -- every name (head `y` or a tail name) is defined in `ρ_h'`.
      intro z hz
      rcases List.mem_cons.mp
          (by rw [show preludeNames ((y, ty, md) :: rest) = y :: preludeNames rest from rfl] at hz
              exact hz) with h_z_y | h_z_rest
      · subst h_z_y
        have h_y_mid_def : (ρ_mid.store z).isSome = true := by
          show (SemanticStore.update ρ_h.store z HasBool.tt z).isSome = true;
              simp [SemanticStore.update]
        exact stmts_preserves_isSome (extendFactory := extendFactory) h_rest_run h_y_mid_def
      · exact h_def' z h_z_rest

/-- **The top-level same-name hoist simulation** of a single source loop by its
hoist (prelude ++ rewritten loop), on `StoreAgreement` (source-on-left).  Given
the prelude names DUAL-undefined at entry (source-undefined, target-undefined) and
`Nodup`, a source loop run is matched by a hoist run reaching the same outcome with
`StoreAgreement` re-established and eval/hasFailure agreement preserved. -/
private def HoistSimSA [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    (s : Stmt P (Cmd P)) (hoist : List (Stmt P (Cmd P)))
    (names : List P.Ident) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    ρ_h.factory = ρ_s.factory → ρ_h.hasFailure = ρ_s.hasFailure →
    StoreAgreement ρ_s.store ρ_h.store →
    WellFormedSemanticEvalBool ρ_s.factory → WellFormedSemanticEvalVal ρ_s.factory →
    WellFormedSemanticEvalMono ρ_s.factory → WellFormedSemanticEvalExprCongr ρ_s.factory →
    WellFormedSemanticEvalVar ρ_s.factory →
    (∀ y ∈ names, ρ_s.store y = none) →
    (∀ y ∈ names, ρ_h.store y = none) →
    (∀ (oc : Option String) (ρ_post : Env P),
      StepStmtStar P (EvalCmd P) extendFactory (.stmt s ρ_s) (Env.outcomeConfig oc ρ_post) →
      ∃ ρ_post_h : Env P,
        StepStmtStar P (EvalCmd P) extendFactory (.stmts hoist ρ_h) (Env.outcomeConfig oc ρ_post_h)
            ∧
        StoreAgreement ρ_post.store ρ_post_h.store ∧
        ρ_post_h.hasFailure = ρ_post.hasFailure ∧ ρ_post_h.factory = ρ_post.factory)

/-- **The sequencer.**  A body sim `BodySimSumSA (preludeNames hs) body body₂`
inhabits `HoistSimSA` for the source loop `.loop (.det g) none [] body md_s` and its
hoist `preludeHavocs hs ++ [.loop (.det g) none [] body₂ md_h]`, with the prelude
names `Nodup`.  The recipe runs the prelude on the target via `prelude_runner`
(establishing `preludeNames hs` target-defined, the `D` the driver wants), then feeds
the terminal/exiting loop drivers, then stitches prelude ++ loop via
`stmts_prefix_terminal_append` + `stmt_to_singleton_stmts`.  No pivot env. -/
private theorem hoistSimSA_of_sequence {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body body₂ : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {hs : List (P.Ident × P.Ty × MetaData P)}
    (body_sim : BodySimSumSA (extendFactory := extendFactory) (preludeNames hs) body body₂)
    (h_src_body_nofd : Block.noFuncDecl body = true)
    (h_nodup : (preludeNames hs).Nodup) :
    HoistSimSA (extendFactory := extendFactory)
      (.loop (.det g) none [] body md_s)
      (preludeHavocs hs ++ [.loop (.det g) none [] body₂ md_h])
      (preludeNames hs) := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwf_def hwf_congr hwf_var
    h_src_none h_tgt_none oc ρ_post h_run
  -- (1) run the prelude on the target, establishing the names target-defined.
  obtain ⟨ρ_pre, h_pre_run, h_agree_pre, h_hf_pre, h_eval_pre, h_def_pre⟩ :=
    prelude_runner hs ρ_s ρ_h h_agree h_src_none h_tgt_none h_nodup (h_eval ▸ hwf_var)
  have h_eval_pre_s : ρ_pre.factory = ρ_s.factory := by rw [h_eval_pre, h_eval]
  have h_hf_pre_s : ρ_pre.hasFailure = ρ_s.hasFailure := by rw [h_hf_pre, h_hf]
  -- (2)+(3) feed the loop driver, with D = preludeNames hs.  (4) stitch prelude++loop.
  cases oc with
  | none =>
    simp only [Env.outcomeConfig] at h_run ⊢
    obtain ⟨ρ_post_h, h_loop_run, h_agree', h_hf', h_eval', _⟩ :=
      samenameLoopDetSA_TE (D := preludeNames hs) (g := g) (md_s := md_s) (md_h := md_h)
        body_sim h_src_body_nofd
        h_agree_pre h_eval_pre_s h_hf_pre_s hwfb hwfv hwf_def hwf_congr hwf_var h_def_pre h_run
    exact ⟨ρ_post_h, ReflTrans_Transitive _ _ _ _
      (stmts_prefix_terminal_append P (EvalCmd P) extendFactory _ _ ρ_h ρ_pre h_pre_run)
      (stmt_to_singleton_stmts (extendFactory := extendFactory) _ ρ_pre ρ_post_h h_loop_run),
      h_agree', h_hf', h_eval'⟩
  | some lbl =>
    simp only [Env.outcomeConfig] at h_run ⊢
    obtain ⟨ρ_post_h, h_loop_run, h_agree', h_hf', h_eval', _⟩ :=
      samenameLoopDetSA_E (D := preludeNames hs) (g := g) (md_s := md_s) (md_h := md_h)
        body_sim h_src_body_nofd
        h_agree_pre h_eval_pre_s h_hf_pre_s hwfb hwfv hwf_def hwf_congr hwf_var h_def_pre h_run
    exact ⟨ρ_post_h, ReflTrans_Transitive _ _ _ _
      (stmts_prefix_terminal_append P (EvalCmd P) extendFactory _ _ ρ_h ρ_pre h_pre_run)
      (stmt_to_singleton_stmts_exiting (extendFactory := extendFactory) _ ρ_pre ρ_post_h lbl
          h_loop_run),
      h_agree', h_hf', h_eval'⟩


/-- Generic walker: a `Bool.and`-homomorphic block predicate that is `true` on
every `.cmd` leaf holds on a block synthesised entirely from commands. The
per-predicate `*_map_cmd` corollaries are one-line instances. -/
theorem block_pred_map_cmd_true {P : PureExpr}
    (blockP : List (Stmt P (Cmd P)) → Bool) (stmtP : Stmt P (Cmd P) → Bool)
    (hnil : blockP [] = true)
    (hcons : ∀ s rest, blockP (s :: rest) = (stmtP s && blockP rest))
    (hcmd : ∀ c, stmtP (Stmt.cmd c) = true)
    (cs : List (Cmd P)) :
    blockP (cs.map Stmt.cmd) = true := by
  induction cs with
  | nil => simpa using hnil
  | cons c rest ih => rw [List.map_cons, hcons, hcmd, ih]; rfl

theorem initVars_map_cmd {P : PureExpr} (cs : List (Cmd P)) :
    Block.initVars (cs.map Stmt.cmd) = Cmds.definedVars cs := by
  induction cs with
  | nil => simp [Block.initVars, Cmds.definedVars]
  | cons c rest ih =>
    simp only [List.map_cons, Block.initVars_cons, Cmds.definedVars]
    rw [ih]; congr 1; cases c <;> simp [Stmt.initVars, Cmd.definedVars, HasVarsImp.definedVars]


/-! ## Lift-level init-name membership (iff). -/
mutual
theorem Stmt.liftP_initVars_mem {P : PureExpr} (s : Stmt P (Cmd P)) (y : P.Ident) :
    (y ∈ Cmds.definedVars (Stmt.liftInitsInLoopBody s).1
      ∨ y ∈ Block.initVars (Stmt.liftInitsInLoopBody s).2) ↔ y ∈ Stmt.initVars s := by
  match s with
  | .cmd c =>
      cases c <;>
        simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Cmd.definedVars,
              Block.initVars, Stmt.initVars, HasVarsImp.definedVars]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Stmt.initVars_block, Block.initVars_cons,
        Block.initVars_nil, List.append_nil]
      exact Block.liftP_initVars_mem bss y
  | .ite g tss ess md =>
      have ht := Block.liftP_initVars_mem tss y
      have he := Block.liftP_initVars_mem ess y
      simp only [Stmt.liftInitsInLoopBody, Stmt.initVars_ite, Block.initVars_cons,
        Block.initVars_nil, List.append_nil, List.mem_append, Cmds.definedVars_append] at ht he ⊢
      constructor
      · rintro ((h | h) | (h | h))
        · exact Or.inl (ht.mp (Or.inl h))
        · exact Or.inr (he.mp (Or.inl h))
        · exact Or.inl (ht.mp (Or.inr h))
        · exact Or.inr (he.mp (Or.inr h))
      · rintro (h | h)
        · rcases ht.mpr h with h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inr (Or.inl h')
        · rcases he.mpr h with h' | h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr (Or.inr h')
  | .loop g m inv body md =>
      simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Block.initVars]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Block.initVars, Stmt.initVars]
  | .funcDecl d md =>
      simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Block.initVars, Stmt.initVars]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Block.initVars, Stmt.initVars]
  termination_by sizeOf s

theorem Block.liftP_initVars_mem {P : PureExpr} (ss : List (Stmt P (Cmd P))) (y : P.Ident) :
    (y ∈ Cmds.definedVars (Block.liftInitsInLoopBody ss).1
      ∨ y ∈ Block.initVars (Block.liftInitsInLoopBody ss).2) ↔ y ∈ Block.initVars ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Cmds.definedVars, Block.initVars]
  | s :: rest =>
      have hs := Stmt.liftP_initVars_mem s y
      have hr := Block.liftP_initVars_mem rest y
      simp only [Block.liftInitsInLoopBody, Block.initVars_cons, Cmds.definedVars_append,
        Block.initVars_append, List.mem_append] at hs hr ⊢
      constructor
      · rintro (h | h)
        · rcases h with h' | h'
          · exact Or.inl (hs.mp (Or.inl h'))
          · exact Or.inr (hr.mp (Or.inl h'))
        · rcases h with h' | h'
          · exact Or.inl (hs.mp (Or.inr h'))
          · exact Or.inr (hr.mp (Or.inr h'))
      · rintro (h | h)
        · rcases hs.mpr h with h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inr (Or.inl h')
        · rcases hr.mpr h with h' | h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr (Or.inr h')
  termination_by sizeOf ss
end

/-! ## Hoist-level init-name membership subset. -/
mutual
theorem Stmt.hoistP_initVars_sub {P : PureExpr} (s : Stmt P (Cmd P)) (y : P.Ident)
    (hy : y ∈ Block.initVars (Stmt.hoistLoopPrefixInits s)) : y ∈ Stmt.initVars s := by
  match s with
  | .cmd c =>
      cases c <;> simp_all [Stmt.hoistLoopPrefixInits, Block.initVars, Stmt.initVars,
        Cmd.definedVars, HasVarsImp.definedVars]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Stmt.initVars_block, Block.initVars_cons,
        Block.initVars_nil, List.append_nil] at hy ⊢
      exact Block.hoistP_initVars_sub bss y hy
  | .ite g tss ess md =>
      simp only [Stmt.hoistLoopPrefixInits, Stmt.initVars_ite, Block.initVars_cons,
        Block.initVars_nil, List.append_nil, List.mem_append] at hy ⊢
      rcases hy with h | h
      · exact Or.inl (Block.hoistP_initVars_sub tss y h)
      · exact Or.inr (Block.hoistP_initVars_sub ess y h)
  | .loop g m inv body md =>
      -- hoist = havocs.map .cmd ++ [.loop g m inv body₂ md] where
      -- (havocs, body₂) = lift (hoist body).
      simp only [Stmt.hoistLoopPrefixInits, Block.initVars_append, Block.initVars_cons,
        Stmt.initVars_loop, Block.initVars_nil, List.append_nil, initVars_map_cmd,
        List.mem_append] at hy ⊢
      -- hy : y ∈ defined havocs ∨ y ∈ initVars body₂  (modulo the [loop] singleton)
      have := (Block.liftP_initVars_mem (Block.hoistLoopPrefixInits body) y).mp hy
      exact Block.hoistP_initVars_sub body y this
  | .exit lbl md => simp_all [Stmt.hoistLoopPrefixInits, Block.initVars]
  | .funcDecl d md => simp_all [Stmt.hoistLoopPrefixInits, Block.initVars]
  | .typeDecl t md => simp_all [Stmt.hoistLoopPrefixInits, Block.initVars]
  termination_by sizeOf s

theorem Block.hoistP_initVars_sub {P : PureExpr} (ss : List (Stmt P (Cmd P))) (y : P.Ident)
    (hy : y ∈ Block.initVars (Block.hoistLoopPrefixInits ss)) : y ∈ Block.initVars ss := by
  match ss with
  | [] => simp_all [Block.hoistLoopPrefixInits, Block.initVars]
  | s :: rest =>
      simp only [Block.hoistLoopPrefixInits, Block.initVars_append, Block.initVars_cons,
        List.mem_append] at hy ⊢
      rcases hy with h | h
      · exact Or.inl (Stmt.hoistP_initVars_sub s y h)
      · exact Or.inr (Block.hoistP_initVars_sub rest y h)
  termination_by sizeOf ss
end

/-! ## noFuncDecl is preserved by the same-name lift residual and the hoist. -/
mutual
theorem Stmt.liftP_noFuncDecl_res {P : PureExpr} (s : Stmt P (Cmd P)) (h : Stmt.noFuncDecl s = true)
    :
    Block.noFuncDecl (Stmt.liftInitsInLoopBody s).2 = true := by
  match s with
  | .cmd c => cases c <;> simp [Stmt.liftInitsInLoopBody, Block.noFuncDecl, Stmt.noFuncDecl]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_true]
      exact Block.liftP_noFuncDecl_res bss (by simpa [Stmt.noFuncDecl] using h)
  | .ite g tss ess md =>
      simp only [Stmt.liftInitsInLoopBody, Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_true]
      simp only [Stmt.noFuncDecl, Bool.and_eq_true] at h
      rw [Block.liftP_noFuncDecl_res tss h.1, Block.liftP_noFuncDecl_res ess h.2]; rfl
  | .loop g m inv body md =>
      simp_all [Stmt.liftInitsInLoopBody, Block.noFuncDecl, Stmt.noFuncDecl]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Block.noFuncDecl, Stmt.noFuncDecl]
  | .funcDecl d md => simp [Stmt.noFuncDecl] at h
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBody, Block.noFuncDecl, Stmt.noFuncDecl]
  termination_by sizeOf s

theorem Block.liftP_noFuncDecl_res {P : PureExpr} (ss : List (Stmt P (Cmd P))) (h : Block.noFuncDecl
    ss = true) :
    Block.noFuncDecl (Block.liftInitsInLoopBody ss).2 = true := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Block.noFuncDecl]
  | s :: rest =>
      simp only [Block.noFuncDecl, Bool.and_eq_true] at h
      rw [Block.liftInitsInLoopBody]
      simp only [Block.noFuncDecl_append]
      rw [Stmt.liftP_noFuncDecl_res s h.1, Block.liftP_noFuncDecl_res rest h.2]; rfl
  termination_by sizeOf ss
end

theorem noFuncDecl_map_cmd {P : PureExpr} (cs : List (Cmd P)) :
    Block.noFuncDecl (cs.map (Stmt.cmd : Cmd P → Stmt P (Cmd P))) = true :=
  block_pred_map_cmd_true Block.noFuncDecl Stmt.noFuncDecl (by simp [Block.noFuncDecl])
    (fun _ _ => by simp [Block.noFuncDecl]) (fun _ => by simp [Stmt.noFuncDecl]) cs

mutual
theorem Stmt.hoistP_noFuncDecl {P : PureExpr} (s : Stmt P (Cmd P)) (h : Stmt.noFuncDecl s = true) :
    Block.noFuncDecl (Stmt.hoistLoopPrefixInits s) = true := by
  match s with
  | .cmd c => simp [Stmt.hoistLoopPrefixInits, Block.noFuncDecl, Stmt.noFuncDecl]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_true]
      exact Block.hoistP_noFuncDecl bss (by simpa [Stmt.noFuncDecl] using h)
  | .ite g tss ess md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_true]
      simp only [Stmt.noFuncDecl, Bool.and_eq_true] at h
      rw [Block.hoistP_noFuncDecl tss h.1, Block.hoistP_noFuncDecl ess h.2]; rfl
  | .loop g m inv body md =>
      have h_body : Block.noFuncDecl body = true := by simpa [Stmt.noFuncDecl] using h
      have h_hb : Block.noFuncDecl (Block.hoistLoopPrefixInits body) = true :=
        Block.hoistP_noFuncDecl body h_body
      simp only [Stmt.hoistLoopPrefixInits, Block.noFuncDecl_append]
      rw [noFuncDecl_map_cmd]
      simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.true_and, Bool.and_true]
      exact Block.liftP_noFuncDecl_res (Block.hoistLoopPrefixInits body) h_hb
  | .exit lbl md => simp [Stmt.hoistLoopPrefixInits, Block.noFuncDecl, Stmt.noFuncDecl]
  | .funcDecl d md => simp [Stmt.noFuncDecl] at h
  | .typeDecl t md => simp [Stmt.hoistLoopPrefixInits, Block.noFuncDecl, Stmt.noFuncDecl]
  termination_by sizeOf s

theorem Block.hoistP_noFuncDecl {P : PureExpr} (ss : List (Stmt P (Cmd P))) (h : Block.noFuncDecl ss
    = true) :
    Block.noFuncDecl (Block.hoistLoopPrefixInits ss) = true := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.noFuncDecl]
  | s :: rest =>
      simp only [Block.noFuncDecl, Bool.and_eq_true] at h
      rw [Block.hoistLoopPrefixInits, Block.noFuncDecl_append,
          Stmt.hoistP_noFuncDecl s h.1, Block.hoistP_noFuncDecl rest h.2]; rfl
  termination_by sizeOf ss
end

/-! ## The body-level dual-undef hoist simulation relation. -/
private def BodyHoistSimSA [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    (U : List P.Ident) (body hoist : List (Stmt P (Cmd P))) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    ρ_h.factory = ρ_s.factory → ρ_h.hasFailure = ρ_s.hasFailure →
    StoreAgreement ρ_s.store ρ_h.store →
    WellFormedSemanticEvalBool ρ_s.factory → WellFormedSemanticEvalVal ρ_s.factory →
    WellFormedSemanticEvalMono ρ_s.factory → WellFormedSemanticEvalExprCongr ρ_s.factory →
    WellFormedSemanticEvalVar ρ_s.factory →
    (∀ y ∈ U, ρ_s.store y = none) →
    (∀ y ∈ U, ρ_h.store y = none) →
    (∀ (oc : Option String) (ρ_post : Env P),
      StepStmtStar P (EvalCmd P) extendFactory (.stmts body ρ_s) (Env.outcomeConfig oc ρ_post) →
      ∃ ρ_post_h : Env P,
        StepStmtStar P (EvalCmd P) extendFactory (.stmts hoist ρ_h) (Env.outcomeConfig oc ρ_post_h)
            ∧
        StoreAgreement ρ_post.store ρ_post_h.store ∧
        ρ_post_h.hasFailure = ρ_post.hasFailure ∧ ρ_post_h.factory = ρ_post.factory)

/-- The empty body. -/
private theorem bodyHoistSimSA_nil {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    (U : List P.Ident) :
    BodyHoistSimSA (extendFactory := extendFactory) U [] [] := by
  intro ρ_s ρ_h h_eval h_hf h_agree _ _ _ _ _ _ _ oc ρ_post h_run
  cases oc with
  | none =>
    simp only [Env.outcomeConfig] at h_run ⊢
    have h_eq := stmts_nil_terminal_eq (extendFactory := extendFactory) ρ_s ρ_post h_run
    subst h_eq
    exact ⟨ρ_h, evalStmtsSmallNil P (EvalCmd P) extendFactory ρ_h, h_agree, h_hf, h_eval⟩
  | some lbl =>
    exfalso
    simp only [Env.outcomeConfig] at h_run
    cases h_run with
    | step _ _ _ h1 hr1 => cases h1; cases hr1 with | step _ _ _ hd _ => exact nomatch hd

/-- An identity statement whose hoist is `[s]` and which preserves StoreAgreement
+ eval/hf agreement at any outcome, with no init dependency, inhabits
`HoistSimSA s [s] U` for any `U`. -/
private theorem hoistSimSA_of_identity {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {U : List P.Ident} {s : Stmt P (Cmd P)}
    (h_id : ∀ (ρ_s ρ_h : Env P),
      ρ_h.factory = ρ_s.factory → ρ_h.hasFailure = ρ_s.hasFailure →
      StoreAgreement ρ_s.store ρ_h.store →
      WellFormedSemanticEvalBool ρ_s.factory → WellFormedSemanticEvalVal ρ_s.factory →
      WellFormedSemanticEvalMono ρ_s.factory → WellFormedSemanticEvalExprCongr ρ_s.factory →
      WellFormedSemanticEvalVar ρ_s.factory →
      ∀ (oc : Option String) (ρ_post : Env P),
        StepStmtStar P (EvalCmd P) extendFactory (.stmt s ρ_s) (Env.outcomeConfig oc ρ_post) →
        ∃ ρ_post_h : Env P,
          StepStmtStar P (EvalCmd P) extendFactory (.stmt s ρ_h) (Env.outcomeConfig oc ρ_post_h) ∧
          StoreAgreement ρ_post.store ρ_post_h.store ∧
          ρ_post_h.hasFailure = ρ_post.hasFailure ∧ ρ_post_h.factory = ρ_post.factory) :
    HoistSimSA (extendFactory := extendFactory) s [s] U := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar _ _ oc ρ_post h_run
  obtain ⟨ρ_post_h, h_run_h, h_agree', h_hf', h_eval'⟩ :=
    h_id ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar oc ρ_post h_run
  exact ⟨ρ_post_h, stmt_to_singleton_stmts_outcome (extendFactory := extendFactory) s ρ_h ρ_post_h
      oc h_run_h,
    h_agree', h_hf', h_eval'⟩

/-! ## The cons sequencer. -/
private theorem bodyHoistSimSA_cons {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
        {extendFactory : ExtendFactory P}
    {s : Stmt P (Cmd P)} {rest hoist_s hoist_rest : List (Stmt P (Cmd P))}
    (h_nofd_s : Stmt.noFuncDecl s = true)
    -- the hoist of `s` defines only names in `Stmt.initVars s`:
    (h_hs_def_sub : ∀ y ∈ Block.definedVars (P := P) (C := Cmd P) hoist_s false, y ∈ Stmt.initVars
        s)
    -- head/tail init-name disjointness (from uniqueInits):
    (h_disj : ∀ y ∈ Stmt.initVars s, y ∉ Block.initVars rest)
    (hhead : HoistSimSA (extendFactory := extendFactory) s hoist_s (Stmt.initVars s))
    (htail : BodyHoistSimSA (extendFactory := extendFactory) (Block.initVars rest) rest hoist_rest)
        :
    BodyHoistSimSA (extendFactory := extendFactory)
      (Stmt.initVars s ++ Block.initVars rest) (s :: rest) (hoist_s ++ hoist_rest) := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none oc ρ_post h_run
  -- split the dual-undef premises into head/tail.
  have h_src_none_s : ∀ y ∈ Stmt.initVars s, ρ_s.store y = none := fun y hy =>
    h_src_none y (List.mem_append_left _ hy)
  have h_tgt_none_s : ∀ y ∈ Stmt.initVars s, ρ_h.store y = none := fun y hy =>
    h_tgt_none y (List.mem_append_left _ hy)
  have h_src_none_r : ∀ y ∈ Block.initVars rest, ρ_s.store y = none := fun y hy =>
    h_src_none y (List.mem_append_right _ hy)
  have h_tgt_none_r : ∀ y ∈ Block.initVars rest, ρ_h.store y = none := fun y hy =>
    h_tgt_none y (List.mem_append_right _ hy)
  -- `s` definedVars = initVars s (definitionally: `initVars := definedVars _ false`).
  have h_s_def_eq : Stmt.definedVars (P := P) (C := Cmd P) s false = Stmt.initVars s := rfl
  rcases stmts_cons_outcome (extendFactory := extendFactory) s rest ρ_s ρ_post oc h_run with
    ⟨lbl, h_oc_eq, h_s_exit⟩ | ⟨ρ_mid, h_s_term, h_rest_run⟩
  · -- head exits with `lbl`: whole list exits, tail is skipped.
    subst h_oc_eq
    obtain ⟨ρ_post_h, h_hs_run, h_agree', h_hf', h_eval'⟩ :=
      hhead ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none_s h_tgt_none_s
        (some lbl) ρ_post (by simpa only [Env.outcomeConfig] using h_s_exit)
    refine ⟨ρ_post_h, ?_, h_agree', h_hf', h_eval'⟩
    simp only [Env.outcomeConfig] at h_hs_run ⊢
    exact stmts_cons_head_exiting_append (extendFactory := extendFactory) _ _ ρ_h ρ_post_h lbl
        h_hs_run
  · -- head terminates to ρ_mid, then tail reaches outcome.
    obtain ⟨ρ_h_mid, h_hs_run, h_agree_mid, h_hf_mid, h_eval_mid⟩ :=
      hhead ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none_s h_tgt_none_s
        none ρ_mid (by simpa only [Env.outcomeConfig] using h_s_term)
    -- recover WF at ρ_mid (source) via noFuncDecl eval-preservation.
    have h_eval_mid_src : ρ_mid.factory = ρ_s.factory :=
      smallStep_noFuncDecl_preserves_eval P (EvalCmd P) extendFactory s ρ_s ρ_mid h_nofd_s h_s_term
    have h_eval_eq_mid : ρ_h_mid.factory = ρ_mid.factory := h_eval_mid
    have h_hf_eq_mid : ρ_h_mid.hasFailure = ρ_mid.hasFailure := h_hf_mid
    -- tail-undef of `Block.initVars rest` at ρ_mid (source): `s` defines only initVars s,
    -- which is disjoint from rest's init names; so the `none` slots survive `s`'s run.
    have h_src_none_r_mid : ∀ y ∈ Block.initVars rest, ρ_mid.store y = none := by
      intro y hy
      have h_y_none : ρ_s.store y = none := h_src_none_r y hy
      have h_y_not_def : y ∉ Stmt.definedVars (P := P) (C := Cmd P) s false := by
        rw [h_s_def_eq]; exact fun hc => h_disj y hc hy
      exact Config.varsUndefinedThroughout_star (Q := (· = y)) (extendFactory := extendFactory)
          h_s_term
        (by rintro z rfl; exact ⟨h_y_none, h_y_not_def⟩) y rfl
    -- tail-undef at ρ_h_mid (hoist): `hoist_s` defines only ⊆ initVars s, disjoint from rest.
    have h_tgt_none_r_mid : ∀ y ∈ Block.initVars rest, ρ_h_mid.store y = none := by
      intro y hy
      have h_y_none : ρ_h.store y = none := h_tgt_none_r y hy
      have h_y_not_def : y ∉ Block.definedVars (P := P) (C := Cmd P) hoist_s false := fun hc =>
        h_disj y (h_hs_def_sub y hc) hy
      exact block_run_terminal_preserves_none_of_not_definedVars
        h_y_not_def h_y_none h_hs_run
    obtain ⟨ρ_post_h, h_rest_run_h, h_agree', h_hf', h_eval'⟩ :=
      htail ρ_mid ρ_h_mid h_eval_eq_mid h_hf_eq_mid h_agree_mid
        (h_eval_mid_src ▸ hwfb) (h_eval_mid_src ▸ hwfv) (h_eval_mid_src ▸ hwfd)
        (h_eval_mid_src ▸ hwfc) (h_eval_mid_src ▸ hwfvar) h_src_none_r_mid h_tgt_none_r_mid
        oc ρ_post h_rest_run
    refine ⟨ρ_post_h, ?_, h_agree', h_hf', h_eval'⟩
    -- reassemble: hoist_s terminal then hoist_rest reaches outcome.
    exact ReflTrans_Transitive _ _ _ _
      (stmts_prefix_terminal_append P (EvalCmd P) extendFactory _ _ ρ_h ρ_h_mid h_hs_run)
      h_rest_run_h

/-! ## Bridge: a `StmtSimSA [] s s` identity sim gives `HoistSimSA s [s] U`. -/
private theorem hoistSimSA_of_stmtSimSA_nilD {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {U : List P.Ident} {s : Stmt P (Cmd P)}
    (h : StmtSimSA (extendFactory := extendFactory) ([] : List P.Ident) s s) :
    HoistSimSA (extendFactory := extendFactory) s [s] U := by
  apply hoistSimSA_of_identity
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar oc ρ_post h_run
  have h_def : ∀ y ∈ ([] : List P.Ident), (ρ_h.store y).isSome = true := by
    intro y hy; exact absurd hy (List.not_mem_nil)
  obtain ⟨h_term, h_exit⟩ := h ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_def
  cases oc with
  | none =>
    simp only [Env.outcomeConfig] at h_run ⊢
    obtain ⟨ρ_post_h, h_run_h, h_agree', h_hf', h_eval', _⟩ := h_term ρ_post h_run
    exact ⟨ρ_post_h, h_run_h, h_agree', h_hf', h_eval'⟩
  | some lbl =>
    simp only [Env.outcomeConfig] at h_run ⊢
    obtain ⟨ρ_post_h, h_run_h, h_agree', h_hf', h_eval', _⟩ := h_exit lbl ρ_post h_run
    exact ⟨ρ_post_h, h_run_h, h_agree', h_hf', h_eval'⟩

/-! ## The `.loop` arm: bridge `hoistSimSA_of_sequence` into the body relation.
A source loop `.loop (.det g) none [] body md_s` hoists to
`preludeHavocs hs ++ [.loop ... body₂ md_h]`.  The names dual-undef at entry are
`preludeNames hs = Block.initVars body`.  `hoistSimSA_of_sequence` consumes a body
sim `BodySimSumSA (preludeNames hs) body body₂` which `bodySimBothSA_of_lift`
produces; the prelude havoc-list shape and `preludeNames` come from the lift. -/

/-! ## Lift havocs are all `.nondet`-inits, hence reconstructible as `preludeHavocs hs`. -/
mutual
theorem Stmt.liftP_havocs_nondet {P : PureExpr} (s : Stmt P (Cmd P)) :
    ∀ c ∈ (Stmt.liftInitsInLoopBody s).1, ∃ y ty md, c = Cmd.init y ty .nondet md := by
  match s with
  | .cmd c =>
      intro c' hc
      cases c <;> simp_all [Stmt.liftInitsInLoopBody]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody]
      exact Block.liftP_havocs_nondet bss
  | .ite g tss ess md =>
      intro c hc
      simp only [Stmt.liftInitsInLoopBody, List.mem_append] at hc
      rcases hc with h | h
      · exact Block.liftP_havocs_nondet tss c h
      · exact Block.liftP_havocs_nondet ess c h
  | .loop g m inv body md => intro c hc; simp [Stmt.liftInitsInLoopBody] at hc
  | .exit lbl md => intro c hc; simp [Stmt.liftInitsInLoopBody] at hc
  | .funcDecl d md => intro c hc; simp [Stmt.liftInitsInLoopBody] at hc
  | .typeDecl t md => intro c hc; simp [Stmt.liftInitsInLoopBody] at hc
  termination_by sizeOf s

theorem Block.liftP_havocs_nondet {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    ∀ c ∈ (Block.liftInitsInLoopBody ss).1, ∃ y ty md, c = Cmd.init y ty .nondet md := by
  match ss with
  | [] => intro c hc; simp [Block.liftInitsInLoopBody] at hc
  | s :: rest =>
      intro c hc
      rw [Block.liftInitsInLoopBody] at hc
      simp only [List.mem_append] at hc
      rcases hc with h | h
      · exact Stmt.liftP_havocs_nondet s c h
      · exact Block.liftP_havocs_nondet rest c h
  termination_by sizeOf ss
end

/-- A command list all of whose entries are `.nondet`-inits reconstructs to a
triple list with the matching `preludeHavocs`/`preludeNames`. -/
theorem nondet_cmds_to_prelude {P : PureExpr} (cs : List (Cmd P))
    (h : ∀ c ∈ cs, ∃ y ty md, c = Cmd.init y ty .nondet md) :
    ∃ hs : List (P.Ident × P.Ty × MetaData P),
      cs.map Stmt.cmd = preludeHavocs hs ∧ preludeNames hs = Cmds.definedVars cs := by
  induction cs with
  | nil => exact ⟨[], by simp [preludeHavocs], by simp [preludeNames, Cmds.definedVars]⟩
  | cons c rest ih =>
    obtain ⟨y, ty, md, h_c⟩ := h c (List.mem_cons_self)
    obtain ⟨hs, h_map, h_names⟩ := ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    refine ⟨(y, ty, md) :: hs, ?_, ?_⟩
    · subst h_c
      simp only [List.map_cons, preludeHavocs, List.map_cons] at h_map ⊢
      rw [h_map]
    · subst h_c
      simp only [preludeNames, List.map_cons, Cmds.definedVars, Cmd.definedVars] at h_names ⊢
      rw [h_names]; rfl



/-! ## Converter: Env.outcomeConfig dual-undef body sim → split dual-undef body sim. -/
private theorem bodyDualUndefSA_of_bodyHoistSimSA {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {U : List P.Ident} {body hoist : List (Stmt P (Cmd P))}
    (h : BodyHoistSimSA (extendFactory := extendFactory) U body hoist) :
    BodyDualUndefSA (extendFactory := extendFactory) U body hoist := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none
  have hh := h ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none
  refine ⟨?_, ?_⟩
  · intro ρ_s' h_run
    have := hh none ρ_s' (by simpa only [Env.outcomeConfig] using h_run)
    simpa only [Env.outcomeConfig] using this
  · intro l ρ_s' h_run
    have := hh (some l) ρ_s' (by simpa only [Env.outcomeConfig] using h_run)
    simpa only [Env.outcomeConfig] using this

/-! ## Hoist preserves transportShape / loopBodyNoInits / Nodup of initVars. -/

-- residual `.2` of the same-name lift is noInitsAnywhere when input is loopBodyNoInits.
mutual
theorem Stmt.liftP_res_noInits {P : PureExpr} (s : Stmt P (Cmd P)) (h : Stmt.loopBodyNoInits s =
    true) :
    Block.noInitsAnywhere (Stmt.liftInitsInLoopBody s).2 = true := by
  match s with
  | .cmd c =>
      cases c <;> simp [Stmt.liftInitsInLoopBody, Block.noInitsAnywhere, Stmt.noInitsAnywhere]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Block.noInitsAnywhere, Stmt.noInitsAnywhere,
          Bool.and_true]
      exact Block.liftP_res_noInits bss (by simpa [Stmt.loopBodyNoInits] using h)
  | .ite g tss ess md =>
      simp only [Stmt.loopBodyNoInits, Bool.and_eq_true] at h
      simp only [Stmt.liftInitsInLoopBody, Block.noInitsAnywhere, Stmt.noInitsAnywhere,
          Bool.and_true]
      rw [Block.liftP_res_noInits tss h.1, Block.liftP_res_noInits ess h.2]; rfl
  | .loop g m inv body md =>
      have h_nia : Block.noInitsAnywhere body = true := by
        simp only [Stmt.loopBodyNoInits, Bool.and_eq_true, List.isEmpty_iff] at h
        exact Block.noInitsAnywhere_of_initVars_nil body h.1
      simp [Stmt.liftInitsInLoopBody, Block.noInitsAnywhere, Stmt.noInitsAnywhere, h_nia]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Block.noInitsAnywhere, Stmt.noInitsAnywhere]
  | .funcDecl d md => simp [Stmt.liftInitsInLoopBody, Block.noInitsAnywhere, Stmt.noInitsAnywhere]
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBody, Block.noInitsAnywhere, Stmt.noInitsAnywhere]
  termination_by sizeOf s

theorem Block.liftP_res_noInits {P : PureExpr} (ss : List (Stmt P (Cmd P))) (h :
    Block.loopBodyNoInits ss = true) :
    Block.noInitsAnywhere (Block.liftInitsInLoopBody ss).2 = true := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Block.noInitsAnywhere]
  | s :: rest =>
      simp only [Block.loopBodyNoInits, Bool.and_eq_true] at h
      rw [Block.liftInitsInLoopBody, Block.noInitsAnywhere_append,
          Stmt.liftP_res_noInits s h.1, Block.liftP_res_noInits rest h.2]; rfl
  termination_by sizeOf ss
end

/-! ## transportShape is trivial on `.cmd`-maps, preserved by lift residual.
(`Block.transportShape_append` is proved upstream in `StmtProps`.) -/
theorem Block.transportShape_map_cmd {P : PureExpr} (cs : List (Cmd P)) :
    Block.transportShape (cs.map (Stmt.cmd : Cmd P → Stmt P (Cmd P))) = true :=
  block_pred_map_cmd_true Block.transportShape Stmt.transportShape (by simp [Block.transportShape])
    (fun _ _ => by simp [Block.transportShape])
    (fun c => by
      cases c with
      | init _ _ e _ => cases e <;> simp [Stmt.transportShape]
      | set _ e _ => cases e <;> simp [Stmt.transportShape]
      | assert _ _ _ => simp [Stmt.transportShape]
      | assume _ _ _ => simp [Stmt.transportShape]
      | cover _ _ _ => simp [Stmt.transportShape]) cs

mutual
theorem Stmt.liftP_res_transportShape {P : PureExpr} (s : Stmt P (Cmd P)) (h : Stmt.transportShape s
    = true) :
    Block.transportShape (Stmt.liftInitsInLoopBody s).2 = true := by
  match s with
  | .cmd c =>
      cases c with
      | init _ _ e _ =>
          cases e <;> simp [Stmt.liftInitsInLoopBody, Block.transportShape, Stmt.transportShape]
      | set _ e _ =>
          cases e <;> simp [Stmt.liftInitsInLoopBody, Block.transportShape, Stmt.transportShape]
      | assert _ _ _ => simp [Stmt.liftInitsInLoopBody, Block.transportShape, Stmt.transportShape]
      | assume _ _ _ => simp [Stmt.liftInitsInLoopBody, Block.transportShape, Stmt.transportShape]
      | cover _ _ _ => simp [Stmt.liftInitsInLoopBody, Block.transportShape, Stmt.transportShape]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Block.transportShape, Stmt.transportShape, Bool.and_true]
      exact Block.liftP_res_transportShape bss (by simpa [Stmt.transportShape] using h)
  | .ite g tss ess md =>
      cases g <;>
      · simp only [Stmt.transportShape, Bool.and_eq_true] at h
        simp only [Stmt.liftInitsInLoopBody, Block.transportShape, Stmt.transportShape,
            Bool.and_true]
        rw [Block.liftP_res_transportShape tss h.1, Block.liftP_res_transportShape ess h.2]; rfl
  | .loop g m inv body md =>
      -- a nested loop is passed through verbatim by the lift residual.
      rw [show (Stmt.liftInitsInLoopBody (.loop g m inv body md)).2 = [.loop g m inv body md] by
        rw [Stmt.liftInitsInLoopBody]]
      simpa only [Block.transportShape, Bool.and_true] using h
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Block.transportShape, Stmt.transportShape]
  | .funcDecl d md => exact absurd h (by simp [Stmt.transportShape])
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBody, Block.transportShape, Stmt.transportShape]
  termination_by sizeOf s

theorem Block.liftP_res_transportShape {P : PureExpr} (ss : List (Stmt P (Cmd P))) (h :
    Block.transportShape ss = true) :
    Block.transportShape (Block.liftInitsInLoopBody ss).2 = true := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Block.transportShape]
  | s :: rest =>
      simp only [Block.transportShape, Bool.and_eq_true] at h
      rw [Block.liftInitsInLoopBody, Block.transportShape_append,
          Stmt.liftP_res_transportShape s h.1, Block.liftP_res_transportShape rest h.2]; rfl
  termination_by sizeOf ss
end

/-! ## Hoist preserves transportShape. -/
mutual
theorem Stmt.hoistP_transportShape {P : PureExpr} (s : Stmt P (Cmd P)) (h : Stmt.transportShape s =
    true) :
    Block.transportShape (Stmt.hoistLoopPrefixInits s) = true := by
  match s with
  | .cmd c =>
      cases c <;> simp_all [Stmt.hoistLoopPrefixInits, Block.transportShape, Stmt.transportShape]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.transportShape, Stmt.transportShape,
          Bool.and_true]
      exact Block.hoistP_transportShape bss (by simpa [Stmt.transportShape] using h)
  | .ite g tss ess md =>
      cases g <;>
      · simp only [Stmt.transportShape, Bool.and_eq_true] at h
        simp only [Stmt.hoistLoopPrefixInits, Block.transportShape, Stmt.transportShape,
            Bool.and_true]
        rw [Block.hoistP_transportShape tss h.1, Block.hoistP_transportShape ess h.2]; rfl
  | .loop g m inv body md =>
      -- transportShape forces `.det g`, `m=none`, `inv=[]`.
      cases g with
      | nondet => exact absurd h (by simp [Stmt.transportShape])
      | det g' =>
        cases m with
        | some _ => exact absurd h (by simp [Stmt.transportShape])
        | none =>
          cases inv with
          | cons _ _ => exact absurd h (by simp [Stmt.transportShape])
          | nil =>
            have h_body : Block.transportShape body = true := by
              simpa [Stmt.transportShape] using h
            have h_hb : Block.transportShape (Block.hoistLoopPrefixInits body) = true :=
              Block.hoistP_transportShape body h_body
            simp only [Stmt.hoistLoopPrefixInits, Block.transportShape_append]
            rw [Block.transportShape_map_cmd]
            simp only [Block.transportShape, Stmt.transportShape, Bool.true_and, Bool.and_true]
            exact Block.liftP_res_transportShape (Block.hoistLoopPrefixInits body) h_hb
  | .exit lbl md => simp [Stmt.hoistLoopPrefixInits, Block.transportShape, Stmt.transportShape]
  | .funcDecl d md => exact absurd h (by simp [Stmt.transportShape])
  | .typeDecl t md => simp [Stmt.hoistLoopPrefixInits, Block.transportShape, Stmt.transportShape]
  termination_by sizeOf s

theorem Block.hoistP_transportShape {P : PureExpr} (ss : List (Stmt P (Cmd P))) (h :
    Block.transportShape ss = true) :
    Block.transportShape (Block.hoistLoopPrefixInits ss) = true := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.transportShape]
  | s :: rest =>
      simp only [Block.transportShape, Bool.and_eq_true] at h
      rw [Block.hoistLoopPrefixInits, Block.transportShape_append,
          Stmt.hoistP_transportShape s h.1, Block.hoistP_transportShape rest h.2]; rfl
  termination_by sizeOf ss
end

/-! ## Hoist preserves loopBodyNoInits. -/
mutual
theorem Stmt.liftP_res_allLoop {P : PureExpr} (s : Stmt P (Cmd P)) (h : Stmt.loopBodyNoInits s =
    true) :
    Block.loopBodyNoInits (Stmt.liftInitsInLoopBody s).2 = true := by
  match s with
  | .cmd c =>
      cases c <;> simp [Stmt.liftInitsInLoopBody, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Block.loopBodyNoInits, Stmt.loopBodyNoInits,
          Bool.and_true]
      exact Block.liftP_res_allLoop bss (by simpa [Stmt.loopBodyNoInits] using h)
  | .ite g tss ess md =>
      simp only [Stmt.loopBodyNoInits, Bool.and_eq_true] at h
      simp only [Stmt.liftInitsInLoopBody, Block.loopBodyNoInits, Stmt.loopBodyNoInits,
          Bool.and_true]
      rw [Block.liftP_res_allLoop tss h.1, Block.liftP_res_allLoop ess h.2]; rfl
  | .loop g m inv body md =>
      rw [show (Stmt.liftInitsInLoopBody (.loop g m inv body md)).2 = [.loop g m inv body md] by
        rw [Stmt.liftInitsInLoopBody]]
      simpa only [Block.loopBodyNoInits, Bool.and_true] using h
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  | .funcDecl d md => simp [Stmt.liftInitsInLoopBody, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBody, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  termination_by sizeOf s

theorem Block.liftP_res_allLoop {P : PureExpr} (ss : List (Stmt P (Cmd P))) (h :
    Block.loopBodyNoInits ss = true) :
    Block.loopBodyNoInits (Block.liftInitsInLoopBody ss).2 = true := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Block.loopBodyNoInits]
  | s :: rest =>
      simp only [Block.loopBodyNoInits, Bool.and_eq_true] at h
      rw [Block.liftInitsInLoopBody, Block.loopBodyNoInits_append,
          Stmt.liftP_res_allLoop s h.1, Block.liftP_res_allLoop rest h.2]; rfl
  termination_by sizeOf ss
end

theorem Block.loopBodyNoInits_map_cmd' {P : PureExpr} (cs : List (Cmd P)) :
    Block.loopBodyNoInits (cs.map (Stmt.cmd : Cmd P → Stmt P (Cmd P))) = true :=
  block_pred_map_cmd_true Block.loopBodyNoInits Stmt.loopBodyNoInits
      (by simp [Block.loopBodyNoInits])
    (fun _ _ => by simp [Block.loopBodyNoInits]) (fun _ => by simp [Stmt.loopBodyNoInits]) cs

mutual
theorem Stmt.hoistP_allLoop {P : PureExpr} (s : Stmt P (Cmd P)) (h : Stmt.loopBodyNoInits s = true)
    :
    Block.loopBodyNoInits (Stmt.hoistLoopPrefixInits s) = true := by
  match s with
  | .cmd c => simp [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits, Stmt.loopBodyNoInits,
          Bool.and_true]
      exact Block.hoistP_allLoop bss (by simpa [Stmt.loopBodyNoInits] using h)
  | .ite g tss ess md =>
      simp only [Stmt.loopBodyNoInits, Bool.and_eq_true] at h
      simp only [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits, Stmt.loopBodyNoInits,
          Bool.and_true]
      rw [Block.hoistP_allLoop tss h.1, Block.hoistP_allLoop ess h.2]; rfl
  | .loop g m inv body md =>
      -- hoist = havocs.map .cmd ++ [.loop g m inv body₂ md]; need loopBodyNoInits of the loop arm.
      simp only [Stmt.loopBodyNoInits, Bool.and_eq_true] at h
      have h_body : Block.loopBodyNoInits body = true := h.2
      have h_hb : Block.loopBodyNoInits (Block.hoistLoopPrefixInits body) = true :=
        Block.hoistP_allLoop body h_body
      simp only [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits_append]
      rw [Block.loopBodyNoInits_map_cmd']
      simp only [Block.loopBodyNoInits, Stmt.loopBodyNoInits, Bool.true_and, Bool.and_true,
        Block.isEmpty_initVars_eq_noInitsAnywhere]
      rw [Block.liftP_res_noInits (Block.hoistLoopPrefixInits body) h_hb,
          Block.liftP_res_allLoop (Block.hoistLoopPrefixInits body) h_hb]; rfl
  | .exit lbl md => simp [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  | .funcDecl d md => simp [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  | .typeDecl t md => simp [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  termination_by sizeOf s

theorem Block.hoistP_allLoop {P : PureExpr} (ss : List (Stmt P (Cmd P))) (h : Block.loopBodyNoInits
    ss = true) :
    Block.loopBodyNoInits (Block.hoistLoopPrefixInits ss) = true := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.loopBodyNoInits]
  | s :: rest =>
      simp only [Block.loopBodyNoInits, Bool.and_eq_true] at h
      rw [Block.hoistLoopPrefixInits, Block.loopBodyNoInits_append,
          Stmt.hoistP_allLoop s h.1, Block.hoistP_allLoop rest h.2]; rfl
  termination_by sizeOf ss
end

/-! ## Hoist output is unconditionally `loopBodyNoInits`.

The hoist transformation rewrites every `.loop` body to
`liftInitsInLoopBody (hoistLoopPrefixInits body)`, which lifts all `.init`
commands out of the body and into a havoc prelude. The result therefore has no
`.init` inside any loop body regardless of the source shape: the property holds
of the OUTPUT with no precondition on the input. -/
mutual
theorem Stmt.hoistP_allLoop_uncond {P : PureExpr} (s : Stmt P (Cmd P)) :
    Block.loopBodyNoInits (Stmt.hoistLoopPrefixInits s) = true := by
  match s with
  | .cmd c => simp [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits, Stmt.loopBodyNoInits,
          Bool.and_true]
      exact Block.hoistP_allLoop_uncond bss
  | .ite g tss ess md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits, Stmt.loopBodyNoInits,
          Bool.and_true]
      rw [Block.hoistP_allLoop_uncond tss, Block.hoistP_allLoop_uncond ess]; rfl
  | .loop g m inv body md =>
      -- hoist = havocs.map .cmd ++ [.loop g m inv (lift (hoist body)).2 md];
      -- the lift residual lemmas need loopBodyNoInits (hoist body), supplied by the IH.
      have h_hb : Block.loopBodyNoInits (Block.hoistLoopPrefixInits body) = true :=
        Block.hoistP_allLoop_uncond body
      simp only [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits_append]
      rw [Block.loopBodyNoInits_map_cmd']
      simp only [Block.loopBodyNoInits, Stmt.loopBodyNoInits, Bool.true_and, Bool.and_true,
        Block.isEmpty_initVars_eq_noInitsAnywhere]
      rw [Block.liftP_res_noInits (Block.hoistLoopPrefixInits body) h_hb,
          Block.liftP_res_allLoop (Block.hoistLoopPrefixInits body) h_hb]; rfl
  | .exit lbl md => simp [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  | .funcDecl d md => simp [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  | .typeDecl t md => simp [Stmt.hoistLoopPrefixInits, Block.loopBodyNoInits, Stmt.loopBodyNoInits]
  termination_by sizeOf s

theorem Block.hoistP_allLoop_uncond {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    Block.loopBodyNoInits (Block.hoistLoopPrefixInits ss) = true := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.loopBodyNoInits]
  | s :: rest =>
      rw [Block.hoistLoopPrefixInits, Block.loopBodyNoInits_append,
          Stmt.hoistP_allLoop_uncond s, Block.hoistP_allLoop_uncond rest]; rfl
  termination_by sizeOf ss
end

/-! ## initVars multiset is preserved (List.Perm) by lift and hoist → Nodup transfers. -/

mutual
theorem Stmt.liftP_initVars_perm {P : PureExpr} (s : Stmt P (Cmd P)) :
    List.Perm (Cmds.definedVars (Stmt.liftInitsInLoopBody s).1
      ++ Block.initVars (Stmt.liftInitsInLoopBody s).2) (Stmt.initVars s) := by
  match s with
  | .cmd c =>
      cases c <;>
        simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Cmd.definedVars, Block.initVars,
          Stmt.initVars, HasVarsImp.definedVars]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Stmt.initVars_block, Block.initVars_cons,
        Block.initVars_nil, List.append_nil]
      exact Block.liftP_initVars_perm bss
  | .ite g tss ess md =>
      simp only [Stmt.liftInitsInLoopBody, Stmt.initVars_ite, Block.initVars_cons,
        Block.initVars_nil, List.append_nil, Cmds.definedVars_append]
      have ht := Block.liftP_initVars_perm tss
      have he := Block.liftP_initVars_perm ess
      refine (perm_append_swap_middle _ _ _ _).trans ?_
      exact ht.append he
  | .loop g m inv body md =>
      simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Block.initVars]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Block.initVars, Stmt.initVars]
  | .funcDecl d md =>
      simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Block.initVars, Stmt.initVars]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBody, Cmds.definedVars, Block.initVars, Stmt.initVars]
  termination_by sizeOf s

theorem Block.liftP_initVars_perm {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    List.Perm (Cmds.definedVars (Block.liftInitsInLoopBody ss).1
      ++ Block.initVars (Block.liftInitsInLoopBody ss).2) (Block.initVars ss) := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Cmds.definedVars, Block.initVars]
  | s :: rest =>
      simp only [Block.liftInitsInLoopBody, Cmds.definedVars_append, Block.initVars_append,
        Block.initVars_cons]
      have hs := Stmt.liftP_initVars_perm s
      have hr := Block.liftP_initVars_perm rest
      refine (perm_append_swap_middle _ _ _ _).trans ?_
      exact hs.append hr
  termination_by sizeOf ss
end

mutual
theorem Stmt.hoistP_initVars_perm {P : PureExpr} (s : Stmt P (Cmd P)) :
    List.Perm (Block.initVars (Stmt.hoistLoopPrefixInits s)) (Stmt.initVars s) := by
  match s with
  | .cmd c => cases c <;> simp [Stmt.hoistLoopPrefixInits, Block.initVars, Stmt.initVars,
      Cmd.definedVars, HasVarsImp.definedVars]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Stmt.initVars_block, Block.initVars_cons,
        Block.initVars_nil, List.append_nil]
      exact Block.hoistP_initVars_perm bss
  | .ite g tss ess md =>
      simp only [Stmt.hoistLoopPrefixInits, Stmt.initVars_ite, Block.initVars_cons,
        Block.initVars_nil, List.append_nil]
      exact (Block.hoistP_initVars_perm tss).append (Block.hoistP_initVars_perm ess)
  | .loop g m inv body md =>
      -- initVars (havocs.map .cmd ++ [loop body₂]) = defined havocs ++ initVars body₂
      --   ~ initVars (hoist body) ~ initVars body.
      simp only [Stmt.hoistLoopPrefixInits, Block.initVars_append, Block.initVars_cons,
        Stmt.initVars_loop, Block.initVars_nil, List.append_nil, initVars_map_cmd]
      exact (Block.liftP_initVars_perm (Block.hoistLoopPrefixInits body)).trans
        (Block.hoistP_initVars_perm body)
  | .exit lbl md => simp [Stmt.hoistLoopPrefixInits, Block.initVars, Stmt.initVars]
  | .funcDecl d md => simp [Stmt.hoistLoopPrefixInits, Block.initVars, Stmt.initVars]
  | .typeDecl t md => simp [Stmt.hoistLoopPrefixInits, Block.initVars, Stmt.initVars]
  termination_by sizeOf s

theorem Block.hoistP_initVars_perm {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    List.Perm (Block.initVars (Block.hoistLoopPrefixInits ss)) (Block.initVars ss) := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.initVars]
  | s :: rest =>
      simp only [Block.hoistLoopPrefixInits, Block.initVars_append, Block.initVars_cons]
      exact (Stmt.hoistP_initVars_perm s).append (Block.hoistP_initVars_perm rest)
  termination_by sizeOf ss
end

/-! ## Same-name hoist output shape lemmas (the pipeline-wiring facts).

The same-name pass keeps every loop head (`g`/`m`/`inv`) verbatim and emits the
hoisted body inits as a sibling `.cmd`-havoc prelude, so the shape predicates the
downstream S2U pass consumes are all preserved (or, for `loopBodyNoInits`, newly
established).  Each lemma mirrors the corresponding fresh-name preservation lemma
but is structurally simpler: there is no rename, so the residual is the plain
`liftInitsInLoopBody` output and the havoc prelude is a `.cmd` list. -/

-- The lift's harvested prelude commands are all `.init` havocs, so mapping them to
-- `.cmd` statements contributes no modified variables.
mutual
theorem Stmt.liftP_havocs_modVars_nil {P : PureExpr} (s : Stmt P (Cmd P)) :
    Block.modifiedVars ((Stmt.liftInitsInLoopBody s).1.map
      (Stmt.cmd : Cmd P → Stmt P (Cmd P))) = [] := by
  match s with
  | .cmd c =>
      cases c <;>
        simp [Stmt.liftInitsInLoopBody, Block.modifiedVars, Stmt.modifiedVars,
          HasVarsImp.modifiedVars, Cmd.modifiedVars]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody]
      exact Block.liftP_havocs_modVars_nil bss
  | .ite g tss ess md =>
      simp only [Stmt.liftInitsInLoopBody, List.map_append, Block.modifiedVars_append,
        Block.liftP_havocs_modVars_nil tss, Block.liftP_havocs_modVars_nil ess, List.append_nil]
  | .loop g m inv body md => simp [Stmt.liftInitsInLoopBody, Block.modifiedVars]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Block.modifiedVars]
  | .funcDecl d md => simp [Stmt.liftInitsInLoopBody, Block.modifiedVars]
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBody, Block.modifiedVars]
  termination_by sizeOf s

theorem Block.liftP_havocs_modVars_nil {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    Block.modifiedVars ((Block.liftInitsInLoopBody ss).1.map
      (Stmt.cmd : Cmd P → Stmt P (Cmd P))) = [] := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Block.modifiedVars]
  | s :: rest =>
      simp only [Block.liftInitsInLoopBody, List.map_append, Block.modifiedVars_append,
        Stmt.liftP_havocs_modVars_nil s, Block.liftP_havocs_modVars_nil rest, List.append_nil]
  termination_by sizeOf ss
end

/-! ### `simpleShape` is preserved (same-name). -/
mutual
theorem Stmt.liftP_res_simpleShape {P : PureExpr} (s : Stmt P (Cmd P)) :
    Block.simpleShape (Stmt.liftInitsInLoopBody s).2 = Stmt.simpleShape s := by
  match s with
  | .cmd c => cases c <;> simp [Stmt.liftInitsInLoopBody, Block.simpleShape, Stmt.simpleShape]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Block.simpleShape, Stmt.simpleShape, Bool.and_true]
      exact Block.liftP_res_simpleShape bss
  | .ite g tss ess md =>
      cases g <;>
        simp [Stmt.liftInitsInLoopBody, Block.simpleShape, Stmt.simpleShape,
          Block.liftP_res_simpleShape tss, Block.liftP_res_simpleShape ess]
  | .loop g m inv body md => simp [Stmt.liftInitsInLoopBody, Block.simpleShape]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Block.simpleShape, Stmt.simpleShape]
  | .funcDecl d md => simp [Stmt.liftInitsInLoopBody, Block.simpleShape, Stmt.simpleShape]
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBody, Block.simpleShape, Stmt.simpleShape]
  termination_by sizeOf s

theorem Block.liftP_res_simpleShape {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    Block.simpleShape (Block.liftInitsInLoopBody ss).2 = Block.simpleShape ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Block.simpleShape]
  | s :: rest =>
      rw [Block.liftInitsInLoopBody, Block.simpleShape_append,
          Stmt.liftP_res_simpleShape s, Block.liftP_res_simpleShape rest, Block.simpleShape]
  termination_by sizeOf ss
end

theorem simpleShape_map_cmd' {P : PureExpr} (cs : List (Cmd P)) :
    Block.simpleShape (cs.map (Stmt.cmd : Cmd P → Stmt P (Cmd P))) = true :=
  block_pred_map_cmd_true Block.simpleShape Stmt.simpleShape (by simp [Block.simpleShape])
    (fun _ _ => by simp [Block.simpleShape]) (fun _ => by simp [Stmt.simpleShape]) cs

mutual
theorem Stmt.hoistP_simpleShape {P : PureExpr} (s : Stmt P (Cmd P)) (h : Stmt.simpleShape s = true)
    :
    Block.simpleShape (Stmt.hoistLoopPrefixInits s) = true := by
  match s with
  | .cmd c => simp [Stmt.hoistLoopPrefixInits, Block.simpleShape, Stmt.simpleShape]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.simpleShape, Stmt.simpleShape, Bool.and_true]
      exact Block.hoistP_simpleShape bss (by simpa [Stmt.simpleShape] using h)
  | .ite g tss ess md =>
      cases g with
      | det e =>
          simp only [Stmt.simpleShape, Bool.and_eq_true] at h
          simp only [Stmt.hoistLoopPrefixInits, Block.simpleShape, Stmt.simpleShape, Bool.and_true]
          rw [Block.hoistP_simpleShape tss h.1, Block.hoistP_simpleShape ess h.2]; rfl
      | nondet => exact absurd h (by simp [Stmt.simpleShape])
  | .loop g m inv body md =>
      cases g with
      | nondet => exact absurd h (by simp [Stmt.simpleShape])
      | det g' =>
        have h_body : Block.simpleShape body = true := by
          simpa [Stmt.simpleShape] using h
        have h_hb : Block.simpleShape (Block.hoistLoopPrefixInits body) = true :=
          Block.hoistP_simpleShape body h_body
        simp only [Stmt.hoistLoopPrefixInits, Block.simpleShape_append]
        rw [simpleShape_map_cmd']
        simp only [Block.simpleShape, Stmt.simpleShape, Bool.true_and, Bool.and_true]
        rw [Block.liftP_res_simpleShape (Block.hoistLoopPrefixInits body)]; exact h_hb
  | .exit lbl md => simp [Stmt.hoistLoopPrefixInits, Block.simpleShape, Stmt.simpleShape]
  | .funcDecl d md => simp [Stmt.hoistLoopPrefixInits, Block.simpleShape, Stmt.simpleShape]
  | .typeDecl t md => simp [Stmt.hoistLoopPrefixInits, Block.simpleShape, Stmt.simpleShape]
  termination_by sizeOf s

theorem Block.hoistP_simpleShape {P : PureExpr} (ss : List (Stmt P (Cmd P))) (h : Block.simpleShape
    ss = true) :
    Block.simpleShape (Block.hoistLoopPrefixInits ss) = true := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.simpleShape]
  | s :: rest =>
      simp only [Block.simpleShape, Bool.and_eq_true] at h
      rw [Block.hoistLoopPrefixInits, Block.simpleShape_append,
          Stmt.hoistP_simpleShape s h.1, Block.hoistP_simpleShape rest h.2]; rfl
  termination_by sizeOf ss
end

/-! ### `loopHasNoInvariants` is preserved (same-name; the loop's `inv` is verbatim). -/
mutual
theorem Stmt.liftP_res_loopHasNoInvariants {P : PureExpr} (s : Stmt P (Cmd P)) :
    Block.loopHasNoInvariants (Stmt.liftInitsInLoopBody s).2 = Stmt.loopHasNoInvariants s := by
  match s with
  | .cmd c =>
      cases c <;> simp [Stmt.liftInitsInLoopBody, Block.loopHasNoInvariants,
          Stmt.loopHasNoInvariants]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants,
          Bool.and_true]
      exact Block.liftP_res_loopHasNoInvariants bss
  | .ite g tss ess md =>
      simp [Stmt.liftInitsInLoopBody, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants,
        Block.liftP_res_loopHasNoInvariants tss, Block.liftP_res_loopHasNoInvariants ess]
  | .loop g m inv body md => simp [Stmt.liftInitsInLoopBody, Block.loopHasNoInvariants]
  | .exit lbl md =>
      simp [Stmt.liftInitsInLoopBody, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  | .funcDecl d md =>
      simp [Stmt.liftInitsInLoopBody, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  | .typeDecl t md =>
      simp [Stmt.liftInitsInLoopBody, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  termination_by sizeOf s

theorem Block.liftP_res_loopHasNoInvariants {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    Block.loopHasNoInvariants (Block.liftInitsInLoopBody ss).2 = Block.loopHasNoInvariants ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Block.loopHasNoInvariants]
  | s :: rest =>
      rw [Block.liftInitsInLoopBody, Block.loopHasNoInvariants_append,
          Stmt.liftP_res_loopHasNoInvariants s, Block.liftP_res_loopHasNoInvariants rest,
          Block.loopHasNoInvariants]
  termination_by sizeOf ss
end

theorem loopHasNoInvariants_map_cmd' {P : PureExpr} (cs : List (Cmd P)) :
    Block.loopHasNoInvariants (cs.map (Stmt.cmd : Cmd P → Stmt P (Cmd P))) = true :=
  block_pred_map_cmd_true Block.loopHasNoInvariants Stmt.loopHasNoInvariants
    (by simp [Block.loopHasNoInvariants])
    (fun _ _ => by simp [Block.loopHasNoInvariants])
    (fun _ => by simp [Stmt.loopHasNoInvariants]) cs

mutual
theorem Stmt.hoistP_loopHasNoInvariants {P : PureExpr} (s : Stmt P (Cmd P))
    (h : Stmt.loopHasNoInvariants s = true) :
    Block.loopHasNoInvariants (Stmt.hoistLoopPrefixInits s) = true := by
  match s with
  | .cmd c => simp [Stmt.hoistLoopPrefixInits, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants,
          Bool.and_true]
      exact Block.hoistP_loopHasNoInvariants bss (by simpa [Stmt.loopHasNoInvariants] using h)
  | .ite g tss ess md =>
      simp only [Stmt.loopHasNoInvariants, Bool.and_eq_true] at h
      simp only [Stmt.hoistLoopPrefixInits, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants,
          Bool.and_true]
      rw [Block.hoistP_loopHasNoInvariants tss h.1, Block.hoistP_loopHasNoInvariants ess h.2]; rfl
  | .loop g m inv body md =>
      simp only [Stmt.loopHasNoInvariants, Bool.and_eq_true] at h
      have h_body : Block.loopHasNoInvariants body = true := h.2
      have h_hb : Block.loopHasNoInvariants (Block.hoistLoopPrefixInits body) = true :=
        Block.hoistP_loopHasNoInvariants body h_body
      simp only [Stmt.hoistLoopPrefixInits, Block.loopHasNoInvariants_append]
      rw [loopHasNoInvariants_map_cmd']
      simp only [Block.loopHasNoInvariants, Stmt.loopHasNoInvariants, Bool.true_and, Bool.and_true,
        Bool.and_eq_true]
      have h_res : Block.loopHasNoInvariants
          (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits body)).2 = true := by
        rw [Block.liftP_res_loopHasNoInvariants (Block.hoistLoopPrefixInits body)]; exact h_hb
      exact ⟨h.1, h_res⟩
  | .exit lbl md =>
      simp [Stmt.hoistLoopPrefixInits, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  | .funcDecl d md =>
      simp [Stmt.hoistLoopPrefixInits, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  | .typeDecl t md =>
      simp [Stmt.hoistLoopPrefixInits, Block.loopHasNoInvariants, Stmt.loopHasNoInvariants]
  termination_by sizeOf s

theorem Block.hoistP_loopHasNoInvariants {P : PureExpr} (ss : List (Stmt P (Cmd P)))
    (h : Block.loopHasNoInvariants ss = true) :
    Block.loopHasNoInvariants (Block.hoistLoopPrefixInits ss) = true := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.loopHasNoInvariants]
  | s :: rest =>
      simp only [Block.loopHasNoInvariants, Bool.and_eq_true] at h
      rw [Block.hoistLoopPrefixInits, Block.loopHasNoInvariants_append,
          Stmt.hoistP_loopHasNoInvariants s h.1, Block.hoistP_loopHasNoInvariants rest h.2]; rfl
  termination_by sizeOf ss
end

/-! ### `noMeasureLoops` is preserved (same-name; the loop's `m` is verbatim). -/
mutual
theorem Stmt.liftP_res_noMeasureLoops {P : PureExpr} (s : Stmt P (Cmd P)) :
    Block.noMeasureLoops (Stmt.liftInitsInLoopBody s).2 = Stmt.noMeasureLoops s := by
  match s with
  | .cmd c => cases c <;> simp [Stmt.liftInitsInLoopBody, Block.noMeasureLoops, Stmt.noMeasureLoops]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Block.noMeasureLoops, Stmt.noMeasureLoops, Bool.and_true]
      exact Block.liftP_res_noMeasureLoops bss
  | .ite g tss ess md =>
      simp [Stmt.liftInitsInLoopBody, Block.noMeasureLoops, Stmt.noMeasureLoops,
        Block.liftP_res_noMeasureLoops tss, Block.liftP_res_noMeasureLoops ess]
  | .loop g m inv body md => simp [Stmt.liftInitsInLoopBody, Block.noMeasureLoops]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Block.noMeasureLoops, Stmt.noMeasureLoops]
  | .funcDecl d md => simp [Stmt.liftInitsInLoopBody, Block.noMeasureLoops, Stmt.noMeasureLoops]
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBody, Block.noMeasureLoops, Stmt.noMeasureLoops]
  termination_by sizeOf s

theorem Block.liftP_res_noMeasureLoops {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    Block.noMeasureLoops (Block.liftInitsInLoopBody ss).2 = Block.noMeasureLoops ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Block.noMeasureLoops]
  | s :: rest =>
      rw [Block.liftInitsInLoopBody, Block.noMeasureLoops_append,
          Stmt.liftP_res_noMeasureLoops s, Block.liftP_res_noMeasureLoops rest,
          Block.noMeasureLoops]
  termination_by sizeOf ss
end

theorem noMeasureLoops_map_cmd' {P : PureExpr} (cs : List (Cmd P)) :
    Block.noMeasureLoops (cs.map (Stmt.cmd : Cmd P → Stmt P (Cmd P))) = true :=
  block_pred_map_cmd_true Block.noMeasureLoops Stmt.noMeasureLoops
    (by simp [Block.noMeasureLoops])
    (fun _ _ => by simp [Block.noMeasureLoops])
    (fun _ => by simp [Stmt.noMeasureLoops]) cs

mutual
theorem Stmt.hoistP_noMeasureLoops {P : PureExpr} (s : Stmt P (Cmd P))
    (h : Stmt.noMeasureLoops s = true) :
    Block.noMeasureLoops (Stmt.hoistLoopPrefixInits s) = true := by
  match s with
  | .cmd c => simp [Stmt.hoistLoopPrefixInits, Block.noMeasureLoops, Stmt.noMeasureLoops]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.noMeasureLoops, Stmt.noMeasureLoops,
          Bool.and_true]
      exact Block.hoistP_noMeasureLoops bss (by simpa [Stmt.noMeasureLoops] using h)
  | .ite g tss ess md =>
      simp only [Stmt.noMeasureLoops, Bool.and_eq_true] at h
      simp only [Stmt.hoistLoopPrefixInits, Block.noMeasureLoops, Stmt.noMeasureLoops,
          Bool.and_true]
      rw [Block.hoistP_noMeasureLoops tss h.1, Block.hoistP_noMeasureLoops ess h.2]; rfl
  | .loop g m inv body md =>
      simp only [Stmt.noMeasureLoops, Bool.and_eq_true] at h
      have h_body : Block.noMeasureLoops body = true := h.2
      have h_hb : Block.noMeasureLoops (Block.hoistLoopPrefixInits body) = true :=
        Block.hoistP_noMeasureLoops body h_body
      simp only [Stmt.hoistLoopPrefixInits, Block.noMeasureLoops_append]
      rw [noMeasureLoops_map_cmd']
      simp only [Block.noMeasureLoops, Stmt.noMeasureLoops, Bool.true_and, Bool.and_true,
        Bool.and_eq_true]
      have h_res : Block.noMeasureLoops
          (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits body)).2 = true := by
        rw [Block.liftP_res_noMeasureLoops (Block.hoistLoopPrefixInits body)]; exact h_hb
      exact ⟨h.1, h_res⟩
  | .exit lbl md => simp [Stmt.hoistLoopPrefixInits, Block.noMeasureLoops, Stmt.noMeasureLoops]
  | .funcDecl d md => simp [Stmt.hoistLoopPrefixInits, Block.noMeasureLoops, Stmt.noMeasureLoops]
  | .typeDecl t md => simp [Stmt.hoistLoopPrefixInits, Block.noMeasureLoops, Stmt.noMeasureLoops]
  termination_by sizeOf s

theorem Block.hoistP_noMeasureLoops {P : PureExpr} (ss : List (Stmt P (Cmd P)))
    (h : Block.noMeasureLoops ss = true) :
    Block.noMeasureLoops (Block.hoistLoopPrefixInits ss) = true := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.noMeasureLoops]
  | s :: rest =>
      simp only [Block.noMeasureLoops, Bool.and_eq_true] at h
      rw [Block.hoistLoopPrefixInits, Block.noMeasureLoops_append,
          Stmt.hoistP_noMeasureLoops s h.1, Block.hoistP_noMeasureLoops rest h.2]; rfl
  termination_by sizeOf ss
end

/-! ### `loopBodyNoInits` is established (same-name), unconditionally. -/
theorem Block.hoistP_loopBodyNoInits {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    Block.loopBodyNoInits (Block.hoistLoopPrefixInits ss) = true :=
  Block.hoistP_allLoop_uncond ss

/-! ### `getBlockLabels` is preserved (same-name; no rename, `.cmd` prelude has no labels). -/

mutual
theorem Stmt.liftP_res_getBlockLabels {P : PureExpr} (s : Stmt P (Cmd P)) :
    Block.getBlockLabels (Stmt.liftInitsInLoopBody s).2 = Block.getBlockLabels [s] := by
  match s with
  | .cmd c =>
      cases c <;>
        simp only [Stmt.liftInitsInLoopBody, Block.getBlockLabels_cmd_cons]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Block.getBlockLabels_block_cons,
        Block.liftP_res_getBlockLabels bss]
  | .ite g tss ess md =>
      simp only [Stmt.liftInitsInLoopBody, Block.getBlockLabels_ite_cons,
        Block.liftP_res_getBlockLabels tss, Block.liftP_res_getBlockLabels ess]
  | .loop g m inv body md => rw [Stmt.liftInitsInLoopBody]
  | .exit lbl md => simp [Stmt.liftInitsInLoopBody, Block.getBlockLabels]
  | .funcDecl d md => simp [Stmt.liftInitsInLoopBody, Block.getBlockLabels]
  | .typeDecl t md => simp [Stmt.liftInitsInLoopBody, Block.getBlockLabels]
  termination_by sizeOf s

theorem Block.liftP_res_getBlockLabels {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    Block.getBlockLabels (Block.liftInitsInLoopBody ss).2 = Block.getBlockLabels ss := by
  match ss with
  | [] => simp [Block.liftInitsInLoopBody, Block.getBlockLabels]
  | s :: rest =>
      rw [Block.liftInitsInLoopBody, Block.getBlockLabels_append,
          show (s :: rest) = [s] ++ rest from rfl, Block.getBlockLabels_append,
          Stmt.liftP_res_getBlockLabels s, Block.liftP_res_getBlockLabels rest]
  termination_by sizeOf ss
end

mutual
theorem Stmt.hoistP_getBlockLabels {P : PureExpr} (s : Stmt P (Cmd P)) :
    Block.getBlockLabels (Stmt.hoistLoopPrefixInits s) = Block.getBlockLabels [s] := by
  match s with
  | .cmd c => rw [Stmt.hoistLoopPrefixInits]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.getBlockLabels_block_cons,
        Block.hoistP_getBlockLabels bss]
  | .ite g tss ess md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.getBlockLabels_ite_cons,
        Block.hoistP_getBlockLabels tss, Block.hoistP_getBlockLabels ess]
  | .loop g m inv body md =>
      rw [Stmt.hoistLoopPrefixInits, Block.getBlockLabels_append, Block.getBlockLabels_map_cmd,
          List.nil_append]
      simp only [Block.getBlockLabels_loop_cons,
        Block.liftP_res_getBlockLabels (Block.hoistLoopPrefixInits body),
        Block.hoistP_getBlockLabels body]
  | .exit lbl md => rw [Stmt.hoistLoopPrefixInits]
  | .funcDecl d md => rw [Stmt.hoistLoopPrefixInits]
  | .typeDecl t md => rw [Stmt.hoistLoopPrefixInits]
  termination_by sizeOf s

theorem Block.hoistP_getBlockLabels {P : PureExpr} (ss : List (Stmt P (Cmd P))) :
    Block.getBlockLabels (Block.hoistLoopPrefixInits ss) = Block.getBlockLabels ss := by
  match ss with
  | [] => simp [Block.hoistLoopPrefixInits, Block.getBlockLabels]
  | s :: rest =>
      rw [Block.hoistLoopPrefixInits, Block.getBlockLabels_append,
          show (s :: rest) = [s] ++ rest from rfl, Block.getBlockLabels_append,
          Stmt.hoistP_getBlockLabels s, Block.hoistP_getBlockLabels rest]
  termination_by sizeOf ss
end

/-! ### `modifiedVars` subset (same-name): the output modvars land in the source
`modifiedVars ++ initVars`.  The `.cmd` havoc prelude adds no modvars (all `.init`),
but the lift rewrites a lifted `.init y` to `.set y`, which turns `y` (an original
`initVar`) into a modvar of the residual — hence the `++ initVars` slack. -/
mutual
theorem Stmt.liftP_res_modVars_sub {P : PureExpr} (s : Stmt P (Cmd P)) (y : P.Ident)
    (hy : y ∈ Block.modifiedVars (Stmt.liftInitsInLoopBody s).2) :
    y ∈ Stmt.modifiedVars s ++ Stmt.initVars s := by
  match s with
  | .cmd c =>
      cases c <;> simp_all [Stmt.liftInitsInLoopBody, Block.modifiedVars, Stmt.modifiedVars,
        Stmt.initVars, HasVarsImp.modifiedVars, Cmd.modifiedVars, Cmd.definedVars,
        HasVarsImp.definedVars]
  | .block lbl bss md =>
      simp only [Stmt.liftInitsInLoopBody, Block.modifiedVars, Stmt.modifiedVars,
          Stmt.initVars_block,
        List.append_nil] at hy ⊢
      exact Block.liftP_res_modVars_sub bss y hy
  | .ite g tss ess md =>
      rw [Stmt.liftInitsInLoopBody] at hy
      simp only [Block.modifiedVars, Stmt.modifiedVars, Stmt.initVars_ite, List.append_nil,
        List.mem_append] at hy ⊢
      rcases hy with h | h
      · rcases List.mem_append.mp (Block.liftP_res_modVars_sub tss y h) with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr (Or.inl h')
      · rcases List.mem_append.mp (Block.liftP_res_modVars_sub ess y h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr (Or.inr h')
  | .loop g m inv body md =>
      -- The lift keeps the loop verbatim: residual = [.loop g m inv body md].
      -- So `Block.modifiedVars` of the residual reduces to `Block.modifiedVars body`,
      -- which is exactly `Stmt.modifiedVars (.loop …)`; land in the left disjunct.
      rw [Stmt.liftInitsInLoopBody] at hy
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hy
      simp only [Stmt.modifiedVars, Stmt.initVars_loop, List.mem_append]
      exact Or.inl hy
  | .exit lbl md => simp_all [Stmt.liftInitsInLoopBody, Block.modifiedVars, Stmt.modifiedVars]
  | .funcDecl d md => simp_all [Stmt.liftInitsInLoopBody, Block.modifiedVars, Stmt.modifiedVars]
  | .typeDecl t md => simp_all [Stmt.liftInitsInLoopBody, Block.modifiedVars, Stmt.modifiedVars]
  termination_by sizeOf s

theorem Block.liftP_res_modVars_sub {P : PureExpr} (ss : List (Stmt P (Cmd P))) (y : P.Ident)
    (hy : y ∈ Block.modifiedVars (Block.liftInitsInLoopBody ss).2) :
    y ∈ Block.modifiedVars ss ++ Block.initVars ss := by
  match ss with
  | [] => simp_all [Block.liftInitsInLoopBody, Block.modifiedVars]
  | s :: rest =>
      rw [Block.liftInitsInLoopBody] at hy
      simp only [Block.modifiedVars_append, Block.modifiedVars, Block.initVars_cons,
        List.mem_append] at hy ⊢
      rcases hy with h | h
      · rcases List.mem_append.mp (Stmt.liftP_res_modVars_sub s y h) with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr (Or.inl h')
      · rcases List.mem_append.mp (Block.liftP_res_modVars_sub rest y h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr (Or.inr h')
  termination_by sizeOf ss
end

mutual
theorem Stmt.hoistP_modVars_sub {P : PureExpr} (s : Stmt P (Cmd P)) (y : P.Ident)
    (hy : y ∈ Block.modifiedVars (Stmt.hoistLoopPrefixInits s)) :
    y ∈ Stmt.modifiedVars s ++ Stmt.initVars s := by
  match s with
  | .cmd c =>
      cases c <;> simp_all [Stmt.hoistLoopPrefixInits, Block.modifiedVars, Stmt.modifiedVars,
        Stmt.initVars, HasVarsImp.modifiedVars, Cmd.modifiedVars, Cmd.definedVars,
        HasVarsImp.definedVars]
  | .block lbl bss md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.modifiedVars, Stmt.modifiedVars,
          Stmt.initVars_block,
        List.append_nil] at hy ⊢
      exact Block.hoistP_modVars_sub bss y hy
  | .ite g tss ess md =>
      simp only [Stmt.hoistLoopPrefixInits, Block.modifiedVars, Stmt.modifiedVars,
          Stmt.initVars_ite,
        List.append_nil, List.mem_append] at hy ⊢
      rcases hy with h | h
      · rcases List.mem_append.mp (Block.hoistP_modVars_sub tss y h) with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr (Or.inl h')
      · rcases List.mem_append.mp (Block.hoistP_modVars_sub ess y h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr (Or.inr h')
  | .loop g m inv body md =>
      -- output = havocs.map .cmd ++ [.loop g m inv body₂ md]; modVars havocs = [] (all `.init`).
      -- modVars body₂ ⊆ modVars (hoist body) ++ initVars (hoist body) (residual), then
      --   modVars (hoist body) ⊆ modVars body ++ initVars body (IH) and
      --   initVars (hoist body) ⊆ initVars body (hoistP_initVars_sub).
      -- The loop stmt has modVars = modVars body, initVars = initVars body.
      simp only [Stmt.hoistLoopPrefixInits, Block.modifiedVars_append,
        Block.liftP_havocs_modVars_nil (Block.hoistLoopPrefixInits body),
        List.nil_append, Block.modifiedVars, Stmt.modifiedVars, Stmt.initVars_loop,
        List.append_nil] at hy ⊢
      rw [List.mem_append]
      rcases List.mem_append.mp
          (Block.liftP_res_modVars_sub (Block.hoistLoopPrefixInits body) y (by simpa using hy))
        with h_mv | h_iv
      · rcases List.mem_append.mp (Block.hoistP_modVars_sub body y h_mv) with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
      · exact Or.inr (Block.hoistP_initVars_sub body y h_iv)
  | .exit lbl md => simp_all [Stmt.hoistLoopPrefixInits, Block.modifiedVars, Stmt.modifiedVars]
  | .funcDecl d md => simp_all [Stmt.hoistLoopPrefixInits, Block.modifiedVars, Stmt.modifiedVars]
  | .typeDecl t md => simp_all [Stmt.hoistLoopPrefixInits, Block.modifiedVars, Stmt.modifiedVars]
  termination_by sizeOf s

theorem Block.hoistP_modVars_sub {P : PureExpr} (ss : List (Stmt P (Cmd P))) (y : P.Ident)
    (hy : y ∈ Block.modifiedVars (Block.hoistLoopPrefixInits ss)) :
    y ∈ Block.modifiedVars ss ++ Block.initVars ss := by
  match ss with
  | [] => simp_all [Block.hoistLoopPrefixInits, Block.modifiedVars]
  | s :: rest =>
      simp only [Block.hoistLoopPrefixInits, Block.modifiedVars_append, Block.modifiedVars,
        Block.initVars_cons, List.mem_append] at hy ⊢
      rcases hy with h | h
      · rcases List.mem_append.mp (Stmt.hoistP_modVars_sub s y h) with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr (Or.inl h')
      · rcases List.mem_append.mp (Block.hoistP_modVars_sub rest y h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr (Or.inr h')
  termination_by sizeOf ss
end

/-! ## The `.loop` arm of the fused producer.

Given the loop body's IH `BodyHoistSimSA (Block.initVars body) body (hoist body)` and
the loop body's own preconditions, produce
`HoistSimSA (.loop (.det g) none [] body md) (Stmt.hoistLoopPrefixInits (.loop … body md))
(Block.initVars body)`.

Recipe: (Leg A) the dual-undef driver relates the source loop `.loop … body` to the
intermediate loop `.loop … (hoist body)` (NO prelude), consuming the converted IH; then
(Leg B) `hoistSimSA_of_sequence` relates the intermediate loop to the output
`prelude ++ [.loop … body₂]`, consuming `bodySimBothSA_of_lift (hoist body)`.  The two
legs compose through the TARGET pivot `ρ_h` (refl `StoreAgreement`). -/
private theorem hoistSimSA_loop_arm {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
        [LawfulHasIdent P]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body : List (Stmt P (Cmd P))} {md : MetaData P}
    (ih : BodyHoistSimSA (extendFactory := extendFactory) (Block.initVars body) body
            (Block.hoistLoopPrefixInits body))
    (h_shape : Block.transportShape body = true)
    (h_nofd : Block.noFuncDecl body = true)
    (h_unique : (Block.initVars body).Nodup) :
    HoistSimSA (extendFactory := extendFactory)
      (.loop (.det g) none [] body md)
      (Stmt.hoistLoopPrefixInits (.loop (.det g) none [] body md))
      (Block.initVars body) := by
  -- preconditions on `hoist body`.
  have h_if_hb : Block.loopBodyNoInits (Block.hoistLoopPrefixInits body) = true :=
    Block.hoistP_allLoop_uncond body
  have h_shape_hb : Block.transportShape (Block.hoistLoopPrefixInits body) = true :=
    Block.hoistP_transportShape body h_shape
  have h_nofd_hb : Block.noFuncDecl (Block.hoistLoopPrefixInits body) = true :=
    Block.hoistP_noFuncDecl body h_nofd
  -- the lift of `hoist body`.
  -- residual `body₂` has no inits (precondition), so its initVars are [].
  have h_body₂_nia : Block.noInitsAnywhere (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits
      body)).2 = true :=
    Block.liftP_res_noInits (Block.hoistLoopPrefixInits body) h_if_hb
  -- `defD`: every defined var of `hoist body` is in `D := Cmds.definedVars
  -- (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits body)).1`.
  have h_defD : ∀ y ∈ Block.definedVars (P := P) (C := Cmd P) (Block.hoistLoopPrefixInits body)
      false,
      y ∈ Cmds.definedVars (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits body)).1 := by
    intro y hy
    rcases (Block.liftP_initVars_mem (Block.hoistLoopPrefixInits body) y).mpr hy with h | h
    · exact h
    · -- y ∈ initVars body₂, but body₂ has no inits → []
      rw [Block.initVars_eq_nil_of_noInitsAnywhere (Block.liftInitsInLoopBody
          (Block.hoistLoopPrefixInits body)).2 h_body₂_nia] at h
      exact absurd h (List.not_mem_nil)
  -- the lift body sim for the intermediate loop.
  have h_lift_sim : BodySimSumSA (extendFactory := extendFactory) (Cmds.definedVars
      (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits body)).1)
      (Block.hoistLoopPrefixInits body) (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits
          body)).2 :=
    (bodySimBothSA_of_lift (D := Cmds.definedVars (Block.liftInitsInLoopBody
        (Block.hoistLoopPrefixInits body)).1) (Block.hoistLoopPrefixInits body)
      h_if_hb h_shape_hb h_nofd_hb h_defD).1
  -- reconstruct the prelude triples from the (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits
  -- body)).1.
  obtain ⟨hs, h_map, h_names⟩ := nondet_cmds_to_prelude (Block.liftInitsInLoopBody
      (Block.hoistLoopPrefixInits body)).1
    (Block.liftP_havocs_nondet (Block.hoistLoopPrefixInits body))
  -- D = preludeNames hs = Cmds.definedVars (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits
  -- body)).1.
  rw [← h_names] at h_lift_sim
  -- Cmds.definedVars (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits body)).1 ~ initVars
  -- (hoist body) (body₂ inits empty) ~ initVars body.
  have h_perm : List.Perm (Cmds.definedVars (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits
      body)).1) (Block.initVars body) := by
    have hL := Block.liftP_initVars_perm (Block.hoistLoopPrefixInits body)
    rw [Block.initVars_eq_nil_of_noInitsAnywhere (Block.liftInitsInLoopBody
        (Block.hoistLoopPrefixInits body)).2 h_body₂_nia, List.append_nil] at hL
    exact hL.trans (Block.hoistP_initVars_perm body)
  have h_pn_sub : ∀ y ∈ preludeNames hs, y ∈ Block.initVars body := by
    intro y hy; rw [h_names] at hy; exact h_perm.mem_iff.mp hy
  -- leg B: hoistSimSA_of_sequence at the intermediate loop.
  have h_legB : HoistSimSA (extendFactory := extendFactory)
      (.loop (.det g) none [] (Block.hoistLoopPrefixInits body) md)
      (preludeHavocs hs ++ [.loop (.det g) none [] (Block.liftInitsInLoopBody
          (Block.hoistLoopPrefixInits body)).2 md])
      (preludeNames hs) := by
    refine hoistSimSA_of_sequence (md_s := md) (md_h := md) h_lift_sim h_nofd_hb ?_
    rw [h_names]
    exact h_perm.nodup_iff.mpr h_unique
  -- the actual hoist output equals `preludeHavocs hs ++ [.loop … body₂ md]`.
  have h_out : Stmt.hoistLoopPrefixInits (.loop (.det g) none [] body md)
      = preludeHavocs hs ++ [.loop (.det g) none [] (Block.liftInitsInLoopBody
          (Block.hoistLoopPrefixInits body)).2 md] := by
    rw [show Stmt.hoistLoopPrefixInits (.loop (.det g) none [] body md)
          = (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits body)).1.map Stmt.cmd ++ [.loop
              (.det g) none [] (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits body)).2 md]
              by
        rw [Stmt.hoistLoopPrefixInits]]
    rw [h_map]
  rw [h_out]
  -- now compose leg A (dual-undef driver) and leg B through the target pivot.
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none oc ρ_post h_run
  -- Leg A: relate source loop to intermediate loop `.loop … (hoist body)`.
  have h_iA : BodyDualUndefSA (extendFactory := extendFactory) (Block.initVars body) body
      (Block.hoistLoopPrefixInits body) := bodyDualUndefSA_of_bodyHoistSimSA ih
  cases oc with
  | none =>
    simp only [Env.outcomeConfig] at h_run ⊢
    obtain ⟨ρ_A, h_runA, h_agreeA, h_hfA, h_evalA⟩ :=
      dualUndefLoopDetSA_TE (g := g) (md_s := md) (md_h := md) h_iA h_nofd
        h_agree h_eval h_hf hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none h_run
    -- Leg B at (ρ_h, ρ_h) with refl.
    have h_pivot_none : ∀ y ∈ preludeNames hs, ρ_h.store y = none := fun y hy =>
      h_tgt_none y (h_pn_sub y hy)
    have h_legB' := h_legB ρ_h ρ_h rfl rfl (StoreAgreement.refl _)
      (h_eval ▸ hwfb) (h_eval ▸ hwfv) (h_eval ▸ hwfd) (h_eval ▸ hwfc) (h_eval ▸ hwfvar)
      h_pivot_none h_pivot_none
    obtain ⟨ρ_B, h_runB, h_agreeB, h_hfB, h_evalB⟩ := h_legB' none ρ_A
      (by simpa only [Env.outcomeConfig] using h_runA)
    refine ⟨ρ_B, by simpa only [Env.outcomeConfig] using h_runB, ?_, ?_, ?_⟩
    · exact StoreAgreement.trans h_agreeA h_agreeB
    · rw [h_hfB, h_hfA]
    · rw [h_evalB, h_evalA]
  | some lbl =>
    simp only [Env.outcomeConfig] at h_run ⊢
    obtain ⟨ρ_A, h_runA, h_agreeA, h_hfA, h_evalA⟩ :=
      dualUndefLoopDetSA_E (g := g) (md_s := md) (md_h := md) h_iA h_nofd
        h_agree h_eval h_hf hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none h_run
    have h_pivot_none : ∀ y ∈ preludeNames hs, ρ_h.store y = none := fun y hy =>
      h_tgt_none y (h_pn_sub y hy)
    have h_legB' := h_legB ρ_h ρ_h rfl rfl (StoreAgreement.refl _)
      (h_eval ▸ hwfb) (h_eval ▸ hwfv) (h_eval ▸ hwfd) (h_eval ▸ hwfc) (h_eval ▸ hwfvar)
      h_pivot_none h_pivot_none
    obtain ⟨ρ_B, h_runB, h_agreeB, h_hfB, h_evalB⟩ := h_legB' (some lbl) ρ_A
      (by simpa only [Env.outcomeConfig] using h_runA)
    refine ⟨ρ_B, by simpa only [Env.outcomeConfig] using h_runB, ?_, ?_, ?_⟩
    · exact StoreAgreement.trans h_agreeA h_agreeB
    · rw [h_hfB, h_hfA]
    · rw [h_evalB, h_evalA]

/-! ## The `.cmd` head sim (identity; consumes the dual-undef premise for `init`). -/
private theorem hoistSimSA_cmd {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    {extendFactory : ExtendFactory P} {U : List P.Ident} (c : Cmd P)
    (h_sub : ∀ x ∈ Cmd.definedVars c, x ∈ U) :
    HoistSimSA (extendFactory := extendFactory) (.cmd c) [.cmd c] U := by
  intro ρ_s ρ_h h_eval h_hf h_agree _ _ hwfd _ _ _ h_tgt_none oc ρ_post h_run
  have h_init_undef : ∀ x ∈ Cmd.definedVars c, ρ_h.store x = none := fun x hx =>
    h_tgt_none x (h_sub x hx)
  cases oc with
  | none =>
    simp only [Env.outcomeConfig] at h_run ⊢
    obtain ⟨ρ_post_h, h_run_h, h_agree', h_hf', h_eval'⟩ :=
      cmd_replay_agreement_storeAgree (extendFactory := extendFactory) c ρ_s ρ_post ρ_h
        h_eval h_hf h_agree hwfd h_init_undef h_run
    exact ⟨ρ_post_h, stmt_to_singleton_stmts (extendFactory := extendFactory) _ ρ_h ρ_post_h
        h_run_h,
      h_agree', h_hf', h_eval'⟩
  | some lbl =>
    -- a single `.cmd` cannot reach `.exiting`.
    exfalso
    simp only [Env.outcomeConfig] at h_run
    cases h_run with
    | step _ _ _ h1 hr1 => cases h1; cases hr1 with | step _ _ _ hd _ => exact nomatch hd

/-! ## The `.block` dual-undef arm. -/
private theorem hoistSimSA_block {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {U : List P.Ident} {lbl : String} {inner inner_h : List (Stmt P (Cmd P))} {md : MetaData P}
    (inner_sim : BodyHoistSimSA (extendFactory := extendFactory) U inner inner_h) :
    HoistSimSA (extendFactory := extendFactory) (.block lbl inner md) [.block lbl inner_h md] U :=
        by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none oc ρ_post h_run
  -- peel the block: `.stmt (.block lbl inner md) ρ → .block (some lbl) ρ.store (.stmts inner ρ)`.
  have peel : StepStmtStar P (EvalCmd P) extendFactory
      (.block (.some lbl) ρ_s.store ρ_s.factory (.stmts inner ρ_s)) (Env.outcomeConfig oc ρ_post) :=
          by
    cases oc <;>
    · simp only [Env.outcomeConfig] at h_run ⊢
      cases h_run with
      | step _ _ _ h1 hr1 => cases h1; exact hr1
  cases oc with
  | none =>
    rcases block_some_reaches_terminal P (EvalCmd P) extendFactory peel with
      ⟨ρ_inner, h_inner_term, h_eq⟩ | ⟨ρ_inner, h_inner_exit, h_eq⟩
    · obtain ⟨ρ_h_inner, h_inner_h_run, h_agree_inner, h_hf_inner, h_eval_inner⟩ :=
        inner_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none
          none ρ_inner (by simpa only [Env.outcomeConfig] using h_inner_term)
      refine ⟨{ ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store,
                               factory := ρ_h.factory }, ?_, ?_, ?_, ?_⟩
      · simp only [Env.outcomeConfig]
        refine .step _ _ _ .step_stmts_cons ?_
        refine ReflTrans_Transitive _ _ _ _ (seq_inner_star P (EvalCmd P) extendFactory _ _ []
          (.step _ _ _ StepStmt.step_block (block_inner_star P (EvalCmd P) extendFactory _ _ (some
              lbl) ρ_h.store ρ_h.factory
            (show StepStmtStar P (EvalCmd P) extendFactory (.stmts inner_h ρ_h) (.terminal
                ρ_h_inner) from h_inner_h_run)))) ?_
        refine .step _ _ _ (.step_seq_inner StepStmt.step_block_done) ?_
        exact .step _ _ _ StepStmt.step_seq_done (.step _ _ _ StepStmt.step_stmts_nil (.refl _))
      · subst h_eq; exact StoreAgreement.of_projectStore_parents h_agree h_agree_inner
      · subst h_eq; show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf_inner
      · subst h_eq; show ρ_h.factory = ρ_s.factory; exact h_eval
    · -- inner exits with `lbl`, the block matches → block terminates.
      obtain ⟨ρ_h_inner, h_inner_h_run, h_agree_inner, h_hf_inner, h_eval_inner⟩ :=
        inner_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none
          (some lbl) ρ_inner (by simpa only [Env.outcomeConfig] using h_inner_exit)
      refine ⟨{ ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store,
                               factory := ρ_h.factory }, ?_, ?_, ?_, ?_⟩
      · simp only [Env.outcomeConfig]
        refine .step _ _ _ .step_stmts_cons ?_
        refine ReflTrans_Transitive _ _ _ _ (seq_inner_star P (EvalCmd P) extendFactory _ _ []
          (.step _ _ _ StepStmt.step_block (block_inner_star P (EvalCmd P) extendFactory _ _ (some
              lbl) ρ_h.store ρ_h.factory
            (show StepStmtStar P (EvalCmd P) extendFactory (.stmts inner_h ρ_h) (.exiting lbl
                ρ_h_inner) from h_inner_h_run)))) ?_
        refine .step _ _ _ (.step_seq_inner (StepStmt.step_block_exit_match rfl)) ?_
        exact .step _ _ _ StepStmt.step_seq_done (.step _ _ _ StepStmt.step_stmts_nil (.refl _))
      · subst h_eq; exact StoreAgreement.of_projectStore_parents h_agree h_agree_inner
      · subst h_eq; show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf_inner
      · subst h_eq; show ρ_h.factory = ρ_s.factory; exact h_eval
  | some l =>
    obtain ⟨h_ne, ρ_inner, h_inner_exit, h_eq⟩ :=
      block_reaches_exiting_strong P (EvalCmd P) extendFactory peel
    obtain ⟨ρ_h_inner, h_inner_h_run, h_agree_inner, h_hf_inner, h_eval_inner⟩ :=
      inner_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none
        (some l) ρ_inner (by simpa only [Env.outcomeConfig] using h_inner_exit)
    refine ⟨{ ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store,
                             factory := ρ_h.factory }, ?_, ?_, ?_, ?_⟩
    · simp only [Env.outcomeConfig]
      refine .step _ _ _ .step_stmts_cons ?_
      refine ReflTrans_Transitive _ _ _ _ (seq_inner_star P (EvalCmd P) extendFactory _ _ []
        (.step _ _ _ StepStmt.step_block (block_inner_star P (EvalCmd P) extendFactory _ _ (some
            lbl) ρ_h.store ρ_h.factory
          (show StepStmtStar P (EvalCmd P) extendFactory (.stmts inner_h ρ_h) (.exiting l ρ_h_inner)
              from h_inner_h_run)))) ?_
      exact .step _ _ _ (.step_seq_inner (StepStmt.step_block_exit_mismatch (fun h => h_ne
          (Option.some.inj h)))) (.step _ _ _ StepStmt.step_seq_exit (.refl _))
    · subst h_eq; exact StoreAgreement.of_projectStore_parents h_agree h_agree_inner
    · subst h_eq; show ρ_h_inner.hasFailure = ρ_inner.hasFailure; exact h_hf_inner
    · subst h_eq; show ρ_h.factory = ρ_s.factory; exact h_eval

/-! ## Monotonicity of `BodyHoistSimSA` in the undef-set `U` (larger U = more premises). -/
private theorem bodyHoistSimSA_weaken {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {U U' : List P.Ident} {body hoist : List (Stmt P (Cmd P))}
    (h_sub : ∀ y ∈ U', y ∈ U)
    (h : BodyHoistSimSA (extendFactory := extendFactory) U' body hoist) :
    BodyHoistSimSA (extendFactory := extendFactory) U body hoist := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none
  exact h ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar
    (fun y hy => h_src_none y (h_sub y hy)) (fun y hy => h_tgt_none y (h_sub y hy))

/-! ## The `.ite` dual-undef arm (det guard). -/
private theorem hoistSimSA_ite {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {U : List P.Ident} {g : P.Expr} {tss tss_h ess ess_h : List (Stmt P (Cmd P))} {md : MetaData P}
    (then_sim : BodyHoistSimSA (extendFactory := extendFactory) U tss tss_h)
    (else_sim : BodyHoistSimSA (extendFactory := extendFactory) U ess ess_h) :
    HoistSimSA (extendFactory := extendFactory) (.ite (.det g) tss ess md)
      [.ite (.det g) tss_h ess_h md] U := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none oc ρ_post h_run
  -- guard transport via StoreAgreement.
  have guard_h : ∀ {bv : P.Expr}, P.eval ρ_s.factory ρ_s.store g = .some bv → P.eval ρ_h.factory
      ρ_h.store g = .some bv := by
    intro bv hg
    rw [h_eval]
    exact hwfd g bv ρ_s.store ρ_h.store
      (storeAgreement_supplies_mono_premise ρ_s.store ρ_h.store h_agree) hg
  -- peel the ite: a run picks a branch (scoped via `.block .none`).
  have peel : (P.eval ρ_s.factory ρ_s.store g = .some HasBool.tt ∧ WellFormedSemanticEvalBool
      ρ_s.factory ∧
        ∃ ρ_inner, StepStmtStar P (EvalCmd P) extendFactory (.stmts tss ρ_s) (Env.outcomeConfig oc
            ρ_inner) ∧
          ρ_post = { ρ_inner with store := projectStore ρ_s.store ρ_inner.store,
                                  factory := ρ_s.factory }) ∨
      (P.eval ρ_s.factory ρ_s.store g = .some HasBool.ff ∧ WellFormedSemanticEvalBool ρ_s.factory ∧
        ∃ ρ_inner, StepStmtStar P (EvalCmd P) extendFactory (.stmts ess ρ_s) (Env.outcomeConfig oc
            ρ_inner) ∧
          ρ_post = { ρ_inner with store := projectStore ρ_s.store ρ_inner.store,
                                  factory := ρ_s.factory }) := by
    cases oc <;>
    · simp only [Env.outcomeConfig] at h_run
      cases h_run with
      | step _ _ _ h1 hr1 =>
        cases h1 with
        | step_ite_true hg hwf =>
            exact .inl ⟨hg, hwf, blockT_none_reaches_outcome (extendFactory := extendFactory) hr1⟩
        | step_ite_false hg hwf =>
            exact .inr ⟨hg, hwf, blockT_none_reaches_outcome (extendFactory := extendFactory) hr1⟩
  rcases peel with ⟨hg, hwf, ρ_inner, h_branch, h_eq⟩ | ⟨hg, hwf, ρ_inner, h_branch, h_eq⟩
  · obtain ⟨ρ_post_h, h_branch_h, h_agree', h_hf', h_eval'⟩ :=
      then_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none oc
          ρ_inner h_branch
    subst h_eq
    refine ⟨{ ρ_post_h with store := projectStore ρ_h.store ρ_post_h.store,
                            factory := ρ_h.factory }, ?_,
      StoreAgreement.of_projectStore_parents h_agree h_agree', ?_, ?_⟩
    · refine stmt_to_singleton_stmts_outcome (extendFactory := extendFactory) _ ρ_h _ oc ?_
      exact .step _ _ _ (StepStmt.step_ite_true (guard_h hg) (h_eval ▸ hwf))
        (blockT_none_build_outcome (extendFactory := extendFactory) _ ρ_h.store ρ_h.factory oc
            ρ_post_h h_branch_h)
    · show ρ_post_h.hasFailure = ρ_inner.hasFailure; exact h_hf'
    · show ρ_h.factory = ρ_s.factory; exact h_eval
  · obtain ⟨ρ_post_h, h_branch_h, h_agree', h_hf', h_eval'⟩ :=
      else_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none oc
          ρ_inner h_branch
    subst h_eq
    refine ⟨{ ρ_post_h with store := projectStore ρ_h.store ρ_post_h.store,
                            factory := ρ_h.factory }, ?_,
      StoreAgreement.of_projectStore_parents h_agree h_agree', ?_, ?_⟩
    · refine stmt_to_singleton_stmts_outcome (extendFactory := extendFactory) _ ρ_h _ oc ?_
      exact .step _ _ _ (StepStmt.step_ite_false (guard_h hg) (h_eval ▸ hwf))
        (blockT_none_build_outcome (extendFactory := extendFactory) _ ρ_h.store ρ_h.factory oc
            ρ_post_h h_branch_h)
    · show ρ_post_h.hasFailure = ρ_inner.hasFailure; exact h_hf'
    · show ρ_h.factory = ρ_s.factory; exact h_eval

/-! ## The `.ite` dual-undef arm (nondet guard). -/
private theorem hoistSimSA_ite_nondet {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {U : List P.Ident} {tss tss_h ess ess_h : List (Stmt P (Cmd P))} {md : MetaData P}
    (then_sim : BodyHoistSimSA (extendFactory := extendFactory) U tss tss_h)
    (else_sim : BodyHoistSimSA (extendFactory := extendFactory) U ess ess_h) :
    HoistSimSA (extendFactory := extendFactory) (.ite .nondet tss ess md)
      [.ite .nondet tss_h ess_h md] U := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none oc ρ_post h_run
  have peel : (∃ ρ_inner, StepStmtStar P (EvalCmd P) extendFactory (.stmts tss ρ_s)
      (Env.outcomeConfig oc ρ_inner) ∧
        ρ_post = { ρ_inner with store := projectStore ρ_s.store ρ_inner.store,
                                factory := ρ_s.factory }) ∨
      (∃ ρ_inner, StepStmtStar P (EvalCmd P) extendFactory (.stmts ess ρ_s) (Env.outcomeConfig oc
          ρ_inner) ∧
        ρ_post = { ρ_inner with store := projectStore ρ_s.store ρ_inner.store,
                                factory := ρ_s.factory }) := by
    cases oc <;>
    · simp only [Env.outcomeConfig] at h_run
      cases h_run with
      | step _ _ _ h1 hr1 =>
        cases h1 with
        | step_ite_nondet_true =>
            exact .inl (blockT_none_reaches_outcome (extendFactory := extendFactory) hr1)
        | step_ite_nondet_false =>
            exact .inr (blockT_none_reaches_outcome (extendFactory := extendFactory) hr1)
  rcases peel with ⟨ρ_inner, h_branch, h_eq⟩ | ⟨ρ_inner, h_branch, h_eq⟩
  · obtain ⟨ρ_post_h, h_branch_h, h_agree', h_hf', h_eval'⟩ :=
      then_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none oc
          ρ_inner h_branch
    subst h_eq
    refine ⟨{ ρ_post_h with store := projectStore ρ_h.store ρ_post_h.store,
                            factory := ρ_h.factory }, ?_,
      StoreAgreement.of_projectStore_parents h_agree h_agree', ?_, ?_⟩
    · refine stmt_to_singleton_stmts_outcome (extendFactory := extendFactory) _ ρ_h _ oc ?_
      exact .step _ _ _ StepStmt.step_ite_nondet_true
        (blockT_none_build_outcome (extendFactory := extendFactory) _ ρ_h.store ρ_h.factory oc
            ρ_post_h h_branch_h)
    · show ρ_post_h.hasFailure = ρ_inner.hasFailure; exact h_hf'
    · show ρ_h.factory = ρ_s.factory; exact h_eval
  · obtain ⟨ρ_post_h, h_branch_h, h_agree', h_hf', h_eval'⟩ :=
      else_sim ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none oc
          ρ_inner h_branch
    subst h_eq
    refine ⟨{ ρ_post_h with store := projectStore ρ_h.store ρ_post_h.store,
                            factory := ρ_h.factory }, ?_,
      StoreAgreement.of_projectStore_parents h_agree h_agree', ?_, ?_⟩
    · refine stmt_to_singleton_stmts_outcome (extendFactory := extendFactory) _ ρ_h _ oc ?_
      exact .step _ _ _ StepStmt.step_ite_nondet_false
        (blockT_none_build_outcome (extendFactory := extendFactory) _ ρ_h.store ρ_h.factory oc
            ρ_post_h h_branch_h)
    · show ρ_post_h.hasFailure = ρ_inner.hasFailure; exact h_hf'
    · show ρ_h.factory = ρ_s.factory; exact h_eval

/-! ## The structural mutual producer. -/
mutual
private theorem Stmt.hoistP_sim {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
        [LawfulHasIdent P]
    {extendFactory : ExtendFactory P} (s : Stmt P (Cmd P))
    (h_shape : Stmt.transportShape s = true)
    (h_nofd : Stmt.noFuncDecl s = true)
    (h_unique : (Stmt.initVars s).Nodup) :
    HoistSimSA (extendFactory := extendFactory) s (Stmt.hoistLoopPrefixInits s) (Stmt.initVars s) :=
        by
  match s, h_shape, h_nofd, h_unique with
  | .cmd c, _, _, _ =>
      rw [show Stmt.hoistLoopPrefixInits (.cmd c) = [.cmd c] by rw [Stmt.hoistLoopPrefixInits]]
      refine hoistSimSA_cmd c ?_
      cases c <;> simp_all [Cmd.definedVars, Stmt.initVars, HasVarsImp.definedVars]
  | .block lbl bss md, h_shape, h_nofd, h_unique =>
      rw [show Stmt.hoistLoopPrefixInits (.block lbl bss md)
            = [.block lbl (Block.hoistLoopPrefixInits bss) md] by rw [Stmt.hoistLoopPrefixInits]]
      rw [Stmt.initVars_block]
      exact hoistSimSA_block (Block.hoistP_sim (extendFactory := extendFactory) bss
        (by simpa [Stmt.transportShape] using h_shape)
        (by simpa [Stmt.noFuncDecl] using h_nofd)
        (by simpa only [Stmt.initVars_block] using h_unique))
  | .ite (.det g) tss ess md, h_shape, h_nofd, h_unique =>
      rw [show Stmt.hoistLoopPrefixInits (.ite (.det g) tss ess md)
            = [.ite (.det g) (Block.hoistLoopPrefixInits tss) (Block.hoistLoopPrefixInits ess) md]
                by
          rw [Stmt.hoistLoopPrefixInits]]
      rw [Stmt.initVars_ite]
      obtain ⟨h_sh_t, h_sh_e⟩ : Block.transportShape tss = true ∧ Block.transportShape ess = true :=
          by
        simpa [Stmt.transportShape, Bool.and_eq_true] using h_shape
      obtain ⟨h_nf_t, h_nf_e⟩ : Block.noFuncDecl tss = true ∧ Block.noFuncDecl ess = true := by
        simpa [Stmt.noFuncDecl, Bool.and_eq_true] using h_nofd
      have h_uni : (Block.initVars tss ++ Block.initVars ess).Nodup := by
        simpa only [Stmt.initVars_ite] using h_unique
      have h_uni_t : (Block.initVars tss).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_e : (Block.initVars ess).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_t := Block.hoistP_sim (extendFactory := extendFactory) tss h_sh_t h_nf_t h_uni_t
      have h_e := Block.hoistP_sim (extendFactory := extendFactory) ess h_sh_e h_nf_e h_uni_e
      exact hoistSimSA_ite
        (bodyHoistSimSA_weaken (fun y hy => List.mem_append_left _ hy) h_t)
        (bodyHoistSimSA_weaken (fun y hy => List.mem_append_right _ hy) h_e)
  | .ite .nondet tss ess md, h_shape, h_nofd, h_unique =>
      rw [show Stmt.hoistLoopPrefixInits (.ite .nondet tss ess md)
            = [.ite .nondet (Block.hoistLoopPrefixInits tss) (Block.hoistLoopPrefixInits ess) md] by
          rw [Stmt.hoistLoopPrefixInits]]
      rw [Stmt.initVars_ite]
      obtain ⟨h_sh_t, h_sh_e⟩ : Block.transportShape tss = true ∧ Block.transportShape ess = true :=
          by
        simpa [Stmt.transportShape, Bool.and_eq_true] using h_shape
      obtain ⟨h_nf_t, h_nf_e⟩ : Block.noFuncDecl tss = true ∧ Block.noFuncDecl ess = true := by
        simpa [Stmt.noFuncDecl, Bool.and_eq_true] using h_nofd
      have h_uni : (Block.initVars tss ++ Block.initVars ess).Nodup := by
        simpa only [Stmt.initVars_ite] using h_unique
      have h_uni_t : (Block.initVars tss).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_e : (Block.initVars ess).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_t := Block.hoistP_sim (extendFactory := extendFactory) tss h_sh_t h_nf_t h_uni_t
      have h_e := Block.hoistP_sim (extendFactory := extendFactory) ess h_sh_e h_nf_e h_uni_e
      exact hoistSimSA_ite_nondet
        (bodyHoistSimSA_weaken (fun y hy => List.mem_append_left _ hy) h_t)
        (bodyHoistSimSA_weaken (fun y hy => List.mem_append_right _ hy) h_e)
  | .loop (.det g) none [] body md, h_shape, h_nofd, h_unique =>
      rw [Stmt.initVars_loop]
      have h_sh_b : Block.transportShape body = true := by simpa [Stmt.transportShape] using h_shape
      have h_nf_b : Block.noFuncDecl body = true := by simpa [Stmt.noFuncDecl] using h_nofd
      have h_uni_b : (Block.initVars body).Nodup := by simpa only [Stmt.initVars_loop] using
          h_unique
      exact hoistSimSA_loop_arm (Block.hoistP_sim (extendFactory := extendFactory) body h_sh_b
          h_nf_b h_uni_b)
        h_sh_b h_nf_b h_uni_b
  | .exit lbl md, _, _, _ =>
      rw [show Stmt.hoistLoopPrefixInits (.exit lbl md) = [.exit lbl md] by
          rw [Stmt.hoistLoopPrefixInits]]
      exact hoistSimSA_of_stmtSimSA_nilD (exit_stmtSimSA lbl md)
  | .typeDecl tc md, _, _, _ =>
      rw [show Stmt.hoistLoopPrefixInits (.typeDecl tc md) = [.typeDecl tc md] by
          rw [Stmt.hoistLoopPrefixInits]]
      exact hoistSimSA_of_stmtSimSA_nilD (typeDecl_stmtSimSA tc md)
  -- excluded by transportShape / noFuncDecl:
  | .loop (.det g) (some me) inv body md, h_shape, _, _ =>
      exact absurd h_shape (by simp [Stmt.transportShape])
  | .loop (.det g) none (i :: inv) body md, h_shape, _, _ =>
      exact absurd h_shape (by simp [Stmt.transportShape])
  | .loop .nondet m inv body md, h_shape, _, _ =>
      exact absurd h_shape (by simp [Stmt.transportShape])
  | .funcDecl d md, _, h_nofd, _ => exact absurd h_nofd (by simp [Stmt.noFuncDecl])
  termination_by sizeOf s

private theorem Block.hoistP_sim {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
        [LawfulHasIdent P]
    {extendFactory : ExtendFactory P} (ss : List (Stmt P (Cmd P)))
    (h_shape : Block.transportShape ss = true)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_unique : (Block.initVars ss).Nodup) :
    BodyHoistSimSA (extendFactory := extendFactory) (Block.initVars ss) ss
        (Block.hoistLoopPrefixInits ss) := by
  match ss, h_shape, h_nofd, h_unique with
  | [], _, _, _ =>
      rw [show Block.hoistLoopPrefixInits ([] : List (Stmt P (Cmd P))) = [] by
          rw [Block.hoistLoopPrefixInits]]
      rw [show Block.initVars ([] : List (Stmt P (Cmd P))) = [] from Block.initVars_nil]
      exact bodyHoistSimSA_nil []
  | s :: rest, h_shape, h_nofd, h_unique =>
      rw [show Block.hoistLoopPrefixInits (s :: rest)
            = Stmt.hoistLoopPrefixInits s ++ Block.hoistLoopPrefixInits rest by
                rw [Block.hoistLoopPrefixInits]]
      rw [Block.initVars_cons]
      obtain ⟨h_sh_s, h_sh_r⟩ : Stmt.transportShape s = true ∧ Block.transportShape rest = true :=
          by
        simpa [Block.transportShape, Bool.and_eq_true] using h_shape
      obtain ⟨h_nf_s, h_nf_r⟩ : Stmt.noFuncDecl s = true ∧ Block.noFuncDecl rest = true := by
        simpa [Block.noFuncDecl, Bool.and_eq_true] using h_nofd
      have h_uni : (Stmt.initVars s ++ Block.initVars rest).Nodup := by
        rw [← Block.initVars_cons]; exact h_unique
      have h_uni_s : (Stmt.initVars s).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_r : (Block.initVars rest).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_disj : ∀ y ∈ Stmt.initVars s, y ∉ Block.initVars rest := by
        have := (List.nodup_append.mp h_uni).2.2
        intro y hy_s hy_r; exact this y hy_s y hy_r rfl
      have hhead := Stmt.hoistP_sim (extendFactory := extendFactory) s h_sh_s h_nf_s h_uni_s
      have htail := Block.hoistP_sim (extendFactory := extendFactory) rest h_sh_r h_nf_r h_uni_r
      -- the hoist of `s` defines only names in `Stmt.initVars s`.
      have h_hs_def_sub : ∀ y ∈ Block.definedVars (P := P) (C := Cmd P) (Stmt.hoistLoopPrefixInits
          s) false,
          y ∈ Stmt.initVars s := by
        intro y hy
        exact Stmt.hoistP_initVars_sub s y hy
      exact bodyHoistSimSA_cons h_nf_s h_hs_def_sub h_disj hhead htail
  termination_by sizeOf ss
end

/-- **The fused same-name hoist producer.**  The source body `body` and
its same-name hoist `Block.hoistLoopPrefixInits body` are related by the body-level
dual-undefinedness `StoreAgreement` simulation `BodyHoistSimSA`, carrying the
dual-undefinedness of every init name (`Block.initVars body`) at entry, under the
genuine `.loop`-arm Bool preconditions (`loopBodyNoInits`, `transportShape`,
`noFuncDecl`) and `uniqueInits` (`Nodup` of init names).  This is the structural
producer the `.loop` arm consumes: no fresh names, no rename, no `subst`, no pivot
through an intermediate `body₁`. -/
private theorem hoistSimSA_of_hoist {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
        [LawfulHasIdent P]
    {extendFactory : ExtendFactory P} (body : List (Stmt P (Cmd P)))
    (h_shape : Block.transportShape body = true)
    (h_nofd : Block.noFuncDecl body = true)
    (h_unique : Block.uniqueInits body) :
    BodyHoistSimSA (extendFactory := extendFactory) (Block.initVars body) body
      (Block.hoistLoopPrefixInits body) :=
  Block.hoistP_sim (extendFactory := extendFactory) body h_shape h_nofd h_unique


/-! ## The FAILING-config same-name hoist simulation (the `CanFail` arm).

`HoistSimFailSA` / `BodyHoistSimFailSA` are the failing-config analogues of
`HoistSimSA` / `BodyHoistSimSA`: a source run that reaches a *failing* config (which
need not be any completed outcome — a non-terminating loop can still fail mid-run) is
matched by a hoist run that reaches a failing config too.  No `StoreAgreement` / eval /
hf re-establishment at the failing point.  The premises mirror the terminal
dual-undef shape (`U`-undef on both source and target).  This arm's loop arm,
structural mutual, and public producer carry NO `loopBodyNoInits` precondition —
the output `loopBodyNoInits` fact is supplied unconditionally by
`Block.hoistP_allLoop_uncond`. -/
private def HoistSimFailSA [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    (s : Stmt P (Cmd P)) (hoist : List (Stmt P (Cmd P)))
    (names : List P.Ident) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    ρ_h.factory = ρ_s.factory → ρ_h.hasFailure = ρ_s.hasFailure →
    StoreAgreement ρ_s.store ρ_h.store →
    WellFormedSemanticEvalBool ρ_s.factory → WellFormedSemanticEvalVal ρ_s.factory →
    WellFormedSemanticEvalMono ρ_s.factory → WellFormedSemanticEvalExprCongr ρ_s.factory →
    WellFormedSemanticEvalVar ρ_s.factory →
    (∀ y ∈ names, ρ_s.store y = none) →
    (∀ y ∈ names, ρ_h.store y = none) →
    (∀ (d : Config P (Cmd P)),
      StepStmtStar P (EvalCmd P) extendFactory (.stmt s ρ_s) d →
      d.getEnv.hasFailure = true →
      ∃ d', StepStmtStar P (EvalCmd P) extendFactory (.stmts hoist ρ_h) d'
        ∧ d'.getEnv.hasFailure = true)

private def BodyHoistSimFailSA [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    (U : List P.Ident) (body hoist : List (Stmt P (Cmd P))) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    ρ_h.factory = ρ_s.factory → ρ_h.hasFailure = ρ_s.hasFailure →
    StoreAgreement ρ_s.store ρ_h.store →
    WellFormedSemanticEvalBool ρ_s.factory → WellFormedSemanticEvalVal ρ_s.factory →
    WellFormedSemanticEvalMono ρ_s.factory → WellFormedSemanticEvalExprCongr ρ_s.factory →
    WellFormedSemanticEvalVar ρ_s.factory →
    (∀ y ∈ U, ρ_s.store y = none) →
    (∀ y ∈ U, ρ_h.store y = none) →
    (∀ (d : Config P (Cmd P)),
      StepStmtStar P (EvalCmd P) extendFactory (.stmts body ρ_s) d →
      d.getEnv.hasFailure = true →
      ∃ d', StepStmtStar P (EvalCmd P) extendFactory (.stmts hoist ρ_h) d'
        ∧ d'.getEnv.hasFailure = true)

/-- Converter: a `BodyHoistSimFailSA U body hoist` (dual-undef premises) is a
`BodyDualUndefFailSA U body hoist` — the slot Leg-A failing (`dualUndefLoopDetSA_F_fuel`)
consumes. -/
private theorem bodyDualUndefFailSA_of_bodyHoistSimFailSA {P : PureExpr} [HasFvar P] [HasFvars P]
    [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendFactory : ExtendFactory P} {U : List P.Ident} {body hoist : List (Stmt P (Cmd P))}
    (h : BodyHoistSimFailSA (extendFactory := extendFactory) U body hoist) :
    BodyDualUndefFailSA (extendFactory := extendFactory) U body hoist := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none d h_run hd_fail
  exact h ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none d h_run
      hd_fail

/-- **The FAILING sequencer.**  Failing analogue of `hoistSimSA_of_sequence`, over the
asymmetric `D`-defined failing driver `samenameLoopDetSA_F`.  Runs the prelude on the
target (terminal, never fails), feeds the source loop's failing run into the
`D`-defined failing loop driver (consuming both the terminal `BodySimSumSA` and the
failing `BodySimSumFailSA`), then stitches `prelude ++ loop` via
`stmts_prefix_terminal_append` and a `.step step_stmts_cons` failing prepend. -/
private theorem hoistSimFailSA_of_sequence {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body body₂ : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {hs : List (P.Ident × P.Ty × MetaData P)}
    (body_sim : BodySimSumSA (extendFactory := extendFactory) (preludeNames hs) body body₂)
    (body_sim_fail : BodySimSumFailSA (extendFactory := extendFactory) (preludeNames hs) body body₂)
    (h_src_body_nofd : Block.noFuncDecl body = true)
    (h_nodup : (preludeNames hs).Nodup) :
    HoistSimFailSA (extendFactory := extendFactory)
      (.loop (.det g) none [] body md_s)
      (preludeHavocs hs ++ [.loop (.det g) none [] body₂ md_h])
      (preludeNames hs) := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwf_def hwf_congr hwf_var
    h_src_none h_tgt_none a' h_run h_a'_fail
  obtain ⟨ρ_pre, h_pre_run, h_agree_pre, h_hf_pre, h_eval_pre, h_def_pre⟩ :=
    prelude_runner hs ρ_s ρ_h h_agree h_src_none h_tgt_none h_nodup (h_eval ▸ hwf_var)
  have h_eval_pre_s : ρ_pre.factory = ρ_s.factory := by rw [h_eval_pre, h_eval]
  have h_hf_pre_s : ρ_pre.hasFailure = ρ_s.hasFailure := by rw [h_hf_pre, h_hf]
  obtain ⟨d_loop, h_loop_run, hd_loop_fail⟩ :=
    samenameLoopDetSA_F (D := preludeNames hs) (g := g) (md_s := md_s) (md_h := md_h)
      body_sim body_sim_fail h_src_body_nofd
      h_agree_pre h_eval_pre_s h_hf_pre_s hwfb hwfv hwf_def hwf_congr hwf_var h_def_pre h_run
      h_a'_fail
  have h_loop_stmts : StepStmtStar P (EvalCmd P) extendFactory
      (.stmts [.loop (.det g) none [] body₂ md_h] ρ_pre)
      (.seq d_loop ([] : List (Stmt P (Cmd P)))) :=
    .step _ _ _ StepStmt.step_stmts_cons
      (seq_inner_star P (EvalCmd P) extendFactory _ _ _ h_loop_run)
  refine ⟨.seq d_loop ([] : List (Stmt P (Cmd P))),
    ReflTrans_Transitive _ _ _ _
      (stmts_prefix_terminal_append P (EvalCmd P) extendFactory _ _ ρ_h ρ_pre h_pre_run)
      h_loop_stmts, ?_⟩
  simpa [Config.getEnv] using hd_loop_fail

/-! ## The FAILING `.loop` arm: compose Leg A failing ∘ Leg B failing
through the target pivot, mirroring `hoistSimSA_loop_arm`.  No `loopBodyNoInits`
precondition; the output initfree fact is `Block.hoistP_allLoop_uncond`. -/
private theorem hoistSimFailSA_loop_arm {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
        [LawfulHasIdent P]
    {extendFactory : ExtendFactory P}
    {g : P.Expr} {body : List (Stmt P (Cmd P))} {md : MetaData P}
    (ih : BodyHoistSimSA (extendFactory := extendFactory) (Block.initVars body) body
            (Block.hoistLoopPrefixInits body))
    (ih_fail : BodyHoistSimFailSA (extendFactory := extendFactory) (Block.initVars body) body
            (Block.hoistLoopPrefixInits body))
    (h_shape : Block.transportShape body = true)
    (h_nofd : Block.noFuncDecl body = true)
    (h_unique : (Block.initVars body).Nodup) :
    HoistSimFailSA (extendFactory := extendFactory)
      (.loop (.det g) none [] body md)
      (Stmt.hoistLoopPrefixInits (.loop (.det g) none [] body md))
      (Block.initVars body) := by
  -- preconditions on `hoist body` (initfree is UNCONDITIONAL).
  have h_if_hb : Block.loopBodyNoInits (Block.hoistLoopPrefixInits body) = true :=
    Block.hoistP_allLoop_uncond body
  have h_shape_hb : Block.transportShape (Block.hoistLoopPrefixInits body) = true :=
    Block.hoistP_transportShape body h_shape
  have h_nofd_hb : Block.noFuncDecl (Block.hoistLoopPrefixInits body) = true :=
    Block.hoistP_noFuncDecl body h_nofd
  have h_body₂_nia : Block.noInitsAnywhere (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits
      body)).2 = true :=
    Block.liftP_res_noInits (Block.hoistLoopPrefixInits body) h_if_hb
  have h_defD : ∀ y ∈ Block.definedVars (P := P) (C := Cmd P) (Block.hoistLoopPrefixInits body)
      false,
      y ∈ Cmds.definedVars (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits body)).1 := by
    intro y hy
    rcases (Block.liftP_initVars_mem (Block.hoistLoopPrefixInits body) y).mpr hy with h | h
    · exact h
    · rw [Block.initVars_eq_nil_of_noInitsAnywhere (Block.liftInitsInLoopBody
        (Block.hoistLoopPrefixInits body)).2 h_body₂_nia] at h
      exact absurd h (List.not_mem_nil)
  -- one combined walk yields both the terminal and failing lift sims.
  obtain ⟨h_lift_sim, h_lift_sim_fail⟩ :=
    bodySimBothSA_of_lift (D := Cmds.definedVars (Block.liftInitsInLoopBody
        (Block.hoistLoopPrefixInits body)).1) (Block.hoistLoopPrefixInits body)
      h_if_hb h_shape_hb h_nofd_hb h_defD
  obtain ⟨hs, h_map, h_names⟩ := nondet_cmds_to_prelude (Block.liftInitsInLoopBody
      (Block.hoistLoopPrefixInits body)).1
    (Block.liftP_havocs_nondet (Block.hoistLoopPrefixInits body))
  rw [← h_names] at h_lift_sim h_lift_sim_fail
  have h_perm : List.Perm (Cmds.definedVars (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits
      body)).1) (Block.initVars body) := by
    have hL := Block.liftP_initVars_perm (Block.hoistLoopPrefixInits body)
    rw [Block.initVars_eq_nil_of_noInitsAnywhere (Block.liftInitsInLoopBody
        (Block.hoistLoopPrefixInits body)).2 h_body₂_nia, List.append_nil] at hL
    exact hL.trans (Block.hoistP_initVars_perm body)
  have h_pn_sub : ∀ y ∈ preludeNames hs, y ∈ Block.initVars body := by
    intro y hy; rw [h_names] at hy; exact h_perm.mem_iff.mp hy
  have h_legB : HoistSimFailSA (extendFactory := extendFactory)
      (.loop (.det g) none [] (Block.hoistLoopPrefixInits body) md)
      (preludeHavocs hs ++ [.loop (.det g) none [] (Block.liftInitsInLoopBody
          (Block.hoistLoopPrefixInits body)).2 md])
      (preludeNames hs) := by
    refine hoistSimFailSA_of_sequence (md_s := md) (md_h := md) h_lift_sim h_lift_sim_fail
        h_nofd_hb ?_
    rw [h_names]
    exact h_perm.nodup_iff.mpr h_unique
  have h_out : Stmt.hoistLoopPrefixInits (.loop (.det g) none [] body md)
      = preludeHavocs hs ++ [.loop (.det g) none [] (Block.liftInitsInLoopBody
          (Block.hoistLoopPrefixInits body)).2 md] := by
    rw [show Stmt.hoistLoopPrefixInits (.loop (.det g) none [] body md)
          = (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits body)).1.map Stmt.cmd ++ [.loop
              (.det g) none [] (Block.liftInitsInLoopBody (Block.hoistLoopPrefixInits body)).2 md]
              by
        rw [Stmt.hoistLoopPrefixInits]]
    rw [h_map]
  rw [h_out]
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none a' h_run
      h_a'_fail
  have h_iA_fail : BodyDualUndefFailSA (extendFactory := extendFactory) (Block.initVars body) body
      (Block.hoistLoopPrefixInits body) := bodyDualUndefFailSA_of_bodyHoistSimFailSA ih_fail
  have h_iA : BodyDualUndefSA (extendFactory := extendFactory) (Block.initVars body) body
      (Block.hoistLoopPrefixInits body) := bodyDualUndefSA_of_bodyHoistSimSA ih
  obtain ⟨ρ_A, h_runA, hρ_A_fail⟩ :=
    dualUndefLoopDetSA_F_fuel (g := g) (md_s := md) (md_h := md) h_iA h_iA_fail h_nofd
      (reflTrans_to_T h_run).len h_agree h_eval h_hf hwfb hwfv hwfd hwfc hwfvar h_src_none
          h_tgt_none
      (reflTrans_to_T h_run) h_a'_fail (Nat.le_refl _)
  have h_pivot_none : ∀ y ∈ preludeNames hs, ρ_h.store y = none := fun y hy =>
    h_tgt_none y (h_pn_sub y hy)
  have h_legB' := h_legB ρ_h ρ_h rfl rfl (StoreAgreement.refl _)
    (h_eval ▸ hwfb) (h_eval ▸ hwfv) (h_eval ▸ hwfd) (h_eval ▸ hwfc) (h_eval ▸ hwfvar)
    h_pivot_none h_pivot_none
  exact h_legB' ρ_A h_runA hρ_A_fail

/-- Monotonicity of `BodyHoistSimFailSA` in the undef-set (larger set = more premises). -/
private theorem bodyHoistSimFailSA_weaken {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {U U' : List P.Ident} {body hoist : List (Stmt P (Cmd P))}
    (h_sub : ∀ y ∈ U', y ∈ U)
    (h : BodyHoistSimFailSA (extendFactory := extendFactory) U' body hoist) :
    BodyHoistSimFailSA (extendFactory := extendFactory) U body hoist := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none
  exact h ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar
    (fun y hy => h_src_none y (h_sub y hy)) (fun y hy => h_tgt_none y (h_sub y hy))

/-- A nil body cannot fail mid-run.  Mirrors `bodyHoistSimSA_nil` at the failing level. -/
private theorem bodyHoistSimFailSA_nil {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    (U : List P.Ident) :
    BodyHoistSimFailSA (extendFactory := extendFactory) U [] [] := by
  intro ρ_s ρ_h h_eval h_hf h_agree _ _ _ _ _ _ _ d h_run hd_fail
  have h_d_env : d.getEnv = ρ_s := by
    cases h_run with
    | refl => rfl
    | step _ _ _ h_step h_rest =>
      cases h_step with
      | step_stmts_nil =>
        have := reflTransT_from_terminal P extendFactory (reflTrans_to_T h_rest)
        rw [this]; rfl
  have hρ : ρ_s.hasFailure = true := by rw [h_d_env] at hd_fail; simpa [Config.getEnv] using hd_fail
  exact ⟨.terminal ρ_h, evalStmtsSmallNil P (EvalCmd P) extendFactory ρ_h,
    by simpa [Config.getEnv] using (h_hf ▸ hρ)⟩

/-- The FAILING cons sequencer. -/
private theorem bodyHoistSimFailSA_cons {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
        {extendFactory : ExtendFactory P}
    {s : Stmt P (Cmd P)} {rest hoist_s hoist_rest : List (Stmt P (Cmd P))}
    (h_nofd_s : Stmt.noFuncDecl s = true)
    (h_hs_def_sub : ∀ y ∈ Block.definedVars (P := P) (C := Cmd P) hoist_s false, y ∈ Stmt.initVars
        s)
    (h_disj : ∀ y ∈ Stmt.initVars s, y ∉ Block.initVars rest)
    (hhead_term : HoistSimSA (extendFactory := extendFactory) s hoist_s (Stmt.initVars s))
    (hhead_fail : HoistSimFailSA (extendFactory := extendFactory) s hoist_s (Stmt.initVars s))
    (htail_fail : BodyHoistSimFailSA (extendFactory := extendFactory) (Block.initVars rest) rest
        hoist_rest) :
    BodyHoistSimFailSA (extendFactory := extendFactory)
      (Stmt.initVars s ++ Block.initVars rest) (s :: rest) (hoist_s ++ hoist_rest) := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none d h_run hd_fail
  have h_src_none_s : ∀ y ∈ Stmt.initVars s, ρ_s.store y = none := fun y hy =>
    h_src_none y (List.mem_append_left _ hy)
  have h_tgt_none_s : ∀ y ∈ Stmt.initVars s, ρ_h.store y = none := fun y hy =>
    h_tgt_none y (List.mem_append_left _ hy)
  have h_src_none_r : ∀ y ∈ Block.initVars rest, ρ_s.store y = none := fun y hy =>
    h_src_none y (List.mem_append_right _ hy)
  have h_tgt_none_r : ∀ y ∈ Block.initVars rest, ρ_h.store y = none := fun y hy =>
    h_tgt_none y (List.mem_append_right _ hy)
  have h_s_def_eq : Stmt.definedVars (P := P) (C := Cmd P) s false = Stmt.initVars s := rfl
  rcases stmts_cons_reaches_failing' P extendFactory (reflTrans_to_T h_run) hd_fail with
    ⟨d_head, h_head_run, hd_head⟩ | ⟨ρ_mid, d_rest, h_head_term, h_rest_run, hd_rest⟩
  · obtain ⟨d', h_head_h_run, hd'_fail⟩ :=
      hhead_fail ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none_s h_tgt_none_s
        d_head h_head_run hd_head
    obtain ⟨c', h_run', hc'_fail⟩ :=
      stmts_prefix_failing_append P extendFactory hoist_s hoist_rest ρ_h d'
        h_head_h_run hd'_fail
    exact ⟨c', h_run', hc'_fail⟩
  · obtain ⟨ρ_h_mid, h_hs_run, h_agree_mid, h_hf_mid, h_eval_mid⟩ :=
      hhead_term ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none_s h_tgt_none_s
        none ρ_mid (by simpa only [Env.outcomeConfig] using h_head_term)
    have h_eval_mid_src : ρ_mid.factory = ρ_s.factory :=
      smallStep_noFuncDecl_preserves_eval P (EvalCmd P) extendFactory s ρ_s ρ_mid h_nofd_s
          h_head_term
    have h_src_none_r_mid : ∀ y ∈ Block.initVars rest, ρ_mid.store y = none := by
      intro y hy
      have h_y_none : ρ_s.store y = none := h_src_none_r y hy
      have h_y_not_def : y ∉ Stmt.definedVars (P := P) (C := Cmd P) s false := by
        rw [h_s_def_eq]; exact fun hc => h_disj y hc hy
      exact Config.varsUndefinedThroughout_star (Q := (· = y)) (extendFactory := extendFactory)
          h_head_term
        (by rintro z rfl; exact ⟨h_y_none, h_y_not_def⟩) y rfl
    have h_tgt_none_r_mid : ∀ y ∈ Block.initVars rest, ρ_h_mid.store y = none := by
      intro y hy
      have h_y_none : ρ_h.store y = none := h_tgt_none_r y hy
      have h_y_not_def : y ∉ Block.definedVars (P := P) (C := Cmd P) hoist_s false := fun hc =>
        h_disj y (h_hs_def_sub y hc) hy
      exact block_run_terminal_preserves_none_of_not_definedVars
        h_y_not_def h_y_none h_hs_run
    obtain ⟨d', h_rest_run_h, hd'_fail⟩ :=
      htail_fail ρ_mid ρ_h_mid h_eval_mid h_hf_mid h_agree_mid
        (h_eval_mid_src ▸ hwfb) (h_eval_mid_src ▸ hwfv) (h_eval_mid_src ▸ hwfd)
        (h_eval_mid_src ▸ hwfc) (h_eval_mid_src ▸ hwfvar) h_src_none_r_mid h_tgt_none_r_mid
        d_rest h_rest_run hd_rest
    exact ⟨d', ReflTrans_Transitive _ _ _ _
      (stmts_prefix_terminal_append P (EvalCmd P) extendFactory _ _ ρ_h ρ_h_mid h_hs_run)
      h_rest_run_h, hd'_fail⟩

/-- A single-outcome statement's FAILING sim follows from its terminal/exiting
`HoistSimSA`. -/
private theorem hoistSimFailSA_of_singleOutcome {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {U : List P.Ident} {s : Stmt P (Cmd P)} {hoist_s : List (Stmt P (Cmd P))}
    (h_outcome : ∀ {ρ : Env P} {d : Config P (Cmd P)},
      StepStmtStar P (EvalCmd P) extendFactory (.stmt s ρ) d →
      (∃ ρ', d = .terminal ρ') ∨ (∃ l ρ', d = .exiting l ρ') ∨ d = .stmt s ρ)
    (h_term : HoistSimSA (extendFactory := extendFactory) s hoist_s U) :
    HoistSimFailSA (extendFactory := extendFactory) s hoist_s U := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none d h_run hd_fail
  rcases h_outcome h_run with ⟨ρ', h_eq⟩ | ⟨l, ρ', h_eq⟩ | h_eq
  · subst h_eq
    have hρ'_fail : ρ'.hasFailure = true := by simpa [Config.getEnv] using hd_fail
    obtain ⟨ρ_h', h_run_h, _, h_hf', _⟩ :=
      h_term ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none
        none ρ' (by simpa only [Env.outcomeConfig] using h_run)
    exact ⟨.terminal ρ_h', by simpa only [Env.outcomeConfig] using h_run_h,
      by simpa [Config.getEnv] using (h_hf' ▸ hρ'_fail)⟩
  · subst h_eq
    have hρ'_fail : ρ'.hasFailure = true := by simpa [Config.getEnv] using hd_fail
    obtain ⟨ρ_h', h_run_h, _, h_hf', _⟩ :=
      h_term ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none
        (some l) ρ' (by simpa only [Env.outcomeConfig] using h_run)
    exact ⟨.exiting l ρ_h', by simpa only [Env.outcomeConfig] using h_run_h,
      by simpa [Config.getEnv] using (h_hf' ▸ hρ'_fail)⟩
  · subst h_eq
    have hρ_s_fail : ρ_s.hasFailure = true := by simpa [Config.getEnv] using hd_fail
    exact ⟨.stmts hoist_s ρ_h, .refl _, by simpa [Config.getEnv] using (h_hf ▸ hρ_s_fail)⟩

/-- The `.cmd` FAILING arm. -/
private theorem hoistSimFailSA_cmd {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    {extendFactory : ExtendFactory P} {U : List P.Ident} (c : Cmd P)
    (h_sub : ∀ x ∈ Cmd.definedVars c, x ∈ U) :
    HoistSimFailSA (extendFactory := extendFactory) (.cmd c) [.cmd c] U :=
  hoistSimFailSA_of_singleOutcome cmd_run_outcome (hoistSimSA_cmd c h_sub)

/-- The `.block` FAILING arm. -/
private theorem hoistSimFailSA_block {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {U : List P.Ident} {lbl : String} {inner inner_h : List (Stmt P (Cmd P))} {md : MetaData P}
    (inner_fail : BodyHoistSimFailSA (extendFactory := extendFactory) U inner inner_h) :
    HoistSimFailSA (extendFactory := extendFactory) (.block lbl inner md) [.block lbl inner_h md] U
        := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none d h_run hd_fail
  rcases h_run with _ | ⟨_, _, _, h1, hr1⟩
  · have hρ_s_fail : ρ_s.hasFailure = true := by simpa [Config.getEnv] using hd_fail
    exact ⟨.stmts [.block lbl inner_h md] ρ_h, .refl _,
      by simpa [Config.getEnv] using (h_hf ▸ hρ_s_fail)⟩
  · cases h1
    obtain ⟨d_inner, h_inner_run, hd_inner_fail⟩ :=      block_reaches_failing' P extendFactory hr1
        hd_fail
    obtain ⟨d', h_inner_h_run, hd'_fail⟩ :=
      inner_fail ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none
          d_inner
        h_inner_run hd_inner_fail
    refine ⟨.seq (.block (.some lbl) ρ_h.store ρ_h.factory d') ([] : List (Stmt P (Cmd P))), ?_,
      by simpa [Config.getEnv] using hd'_fail⟩
    refine .step _ _ _ StepStmt.step_stmts_cons ?_
    refine seq_inner_star P (EvalCmd P) extendFactory _ _ _ ?_
    refine .step _ _ _ StepStmt.step_block ?_
    exact block_inner_star P (EvalCmd P) extendFactory _ _ (some lbl) ρ_h.store ρ_h.factory
        h_inner_h_run

/-- The `.ite (.det g)` FAILING arm. -/
private theorem hoistSimFailSA_ite {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {U : List P.Ident} {g : P.Expr} {tss tss_h ess ess_h : List (Stmt P (Cmd P))} {md : MetaData P}
    (then_fail : BodyHoistSimFailSA (extendFactory := extendFactory) U tss tss_h)
    (else_fail : BodyHoistSimFailSA (extendFactory := extendFactory) U ess ess_h) :
    HoistSimFailSA (extendFactory := extendFactory) (.ite (.det g) tss ess md)
      [.ite (.det g) tss_h ess_h md] U := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none d h_run hd_fail
  have guard_h : ∀ {bv : P.Expr}, P.eval ρ_s.factory ρ_s.store g = .some bv →
      P.eval ρ_h.factory ρ_h.store g = .some bv := by
    intro bv hg
    rw [h_eval]
    exact hwfd g bv ρ_s.store ρ_h.store
      (storeAgreement_supplies_mono_premise ρ_s.store ρ_h.store h_agree) hg
  rcases h_run with _ | ⟨_, _, _, h1, hr1⟩
  · have hρ_s_fail : ρ_s.hasFailure = true := by simpa [Config.getEnv] using hd_fail
    exact ⟨.stmts [.ite (.det g) tss_h ess_h md] ρ_h, .refl _,
      by simpa [Config.getEnv] using (h_hf ▸ hρ_s_fail)⟩
  · cases h1 with
    | step_ite_true hg hwf =>
      obtain ⟨d_inner, h_inner_run, hd_inner_fail, _⟩ :=
        blockT_none_reaches_failing' P extendFactory (reflTrans_to_T hr1) hd_fail
      obtain ⟨d', h_branch_h, hd'_fail⟩ :=
        then_fail ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none
            d_inner
          (reflTransT_to_prop h_inner_run) hd_inner_fail
      refine ⟨.seq (.block .none ρ_h.store ρ_h.factory d') ([] : List (Stmt P (Cmd P))), ?_,
        by simpa [Config.getEnv] using hd'_fail⟩
      refine .step _ _ _ StepStmt.step_stmts_cons ?_
      exact seq_inner_star P (EvalCmd P) extendFactory _ _ _
        (.step _ _ _ (StepStmt.step_ite_true (guard_h hg) (h_eval ▸ hwf))
          (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_h.store ρ_h.factory h_branch_h))
    | step_ite_false hg hwf =>
      obtain ⟨d_inner, h_inner_run, hd_inner_fail, _⟩ :=
        blockT_none_reaches_failing' P extendFactory (reflTrans_to_T hr1) hd_fail
      obtain ⟨d', h_branch_h, hd'_fail⟩ :=
        else_fail ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none
            d_inner
          (reflTransT_to_prop h_inner_run) hd_inner_fail
      refine ⟨.seq (.block .none ρ_h.store ρ_h.factory d') ([] : List (Stmt P (Cmd P))), ?_,
        by simpa [Config.getEnv] using hd'_fail⟩
      refine .step _ _ _ StepStmt.step_stmts_cons ?_
      exact seq_inner_star P (EvalCmd P) extendFactory _ _ _
        (.step _ _ _ (StepStmt.step_ite_false (guard_h hg) (h_eval ▸ hwf))
          (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_h.store ρ_h.factory h_branch_h))

/-- The `.ite .nondet` FAILING arm. -/
private theorem hoistSimFailSA_ite_nondet {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {U : List P.Ident} {tss tss_h ess ess_h : List (Stmt P (Cmd P))} {md : MetaData P}
    (then_fail : BodyHoistSimFailSA (extendFactory := extendFactory) U tss tss_h)
    (else_fail : BodyHoistSimFailSA (extendFactory := extendFactory) U ess ess_h) :
    HoistSimFailSA (extendFactory := extendFactory) (.ite .nondet tss ess md)
      [.ite .nondet tss_h ess_h md] U := by
  intro ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none d h_run hd_fail
  rcases h_run with _ | ⟨_, _, _, h1, hr1⟩
  · have hρ_s_fail : ρ_s.hasFailure = true := by simpa [Config.getEnv] using hd_fail
    exact ⟨.stmts [.ite .nondet tss_h ess_h md] ρ_h, .refl _,
      by simpa [Config.getEnv] using (h_hf ▸ hρ_s_fail)⟩
  · cases h1 with
    | step_ite_nondet_true =>
      obtain ⟨d_inner, h_inner_run, hd_inner_fail, _⟩ :=
        blockT_none_reaches_failing' P extendFactory (reflTrans_to_T hr1) hd_fail
      obtain ⟨d', h_branch_h, hd'_fail⟩ :=
        then_fail ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none
            d_inner
          (reflTransT_to_prop h_inner_run) hd_inner_fail
      refine ⟨.seq (.block .none ρ_h.store ρ_h.factory d') ([] : List (Stmt P (Cmd P))), ?_,
        by simpa [Config.getEnv] using hd'_fail⟩
      refine .step _ _ _ StepStmt.step_stmts_cons ?_
      exact seq_inner_star P (EvalCmd P) extendFactory _ _ _
        (.step _ _ _ StepStmt.step_ite_nondet_true
          (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_h.store ρ_h.factory h_branch_h))
    | step_ite_nondet_false =>
      obtain ⟨d_inner, h_inner_run, hd_inner_fail, _⟩ :=
        blockT_none_reaches_failing' P extendFactory (reflTrans_to_T hr1) hd_fail
      obtain ⟨d', h_branch_h, hd'_fail⟩ :=
        else_fail ρ_s ρ_h h_eval h_hf h_agree hwfb hwfv hwfd hwfc hwfvar h_src_none h_tgt_none
            d_inner
          (reflTransT_to_prop h_inner_run) hd_inner_fail
      refine ⟨.seq (.block .none ρ_h.store ρ_h.factory d') ([] : List (Stmt P (Cmd P))), ?_,
        by simpa [Config.getEnv] using hd'_fail⟩
      refine .step _ _ _ StepStmt.step_stmts_cons ?_
      exact seq_inner_star P (EvalCmd P) extendFactory _ _ _
        (.step _ _ _ StepStmt.step_ite_nondet_false
          (block_inner_star P (EvalCmd P) extendFactory _ _ .none ρ_h.store ρ_h.factory h_branch_h))

/-- Bridge: a single-outcome identity statement (`.exit` / `.typeDecl`) reduces to its
terminal `HoistSimSA s [s] U`. -/
private theorem hoistSimFailSA_of_stmtSimSA_nilD {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendFactory : ExtendFactory P}
    {U : List P.Ident} {s : Stmt P (Cmd P)}
    (h_outcome : ∀ {ρ : Env P} {d : Config P (Cmd P)},
      StepStmtStar P (EvalCmd P) extendFactory (.stmt s ρ) d →
      (∃ ρ', d = .terminal ρ') ∨ (∃ l ρ', d = .exiting l ρ') ∨ d = .stmt s ρ)
    (h : StmtSimSA (extendFactory := extendFactory) ([] : List P.Ident) s s) :
    HoistSimFailSA (extendFactory := extendFactory) s [s] U :=
  hoistSimFailSA_of_singleOutcome h_outcome (hoistSimSA_of_stmtSimSA_nilD h)

/-! ## The FAILING structural mutual producer (mirrors `Stmt.hoistP_sim` /
`Block.hoistP_sim`, same match structure, `termination_by sizeOf`; NO
`loopBodyNoInits` precondition). -/
mutual
private theorem Stmt.hoistP_sim_fail {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
        [LawfulHasIdent P]
    {extendFactory : ExtendFactory P} (s : Stmt P (Cmd P))
    (h_shape : Stmt.transportShape s = true)
    (h_nofd : Stmt.noFuncDecl s = true)
    (h_unique : (Stmt.initVars s).Nodup) :
    HoistSimFailSA (extendFactory := extendFactory) s (Stmt.hoistLoopPrefixInits s) (Stmt.initVars
        s) := by
  match s, h_shape, h_nofd, h_unique with
  | .cmd c, _, _, _ =>
      rw [show Stmt.hoistLoopPrefixInits (.cmd c) = [.cmd c] by rw [Stmt.hoistLoopPrefixInits]]
      refine hoistSimFailSA_cmd c ?_
      cases c <;> simp_all [Cmd.definedVars, Stmt.initVars, HasVarsImp.definedVars]
  | .block lbl bss md, h_shape, h_nofd, h_unique =>
      rw [show Stmt.hoistLoopPrefixInits (.block lbl bss md)
            = [.block lbl (Block.hoistLoopPrefixInits bss) md] by rw [Stmt.hoistLoopPrefixInits]]
      rw [Stmt.initVars_block]
      exact hoistSimFailSA_block (Block.hoistP_sim_fail (extendFactory := extendFactory) bss
        (by simpa [Stmt.transportShape] using h_shape)
        (by simpa [Stmt.noFuncDecl] using h_nofd)
        (by simpa only [Stmt.initVars_block] using h_unique))
  | .ite (.det g) tss ess md, h_shape, h_nofd, h_unique =>
      rw [show Stmt.hoistLoopPrefixInits (.ite (.det g) tss ess md)
            = [.ite (.det g) (Block.hoistLoopPrefixInits tss) (Block.hoistLoopPrefixInits ess) md]
                by
          rw [Stmt.hoistLoopPrefixInits]]
      rw [Stmt.initVars_ite]
      obtain ⟨h_sh_t, h_sh_e⟩ : Block.transportShape tss = true ∧ Block.transportShape ess = true :=
          by
        simpa [Stmt.transportShape, Bool.and_eq_true] using h_shape
      obtain ⟨h_nf_t, h_nf_e⟩ : Block.noFuncDecl tss = true ∧ Block.noFuncDecl ess = true := by
        simpa [Stmt.noFuncDecl, Bool.and_eq_true] using h_nofd
      have h_uni : (Block.initVars tss ++ Block.initVars ess).Nodup := by
        simpa only [Stmt.initVars_ite] using h_unique
      have h_uni_t : (Block.initVars tss).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_e : (Block.initVars ess).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_t := Block.hoistP_sim_fail (extendFactory := extendFactory) tss h_sh_t h_nf_t h_uni_t
      have h_e := Block.hoistP_sim_fail (extendFactory := extendFactory) ess h_sh_e h_nf_e h_uni_e
      exact hoistSimFailSA_ite
        (bodyHoistSimFailSA_weaken (fun y hy => List.mem_append_left _ hy) h_t)
        (bodyHoistSimFailSA_weaken (fun y hy => List.mem_append_right _ hy) h_e)
  | .ite .nondet tss ess md, h_shape, h_nofd, h_unique =>
      rw [show Stmt.hoistLoopPrefixInits (.ite .nondet tss ess md)
            = [.ite .nondet (Block.hoistLoopPrefixInits tss) (Block.hoistLoopPrefixInits ess) md] by
          rw [Stmt.hoistLoopPrefixInits]]
      rw [Stmt.initVars_ite]
      obtain ⟨h_sh_t, h_sh_e⟩ : Block.transportShape tss = true ∧ Block.transportShape ess = true :=
          by
        simpa [Stmt.transportShape, Bool.and_eq_true] using h_shape
      obtain ⟨h_nf_t, h_nf_e⟩ : Block.noFuncDecl tss = true ∧ Block.noFuncDecl ess = true := by
        simpa [Stmt.noFuncDecl, Bool.and_eq_true] using h_nofd
      have h_uni : (Block.initVars tss ++ Block.initVars ess).Nodup := by
        simpa only [Stmt.initVars_ite] using h_unique
      have h_uni_t : (Block.initVars tss).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_e : (Block.initVars ess).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_t := Block.hoistP_sim_fail (extendFactory := extendFactory) tss h_sh_t h_nf_t h_uni_t
      have h_e := Block.hoistP_sim_fail (extendFactory := extendFactory) ess h_sh_e h_nf_e h_uni_e
      exact hoistSimFailSA_ite_nondet
        (bodyHoistSimFailSA_weaken (fun y hy => List.mem_append_left _ hy) h_t)
        (bodyHoistSimFailSA_weaken (fun y hy => List.mem_append_right _ hy) h_e)
  | .loop (.det g) none [] body md, h_shape, h_nofd, h_unique =>
      rw [Stmt.initVars_loop]
      have h_sh_b : Block.transportShape body = true := by simpa [Stmt.transportShape] using h_shape
      have h_nf_b : Block.noFuncDecl body = true := by simpa [Stmt.noFuncDecl] using h_nofd
      have h_uni_b : (Block.initVars body).Nodup := by simpa only [Stmt.initVars_loop] using
          h_unique
      exact hoistSimFailSA_loop_arm
        (Block.hoistP_sim (extendFactory := extendFactory) body h_sh_b h_nf_b h_uni_b)
        (Block.hoistP_sim_fail (extendFactory := extendFactory) body h_sh_b h_nf_b h_uni_b)
        h_sh_b h_nf_b h_uni_b
  | .exit lbl md, _, _, _ =>
      rw [show Stmt.hoistLoopPrefixInits (.exit lbl md) = [.exit lbl md] by
          rw [Stmt.hoistLoopPrefixInits]]
      exact hoistSimFailSA_of_stmtSimSA_nilD exit_run_outcome (exit_stmtSimSA lbl md)
  | .typeDecl tc md, _, _, _ =>
      rw [show Stmt.hoistLoopPrefixInits (.typeDecl tc md) = [.typeDecl tc md] by
          rw [Stmt.hoistLoopPrefixInits]]
      exact hoistSimFailSA_of_stmtSimSA_nilD typeDecl_run_outcome (typeDecl_stmtSimSA tc md)
  -- excluded by transportShape / noFuncDecl:
  | .loop (.det g) (some me) inv body md, h_shape, _, _ =>
      exact absurd h_shape (by simp [Stmt.transportShape])
  | .loop (.det g) none (i :: inv) body md, h_shape, _, _ =>
      exact absurd h_shape (by simp [Stmt.transportShape])
  | .loop .nondet m inv body md, h_shape, _, _ =>
      exact absurd h_shape (by simp [Stmt.transportShape])
  | .funcDecl d md, _, h_nofd, _ => exact absurd h_nofd (by simp [Stmt.noFuncDecl])
  termination_by sizeOf s

private theorem Block.hoistP_sim_fail {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
        [LawfulHasIdent P]
    {extendFactory : ExtendFactory P} (ss : List (Stmt P (Cmd P)))
    (h_shape : Block.transportShape ss = true)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_unique : (Block.initVars ss).Nodup) :
    BodyHoistSimFailSA (extendFactory := extendFactory) (Block.initVars ss) ss
        (Block.hoistLoopPrefixInits ss) := by
  match ss, h_shape, h_nofd, h_unique with
  | [], _, _, _ =>
      rw [show Block.hoistLoopPrefixInits ([] : List (Stmt P (Cmd P))) = [] by
          rw [Block.hoistLoopPrefixInits]]
      rw [show Block.initVars ([] : List (Stmt P (Cmd P))) = [] from Block.initVars_nil]
      exact bodyHoistSimFailSA_nil []
  | s :: rest, h_shape, h_nofd, h_unique =>
      rw [show Block.hoistLoopPrefixInits (s :: rest)
            = Stmt.hoistLoopPrefixInits s ++ Block.hoistLoopPrefixInits rest by
                rw [Block.hoistLoopPrefixInits]]
      rw [Block.initVars_cons]
      obtain ⟨h_sh_s, h_sh_r⟩ : Stmt.transportShape s = true ∧ Block.transportShape rest = true :=
          by
        simpa [Block.transportShape, Bool.and_eq_true] using h_shape
      obtain ⟨h_nf_s, h_nf_r⟩ : Stmt.noFuncDecl s = true ∧ Block.noFuncDecl rest = true := by
        simpa [Block.noFuncDecl, Bool.and_eq_true] using h_nofd
      have h_uni : (Stmt.initVars s ++ Block.initVars rest).Nodup := by
        rw [← Block.initVars_cons]; exact h_unique
      have h_uni_s : (Stmt.initVars s).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_r : (Block.initVars rest).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_disj : ∀ y ∈ Stmt.initVars s, y ∉ Block.initVars rest := by
        have := (List.nodup_append.mp h_uni).2.2
        intro y hy_s hy_r; exact this y hy_s y hy_r rfl
      have hhead_term := Stmt.hoistP_sim (extendFactory := extendFactory) s h_sh_s h_nf_s h_uni_s
      have hhead_fail := Stmt.hoistP_sim_fail (extendFactory := extendFactory) s h_sh_s h_nf_s
          h_uni_s
      have htail_fail := Block.hoistP_sim_fail (extendFactory := extendFactory) rest h_sh_r h_nf_r
          h_uni_r
      have h_hs_def_sub : ∀ y ∈ Block.definedVars (P := P) (C := Cmd P) (Stmt.hoistLoopPrefixInits
          s) false,
          y ∈ Stmt.initVars s := by
        intro y hy
        exact Stmt.hoistP_initVars_sub s y hy
      exact bodyHoistSimFailSA_cons h_nf_s h_hs_def_sub h_disj hhead_term hhead_fail htail_fail
  termination_by sizeOf ss
end

/-- **The fused same-name FAILING hoist producer.**  The `CanFail`-arm
analogue of `hoistSimSA_of_hoist`: the source body and its same-name hoist are related
by the body-level failing-config `StoreAgreement` simulation `BodyHoistSimFailSA`,
carrying the dual-undefinedness of every init name (`Block.initVars body`) at entry,
under the `.loop`-arm Bool preconditions `transportShape` / `noFuncDecl` and
`uniqueInits` — NO `loopBodyNoInits`. -/
private theorem hoistSimFailSA_of_hoist {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
        [LawfulHasIdent P]
    {extendFactory : ExtendFactory P} (body : List (Stmt P (Cmd P)))
    (h_shape : Block.transportShape body = true)
    (h_nofd : Block.noFuncDecl body = true)
    (h_unique : Block.uniqueInits body) :
    BodyHoistSimFailSA (extendFactory := extendFactory) (Block.initVars body) body
      (Block.hoistLoopPrefixInits body) :=
  Block.hoistP_sim_fail (extendFactory := extendFactory) body h_shape h_nofd h_unique


end LoopInitHoistProducerProps


/-! # `Block.hoistLoopPrefixInits` correctness

This module exposes the top-level forward-simulation theorems for the
hoisting pass `Block.hoistLoopPrefixInits` (Strata/Transform/LoopInitHoist.lean).
The terminal arm is `hoistLoopPrefixInits_preserves_sa`:

```
hoistLoopPrefixInits_preserves_sa :
  StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ_src) (.terminal ρ_src') →
  StoreAgreement ρ_src.store ρ_tgt.store →   -- source/target start related, not identical
  ∃ ρ_h',
    StepStmtStar P (EvalCmd P) extendFactory
      (.stmts (Block.hoistLoopPrefixInits ss) ρ_tgt) (.terminal ρ_h') ∧
    StoreAgreement ρ_src'.store ρ_h'.store ∧
    ρ_h'.hasFailure = ρ_src'.hasFailure
```

with `hoistLoopPrefixInits_preserves_exit_sa` the exiting-label analogue and
`hoistLoopPrefixInits_to_fail_sa` the `CanFail` analogue. The target runs from
an arbitrary `ρ_tgt` related to `ρ_src` by `StoreAgreement` (not the same
environment), which is what the up-to-relation composition threads.

The store relation is `StoreAgreement` (semantics preservation *modulo
hoisted variables*), not exact pointwise equality: the hoisting pass lifts
loop-body inits to fresh targets defined only in the hoisted store, so the
hoisted store legitimately carries entries the source store never defines.
`StoreAgreement σ_src σ_h` constrains only source-defined variables, leaving
those fresh hoist targets (and projected loop-locals) correctly unconstrained.

The proof is a mutual structural induction on the source block
(`Stmt.hoistP_sim` / `Block.hoistP_sim`, with the `_fail` variants for the
failing arm), dispatching each `.loop` arm via `hoistSimSA_loop_arm` after
running the hoisted prelude.
-/

open StringGenState (GenStep) in
/-- Classification of an `initVars` element of the post-order pass output:
either an ORIGINAL source init (a member of the source `initVars` carrier
`src`), or a FRESH generator name (`HasIdent.ident str` for a string `str`
captured in the output state `σ'` but absent from the input state `σ`).  The
fresh disjunct additionally records that `str` carries the hoist pass's gen
kind `Q` (`Q str`), which the freshly generated carrier names satisfy by the gen
witness `hQgen`.  Instantiating `Q := String.HasUnderscoreDigitSuffix` recovers
the blanket generator-suffix statement. -/
def HoistInitClass {P : PureExpr} [HasIdent P] (Q : String → Prop) (src : List P.Ident) (σ σ' :
    StringGenState) (x : P.Ident) : Prop :=
  (x ∈ src) ∨
  (∃ str : String, x = HasIdent.ident str
    ∧ str ∈ StringGenState.stringGens σ'
    ∧ str ∉ StringGenState.stringGens σ
    ∧ Q str)

open StringGenState (GenStep) in
/-- Two classified `initVars` carriers from consecutive sub-passes are disjoint:
originals are disjoint by `uniqueInits` and suffix-free by `h_src_shapefree`;
fresh names are suffix-shaped and captured in disjoint state windows.  All four
cross-class collisions are impossible. -/
private theorem hoistInitClass_disjoint {P : PureExpr} [HasIdent P] [LawfulHasIdent P] {Q : String → Prop}
    (src₁ src₂ : List P.Ident) (σ σmid σ' : StringGenState)
    (h_src_disjoint : ∀ a ∈ src₁, ∀ b ∈ src₂, a ≠ b)
    (h_sf₁ : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ src₁)
    (h_sf₂ : ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ src₂)
    (L₁ L₂ : List P.Ident)
    (hc₁ : ∀ x ∈ L₁, HoistInitClass Q src₁ σ σmid x)
    (hc₂ : ∀ x ∈ L₂, HoistInitClass Q src₂ σmid σ' x) :
    ∀ a ∈ L₁, ∀ b ∈ L₂, a ≠ b := by
  intro a ha b hb hab
  subst hab
  rcases hc₁ a ha with h_o₁ | ⟨str₁, hstr₁_eq, hstr₁_in, hstr₁_not, hstr₁_Q⟩
  · rcases hc₂ a hb with h_o₂ | ⟨str₂, hstr₂_eq, hstr₂_in, _, hstr₂_Q⟩
    · exact h_src_disjoint a h_o₁ a h_o₂ rfl
    · -- a ∈ src₁ (kind-free) but a = ident str₂ with `Q str₂`.
      exact h_sf₁ str₂ hstr₂_Q (hstr₂_eq ▸ h_o₁)
  · -- a = ident str₁ with str₁ ∈ σmid \ σ and `Q str₁`.
    rcases hc₂ a hb with h_o₂ | ⟨str₂, hstr₂_eq, hstr₂_in, hstr₂_not, _⟩
    · exact h_sf₂ str₁ hstr₁_Q (hstr₁_eq ▸ h_o₂)
    · -- ident str₁ = ident str₂ ⇒ str₁ = str₂; but str₁ ∈ σmid, str₂ ∉ σmid.
      have h_id : (HasIdent.ident str₁ : P.Ident) = HasIdent.ident str₂ :=
        hstr₁_eq.symm.trans hstr₂_eq
      have : str₁ = str₂ := LawfulHasIdent.ident_inj h_id
      exact hstr₂_not (this ▸ hstr₁_in)

/-! ## Same-name (`StoreAgreement`) public entry points

These are the same-name entry points for the hoist simulation.  They are stated
over the **pure same-name** pass
`Block.hoistLoopPrefixInits`, whose `.init y` arms reuse the source
name `y` and emit a same-name havoc prelude — no fresh target, no rename,
no `subst`.  Consequently these entries drop the `Q` / `hQgen` freshness apparatus
the fresh-name entries thread; they take only the source-shape
structural preconditions (`loopBodyNoInits`, `transportShape`, `noFuncDecl`,
`uniqueInits`) the same-name producer `hoistSimSA_of_hoist` consumes, plus the
DUAL-undefinedness of the init names (`Block.initVars ss`) on both the source and
the target store at entry.

Each forwards to the structural producer `hoistSimSA_of_hoist`, which inhabits the
body-level dual-undefinedness simulation
`BodyHoistSimSA (Block.initVars ss) ss (Block.hoistLoopPrefixInits ss)`; unfolding
that relation at the `none` / `some lbl` outcome yields the terminal / exiting
conclusions.  The conclusions are `StoreAgreement` (preservation modulo the
hoisted-but-still-same-named slots) plus `hasFailure` agreement, exactly the
`HoistSimSA`/`BodyHoistSimSA` clauses.

The target runs from an arbitrary `ρ_tgt` related to the source by
`StoreAgreement` (+ `eval`/`hasFailure` equalities + a `ρ_tgt`-side init-undefinedness
obligation) — the compositional shape a per-pass overapproximation instance needs.

The `_to_fail` analogue (`hoistLoopPrefixInits_to_fail_sa`) is provided
separately: `BodyHoistSimSA` matches only completed outcomes (terminal /
exiting), so a mid-run failing configuration — which need not reach any outcome
on a non-terminating loop — cannot be matched from it.  The failing arm instead
routes through the same-name *failing* loop driver `samenameLoopDetSA_F` (the
`StoreAgreement` analogue of the fresh-name failing driver) and the failing
producer `hoistSimFailSA_of_hoist`. -/

/-- **Same-name terminal forward simulation.**  A terminating source run of `ss`
is matched by a terminating run of the same-name hoist `Block.hoistLoopPrefixInits
ss` from any `StoreAgreement`-related `ρ_tgt`, producing a `StoreAgreement`-related
terminal store and the same `hasFailure` flag.  Forwards to the structural producer
`hoistSimSA_of_hoist` (its `BodyHoistSimSA` unfolded at the `none` outcome). -/
theorem hoistLoopPrefixInits_preserves_sa {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasIdent P]
    {extendFactory : ExtendFactory P}
    (ss : List (Stmt P (Cmd P)))
    {ρ_src ρ_tgt ρ_src' : Env P}
    (h_shape      : Block.transportShape ss = true)
    (h_nofd       : Block.noFuncDecl ss = true)
    (h_unique     : Block.uniqueInits ss)
    (h_eval_eq    : ρ_tgt.factory = ρ_src.factory)
    (h_hf_eq      : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree      : StoreAgreement ρ_src.store ρ_tgt.store)
    (h_src_undef  : ∀ y ∈ Block.initVars ss, ρ_src.store y = none)
    (h_tgt_undef  : ∀ y ∈ Block.initVars ss, ρ_tgt.store y = none)
    (h_wfb        : WellFormedSemanticEvalBool ρ_src.factory)
    (h_wfv        : WellFormedSemanticEvalVal ρ_src.factory)
    (h_wfd        : WellFormedSemanticEvalMono ρ_src.factory)
    (h_wfc        : WellFormedSemanticEvalExprCongr ρ_src.factory)
    (h_wfvar      : WellFormedSemanticEvalVar ρ_src.factory)
    (h_run_src    : StepStmtStar P (EvalCmd P) extendFactory
                       (.stmts ss ρ_src) (.terminal ρ_src')) :
    ∃ ρ_h',
      StepStmtStar P (EvalCmd P) extendFactory
        (.stmts (Block.hoistLoopPrefixInits ss) ρ_tgt) (.terminal ρ_h')
      ∧ StoreAgreement ρ_src'.store ρ_h'.store
      ∧ ρ_h'.hasFailure = ρ_src'.hasFailure := by
  have hbody :
      LoopInitHoistProducerProps.BodyHoistSimSA (extendFactory := extendFactory)
        (Block.initVars ss) ss (Block.hoistLoopPrefixInits ss) :=
    LoopInitHoistProducerProps.hoistSimSA_of_hoist ss h_shape h_nofd h_unique
  obtain ⟨ρ_h', h_run_h, h_agree', h_hf', _⟩ :=
    hbody ρ_src ρ_tgt h_eval_eq h_hf_eq h_agree h_wfb h_wfv h_wfd h_wfc h_wfvar
      h_src_undef h_tgt_undef none ρ_src'
      (by simpa only [Env.outcomeConfig] using h_run_src)
  exact ⟨ρ_h', by simpa only [Env.outcomeConfig] using h_run_h, h_agree', h_hf'⟩

/-- **Same-name exiting forward simulation.**  Escaping companion of
`hoistLoopPrefixInits_preserves_sa`: an escaping source run of `ss` (reaching
`.exiting lbl ρ_src'`) is matched by an escaping run of the same-name hoist to the
*same* label, with a `StoreAgreement`-related final store and the same `hasFailure`
flag.  Forwards to `hoistSimSA_of_hoist` (its `BodyHoistSimSA` unfolded at the `some
lbl` outcome). -/
theorem hoistLoopPrefixInits_preserves_exit_sa {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasIdent P]
    {extendFactory : ExtendFactory P}
    (ss : List (Stmt P (Cmd P)))
    {ρ_src ρ_tgt ρ_src' : Env P}
    (h_shape      : Block.transportShape ss = true)
    (h_nofd       : Block.noFuncDecl ss = true)
    (h_unique     : Block.uniqueInits ss)
    (h_eval_eq    : ρ_tgt.factory = ρ_src.factory)
    (h_hf_eq      : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree      : StoreAgreement ρ_src.store ρ_tgt.store)
    (h_src_undef  : ∀ y ∈ Block.initVars ss, ρ_src.store y = none)
    (h_tgt_undef  : ∀ y ∈ Block.initVars ss, ρ_tgt.store y = none)
    (h_wfb        : WellFormedSemanticEvalBool ρ_src.factory)
    (h_wfv        : WellFormedSemanticEvalVal ρ_src.factory)
    (h_wfd        : WellFormedSemanticEvalMono ρ_src.factory)
    (h_wfc        : WellFormedSemanticEvalExprCongr ρ_src.factory)
    (h_wfvar      : WellFormedSemanticEvalVar ρ_src.factory)
    (lbl          : String)
    (h_run_src    : StepStmtStar P (EvalCmd P) extendFactory
                       (.stmts ss ρ_src) (.exiting lbl ρ_src')) :
    ∃ ρ_h',
      StepStmtStar P (EvalCmd P) extendFactory
        (.stmts (Block.hoistLoopPrefixInits ss) ρ_tgt) (.exiting lbl ρ_h')
      ∧ StoreAgreement ρ_src'.store ρ_h'.store
      ∧ ρ_h'.hasFailure = ρ_src'.hasFailure := by
  have hbody :
      LoopInitHoistProducerProps.BodyHoistSimSA (extendFactory := extendFactory)
        (Block.initVars ss) ss (Block.hoistLoopPrefixInits ss) :=
    LoopInitHoistProducerProps.hoistSimSA_of_hoist ss h_shape h_nofd h_unique
  obtain ⟨ρ_h', h_run_h, h_agree', h_hf', _⟩ :=
    hbody ρ_src ρ_tgt h_eval_eq h_hf_eq h_agree h_wfb h_wfv h_wfd h_wfc h_wfvar
      h_src_undef h_tgt_undef (some lbl) ρ_src'
      (by simpa only [Env.outcomeConfig] using h_run_src)
  exact ⟨ρ_h', by simpa only [Env.outcomeConfig] using h_run_h, h_agree', h_hf'⟩

/-- **Same-name FAILING forward simulation (the `CanFail` arm).**  Failing-config
companion of `hoistLoopPrefixInits_preserves_sa`: a source run of `ss` that reaches a
*failing* config (`d.getEnv.hasFailure = true`; need not be any completed outcome — a
non-terminating loop can still fail mid-run) is matched by a same-name hoist run that
reaches a failing config too.  The preconditions are the SAME structural subset as
`hoistLoopPrefixInits_preserves_sa` (`transportShape` + `noFuncDecl` + `uniqueInits` +
the WF bundle + dual init-undef + `StoreAgreement` + eval/hf agreement) — NO
`loopBodyNoInits`.  Forwards to the failing producer
`hoistSimFailSA_of_hoist` (its `BodyHoistSimFailSA`). -/
theorem hoistLoopPrefixInits_to_fail_sa {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasIdent P]
    {extendFactory : ExtendFactory P}
    (ss : List (Stmt P (Cmd P)))
    {ρ_src ρ_tgt : Env P} {d : Config P (Cmd P)}
    (h_shape      : Block.transportShape ss = true)
    (h_nofd       : Block.noFuncDecl ss = true)
    (h_unique     : Block.uniqueInits ss)
    (h_eval_eq    : ρ_tgt.factory = ρ_src.factory)
    (h_hf_eq      : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree      : StoreAgreement ρ_src.store ρ_tgt.store)
    (h_src_undef  : ∀ y ∈ Block.initVars ss, ρ_src.store y = none)
    (h_tgt_undef  : ∀ y ∈ Block.initVars ss, ρ_tgt.store y = none)
    (h_wfb        : WellFormedSemanticEvalBool ρ_src.factory)
    (h_wfv        : WellFormedSemanticEvalVal ρ_src.factory)
    (h_wfd        : WellFormedSemanticEvalMono ρ_src.factory)
    (h_wfc        : WellFormedSemanticEvalExprCongr ρ_src.factory)
    (h_wfvar      : WellFormedSemanticEvalVar ρ_src.factory)
    (h_run_src    : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ_src) d)
    (h_d_fail     : d.getEnv.hasFailure = true) :
    ∃ d',
      StepStmtStar P (EvalCmd P) extendFactory
        (.stmts (Block.hoistLoopPrefixInits ss) ρ_tgt) d'
      ∧ d'.getEnv.hasFailure = true := by
  have hbody :
      LoopInitHoistProducerProps.BodyHoistSimFailSA (extendFactory := extendFactory)
        (Block.initVars ss) ss (Block.hoistLoopPrefixInits ss) :=
    LoopInitHoistProducerProps.hoistSimFailSA_of_hoist ss h_shape h_nofd h_unique
  exact hbody ρ_src ρ_tgt h_eval_eq h_hf_eq h_agree h_wfb h_wfv h_wfd h_wfc h_wfvar
    h_src_undef h_tgt_undef d h_run_src h_d_fail


/-! ## `hoist` per-pass overapproximation instance

The middle structured pass stated as its own `OverapproximatesUptoWhen` instance,
over the imperative-block language `Lang.imperativeBlock` (both the post-nondetElim
and post-hoist intermediate languages share this shape) and the output relation
`EnvStoreAgree`.  Statement-shape premises come from `pre`; the evaluator facts and
store-freshness come from the source language's `initEnvWF (s2uKind) ss ρ₀` at the
shared initial env `ρ₀`.  Forwarded shape conjuncts re-establish the downstream
`stmtsToCFG` instance's `pre`. -/
section HoistOverapprox
open Imperative.Specification Imperative.Specification.Transform
open StructuredToUnstructuredCorrect (s2uKind)

/-- `Block.hoistLoopPrefixInits` overapproximates its source up to `EnvStoreAgree`: for a
block that is nondet-loop-free, func-decl-free, invariant/measure-free, has unique
inits and covered exits, is simple-shaped, and whose `s2uKind` names are absent from
its init/modified variables, every source run is matched by a run of the hoisted block
ending in a store-agreeing, failure-matching, factory-preserving target state.  This is
the middle per-pass instance the pipeline capstone composes. -/
theorem hoist_overapproximates_upto {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent
    P]
    [HasInt P] [HasIntOps P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    [HasSubstFvar P] (extendFactory : ExtendFactory P) :
    Specification.Transform.OverapproximatesUptoWhen
      (· = ·)
      (Specification.Transform.EnvStoreAgree (P := P))
      (Lang.imperativeBlock (EvalCmd P) extendFactory (isAtAssert P))
      (Lang.imperativeBlock (EvalCmd P) extendFactory (isAtAssert P))
      (fun ss => some (Block.hoistLoopPrefixInits ss))
      (fun ss =>
        Block.containsNondetLoop ss = false
        ∧ Block.noFuncDecl ss = true
        ∧ Block.loopHasNoInvariants ss = true
        ∧ Block.noMeasureLoops ss = true
        ∧ Block.uniqueInits ss
        ∧ Block.exitsCoveredByBlocks [] ss
        ∧ Block.simpleShape ss = true
        ∧ Block.userLabelsShapeNodup ss
        ∧ (∀ s : String, s2uKind s → HasIdent.ident (P := P) s ∉ Block.initVars ss)
        ∧ (∀ s : String, s2uKind s → HasIdent.ident (P := P) s ∉ Block.modifiedVars ss))
      s2uKind s2uKind := by
  intro ss ss' ht hpre ρ₀ ρ₀' hEq hwf
  subst hEq
  simp only [Option.some.injEq] at ht
  subst ht
  obtain ⟨h_no_nd, h_no_fd, h_no_inv, h_no_measure, h_unique, _,
    _, _, _, _⟩ := hpre
  have h_inits := hwf.defsUndefined
  have h_s2u := hwf.definedVarsNotReserved
  have hwfbool₀ := hwf.bool
  have hwfval₀ := hwf.val
  have hwfvar₀ := hwf.var
  have hwfcongr₀ := hwf.exprCongr
  have hwfmono₀ := hwf.mono
  have h_nofd : Block.noFuncDecl ss = true := h_no_fd
  have h_shape : Block.transportShape ss = true :=
    Block.transportShape_of_arm_preconds ss
      h_no_nd h_no_fd h_no_inv h_no_measure
  refine ⟨fun ρ' => ⟨fun hstar => ?_, fun lbl hstar => ?_⟩, ?_, ?_⟩
  · -- ===== TERMINAL ARM =====
    have h_term : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ₀) (.terminal ρ') := by
      simpa [Lang.imperativeBlock] using hstar
    obtain ⟨ρ_out, h_run, h_off, h_fl⟩ :=
      hoistLoopPrefixInits_preserves_sa
        (extendFactory := extendFactory) ss h_shape h_nofd h_unique
        rfl rfl (StoreAgreement.refl _) h_inits h_inits
        hwfbool₀ hwfval₀ hwfmono₀ hwfcongr₀ hwfvar₀
        h_term
    have h_src_eval : ρ'.factory = ρ₀.factory :=
      block_noFuncDecl_preserves_factory P (EvalCmd P) extendFactory ss ρ₀ ρ' h_nofd h_term
    have h_tgt_eval : ρ_out.factory = ρ₀.factory :=
      block_noFuncDecl_preserves_factory P (EvalCmd P) extendFactory (Block.hoistLoopPrefixInits ss)
        ρ₀ ρ_out (LoopInitHoistProducerProps.Block.hoistP_noFuncDecl ss h_nofd) h_run
    refine ⟨ρ_out, ⟨h_off, h_fl.symm, ?_⟩, ?_⟩
    · rw [h_tgt_eval, h_src_eval]
    · simpa [Lang.imperativeBlock] using h_run
  · -- ===== EXITING ARM =====
    have h_exit : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ₀) (.exiting lbl ρ') := by
      simpa [Lang.imperativeBlock] using hstar
    obtain ⟨ρ_out, h_run, h_off, h_fl⟩ :=
      hoistLoopPrefixInits_preserves_exit_sa
        (extendFactory := extendFactory) ss h_shape h_nofd h_unique
        rfl rfl (StoreAgreement.refl _) h_inits h_inits
        hwfbool₀ hwfval₀ hwfmono₀ hwfcongr₀ hwfvar₀
        lbl h_exit
    have h_src_eval : ρ'.factory = ρ₀.factory :=
      block_noFuncDecl_preserves_factory_exiting ss ρ₀ ρ' lbl h_nofd h_exit
    have h_tgt_eval : ρ_out.factory = ρ₀.factory :=
      block_noFuncDecl_preserves_factory_exiting
        (Block.hoistLoopPrefixInits ss) ρ₀ ρ_out lbl
        (LoopInitHoistProducerProps.Block.hoistP_noFuncDecl ss h_nofd) h_run
    refine ⟨ρ_out, ⟨h_off, h_fl.symm, ?_⟩, ?_⟩
    · rw [h_tgt_eval, h_src_eval]
    · simpa [Lang.imperativeBlock] using h_run
  · -- ===== CanFail ARM =====
    intro h_src
    by_cases h_ρ₀_fail : ρ₀.hasFailure = true
    · refine ⟨(Config.stmts (Block.hoistLoopPrefixInits ss) ρ₀ : Config P (Cmd P)), ?_, ?_⟩
      · simpa [Lang.imperativeBlock, Config.getEnv] using h_ρ₀_fail
      · simpa [Lang.imperativeBlock] using
          (ReflTrans.refl (Config.stmts (Block.hoistLoopPrefixInits ss) ρ₀ : Config P (Cmd P)))
    · obtain ⟨cfg_s, h_cfg_fail, h_cfg_reach⟩ := h_src
      have h_reach : StepStmtStar P (EvalCmd P) extendFactory (.stmts ss ρ₀) cfg_s := by
        simpa [Lang.imperativeBlock] using h_cfg_reach
      have h_fail : cfg_s.getEnv.hasFailure = true := by
        simpa [Lang.imperativeBlock] using h_cfg_fail
      obtain ⟨d, hd_run, hd_fail⟩ :=
        hoistLoopPrefixInits_to_fail_sa
          (extendFactory := extendFactory) ss h_shape h_nofd h_unique
          rfl rfl (StoreAgreement.refl _) h_inits h_inits
          hwfbool₀ hwfval₀ hwfmono₀ hwfcongr₀ hwfvar₀
          h_reach h_fail
      exact ⟨d, by simpa [Lang.imperativeBlock] using hd_fail,
        by simpa [Lang.imperativeBlock] using hd_run⟩
  · -- ===== target initEnvWF conjunct =====
    refine { hwf with defsUndefined := ?_, definedVarsNotReserved := h_s2u }
    intro x hx
    exact h_inits x (LoopInitHoistProducerProps.Block.hoistP_initVars_sub ss x hx)

end HoistOverapprox

/-! ## Relocated nondetElim structural lemmas (exprsShapeFree-dependent)

These lemmas about `Block.nondetElim` land here (rather than in `NondetElimCorrect`)
because their statements or proofs mention `Block.exprsShapeFree`/`Stmt.exprsShapeFree`,
`namesFreshInRhsExprs`, or the file-private `Block.namesFreshInExprs_of_exprsShapeFree'`,
all of which are introduced in this module.  The `initVars`-nodup classification also
lives here because it consumes `HoistInitClass`/`hoistInitClass_disjoint`.  The two
hoist exit-coverage mutuals close out the coverage-preservation story for this pass. -/

section NondetElimShapeFree

/-- A `.cmd (init _ _ .nondet _)` reads nothing, so it is `exprsShapeFree`. -/
private theorem init_nondet_sf {P : PureExpr} [HasIdent P] [HasVarsPure P P.Expr] [HasFvars P] {Q :
    String → Prop} (ident : P.Ident) (ty : P.Ty)
    (md : MetaData P) :
    Stmt.exprsShapeFree (P := P) Q (Stmt.cmd (HasInit.init ident ty ExprOrNondet.nondet md)) := by
  show Stmt.exprsShapeFree (P := P) Q (Stmt.cmd (Cmd.init ident ty ExprOrNondet.nondet md))
  rw [Stmt.exprsShapeFree_cmd]
  simp only [Cmd.getVars, ExprOrNondet.getVars]
  exact fun str _ hmem => absurd hmem List.not_mem_nil

/-- A `.cmd (havoc _)` reads nothing, so it is `exprsShapeFree`. -/
private theorem havoc_sf {P : PureExpr} [HasIdent P] [HasVarsPure P P.Expr] [HasFvars P] {Q : String
    → Prop} (ident : P.Ident) (md : MetaData P) :
    Stmt.exprsShapeFree (P := P) Q (Stmt.cmd (HasHavoc.havoc ident md)) := by
  show Stmt.exprsShapeFree (P := P) Q (Stmt.cmd (Cmd.set ident ExprOrNondet.nondet md))
  rw [Stmt.exprsShapeFree_cmd]
  simp only [Cmd.getVars, ExprOrNondet.getVars]
  exact fun str _ hmem => absurd hmem List.not_mem_nil

/-- The freshly generated ndelim guard ident is `∉ getVars` of any `Q`-foreign
read-var slot: the only read is `mkFvar ident` whose vars ⊆ `[ident]` and `ident`
carries the ndelim kind, foreign to `Q`. -/
private theorem ndelim_guard_fresh {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P] [HasVarsPure
    P P.Expr]
    [LawfulHasFvar P] [LawfulHasFvars P] [LawfulHasIdent P] {Q : String → Prop}
    (pf : String) (σ : StringGenState)
    (hforeign : ¬ Q (StringGenState.gen pf σ).1) :
    ∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉
        HasFvars.getFvars (P := P)
          (HasFvar.mkFvar (HasIdent.ident (P := P) (StringGenState.gen pf σ).1)) := by
  intro str hQ hmem
  have hin : HasIdent.ident (P := P) str ∈
      [HasIdent.ident (P := P) (StringGenState.gen pf σ).1] :=
    LawfulHasFvars.mkFvar_getFvars (P := P) _ hmem
  rw [List.mem_singleton] at hin
  exact hforeign (LawfulHasIdent.ident_inj hin ▸ hQ)

/-- Transport `exprsShapeFree` across a `.loop` whose guard/body are replaced but
whose measure/invariants are unchanged: the measure/invariant freshness conjuncts
carry over verbatim from the source loop. -/
private theorem loop_sf_transport {P : PureExpr} [HasIdent P] [HasVarsPure P P.Expr] [HasFvars P] {Q
    : String → Prop} (g₀ g₁ : ExprOrNondet P)
    (m : Option P.Expr) (inv : List (String × P.Expr))
    (body₀ body₁ : List (Stmt P (Cmd P))) (md : MetaData P)
    (h : Stmt.exprsShapeFree (P := P) Q (.loop g₀ m inv body₀ md))
    (hg : ∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉ ExprOrNondet.getVars (P := P) g₁)
    (hb : Block.exprsShapeFree (P := P) Q body₁) :
    Stmt.exprsShapeFree (P := P) Q (.loop g₁ m inv body₁ md) := by
  rw [Stmt.exprsShapeFree_loop] at h ⊢
  exact ⟨hg, h.2.1, h.2.2.1, hb⟩

mutual
/-- `nondetElim` preserves `exprsShapeFree Q`, provided the labels it generates (the
two ndelim guard prefixes) are foreign to `Q`: source read-vars stay `Q`-free,
and the only new read-var is the freshly-generated guard ident, which is `¬ Q` by
foreignness. -/
theorem Stmt.nondetElimM_exprsShapeFree {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P]
    [LawfulHasFvars P] [HasBool P] [HasVarsPure P P.Expr]
    [LawfulHasFvar P] [LawfulHasFvars P] [LawfulHasIdent P] {Q : String → Prop}
    (hfi : ∀ sg, ¬ Q (StringGenState.gen ndelimItePrefix sg).1)
    (hfl : ∀ sg, ¬ Q (StringGenState.gen ndelimLoopPrefix sg).1)
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (h : Stmt.exprsShapeFree (P := P) Q s) :
    Block.exprsShapeFree (P := P) Q (Stmt.nondetElimM s σ).1 := by
  match s with
  | .cmd c =>
      simp only [Stmt.nondetElimM]
      exact Block.exprsShapeFree_singleton.mpr h
  | .block lbl bss md =>
      rw [Stmt.nondetElimM_block_out]
      rw [Stmt.exprsShapeFree_block] at h
      rw [Block.exprsShapeFree_singleton, Stmt.exprsShapeFree_block]
      exact Block.nondetElimM_exprsShapeFree hfi hfl bss σ h
  | .ite (.det e) tss ess md =>
      rw [Stmt.nondetElimM_ite_det_out]
      rw [Stmt.exprsShapeFree_ite] at h
      rw [Block.exprsShapeFree_singleton, Stmt.exprsShapeFree_ite]
      exact ⟨h.1, Block.nondetElimM_exprsShapeFree hfi hfl tss σ h.2.1,
             Block.nondetElimM_exprsShapeFree hfi hfl ess _ h.2.2⟩
  | .ite .nondet tss ess md =>
      rw [Stmt.nondetElimM_ite_nondet_out]
      rw [Stmt.exprsShapeFree_ite] at h
      rw [Block.exprsShapeFree_cons_iff]
      refine ⟨init_nondet_sf _ _ _, ?_⟩
      rw [Block.exprsShapeFree_singleton, Stmt.exprsShapeFree_ite]
      refine ⟨ndelim_guard_fresh ndelimItePrefix σ (hfi σ),
              Block.nondetElimM_exprsShapeFree hfi hfl tss _ h.2.1,
              Block.nondetElimM_exprsShapeFree hfi hfl ess _ h.2.2⟩
  | .loop (.det e) m inv body md =>
      rw [Stmt.nondetElimM_loop_det_out]
      obtain ⟨hg, -, -, hbody⟩ := Stmt.exprsShapeFree_loop.mp h
      rw [Block.exprsShapeFree_singleton]
      exact loop_sf_transport (.det e) (.det e) m inv body _ md h hg
        (Block.nondetElimM_exprsShapeFree hfi hfl body σ hbody)
  | .loop .nondet m inv body md =>
      rw [Stmt.nondetElimM_loop_nondet_out]
      obtain ⟨-, -, -, hbody⟩ := Stmt.exprsShapeFree_loop.mp h
      rw [Block.exprsShapeFree_cons_iff]
      refine ⟨init_nondet_sf _ _ _, ?_⟩
      rw [Block.exprsShapeFree_singleton]
      refine loop_sf_transport .nondet
        (.det (HasFvar.mkFvar (HasIdent.ident (P := P) (StringGenState.gen ndelimLoopPrefix σ).1)))
        m inv body _ md h
        (ndelim_guard_fresh ndelimLoopPrefix σ (hfl σ)) ?_
      refine Block.exprsShapeFree_append _ _
        ⟨Block.nondetElimM_exprsShapeFree hfi hfl body _ hbody, ?_⟩
      exact Block.exprsShapeFree_singleton.mpr (havoc_sf _ _)
  | .exit lbl md | .typeDecl _ md =>
      simp only [Stmt.nondetElimM]
      rw [Block.exprsShapeFree_singleton]
      intro str _ hmem
      simp only [Stmt.getVars] at hmem; exact absurd hmem List.not_mem_nil
  | .funcDecl d md =>
      simp only [Stmt.nondetElimM]
      exact Block.exprsShapeFree_singleton.mpr h
  termination_by sizeOf s

/-- Block-level `exprsShapeFree Q` preservation through `nondetElim`. -/
theorem Block.nondetElimM_exprsShapeFree {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P]
    [LawfulHasFvars P] [HasBool P] [HasVarsPure P P.Expr]
    [LawfulHasFvar P] [LawfulHasFvars P] [LawfulHasIdent P] {Q : String → Prop}
    (hfi : ∀ sg, ¬ Q (StringGenState.gen ndelimItePrefix sg).1)
    (hfl : ∀ sg, ¬ Q (StringGenState.gen ndelimLoopPrefix sg).1)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h : Block.exprsShapeFree (P := P) Q ss) :
    Block.exprsShapeFree (P := P) Q (Block.nondetElimM ss σ).1 := by
  match ss with
  | [] =>
      simp only [Block.nondetElimM]
      exact Block.exprsShapeFree_nil
  | s :: rest =>
      rw [Block.nondetElimM_cons_out]
      rw [Block.exprsShapeFree_cons_iff] at h
      exact Block.exprsShapeFree_append _ _
        ⟨Stmt.nondetElimM_exprsShapeFree hfi hfl s σ h.1,
         Block.nondetElimM_exprsShapeFree hfi hfl rest _ h.2⟩
  termination_by sizeOf ss
end

/-- The freshly generated ndelim guard satisfies the `HoistInitClass` fresh
disjunct at `ndelimKind` over a one-`gen`-step window. -/
private theorem ndelim_fresh_class {P : PureExpr} [HasIdent P] (pf : String) (σ : StringGenState)
    (h_wf : StringGenState.WF σ)
    (hpf : ndelimKind (StringGenState.gen pf σ).1) :
    ∃ str : String, HasIdent.ident (P := P) (StringGenState.gen pf σ).1 = HasIdent.ident str
      ∧ str ∈ StringGenState.stringGens (StringGenState.gen pf σ).2
      ∧ str ∉ StringGenState.stringGens σ
      ∧ ndelimKind str :=
  ⟨(StringGenState.gen pf σ).1, rfl,
    by rw [StringGenState.stringGens_gen]; exact List.mem_cons.mpr (Or.inl rfl),
    StringGenState.stringGens_gen_not_in pf σ h_wf, hpf⟩

mutual
/-- Strengthened nondetElim `initVars` classification: window-tracked
`HoistInitClass` at `ndelimKind`, plus `Nodup`.  Mirrors the hoist
`_initVars_classified`. -/
theorem Stmt.nondetElimM_initVars_nodup {P : PureExpr} [HasIdent P] [LawfulHasIdent P] [HasFvar P]
    [HasFvars P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) (h_wf : StringGenState.WF σ)
    (h_unique : (Stmt.initVars s).Nodup)
    (h_sf : ∀ str : String, ndelimKind str → HasIdent.ident (P := P) str ∉ Stmt.initVars s) :
    (∀ x ∈ Block.initVars (P := P) (Stmt.nondetElimM s σ).1,
        HoistInitClass ndelimKind (Stmt.initVars s) σ (Stmt.nondetElimM s σ).2 x)
      ∧ (Block.initVars (P := P) (Stmt.nondetElimM s σ).1).Nodup := by
  match s with
  | .cmd c =>
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars_nil, List.append_nil]
          at hx ⊢
        exact Or.inl hx
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars_nil, List.append_nil]
        exact h_unique
  | .block lbl bss md =>
      rw [Stmt.nondetElimM_block_out, Stmt.nondetElimM_block_state]
      have h_unique' : (Block.initVars bss).Nodup := by
        simpa only [Stmt.initVars_block] using h_unique
      have h_sf' : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars bss := by
        intro str hsuf; simpa only [Stmt.initVars_block] using h_sf str hsuf
      have ih := Block.nondetElimM_initVars_nodup bss σ h_wf h_unique' h_sf'
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Block.initVars_cons, Stmt.initVars_block, Block.initVars_nil,
          List.append_nil] at hx ⊢
        simpa only [Stmt.initVars_block] using ih.1 x hx
      · simp only [Block.initVars_cons, Stmt.initVars_block, Block.initVars_nil, List.append_nil]
        exact ih.2
  | .ite (.det e) tss ess md =>
      rw [Stmt.nondetElimM_ite_det_out, Stmt.nondetElimM_ite_det_state]
      have h_uni : (Block.initVars tss ++ Block.initVars ess).Nodup := by
        simpa only [Stmt.initVars_ite] using h_unique
      have h_uni_t : (Block.initVars tss).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_e : (Block.initVars ess).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_disj_te : ∀ a ∈ Block.initVars tss, ∀ b ∈ Block.initVars ess, a ≠ b :=
        (List.nodup_append.mp h_uni).2.2
      have h_sf_t : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars tss := by
        intro str hsuf hmem; exact h_sf str hsuf (by
          rw [Stmt.initVars_ite, List.mem_append]; exact Or.inl hmem)
      have h_sf_e : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars ess := by
        intro str hsuf hmem; exact h_sf str hsuf (by
          rw [Stmt.initVars_ite, List.mem_append]; exact Or.inr hmem)
      have ih_t := Block.nondetElimM_initVars_nodup tss σ h_wf h_uni_t h_sf_t
      have h_wf_t : StringGenState.WF (Block.nondetElimM tss σ).2 :=
        (Block.nondetElimM_genStep tss σ).wf_mono h_wf
      have ih_e := Block.nondetElimM_initVars_nodup ess (Block.nondetElimM tss σ).2 h_wf_t h_uni_e
          h_sf_e
      have h_step_t : StringGenState.GenStep σ (Block.nondetElimM tss σ).2 :=
          Block.nondetElimM_genStep tss σ
      have h_step_e : StringGenState.GenStep (Block.nondetElimM tss σ).2
          (Block.nondetElimM ess (Block.nondetElimM tss σ).2).2 := Block.nondetElimM_genStep ess _
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Block.initVars_cons, Stmt.initVars_ite, Block.initVars_nil, List.append_nil]
            at hx ⊢
        rw [List.mem_append] at hx
        rcases hx with h | h
        · rcases ih_t.1 x h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [List.mem_append]; exact Or.inl h_o)
          · exact Or.inr ⟨str, he, h_step_e.subset hin, hnot, hQ⟩
        · rcases ih_e.1 x h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [List.mem_append]; exact Or.inr h_o)
          · exact Or.inr ⟨str, he, hin, fun h_in_σ => hnot (h_step_t.subset h_in_σ), hQ⟩
      · simp only [Block.initVars_cons, Stmt.initVars_ite, Block.initVars_nil, List.append_nil]
        rw [List.nodup_append]
        exact ⟨ih_t.2, ih_e.2, hoistInitClass_disjoint (Block.initVars tss) (Block.initVars ess)
          σ (Block.nondetElimM tss σ).2 _
          h_disj_te h_sf_t h_sf_e _ _ ih_t.1 ih_e.1⟩
  | .ite .nondet tss ess md =>
      rw [Stmt.nondetElimM_ite_nondet_out, Stmt.nondetElimM_ite_nondet_state]
      have h_wf₀ : StringGenState.WF (StringGenState.gen ndelimItePrefix σ).2 :=
          (StringGenState.GenStep.of_gen ndelimItePrefix σ).wf_mono h_wf
      have h_step_g : StringGenState.GenStep σ (StringGenState.gen ndelimItePrefix σ).2 :=
          StringGenState.GenStep.of_gen ndelimItePrefix σ
      -- the source `.ite .nondet` initVars are the branches'.
      have h_uni : (Block.initVars tss ++ Block.initVars ess).Nodup := by
        simpa only [Stmt.initVars_ite] using h_unique
      have h_uni_t : (Block.initVars tss).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_e : (Block.initVars ess).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_disj_te : ∀ a ∈ Block.initVars tss, ∀ b ∈ Block.initVars ess, a ≠ b :=
        (List.nodup_append.mp h_uni).2.2
      have h_sf_src : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars tss ++ Block.initVars ess := by
        intro str hsuf; simpa only [Stmt.initVars_ite] using h_sf str hsuf
      have h_sf_t : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars tss :=
        fun str hsuf hmem => h_sf_src str hsuf (List.mem_append.mpr (Or.inl hmem))
      have h_sf_e : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars ess :=
        fun str hsuf hmem => h_sf_src str hsuf (List.mem_append.mpr (Or.inr hmem))
      have ih_t := Block.nondetElimM_initVars_nodup tss (StringGenState.gen ndelimItePrefix σ).2
          h_wf₀ h_uni_t h_sf_t
      have h_wf_t : StringGenState.WF (Block.nondetElimM tss (StringGenState.gen ndelimItePrefix
          σ).2).2 :=
        (Block.nondetElimM_genStep tss (StringGenState.gen ndelimItePrefix σ).2).wf_mono h_wf₀
      have ih_e := Block.nondetElimM_initVars_nodup ess (Block.nondetElimM tss (StringGenState.gen
          ndelimItePrefix σ).2).2 h_wf_t h_uni_e h_sf_e
      have h_step_t : StringGenState.GenStep (StringGenState.gen ndelimItePrefix σ).2
          (Block.nondetElimM tss (StringGenState.gen ndelimItePrefix σ).2).2 :=
          Block.nondetElimM_genStep tss (StringGenState.gen ndelimItePrefix σ).2
      have h_step_e : StringGenState.GenStep (Block.nondetElimM tss (StringGenState.gen
          ndelimItePrefix σ).2).2
          (Block.nondetElimM ess (Block.nondetElimM tss (StringGenState.gen ndelimItePrefix
              σ).2).2).2 := Block.nondetElimM_genStep ess _
      -- the freshly generated guard, classified over the `σ → (StringGenState.gen ndelimItePrefix
      -- σ).2` gen window.
      have h_guard_iv : Stmt.initVars (P := P) (C := Cmd P)
          (Stmt.cmd (HasInit.init (HasIdent.ident (P := P) (StringGenState.gen ndelimItePrefix σ).1)
            HasBool.boolTy ExprOrNondet.nondet md)) =
          [HasIdent.ident (P := P) (StringGenState.gen ndelimItePrefix σ).1] := by
        with_unfolding_all rfl
      -- branch inits classified together over the post-gen window `(StringGenState.gen
      -- ndelimItePrefix σ).2 → σ₂`.
      have h_branchClass : ∀ y ∈ Block.initVars (Block.nondetElimM tss (StringGenState.gen
          ndelimItePrefix σ).2).1 ++
            Block.initVars (Block.nondetElimM ess (Block.nondetElimM tss (StringGenState.gen
                ndelimItePrefix σ).2).2).1,
          HoistInitClass ndelimKind (Block.initVars tss ++ Block.initVars ess) (StringGenState.gen
              ndelimItePrefix σ).2
            (Block.nondetElimM ess (Block.nondetElimM tss (StringGenState.gen ndelimItePrefix
                σ).2).2).2 y := by
        intro y hy
        rw [List.mem_append] at hy
        rcases hy with h | h
        · rcases ih_t.1 y h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (List.mem_append.mpr (Or.inl h_o))
          · exact Or.inr ⟨str, he, h_step_e.subset hin, hnot, hQ⟩
        · rcases ih_e.1 y h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (List.mem_append.mpr (Or.inr h_o))
          · exact Or.inr ⟨str, he, hin, fun hσ => hnot (h_step_t.subset hσ), hQ⟩
      have h_branchNodup : (Block.initVars (Block.nondetElimM tss (StringGenState.gen
          ndelimItePrefix σ).2).1 ++
            Block.initVars (Block.nondetElimM ess (Block.nondetElimM tss (StringGenState.gen
                ndelimItePrefix σ).2).2).1).Nodup := by
        rw [List.nodup_append]
        exact ⟨ih_t.2, ih_e.2, hoistInitClass_disjoint (Block.initVars tss) (Block.initVars ess)
          (StringGenState.gen ndelimItePrefix σ).2 (Block.nondetElimM tss (StringGenState.gen
              ndelimItePrefix σ).2).2 _
          h_disj_te h_sf_t h_sf_e _ _ ih_t.1 ih_e.1⟩
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Block.initVars_cons, Stmt.initVars_ite, Block.initVars_nil, List.append_nil,
          h_guard_iv, List.singleton_append, List.mem_cons, List.mem_append] at hx
        rcases hx with h_g | h_t | h_e
        · obtain ⟨str, he, hin, hnot, hQ⟩ := ndelim_fresh_class (P := P) ndelimItePrefix σ h_wf
            (ndelimKind_gen.1 σ)
          exact Or.inr ⟨str, h_g.trans he, h_step_e.subset (h_step_t.subset hin), hnot, hQ⟩
        · rcases ih_t.1 x h_t with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [Stmt.initVars_ite, List.mem_append]; exact Or.inl h_o)
          · exact Or.inr ⟨str, he, h_step_e.subset hin,
              fun hσ => hnot (h_step_g.subset hσ), hQ⟩
        · rcases ih_e.1 x h_e with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [Stmt.initVars_ite, List.mem_append]; exact Or.inr h_o)
          · exact Or.inr ⟨str, he, hin,
              fun hσ => hnot (h_step_t.subset (h_step_g.subset hσ)), hQ⟩
      · simp only [Block.initVars_cons, Stmt.initVars_ite, Block.initVars_nil, List.append_nil,
          h_guard_iv, List.singleton_append]
        rw [List.nodup_cons]
        refine ⟨?_, h_branchNodup⟩
        -- guard ∉ branchInits: a guard ident is `∈ stringGens (StringGenState.gen ndelimItePrefix
        -- σ).2 \ σ`; classify each
        -- branch member and refute each cross-class collision.
        intro hmem
        have h_guard_fresh := ndelim_fresh_class (P := P) ndelimItePrefix σ h_wf (ndelimKind_gen.1
            σ)
        obtain ⟨gstr, geq, gin, gnot, gQ⟩ := h_guard_fresh
        rcases h_branchClass _ hmem with h_o | ⟨str, he, hin, hnot, hQ⟩
        · exact h_sf_src gstr gQ (geq ▸ h_o)
        · have : gstr = str := LawfulHasIdent.ident_inj (geq.symm.trans he)
          exact hnot (this ▸ gin)
  | .loop (.det e) m inv body md =>
      rw [Stmt.nondetElimM_loop_det_out, Stmt.nondetElimM_loop_det_state]
      have h_unique' : (Block.initVars body).Nodup := by
        simpa only [Stmt.initVars_loop] using h_unique
      have h_sf' : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars body := by
        intro str hsuf; simpa only [Stmt.initVars_loop] using h_sf str hsuf
      have ih := Block.nondetElimM_initVars_nodup body σ h_wf h_unique' h_sf'
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Block.initVars_cons, Stmt.initVars_loop, Block.initVars_nil,
          List.append_nil] at hx ⊢
        simpa only [Stmt.initVars_loop] using ih.1 x hx
      · simp only [Block.initVars_cons, Stmt.initVars_loop, Block.initVars_nil, List.append_nil]
        exact ih.2
  | .loop .nondet m inv body md =>
      rw [Stmt.nondetElimM_loop_nondet_out, Stmt.nondetElimM_loop_nondet_state]
      have h_wf₀ : StringGenState.WF (StringGenState.gen ndelimLoopPrefix σ).2 :=
        (StringGenState.GenStep.of_gen ndelimLoopPrefix σ).wf_mono h_wf
      have h_step_g : StringGenState.GenStep σ (StringGenState.gen ndelimLoopPrefix σ).2 :=
        StringGenState.GenStep.of_gen ndelimLoopPrefix σ
      have h_unique' : (Block.initVars body).Nodup := by
        simpa only [Stmt.initVars_loop] using h_unique
      have h_sf' : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars body := by
        intro str hsuf; simpa only [Stmt.initVars_loop] using h_sf str hsuf
      have ih := Block.nondetElimM_initVars_nodup body (StringGenState.gen ndelimLoopPrefix σ).2
          h_wf₀ h_unique' h_sf'
      have h_step_body : StringGenState.GenStep (StringGenState.gen ndelimLoopPrefix σ).2
          (Block.nondetElimM body (StringGenState.gen ndelimLoopPrefix σ).2).2 :=
        Block.nondetElimM_genStep body _
      -- the new loop body is `body' ++ [havoc guard]`; havoc has no inits.
      have h_havoc_init : Block.initVars (P := P) (C := Cmd P)
          [Stmt.cmd (HasHavoc.havoc (HasIdent.ident (P := P) (StringGenState.gen ndelimLoopPrefix
              σ).1) md)] = [] := by
        with_unfolding_all rfl
      have h_guard_iv : Stmt.initVars (P := P) (C := Cmd P)
          (Stmt.cmd (HasInit.init (HasIdent.ident (P := P) (StringGenState.gen ndelimLoopPrefix
              σ).1)
            HasBool.boolTy ExprOrNondet.nondet md)) =
          [HasIdent.ident (P := P) (StringGenState.gen ndelimLoopPrefix σ).1] := by
        with_unfolding_all rfl
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Block.initVars_cons, Stmt.initVars_loop, Block.initVars_nil, List.append_nil,
          h_guard_iv, List.singleton_append, List.mem_cons] at hx
        rw [Block.initVars_append, h_havoc_init, List.append_nil] at hx
        simp only [Stmt.initVars_loop]
        rcases hx with h_g | h_body
        · obtain ⟨str, he, hin, hnot, hQ⟩ := ndelim_fresh_class (P := P) ndelimLoopPrefix σ h_wf
            (ndelimKind_gen.2 σ)
          exact Or.inr ⟨str, h_g.trans he, h_step_body.subset hin, hnot, hQ⟩
        · rcases ih.1 x h_body with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl h_o
          · exact Or.inr ⟨str, he, hin, fun hσ => hnot (h_step_g.subset hσ), hQ⟩
      · simp only [Block.initVars_cons, Stmt.initVars_loop, Block.initVars_nil, List.append_nil,
          h_guard_iv, List.singleton_append]
        rw [Block.initVars_append, h_havoc_init, List.append_nil, List.nodup_cons]
        refine ⟨?_, ih.2⟩
        intro hmem
        obtain ⟨gstr, geq, gin, gnot, gQ⟩ := ndelim_fresh_class (P := P) ndelimLoopPrefix σ h_wf
            (ndelimKind_gen.2 σ)
        rcases ih.1 _ hmem with h_o | ⟨str, he, hin, hnot, hQ⟩
        · exact h_sf' gstr gQ (geq ▸ h_o)
        · have : gstr = str := LawfulHasIdent.ident_inj (geq.symm.trans he)
          exact hnot (this ▸ gin)
  | .exit lbl md =>
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars_nil, Stmt.initVars,
          Stmt.definedVars,
          List.append_nil] at hx; exact (List.not_mem_nil hx).elim
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars_nil, Stmt.initVars,
          Stmt.definedVars,
          List.append_nil]; exact List.nodup_nil
  | .funcDecl d md =>
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars_nil, Stmt.initVars,
          Stmt.definedVars,
          List.append_nil] at hx; exact (List.not_mem_nil hx).elim
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars_nil, Stmt.initVars,
          Stmt.definedVars,
          List.append_nil]; exact List.nodup_nil
  | .typeDecl t md =>
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars_nil, Stmt.initVars,
          Stmt.definedVars,
          List.append_nil] at hx; exact (List.not_mem_nil hx).elim
      · simp only [Stmt.nondetElimM, Block.initVars_cons, Block.initVars_nil, Stmt.initVars,
          Stmt.definedVars,
          List.append_nil]; exact List.nodup_nil
  termination_by sizeOf s

theorem Block.nondetElimM_initVars_nodup {P : PureExpr} [HasIdent P] [LawfulHasIdent P] [HasFvar P]
    [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) (h_wf : StringGenState.WF σ)
    (h_unique : (Block.initVars ss).Nodup)
    (h_sf : ∀ str : String, ndelimKind str → HasIdent.ident (P := P) str ∉ Block.initVars ss) :
    (∀ x ∈ Block.initVars (P := P) (Block.nondetElimM ss σ).1,
        HoistInitClass ndelimKind (Block.initVars ss) σ (Block.nondetElimM ss σ).2 x)
      ∧ (Block.initVars (P := P) (Block.nondetElimM ss σ).1).Nodup := by
  match ss with
  | [] =>
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [Block.nondetElimM, Block.initVars_nil] at hx; exact (List.not_mem_nil hx).elim
      · simp only [Block.nondetElimM, Block.initVars_nil]; exact List.nodup_nil
  | s :: rest =>
      rw [Block.nondetElimM_cons_out, Block.nondetElimM_cons_state]
      have h_uni : (Stmt.initVars s ++ Block.initVars rest).Nodup := by
        simpa only [Block.initVars_cons] using h_unique
      have h_uni_s : (Stmt.initVars s).Nodup := (List.nodup_append.mp h_uni).1
      have h_uni_r : (Block.initVars rest).Nodup := (List.nodup_append.mp h_uni).2.1
      have h_disj_sr : ∀ a ∈ Stmt.initVars s, ∀ b ∈ Block.initVars rest, a ≠ b :=
        (List.nodup_append.mp h_uni).2.2
      have h_sf_s : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Stmt.initVars s := by
        intro str hsuf hmem; exact h_sf str hsuf (by
          rw [Block.initVars_cons, List.mem_append]; exact Or.inl hmem)
      have h_sf_r : ∀ str : String, ndelimKind str →
          HasIdent.ident (P := P) str ∉ Block.initVars rest := by
        intro str hsuf hmem; exact h_sf str hsuf (by
          rw [Block.initVars_cons, List.mem_append]; exact Or.inr hmem)
      have ih_s := Stmt.nondetElimM_initVars_nodup s σ h_wf h_uni_s h_sf_s
      have h_wf_s : StringGenState.WF (Stmt.nondetElimM s σ).2 :=
        (Stmt.nondetElimM_genStep s σ).wf_mono h_wf
      have ih_r := Block.nondetElimM_initVars_nodup rest (Stmt.nondetElimM s σ).2 h_wf_s h_uni_r
          h_sf_r
      have h_step_s : StringGenState.GenStep σ (Stmt.nondetElimM s σ).2 := Stmt.nondetElimM_genStep
          s σ
      have h_step_r : StringGenState.GenStep (Stmt.nondetElimM s σ).2
          (Block.nondetElimM rest (Stmt.nondetElimM s σ).2).2 := Block.nondetElimM_genStep rest _
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Block.initVars_append] at hx
        rw [Block.initVars_cons]
        rw [List.mem_append] at hx
        rcases hx with h | h
        · rcases ih_s.1 x h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [List.mem_append]; exact Or.inl h_o)
          · exact Or.inr ⟨str, he, h_step_r.subset hin, hnot, hQ⟩
        · rcases ih_r.1 x h with h_o | ⟨str, he, hin, hnot, hQ⟩
          · exact Or.inl (by rw [List.mem_append]; exact Or.inr h_o)
          · exact Or.inr ⟨str, he, hin, fun h_in_σ => hnot (h_step_s.subset h_in_σ), hQ⟩
      · rw [Block.initVars_append, List.nodup_append]
        exact ⟨ih_s.2, ih_r.2, hoistInitClass_disjoint (Stmt.initVars s) (Block.initVars rest)
          σ (Stmt.nondetElimM s σ).2 _
          h_disj_sr h_sf_s h_sf_r _ _ ih_s.1 ih_r.1⟩
  termination_by sizeOf ss
end

/-- A `.cmd (init _ _ .nondet _)` has an empty-vars RHS, so any names list is
RHS-fresh in it. -/
private theorem init_nondet_rhsfree {P : PureExpr} [HasVarsPure P P.Expr] [HasFvars P] (names : List
    P.Ident) (ident : P.Ident)
    (ty : P.Ty) (md : MetaData P) :
    Stmt.namesFreshInRhsExprs (P := P) names
      (Stmt.cmd (HasInit.init ident ty ExprOrNondet.nondet md)) := by
  show Stmt.namesFreshInRhsExprs (P := P) names
    (Stmt.cmd (Cmd.init ident ty ExprOrNondet.nondet md))
  simp only [Stmt.namesFreshInRhsExprs, ExprOrNondet.getVars]
  intro z _ hz; simp at hz

/-- A `.cmd (havoc _)` has an empty-vars RHS, so any names list is RHS-fresh in
it. -/
private theorem havoc_rhsfree {P : PureExpr} [HasVarsPure P P.Expr] [HasFvars P] (names : List
    P.Ident) (ident : P.Ident)
    (md : MetaData P) :
    Stmt.namesFreshInRhsExprs (P := P) names
      (Stmt.cmd (HasHavoc.havoc ident md)) := by
  show Stmt.namesFreshInRhsExprs (P := P) names
    (Stmt.cmd (Cmd.set ident ExprOrNondet.nondet md))
  simp only [Stmt.namesFreshInRhsExprs, ExprOrNondet.getVars]
  intro z _ hz; simp at hz

mutual
/-- `nondetElim` preserves `namesFreshInRhsExprs names` for a fixed name list:
all introduced command RHS positions read nothing, and source RHS positions are
unchanged. -/
theorem Stmt.nondetElimM_namesFreshInRhsExprs {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P]
    [HasBool P] [HasVarsPure P P.Expr] (names : List P.Ident)
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (h : Stmt.namesFreshInRhsExprs (P := P) names s) :
    Block.namesFreshInRhsExprs (P := P) names (Stmt.nondetElimM s σ).1 := by
  match s with
  | .cmd c =>
      simp only [Stmt.nondetElimM, Block.namesFreshInRhsExprs, and_true]
      exact h
  | .block lbl bss md =>
      rw [Stmt.nondetElimM_block_out]
      simp only [Stmt.namesFreshInRhsExprs] at h
      simp only [Block.namesFreshInRhsExprs, Stmt.namesFreshInRhsExprs, and_true]
      exact Block.nondetElimM_namesFreshInRhsExprs names bss σ h
  | .ite (.det e) tss ess md =>
      rw [Stmt.nondetElimM_ite_det_out]
      simp only [Stmt.namesFreshInRhsExprs] at h
      simp only [Block.namesFreshInRhsExprs, Stmt.namesFreshInRhsExprs, and_true]
      exact ⟨Block.nondetElimM_namesFreshInRhsExprs names tss σ h.1,
             Block.nondetElimM_namesFreshInRhsExprs names ess _ h.2⟩
  | .ite .nondet tss ess md =>
      rw [Stmt.nondetElimM_ite_nondet_out]
      simp only [Stmt.namesFreshInRhsExprs] at h
      simp only [Block.namesFreshInRhsExprs, and_true]
      refine ⟨init_nondet_rhsfree _ _ _ _, ?_⟩
      simp only [Stmt.namesFreshInRhsExprs]
      exact ⟨Block.nondetElimM_namesFreshInRhsExprs names tss _ h.1,
             Block.nondetElimM_namesFreshInRhsExprs names ess _ h.2⟩
  | .loop (.det e) m inv body md =>
      rw [Stmt.nondetElimM_loop_det_out]
      simp only [Stmt.namesFreshInRhsExprs] at h
      simp only [Block.namesFreshInRhsExprs, Stmt.namesFreshInRhsExprs, and_true]
      exact Block.nondetElimM_namesFreshInRhsExprs names body σ h
  | .loop .nondet m inv body md =>
      rw [Stmt.nondetElimM_loop_nondet_out]
      simp only [Stmt.namesFreshInRhsExprs] at h
      simp only [Block.namesFreshInRhsExprs, Stmt.namesFreshInRhsExprs, and_true]
      have h_havoc : Block.namesFreshInRhsExprs (P := P) names
          [Stmt.cmd (HasHavoc.havoc (HasIdent.ident (P := P) (StringGenState.gen ndelimLoopPrefix
              σ).1) md)] := by
        simp only [Block.namesFreshInRhsExprs, and_true]
        exact havoc_rhsfree _ _ _
      refine ⟨init_nondet_rhsfree _ _ _ _, ?_⟩
      exact Block.namesFreshInRhsExprs_append _ _
        (Block.nondetElimM_namesFreshInRhsExprs names body _ h) h_havoc
  | .exit lbl md =>
      simp only [Stmt.nondetElimM, Block.namesFreshInRhsExprs, Stmt.namesFreshInRhsExprs,
        and_true]
  | .funcDecl d md =>
      simp only [Stmt.nondetElimM, Block.namesFreshInRhsExprs, Stmt.namesFreshInRhsExprs,
        and_true]
  | .typeDecl t md =>
      simp only [Stmt.nondetElimM, Block.namesFreshInRhsExprs, Stmt.namesFreshInRhsExprs,
        and_true]
  termination_by sizeOf s

theorem Block.nondetElimM_namesFreshInRhsExprs {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P]
    [HasBool P] [HasVarsPure P P.Expr] (names : List P.Ident)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h : Block.namesFreshInRhsExprs (P := P) names ss) :
    Block.namesFreshInRhsExprs (P := P) names (Block.nondetElimM ss σ).1 := by
  match ss with
  | [] => simp only [Block.nondetElimM, Block.namesFreshInRhsExprs]
  | s :: rest =>
      rw [Block.nondetElimM_cons_out]
      simp only [Block.namesFreshInRhsExprs] at h
      exact Block.namesFreshInRhsExprs_append _ _
        (Stmt.nondetElimM_namesFreshInRhsExprs names s σ h.1)
        (Block.nondetElimM_namesFreshInRhsExprs names rest _ h.2)
  termination_by sizeOf ss
end

/-- An `ndelimKind` guard ident is RHS-fresh in the kind-free source: it is the
identifier of an `ndelimKind` label, and the source reads no `ndelimKind` ident
in any expression (`exprsShapeFree ndelimKind`), so a fortiori not in any RHS. -/
private theorem ndelim_guard_namesFreshInRhsExprs_src {P : PureExpr} [HasIdent P] [HasVarsPure P
    P.Expr] [HasFvars P]
    {str : String} (h_kind : ndelimKind str) (ss : List (Stmt P (Cmd P)))
    (h_sf : Block.exprsShapeFree (P := P) ndelimKind ss) :
    Block.namesFreshInRhsExprs (P := P) [HasIdent.ident (P := P) str] ss :=
  Block.namesFreshInRhsExprs_of_namesFreshInExprs _ ss
    (Block.namesFreshInExprs_of_exprsShapeFree' (Q := ndelimKind)
      (fun z hz => by
        rw [List.mem_singleton] at hz; exact ⟨str, hz, h_kind⟩)
      ss h_sf)

/-- Every name in `initVars (nondetElim ss)` is RHS-fresh in the source `ss`:
source inits inherit the source RHS-freshness; freshly generated `ndelimKind`
guards are RHS-fresh by source kind-freedom. -/
theorem nondetElim_initVars_namesFreshInRhsExprs_src {P : PureExpr} [HasIdent P] [HasFvar P]
    [HasFvars P] [HasBool P] [HasVarsPure P P.Expr]
    (ss : List (Stmt P (Cmd P)))
    (h_src_rhs : Block.namesFreshInRhsExprs (P := P) (Block.initVars ss) ss)
    (h_sf : Block.exprsShapeFree (P := P) ndelimKind ss) :
    Block.namesFreshInRhsExprs (P := P)
      (Block.initVars (Block.nondetElim ss)) ss := by
  refine Block.namesFreshInRhsExprs_of_forall_mem _ ss (fun z hz => ?_)
  rcases Block.nondetElimM_initVars_classified ss StringGenState.emp z hz with
    h_src | ⟨str, h_eq, h_kind⟩
  · exact Block.namesFreshInRhsExprs_subset
      (fun w hw => by rw [List.mem_singleton] at hw; exact hw ▸ h_src) ss h_src_rhs
  · exact h_eq ▸ ndelim_guard_namesFreshInRhsExprs_src h_kind ss h_sf

/-- The `namesFreshInRhsExprs (initVars …) …` conjunct of
`hoistedNamesFreshInRhsAndGuards` holds on the `nondetElim` output: the source
fact (every output init RHS-fresh in the source) is transported through the pass
(which only adds variable-free command RHS positions). -/
theorem nondetElim_namesFreshInRhsExprs {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P]
    [HasBool P] [HasVarsPure P P.Expr]
    (ss : List (Stmt P (Cmd P)))
    (h_src_rhs : Block.namesFreshInRhsExprs (P := P) (Block.initVars ss) ss)
    (h_sf : Block.exprsShapeFree (P := P) ndelimKind ss) :
    Block.namesFreshInRhsExprs (P := P)
      (Block.initVars (Block.nondetElim ss)) (Block.nondetElim ss) :=
  Block.nondetElimM_namesFreshInRhsExprs _ ss StringGenState.emp
    (nondetElim_initVars_namesFreshInRhsExprs_src ss h_src_rhs h_sf)

/-- Top-level Direction-A bridge: `nondetElim` establishes the
`hoistedNamesFreshInRhsAndGuards` postcondition on its output, given the
front-end source facts (its own `hoistedNamesFreshInRhsAndGuards` and its
`ndelimKind`-freedom). This discharges the hoist `h_fresh` precondition at
the `nondetElim` output: the predicate is the RHS-only `initVars` freshness,
preserved verbatim because `nondetElim` only ever adds variable-free command
RHS positions (its fresh guard is read only in a `.ite`/`.loop` guard). -/
theorem nondetElim_hoistedNamesFreshInRhsAndGuards {P : PureExpr} [HasIdent P] [LawfulHasIdent P]
    [HasFvar P] [HasFvars P] [HasBool P] [HasVarsPure P P.Expr] [LawfulHasFvar P] [LawfulHasFvars P]
    (ss : List (Stmt P (Cmd P)))
    (h_fresh_src : Block.hoistedNamesFreshInRhsAndGuards (P := P) ss)
    (h_sf : Block.exprsShapeFree (P := P) ndelimKind ss) :
    Block.hoistedNamesFreshInRhsAndGuards (P := P) (Block.nondetElim ss) := by
  unfold Block.hoistedNamesFreshInRhsAndGuards at h_fresh_src ⊢
  exact nondetElim_namesFreshInRhsExprs ss h_fresh_src h_sf

mutual
/-- `Stmt.liftInitsInLoopBody` preserves exit coverage on its residual (`.2`)
component: lifted inits become sibling `.cmd`s, and `.block`/`.exit`/`.loop` are
structurally preserved. -/
theorem Stmt.liftInitsInLoopBody_exitsCoveredByBlocks {P : PureExpr}
    (labels : List String) (s : Stmt P (Cmd P))
    (h : Stmt.exitsCoveredByBlocks labels s) :
    Block.exitsCoveredByBlocks labels
      (Stmt.liftInitsInLoopBody s).2 := by
  match s with
  | .cmd c =>
    cases c <;>
      (simp only [Stmt.liftInitsInLoopBody]; exact ⟨trivial, trivial⟩)
  | .block lbl bss md =>
    simp only [Stmt.liftInitsInLoopBody]
    exact coveredBlock_singleton labels (.block lbl _ md)
      (Block.liftInitsInLoopBody_exitsCoveredByBlocks (lbl :: labels) bss
        (by simpa [Stmt.exitsCoveredByBlocks] using h))
  | .ite g tss ess md =>
    simp only [Stmt.liftInitsInLoopBody]
    obtain ⟨ht, he⟩ := h
    exact coveredBlock_singleton labels (.ite g _ _ md)
      ⟨Block.liftInitsInLoopBody_exitsCoveredByBlocks labels tss ht,
       Block.liftInitsInLoopBody_exitsCoveredByBlocks labels ess he⟩
  | .loop g m inv body md =>
    simp only [Stmt.liftInitsInLoopBody]
    exact coveredBlock_singleton labels (.loop g m inv body md) h
  | .exit lbl md =>
    simp only [Stmt.liftInitsInLoopBody]
    exact coveredBlock_singleton labels (.exit lbl md) h
  | .funcDecl d md =>
    simp only [Stmt.liftInitsInLoopBody]
    exact coveredBlock_singleton labels (.funcDecl d md) trivial
  | .typeDecl t md =>
    simp only [Stmt.liftInitsInLoopBody]
    exact coveredBlock_singleton labels (.typeDecl t md) trivial
  termination_by sizeOf s

/-- `Block.liftInitsInLoopBody` preserves exit coverage on its residual. -/
theorem Block.liftInitsInLoopBody_exitsCoveredByBlocks {P : PureExpr}
    (labels : List String) (ss : List (Stmt P (Cmd P)))
    (h : Block.exitsCoveredByBlocks labels ss) :
    Block.exitsCoveredByBlocks labels
      (Block.liftInitsInLoopBody ss).2 := by
  match ss with
  | [] => simp only [Block.liftInitsInLoopBody]; exact trivial
  | s :: rest =>
    rw [Block.liftInitsInLoopBody]
    exact block_exitsCoveredByBlocks_append labels _ _
      (Stmt.liftInitsInLoopBody_exitsCoveredByBlocks labels s h.1)
      (Block.liftInitsInLoopBody_exitsCoveredByBlocks labels rest h.2)
  termination_by sizeOf ss
end

mutual
/-- `Stmt.hoistLoopPrefixInits` preserves exit coverage: the hoisted `init`
prelude is `.cmd`s (trivially covered), and the loop body's exits are covered by
the same labels before and after (the hoist neither relabels `.block`s nor moves
`.exit`s across a `.block` boundary). -/
theorem Stmt.hoistP_exitsCoveredByBlocks {P : PureExpr}
    (labels : List String) (s : Stmt P (Cmd P))
    (h : Stmt.exitsCoveredByBlocks labels s) :
    Block.exitsCoveredByBlocks labels
      (Stmt.hoistLoopPrefixInits s) := by
  match s with
  | .cmd c =>
    simp only [Stmt.hoistLoopPrefixInits]; exact coveredBlock_singleton labels (.cmd c) trivial
  | .block lbl bss md =>
    simp only [Stmt.hoistLoopPrefixInits]
    exact coveredBlock_singleton labels (.block lbl _ md)
      (Block.hoistP_exitsCoveredByBlocks (lbl :: labels) bss
        (by simpa [Stmt.exitsCoveredByBlocks] using h))
  | .ite g tss ess md =>
    simp only [Stmt.hoistLoopPrefixInits]
    obtain ⟨ht, he⟩ := h
    exact coveredBlock_singleton labels (.ite g _ _ md)
      ⟨Block.hoistP_exitsCoveredByBlocks labels tss ht,
       Block.hoistP_exitsCoveredByBlocks labels ess he⟩
  | .loop g m inv body md =>
    simp only [Stmt.hoistLoopPrefixInits]
    refine block_exitsCoveredByBlocks_append labels _ _
      (all_cmd_exitsCoveredByBlocks labels _
        (by intro s hs;
            simp only [List.mem_map] at hs;
            obtain ⟨c, _, hc⟩ := hs;
            exact ⟨c, hc.symm⟩))
      ?_
    exact coveredBlock_singleton labels (.loop g m inv _ md)
      (Block.liftInitsInLoopBody_exitsCoveredByBlocks labels _
        (Block.hoistP_exitsCoveredByBlocks labels body
          (by simpa [Stmt.exitsCoveredByBlocks] using h)))
  | .exit lbl md =>
    simp only [Stmt.hoistLoopPrefixInits]
    exact coveredBlock_singleton labels (.exit lbl md) h
  | .funcDecl d md =>
    simp only [Stmt.hoistLoopPrefixInits]
    exact coveredBlock_singleton labels (.funcDecl d md) trivial
  | .typeDecl t md =>
    simp only [Stmt.hoistLoopPrefixInits]
    exact coveredBlock_singleton labels (.typeDecl t md) trivial
  termination_by sizeOf s

/-- `Block.hoistLoopPrefixInits` preserves exit coverage. -/
theorem Block.hoistP_exitsCoveredByBlocks {P : PureExpr}
    (labels : List String) (ss : List (Stmt P (Cmd P)))
    (h : Block.exitsCoveredByBlocks labels ss) :
    Block.exitsCoveredByBlocks labels
      (Block.hoistLoopPrefixInits ss) := by
  match ss with
  | [] => simp only [Block.hoistLoopPrefixInits]; exact trivial
  | s :: rest =>
    rw [Block.hoistLoopPrefixInits]
    exact block_exitsCoveredByBlocks_append labels _ _
      (Stmt.hoistP_exitsCoveredByBlocks labels s h.1)
      (Block.hoistP_exitsCoveredByBlocks labels rest h.2)
  termination_by sizeOf ss
end

end NondetElimShapeFree


end Imperative

end -- public section
