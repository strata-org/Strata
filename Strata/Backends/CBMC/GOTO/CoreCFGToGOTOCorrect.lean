/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.Semantics
public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOInvariants
public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Util.Relations
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.StatementSemantics

public section

/-! # Forward simulation: Core DetCFG → CBMC GOTO

This module states and proves (modulo well-marked obligations) the main
correctness theorem for the `coreCFGToGotoTransform` translation pipeline:

> If a `Core.DetCFG` run terminates in store `σ'` with failure flag `b`,
> then the translated GOTO program reaches the same final `(σ', b)`.

## Scope

* **Source language**: `Core.DetCFG` with `EvalDetBlock` step relation,
  restricted to the admitted fragment (no `.call`, no `.cover`, no
  nondet `.init` — see `Core.CmdExt.isAdmittedCmd`).
* **Target language**: GOTO `Program`s under the small-step
  `StepGoto`/`StepGotoStar` semantics defined in `Semantics.lean`.
* **Theorem shape**: forward simulation for terminating runs, mirroring
  the existing pattern in `Strata.Transform.DetToKleeneCorrect`.

## Hypotheses (axiomatized)

* **Expression-translation correctness** — the GOTO evaluator agrees with
  Core's evaluator on every translated expression. Captured as
  `ExprTranslationPreservesEval`.
* **Translator well-formedness** — the program output by
  `coreCFGToGotoTransform` is a `WellFormedTranslation` of its input CFG.
  Consumed as a hypothesis; discharging it is a separate proof obligation
  (see `CoreCFGToGOTOInvariants.lean`).

## Proof outline

1. **Simulation relation `Sim`** — relates a `CFGConfig` to a `GotoConfig`
   via the well-formedness predicate's `labelMap`.
2. **Block simulation lemma** — one `EvalDetBlock` derivation translates to
   a `StepGotoStar` covering the corresponding GOTO instruction range.
   Internally inducts on the command list (commands map to 1–2 GOTO steps),
   then handles the transfer.
3. **Transfer simulation** — `condGoto` corresponds to the two-`GOTO`
   pattern (one conditional + one unconditional); `finish` corresponds to
   reaching `END_FUNCTION` via fall-through.
4. **Main theorem** — induction on `ReflTrans` length, using block
   simulation at each step. -/

namespace CProverGOTO

open Imperative

/-! ## Hypothesis: expression-translation correctness

We axiomatize the relationship between Core's expression evaluator (`δ`) and
the GOTO expression evaluator (`δ_goto`) used by `StepGoto`. The translator
`Lambda.LExpr.toGotoExprCtx` should preserve evaluation; this hypothesis
states that explicitly without the proof. Discharging it is a separate
project — its proof involves a mutual induction over the expression
language tying GOTO operator semantics to Core's. -/

/-- Expression-translation correctness as a global property: there is a
*function* `tx` (the expression translator, e.g. `Lambda.LExpr.toGotoExprCtx`
specialized to the success path) such that every Core expression and its
GOTO translation are `ExprTranslated`-equivalent under the given evaluators.

The simulation theorem takes a value of this type as a hypothesis. The
function form (rather than per-expression existentials) lets us name the
specific GOTO expression for any given Core source — needed when relating
a `condGoto cond _ _` transfer in DetCFG to the emitted GOTO instruction
whose guard is the translation of `cond`. -/
structure ExprTranslationPreservesEval
    (δ : SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression) where
  /-- The expression translator. -/
  tx : Core.Expression.Expr → Expr
  /-- For every Core expression, the translator produces an evaluation-
  equivalent GOTO expression. -/
  tx_correct : ∀ e_core,
    ExprTranslated δ δ_goto δ_goto_bool e_core (tx e_core)
  /-- The translator commutes with negation, up to translation: the GOTO
  side's `Expr.not` of a translated expression is the translation of
  Core's `HasNot.not` of the source. (The CFG-to-GOTO translator emits
  `Expr.not (tx cond)` for `condGoto cond _ _`, while the DetCFG step
  relation evaluates `δ σ cond`. Combined with `WellFormedSemanticEvalBool`
  and `WellFormedSemanticEvalGotoBool`, this lets us bridge the two sides
  on conditional transfers.) -/
  tx_commutes_not :
    ∀ e_core,
      tx (HasNot.not (P := Core.Expression) e_core) = (tx e_core).not

/-! ## Simulation relation

Relates DetCFG configurations to GOTO configurations under a
`WellFormedTranslation` witness. -/

/-- The simulation invariant.

* A `cont l σ failed` configuration corresponds to running at the `pc` for
  `l`'s `LOCATION` instruction with the same store and failure flag.
* A `terminal σ failed` configuration corresponds to a GOTO `terminal`
  configuration with the same store and failure flag. -/
inductive Sim (cfg : Core.DetCFG) (pgm : Program)
    {δ : Imperative.SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (wf : WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool) :
    CFGConfig String Core.Expression → GotoConfig Core.Expression → Prop where
  | sim_cont :
    wf.labelMap l = some pc →
    Sim cfg pgm wf (.cont l σ failed) (.running pc σ failed)
  | sim_terminal :
    Sim cfg pgm wf (.terminal σ failed) (.terminal σ failed)

/-! ## Inversion lemma: `EvalCommand` on a `.cmd` collapses to `EvalCmd` -/

/-- The Core command-step relation `EvalCommand`, applied to a `.cmd c`
constructor, is exactly the imperative `EvalCmd` relation on the inner
command. The `.call` constructor is unreachable here because the LHS
pattern matches `.cmd c`. -/
theorem evalCommand_cmd_iff_evalCmd
    (π : String → Option Core.Procedure)
    (φ : Core.CoreEval → Imperative.PureFunc Core.Expression → Core.CoreEval)
    (δ : Imperative.SemanticEval Core.Expression)
    (σ σ' : Imperative.SemanticStore Core.Expression)
    (c : Imperative.Cmd Core.Expression) (failed : Bool) :
    Core.EvalCommand π φ δ σ (.cmd c) σ' failed ↔
      Imperative.EvalCmd (P := Core.Expression) δ σ c σ' failed := by
  constructor
  · intro h
    cases h with
    | cmd_sem h => exact h
  · intro h
    exact .cmd_sem h

/-! ## Per-command simulation -/

/-- `UpdateState P σ x v σ` holds whenever `σ x = some v`: rewriting a
variable to the value it already has is a fixed point. -/
private theorem UpdateState_self
    {P : Imperative.PureExpr} {σ : Imperative.SemanticStore P}
    {x : P.Ident} {v : P.Expr}
    (h : σ x = some v) : Imperative.UpdateState P σ x v σ :=
  .update h h (fun _ _ => rfl)

/-- A single `EvalCmd` step on a plain command corresponds to a
`StepGotoStar` trace of length `c.gotoInstrCount` over the GOTO
instructions emitted for `c`.

This is proved by `cases` on both the evaluation step and the
`CmdEmittedAt` layout, producing one or two `StepGoto` constructor
applications per case. All sub-cases are closed:
* `eval_init × init_det` uses `step_decl` then `step_assign_nondet` as
  a no-op (via `UpdateState_self`), sidestepping the δ_goto monotonicity
  question that `step_assign` would have raised;
* `eval_set_nondet × set_nondet` uses the new `step_assign_nondet`;
* `eval_cover` is unreachable under the tightened `isAdmittedCmd`. -/
theorem single_cmd_simulation
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_wf_bool_goto : WellFormedSemanticEvalGotoBool δ_goto_bool)
    (pgm : Program) (c : Imperative.Cmd Core.Expression)
    (σ σ' : Imperative.SemanticStore Core.Expression)
    (failed cmd_failed : Bool)
    (h_admitted : Core.CmdExt.isAdmittedCmd (.cmd c) = true)
    (h_eval : Imperative.EvalCmd (P := Core.Expression) δ σ c σ' cmd_failed)
    (pc : Nat)
    (h_layout : CmdEmittedAt δ δ_goto δ_goto_bool pgm pc c)
    : StepGotoStar Core.Expression δ_goto δ_goto_bool pgm
        (.running pc σ failed)
        (.running (pc + Imperative.Cmd.gotoInstrCount c) σ' (failed || cmd_failed)) := by
  unfold StepGotoStar
  cases h_eval with
  | eval_init h_eval h_init _ =>
    -- `.init v ty (.det e) md` translates to DECL + ASSIGN. The two-step
    -- target trace lands at the same store as the source's one-step
    -- `eval_init` by:
    --  (1) `step_decl` with the source's InitState `h_init`, which puts
    --      x ↦ v into σ to get σ';
    --  (2) `step_assign_nondet` (rather than `step_assign`) on σ' as a
    --      no-op via `UpdateState_self`. We sidestep the δ_goto
    --      evaluation premise of `step_assign` (which would otherwise
    --      require expression-evaluator monotonicity from σ to σ').
    --      `step_assign_nondet` only requires `instr.type = .ASSIGN`,
    --      which the `init_det` layout supplies via `h_assn_ty`.
    show ReflTrans _ _ (GotoConfig.running (pc + 2) _ (failed || false))
    rw [Bool.or_false]
    cases h_layout with
    | init_det _ _ _ _ _ _ h_decl_at h_decl_ty h_assn_at h_assn_ty
                _ h_assn_code h_translated =>
      -- After step_decl's InitState lands at σ', we have σ' x = some v.
      cases h_init with
      | init hpre hpost hother =>
        have h_upd_self := UpdateState_self hpost
        exact ReflTrans.step _ _ _
          (StepGoto.step_decl h_decl_at h_decl_ty (.init hpre hpost hother))
          (ReflTrans.step _ _ _
            (StepGoto.step_assign_nondet h_assn_at h_assn_ty h_upd_self)
            (ReflTrans.refl _))
  | eval_init_unconstrained h_init _ =>
    -- `.init v ty .nondet md` — single DECL.
    show ReflTrans _ _ (GotoConfig.running (pc + 1) _ (failed || false))
    rw [Bool.or_false]
    cases h_layout with
    | init_nondet _ _ _ _ h_decl_at h_decl_ty =>
      refine ReflTrans.step _ _ _ ?_ (ReflTrans.refl _)
      exact StepGoto.step_decl h_decl_at h_decl_ty h_init
  | eval_set h_eval h_upd _ =>
    -- `.set v (.det e) md` — single ASSIGN.
    show ReflTrans _ _ (GotoConfig.running (pc + 1) _ (failed || false))
    rw [Bool.or_false]
    cases h_layout with
    | set_det _ _ _ _ h_assn_at h_assn_ty _ h_assn_code h_translated =>
      have h_goto_eval := (h_translated.value_agree _ _).mp h_eval
      refine ReflTrans.step _ _ _ ?_ (ReflTrans.refl _)
      exact StepGoto.step_assign h_assn_at h_assn_ty h_goto_eval h_upd
  | eval_set_nondet h_upd _ =>
    -- `.set v .nondet md` — single ASSIGN with nondet RHS. Uses the
    -- new `step_assign_nondet` constructor.
    show ReflTrans _ _ (GotoConfig.running (pc + 1) _ (failed || false))
    rw [Bool.or_false]
    cases h_layout with
    | set_nondet _ _ _ h_assn_at h_assn_ty _ =>
      refine ReflTrans.step _ _ _ ?_ (ReflTrans.refl _)
      exact StepGoto.step_assign_nondet h_assn_at h_assn_ty h_upd
  | eval_assert_pass h_eval _ =>
    show ReflTrans _ _ (GotoConfig.running (pc + 1) _ (failed || false))
    rw [Bool.or_false]
    cases h_layout with
    | assert_emit _ _ _ _ h_at h_ty _ h_guard h_translated =>
      have h_goto_eval := (h_translated.bool_tt_agree _).mp h_eval
      rw [← h_guard] at h_goto_eval
      refine ReflTrans.step _ _ _ ?_ (ReflTrans.refl _)
      exact StepGoto.step_assert_pass h_at h_ty h_goto_eval
  | eval_assert_fail h_eval _ =>
    show ReflTrans _ _ (GotoConfig.running (pc + 1) _ (failed || true))
    rw [Bool.or_true]
    cases h_layout with
    | assert_emit _ _ _ _ h_at h_ty _ h_guard h_translated =>
      have h_goto_eval := (h_translated.bool_ff_agree _).mp h_eval
      rw [← h_guard] at h_goto_eval
      refine ReflTrans.step _ _ _ ?_ (ReflTrans.refl _)
      exact StepGoto.step_assert_fail h_at h_ty h_goto_eval
  | eval_assume h_eval _ =>
    show ReflTrans _ _ (GotoConfig.running (pc + 1) _ (failed || false))
    rw [Bool.or_false]
    cases h_layout with
    | assume_emit _ _ _ _ h_at h_ty _ h_guard h_translated =>
      have h_goto_eval := (h_translated.bool_tt_agree _).mp h_eval
      rw [← h_guard] at h_goto_eval
      refine ReflTrans.step _ _ _ ?_ (ReflTrans.refl _)
      exact StepGoto.step_assume_pass h_at h_ty h_goto_eval
  | eval_cover _ =>
    -- The `h_admitted : isAdmittedCmd (.cmd (.cover ...)) = true` hypothesis
    -- is false (cover is excluded). Discharge by reduction via simp.
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-! ## Auxiliary: command-list simulation -/

/-- Size-induction helper for `block_body_simulation`'s `cmd` case.

Says: given a CFG block `(l, blk) ∈ cfg.blocks` and a `k`-suffix
`cs := blk.cmds.drop k` of its commands, an `EvalDetBlock` derivation
on the synthetic block `⟨cs, t⟩` for `t := blk.transfer` (i.e., what's
left after the first `k` commands) translates to a `StepGotoStar`
starting at the appropriate offset within the block's GOTO instruction
range. The transfer is exposed as a separate parameter `t` so that the
three transfer cases can pattern-match on it directly.

`block_body_simulation` instantiates this with `k := 0`, `cs := blk.cmds`,
`t := blk.transfer`. -/
theorem block_body_cmds_simulation
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_wf_bool_goto : WellFormedSemanticEvalGotoBool δ_goto_bool)
    (π : String → Option Core.Procedure)
    (φ : Core.CoreEval → Imperative.PureFunc Core.Expression → Core.CoreEval)
    (cfg : Core.DetCFG) (pgm : Program)
    (wf : WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool)
    (l : String) (blk : Imperative.DetBlock String Core.Command Core.Expression)
    (h_block : (l, blk) ∈ cfg.blocks)
    (h_call_free : ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (pc : Nat) (h_pc : wf.labelMap l = some pc)
    (t : Imperative.DetTransferCmd String Core.Expression)
    (h_t : t = blk.transfer)
    (k : Nat)
    (cs : List Core.Command)
    (h_suffix : blk.cmds.drop k = cs)
    (σ : Imperative.SemanticStore Core.Expression) (failed : Bool)
    (c_after : Imperative.CFGConfig String Core.Expression)
    (h_step :
      Imperative.EvalDetBlock Core.Expression
        (Core.EvalCommand π φ) (Core.EvalPureFunc φ) δ σ
        ⟨cs, t⟩ c_after)
    : ∃ c_after_goto,
        StepGotoStar Core.Expression δ_goto δ_goto_bool pgm
          (.running (pc + 1 + cmdsPrefixInstrCount blk.cmds k) σ failed)
          c_after_goto ∧
        Sim cfg pgm wf
          (Imperative.updateFailure c_after failed) c_after_goto := by
  -- Strong induction on cs.length so the cmd case can recurse on the
  -- shorter tail-suffix (which has length cs.length - 1).
  induction h_size : cs.length using Nat.strongRecOn
    generalizing k cs σ failed c_after
  case _ n ih =>
    cases h_step with
    | cmd h_eval h_rest =>
      -- After cases, the renames produced by Lean appear in this order:
      -- `c` (head cmd), `σ_step` (post-store), `head_failed` (failed flag),
      -- `cs_tail` (rest of cs), `config` (post-config). The original `cs`
      -- has been substituted to `c :: cs_tail` everywhere.
      rename_i c σ_step head_failed cs_tail config
      -- After cases, `h_suffix : blk.cmds.drop k = c :: cs_tail`.
      -- Membership of `c` in `blk.cmds` follows by `mem_of_mem_drop`.
      have h_c_mem : c ∈ blk.cmds := by
        have h_in_drop : c ∈ blk.cmds.drop k := by
          rw [h_suffix]; exact List.mem_cons_self
        exact List.mem_of_mem_drop h_in_drop
      have h_pf : c.isAdmittedCmd = true := h_call_free c h_c_mem
      cases c with
      | call _ _ _ =>
        simp [Core.CmdExt.isAdmittedCmd] at h_pf
      | cmd inner =>
        -- Convert EvalCommand → EvalCmd via the inversion lemma.
        have h_evalCmd :
            Imperative.EvalCmd (P := Core.Expression)
              δ σ inner σ_step head_failed :=
          (evalCommand_cmd_iff_evalCmd π φ δ σ σ_step inner head_failed).mp h_eval
        -- (c :: cs_tail).length = n, so cs_tail.length + 1 = n.
        have h_cs_pos : 0 < n := by
          have : (Core.CmdExt.cmd inner :: cs_tail).length = n := h_size
          simp [List.length_cons] at this
          omega
        have h_k_lt : k < blk.cmds.length := by
          have h_drop_len : (blk.cmds.drop k).length =
              (Core.CmdExt.cmd inner :: cs_tail).length := by
            rw [h_suffix]
          rw [List.length_drop] at h_drop_len
          simp [List.length_cons] at h_drop_len
          omega
        -- The head of cs is .cmd inner; therefore blk.cmds[k] = .cmd inner.
        have h_blk_at_k : blk.cmds[k]'h_k_lt = .cmd inner := by
          have h_head : (blk.cmds.drop k).head? = some (.cmd inner) := by
            rw [h_suffix]; rfl
          rw [List.head?_drop] at h_head
          rw [List.getElem?_eq_getElem h_k_lt] at h_head
          injection h_head
        have h_admitted_inner :
            Core.CmdExt.isAdmittedCmd (.cmd inner) = true := by
          rw [← h_blk_at_k]
          exact h_call_free _ (List.getElem_mem _)
        -- Pull layout for the head command.
        have h_layout :
            CmdEmittedAt δ δ_goto δ_goto_bool pgm
              (pc + 1 + cmdsPrefixInstrCount blk.cmds k) inner :=
          wf.layout_block_body l blk pc h_block h_pc k inner h_k_lt h_blk_at_k
        -- Step the head via single_cmd_simulation.
        have h_head :=
          single_cmd_simulation δ δ_goto δ_goto_bool h_wf_bool_goto
            pgm inner σ σ_step failed head_failed h_admitted_inner
            h_evalCmd (pc + 1 + cmdsPrefixInstrCount blk.cmds k) h_layout
        -- The head's post-pc equals (pc + 1 + cmdsPrefixInstrCount blk.cmds (k+1)).
        have h_prefix_step :
            cmdsPrefixInstrCount blk.cmds (k + 1) =
              cmdsPrefixInstrCount blk.cmds k +
                Imperative.Cmd.gotoInstrCount inner := by
          unfold cmdsPrefixInstrCount
          rw [List.take_add_one]
          have h_get : blk.cmds[k]? = some (.cmd inner) := by
            rw [List.getElem?_eq_getElem h_k_lt, h_blk_at_k]
          rw [h_get]
          -- Goal: (take k blk.cmds ++ [.cmd inner]).foldl (acc, c) (acc + gotoInstrCount c) 0
          --     = (take k blk.cmds).foldl ... 0 + Imperative.Cmd.gotoInstrCount inner
          simp [List.foldl_append]
          -- Now: a final unfold of `.cmd inner.gotoInstrCount = inner.gotoInstrCount`
          -- by definition of `Core.CmdExt.gotoInstrCount`.
          rfl
        -- Apply IH on the tail-suffix at index k+1.
        have h_tail_suffix : blk.cmds.drop (k + 1) = cs_tail := by
          rw [List.drop_add_one_eq_tail_drop, h_suffix]
          rfl
        have h_tail_size : cs_tail.length < n := by
          have h_cs_len : (Core.CmdExt.cmd inner :: cs_tail).length = n := h_size
          simp [List.length_cons] at h_cs_len
          omega
        obtain ⟨c_tail_goto, h_tail_steps, h_tail_sim⟩ :=
          ih cs_tail.length h_tail_size (k + 1) cs_tail h_tail_suffix
            σ_step (failed || head_failed) config h_rest rfl
        -- Concatenate head and tail traces.
        refine ⟨c_tail_goto, ?_, ?_⟩
        · -- StepGotoStar: head's trace at offset k, then tail's trace at
          -- offset k+1. The pcs line up via h_prefix_step.
          unfold StepGotoStar at h_head h_tail_steps ⊢
          have h_pc_link :
              pc + 1 + cmdsPrefixInstrCount blk.cmds k +
                  Imperative.Cmd.gotoInstrCount inner =
                pc + 1 + cmdsPrefixInstrCount blk.cmds (k + 1) := by
            rw [h_prefix_step]; omega
          rw [h_pc_link] at h_head
          exact ReflTrans_Transitive _ _ _ _ h_head h_tail_steps
        · -- Sim threads through. updateFailure flag is monotone:
          -- updateFailure (updateFailure config head_failed) failed
          --   = updateFailure config (failed || head_failed) (up to bool comm/assoc).
          have h_eq :
              Imperative.updateFailure
                  (Imperative.updateFailure config head_failed) failed
                = Imperative.updateFailure config (failed || head_failed) := by
            cases config with
            | cont t σ' f =>
              simp [Imperative.updateFailure]
              -- f || head_failed || failed = f || (failed || head_failed)
              ac_rfl
            | terminal σ' f =>
              simp [Imperative.updateFailure]
              ac_rfl
          rw [h_eq]
          exact h_tail_sim
    | goto_true h_cond _ =>
      sorry
    | goto_false h_cond _ =>
      sorry
    | terminal =>
      sorry

/-! ## Block-body simulation (post-LOCATION) -/

/-- One block's `EvalDetBlock` derivation translates to a
`StepGotoStar` covering the block's GOTO instruction range, *starting
after* the leading `LOCATION` (i.e., at `pc + 1`). The wrapper
`block_simulation` prepends one `step_location`.

Three of four cases are proved (`goto_true`, `goto_false`, `terminal`);
the inductive `cmd` case is sorry, requiring a separate induction
generalization deferred to a follow-up. -/
theorem block_body_simulation
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_wf_bool_goto : WellFormedSemanticEvalGotoBool δ_goto_bool)
    (π : String → Option Core.Procedure)
    (φ : Core.CoreEval → Imperative.PureFunc Core.Expression → Core.CoreEval)
    (cfg : Core.DetCFG) (pgm : Program)
    (wf : WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool)
    (l : String) (blk : Imperative.DetBlock String Core.Command Core.Expression)
    (h_block : (l, blk) ∈ cfg.blocks)
    (h_call_free : ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (σ : Imperative.SemanticStore Core.Expression) (failed : Bool)
    (c_after : Imperative.CFGConfig String Core.Expression)
    (h_step :
      Imperative.EvalDetBlock Core.Expression
        (Core.EvalCommand π φ) (Core.EvalPureFunc φ) δ σ blk c_after)
    (pc : Nat) (h_pc : wf.labelMap l = some pc)
    : ∃ c_after_goto,
        StepGotoStar Core.Expression δ_goto δ_goto_bool pgm
          (.running (pc + 1) σ failed) c_after_goto ∧
        Sim cfg pgm wf
          (Imperative.updateFailure c_after failed) c_after_goto := by
  cases h_step with
  | cmd h_eval h_rest =>
    -- Inductive case: head command is `c`, tail is `cs`. Use
    -- `single_cmd_simulation` for the head, then IH for the tail.
    -- Generalizing the recursion over the block parameter requires care;
    -- deferred as a follow-up.
    sorry
  | goto_true h_cond h_wf_bool_core =>
    -- Empty body, condGoto cond t e md, output is .cont t σ false.
    -- After `cases`, blk is unified with ⟨[], .condGoto cond t e md⟩.
    -- The eval `δ` here is the inductive's index — the outer `δ`, not a
    -- fresh existential. So `h_cond : δ σ cond = some HasBool.tt`
    -- directly without a compatibility bridge.
    rename_i md cond t e
    obtain ⟨pc_neg, pc_uncond, pc_lf, pc_lt, instr_neg, instr_uncond,
            h_pc_neg_eq, h_pc_uncond_eq, h_neg_at, h_neg_ty, h_neg_tgt, h_lf_map,
            h_uncond_at, h_uncond_ty, h_uncond_tgt, h_lt_map⟩ :=
      wf.layout_cond_goto l _ pc cond t e md h_block h_pc rfl
    -- For the empty-cmds case, blk = ⟨[], .condGoto cond t e md⟩, so
    -- DetBlockBodyInstrCount blk = 0.
    have h_body_zero :
        DetBlockBodyInstrCount
          (⟨[], (DetTransferCmd.condGoto cond t e md :
              DetTransferCmd String Core.Expression)⟩ :
            Imperative.DetBlock String Core.Command Core.Expression) = 0 := by
      unfold DetBlockBodyInstrCount; rfl
    have h_pc_neg : pc_neg = pc + 1 := by rw [h_pc_neg_eq, h_body_zero]
    have h_pc_uncond : pc_uncond = pc + 1 + 1 := by
      rw [h_pc_uncond_eq, h_pc_neg]
    -- Pull layout_cond_goto_guards using the witnesses we already have.
    obtain ⟨e_goto, h_neg_guard, h_translated, h_uncond_guard⟩ :=
      wf.layout_cond_goto_guards l _ pc cond t e md instr_neg instr_uncond
        h_block h_pc rfl
        (by rw [h_body_zero]; exact h_pc_neg ▸ h_neg_at)
        (by rw [h_body_zero]; exact h_pc_uncond ▸ h_uncond_at)
    -- Build the bool reasoning: δ σ cond = some HasBool.tt
    -- ⇒ δ_goto_bool σ e_goto = some true (via h_translated.bool_tt_agree)
    -- ⇒ δ_goto_bool σ e_goto.not = some false (via h_wf_bool_goto.1).
    have h_g1 : δ_goto_bool σ e_goto = some true :=
      (h_translated.bool_tt_agree σ).mp h_cond
    have h_wf_bool_neg := h_wf_bool_goto.left
    have h_wf_bool_const := h_wf_bool_goto.right
    have h_g2 : δ_goto_bool σ e_goto.not = some false :=
      (h_wf_bool_neg σ e_goto).left.mp h_g1
    -- Build the 2-step trace.
    -- We have pc_neg = pc + 1 and pc_uncond = pc + 1 + 1.
    rw [h_pc_neg] at h_neg_at
    rw [h_pc_uncond] at h_uncond_at
    refine ⟨GotoConfig.running pc_lt σ failed, ?_, .sim_cont h_lt_map⟩
    unfold StepGotoStar
    refine ReflTrans.step
      (GotoConfig.running (pc + 1) σ failed)
      (GotoConfig.running (pc + 1 + 1) σ failed)
      (GotoConfig.running pc_lt σ failed) ?_ ?_
    · refine StepGoto.step_goto_fallthrough h_neg_at h_neg_ty ?_
      rw [h_neg_guard]; exact h_g2
    · refine ReflTrans.step _ _ _ ?_ (ReflTrans.refl _)
      refine StepGoto.step_goto_taken h_uncond_at h_uncond_ty h_uncond_tgt ?_
      rw [h_uncond_guard]
      exact h_wf_bool_const σ
  | goto_false h_cond h_wf_bool_core =>
    -- Empty body, condGoto cond t e md, output is .cont e σ false.
    -- One-step trace: take the negated GOTO (because cond=ff means ¬cond=tt).
    -- The eval `δ` here is the inductive's index — the outer `δ`.
    rename_i md cond t e
    obtain ⟨pc_neg, pc_uncond, pc_lf, pc_lt, instr_neg, instr_uncond,
            h_pc_neg_eq, h_pc_uncond_eq, h_neg_at, h_neg_ty, h_neg_tgt, h_lf_map,
            h_uncond_at, h_uncond_ty, h_uncond_tgt, h_lt_map⟩ :=
      wf.layout_cond_goto l _ pc cond t e md h_block h_pc rfl
    have h_body_zero :
        DetBlockBodyInstrCount
          (⟨[], (DetTransferCmd.condGoto cond t e md :
              DetTransferCmd String Core.Expression)⟩ :
            Imperative.DetBlock String Core.Command Core.Expression) = 0 := by
      unfold DetBlockBodyInstrCount; rfl
    have h_pc_neg : pc_neg = pc + 1 := by rw [h_pc_neg_eq, h_body_zero]
    have h_pc_uncond : pc_uncond = pc + 1 + 1 := by
      rw [h_pc_uncond_eq, h_pc_neg]
    obtain ⟨e_goto, h_neg_guard, h_translated, _⟩ :=
      wf.layout_cond_goto_guards l _ pc cond t e md instr_neg instr_uncond
        h_block h_pc rfl
        (by rw [h_body_zero]; exact h_pc_neg ▸ h_neg_at)
        (by rw [h_body_zero]; exact h_pc_uncond ▸ h_uncond_at)
    -- δ σ cond = some HasBool.ff ⇒ δ_goto_bool σ e_goto = some false
    -- ⇒ δ_goto_bool σ e_goto.not = some true.
    have h_g1 : δ_goto_bool σ e_goto = some false :=
      (h_translated.bool_ff_agree σ).mp h_cond
    have h_wf_bool_neg := h_wf_bool_goto.left
    have h_g2 : δ_goto_bool σ e_goto.not = some true :=
      (h_wf_bool_neg σ e_goto).right.mp h_g1
    rw [h_pc_neg] at h_neg_at
    refine ⟨GotoConfig.running pc_lf σ failed, ?_, .sim_cont h_lf_map⟩
    unfold StepGotoStar
    refine ReflTrans.step _ _ _ ?_ (ReflTrans.refl _)
    refine StepGoto.step_goto_taken h_neg_at h_neg_ty h_neg_tgt ?_
    rw [h_neg_guard]; exact h_g2
  | terminal =>
    -- Empty body, finish md, output is .terminal σ false.
    rename_i md
    obtain ⟨pc_end, instr_end, h_pc_end_eq, h_end_at, h_end_ty⟩ :=
      wf.layout_finish l _ pc md h_block h_pc rfl
    have h_body_zero :
        DetBlockBodyInstrCount
          (⟨[], (DetTransferCmd.finish md :
              DetTransferCmd String Core.Expression)⟩ :
            Imperative.DetBlock String Core.Command Core.Expression) = 0 := by
      unfold DetBlockBodyInstrCount; rfl
    have h_pc_end : pc_end = pc + 1 := by rw [h_pc_end_eq, h_body_zero]
    refine ⟨GotoConfig.terminal σ failed, ?_, .sim_terminal⟩
    unfold StepGotoStar
    refine ReflTrans.step _ _ _ ?_ (ReflTrans.refl _)
    rw [h_pc_end] at h_end_at
    exact StepGoto.step_end_function h_end_at h_end_ty

/-! ## Block simulation lemma

The crux: a single `EvalDetBlock` derivation corresponds to a sequence of
`StepGoto` steps over the GOTO instruction range for that block.

Proof strategy: induct on the `EvalDetBlock` derivation. Each `cmd`
constructor consumes one command and produces one or two GOTO steps via
`Cmd.toGotoInstructions`. The transfer constructors (`goto_true`,
`goto_false`, `terminal`) handle the trailing instructions. -/

/-! ### Concrete sub-lemma: empty-body `finish` block

This is the simplest possible case: a block with no commands and a `finish`
transfer. It exercises the proof skeleton end-to-end and validates that
the `WellFormedTranslation` predicate is shaped correctly for the
`finish` case.

A real `block_simulation` proof would handle this case as one of several
in an induction; we prove it standalone as a sanity check. -/

/-- An empty-body `finish` block simulates: from `(.running pc σ failed)`
where `pc` points at the block's `LOCATION` instruction, two GOTO steps
(`LOCATION` then `END_FUNCTION`, with `DetBlockBodyInstrCount blk = 0`)
reach the corresponding GOTO terminal config. -/
theorem block_simulation_empty_finish
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (cfg : Core.DetCFG) (pgm : Program)
    (wf : WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool)
    (l : String) (md : MetaData Core.Expression)
    (blk : Imperative.DetBlock String Core.Command Core.Expression)
    (h_blk_cmds : blk.cmds = [])
    (h_blk_xfer : blk.transfer = .finish md)
    (h_block : (l, blk) ∈ cfg.blocks)
    (σ : Imperative.SemanticStore Core.Expression) (failed : Bool)
    (pc : Nat) (h_pc : wf.labelMap l = some pc)
    : StepGotoStar Core.Expression δ_goto δ_goto_bool pgm
        (.running pc σ failed) (.terminal σ failed) := by
  -- Step 1: at `pc`, the LOCATION instruction is present (from `wf`).
  obtain ⟨instr_loc, h_loc_at, h_loc_ty⟩ :=
    wf.layout_location l blk pc h_block h_pc
  -- Step 2: at `pc + 1 + 0`, an END_FUNCTION instruction is present.
  obtain ⟨pc_end, instr_end, h_pc_end_eq, h_end_at, h_end_ty⟩ :=
    wf.layout_finish l blk pc md h_block h_pc h_blk_xfer
  -- The body instruction count is 0 since `blk.cmds = []`.
  have h_body : DetBlockBodyInstrCount blk = 0 := by
    unfold DetBlockBodyInstrCount; rw [h_blk_cmds]; rfl
  -- So `pc_end = pc + 1`.
  have h_pc_end : pc_end = pc + 1 := by
    rw [h_pc_end_eq, h_body]
  -- Build the two-step trace: LOCATION, then END_FUNCTION, via `ReflTrans`.
  unfold StepGotoStar
  rw [h_pc_end] at h_end_at
  exact ReflTrans.step
    (GotoConfig.running pc σ failed)
    (GotoConfig.running (pc + 1) σ failed)
    (GotoConfig.terminal σ failed)
    (StepGoto.step_location h_loc_at h_loc_ty)
    (ReflTrans.step _ _ _
      (StepGoto.step_end_function h_end_at h_end_ty)
      (ReflTrans.refl _))

/-- One block's `EvalDetBlock` derivation translates to a `StepGotoStar`
covering the block's GOTO instruction range.

The full proof requires:

1. Induction on the `EvalDetBlock` derivation,
2. Per-command instruction-emission lemmas (each `Imperative.Cmd` matches
   the count in `Cmd.gotoInstrCount`),
3. Use of `WellFormedTranslation` to locate the next block's `pc` after a
   transfer.

For the call-free fragment, `EvalCmd` for each `Cmd P` constructor maps
1-to-1 onto the GOTO `step_*` constructors with the same names. -/
theorem block_simulation
    (δ : SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_wf_bool : WellFormedSemanticEvalGotoBool δ_goto_bool)
    (π : String → Option Core.Procedure)
    (φ : Core.CoreEval → Imperative.PureFunc Core.Expression → Core.CoreEval)
    (cfg : Core.DetCFG) (pgm : Program)
    (wf : WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool)
    (l : String) (blk : Imperative.DetBlock String Core.Command Core.Expression)
    (h_block : (l, blk) ∈ cfg.blocks)
    (h_call_free : ∀ c ∈ blk.cmds, c.isAdmittedCmd = true)
    (σ : Imperative.SemanticStore Core.Expression) (failed : Bool)
    (c_after : Imperative.CFGConfig String Core.Expression)
    (h_step :
      Imperative.EvalDetBlock Core.Expression
        (Core.EvalCommand π φ) (Core.EvalPureFunc φ) δ σ blk c_after)
    (pc : Nat) (h_pc : wf.labelMap l = some pc)
    : ∃ c_after_goto,
        StepGotoStar Core.Expression δ_goto δ_goto_bool pgm
          (.running pc σ failed) c_after_goto ∧
        Sim cfg pgm wf
          (Imperative.updateFailure c_after failed) c_after_goto := by
  -- Step 1: take the LOCATION step.
  obtain ⟨i_loc, h_loc_at, h_loc_ty⟩ :=
    wf.layout_location l blk pc h_block h_pc
  -- Step 2: delegate to block_body_simulation.
  obtain ⟨c_after_goto, h_body_steps, h_sim⟩ :=
    block_body_simulation δ δ_goto δ_goto_bool h_wf_bool π φ
      cfg pgm wf l blk h_block h_call_free σ failed c_after h_step pc h_pc
  -- Step 3: prepend the LOCATION step to the body trace.
  refine ⟨c_after_goto, ?_, h_sim⟩
  unfold StepGotoStar at h_body_steps ⊢
  exact ReflTrans.step _ _ _
    (StepGoto.step_location h_loc_at h_loc_ty) h_body_steps

/-! ## Main forward-simulation theorem

The end-to-end statement: a successful DetCFG run is matched by a successful
GOTO run reaching the same final configuration.

This wraps `block_simulation` with a `ReflTrans`-length induction, mirroring
the pattern in `Strata.Transform.DetToKleeneCorrect`. -/

/-- Forward simulation: any terminating DetCFG run is matched by a
terminating GOTO run with the same final store and failure flag.

Hypotheses:

* `h_expr` — every Core expression has a GOTO translation that the
  evaluators agree on.
* `h_wf_bool` — the GOTO boolean evaluator is well-formed under negation.
* `wf` — a `WellFormedTranslation` witness for `pgm` against `cfg`.
* `h_run` — a multi-step DetCFG run from the entry to a terminal config.
* (Implicit: the CFG's blocks are call-free; the proof obligation above
  takes this as a per-block hypothesis.)

Conclusion: there is a `StepGotoStar` from the GOTO program's entry
configuration to a `terminal` configuration with the same `(σ', b)`. -/
theorem coreCFGToGoto_forward_simulation
    (δ : SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_wf_bool : WellFormedSemanticEvalGotoBool δ_goto_bool)
    (π : String → Option Core.Procedure)
    (φ : Core.CoreEval → Imperative.PureFunc Core.Expression → Core.CoreEval)
    (cfg : Core.DetCFG) (pgm : Program)
    (wf : WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool)
    (h_call_free :
      ∀ p ∈ cfg.blocks, ∀ c ∈ p.2.cmds, c.isAdmittedCmd = true)
    (σ σ' : Imperative.SemanticStore Core.Expression) (b : Bool)
    (h_run :
      Core.CoreCFGStepStar π φ δ cfg
        (.cont cfg.entry σ false)
        (.terminal σ' b))
    : ∃ pc_entry,
        wf.labelMap cfg.entry = some pc_entry ∧
        StepGotoStar Core.Expression δ_goto δ_goto_bool pgm
          (.running pc_entry σ false)
          (.terminal σ' b) := by
  -- Proof outline (deferred):
  -- 1. From `wf.entry_in_map`, obtain `pc_entry` such that
  --    `wf.labelMap cfg.entry = some pc_entry`.
  -- 2. Induct on `h_run : CoreCFGStepStar …` (which has its own `refl` /
  --    `step` constructors, mutually defined with `EvalCommand`).
  --    For each `step` case, apply `block_simulation` to get a
  --    corresponding `StepGotoStar` segment, then concatenate with the
  --    induction hypothesis via `ReflTrans_Transitive`.
  -- 3. The `refl` case is impossible here because the start config
  --    `(.cont cfg.entry σ false)` is not equal to a terminal config —
  --    it's discharged by `cases` / `injection`.
  -- 4. The `terminal` case lifts via `Sim.sim_terminal`.
  --
  -- Mirrors the structure of `detToKleene_overapproximates` in
  -- `Strata/Transform/DetToKleeneCorrect.lean`.
  sorry

end CProverGOTO
