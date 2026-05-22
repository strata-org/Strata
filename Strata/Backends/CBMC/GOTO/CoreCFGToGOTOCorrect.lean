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
public import Strata.Languages.Core.StatementSemanticsProps

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
                _ _ _ h_assn_code h_translated =>
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
    | init_nondet _ _ _ _ h_decl_at h_decl_ty _ _ =>
      refine ReflTrans.step _ _ _ ?_ (ReflTrans.refl _)
      exact StepGoto.step_decl h_decl_at h_decl_ty h_init
  | eval_set h_eval h_upd _ =>
    -- `.set v (.det e) md` — single ASSIGN.
    show ReflTrans _ _ (GotoConfig.running (pc + 1) _ (failed || false))
    rw [Bool.or_false]
    cases h_layout with
    | set_det _ _ _ _ h_assn_at h_assn_ty _ _ h_assn_code h_translated =>
      have h_goto_eval := (h_translated.value_agree _ _).mp h_eval
      refine ReflTrans.step _ _ _ ?_ (ReflTrans.refl _)
      exact StepGoto.step_assign h_assn_at h_assn_ty h_goto_eval h_upd
  | eval_set_nondet h_upd _ =>
    -- `.set v .nondet md` — single ASSIGN with nondet RHS. Uses the
    -- new `step_assign_nondet` constructor.
    show ReflTrans _ _ (GotoConfig.running (pc + 1) _ (failed || false))
    rw [Bool.or_false]
    cases h_layout with
    | set_nondet _ _ _ h_assn_at h_assn_ty _ _ =>
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

/-- When `k` meets or exceeds `blk.cmds.length`, the prefix instruction
count saturates at the full block body count. Used by the transfer
cases of `block_body_cmds_simulation` where `cs = []` (the suffix is
empty), implying `blk.cmds.length ≤ k`. -/
private theorem cmdsPrefixInstrCount_at_blk_length
    (blk : Imperative.DetBlock String Core.Command Core.Expression)
    (k : Nat) (h : blk.cmds.length ≤ k) :
    cmdsPrefixInstrCount blk.cmds k = DetBlockBodyInstrCount blk := by
  unfold cmdsPrefixInstrCount DetBlockBodyInstrCount
  rw [List.take_of_length_le h]

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
        simp only [Core.CmdExt.isAdmittedCmd, reduceCtorEq] at h_pf
      | cmd inner =>
        -- Convert EvalCommand → EvalCmd via the inversion lemma.
        have h_evalCmd :
            Imperative.EvalCmd (P := Core.Expression)
              δ σ inner σ_step head_failed :=
          (evalCommand_cmd_iff_evalCmd π φ δ σ σ_step inner head_failed).mp h_eval
        -- (c :: cs_tail).length = n, so cs_tail.length + 1 = n.
        have h_cs_pos : 0 < n := by
          have : (Core.CmdExt.cmd inner :: cs_tail).length = n := h_size
          simp only [List.length_cons] at this
          omega
        have h_k_lt : k < blk.cmds.length := by
          have h_drop_len : (blk.cmds.drop k).length =
              (Core.CmdExt.cmd inner :: cs_tail).length := by
            rw [h_suffix]
          rw [List.length_drop] at h_drop_len
          simp only [List.length_cons] at h_drop_len
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
          simp only [List.foldl_append]
          -- Now: a final unfold of `.cmd inner.gotoInstrCount = inner.gotoInstrCount`
          -- by definition of `Core.CmdExt.gotoInstrCount`.
          rfl
        -- Apply IH on the tail-suffix at index k+1.
        have h_tail_suffix : blk.cmds.drop (k + 1) = cs_tail := by
          rw [List.drop_add_one_eq_tail_drop, h_suffix]
          rfl
        have h_tail_size : cs_tail.length < n := by
          have h_cs_len : (Core.CmdExt.cmd inner :: cs_tail).length = n := h_size
          simp only [List.length_cons] at h_cs_len
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
              simp only [Imperative.updateFailure]
              -- f || head_failed || failed = f || (failed || head_failed)
              ac_rfl
            | terminal σ' f =>
              simp only [Imperative.updateFailure]
              ac_rfl
          rw [h_eq]
          exact h_tail_sim
    | goto_true h_cond h_wf_bool_core =>
      -- Empty cs case: cs = [] (from the constructor), and t is unified
      -- with `.condGoto cond t' e' md`. Use `h_t` to recover the equality
      -- `blk.transfer = .condGoto cond t' e' md` for the layout helpers.
      rename_i md cond t' e'
      have h_xfer_eq : blk.transfer = DetTransferCmd.condGoto cond t' e' md := by
        rw [← h_t]
      have h_drop_empty : blk.cmds.drop k = [] := h_suffix
      have h_k_ge : blk.cmds.length ≤ k :=
        List.drop_eq_nil_iff.mp h_drop_empty
      have h_prefix_eq :
          cmdsPrefixInstrCount blk.cmds k = DetBlockBodyInstrCount blk :=
        cmdsPrefixInstrCount_at_blk_length blk k h_k_ge
      obtain ⟨pc_neg, pc_uncond, pc_lf, pc_lt, instr_neg, instr_uncond,
              h_pc_neg_eq, h_pc_uncond_eq, h_neg_at, h_neg_ty, _h_neg_tgt, _h_lf_map,
              h_uncond_at, h_uncond_ty, h_uncond_tgt, h_lt_map⟩ :=
        wf.layout_cond_goto l _ pc cond t' e' md h_block h_pc h_xfer_eq
      have h_pc_neg : pc_neg = pc + 1 + DetBlockBodyInstrCount blk := h_pc_neg_eq
      have h_pc_uncond : pc_uncond = pc + 1 + DetBlockBodyInstrCount blk + 1 := by
        rw [h_pc_uncond_eq, h_pc_neg]
      obtain ⟨e_goto, h_neg_guard, h_translated, h_uncond_guard⟩ :=
        wf.layout_cond_goto_guards l _ pc cond t' e' md instr_neg instr_uncond
          h_block h_pc h_xfer_eq
          (by rw [← h_pc_neg]; exact h_neg_at)
          (by rw [← h_pc_uncond]; exact h_uncond_at)
      have h_g1 : δ_goto_bool σ e_goto = some true :=
        (h_translated.bool_tt_agree σ).mp h_cond
      have h_wf_bool_neg := h_wf_bool_goto.left
      have h_wf_bool_const := h_wf_bool_goto.right
      have h_g2 : δ_goto_bool σ e_goto.not = some false :=
        (h_wf_bool_neg σ e_goto).left.mp h_g1
      -- 2-step trace: fallthrough on negated guard, then unconditional taken.
      refine ⟨GotoConfig.running pc_lt σ failed, ?_, .sim_cont h_lt_map⟩
      unfold StepGotoStar
      rw [h_prefix_eq, ← h_pc_neg]
      refine ReflTrans.step
        (GotoConfig.running pc_neg σ failed)
        (GotoConfig.running (pc_neg + 1) σ failed)
        (GotoConfig.running pc_lt σ failed) ?_ ?_
      · refine StepGoto.step_goto_fallthrough h_neg_at h_neg_ty ?_
        · rw [h_neg_guard]; exact h_g2
      · refine ReflTrans.step _ _ _ ?_ (ReflTrans.refl _)
        rw [show pc_neg + 1 = pc_uncond from h_pc_uncond_eq.symm]
        refine StepGoto.step_goto_taken h_uncond_at h_uncond_ty h_uncond_tgt ?_
        · rw [h_uncond_guard]; exact h_wf_bool_const σ
    | goto_false h_cond h_wf_bool_core =>
      -- Empty cs case: cs = [] (from constructor), one-step trace via the
      -- negated GOTO (because cond=ff means ¬cond=tt).
      rename_i md cond t' e'
      have h_xfer_eq : blk.transfer = DetTransferCmd.condGoto cond t' e' md := by
        rw [← h_t]
      have h_drop_empty : blk.cmds.drop k = [] := h_suffix
      have h_k_ge : blk.cmds.length ≤ k :=
        List.drop_eq_nil_iff.mp h_drop_empty
      have h_prefix_eq :
          cmdsPrefixInstrCount blk.cmds k = DetBlockBodyInstrCount blk :=
        cmdsPrefixInstrCount_at_blk_length blk k h_k_ge
      obtain ⟨pc_neg, pc_uncond, pc_lf, _pc_lt, instr_neg, instr_uncond,
              h_pc_neg_eq, h_pc_uncond_eq, h_neg_at, h_neg_ty, h_neg_tgt, h_lf_map,
              h_uncond_at, _h_uncond_ty, _h_uncond_tgt, _h_lt_map⟩ :=
        wf.layout_cond_goto l _ pc cond t' e' md h_block h_pc h_xfer_eq
      have h_pc_neg : pc_neg = pc + 1 + DetBlockBodyInstrCount blk := h_pc_neg_eq
      have h_pc_uncond : pc_uncond = pc + 1 + DetBlockBodyInstrCount blk + 1 := by
        rw [h_pc_uncond_eq, h_pc_neg]
      obtain ⟨e_goto, h_neg_guard, h_translated, _⟩ :=
        wf.layout_cond_goto_guards l _ pc cond t' e' md instr_neg instr_uncond
          h_block h_pc h_xfer_eq
          (by rw [← h_pc_neg]; exact h_neg_at)
          (by rw [← h_pc_uncond]; exact h_uncond_at)
      have h_g1 : δ_goto_bool σ e_goto = some false :=
        (h_translated.bool_ff_agree σ).mp h_cond
      have h_wf_bool_neg := h_wf_bool_goto.left
      have h_g2 : δ_goto_bool σ e_goto.not = some true :=
        (h_wf_bool_neg σ e_goto).right.mp h_g1
      refine ⟨GotoConfig.running pc_lf σ failed, ?_, .sim_cont h_lf_map⟩
      unfold StepGotoStar
      rw [h_prefix_eq, ← h_pc_neg]
      refine ReflTrans.step _ _ _ ?_ (ReflTrans.refl _)
      refine StepGoto.step_goto_taken h_neg_at h_neg_ty h_neg_tgt ?_
      · rw [h_neg_guard]; exact h_g2
    | terminal =>
      -- Empty cs case: cs = [] (from constructor), t = .finish md, output
      -- is `.terminal σ false`. One-step trace via END_FUNCTION.
      rename_i md
      have h_xfer_eq : blk.transfer = DetTransferCmd.finish md := by
        rw [← h_t]
      have h_drop_empty : blk.cmds.drop k = [] := h_suffix
      have h_k_ge : blk.cmds.length ≤ k :=
        List.drop_eq_nil_iff.mp h_drop_empty
      have h_prefix_eq :
          cmdsPrefixInstrCount blk.cmds k = DetBlockBodyInstrCount blk :=
        cmdsPrefixInstrCount_at_blk_length blk k h_k_ge
      obtain ⟨pc_end, _instr_end, h_pc_end_eq, h_end_at, h_end_ty⟩ :=
        wf.layout_finish l _ pc md h_block h_pc h_xfer_eq
      have h_pc_end : pc_end = pc + 1 + DetBlockBodyInstrCount blk := h_pc_end_eq
      refine ⟨GotoConfig.terminal σ failed, ?_, .sim_terminal⟩
      unfold StepGotoStar
      rw [h_prefix_eq, ← h_pc_end]
      refine ReflTrans.step _ _ _ ?_ (ReflTrans.refl _)
      exact StepGoto.step_end_function h_end_at h_end_ty

/-! ## Block-body simulation (post-LOCATION) -/

/-- One block's `EvalDetBlock` derivation translates to a
`StepGotoStar` covering the block's GOTO instruction range, *starting
after* the leading `LOCATION` (i.e., at `pc + 1`). The wrapper
`block_simulation` prepends one `step_location`.

Decomposes via `block_body_cmds_simulation` at `k = 0`, which inducts
on the suffix of the block's command list. -/
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
  -- Reduce to `block_body_cmds_simulation` at `k = 0`.
  -- At `k = 0`, `cmdsPrefixInstrCount blk.cmds 0 = 0`, so the auxiliary's
  -- starting pc `pc + 1 + cmdsPrefixInstrCount blk.cmds 0` reduces to `pc + 1`.
  have h_offset : pc + 1 + cmdsPrefixInstrCount blk.cmds 0 = pc + 1 := by
    unfold cmdsPrefixInstrCount
    simp
  have h_suffix : blk.cmds.drop 0 = blk.cmds := List.drop_zero
  -- The block decomposes as ⟨blk.cmds, blk.transfer⟩ definitionally.
  -- `h_step`'s block argument needs to become ⟨blk.cmds, blk.transfer⟩
  -- (the explicit transfer parameter required by block_body_cmds_simulation).
  have h_step' :
      Imperative.EvalDetBlock Core.Expression
        (Core.EvalCommand π φ) (Core.EvalPureFunc φ) δ σ
        ⟨blk.cmds, blk.transfer⟩ c_after := h_step
  obtain ⟨c_after_goto, h_steps, h_sim⟩ :=
    block_body_cmds_simulation δ δ_goto δ_goto_bool h_wf_bool_goto
      π φ cfg pgm wf l blk h_block h_call_free pc h_pc
      blk.transfer rfl 0 blk.cmds h_suffix σ failed c_after h_step'
  rw [h_offset] at h_steps
  exact ⟨c_after_goto, h_steps, h_sim⟩

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

The main theorem `coreCFGToGoto_forward_simulation` is a thin wrapper that
delegates to the auxiliary `cfgStepStar_to_gotoStar`, which performs the
induction over `CoreCFGStepStar`, case-splitting `Sim` to either invoke
the induction hypothesis on the post-block continuation label or collapse
the tail to `refl` when the block transitioned to a terminal config. -/

/-- Auxiliary induction over `CoreCFGStepStar`: from any `(.cont l σ failed)`
configuration that reaches `(.terminal σ' b)` in the source CFG, we can
build a matching GOTO trace from `(.running pc σ failed)` to
`(.terminal σ' b)`, where `pc` is the GOTO entry for label `l`.

The main theorem is a wrapper that instantiates `l := cfg.entry` and
`failed := false`; `σ` is whatever store the caller supplies. -/
private theorem cfgStepStar_to_gotoStar
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
    (l : String) (σ : Imperative.SemanticStore Core.Expression)
    (failed : Bool)
    (σ' : Imperative.SemanticStore Core.Expression) (b : Bool)
    (pc : Nat) (h_pc : wf.labelMap l = some pc)
    (h_run :
      Core.CoreCFGStepStar π φ δ cfg
        (.cont l σ failed)
        (.terminal σ' b))
    : StepGotoStar Core.Expression δ_goto δ_goto_bool pgm
        (.running pc σ failed) (.terminal σ' b) := by
  -- Use `Core.CoreCFGStepStar_rec` since `CoreCFGStepStar` is mutually
  -- inductive and the `induction` tactic doesn't apply. Encode the
  -- conclusion as a motive over `(c₁, c₂)` so that the IH gives us a
  -- tail trace from the post-block continuation label.
  -- The motive's universals are named `l₀ σ₀ failed₀ pc₀ σ₀' b₀` to avoid
  -- shadowing the outer signature's `l σ failed pc σ' b`. The recursor
  -- abstracts over `(c₁, c₂)`, so we re-introduce the outer-style indices
  -- as universally quantified hypotheses inside the motive, and unify them
  -- with the outer ones at the closing `exact key …`.
  let motive : Imperative.CFGConfig String Core.Expression →
               Imperative.CFGConfig String Core.Expression → Prop :=
    fun c₁ c₂ =>
      ∀ (l₀ : String) (σ₀ : Imperative.SemanticStore Core.Expression)
        (failed₀ : Bool) (pc₀ : Nat),
        c₁ = .cont l₀ σ₀ failed₀ →
        wf.labelMap l₀ = some pc₀ →
        ∀ (σ₀' : Imperative.SemanticStore Core.Expression) (b₀ : Bool),
          c₂ = .terminal σ₀' b₀ →
          StepGotoStar Core.Expression δ_goto δ_goto_bool pgm
            (.running pc₀ σ₀ failed₀) (.terminal σ₀' b₀)
  have key : motive (.cont l σ failed) (.terminal σ' b) := by
    apply Core.CoreCFGStepStar_rec (motive := motive) ?_ ?_ h_run
    · -- refl case: motive c c. The two equalities force
      -- (.cont l σ failed) = (.terminal σ' b), which is impossible.
      intro c l' σ_l f_l pc_l h_eq_l _h_pc σ_r b_r h_eq_r
      rw [h_eq_l] at h_eq_r
      cases h_eq_r
    · -- step case
      intro t blk_step σ_step failed_step config c₃
        h_lookup h_blk h_rest ih
        l' σ_l f_l pc_l h_eq_l h_pc_l σ_r b_r h_eq_r
      -- Constructor injection on
      --   h_eq_l : (.cont t σ_step failed_step) = (.cont l' σ_l f_l)
      -- Cases substitutes l', σ_l, f_l by t, σ_step, failed_step.
      cases h_eq_l
      -- Derive (t, blk_step) ∈ cfg.blocks from h_lookup.
      have h_mem : (t, blk_step) ∈ cfg.blocks := by
        obtain ⟨l₁, l₂, h_split, _⟩ :=
          List.lookup_eq_some_iff.mp h_lookup
        rw [h_split]
        exact List.mem_append_right _ List.mem_cons_self
      -- Apply block_simulation.
      obtain ⟨c_after_goto, h_blk_steps, h_sim⟩ :=
        block_simulation δ δ_goto δ_goto_bool h_expr h_wf_bool
          π φ cfg pgm wf t blk_step h_mem
          (h_call_free (t, blk_step) h_mem)
          σ_step failed_step _ h_blk pc_l h_pc_l
      -- Case-split on `config`: this forces `updateFailure config failed_step`
      -- to reduce so that `cases h_sim` can match `Sim`'s constructor patterns.
      cases config with
      | cont l_blk σ_blk f_blk =>
        -- updateFailure (.cont l_blk σ_blk f_blk) failed_step
        -- = .cont l_blk σ_blk (f_blk || failed_step)
        cases h_sim with
        | sim_cont h_lnext =>
          -- Apply IH: motive (updateFailure config failed_step) c₃
          -- specialized at (l_blk, σ_blk, f_blk || failed_step, _, σ_r, b_r, h_eq_r).
          have h_tail :=
            ih l_blk σ_blk (f_blk || failed_step) _ rfl h_lnext σ_r b_r h_eq_r
          -- Concatenate block trace with tail.
          unfold StepGotoStar at h_blk_steps h_tail ⊢
          exact ReflTrans_Transitive _ _ _ _ h_blk_steps h_tail
      | terminal σ_blk f_blk =>
        -- updateFailure (.terminal σ_blk f_blk) failed_step
        -- = .terminal σ_blk (f_blk || failed_step). After cases h_sim,
        -- h_blk_steps lands at the GOTO terminal config matching this.
        cases h_sim with
        | sim_terminal =>
          -- CoreCFGStepStar.step requires a `.cont` source; from a
          -- `.terminal` source the only inhabitant is `.refl`, which
          -- unifies c₃ with `.terminal σ_blk (f_blk || failed_step)`.
          cases h_rest with
          | refl =>
            -- h_eq_r : .terminal σ_blk (f_blk || failed_step) = .terminal σ_r b_r
            cases h_eq_r
            -- σ_r and b_r are now σ_blk and (f_blk || failed_step).
            -- h_blk_steps already lands at the goal.
            exact h_blk_steps
  exact key l σ failed pc rfl h_pc σ' b rfl

/-- Forward simulation: any terminating DetCFG run is matched by a
terminating GOTO run with the same final store and failure flag.

Hypotheses:

* `h_expr` — every Core expression has a GOTO translation that the
  evaluators agree on. (Currently unused by the proof chain — threaded
  through `WellFormedTranslation.layout_*` instead — but retained as a
  documented axiomatized input.)
* `h_wf_bool` — the GOTO boolean evaluator is well-formed under negation.
* `wf` — a `WellFormedTranslation` witness for `pgm` against `cfg`.
* `h_call_free` — every block of the CFG admits the proof's restricted
  command fragment (no `.call`, no `.cover`, no nondet `.init`).
* `h_run` — a multi-step DetCFG run from the entry to a terminal config.

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
  obtain ⟨pc_entry, h_pc_entry⟩ := wf.entry_in_map
  refine ⟨pc_entry, h_pc_entry, ?_⟩
  exact cfgStepStar_to_gotoStar δ δ_goto δ_goto_bool h_expr h_wf_bool
    π φ cfg pgm wf h_call_free
    cfg.entry σ false σ' b pc_entry h_pc_entry h_run

end CProverGOTO
