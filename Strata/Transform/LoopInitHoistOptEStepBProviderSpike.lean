/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT

  Step B provider — the per-iteration body-simulation vocabulary the loop-init
  hoisting correctness proof is built on.  This file is load-bearing: it is
  imported by `LoopInitHoistBodyTransport` (and transitively by the end-to-end
  theorem `hoistLoopPrefixInits_preserves`).

  It defines the eval-carrying simulation predicates `BodySim` / `BodySimE` /
  `StmtSimE` and their combinators (`bodySimE_nil`, `bodySimE_cons`,
  `bodySimE_to_bodySim`, `nestedLoop_stmtSimE`).  `Block.bodyTransport` consumes
  this vocabulary in every statement arm; the nested-loop arm feeds an inner body
  simulation — produced from the same mutual induction — into the renamed-guard
  loop driver, so a renamed+lifted loop body (whose guard is rewritten and whose
  nested loops are renamed) simulates its source faithfully.
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CmdSemantics
public import Strata.Transform.LoopInitHoist
public import Strata.Transform.LoopInitHoistContains
public import Strata.Transform.LoopInitHoistFreshness
public import Strata.Transform.LoopInitHoistRewrite
public import Strata.Transform.LoopInitHoistInfra
public import Strata.Transform.LoopInitHoistLoopDriver

import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.Cmd
import all Strata.Transform.LoopInitHoist
import all Strata.Transform.LoopInitHoistContains
import all Strata.Transform.LoopInitHoistFreshness
import all Strata.Transform.LoopInitHoistRewrite
import all Strata.Transform.LoopInitHoistInfra
import all Strata.Transform.LoopInitHoistLoopDriver

public section

namespace Imperative
namespace OptEStepBProvider

open StructuredToUnstructuredCorrect (extendStoreOne extendStoreOne_self extendStoreOne_other)
open LoopInitHoistLoopDriver (loopDet_lift_2g loopDet_lift_renamedGuard loopDet_lift_renamedGuard_E
  loopDet_lift_renamedGuard_TE renamed_guard_eval_same_delta)

variable {P : PureExpr}

/-- The `body_sim`-shaped per-iteration body simulation (exactly the slot the
    2-guard driver consumes), for a fixed `body_src`/`body_h`/`A B subst`.

    `BodySim` is the 2-guard driver's literal slot type; `BodySimE` is the same
    enriched with EVAL PRESERVATION in the output (`ρ_s'.eval = ρ_h'.eval`).  The
    enrichment is what makes the cons-sequencer go through (the tail sim needs
    eval-equality at the mid env), and it is faithfully available: every §E arm's
    output preserves `eval` (the small-step semantics over `noFuncDecl` bodies
    leave `eval` fixed, cf. `smallStep_noFuncDecl_preserves_eval_block`).  We
    DERIVE `BodySim` from `BodySimE` by forgetting the eval conjunct, so the final
    term still drops straight into the driver's `body_sim` slot. -/
def BodySim [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    (A B : List P.Ident) (subst : List (P.Ident × P.Ident))
    (bsrc bh : List (Stmt P (Cmd P))) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    HoistInv (P := P) A B subst ρ_s.store ρ_h.store →
    ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
    (∀ y ∈ B, ρ_h.store y ≠ none) →
    ∀ (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendEval (.stmts bsrc ρ_s) (.terminal ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendEval (.stmts bh ρ_h) (.terminal ρ_h') ∧
        HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
        ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none)

/-- Eval-carrying body sim (output also records `ρ_s'.eval = ρ_h'.eval`). -/
@[expose] def BodySimE [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    (A B : List P.Ident) (subst : List (P.Ident × P.Ident))
    (bsrc bh : List (Stmt P (Cmd P))) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    HoistInv (P := P) A B subst ρ_s.store ρ_h.store →
    ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
    (∀ y ∈ B, ρ_h.store y ≠ none) →
    ∀ (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendEval (.stmts bsrc ρ_s) (.terminal ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendEval (.stmts bh ρ_h) (.terminal ρ_h') ∧
        HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
        ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none) ∧
        ρ_s'.eval = ρ_h'.eval

/-- Forget the eval conjunct: `BodySimE → BodySim` (drops into the driver slot). -/
theorem bodySimE_to_bodySim [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {bsrc bh : List (Stmt P (Cmd P))}
    (h : BodySimE (extendEval := extendEval) A B subst bsrc bh) :
    BodySim (extendEval := extendEval) A B subst bsrc bh := by
  intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
  obtain ⟨ρ_h', h_run_h, h_hinv', h_hf', h_bnd', _⟩ :=
    h ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
  exact ⟨ρ_h', h_run_h, h_hinv', h_hf', h_bnd'⟩

/-! ## STEP 0 — the concrete `body₃` for my body under `applyRenames [(x,x')]`.

Confirm by reduction that the outer rename DESCENDS into the nested loop:
  body  = [ .cmd (.init x τ (.det rhs) md), .loop g2 none [] [.cmd (.assert lbl e md)] md2 ]
  body₃ = applyRenames [(x,x')] body
        = [ .cmd (.init (if x=x then x' else x) τ (.det (substFvar rhs x x')) md),
            .loop (g2.substIdent x x') none []
                  [.cmd (.assert lbl (substFvar e x x') md)] md2 ] -/
theorem body₃_concrete [HasFvar P] [HasSubstFvar P] [DecidableEq P.Ident]
    (x x' : P.Ident) (τ : P.Ty) (rhs e : P.Expr) (g2 : ExprOrNondet P)
    (lbl : String) (md md2 : MetaData P) :
    Block.applyRenames [(x, x')]
        [ Stmt.cmd (.init x τ (.det rhs) md),
          Stmt.loop g2 none [] [Stmt.cmd (.assert lbl e md)] md2 ]
      = [ Stmt.cmd (.init x' τ (.det (HasSubstFvar.substFvar rhs x (HasFvar.mkFvar x'))) md),
          Stmt.loop (g2.substIdent x x') none []
            [Stmt.cmd (.assert lbl (HasSubstFvar.substFvar e x (HasFvar.mkFvar x')) md)] md2 ] := by
  simp only [Block.applyRenames, List.foldl_cons, List.foldl_nil,
    Block.substIdent_cons, Block.substIdent_nil, Stmt.substIdent_cmd, Stmt.substIdent_loop,
    Cmd.substIdent_init, Cmd.substIdent_assert, ExprOrNondet.substIdent_det,
    Option.map_none, List.map_nil, if_true]

/-! ## STEP 1 — the per-statement sim and the cons-sequencer.

A `StmtSimE A B subst s s'` is the single-statement (eval-carrying) analogue of
`BodySimE` (run the ONE statement `s` against `s'` from any `HoistInv`-related
entry, terminal to terminal, preserving eval).  This is EXACTLY what each §E arm
produces for ONE statement of the loop body — the `.cmd` arm produces a `StmtSimE`
for the init, the `.loop` arm produces a `StmtSimE` for the nested loop (via the
loop driver).  The cons sequencer stitches a head `StmtSimE` with a tail
`BodySimE` into a `BodySimE` for the whole body, replaying the proven
`stmts_cons_step` / `stmts_cons_terminal_inv` sequencing. -/
@[expose] def StmtSimE [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    (A B : List P.Ident) (subst : List (P.Ident × P.Ident))
    (s s' : Stmt P (Cmd P)) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    HoistInv (P := P) A B subst ρ_s.store ρ_h.store →
    ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
    (∀ y ∈ B, ρ_h.store y ≠ none) →
    ∀ (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ_s) (.terminal ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendEval (.stmt s' ρ_h) (.terminal ρ_h') ∧
        HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
        ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none) ∧
        ρ_s'.eval = ρ_h'.eval

/-- The empty body is a `BodySimE` (terminal stays terminal, store/eval unchanged). -/
theorem bodySimE_nil [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    (A B : List P.Ident) (subst : List (P.Ident × P.Ident)) :
    BodySimE (extendEval := extendEval) A B subst [] [] := by
  intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
  have h_eq : ρ_s' = ρ_s := by
    cases h_run with
    | step _ _ _ h1 hr1 =>
      cases h1
      cases hr1 with
      | refl => rfl
      | step _ _ _ hd _ => exact nomatch hd
  subst h_eq
  refine ⟨ρ_h, ?_, h_hinv, h_hf, h_bnd, h_eval⟩
  exact ReflTrans.step _ _ _ StepStmt.step_stmts_nil (ReflTrans.refl _)

/-- THE CONS-SEQUENCER: a head `StmtSimE` and a tail `BodySimE` compose into a
`BodySimE` for the cons body.  This is the structural glue the §E cons recursion
performs; here it is proved ONCE, generically, at arbitrary carriers `A B subst`.
The proof: invert the source cons-run into head + tail (`stmts_cons_terminal_inv`),
fire the head `StmtSimE` to get the hoist head-run, MID `HoistInv`, and MID eval-eq,
fire the tail `BodySimE` from the mid env, and reassemble the hoist cons-run via
`stmts_cons_step`. -/
theorem bodySimE_cons [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {s s' : Stmt P (Cmd P)} {rest rest' : List (Stmt P (Cmd P))}
    (hhead : StmtSimE (extendEval := extendEval) A B subst s s')
    (htail : BodySimE (extendEval := extendEval) A B subst rest rest') :
    BodySimE (extendEval := extendEval) A B subst (s :: rest) (s' :: rest') := by
  intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
  -- split source cons-run into head + tail.
  obtain ⟨ρ_mid, h_head_run, h_rest_run⟩ :=
    stmts_cons_terminal_inv (extendEval := extendEval) h_run
  -- fire the head StmtSimE: yields hoist head-run, mid HoistInv, mid hf/bnd, mid eval.
  obtain ⟨ρ_h_mid, h_head_h_run, h_hinv_mid, h_hf_mid, h_bnd_mid, h_eval_mid⟩ :=
    hhead ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_mid h_head_run
  -- fire the tail BodySimE from the mid envs.
  obtain ⟨ρ_h', h_rest_h_run, h_hinv', h_hf', h_bnd', h_eval'⟩ :=
    htail ρ_mid ρ_h_mid h_hinv_mid h_eval_mid h_hf_mid h_bnd_mid ρ_s' h_rest_run
  refine ⟨ρ_h', ?_, h_hinv', h_hf', h_bnd', h_eval'⟩
  -- reassemble the hoist cons-run: head step (s' to ρ_h_mid) then tail run.
  exact ReflTrans_Transitive _ _ _ _
    (stmts_cons_step P (EvalCmd P) extendEval s' rest' ρ_h ρ_h_mid h_head_h_run)
    h_rest_h_run

/-! ## STEP 2 — the NESTED-LOOP `StmtSimE` from a `BodySimE` for the inner body.

THE CRITICAL NEW QUESTION.  The inner loop `.loop (.det g2) none [] inner md2` has
its guard renamed to `substFvarMany g2 subst` and its body renamed to `inner_h`.
We must produce a `StmtSimE` for this nested loop — the per-statement sim slot the
cons sequencer consumes for the loop position.  Its body_sim is a `BodySimE` for
`inner → inner_h` (the SELF-REFERENTIAL piece: in the real §E mutual this comes
from the SAME mutual recursion on the strictly-smaller inner body).

We obtain the loop simulation from `loopDet_lift_renamedGuard` (guard transport
discharged internally from guard freshness), then RECOVER the eval-preservation
conjunct from the source and hoist runs via `smallStep_noFuncDecl_preserves_eval`
(both loop statements are `noFuncDecl`).  This settles, by compilation, that:
  • the renamed-guard nested loop's sub-simulation comes from
    `loopDet_lift_renamedGuard` recursively, and
  • it produces a `StmtSimE` at the OUTER carriers `A B subst` (= `[x] [x'] [(x,x')]`)
    that drops into the cons sequencer's head slot. -/
theorem nestedLoop_stmtSimE [HasFvar P] [HasBool P] [HasNot P] [HasSubstFvar P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {g2 : P.Expr} {inner inner_h : List (Stmt P (Cmd P))} {md2_s md2_h : MetaData P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    -- subst well-formedness for the renamed guard transport:
    (h_A_subst_fst : ∀ a ∈ A, a ∈ subst.map Prod.fst)
    (h_src_nodup : (subst.map Prod.fst).Nodup)
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd)
    (h_tgt_nodup : (subst.map Prod.snd).Nodup)
    (h_g_B_fresh : ∀ z ∈ B, z ∉ HasVarsPure.getVars g2)
    (h_wfvar   : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval)
    (h_wfcongr : ∀ ρ : Env P, WellFormedSemanticEvalExprCongr ρ.eval)
    (h_wfsubst : ∀ ρ : Env P, WellFormedSemanticEvalSubstFvar ρ.eval)
    (h_wfdef   : ∀ ρ : Env P, WellFormedSemanticEvalDef ρ.eval)
    -- the inner body sim (self-referential piece — the §E IH on the SMALLER body):
    (inner_sim : BodySim (extendEval := extendEval) A B subst inner inner_h)
    (h_src_body_no_exit : ∀ (ρ : Env P) (lbl : String) (ρe : Env P),
       ¬ StepStmtStar P (EvalCmd P) extendEval (.stmts inner ρ) (.exiting lbl ρe))
    (h_nofd_src : Block.noFuncDecl inner = true)
    (h_nofd_h : Block.noFuncDecl inner_h = true) :
    StmtSimE (extendEval := extendEval) A B subst
      (.loop (.det g2) none [] inner md2_s)
      (.loop (.det (substFvarMany g2 subst)) none [] inner_h md2_h) := by
  intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
  -- the source run is a `.stmt (.loop ...)` run; the driver consumes the same.
  obtain ⟨ρ_h', h_loop_h_run, h_hinv', h_hf', h_bnd'⟩ :=
    loopDet_lift_renamedGuard (A := A) (B := B) (subst := subst)
      h_A_subst_fst h_src_nodup h_disjoint h_tgt_nodup h_g_B_fresh
      h_wfvar h_wfcongr h_wfsubst h_wfdef
      inner_sim h_src_body_no_exit h_nofd_src h_nofd_h
      h_hinv h_eval h_hf h_bnd h_run
  refine ⟨ρ_h', h_loop_h_run, h_hinv', h_hf', h_bnd', ?_⟩
  -- recover eval: both loop statements are noFuncDecl, so the runs fix eval.
  have h_src_nofd_loop : Stmt.noFuncDecl (.loop (.det g2) none [] inner md2_s) = true := by
    simp only [Stmt.noFuncDecl]; exact h_nofd_src
  have h_h_nofd_loop :
      Stmt.noFuncDecl (.loop (.det (substFvarMany g2 subst)) none [] inner_h md2_h) = true := by
    simp only [Stmt.noFuncDecl]; exact h_nofd_h
  have e_s : ρ_s'.eval = ρ_s.eval :=
    smallStep_noFuncDecl_preserves_eval P (EvalCmd P) extendEval _ ρ_s ρ_s' h_src_nofd_loop h_run
  have e_h : ρ_h'.eval = ρ_h.eval :=
    smallStep_noFuncDecl_preserves_eval P (EvalCmd P) extendEval _ ρ_h ρ_h' h_h_nofd_loop h_loop_h_run
  rw [e_s, e_h]; exact h_eval

/-! ## STEP 3 — the OUTER body_sim for the concrete `init :: [nested loop]` body.

Assemble the outer `BodySimE [x] [x'] [(x,x')] body body₃` by sequencing:
  • the init `StmtSimE` (`.cmd (.init x ..) → .cmd (.init x' ..)`) — the §E `.cmd`
    arm output for the lifted init (modelled here as a hypothesis of the §E `.cmd`
    shape: `init_sim`), with
  • the nested-loop `StmtSimE` (from `nestedLoop_stmtSimE`, whose own body sim
    `inner_sim` is the §E `.cmd` arm output for the inner assert), and
  • the empty tail (`bodySimE_nil`).
Then forget eval (`bodySimE_to_bodySim`) to land in the driver's `body_sim` slot. -/
theorem outer_bodySim_concrete [HasFvar P] [HasBool P] [HasNot P] [HasSubstFvar P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {x x' : P.Ident} {τ : P.Ty} {rhs e g2 : P.Expr} {lbl : String}
    {md md2_s md2_h : MetaData P}
    -- §E `.cmd` arm output for the lifted top-level init `x ↦ x'`:
    (init_sim : StmtSimE (extendEval := extendEval) [x] [x'] [(x, x')]
        (.cmd (.init x τ (.det rhs) md))
        (.cmd (.init x' τ (.det (HasSubstFvar.substFvar rhs x (HasFvar.mkFvar x'))) md)))
    -- §E `.cmd` arm output for the inner assert `x ↦ x'` (inner loop body sim):
    (inner_sim : BodySim (extendEval := extendEval) [x] [x'] [(x, x')]
        [.cmd (.assert lbl e md)]
        [.cmd (.assert lbl (HasSubstFvar.substFvar e x (HasFvar.mkFvar x')) md)])
    -- nested-loop driver side-facts (at the OUTER carriers [x] [x'] [(x,x')]):
    (h_A_subst_fst : ∀ a ∈ [x], a ∈ ([(x, x')] : List (P.Ident × P.Ident)).map Prod.fst)
    (h_src_nodup : (([(x, x')] : List (P.Ident × P.Ident)).map Prod.fst).Nodup)
    (h_disjoint : ∀ a ∈ ([(x, x')] : List (P.Ident × P.Ident)).map Prod.fst,
        a ∉ ([(x, x')] : List (P.Ident × P.Ident)).map Prod.snd)
    (h_tgt_nodup : (([(x, x')] : List (P.Ident × P.Ident)).map Prod.snd).Nodup)
    (_h_g2_A_fresh : ∀ z ∈ [x], z ∉ HasVarsPure.getVars g2)
    (h_g2_B_fresh : ∀ z ∈ [x'], z ∉ HasVarsPure.getVars g2)
    (h_wfvar   : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval)
    (h_wfcongr : ∀ ρ : Env P, WellFormedSemanticEvalExprCongr ρ.eval)
    (h_wfsubst : ∀ ρ : Env P, WellFormedSemanticEvalSubstFvar ρ.eval)
    (h_wfdef   : ∀ ρ : Env P, WellFormedSemanticEvalDef ρ.eval)
    (h_inner_no_exit : ∀ (ρ : Env P) (lbl' : String) (ρe : Env P),
       ¬ StepStmtStar P (EvalCmd P) extendEval
           (.stmts [.cmd (.assert lbl e md)] ρ) (.exiting lbl' ρe)) :
    BodySim (extendEval := extendEval) [x] [x'] [(x, x')]
      [ Stmt.cmd (.init x τ (.det rhs) md),
        Stmt.loop (.det g2) none [] [Stmt.cmd (.assert lbl e md)] md2_s ]
      [ Stmt.cmd (.init x' τ (.det (HasSubstFvar.substFvar rhs x (HasFvar.mkFvar x'))) md),
        Stmt.loop (.det (substFvarMany g2 [(x, x')])) none []
          [Stmt.cmd (.assert lbl (HasSubstFvar.substFvar e x (HasFvar.mkFvar x')) md)] md2_h ] := by
  -- inner assert body is noFuncDecl on both sides.
  have h_nofd_inner_src :
      Block.noFuncDecl (P := P) [Stmt.cmd (Cmd.assert lbl e md)] = true := by
    simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_true]
  have h_nofd_inner_h : Block.noFuncDecl (P := P)
      [Stmt.cmd (Cmd.assert lbl (HasSubstFvar.substFvar e x (HasFvar.mkFvar x')) md)] = true := by
    simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_true]
  -- nested-loop StmtSimE from the inner body sim (the recursive driver call).
  have loop_sim :
      StmtSimE (extendEval := extendEval) [x] [x'] [(x, x')]
        (.loop (.det g2) none [] [Stmt.cmd (.assert lbl e md)] md2_s)
        (.loop (.det (substFvarMany g2 [(x, x')])) none []
          [Stmt.cmd (.assert lbl (HasSubstFvar.substFvar e x (HasFvar.mkFvar x')) md)] md2_h) :=
    nestedLoop_stmtSimE (A := [x]) (B := [x']) (subst := [(x, x')])
      h_A_subst_fst h_src_nodup h_disjoint h_tgt_nodup h_g2_B_fresh
      h_wfvar h_wfcongr h_wfsubst h_wfdef inner_sim h_inner_no_exit
      h_nofd_inner_src h_nofd_inner_h
  -- sequence: init :: loop :: nil.
  have body_simE :
      BodySimE (extendEval := extendEval) [x] [x'] [(x, x')]
        [ Stmt.cmd (.init x τ (.det rhs) md),
          Stmt.loop (.det g2) none [] [Stmt.cmd (.assert lbl e md)] md2_s ]
        [ Stmt.cmd (.init x' τ (.det (HasSubstFvar.substFvar rhs x (HasFvar.mkFvar x'))) md),
          Stmt.loop (.det (substFvarMany g2 [(x, x')])) none []
            [Stmt.cmd (.assert lbl (HasSubstFvar.substFvar e x (HasFvar.mkFvar x')) md)] md2_h ] :=
    bodySimE_cons init_sim (bodySimE_cons loop_sim (bodySimE_nil _ _ _))
  exact bodySimE_to_bodySim body_simE

/-! ## STEP 4 — END-TO-END: feed the assembled outer body_sim into the OUTER loop
    driver to produce the full OUTER-loop simulation.

The OUTER loop guard `g` is UNCHANGED (only NESTED guards are renamed), so the
outer loop driver is the SAME-guard `loopDet_lift_2g_recovers_single`
(`g_s = g_h = g`) at the lift carriers `[x] [x'] [(x,x')]`.  Its body_sim is the
`outer_bodySim_concrete` output (body → body₃).  If this compiles, the full chain
  inner-assert §E.cmd output  →(driver)→  nested-loop StmtSimE
  init §E.cmd output ⊕ nested-loop StmtSimE  →(cons-seq)→  outer body_sim
  outer body_sim  →(driver)→  OUTER loop simulation
type-checks end to end on a body WITH a nested loop.

The genuinely load-bearing end-to-end: the OUTER loop `.loop (.det g) … body`
runs against `.loop (.det g) … body₃` (guard UNCHANGED — top-level), the body_sim
being the assembled `outer_bodySim_concrete`.  Source/hoist outer-loop runs are
related by `HoistInv [x] [x'] [(x,x')]`, eval/hf/bound, exactly as the §E `.loop`
arm holds after the prelude `prelude_bridge_list` re-establishes the entry
invariant. -/
theorem outer_loop_simulation_concrete [HasFvar P] [HasBool P] [HasNot P] [HasSubstFvar P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {g x x' g2idx : P.Ident} {τ : P.Ty} {rhs e : P.Expr} {lbl : String}
    {md md2_s md2_h md_loop_s md_loop_h : MetaData P}
    {ρ_src ρ_hoist ρ_post : Env P}
    -- the assembled outer body_sim (from STEP 3):
    (body_sim : BodySim (extendEval := extendEval) [x] [x'] [(x, x')]
      [ Stmt.cmd (.init x τ (.det rhs) md),
        Stmt.loop (.det (HasFvar.mkFvar g2idx)) none [] [Stmt.cmd (.assert lbl e md)] md2_s ]
      [ Stmt.cmd (.init x' τ (.det (HasSubstFvar.substFvar rhs x (HasFvar.mkFvar x'))) md),
        Stmt.loop (.det (substFvarMany (HasFvar.mkFvar g2idx) [(x, x')])) none []
          [Stmt.cmd (.assert lbl (HasSubstFvar.substFvar e x (HasFvar.mkFvar x')) md)] md2_h ])
    -- outer-loop guard-transport (top-level guard `g` UNCHANGED, so same-guard):
    (h_guard_tt : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) [x] [x'] [(x, x')] ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
       ρ_s.eval ρ_s.store (HasFvar.mkFvar g) = .some HasBool.tt →
       ρ_h.eval ρ_h.store (HasFvar.mkFvar g) = .some HasBool.tt)
    (h_guard_ff : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) [x] [x'] [(x, x')] ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
       ρ_s.eval ρ_s.store (HasFvar.mkFvar g) = .some HasBool.ff →
       ρ_h.eval ρ_h.store (HasFvar.mkFvar g) = .some HasBool.ff)
    (h_wfb : ∀ (ρ_s ρ_h : Env P), ρ_s.eval = ρ_h.eval →
       WellFormedSemanticEvalBool ρ_s.eval → WellFormedSemanticEvalBool ρ_h.eval)
    -- the OUTER body's no-exit + nofd (both sides):
    (h_outer_no_exit : ∀ (ρ : Env P) (lbl' : String) (ρe : Env P),
       ¬ StepStmtStar P (EvalCmd P) extendEval
           (.stmts
             [ Stmt.cmd (.init x τ (.det rhs) md),
               Stmt.loop (.det (HasFvar.mkFvar g2idx)) none [] [Stmt.cmd (.assert lbl e md)] md2_s ]
             ρ) (.exiting lbl' ρe))
    (h_outer_nofd_src : Block.noFuncDecl (P := P) (C := Cmd P)
       [ Stmt.cmd (.init x τ (.det rhs) md),
         Stmt.loop (.det (HasFvar.mkFvar g2idx)) none [] [Stmt.cmd (.assert lbl e md)] md2_s ] = true)
    (h_outer_nofd_h : Block.noFuncDecl (P := P) (C := Cmd P)
       [ Stmt.cmd (.init x' τ (.det (HasSubstFvar.substFvar rhs x (HasFvar.mkFvar x'))) md),
         Stmt.loop (.det (substFvarMany (HasFvar.mkFvar g2idx) [(x, x')])) none []
           [Stmt.cmd (.assert lbl (HasSubstFvar.substFvar e x (HasFvar.mkFvar x')) md)] md2_h ] = true)
    (h_hinv : HoistInv (P := P) [x] [x'] [(x, x')] ρ_src.store ρ_hoist.store)
    (h_eval : ρ_src.eval = ρ_hoist.eval) (h_hf : ρ_src.hasFailure = ρ_hoist.hasFailure)
    (h_bound : ∀ z ∈ [x'], ρ_hoist.store z ≠ none)
    (h_run : StepStmtStar P (EvalCmd P) extendEval
        (.stmt (.loop (.det (HasFvar.mkFvar g)) none []
          [ Stmt.cmd (.init x τ (.det rhs) md),
            Stmt.loop (.det (HasFvar.mkFvar g2idx)) none [] [Stmt.cmd (.assert lbl e md)] md2_s ]
          md_loop_s) ρ_src) (.terminal ρ_post)) :
    ∃ ρ_post_h : Env P,
      StepStmtStar P (EvalCmd P) extendEval
        (.stmt (.loop (.det (HasFvar.mkFvar g)) none []
          [ Stmt.cmd (.init x' τ (.det (HasSubstFvar.substFvar rhs x (HasFvar.mkFvar x'))) md),
            Stmt.loop (.det (substFvarMany (HasFvar.mkFvar g2idx) [(x, x')])) none []
              [Stmt.cmd (.assert lbl (HasSubstFvar.substFvar e x (HasFvar.mkFvar x')) md)] md2_h ]
          md_loop_h) ρ_hoist) (.terminal ρ_post_h) ∧
      HoistInv (P := P) [x] [x'] [(x, x')] ρ_post.store ρ_post_h.store ∧
      ρ_post.hasFailure = ρ_post_h.hasFailure ∧
      (∀ z ∈ [x'], ρ_post_h.store z ≠ none) :=
  LoopInitHoistLoopDriver.loopDet_lift_2g_recovers_single (g := HasFvar.mkFvar g)
    h_guard_tt h_guard_ff h_wfb
    body_sim h_outer_no_exit h_outer_nofd_src h_outer_nofd_h
    h_hinv h_eval h_hf h_bound h_run

/-! ## SUM-TYPED (terminal-OR-exiting) body/statement simulation.

The predicates above (`BodySimE` / `StmtSimE`) are TERMINAL-ONLY by construction:
they say nothing about a body that runs to `.exiting l ρ'` (the break pattern).
The redesigned `loopDet_lift_*_E` driver family (which drops `h_src_body_no_exit`)
consumes the sum-typed `BodySimSum`; to PRODUCE one from a `BodyTransport`
derivation, the eval-carrying provider vocabulary must also gain the exiting
clause.

`BodySimES` / `StmtSimES` are the eval-carrying, SUM-TYPED analogues: each carries
the existing terminal clause AND a parallel exiting clause that matches a source
`.exiting l ρ_s'` run by a hoist `.exiting l ρ_h'` run at the SAME label `l`,
re-establishing `HoistInv` / `hasFailure` / `B`-boundedness / `eval` at the
body-exit stores.  This is the exact relation the §E mutual already carries on
its `.exiting` disjunct (the body-exit `HoistInv`, NOT the weaker projected-store
`StoreAgreement`), so the enclosing loop's `.block .none` projection re-establishes
`HoistInv` via `HoistInv.project_both` exactly as the terminal clause does. -/

/-- Eval-carrying SUM-TYPED body sim: the terminal clause of `BodySimE`, plus an
exiting clause (a source `.exiting l` run is matched by a hoist `.exiting l` run
at the SAME label, with `HoistInv` / `hasFailure` / `B`-bound / `eval` agreement at
the body-exit stores). -/
@[expose] def BodySimES [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    (A B : List P.Ident) (subst : List (P.Ident × P.Ident))
    (bsrc bh : List (Stmt P (Cmd P))) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    HoistInv (P := P) A B subst ρ_s.store ρ_h.store →
    ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
    (∀ y ∈ B, ρ_h.store y ≠ none) →
    -- TERMINAL clause (exactly `BodySimE`):
    (∀ (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendEval (.stmts bsrc ρ_s) (.terminal ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendEval (.stmts bh ρ_h) (.terminal ρ_h') ∧
        HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
        ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none) ∧
        ρ_s'.eval = ρ_h'.eval)
    ∧
    -- EXITING clause (new):
    (∀ (l : String) (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendEval (.stmts bsrc ρ_s) (.exiting l ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendEval (.stmts bh ρ_h) (.exiting l ρ_h') ∧
        HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
        ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none) ∧
        ρ_s'.eval = ρ_h'.eval)

/-- Eval-carrying SUM-TYPED single-statement sim (the `StmtSimE` analogue, with the
parallel exiting clause). -/
@[expose] def StmtSimES [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    (A B : List P.Ident) (subst : List (P.Ident × P.Ident))
    (s s' : Stmt P (Cmd P)) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    HoistInv (P := P) A B subst ρ_s.store ρ_h.store →
    ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
    (∀ y ∈ B, ρ_h.store y ≠ none) →
    (∀ (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ_s) (.terminal ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendEval (.stmt s' ρ_h) (.terminal ρ_h') ∧
        HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
        ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none) ∧
        ρ_s'.eval = ρ_h'.eval)
    ∧
    (∀ (l : String) (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ_s) (.exiting l ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendEval (.stmt s' ρ_h) (.exiting l ρ_h') ∧
        HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
        ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none) ∧
        ρ_s'.eval = ρ_h'.eval)

/-- Forget the eval conjunct: `BodySimES → BodySimSum` (drops into the sum-typed
driver `loopDet_lift_2g_E`'s `body_sim` slot). -/
theorem bodySimES_to_bodySimSum [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
    [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {bsrc bh : List (Stmt P (Cmd P))}
    (h : BodySimES (extendEval := extendEval) A B subst bsrc bh) :
    LoopInitHoistLoopDriver.BodySimSum (extendEval := extendEval) A B subst bsrc bh := by
  intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd
  obtain ⟨h_term, h_exit⟩ := h ρ_s ρ_h h_hinv h_eval h_hf h_bnd
  refine ⟨?_, ?_⟩
  · intro ρ_s' h_run
    obtain ⟨ρ_h', h_run_h, h_hinv', h_hf', h_bnd', _⟩ := h_term ρ_s' h_run
    exact ⟨ρ_h', h_run_h, h_hinv', h_hf', h_bnd'⟩
  · intro l ρ_s' h_run
    obtain ⟨ρ_h', h_run_h, h_hinv', h_hf', h_bnd', _⟩ := h_exit l ρ_s' h_run
    exact ⟨ρ_h', h_run_h, h_hinv', h_hf', h_bnd'⟩

/-- The empty body is a `BodySimES`: terminal stays terminal (the `bodySimE_nil`
proof), and the empty body NEVER reaches `.exiting` (the only run is `step_stmts_nil`
to `.terminal`, so the exiting clause is vacuous). -/
theorem bodySimES_nil [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    (A B : List P.Ident) (subst : List (P.Ident × P.Ident)) :
    BodySimES (extendEval := extendEval) A B subst [] [] := by
  intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd
  refine ⟨?_, ?_⟩
  · -- terminal clause: replay `bodySimE_nil`.
    intro ρ_s' h_run
    have h_eq : ρ_s' = ρ_s := by
      cases h_run with
      | step _ _ _ h1 hr1 =>
        cases h1
        cases hr1 with
        | refl => rfl
        | step _ _ _ hd _ => exact nomatch hd
    subst h_eq
    refine ⟨ρ_h, ?_, h_hinv, h_hf, h_bnd, h_eval⟩
    exact ReflTrans.step _ _ _ StepStmt.step_stmts_nil (ReflTrans.refl _)
  · -- exiting clause: the empty body cannot reach `.exiting`.
    intro l ρ_s' h_run
    exfalso
    cases h_run with
    | step _ _ _ h1 hr1 =>
      cases h1
      cases hr1 with
      | step _ _ _ hd _ => exact nomatch hd

/-- THE SUM-TYPED CONS-SEQUENCER: a head `StmtSimES` and a tail `BodySimES` compose
into a `BodySimES` for the cons body.

The terminal clause is the `bodySimE_cons` proof verbatim.  The exiting clause:
a cons-run reaching `.exiting l ρ_s'` steps `.stmts (s :: rest) → .seq (.stmt s ρ_s) rest`,
then by `seq_reaches_exiting` either
  (a) the HEAD exits (`.stmt s ρ_s →* .exiting l ρ_s'`): fire the head's exiting
      clause → hoist head exits → reassemble the hoist cons-run's exit (`step_stmts_cons`
      then `seq_inner_star` then `step_seq_exit`); or
  (b) the head terminates to `ρ_mid` and the TAIL exits: fire the head's terminal
      clause (yielding mid `HoistInv`/eval/hf/bound), then the tail's exiting clause
      from the mid env, and splice the hoist head-run (terminal) with the hoist
      tail-run (exit) via `stmts_cons_step` then the tail. -/
theorem bodySimES_cons [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {s s' : Stmt P (Cmd P)} {rest rest' : List (Stmt P (Cmd P))}
    (hhead : StmtSimES (extendEval := extendEval) A B subst s s')
    (htail : BodySimES (extendEval := extendEval) A B subst rest rest') :
    BodySimES (extendEval := extendEval) A B subst (s :: rest) (s' :: rest') := by
  intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd
  refine ⟨?_, ?_⟩
  · -- terminal clause: `bodySimE_cons`.
    intro ρ_s' h_run
    obtain ⟨ρ_mid, h_head_run, h_rest_run⟩ :=
      stmts_cons_terminal_inv (extendEval := extendEval) h_run
    obtain ⟨ρ_h_mid, h_head_h_run, h_hinv_mid, h_hf_mid, h_bnd_mid, h_eval_mid⟩ :=
      (hhead ρ_s ρ_h h_hinv h_eval h_hf h_bnd).1 ρ_mid h_head_run
    obtain ⟨ρ_h', h_rest_h_run, h_hinv', h_hf', h_bnd', h_eval'⟩ :=
      (htail ρ_mid ρ_h_mid h_hinv_mid h_eval_mid h_hf_mid h_bnd_mid).1 ρ_s' h_rest_run
    refine ⟨ρ_h', ?_, h_hinv', h_hf', h_bnd', h_eval'⟩
    exact ReflTrans_Transitive _ _ _ _
      (stmts_cons_step P (EvalCmd P) extendEval s' rest' ρ_h ρ_h_mid h_head_h_run)
      h_rest_h_run
  · -- exiting clause.
    intro l ρ_s' h_run
    -- `.stmts (s :: rest) ρ_s → .seq (.stmt s ρ_s) rest → … → .exiting l ρ_s'`.
    have h_seq : StepStmtStar P (EvalCmd P) extendEval
        (.seq (.stmt s ρ_s) rest) (.exiting l ρ_s') := by
      cases h_run with
      | step _ _ _ h1 hr1 => cases h1; exact hr1
    rcases seq_reaches_exiting P (EvalCmd P) extendEval h_seq with
      h_head_exit | ⟨ρ_mid, h_head_term, h_tail_exit⟩
    · -- (a) the head exits with `l`.
      obtain ⟨ρ_h', h_head_h_exit, h_hinv', h_hf', h_bnd', h_eval'⟩ :=
        (hhead ρ_s ρ_h h_hinv h_eval h_hf h_bnd).2 l ρ_s' h_head_exit
      refine ⟨ρ_h', ?_, h_hinv', h_hf', h_bnd', h_eval'⟩
      -- reassemble: `.stmts (s' :: rest') ρ_h → .seq (.stmt s' ρ_h) rest' → … → .exiting`.
      refine ReflTrans.step _ _ _ StepStmt.step_stmts_cons ?_
      refine ReflTrans_Transitive _ _ _ _
        (seq_inner_star P (EvalCmd P) extendEval _ _ _ h_head_h_exit) ?_
      exact ReflTrans.step _ _ _ StepStmt.step_seq_exit (ReflTrans.refl _)
    · -- (b) the head terminates to `ρ_mid`, the tail exits with `l`.
      obtain ⟨ρ_h_mid, h_head_h_run, h_hinv_mid, h_hf_mid, h_bnd_mid, h_eval_mid⟩ :=
        (hhead ρ_s ρ_h h_hinv h_eval h_hf h_bnd).1 ρ_mid h_head_term
      obtain ⟨ρ_h', h_tail_h_exit, h_hinv', h_hf', h_bnd', h_eval'⟩ :=
        (htail ρ_mid ρ_h_mid h_hinv_mid h_eval_mid h_hf_mid h_bnd_mid).2 l ρ_s' h_tail_exit
      refine ⟨ρ_h', ?_, h_hinv', h_hf', h_bnd', h_eval'⟩
      -- splice the hoist head-run (terminal) with the hoist tail-run (exit).
      exact ReflTrans_Transitive _ _ _ _
        (stmts_cons_step P (EvalCmd P) extendEval s' rest' ρ_h ρ_h_mid h_head_h_run)
        h_tail_h_exit

/-! ## SUM-TYPED nested-loop `StmtSimES`.

The sum-typed analogue of `nestedLoop_stmtSimE`.  A nested loop
`.loop (.det g2) none [] inner` reaches `.exiting l` exactly when its OWN body
`inner` breaks with a label `l` (a loop has no catching label, so a body `.exit`
propagates straight through).  The terminal clause replays `nestedLoop_stmtSimE`'s
proof via `loopDet_lift_renamedGuard` (consuming the inner body's TERMINAL clause);
the exiting clause fires `loopDet_lift_renamedGuard_E` on the inner body's SUM-TYPED
sim, then recovers eval-preservation from both loop runs (`noFuncDecl` ⇒ eval fixed).

The inner-body simulation is supplied as a `BodySimSum` (the SELF-REFERENTIAL piece:
in the real §E mutual it comes from the same mutual recursion on the strictly-smaller
inner body, now sum-typed). -/
theorem nestedLoop_stmtSimES [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
    [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {g2 : P.Expr} {inner inner_h : List (Stmt P (Cmd P))} {md2_s md2_h : MetaData P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    (h_A_subst_fst : ∀ a ∈ A, a ∈ subst.map Prod.fst)
    (h_src_nodup : (subst.map Prod.fst).Nodup)
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd)
    (h_tgt_nodup : (subst.map Prod.snd).Nodup)
    (h_g_B_fresh : ∀ z ∈ B, z ∉ HasVarsPure.getVars g2)
    (h_wfvar   : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval)
    (h_wfcongr : ∀ ρ : Env P, WellFormedSemanticEvalExprCongr ρ.eval)
    (h_wfsubst : ∀ ρ : Env P, WellFormedSemanticEvalSubstFvar ρ.eval)
    (h_wfdef   : ∀ ρ : Env P, WellFormedSemanticEvalDef ρ.eval)
    -- the inner body's SUM-TYPED sim (self-referential piece — the §E IH on the
    -- SMALLER body, now terminal-OR-exiting):
    (inner_sim : LoopInitHoistLoopDriver.BodySimSum (extendEval := extendEval) A B subst inner inner_h)
    (h_nofd_src : Block.noFuncDecl inner = true)
    (h_nofd_h : Block.noFuncDecl inner_h = true) :
    StmtSimES (extendEval := extendEval) A B subst
      (.loop (.det g2) none [] inner md2_s)
      (.loop (.det (substFvarMany g2 subst)) none [] inner_h md2_h) := by
  intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd
  have h_src_nofd_loop : Stmt.noFuncDecl (.loop (.det g2) none [] inner md2_s) = true := by
    simp only [Stmt.noFuncDecl]; exact h_nofd_src
  have h_h_nofd_loop :
      Stmt.noFuncDecl (.loop (.det (substFvarMany g2 subst)) none [] inner_h md2_h) = true := by
    simp only [Stmt.noFuncDecl]; exact h_nofd_h
  refine ⟨?_, ?_⟩
  · -- terminal clause: the inner-body sum-typed sim feeds `loopDet_lift_renamedGuard_TE`
    -- (a nested loop CAN exit, so we route through the sum-typed terminal driver,
    -- which peels iterations WITHOUT a no-exit hypothesis — a `.none`-block reaching
    -- `.terminal` forces an inner `.terminal`, capping any would-be break).
    intro ρ_s' h_run
    obtain ⟨ρ_h', h_loop_h_run, h_hinv', h_hf', h_bnd'⟩ :=
      loopDet_lift_renamedGuard_TE (A := A) (B := B) (subst := subst)
        h_A_subst_fst h_src_nodup h_disjoint h_tgt_nodup h_g_B_fresh
        h_wfvar h_wfcongr h_wfsubst h_wfdef
        inner_sim h_nofd_src h_nofd_h
        h_hinv h_eval h_hf h_bnd h_run
    refine ⟨ρ_h', h_loop_h_run, h_hinv', h_hf', h_bnd', ?_⟩
    have e_s : ρ_s'.eval = ρ_s.eval :=
      smallStep_noFuncDecl_preserves_eval P (EvalCmd P) extendEval _ ρ_s ρ_s' h_src_nofd_loop h_run
    have e_h : ρ_h'.eval = ρ_h.eval :=
      smallStep_noFuncDecl_preserves_eval P (EvalCmd P) extendEval _ ρ_h ρ_h' h_h_nofd_loop h_loop_h_run
    rw [e_s, e_h]; exact h_eval
  · -- exiting clause: the inner-body SUM-TYPED sim feeds `loopDet_lift_renamedGuard_E`.
    intro l ρ_s' h_run
    obtain ⟨ρ_h', h_loop_h_run, h_hinv', h_hf', h_bnd'⟩ :=
      loopDet_lift_renamedGuard_E (A := A) (B := B) (subst := subst)
        h_A_subst_fst h_src_nodup h_disjoint h_tgt_nodup h_g_B_fresh
        h_wfvar h_wfcongr h_wfsubst h_wfdef
        inner_sim h_nofd_src h_nofd_h
        h_hinv h_eval h_hf h_bnd h_run
    refine ⟨ρ_h', h_loop_h_run, h_hinv', h_hf', h_bnd', ?_⟩
    have e_s : ρ_s'.eval = ρ_s.eval :=
      smallStep_noFuncDecl_preserves_eval_exiting P (EvalCmd P) extendEval _ ρ_s ρ_s' l h_src_nofd_loop h_run
    have e_h : ρ_h'.eval = ρ_h.eval :=
      smallStep_noFuncDecl_preserves_eval_exiting P (EvalCmd P) extendEval _ ρ_h ρ_h' l h_h_nofd_loop h_loop_h_run
    rw [e_s, e_h]; exact h_eval

/-- Generic lifter: a terminal-only `StmtSimE s s'` whose SOURCE statement `s` can
NEVER reach `.exiting` lifts to a sum-typed `StmtSimES s s'` — the exiting clause is
vacuous.  This is what every `.cmd` arm (init/set/assert/assume/cover/typeDecl) of
`Block.bodyTransport` needs: a command steps only to `.terminal` (`step_cmd`), so it
never `.exiting`s, and its existing `StmtSimE` lifts for free. -/
theorem stmtSimE_to_stmtSimES_of_noExit [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {s s' : Stmt P (Cmd P)}
    (h_src_no_exit : ∀ (ρ : Env P) (l : String) (ρe : Env P),
       ¬ StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ) (.exiting l ρe))
    (h : StmtSimE (extendEval := extendEval) A B subst s s') :
    StmtSimES (extendEval := extendEval) A B subst s s' := by
  intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd
  refine ⟨?_, ?_⟩
  · intro ρ_s' h_run; exact h ρ_s ρ_h h_hinv h_eval h_hf h_bnd ρ_s' h_run
  · intro l ρ_s' h_run; exact absurd h_run (h_src_no_exit ρ_s l ρ_s')

/-- A single `.cmd` statement never reaches `.exiting` (it steps to `.terminal` via
`step_cmd` and is then stuck). -/
theorem cmd_stmt_no_exit [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    (c : Cmd P) :
    ∀ (ρ : Env P) (l : String) (ρe : Env P),
      ¬ StepStmtStar P (EvalCmd P) extendEval (.stmt (.cmd c) ρ) (.exiting l ρe) := by
  intro ρ l ρe h
  cases h with
  | step _ _ _ h1 hr1 =>
    cases h1
    cases hr1 with
    | step _ _ _ hd _ => exact nomatch hd

/-! ## The `.ite` arms of a sum-typed `StmtSimES`.

An `.ite` steps to its taken branch body `.stmts tss/ess ρ` in the SAME store (no
block wrapper — branch-locals are not projected).  So an `.ite` reaches `.exiting l`
exactly when the taken branch exits with `l`, propagated verbatim.  The det-guard
arm transports the guard via the supplied `h_guard_eq` (the renamed guard evaluates as
the source guard, exactly the `cond_transport'` fact `Block.bodyTransport`'s `.ite`
arm computes); the nondet arm replays the same branch choice. -/
theorem ite_stmtSimES [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
    [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {g : P.Expr} {tss_s tss_h ess_s ess_h : List (Stmt P (Cmd P))} {md : MetaData P}
    -- the renamed guard evaluates as the source guard under any HoistInv-related
    -- entry with eval-equality (the `cond_transport'` fact):
    (h_guard_eq : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
       (∃ w, ρ_s.eval ρ_s.store g = some w) →
       ρ_s.eval ρ_s.store g = ρ_h.eval ρ_h.store (substFvarMany g subst))
    (then_sim : BodySimES (extendEval := extendEval) A B subst tss_s tss_h)
    (else_sim : BodySimES (extendEval := extendEval) A B subst ess_s ess_h) :
    StmtSimES (extendEval := extendEval) A B subst
      (.ite (.det g) tss_s ess_s md)
      (.ite (.det (substFvarMany g subst)) tss_h ess_h md) := by
  intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd
  -- Peel the source `.ite` step into a branch run (guard tt → then, ff → else).  The
  -- `.refl` case is impossible: a target reaching `.terminal`/`.exiting` differs from
  -- the un-stepped `.stmt (.ite …)`, so any such run takes the ite step first.
  have peel : ∀ {ρ' : Env P} {tgt : Config P (Cmd P)},
      (tgt = .terminal ρ' ∨ ∃ l, tgt = .exiting l ρ') →
      StepStmtStar P (EvalCmd P) extendEval (.stmt (.ite (.det g) tss_s ess_s md) ρ_s) tgt →
      (ρ_s.eval ρ_s.store g = .some HasBool.tt ∧ WellFormedSemanticEvalBool ρ_s.eval ∧
        StepStmtStar P (EvalCmd P) extendEval (.stmts tss_s ρ_s) tgt) ∨
      (ρ_s.eval ρ_s.store g = .some HasBool.ff ∧ WellFormedSemanticEvalBool ρ_s.eval ∧
        StepStmtStar P (EvalCmd P) extendEval (.stmts ess_s ρ_s) tgt) := by
    intro ρ' tgt htgt h
    cases h with
    | refl => rcases htgt with h | ⟨l, h⟩ <;> exact nomatch h
    | step _ _ _ h1 hr1 =>
      cases h1 with
      | step_ite_true hg hwf => exact .inl ⟨hg, hwf, hr1⟩
      | step_ite_false hg hwf => exact .inr ⟨hg, hwf, hr1⟩
  -- The hoist guard equals the source guard's value (transported).
  have guard_h : ∀ {bv : P.Expr}, ρ_s.eval ρ_s.store g = .some bv →
      ρ_h.eval ρ_h.store (substFvarMany g subst) = .some bv := by
    intro bv hg
    have := h_guard_eq ρ_s ρ_h h_hinv h_eval ⟨_, hg⟩
    rw [hg] at this; exact this.symm
  refine ⟨?_, ?_⟩
  · -- terminal clause.
    intro ρ_s' h_run
    rcases peel (Or.inl rfl) h_run with ⟨hg, hwf, h_branch⟩ | ⟨hg, hwf, h_branch⟩
    · obtain ⟨ρ_h', h_branch_h, h_hinv', h_hf', h_bnd', h_eval'⟩ :=
        (then_sim ρ_s ρ_h h_hinv h_eval h_hf h_bnd).1 ρ_s' h_branch
      refine ⟨ρ_h', ?_, h_hinv', h_hf', h_bnd', h_eval'⟩
      exact ReflTrans.step _ _ _ (StepStmt.step_ite_true (guard_h hg) (h_eval ▸ hwf)) h_branch_h
    · obtain ⟨ρ_h', h_branch_h, h_hinv', h_hf', h_bnd', h_eval'⟩ :=
        (else_sim ρ_s ρ_h h_hinv h_eval h_hf h_bnd).1 ρ_s' h_branch
      refine ⟨ρ_h', ?_, h_hinv', h_hf', h_bnd', h_eval'⟩
      exact ReflTrans.step _ _ _ (StepStmt.step_ite_false (guard_h hg) (h_eval ▸ hwf)) h_branch_h
  · -- exiting clause.
    intro l ρ_s' h_run
    rcases peel (Or.inr ⟨l, rfl⟩) h_run with ⟨hg, hwf, h_branch⟩ | ⟨hg, hwf, h_branch⟩
    · obtain ⟨ρ_h', h_branch_h, h_hinv', h_hf', h_bnd', h_eval'⟩ :=
        (then_sim ρ_s ρ_h h_hinv h_eval h_hf h_bnd).2 l ρ_s' h_branch
      refine ⟨ρ_h', ?_, h_hinv', h_hf', h_bnd', h_eval'⟩
      exact ReflTrans.step _ _ _ (StepStmt.step_ite_true (guard_h hg) (h_eval ▸ hwf)) h_branch_h
    · obtain ⟨ρ_h', h_branch_h, h_hinv', h_hf', h_bnd', h_eval'⟩ :=
        (else_sim ρ_s ρ_h h_hinv h_eval h_hf h_bnd).2 l ρ_s' h_branch
      refine ⟨ρ_h', ?_, h_hinv', h_hf', h_bnd', h_eval'⟩
      exact ReflTrans.step _ _ _ (StepStmt.step_ite_false (guard_h hg) (h_eval ▸ hwf)) h_branch_h

/-- The nondet-guard `.ite` arm: no guard test; the hoist replays the SAME branch
choice (then/else) the source took. -/
theorem ite_nondet_stmtSimES [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
    [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {tss_s tss_h ess_s ess_h : List (Stmt P (Cmd P))} {md : MetaData P}
    (then_sim : BodySimES (extendEval := extendEval) A B subst tss_s tss_h)
    (else_sim : BodySimES (extendEval := extendEval) A B subst ess_s ess_h) :
    StmtSimES (extendEval := extendEval) A B subst
      (.ite .nondet tss_s ess_s md) (.ite .nondet tss_h ess_h md) := by
  intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd
  have peel : ∀ {ρ' : Env P} {tgt : Config P (Cmd P)},
      (tgt = .terminal ρ' ∨ ∃ l, tgt = .exiting l ρ') →
      StepStmtStar P (EvalCmd P) extendEval (.stmt (.ite .nondet tss_s ess_s md) ρ_s) tgt →
      (StepStmtStar P (EvalCmd P) extendEval (.stmts tss_s ρ_s) tgt) ∨
      (StepStmtStar P (EvalCmd P) extendEval (.stmts ess_s ρ_s) tgt) := by
    intro ρ' tgt htgt h
    cases h with
    | refl => rcases htgt with h | ⟨l, h⟩ <;> exact nomatch h
    | step _ _ _ h1 hr1 =>
      cases h1 with
      | step_ite_nondet_true => exact .inl hr1
      | step_ite_nondet_false => exact .inr hr1
  refine ⟨?_, ?_⟩
  · intro ρ_s' h_run
    rcases peel (Or.inl rfl) h_run with h_branch | h_branch
    · obtain ⟨ρ_h', h_branch_h, h_hinv', h_hf', h_bnd', h_eval'⟩ :=
        (then_sim ρ_s ρ_h h_hinv h_eval h_hf h_bnd).1 ρ_s' h_branch
      exact ⟨ρ_h', ReflTrans.step _ _ _ StepStmt.step_ite_nondet_true h_branch_h,
        h_hinv', h_hf', h_bnd', h_eval'⟩
    · obtain ⟨ρ_h', h_branch_h, h_hinv', h_hf', h_bnd', h_eval'⟩ :=
        (else_sim ρ_s ρ_h h_hinv h_eval h_hf h_bnd).1 ρ_s' h_branch
      exact ⟨ρ_h', ReflTrans.step _ _ _ StepStmt.step_ite_nondet_false h_branch_h,
        h_hinv', h_hf', h_bnd', h_eval'⟩
  · intro l ρ_s' h_run
    rcases peel (Or.inr ⟨l, rfl⟩) h_run with h_branch | h_branch
    · obtain ⟨ρ_h', h_branch_h, h_hinv', h_hf', h_bnd', h_eval'⟩ :=
        (then_sim ρ_s ρ_h h_hinv h_eval h_hf h_bnd).2 l ρ_s' h_branch
      exact ⟨ρ_h', ReflTrans.step _ _ _ StepStmt.step_ite_nondet_true h_branch_h,
        h_hinv', h_hf', h_bnd', h_eval'⟩
    · obtain ⟨ρ_h', h_branch_h, h_hinv', h_hf', h_bnd', h_eval'⟩ :=
        (else_sim ρ_s ρ_h h_hinv h_eval h_hf h_bnd).2 l ρ_s' h_branch
      exact ⟨ρ_h', ReflTrans.step _ _ _ StepStmt.step_ite_nondet_false h_branch_h,
        h_hinv', h_hf', h_bnd', h_eval'⟩

/-! ## The `.block` arm of a sum-typed `StmtSimES` (the hard extension).

This is the arm the StepC-producer comment names as "the hard extension".  A
`.block lbl inner` whose inner body can `.exit` has THREE outcomes:
  (T1) inner `.terminal` → block `.terminal` (projected);
  (T2) inner `.exiting lbl` (matches the block label) → block CATCHES it →
       `.terminal` (projected) — this is the previously-unhandled case;
  (X)  inner `.exiting l` with `l ≠ lbl` (mismatch) → block PROPAGATES `.exiting l`
       (projected).
Given a `BodySimES` for the inner body, all three close: the hoist block replays the
same inner outcome (terminal/match/mismatch) at the SAME label, and `HoistInv` survives
the projection via `HoistInv.project_both`. -/
theorem block_stmtSimES [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
    [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {lbl : String} {inner inner_h : List (Stmt P (Cmd P))} {md : MetaData P}
    (inner_sim : BodySimES (extendEval := extendEval) A B subst inner inner_h) :
    StmtSimES (extendEval := extendEval) A B subst
      (.block lbl inner md) (.block lbl inner_h md) := by
  intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd
  -- A `b ∈ B` survives the projection `projectStore ρ_h.store · b`: the parent binds
  -- `b` (`h_bnd`), so `projectStore` keeps the inner value, which the inner sim's
  -- boundedness makes `some`.
  have bound_proj : ∀ (ρ_inner : Env P), (∀ y ∈ B, ρ_inner.store y ≠ none) →
      ∀ y ∈ B, projectStore ρ_h.store ρ_inner.store y ≠ none := by
    intro ρ_inner h_bnd_inner y hy
    unfold projectStore
    have h_parent_some : (ρ_h.store y).isSome = true := by
      cases h : ρ_h.store y with
      | none => exact absurd h (h_bnd y hy)
      | some _ => rfl
    rw [h_parent_some]; simp; exact h_bnd_inner y hy
  -- Peel the source block-enter step: `.stmt (.block lbl inner md) ρ → .block (.some lbl)
  -- ρ.store (.stmts inner ρ)`, exposing the inner-config run for inversion.
  have peel_term : ∀ (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendEval (.stmt (.block lbl inner md) ρ_s) (.terminal ρ_s') →
      StepStmtStar P (EvalCmd P) extendEval
        (.block (.some lbl) ρ_s.store (.stmts inner ρ_s)) (.terminal ρ_s') := by
    intro ρ_s' h_run
    cases h_run with
    | step _ _ _ h1 hr1 => cases h1; exact hr1
  have peel_exit : ∀ (l : String) (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendEval (.stmt (.block lbl inner md) ρ_s) (.exiting l ρ_s') →
      StepStmtStar P (EvalCmd P) extendEval
        (.block (.some lbl) ρ_s.store (.stmts inner ρ_s)) (.exiting l ρ_s') := by
    intro l ρ_s' h_run
    cases h_run with
    | step _ _ _ h1 hr1 => cases h1; exact hr1
  refine ⟨?_, ?_⟩
  · -- terminal clause: inner `.terminal` (T1) OR inner `.exiting lbl` matched (T2).
    intro ρ_s' h_run0
    have h_run := peel_term ρ_s' h_run0
    rcases block_some_reaches_terminal P (EvalCmd P) extendEval h_run with
      ⟨ρ_inner, h_inner_term, h_eq⟩ | ⟨ρ_inner, h_inner_exit, h_eq⟩
    · -- T1: inner terminates.  Feed the inner TERMINAL clause.
      obtain ⟨ρ_h_inner, h_inner_h_run, h_hinv_inner, h_hf_inner, h_bnd_inner, h_eval_inner⟩ :=
        (inner_sim ρ_s ρ_h h_hinv h_eval h_hf h_bnd).1 ρ_inner h_inner_term
      refine ⟨{ ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store }, ?_, ?_, ?_, ?_, ?_⟩
      · -- hoist block: enter, run inner to terminal, `step_block_done`.
        refine ReflTrans.step _ _ _ StepStmt.step_block ?_
        refine ReflTrans_Transitive _ _ _ _
          (block_inner_star P (EvalCmd P) extendEval _ _ (some lbl) ρ_h.store h_inner_h_run) ?_
        exact ReflTrans.step _ _ _ StepStmt.step_block_done (ReflTrans.refl _)
      · subst h_eq; exact HoistInv.project_both h_hinv h_hinv_inner
      · subst h_eq; show ρ_inner.hasFailure = ρ_h_inner.hasFailure; exact h_hf_inner
      · subst h_eq; exact bound_proj ρ_h_inner h_bnd_inner
      · subst h_eq; show ρ_inner.eval = ρ_h_inner.eval; exact h_eval_inner
    · -- T2: inner exits with the block's own label `lbl` → block catches it.
      obtain ⟨ρ_h_inner, h_inner_h_run, h_hinv_inner, h_hf_inner, h_bnd_inner, h_eval_inner⟩ :=
        (inner_sim ρ_s ρ_h h_hinv h_eval h_hf h_bnd).2 lbl ρ_inner h_inner_exit
      refine ⟨{ ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store }, ?_, ?_, ?_, ?_, ?_⟩
      · -- hoist block: enter, run inner to `.exiting lbl`, `step_block_exit_match`.
        refine ReflTrans.step _ _ _ StepStmt.step_block ?_
        refine ReflTrans_Transitive _ _ _ _
          (block_inner_star P (EvalCmd P) extendEval _ _ (some lbl) ρ_h.store h_inner_h_run) ?_
        exact ReflTrans.step _ _ _ (StepStmt.step_block_exit_match rfl) (ReflTrans.refl _)
      · subst h_eq; exact HoistInv.project_both h_hinv h_hinv_inner
      · subst h_eq; show ρ_inner.hasFailure = ρ_h_inner.hasFailure; exact h_hf_inner
      · subst h_eq; exact bound_proj ρ_h_inner h_bnd_inner
      · subst h_eq; show ρ_inner.eval = ρ_h_inner.eval; exact h_eval_inner
  · -- exiting clause: inner exits with `l ≠ lbl` (mismatch) → block propagates.
    intro l ρ_s' h_run0
    have h_run := peel_exit l ρ_s' h_run0
    obtain ⟨ρ_inner, h_inner_exit, h_ne, h_eq⟩ :=
      block_reaches_exiting_strong P (EvalCmd P) extendEval h_run
    obtain ⟨ρ_h_inner, h_inner_h_run, h_hinv_inner, h_hf_inner, h_bnd_inner, h_eval_inner⟩ :=
      (inner_sim ρ_s ρ_h h_hinv h_eval h_hf h_bnd).2 l ρ_inner h_inner_exit
    refine ⟨{ ρ_h_inner with store := projectStore ρ_h.store ρ_h_inner.store }, ?_, ?_, ?_, ?_, ?_⟩
    · -- hoist block: enter, run inner to `.exiting l`, `step_block_exit_mismatch`.
      refine ReflTrans.step _ _ _ StepStmt.step_block ?_
      refine ReflTrans_Transitive _ _ _ _
        (block_inner_star P (EvalCmd P) extendEval _ _ (some lbl) ρ_h.store h_inner_h_run) ?_
      exact ReflTrans.step _ _ _ (StepStmt.step_block_exit_mismatch h_ne) (ReflTrans.refl _)
    · subst h_eq; exact HoistInv.project_both h_hinv h_hinv_inner
    · subst h_eq; show ρ_inner.hasFailure = ρ_h_inner.hasFailure; exact h_hf_inner
    · subst h_eq; exact bound_proj ρ_h_inner h_bnd_inner
    · subst h_eq; show ρ_inner.eval = ρ_h_inner.eval; exact h_eval_inner

/-! ## The `.exit` base case for a sum-typed `StmtSimES`.

A single `.exit lbl md` statement is the new base case the (future) `BodyTransport.exit`
constructor invokes.  The source `.stmt (.exit lbl md) ρ_s` reaches ONLY `.exiting lbl ρ_s`
(never `.terminal` — `step_exit` produces `.exiting`).  The hoist side is the SAME
`.exit lbl md` (`applyRenames`/`substIdent` leaves `.exit` literally unchanged), which
reaches `.exiting lbl ρ_h` carrying the body-entry `HoistInv`/eval/hf/bound unchanged
(the `.exit` copies the env).  So the terminal clause is vacuous and the exiting clause
re-uses the entry invariant. -/
theorem exit_stmtSimES [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    (A B : List P.Ident) (subst : List (P.Ident × P.Ident)) (lbl : String) (md : MetaData P) :
    StmtSimES (extendEval := extendEval) A B subst (.exit lbl md) (.exit lbl md) := by
  intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd
  refine ⟨?_, ?_⟩
  · -- terminal clause: `.exit` never reaches `.terminal` (only `.exiting`).
    intro ρ_s' h_run
    exfalso
    cases h_run with
    | step _ _ _ h1 hr1 =>
      cases h1
      cases hr1 with
      | step _ _ _ hd _ => exact nomatch hd
  · -- exiting clause: invert the source `.exit` run (label = lbl, env unchanged),
    -- then drive the hoist `.exit` to `.exiting lbl ρ_h`.
    intro l ρ_s' h_run
    have h_inv : l = lbl ∧ ρ_s' = ρ_s := by
      cases h_run with
      | step _ _ _ h1 hr1 =>
        cases h1
        cases hr1 with
        | refl => exact ⟨rfl, rfl⟩
        | step _ _ _ hd _ => exact nomatch hd
    obtain ⟨h_l, h_ρ⟩ := h_inv
    subst h_l; subst h_ρ
    refine ⟨ρ_h, ?_, h_hinv, h_hf, h_bnd, h_eval⟩
    exact ReflTrans.step _ _ _ StepStmt.step_exit (ReflTrans.refl _)

end OptEStepBProvider
end Imperative

end -- public section
