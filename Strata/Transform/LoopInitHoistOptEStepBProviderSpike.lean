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
open LoopInitHoistLoopDriver (loopDet_lift_2g loopDet_lift_renamedGuard renamed_guard_eval_same_delta)

variable {P : PureExpr}
  [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
  [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr]
  [DecidableEq P.Ident]

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
def BodySim {extendEval : ExtendEval P}
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
@[expose] def BodySimE {extendEval : ExtendEval P}
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

omit [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [DecidableEq P.Ident] in
/-- Forget the eval conjunct: `BodySimE → BodySim` (drops into the driver slot). -/
theorem bodySimE_to_bodySim {extendEval : ExtendEval P}
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
omit [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P] [HasVarsPure P P.Expr] in
theorem body₃_concrete
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
@[expose] def StmtSimE {extendEval : ExtendEval P}
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

omit [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [DecidableEq P.Ident] in
/-- The empty body is a `BodySimE` (terminal stays terminal, store/eval unchanged). -/
theorem bodySimE_nil {extendEval : ExtendEval P}
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

omit [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [DecidableEq P.Ident] in
/-- THE CONS-SEQUENCER: a head `StmtSimE` and a tail `BodySimE` compose into a
`BodySimE` for the cons body.  This is the structural glue the §E cons recursion
performs; here it is proved ONCE, generically, at arbitrary carriers `A B subst`.
The proof: invert the source cons-run into head + tail (`stmts_cons_terminal_inv`),
fire the head `StmtSimE` to get the hoist head-run, MID `HoistInv`, and MID eval-eq,
fire the tail `BodySimE` from the mid env, and reassemble the hoist cons-run via
`stmts_cons_step`. -/
theorem bodySimE_cons {extendEval : ExtendEval P}
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
omit [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P] in
theorem nestedLoop_stmtSimE
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
omit [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P] in
theorem outer_bodySim_concrete
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
omit [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P] in
theorem outer_loop_simulation_concrete
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

end OptEStepBProvider
end Imperative

end -- public section
