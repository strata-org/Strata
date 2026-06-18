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
public import Strata.Transform.LoopInitHoistContains
public import Strata.Transform.LoopInitHoistFreshness
public import Strata.Transform.LoopInitHoistRewrite
public import Strata.Transform.LoopInitHoistInfra
public import Strata.Transform.DetToKleeneCorrect

import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.Cmd
import all Strata.Transform.LoopInitHoist
import all Strata.Transform.LoopInitHoistContains
import all Strata.Transform.LoopInitHoistFreshness
import all Strata.Transform.LoopInitHoistRewrite
import all Strata.Transform.LoopInitHoistInfra
import all Strata.Transform.DetToKleeneCorrect

public section

/-! # Loop-init hoisting: the `.loop`-arm driver library

This file collects the reusable lemmas that the `.loop` arm of the loop-init
hoisting equivalence proof (`Strata/Transform/LoopInitHoistCorrect.lean`) cites
to discharge a renamed nested loop.  It sits upstream of the equivalence proof
(`LoopInitHoistCorrect` imports it) and depends only on the hoisting
infrastructure (`LoopInitHoistInfra`) and the determinised-loop iteration
machinery (`DetToKleeneCorrect`).

The library has four parts:

1. **Two-guard determinised-loop driver.**  A generalisation of the
   single-guard iteration lift in which the source loop guard `g_s` and the
   hoist loop guard `g_h` may differ.  A nested loop's guard is renamed by
   `applyRenames` (`g ↦ substFvarMany g subst`), so the source runs
   `.loop (.det g_s) …` while the hoist runs `.loop (.det g_h) …` with
   `g_h = substFvarMany g_s subst`.  The two guards need not be definitionally
   equal — only to evaluate equally under `HoistInv`, which
   `renamed_guard_eval_same_delta` establishes because the loop guard reads no
   renamed name (every variable it reads lies in the `HoistInv` frame).
   `loopDet_lift_renamedGuard` packages this specialisation: the caller supplies
   only the body simulation and the freshness / well-formedness side facts.

2. **Entries-from-lift structural bridge.**  Connects the concrete lift output
   `Block.liftInitsInLoopBodyM ss σ` to the abstract `entries` list consumed by
   the prelude bridge: it exhibits `entries` such that the lift's havocs (mapped
   to `.cmd`) equal `havocStmts' entries`, the lift's renames equal
   `substOf' entries`, and every entry's source ident is a body init.

3. **Per-entry-metadata prelude bridge.**  Runs the arbitrary-length havoc
   prelude `havocStmts' entries` from a store-equal environment and establishes
   `HoistInv A (targetsOf' entries) (substOf' entries)` together with the
   evaluator / failure agreement and target-boundedness the driver consumes.
   Each entry carries its own type and metadata, matching the lift output on the
   nose.

4. **Union-carrier body-simulation compose.**  Composes a Step-A body
   simulation at the enclosing carriers `Ao Bo so` with a Step-B body simulation
   at the new inner carriers `As Bs ss` into a single body simulation at the
   union carriers `(Ao ++ As) (Bo ++ Bs) (so ++ ss)`, which is exactly the
   `body_sim` slot the two-guard driver consumes.
-/

namespace Imperative
namespace LoopInitHoistLoopDriver

open StructuredToUnstructuredCorrect (extendStoreOne extendStoreOne_self extendStoreOne_other)

variable {P : PureExpr}

/-! ## Iteration peel / build helpers.

`peelIterationDet` and `buildLoopIterationDet` are the per-iteration inversion
and construction lemmas for a determinised loop with no measure and no
invariants.  They are restated here (rather than imported from the equivalence
proof) so this driver library sits strictly upstream of that proof.  Both are
self-contained against the iteration machinery in `DetToKleeneCorrect` and the
store/relation helpers; they are internal to this file. -/

private theorem peelIterationDet [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {g : P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {ρ_pre ρ_post : Env P} {hasInvFailure : Bool}
    (h_body_no_exit : ∀ (lbl : String) (ρe : Env P),
       ¬ StepStmtStar P (EvalCmd P) extendEval
           (.stmts body { ρ_pre with hasFailure := ρ_pre.hasFailure || hasInvFailure })
           (.exiting lbl ρe))
    (hrest : ReflTransT (StepStmt P (EvalCmd P) extendEval)
       (.seq (.block .none ρ_pre.store
                (.stmts body { ρ_pre with hasFailure := ρ_pre.hasFailure || hasInvFailure }))
             [.loop (.det g) none inv body md])
       (.terminal ρ_post)) :
    ∃ (ρ_inner : Env P),
      StepStmtStar P (EvalCmd P) extendEval
        (.stmts body { ρ_pre with hasFailure := ρ_pre.hasFailure || hasInvFailure })
        (.terminal ρ_inner) ∧
      ∃ (h_inner_T : ReflTransT (StepStmt P (EvalCmd P) extendEval)
                      (.stmt (Stmt.loop (.det g) none inv body md)
                        { ρ_inner with store := projectStore ρ_pre.store ρ_inner.store })
                      (.terminal ρ_post)),
        h_inner_T.len < hrest.len := by
  obtain ⟨ρ_block, h_block_term, h_loop_stmts, hlen_seq⟩ :=
    seqT_reaches_terminal extendEval hrest
  obtain ⟨ρ_inner, h_body_term_T, h_ρ_block_eq, hlen_block⟩ :=
    blockT_reaches_terminal_noExit extendEval h_block_term h_body_no_exit
  subst h_ρ_block_eq
  obtain ⟨ρ_x, h_loop_T, h_nil, hlen_cons⟩ :=
    stmtsT_cons_terminal extendEval h_loop_stmts
  have hρ_x_eq : ρ_x = ρ_post := by
    match h_nil with
    | .step _ _ _ .step_stmts_nil hr2 =>
      match hr2 with
      | .refl _ => rfl
      | .step _ _ _ h _ => exact nomatch h
  subst hρ_x_eq
  exact ⟨ρ_inner, reflTransT_to_prop h_body_term_T, h_loop_T, by omega⟩

private theorem buildLoopIterationDet [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {g : P.Expr} {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {ρ_pre ρ_body : Env P}
    (h_guard : ρ_pre.eval ρ_pre.store g = .some HasBool.tt)
    (h_wfb : WellFormedSemanticEvalBool ρ_pre.eval)
    (h_body_run : StepStmtStar P (EvalCmd P) extendEval
        (.stmts body ρ_pre) (.terminal ρ_body)) :
    StepStmtStar P (EvalCmd P) extendEval
      (.stmt (.loop (.det g) none [] body md) ρ_pre)
      (.stmts [.loop (.det g) none [] body md]
        { ρ_body with store := projectStore ρ_pre.store ρ_body.store }) := by
  have h_enter : StepStmt P (EvalCmd P) extendEval
      (.stmt (.loop (.det g) none [] body md) ρ_pre)
      (.seq (.block .none ρ_pre.store
              (.stmts body { ρ_pre with hasFailure := ρ_pre.hasFailure || false }))
            [.loop (.det g) none [] body md]) :=
    .step_loop_enter h_guard (by intro le hle; simp at hle) (by simp) h_wfb
  have h_ρpre_eq : ({ ρ_pre with hasFailure := ρ_pre.hasFailure || false } : Env P) = ρ_pre := by
    simp
  rw [h_ρpre_eq] at h_enter
  have h_block_run : StepStmtStar P (EvalCmd P) extendEval
      (.block .none ρ_pre.store (.stmts body ρ_pre))
      (.terminal { ρ_body with store := projectStore ρ_pre.store ρ_body.store }) :=
    ReflTrans_Transitive _ _ _ _
      (block_inner_star P (EvalCmd P) extendEval _ _ (none : Option String) ρ_pre.store h_body_run)
      (.step _ _ _ .step_block_done (.refl _))
  have h_seq_run : StepStmtStar P (EvalCmd P) extendEval
      (.seq (.block .none ρ_pre.store (.stmts body ρ_pre))
            [.loop (.det g) none [] body md])
      (.stmts [.loop (.det g) none [] body md]
        { ρ_body with store := projectStore ρ_pre.store ρ_body.store }) :=
    ReflTrans_Transitive _ _ _ _
      (seq_inner_star P (EvalCmd P) extendEval _ _ _ h_block_run)
      (.step _ _ _ .step_seq_done (.refl _))
  exact ReflTrans.step _ _ _ h_enter h_seq_run

/-! ## No-exit lemmas for hoist-eligible determinised loops.

A determinised loop whose body never produces a labeled `.exiting` can itself
never reach `.exiting`.  These `*'`-suffixed `ReflTransT` exiting-trace
decompositions and the fuel-bounded `loopDet_no_exit*` family are restated here
(rather than imported from the equivalence proof) so this driver library sits
strictly upstream of that proof.  They are self-contained against the iteration
machinery in `DetToKleeneCorrect` and the store/relation helpers. -/

/-- T-version of `seq_reaches_exiting` (private in SUC; re-derived here). -/
public theorem seqT_reaches_exiting' [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {inner : Config P (Cmd P)} {ss : List (Stmt P (Cmd P))}
    {label : String} {ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval)
              (.seq inner ss) (.exiting label ρ')) :
    (∃ (h : ReflTransT (StepStmt P (EvalCmd P) extendEval) inner (.exiting label ρ')),
      h.len < hstar.len) ∨
    (∃ (ρ₁ : Env P)
      (h1 : ReflTransT (StepStmt P (EvalCmd P) extendEval) inner (.terminal ρ₁))
      (h2 : ReflTransT (StepStmt P (EvalCmd P) extendEval)
              (.stmts ss ρ₁) (.exiting label ρ')),
      h1.len + h2.len < hstar.len) := by
  match hstar with
  | .step _ _ _ (.step_seq_inner h) hrest =>
    match seqT_reaches_exiting' hrest with
    | .inl ⟨hexit, hlen⟩ => exact .inl ⟨.step _ _ _ h hexit, by simp [ReflTransT.len]; omega⟩
    | .inr ⟨ρ₁, h1, h2, hlen⟩ => exact .inr ⟨ρ₁, .step _ _ _ h h1, h2, by simp [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_seq_done hrest =>
    exact .inr ⟨_, .refl _, hrest, by show 0 + hrest.len < 1 + hrest.len; omega⟩
  | .step _ _ _ .step_seq_exit hrest =>
    match hrest with
    | .refl _ => exact .inl ⟨.refl _, by show 0 < 1; omega⟩
    | .step _ _ _ h _ => exact nomatch h

/-- T-version: `.block .none σ inner` reaching `.exiting label`. -/
public theorem blockT_none_reaches_exiting' [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {inner : Config P (Cmd P)} {σ_parent : SemanticStore P}
    {label : String} {ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval)
              (.block .none σ_parent inner) (.exiting label ρ')) :
    ∃ (ρ_inner : Env P)
      (h : ReflTransT (StepStmt P (EvalCmd P) extendEval) inner (.exiting label ρ_inner)),
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } ∧
      h.len < hstar.len := by
  match hstar with
  | .step _ (.block _ _ inner₁) _ (.step_block_body h) hrest =>
    have ⟨ρ_inner, hexit, heq, hlen⟩ := blockT_none_reaches_exiting' hrest
    exact ⟨ρ_inner, .step _ _ _ h hexit, heq, by simp [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_block_done hrest =>
    match hrest with
    | .step _ _ _ h _ => exact nomatch h
  | .step _ _ _ (.step_block_exit_match heq) _ => exact (nomatch heq)
  | .step _ _ _ (.step_block_exit_mismatch hne) hrest =>
    match hrest with
    | .refl _ => exact ⟨_, .refl _, rfl, by simp [ReflTransT.len]⟩
    | .step _ _ _ h _ => exact nomatch h

/-- T-version of `stmtsT_cons` for the exiting case. -/
public theorem stmtsT_cons_exiting' [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))}
    {ρ₀ : Env P} {label : String} {ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval)
              (.stmts (s :: rest) ρ₀) (.exiting label ρ')) :
    (∃ (h : ReflTransT (StepStmt P (EvalCmd P) extendEval)
              (.stmt s ρ₀) (.exiting label ρ')),
      h.len < hstar.len) ∨
    (∃ (ρ₁ : Env P)
      (h1 : ReflTransT (StepStmt P (EvalCmd P) extendEval)
              (.stmt s ρ₀) (.terminal ρ₁))
      (h2 : ReflTransT (StepStmt P (EvalCmd P) extendEval)
              (.stmts rest ρ₁) (.exiting label ρ')),
      h1.len + h2.len < hstar.len) := by
  match hstar with
  | .step _ _ _ .step_stmts_cons hrest =>
    match seqT_reaches_exiting' hrest with
    | .inl ⟨hexit, hlen⟩ => exact .inl ⟨hexit, by simp [ReflTransT.len]; omega⟩
    | .inr ⟨ρ₁, h1, h2, hlen⟩ => exact .inr ⟨ρ₁, h1, h2, by simp [ReflTransT.len]; omega⟩









/-! ## The sum-typed (terminal-OR-exiting) two-guard driver.

The driver above (`loopDet_lift_2g*`) concludes only the TERMINAL loop outcome and
takes `h_src_body_no_exit`, ruling out a loop body that breaks (`.exit`).  This
section drops `h_src_body_no_exit` and adds the parallel EXITING outcome: a source
loop run that reaches `.exiting label ρ_post` (the loop terminated early because
some iteration's body broke) is matched by a hoist loop run that reaches
`.exiting label ρ_post_h`, with `HoistInv` / `hasFailure` / `B`-boundedness at the
projected (capped) exit stores.

The `body_sim` slot is replaced by the sum-typed `BodySimSum`: a body run that
TERMINATES is matched by a terminating hoist run (the existing terminal clause),
and a body run that EXITS with label `l` is matched by a hoist run that exits with
the SAME label `l`, re-establishing `HoistInv` at the body-exit stores.  The
enclosing loop's `.block .none` projection then caps both the source body-local
and the hoist target away, so `HoistInv` survives via `HoistInv.project_both` —
exactly the relation the §E mutual already carries on its `.exiting` disjunct.

This section is strictly ADDITIVE: the terminal-only driver and its `*_no_exit`
support lemmas are untouched, so existing call paths keep building unchanged. -/

/-- The sum-typed body simulation: a body run that TERMINATES is matched by a
terminating hoist run (the existing terminal clause), and a body run that EXITS
with label `l` is matched by a hoist run that exits with the SAME label `l`,
re-establishing `HoistInv` at the body-exit stores together with `hasFailure`
agreement and `B`-boundedness.  This is the predicate the sum-typed two-guard
driver's `body_sim` slot consumes. -/
public def BodySimSum [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendEval : ExtendEval P}
    (A B : List P.Ident) (subst : List (P.Ident × P.Ident))
    (bsrc bh : List (Stmt P (Cmd P))) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    HoistInv (P := P) A B subst ρ_s.store ρ_h.store →
    ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
    (∀ y ∈ B, ρ_h.store y ≠ none) →
    -- TERMINAL clause (the existing `BodySim`):
    (∀ (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendEval (.stmts bsrc ρ_s) (.terminal ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendEval (.stmts bh ρ_h) (.terminal ρ_h') ∧
        HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
        ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none))
    ∧
    -- EXITING clause (new):
    (∀ (l : String) (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendEval (.stmts bsrc ρ_s) (.exiting l ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendEval (.stmts bh ρ_h) (.exiting l ρ_h') ∧
        HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
        ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none))

/-- No-exit-free block-terminal inversion for a `.none`-labelled block: a `.none`
block can only reach `.terminal` via `step_block_done` from an inner `.terminal`
(an inner `.exiting` always MISMATCHES `.none` and propagates as `.exiting`, never
`.terminal`), so the inner body reached `.terminal ρ_inner` with the projected
store — WITHOUT any no-exit hypothesis.  The sum-typed driver's recursive
(terminal-iteration) case uses this to recover the body's terminal run for an
intermediate iteration without ruling out body exits in general. -/
public theorem blockT_none_reaches_terminal [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {inner : Config P (Cmd P)} {σ_parent : SemanticStore P} {ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval)
              (.block .none σ_parent inner) (.terminal ρ')) :
    ∃ (ρ_inner : Env P)
      (h : ReflTransT (StepStmt P (EvalCmd P) extendEval) inner (.terminal ρ_inner)),
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } ∧
      h.len < hstar.len := by
  match hstar with
  | .step _ (.block _ _ inner₁) _ (.step_block_body h) hrest =>
    have ⟨ρ_inner, hterm, heq, hlen⟩ := blockT_none_reaches_terminal hrest
    exact ⟨ρ_inner, .step _ _ _ h hterm, heq, by simp [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_block_done hrest =>
    match hrest with
    | .refl _ => exact ⟨_, .refl _, rfl, by simp [ReflTransT.len]⟩
    | .step _ _ _ h _ => exact nomatch h
  | .step _ _ _ (.step_block_exit_match heq) _ => exact (nomatch heq)
  | .step _ _ _ (.step_block_exit_mismatch _) hrest =>
    match hrest with
    | .step _ _ _ h _ => exact nomatch h

/-- **The sum-typed two-guard exiting-target fuel recursion.**

The EXITING analogue of `loopDet_lift_2g_fuel`.  Takes a sum-typed `body_sim`
(terminal AND exiting clauses) and, given a source loop run reaching `.exiting
label ρ_post`, produces a hoist loop run reaching `.exiting label ρ_post_h` with
`HoistInv` / `hasFailure` / `B`-boundedness at the exit stores.

Structure of the recursion (fuel `n` on the source run length):
* `step_loop_exit` cannot reach `.exiting` (it goes to `.terminal`) — discharged
  by inverting `hrest`.
* `step_loop_enter`: the body of THIS iteration runs in `.block .none`.  By
  `seqT_reaches_exiting'`:
  - **inl** (this iteration's block exits): `blockT_none_reaches_exiting'` gives a
    body run to `.exiting label ρ_inner` with `ρ_post = {ρ_inner with store :=
    projectStore ρ_src.store ρ_inner.store}`.  Feed the body's EXITING clause →
    hoist body exits → build the hoist loop's early exit (`step_loop_enter` then
    the `.none`-block mismatch + seq exit).
  - **inr** (this iteration's block terminates, then the recursive loop exits):
    `blockT_none_reaches_terminal` recovers the body's TERMINAL run (no no-exit
    needed); feed the body's TERMINAL clause, build one hoist iteration, and
    recurse via `ih` on the inner loop. -/
public theorem loopDet_lift_2g_E_fuel [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {g_s g_h : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    (h_guard_transport : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
       ρ_s.eval ρ_s.store g_s = .some HasBool.tt → ρ_h.eval ρ_h.store g_h = .some HasBool.tt)
    (h_wfb_transport : ∀ (ρ_s ρ_h : Env P),
       ρ_s.eval = ρ_h.eval → WellFormedSemanticEvalBool ρ_s.eval →
       WellFormedSemanticEvalBool ρ_h.eval)
    (body_sim : BodySimSum (extendEval := extendEval) A B subst body_src body_h)
    (h_src_body_nofd : Block.noFuncDecl body_src = true)
    (h_h_body_nofd : Block.noFuncDecl body_h = true) :
    ∀ (n : Nat) {ρ_src ρ_hoist ρ_post : Env P} {label : String},
      HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store →
      ρ_src.eval = ρ_hoist.eval → ρ_src.hasFailure = ρ_hoist.hasFailure →
      (∀ y ∈ B, ρ_hoist.store y ≠ none) →
      (h_run : ReflTransT (StepStmt P (EvalCmd P) extendEval)
        (.stmt (.loop (.det g_s) none [] body_src md_s) ρ_src) (.exiting label ρ_post)) →
      h_run.len ≤ n →
      ∃ ρ_post_h : Env P,
        StepStmtStar P (EvalCmd P) extendEval
          (.stmt (.loop (.det g_h) none [] body_h md_h) ρ_hoist) (.exiting label ρ_post_h) ∧
        HoistInv (P := P) A B subst ρ_post.store ρ_post_h.store ∧
        ρ_post.hasFailure = ρ_post_h.hasFailure ∧
        (∀ y ∈ B, ρ_post_h.store y ≠ none) := by
  intro n
  induction n with
  | zero =>
    intro ρ_src ρ_hoist ρ_post label _ _ _ _ h_run hlen
    match h_run with
    | .step _ _ _ _ _ => simp [ReflTransT.len] at hlen
  | succ n ih =>
    intro ρ_src ρ_hoist ρ_post label h_hinv h_eval h_hf h_bound h_run hlen
    match h_run with
    | .step _ _ _ step hrest =>
      cases step with
      | step_loop_exit ht hinv hiff hwf =>
        -- A `.terminal` target; `hrest : .terminal … →* .exiting …` is impossible.
        match hrest with
        | .step _ _ _ hd _ => exact nomatch hd
      | step_loop_enter ht hinv hiff hwf =>
        rename_i hasInvFailure
        have h_hif_false : hasInvFailure = false := by
          cases h_hif : hasInvFailure with
          | false => rfl
          | true => obtain ⟨le, hle_mem, _⟩ := hiff.mp h_hif; simp at hle_mem
        subst h_hif_false
        -- Common bodies, with the `|| false` collapse.
        let ρ_src_body : Env P := { ρ_src with hasFailure := ρ_src.hasFailure || false }
        let ρ_h_body : Env P := { ρ_hoist with hasFailure := ρ_hoist.hasFailure || false }
        have h_hinv_body : HoistInv (P := P) A B subst ρ_src_body.store ρ_h_body.store := by
          show HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store; exact h_hinv
        have h_eval_body : ρ_src_body.eval = ρ_h_body.eval := h_eval
        have h_hf_body : ρ_src_body.hasFailure = ρ_h_body.hasFailure := by
          show (ρ_src.hasFailure || false) = (ρ_hoist.hasFailure || false); simp [h_hf]
        have h_bound_body : ∀ y ∈ B, ρ_h_body.store y ≠ none := h_bound
        have h_guard_h : ρ_hoist.eval ρ_hoist.store g_h = .some HasBool.tt :=
          h_guard_transport ρ_src ρ_hoist h_hinv h_eval ht
        have h_wfb_h : WellFormedSemanticEvalBool ρ_hoist.eval :=
          h_wfb_transport ρ_src ρ_hoist h_eval hwf
        -- Decompose the seq run to `.exiting`: either this iteration's block exits
        -- (inl), or it terminates and the recursive loop exits (inr).
        rcases seqT_reaches_exiting' hrest with ⟨h_block_exit, hl⟩ | ⟨ρ₁, h_block_term, h_loop_stmts, hl⟩
        · -- inl: this iteration's body exits with `label`.
          obtain ⟨ρ_inner, h_body_exit_T, h_ρpost_eq, hl2⟩ := blockT_none_reaches_exiting' h_block_exit
          -- Feed the EXITING clause of the body simulation.
          obtain ⟨ρ_h_inner, h_body_h_exit, h_hinv_inner, h_hf_inner, h_bound_inner⟩ :=
            (body_sim ρ_src_body ρ_h_body h_hinv_body h_eval_body h_hf_body h_bound_body).2
              label ρ_inner (reflTransT_to_prop h_body_exit_T)
          -- Build the hoist loop's early exit:
          --   .stmt loop ρ_hoist
          --   → .seq (.block .none ρ_hoist.store (.stmts body_h ρ_h_body)) [loop]   (step_loop_enter)
          --   →* .seq (.block .none ρ_hoist.store (.exiting label ρ_h_inner)) [loop]  (body run)
          --   → .seq (.exiting label {ρ_h_inner with store := projectStore …}) [loop] (block mismatch)
          --   → .exiting label {ρ_h_inner with store := projectStore …}              (seq exit)
          refine ⟨{ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store }, ?_, ?_, ?_, ?_⟩
          · refine ReflTrans.step _ _ _
              (.step_loop_enter (hasInvFailure := false)
                h_guard_h (by intro le hle; simp at hle) (by simp) h_wfb_h) ?_
            -- Run the body inside the seq+block context to `.exiting`.
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendEval _ _ _
                (block_inner_star P (EvalCmd P) extendEval _ _ (none : Option String) ρ_hoist.store
                  (show StepStmtStar P (EvalCmd P) extendEval
                      (.stmts body_h { ρ_hoist with hasFailure := ρ_hoist.hasFailure || false })
                      (.exiting label ρ_h_inner) from h_body_h_exit))) ?_
            -- `.seq (.block .none ρ_hoist.store (.exiting label ρ_h_inner)) [loop]` exits.
            refine ReflTrans.step _ _ _ (.step_seq_inner (.step_block_exit_mismatch ?_)) ?_
            · exact (by simp)
            · exact ReflTrans.step _ _ _ .step_seq_exit (.refl _)
          · -- HoistInv at the projected exit stores: `HoistInv.project_both`.
            subst h_ρpost_eq
            exact HoistInv.project_both h_hinv h_hinv_inner
          · -- hasFailure agreement at the projected stores (store-only projection).
            subst h_ρpost_eq
            show ρ_inner.hasFailure = ρ_h_inner.hasFailure; exact h_hf_inner
          · -- `B`-boundedness survives the projection (parent binds `B`).
            intro y hy
            show projectStore ρ_hoist.store ρ_h_inner.store y ≠ none
            unfold projectStore
            have h_parent_some : (ρ_hoist.store y).isSome = true := by
              cases h : ρ_hoist.store y with
              | none => exact absurd h (h_bound y hy)
              | some _ => rfl
            rw [h_parent_some]; simp; exact h_bound_inner y hy
        · -- inr: this iteration's body terminates; recurse on the inner loop.
          obtain ⟨ρ_inner, h_body_term_T, h_ρ_block_eq, hl_blk⟩ := blockT_none_reaches_terminal h_block_term
          subst h_ρ_block_eq
          -- Feed the TERMINAL clause of the body simulation for this iteration.
          obtain ⟨ρ_h_inner, h_body_h_run, h_hinv_inner, h_hf_inner, h_bound_inner⟩ :=
            (body_sim ρ_src_body ρ_h_body h_hinv_body h_eval_body h_hf_body h_bound_body).1
              ρ_inner (reflTransT_to_prop h_body_term_T)
          -- Build one hoist iteration: loop → … → .stmts [loop_h] {ρ_h_inner with projected}.
          have h_hoist_iter : StepStmtStar P (EvalCmd P) extendEval
              (.stmt (.loop (.det g_h) none [] body_h md_h) ρ_hoist)
              (.stmts [.loop (.det g_h) none [] body_h md_h]
                { ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store }) := by
            have hb : StepStmtStar P (EvalCmd P) extendEval
                (.stmts body_h ρ_h_body) (.terminal ρ_h_inner) := h_body_h_run
            have := buildLoopIterationDet (g := g_h) (body := body_h) (md := md_h)
              (ρ_pre := ρ_h_body) (ρ_body := ρ_h_inner) ?_ ?_ hb
            · simpa [ρ_h_body] using this
            · show ρ_h_body.eval ρ_h_body.store g_h = .some HasBool.tt
              show ρ_hoist.eval ρ_hoist.store g_h = .some HasBool.tt; exact h_guard_h
            · show WellFormedSemanticEvalBool ρ_h_body.eval
              show WellFormedSemanticEvalBool ρ_hoist.eval; exact h_wfb_h
          -- The inner-loop entry stores are HoistInv-related (project_both) etc.
          have h_hinv_block : HoistInv (P := P) A B subst
              (projectStore ρ_src.store ρ_inner.store)
              (projectStore ρ_hoist.store ρ_h_inner.store) :=
            HoistInv.project_both h_hinv h_hinv_inner
          have h_eval_block : ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P).eval
              = ({ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store } : Env P).eval := by
            show ρ_inner.eval = ρ_h_inner.eval
            have e1 : ρ_inner.eval = ρ_src_body.eval :=
              smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
                body_src ρ_src_body ρ_inner h_src_body_nofd (reflTransT_to_prop h_body_term_T)
            have e2 : ρ_h_inner.eval = ρ_h_body.eval :=
              smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
                body_h ρ_h_body ρ_h_inner h_h_body_nofd h_body_h_run
            rw [e1, e2]; exact h_eval_body
          have h_hf_block : ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P).hasFailure
              = ({ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store } : Env P).hasFailure := by
            show ρ_inner.hasFailure = ρ_h_inner.hasFailure; exact h_hf_inner
          have h_bound_block : ∀ y ∈ B,
              ({ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store } : Env P).store y ≠ none := by
            intro y hy
            show projectStore ρ_hoist.store ρ_h_inner.store y ≠ none
            unfold projectStore
            have h_parent_some : (ρ_hoist.store y).isSome = true := by
              cases h : ρ_hoist.store y with
              | none => exact absurd h (h_bound y hy)
              | some _ => rfl
            rw [h_parent_some]; simp; exact h_bound_inner y hy
          -- The residual after the terminal block is `.stmts [loop_s] ρ_inner_proj`
          -- reaching `.exiting`.  Recover the inner-loop run via stmtsT_cons_exiting'.
          rcases stmtsT_cons_exiting' h_loop_stmts with ⟨h_inner_loop_T, _⟩ | ⟨ρ₂, _, h_nil, _⟩
          · -- The single loop statement (the recursive loop) reaches `.exiting`; recurse.
            obtain ⟨ρ_post_h, h_post_h_run, h_hinv_post, h_hf_post, h_bound_post⟩ :=
              ih h_hinv_block h_eval_block h_hf_block h_bound_block h_inner_loop_T
                (by simp only [ReflTransT.len] at hlen; omega)
            refine ⟨ρ_post_h, ?_, h_hinv_post, h_hf_post, h_bound_post⟩
            -- Splice: one hoist iteration, then the recursive hoist loop's exit.
            refine ReflTrans_Transitive _ _ _ _ h_hoist_iter ?_
            refine ReflTrans.step _ _ _ .step_stmts_cons ?_
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendEval _ _ _ h_post_h_run) ?_
            exact ReflTrans.step _ _ _ .step_seq_exit (.refl _)
          · -- tail is `[]`, cannot reach `.exiting`.
            match h_nil with
            | .step _ _ _ .step_stmts_nil hr2 =>
              match hr2 with
              | .step _ _ _ hd _ => exact nomatch hd

/-- Prop-level wrapper of `loopDet_lift_2g_E_fuel`: the sum-typed exiting-target
two-guard driver.  Given a source loop run reaching `.exiting label ρ_post`,
produces the matching hoist loop run reaching `.exiting label ρ_post_h`. -/
public theorem loopDet_lift_2g_E [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {g_s g_h : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    (h_guard_transport : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
       ρ_s.eval ρ_s.store g_s = .some HasBool.tt → ρ_h.eval ρ_h.store g_h = .some HasBool.tt)
    (h_wfb_transport : ∀ (ρ_s ρ_h : Env P),
       ρ_s.eval = ρ_h.eval → WellFormedSemanticEvalBool ρ_s.eval →
       WellFormedSemanticEvalBool ρ_h.eval)
    (body_sim : BodySimSum (extendEval := extendEval) A B subst body_src body_h)
    (h_src_body_nofd : Block.noFuncDecl body_src = true)
    (h_h_body_nofd : Block.noFuncDecl body_h = true)
    {ρ_src ρ_hoist ρ_post : Env P} {label : String}
    (h_hinv : HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store)
    (h_eval : ρ_src.eval = ρ_hoist.eval) (h_hf : ρ_src.hasFailure = ρ_hoist.hasFailure)
    (h_bound : ∀ y ∈ B, ρ_hoist.store y ≠ none)
    (h_run : StepStmtStar P (EvalCmd P) extendEval
        (.stmt (.loop (.det g_s) none [] body_src md_s) ρ_src) (.exiting label ρ_post)) :
    ∃ ρ_post_h : Env P,
      StepStmtStar P (EvalCmd P) extendEval
        (.stmt (.loop (.det g_h) none [] body_h md_h) ρ_hoist) (.exiting label ρ_post_h) ∧
      HoistInv (P := P) A B subst ρ_post.store ρ_post_h.store ∧
      ρ_post.hasFailure = ρ_post_h.hasFailure ∧
      (∀ y ∈ B, ρ_post_h.store y ≠ none) :=
  loopDet_lift_2g_E_fuel h_guard_transport h_wfb_transport body_sim h_src_body_nofd h_h_body_nofd
    (reflTrans_to_T h_run).len h_hinv h_eval h_hf h_bound (reflTrans_to_T h_run) (Nat.le_refl _)

/-- **`loopDet_preserves_none` for an EXITING loop run — WITHOUT a no-exit
hypothesis.**

A loop run reaching `.exiting label ρ_post` keeps any variable `x` undefined at
the exit store provided it was undefined at loop entry.  No `h_body_no_exit` is
needed: a `.none`-block iteration projects (`projectStore`) every entry undefined
at iteration entry back to `none`, so the entry-undefinedness of `x` is an
invariant across iterations, and the FINAL (exiting) iteration's `.block .none`
mismatch caps the body-exit store via the same `projectStore` (so `x` stays
`none` at the projected exit env).  Mirrors `loopDet_lift_2g_E_fuel`'s exit-run
inversion, tracking a single `x`'s undefinedness instead of the simulation. -/
public theorem loopDet_preserves_none_exiting_fuel [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {g : P.Expr} {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {x : P.Ident} :
    ∀ (n : Nat) {ρ ρ_post : Env P} {label : String},
      ρ.store x = none →
      (h_run : ReflTransT (StepStmt P (EvalCmd P) extendEval)
        (.stmt (.loop (.det g) none [] body md) ρ) (.exiting label ρ_post)) →
      h_run.len ≤ n →
      ρ_post.store x = none := by
  intro n
  induction n with
  | zero =>
    intro ρ ρ_post label _ h_run hlen
    match h_run with
    | .step _ _ _ _ _ => simp [ReflTransT.len] at hlen
  | succ n ih =>
    intro ρ ρ_post label h_none h_run hlen
    match h_run with
    | .step _ _ _ step hrest =>
      cases step with
      | step_loop_exit ht hinv hiff hwf =>
        match hrest with
        | .step _ _ _ hd _ => exact nomatch hd
      | step_loop_enter ht hinv hiff hwf =>
        rename_i hasInvFailure
        have h_hif_false : hasInvFailure = false := by
          cases h_hif : hasInvFailure with
          | false => rfl
          | true => obtain ⟨le, hle_mem, _⟩ := hiff.mp h_hif; simp at hle_mem
        subst h_hif_false
        rcases seqT_reaches_exiting' hrest with ⟨h_block_exit, _⟩ | ⟨ρ₁, h_block_term, h_loop_stmts, _⟩
        · -- inl: this iteration's body exits; `ρ_post` is the projected exit store.
          obtain ⟨ρ_inner, _, h_ρpost_eq, _⟩ := blockT_none_reaches_exiting' h_block_exit
          subst h_ρpost_eq
          show projectStore ρ.store ρ_inner.store x = none
          exact projectStore_undef_at h_none
        · -- inr: this iteration's body terminates; recurse on the inner loop.
          obtain ⟨ρ_inner, _, h_ρ_block_eq, _⟩ := blockT_none_reaches_terminal h_block_term
          subst h_ρ_block_eq
          have h_none_inner :
              ({ ρ_inner with store := projectStore ρ.store ρ_inner.store } : Env P).store x = none := by
            show projectStore ρ.store ρ_inner.store x = none
            exact projectStore_undef_at h_none
          rcases stmtsT_cons_exiting' h_loop_stmts with ⟨h_inner_loop_T, _⟩ | ⟨ρ₂, _, h_nil, _⟩
          · exact ih h_none_inner h_inner_loop_T (by simp only [ReflTransT.len] at hlen; omega)
          · match h_nil with
            | .step _ _ _ .step_stmts_nil hr2 =>
              match hr2 with
              | .step _ _ _ hd _ => exact nomatch hd

/-- Prop-level corollary of `loopDet_preserves_none_exiting_fuel`. -/
public theorem loopDet_preserves_none_exiting [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {g : P.Expr} {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {x : P.Ident} {ρ ρ_post : Env P} {label : String}
    (h_none : ρ.store x = none)
    (h_run : StepStmtStar P (EvalCmd P) extendEval
      (.stmt (.loop (.det g) none [] body md) ρ) (.exiting label ρ_post)) :
    ρ_post.store x = none :=
  loopDet_preserves_none_exiting_fuel (reflTrans_to_T h_run).len h_none
    (reflTrans_to_T h_run) (Nat.le_refl _)

/-- **`loopDet_preserves_none` for a TERMINAL loop run — WITHOUT a no-exit
hypothesis.**

The TERMINAL analogue of `loopDet_preserves_none_exiting_fuel`: like
`loopDet_preserves_none_fuel` but DROPS `h_body_no_exit`.  A loop run reaching
`.terminal ρ_post` keeps any variable `x` undefined at the exit store provided it
was undefined at loop entry.  No `h_body_no_exit` is needed: the loop terminates
either by failing the guard (`step_loop_exit`, store unchanged at `x`) or by
running an iteration whose `.none`-block reaches `.terminal`
(`blockT_none_reaches_terminal`, an inner `.exiting` always mismatches `.none` and
propagates, so a `.none`-block reaching `.terminal` forces an inner `.terminal`);
each iteration projects (`projectStore`) every entry undefined at iteration entry
back to `none`, so the entry-undefinedness of `x` is an invariant across
iterations.  Mirrors `loopDet_preserves_none_exiting_fuel`'s inversion, with the
`.terminal` target instead of `.exiting`. -/
public theorem loopDet_preserves_none_terminal_fuel [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {g : P.Expr} {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {x : P.Ident} :
    ∀ (n : Nat) {ρ ρ_post : Env P},
      ρ.store x = none →
      (h_run : ReflTransT (StepStmt P (EvalCmd P) extendEval)
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
      | step_loop_exit ht hinv hiff hwf =>
        rename_i hasInvFailure
        have h_ρ_post_eq : ρ_post = { ρ with hasFailure := ρ.hasFailure || hasInvFailure } := by
          match hrest with
          | .refl _ => rfl
          | .step _ _ _ hd _ => exact nomatch hd
        subst h_ρ_post_eq
        exact h_none
      | step_loop_enter ht hinv hiff hwf =>
        rename_i hasInvFailure
        have h_hif_false : hasInvFailure = false := by
          cases h_hif : hasInvFailure with
          | false => rfl
          | true => obtain ⟨le, hle_mem, _⟩ := hiff.mp h_hif; simp at hle_mem
        subst h_hif_false
        -- Peel one iteration WITHOUT a no-exit hypothesis: the seq decomposes to a
        -- `.block .none` reaching `.terminal`, which forces an inner `.terminal`.
        obtain ⟨ρ_block, h_block_term, h_loop_stmts, _⟩ :=
          seqT_reaches_terminal extendEval hrest
        obtain ⟨ρ_inner, _, h_ρ_block_eq, _⟩ := blockT_none_reaches_terminal h_block_term
        subst h_ρ_block_eq
        obtain ⟨ρ_x, h_loop_T, h_nil, _⟩ :=
          stmtsT_cons_terminal extendEval h_loop_stmts
        have hρ_x_eq : ρ_x = ρ_post := by
          match h_nil with
          | .step _ _ _ .step_stmts_nil hr2 =>
            match hr2 with
            | .refl _ => rfl
            | .step _ _ _ h _ => exact nomatch h
        subst hρ_x_eq
        have h_none_inner :
            ({ ρ_inner with store := projectStore ρ.store ρ_inner.store } : Env P).store x = none := by
          show projectStore ρ.store ρ_inner.store x = none
          exact projectStore_undef_at h_none
        exact ih h_none_inner h_loop_T (by simp only [ReflTransT.len] at hlen; omega)

/-- Prop-level corollary of `loopDet_preserves_none_terminal_fuel`. -/
public theorem loopDet_preserves_none_terminal [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {g : P.Expr} {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {x : P.Ident} {ρ ρ_post : Env P}
    (h_none : ρ.store x = none)
    (h_run : StepStmtStar P (EvalCmd P) extendEval
      (.stmt (.loop (.det g) none [] body md) ρ) (.terminal ρ_post)) :
    ρ_post.store x = none :=
  loopDet_preserves_none_terminal_fuel (reflTrans_to_T h_run).len h_none
    (reflTrans_to_T h_run) (Nat.le_refl _)

/-- **The sum-typed two-guard TERMINAL-target fuel recursion.**

The TERMINAL analogue of `loopDet_lift_2g_E_fuel`: like `loopDet_lift_2g_fuel`
but DROPS `h_src_body_no_exit` and consumes a sum-typed `body_sim` (`BodySimSum`).
A source loop run reaching `.terminal ρ_post` means NO iteration's body broke (a
body `.exit` would propagate the loop to `.exiting`, not `.terminal`); so each
peeled iteration's `.block .none` reaches `.terminal` via `blockT_none_reaches_terminal`
(which recovers the body's TERMINAL run WITHOUT a no-exit hypothesis — an inner
`.exiting` always mismatches `.none` and propagates, so a `.none`-block reaching
`.terminal` forces an inner `.terminal`).  The body's TERMINAL clause then drives
one hoist iteration, and the recursion (`ih`) handles the residual loop. -/
public theorem loopDet_lift_2g_TE_fuel [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {g_s g_h : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    (h_guard_transport : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
       ρ_s.eval ρ_s.store g_s = .some HasBool.tt → ρ_h.eval ρ_h.store g_h = .some HasBool.tt)
    (h_guard_transport_ff : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
       ρ_s.eval ρ_s.store g_s = .some HasBool.ff → ρ_h.eval ρ_h.store g_h = .some HasBool.ff)
    (h_wfb_transport : ∀ (ρ_s ρ_h : Env P),
       ρ_s.eval = ρ_h.eval → WellFormedSemanticEvalBool ρ_s.eval →
       WellFormedSemanticEvalBool ρ_h.eval)
    (body_sim : BodySimSum (extendEval := extendEval) A B subst body_src body_h)
    (h_src_body_nofd : Block.noFuncDecl body_src = true)
    (h_h_body_nofd : Block.noFuncDecl body_h = true) :
    ∀ (n : Nat) {ρ_src ρ_hoist ρ_post : Env P},
      HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store →
      ρ_src.eval = ρ_hoist.eval → ρ_src.hasFailure = ρ_hoist.hasFailure →
      (∀ y ∈ B, ρ_hoist.store y ≠ none) →
      (h_run : ReflTransT (StepStmt P (EvalCmd P) extendEval)
        (.stmt (.loop (.det g_s) none [] body_src md_s) ρ_src) (.terminal ρ_post)) →
      h_run.len ≤ n →
      ∃ ρ_post_h : Env P,
        StepStmtStar P (EvalCmd P) extendEval
          (.stmt (.loop (.det g_h) none [] body_h md_h) ρ_hoist) (.terminal ρ_post_h) ∧
        HoistInv (P := P) A B subst ρ_post.store ρ_post_h.store ∧
        ρ_post.hasFailure = ρ_post_h.hasFailure ∧
        (∀ y ∈ B, ρ_post_h.store y ≠ none) := by
  intro n
  induction n with
  | zero =>
    intro ρ_src ρ_hoist ρ_post _ _ _ _ h_run hlen
    match h_run with
    | .step _ _ _ _ _ => simp [ReflTransT.len] at hlen
  | succ n ih =>
    intro ρ_src ρ_hoist ρ_post h_hinv h_eval h_hf h_bound h_run hlen
    match h_run with
    | .step _ _ _ step hrest =>
      cases step with
      | step_loop_exit ht hinv hiff hwf =>
        rename_i hasInvFailure
        have h_hif_false : hasInvFailure = false := by
          cases h_hif : hasInvFailure with
          | false => rfl
          | true => obtain ⟨le, hle_mem, _⟩ := hiff.mp h_hif; simp at hle_mem
        have h_ρ_post_eq : ρ_post = { ρ_src with hasFailure := ρ_src.hasFailure || hasInvFailure } := by
          match hrest with
          | .refl _ => rfl
          | .step _ _ _ hd _ => exact nomatch hd
        subst h_ρ_post_eq
        subst h_hif_false
        have h_guard_h : ρ_hoist.eval ρ_hoist.store g_h = .some HasBool.ff :=
          h_guard_transport_ff ρ_src ρ_hoist h_hinv h_eval ht
        have h_wfb_h : WellFormedSemanticEvalBool ρ_hoist.eval :=
          h_wfb_transport ρ_src ρ_hoist h_eval hwf
        refine ⟨{ ρ_hoist with hasFailure := ρ_hoist.hasFailure || false }, ?_, ?_, ?_, ?_⟩
        · exact .step _ _ _
            (.step_loop_exit h_guard_h (by intro le hle; simp at hle) (by simp) h_wfb_h)
            (.refl _)
        · simpa using h_hinv
        · show (ρ_src.hasFailure || false) = (ρ_hoist.hasFailure || false); simp [h_hf]
        · intro y hy; show ρ_hoist.store y ≠ none; exact h_bound y hy
      | step_loop_enter ht hinv hiff hwf =>
        rename_i hasInvFailure
        have h_hif_false : hasInvFailure = false := by
          cases h_hif : hasInvFailure with
          | false => rfl
          | true => obtain ⟨le, hle_mem, _⟩ := hiff.mp h_hif; simp at hle_mem
        subst h_hif_false
        -- Peel one iteration WITHOUT a no-exit hypothesis: the seq decomposes to a
        -- `.block .none` reaching `.terminal`, which forces an inner `.terminal`.
        obtain ⟨ρ_block, h_block_term, h_loop_stmts, hlen_seq⟩ :=
          seqT_reaches_terminal extendEval hrest
        obtain ⟨ρ_inner, h_body_src_T, h_ρ_block_eq, hlen_block⟩ :=
          blockT_none_reaches_terminal h_block_term
        subst h_ρ_block_eq
        obtain ⟨ρ_x, h_loop_T, h_nil, hlen_cons⟩ :=
          stmtsT_cons_terminal extendEval h_loop_stmts
        have hρ_x_eq : ρ_x = ρ_post := by
          match h_nil with
          | .step _ _ _ .step_stmts_nil hr2 =>
            match hr2 with
            | .refl _ => rfl
            | .step _ _ _ h _ => exact nomatch h
        subst hρ_x_eq
        let ρ_src_body : Env P := { ρ_src with hasFailure := ρ_src.hasFailure || false }
        let ρ_h_body : Env P := { ρ_hoist with hasFailure := ρ_hoist.hasFailure || false }
        have h_hinv_body : HoistInv (P := P) A B subst ρ_src_body.store ρ_h_body.store := by
          show HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store; exact h_hinv
        have h_eval_body : ρ_src_body.eval = ρ_h_body.eval := h_eval
        have h_hf_body : ρ_src_body.hasFailure = ρ_h_body.hasFailure := by
          show (ρ_src.hasFailure || false) = (ρ_hoist.hasFailure || false); simp [h_hf]
        have h_bound_body : ∀ y ∈ B, ρ_h_body.store y ≠ none := h_bound
        obtain ⟨ρ_h_inner, h_body_h_run, h_hinv_inner, h_hf_inner, h_bound_inner⟩ :=
          (body_sim ρ_src_body ρ_h_body h_hinv_body h_eval_body h_hf_body h_bound_body).1
            ρ_inner (reflTransT_to_prop h_body_src_T)
        have h_guard_h : ρ_hoist.eval ρ_hoist.store g_h = .some HasBool.tt :=
          h_guard_transport ρ_src ρ_hoist h_hinv h_eval ht
        have h_wfb_h : WellFormedSemanticEvalBool ρ_hoist.eval :=
          h_wfb_transport ρ_src ρ_hoist h_eval hwf
        have h_hoist_iter : StepStmtStar P (EvalCmd P) extendEval
            (.stmt (.loop (.det g_h) none [] body_h md_h) ρ_hoist)
            (.stmts [.loop (.det g_h) none [] body_h md_h]
              { ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store }) := by
          have hb : StepStmtStar P (EvalCmd P) extendEval
              (.stmts body_h ρ_h_body) (.terminal ρ_h_inner) := h_body_h_run
          have := buildLoopIterationDet (g := g_h) (body := body_h) (md := md_h)
            (ρ_pre := ρ_h_body) (ρ_body := ρ_h_inner) ?_ ?_ hb
          · simpa [ρ_h_body] using this
          · show ρ_h_body.eval ρ_h_body.store g_h = .some HasBool.tt
            show ρ_hoist.eval ρ_hoist.store g_h = .some HasBool.tt; exact h_guard_h
          · show WellFormedSemanticEvalBool ρ_h_body.eval
            show WellFormedSemanticEvalBool ρ_hoist.eval; exact h_wfb_h
        have h_hinv_block : HoistInv (P := P) A B subst
            (projectStore ρ_src.store ρ_inner.store)
            (projectStore ρ_hoist.store ρ_h_inner.store) :=
          HoistInv.project_both h_hinv h_hinv_inner
        have h_eval_block : ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P).eval
            = ({ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store } : Env P).eval := by
          show ρ_inner.eval = ρ_h_inner.eval
          have e1 : ρ_inner.eval = ρ_src_body.eval :=
            smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
              body_src ρ_src_body ρ_inner h_src_body_nofd (reflTransT_to_prop h_body_src_T)
          have e2 : ρ_h_inner.eval = ρ_h_body.eval :=
            smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
              body_h ρ_h_body ρ_h_inner h_h_body_nofd h_body_h_run
          rw [e1, e2]; exact h_eval_body
        have h_hf_block : ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P).hasFailure
            = ({ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store } : Env P).hasFailure := by
          show ρ_inner.hasFailure = ρ_h_inner.hasFailure; exact h_hf_inner
        have h_bound_block : ∀ y ∈ B,
            ({ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store } : Env P).store y ≠ none := by
          intro y hy
          show projectStore ρ_hoist.store ρ_h_inner.store y ≠ none
          unfold projectStore
          have h_parent_some : (ρ_hoist.store y).isSome = true := by
            cases h : ρ_hoist.store y with
            | none => exact absurd h (h_bound y hy)
            | some _ => rfl
          rw [h_parent_some]; simp; exact h_bound_inner y hy
        obtain ⟨ρ_post_h, h_post_h_run, h_hinv_post, h_hf_post, h_bound_post⟩ :=
          ih h_hinv_block h_eval_block h_hf_block h_bound_block h_loop_T
            (by simp only [ReflTransT.len] at hlen; omega)
        refine ⟨ρ_post_h, ?_, h_hinv_post, h_hf_post, h_bound_post⟩
        refine ReflTrans_Transitive _ _ _ _ h_hoist_iter ?_
        refine ReflTrans.step _ _ _ .step_stmts_cons ?_
        refine ReflTrans_Transitive _ _ _ _
          (seq_inner_star P (EvalCmd P) extendEval _ _ _ h_post_h_run) ?_
        exact ReflTrans.step _ _ _ .step_seq_done
          (ReflTrans.step _ _ _ .step_stmts_nil (.refl _))

/-- Prop-level wrapper of `loopDet_lift_2g_TE_fuel`: the sum-typed two-guard
TERMINAL-target driver (consumes a `BodySimSum` body sim, concludes `.terminal`,
no `h_src_body_no_exit`). -/
public theorem loopDet_lift_2g_TE [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {g_s g_h : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    (h_guard_transport : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
       ρ_s.eval ρ_s.store g_s = .some HasBool.tt → ρ_h.eval ρ_h.store g_h = .some HasBool.tt)
    (h_guard_transport_ff : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
       ρ_s.eval ρ_s.store g_s = .some HasBool.ff → ρ_h.eval ρ_h.store g_h = .some HasBool.ff)
    (h_wfb_transport : ∀ (ρ_s ρ_h : Env P),
       ρ_s.eval = ρ_h.eval → WellFormedSemanticEvalBool ρ_s.eval →
       WellFormedSemanticEvalBool ρ_h.eval)
    (body_sim : BodySimSum (extendEval := extendEval) A B subst body_src body_h)
    (h_src_body_nofd : Block.noFuncDecl body_src = true)
    (h_h_body_nofd : Block.noFuncDecl body_h = true)
    {ρ_src ρ_hoist ρ_post : Env P}
    (h_hinv : HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store)
    (h_eval : ρ_src.eval = ρ_hoist.eval) (h_hf : ρ_src.hasFailure = ρ_hoist.hasFailure)
    (h_bound : ∀ y ∈ B, ρ_hoist.store y ≠ none)
    (h_run : StepStmtStar P (EvalCmd P) extendEval
        (.stmt (.loop (.det g_s) none [] body_src md_s) ρ_src) (.terminal ρ_post)) :
    ∃ ρ_post_h : Env P,
      StepStmtStar P (EvalCmd P) extendEval
        (.stmt (.loop (.det g_h) none [] body_h md_h) ρ_hoist) (.terminal ρ_post_h) ∧
      HoistInv (P := P) A B subst ρ_post.store ρ_post_h.store ∧
      ρ_post.hasFailure = ρ_post_h.hasFailure ∧
      (∀ y ∈ B, ρ_post_h.store y ≠ none) :=
  loopDet_lift_2g_TE_fuel h_guard_transport h_guard_transport_ff h_wfb_transport
    body_sim h_src_body_nofd h_h_body_nofd
    (reflTrans_to_T h_run).len h_hinv h_eval h_hf h_bound (reflTrans_to_T h_run) (Nat.le_refl _)





/-! ## Guard-transport companion — discharges the renamed-guard seam.

Under `HoistInv` and guard-freshness, the source guard `g` on the source store
evaluates exactly as its renamed image `substFvarMany g subst` on the hoist
store (both via the SAME evaluator `δ`).  Every read var of `g` lies outside the
rename sources/targets, so the frame component of `HoistInv` closes it. -/
public theorem renamed_guard_eval_same_delta [HasFvar P] [HasSubstFvar P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {δ : SemanticEval P}
    {g : P.Expr} {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {σ_s σ_h : SemanticStore P}
    (h_A_subst_fst : ∀ a ∈ A, a ∈ subst.map Prod.fst)
    (h_src_nodup : (subst.map Prod.fst).Nodup)
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd)
    (h_tgt_nodup : (subst.map Prod.snd).Nodup)
    (h_g_B_fresh : ∀ x ∈ B, x ∉ HasVarsPure.getVars g)
    (h_hinv : HoistInv (P := P) A B subst σ_s σ_h)
    (h_read_def : ∀ x ∈ HasVarsPure.getVars g, σ_s x ≠ none)
    (h_wfcongr : WellFormedSemanticEvalExprCongr δ)
    (h_wfsubst : WellFormedSemanticEvalSubstFvar δ) :
    δ σ_s g = δ σ_h (substFvarMany g subst) := by
  classical
  have h_congr : δ σ_s g = δ (fun x => σ_h (renameLookup subst x)) g := by
    apply h_wfcongr g σ_s (fun x => σ_h (renameLookup subst x))
    intro x hx
    -- A read var `x` is either a rename SOURCE (in `subst.fst`) — handled by the
    -- guarded pairing (read ⇒ defined ⇒ the pairing antecedent holds) — or it is
    -- outside the rename and `A`/`B`-frame, handled by the guarded frame.  No
    -- source-freshness of `g` is needed: a guard var that IS a rename source is
    -- exactly what the guarded pairing closes.
    by_cases hx_src : x ∈ subst.map Prod.fst
    · obtain ⟨⟨a, b⟩, hb_pair, hxa⟩ := List.mem_map.mp hx_src
      simp only at hxa
      subst a
      rw [renameLookup_mem subst h_src_nodup hb_pair]
      exact (h_hinv.2 x b hb_pair (h_read_def x hx)).2
    · have hx_notin_A : x ∉ A := fun hA => hx_src (h_A_subst_fst x hA)
      have hx_notin_B : x ∉ B := fun hB => h_g_B_fresh x hB hx
      rw [renameLookup_notin subst x hx_src]
      -- Guarded frame: read var `x` is defined in `σ_s` by `h_read_def`.
      exact h_hinv.1 x hx_notin_A hx_notin_B (h_read_def x hx)
  rw [h_congr]
  exact substFvarMany_eval_tweak δ subst h_src_nodup h_disjoint h_tgt_nodup h_wfsubst


/-- The SUM-TYPED (exiting-target) renamed-guard driver: the exiting analogue of
`loopDet_lift_renamedGuard`, a thin wrapper over the sum-typed exiting driver
`loopDet_lift_2g_E` (the renamed-guard discharge of the guard-tt transport is
identical; the exit path never takes the false-guard branch, so no ff-transport is
needed).  Consumes a sum-typed `BodySimSum` (the inner loop body may break) and a
source loop run reaching `.exiting label ρ_post`, producing the matching hoist
(renamed-guard) loop run reaching `.exiting label ρ_post_h`. -/
public theorem loopDet_lift_renamedGuard_E [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {g : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    (h_A_subst_fst : ∀ a ∈ A, a ∈ subst.map Prod.fst)
    (h_src_nodup : (subst.map Prod.fst).Nodup)
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd)
    (h_tgt_nodup : (subst.map Prod.snd).Nodup)
    (h_g_B_fresh : ∀ x ∈ B, x ∉ HasVarsPure.getVars g)
    (_h_wfvar   : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval)
    (h_wfcongr : ∀ ρ : Env P, WellFormedSemanticEvalExprCongr ρ.eval)
    (h_wfsubst : ∀ ρ : Env P, WellFormedSemanticEvalSubstFvar ρ.eval)
    (h_wfdef   : ∀ ρ : Env P, WellFormedSemanticEvalDef ρ.eval)
    (body_sim : BodySimSum (extendEval := extendEval) A B subst body_src body_h)
    (h_src_body_nofd : Block.noFuncDecl body_src = true)
    (h_h_body_nofd : Block.noFuncDecl body_h = true)
    {ρ_src ρ_hoist ρ_post : Env P} {label : String}
    (h_hinv : HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store)
    (h_eval : ρ_src.eval = ρ_hoist.eval) (h_hf : ρ_src.hasFailure = ρ_hoist.hasFailure)
    (h_bound : ∀ y ∈ B, ρ_hoist.store y ≠ none)
    (h_run : StepStmtStar P (EvalCmd P) extendEval
        (.stmt (.loop (.det g) none [] body_src md_s) ρ_src) (.exiting label ρ_post)) :
    ∃ ρ_post_h : Env P,
      StepStmtStar P (EvalCmd P) extendEval
        (.stmt (.loop (.det (substFvarMany g subst)) none [] body_h md_h) ρ_hoist)
        (.exiting label ρ_post_h) ∧
      HoistInv (P := P) A B subst ρ_post.store ρ_post_h.store ∧
      ρ_post.hasFailure = ρ_post_h.hasFailure ∧
      (∀ y ∈ B, ρ_post_h.store y ≠ none) := by
  refine loopDet_lift_2g_E (g_s := g) (g_h := substFvarMany g subst)
    ?_ ?_ body_sim h_src_body_nofd h_h_body_nofd
    h_hinv h_eval h_hf h_bound h_run
  · intro ρ_s ρ_h hi he ht
    have h := renamed_guard_eval_same_delta (δ := ρ_h.eval) (g := g)
      h_A_subst_fst h_src_nodup h_disjoint h_tgt_nodup h_g_B_fresh
      hi (read_vars_def_of_eval (h_wfdef ρ_h) (he ▸ ht)) (h_wfcongr ρ_h) (h_wfsubst ρ_h)
    rw [← h, ← he]; exact ht
  · intro ρ_s ρ_h he hwfb; exact he ▸ hwfb

/-- The renamed-guard TERMINAL-target sum-typed driver: a thin wrapper over
`loopDet_lift_2g_TE` discharging the renamed-guard transport (the terminal companion
of `loopDet_lift_renamedGuard_E`).  Consumes a sum-typed `BodySimSum` (the inner
loop body may break) but a source loop run reaching `.terminal`. -/
public theorem loopDet_lift_renamedGuard_TE [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {g : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    (h_A_subst_fst : ∀ a ∈ A, a ∈ subst.map Prod.fst)
    (h_src_nodup : (subst.map Prod.fst).Nodup)
    (h_disjoint : ∀ a ∈ subst.map Prod.fst, a ∉ subst.map Prod.snd)
    (h_tgt_nodup : (subst.map Prod.snd).Nodup)
    (h_g_B_fresh : ∀ x ∈ B, x ∉ HasVarsPure.getVars g)
    (_h_wfvar   : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval)
    (h_wfcongr : ∀ ρ : Env P, WellFormedSemanticEvalExprCongr ρ.eval)
    (h_wfsubst : ∀ ρ : Env P, WellFormedSemanticEvalSubstFvar ρ.eval)
    (h_wfdef   : ∀ ρ : Env P, WellFormedSemanticEvalDef ρ.eval)
    (body_sim : BodySimSum (extendEval := extendEval) A B subst body_src body_h)
    (h_src_body_nofd : Block.noFuncDecl body_src = true)
    (h_h_body_nofd : Block.noFuncDecl body_h = true)
    {ρ_src ρ_hoist ρ_post : Env P}
    (h_hinv : HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store)
    (h_eval : ρ_src.eval = ρ_hoist.eval) (h_hf : ρ_src.hasFailure = ρ_hoist.hasFailure)
    (h_bound : ∀ y ∈ B, ρ_hoist.store y ≠ none)
    (h_run : StepStmtStar P (EvalCmd P) extendEval
        (.stmt (.loop (.det g) none [] body_src md_s) ρ_src) (.terminal ρ_post)) :
    ∃ ρ_post_h : Env P,
      StepStmtStar P (EvalCmd P) extendEval
        (.stmt (.loop (.det (substFvarMany g subst)) none [] body_h md_h) ρ_hoist)
        (.terminal ρ_post_h) ∧
      HoistInv (P := P) A B subst ρ_post.store ρ_post_h.store ∧
      ρ_post.hasFailure = ρ_post_h.hasFailure ∧
      (∀ y ∈ B, ρ_post_h.store y ≠ none) := by
  refine loopDet_lift_2g_TE (g_s := g) (g_h := substFvarMany g subst)
    ?_ ?_ ?_ body_sim h_src_body_nofd h_h_body_nofd
    h_hinv h_eval h_hf h_bound h_run
  · intro ρ_s ρ_h hi he ht
    have h := renamed_guard_eval_same_delta (δ := ρ_h.eval) (g := g)
      h_A_subst_fst h_src_nodup h_disjoint h_tgt_nodup h_g_B_fresh
      hi (read_vars_def_of_eval (h_wfdef ρ_h) (he ▸ ht)) (h_wfcongr ρ_h) (h_wfsubst ρ_h)
    rw [← h, ← he]; exact ht
  · intro ρ_s ρ_h hi he hf
    have h := renamed_guard_eval_same_delta (δ := ρ_h.eval) (g := g)
      h_A_subst_fst h_src_nodup h_disjoint h_tgt_nodup h_g_B_fresh
      hi (read_vars_def_of_eval (h_wfdef ρ_h) (he ▸ hf)) (h_wfcongr ρ_h) (h_wfsubst ρ_h)
    rw [← h, ← he]; exact hf
  · intro ρ_s ρ_h he hwfb; exact he ▸ hwfb

/-! ## Entries-from-lift structural bridge.

`Entry P = P.Ident × P.Ident × P.Ty × MetaData P`, `e = (y, y', ty, md)`:
* `y  = e.1`        — source body-local being renamed;
* `y' = e.2.1`      — fresh hoist target;
* `ty = e.2.2.1`    — init type carried into the havoc;
* `md = e.2.2.2`    — the original init's metadata carried into the havoc.

The lift's `.cmd (.init y ty rhs md)` arm emits a havoc `.init y' ty .nondet md`
carrying the original init's `md` (and `ty`), so each entry stores its own
`(ty, md)`. -/

@[expose] abbrev Entry (P : PureExpr) := P.Ident × P.Ident × P.Ty × MetaData P

/-- Per-entry-metadata havoc statements: each entry yields its own `md`. -/
@[expose] def havocStmts' (entries : List (Entry P)) : List (Stmt P (Cmd P)) :=
  entries.map (fun e => Stmt.cmd (.init e.2.1 e.2.2.1 ExprOrNondet.nondet e.2.2.2))

/-- Source↦fresh substitution recorded by the entries (reads only `e.1`/`e.2.1`). -/
@[expose] def substOf' (entries : List (Entry P)) : List (P.Ident × P.Ident) :=
  entries.map (fun e => (e.1, e.2.1))

/-- Hoist target idents. -/
@[expose] def targetsOf' (entries : List (Entry P)) : List P.Ident :=
  entries.map (fun e => e.2.1)

/-- Source idents being renamed (the `y`s). -/
@[expose] def sourcesOf' (entries : List (Entry P)) : List P.Ident :=
  entries.map (fun e => e.1)

@[simp] theorem havocStmts'_nil : havocStmts' ([] : List (Entry P)) = [] := rfl
@[simp] theorem havocStmts'_cons (e : Entry P) (rest : List (Entry P)) :
    havocStmts' (e :: rest)
      = Stmt.cmd (.init e.2.1 e.2.2.1 ExprOrNondet.nondet e.2.2.2)
          :: havocStmts' rest := rfl
@[simp] theorem substOf'_nil : substOf' ([] : List (Entry P)) = [] := rfl
@[simp] theorem substOf'_cons (e : Entry P) (rest : List (Entry P)) :
    substOf' (e :: rest) = (e.1, e.2.1) :: substOf' rest := rfl
@[simp] theorem targetsOf'_nil : targetsOf' ([] : List (Entry P)) = [] := rfl
@[simp] theorem targetsOf'_cons (e : Entry P) (rest : List (Entry P)) :
    targetsOf' (e :: rest) = e.2.1 :: targetsOf' rest := rfl
@[simp] theorem sourcesOf'_nil : sourcesOf' ([] : List (Entry P)) = [] := rfl
@[simp] theorem sourcesOf'_cons (e : Entry P) (rest : List (Entry P)) :
    sourcesOf' (e :: rest) = e.1 :: sourcesOf' rest := rfl

theorem havocStmts'_append (xs ys : List (Entry P)) :
    havocStmts' (xs ++ ys) = havocStmts' xs ++ havocStmts' ys := by
  simp [havocStmts', List.map_append]

theorem substOf'_append (xs ys : List (Entry P)) :
    substOf' (xs ++ ys) = substOf' xs ++ substOf' ys := by
  simp [substOf', List.map_append]

theorem sourcesOf'_append (xs ys : List (Entry P)) :
    sourcesOf' (xs ++ ys) = sourcesOf' xs ++ sourcesOf' ys := by
  simp [sourcesOf', List.map_append]

theorem sourcesOf'_mem {entries : List (Entry P)} {e : Entry P} (he : e ∈ entries) :
    e.1 ∈ sourcesOf' entries :=
  List.mem_map.mpr ⟨e, he, rfl⟩

/-! ### The harvested entries, mutual over the lift recursion. -/

mutual
/-- The entries harvested from a single statement's lift, threaded at `σ`. -/
@[expose] def Stmt.entriesOf [HasIdent P] (s : Stmt P (Cmd P)) (σ : StringGenState) :
    List (Entry P) :=
  match s with
  | .cmd (.init y ty _ md) =>
      let (fresh, _) := StringGenState.gen hoistFreshPrefix σ
      [(y, HasIdent.ident fresh, ty, md)]
  | .cmd _ => []
  | .block _ bss _ => Block.entriesOf bss σ
  | .ite _ tss ess _ =>
      Block.entriesOf tss σ ++
        Block.entriesOf ess (Block.liftInitsInLoopBodyM tss σ).2
  | .loop _ _ _ _ _ => []
  | .exit _ _ => []
  | .funcDecl _ _ => []
  | .typeDecl _ _ => []
  termination_by sizeOf s

/-- The entries harvested from a block's lift, threaded at `σ`. -/
@[expose] def Block.entriesOf [HasIdent P] (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    List (Entry P) :=
  match ss with
  | [] => []
  | s :: rest =>
      Stmt.entriesOf s σ ++
        Block.entriesOf rest (Stmt.liftInitsInLoopBodyM s σ).2
  termination_by sizeOf ss
end

theorem Stmt.entriesOf_block [HasIdent P] (lbl : String) (bss : List (Stmt P (Cmd P)))
    (md : MetaData P) (σ : StringGenState) :
    Stmt.entriesOf (.block lbl bss md) σ = Block.entriesOf bss σ := by
  rw [Stmt.entriesOf]

theorem Stmt.entriesOf_ite [HasIdent P] (g : ExprOrNondet P) (tss ess : List (Stmt P (Cmd P)))
    (md : MetaData P) (σ : StringGenState) :
    Stmt.entriesOf (.ite g tss ess md) σ =
      Block.entriesOf tss σ ++
        Block.entriesOf ess (Block.liftInitsInLoopBodyM tss σ).2 := by
  rw [Stmt.entriesOf]

theorem Block.entriesOf_cons [HasIdent P] (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P)))
    (σ : StringGenState) :
    Block.entriesOf (s :: rest) σ =
      Stmt.entriesOf s σ ++
        Block.entriesOf rest (Stmt.liftInitsInLoopBodyM s σ).2 := by
  rw [Block.entriesOf]

/-! ### Correspondence: harvest + renames = `havocStmts'` + `substOf'`. -/

mutual
theorem Stmt.lift_harvest_subst [HasIdent P] (s : Stmt P (Cmd P)) (σ : StringGenState) :
    (Stmt.liftInitsInLoopBodyM s σ).1.1.map Stmt.cmd = havocStmts' (Stmt.entriesOf s σ)
    ∧ (Stmt.liftInitsInLoopBodyM s σ).1.2.1 = substOf' (Stmt.entriesOf s σ) := by
  match s with
  | .cmd c =>
      cases c <;>
        refine ⟨?_, ?_⟩ <;>
        simp [Stmt.liftInitsInLoopBodyM, Stmt.entriesOf, havocStmts', substOf']
  | .block lbl bss md =>
      rw [Stmt.liftInitsInLoopBodyM, Stmt.entriesOf_block]
      rcases h : Block.liftInitsInLoopBodyM bss σ with ⟨⟨hs, rn, bss'⟩, σ'⟩
      have ih := Block.lift_harvest_subst bss σ
      rw [h] at ih
      simp only [h]
      exact ih
  | .ite g tss ess md =>
      rw [Stmt.liftInitsInLoopBodyM, Stmt.entriesOf_ite]
      rcases h₁ : Block.liftInitsInLoopBodyM tss σ with ⟨⟨ths, trn, tss'⟩, σ₁⟩
      rcases h₂ : Block.liftInitsInLoopBodyM ess σ₁ with ⟨⟨ehs, ern, ess'⟩, σ₂⟩
      have hσ₁ : (Block.liftInitsInLoopBodyM tss σ).2 = σ₁ := by rw [h₁]
      have ih₁ := Block.lift_harvest_subst tss σ
      rw [h₁] at ih₁; simp only at ih₁
      have ih₂ := Block.lift_harvest_subst ess σ₁
      rw [h₂] at ih₂; simp only at ih₂
      simp only [h₁, h₂]
      refine ⟨?_, ?_⟩
      · rw [List.map_append, ih₁.1, ih₂.1, havocStmts'_append]
      · rw [ih₁.2, ih₂.2, substOf'_append]
  | .loop g m inv body md =>
      rw [Stmt.liftInitsInLoopBodyM, Stmt.entriesOf]; exact ⟨rfl, rfl⟩
  | .exit lbl md => rw [Stmt.liftInitsInLoopBodyM, Stmt.entriesOf]; exact ⟨rfl, rfl⟩
  | .funcDecl d md => rw [Stmt.liftInitsInLoopBodyM, Stmt.entriesOf]; exact ⟨rfl, rfl⟩
  | .typeDecl t md => rw [Stmt.liftInitsInLoopBodyM, Stmt.entriesOf]; exact ⟨rfl, rfl⟩
  termination_by sizeOf s

theorem Block.lift_harvest_subst [HasIdent P] (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    (Block.liftInitsInLoopBodyM ss σ).1.1.map Stmt.cmd = havocStmts' (Block.entriesOf ss σ)
    ∧ (Block.liftInitsInLoopBodyM ss σ).1.2.1 = substOf' (Block.entriesOf ss σ) := by
  match ss with
  | [] => rw [Block.liftInitsInLoopBodyM, Block.entriesOf]; exact ⟨rfl, rfl⟩
  | s :: rest =>
      rw [Block.liftInitsInLoopBodyM, Block.entriesOf_cons]
      rcases h₁ : Stmt.liftInitsInLoopBodyM s σ with ⟨⟨hs_s, rn_s, ss_s⟩, σ₁⟩
      rcases h₂ : Block.liftInitsInLoopBodyM rest σ₁ with ⟨⟨hs_r, rn_r, ss_r⟩, σ₂⟩
      have hσ₁ : (Stmt.liftInitsInLoopBodyM s σ).2 = σ₁ := by rw [h₁]
      have ih₁ := Stmt.lift_harvest_subst s σ
      rw [h₁] at ih₁; simp only at ih₁
      have ih₂ := Block.lift_harvest_subst rest σ₁
      rw [h₂] at ih₂; simp only at ih₂
      simp only [h₁, h₂]
      refine ⟨?_, ?_⟩
      · rw [List.map_append, ih₁.1, ih₂.1, havocStmts'_append]
      · rw [ih₁.2, ih₂.2, substOf'_append]
  termination_by sizeOf ss
end

/-! ### The `e.1 ∈ initVars` invariant.

Every harvested entry's source ident `e.1` lies in the input's `initVars`.  This
is a subset (not equality): `entriesOf` harvests inits reachable through
`.block`/`.ite` only, not through nested `.loop` (which the lift passes through),
whereas `Block.initVars` also descends into `.loop` bodies.  Since `entriesOf`
skips loops and loops only add to `initVars`, the harvest sources are a subset of
`initVars` unconditionally. -/

mutual
theorem Stmt.sourcesOf_entriesOf_subset [HasIdent P] (s : Stmt P (Cmd P)) (σ : StringGenState) :
    ∀ x ∈ sourcesOf' (Stmt.entriesOf s σ), x ∈ Stmt.initVars s := by
  match s with
  | .cmd c =>
      cases c <;>
        simp [Stmt.entriesOf, Stmt.initVars, sourcesOf']
  | .block lbl bss md =>
      intro x hx
      rw [Stmt.entriesOf_block] at hx
      rw [Stmt.initVars_block]
      exact Block.sourcesOf_entriesOf_subset bss σ x hx
  | .ite g tss ess md =>
      intro x hx
      rw [Stmt.entriesOf_ite, sourcesOf'_append, List.mem_append] at hx
      rw [Stmt.initVars_ite, List.mem_append]
      rcases hx with h | h
      · exact Or.inl (Block.sourcesOf_entriesOf_subset tss σ x h)
      · exact Or.inr (Block.sourcesOf_entriesOf_subset ess _ x h)
  | .loop g m inv body md =>
      simp [Stmt.entriesOf, sourcesOf']
  | .exit lbl md => simp [Stmt.entriesOf, sourcesOf']
  | .funcDecl d md => simp [Stmt.entriesOf, sourcesOf']
  | .typeDecl t md => simp [Stmt.entriesOf, sourcesOf']
  termination_by sizeOf s

theorem Block.sourcesOf_entriesOf_subset [HasIdent P] (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ∀ x ∈ sourcesOf' (Block.entriesOf ss σ), x ∈ Block.initVars ss := by
  match ss with
  | [] => simp [Block.entriesOf, sourcesOf']
  | s :: rest =>
      intro x hx
      rw [Block.entriesOf_cons, sourcesOf'_append, List.mem_append] at hx
      rw [Block.initVars_cons, List.mem_append]
      rcases hx with h | h
      · exact Or.inl (Stmt.sourcesOf_entriesOf_subset s σ x h)
      · exact Or.inr (Block.sourcesOf_entriesOf_subset rest _ x h)
  termination_by sizeOf ss
end

/-- Membership form: every entry's source ident is in the block's `initVars`. -/
theorem Block.entry_source_mem_initVars [HasIdent P] (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    {e : Entry P} (he : e ∈ Block.entriesOf ss σ) :
    e.1 ∈ Block.initVars ss :=
  Block.sourcesOf_entriesOf_subset ss σ e.1 (sourcesOf'_mem he)

/-- The top-level entries-from-lift bridge (block-level): from a body `ss` lifted
at `σ`, exhibit `entries` such that the lift's havocs (mapped to `.cmd`) equal
`havocStmts' entries`, the lift's renames equal `substOf' entries`, and every
entry's source ident is a body init. -/
public theorem entries_from_lift [HasIdent P] (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ∃ entries : List (Entry P),
      let r := Block.liftInitsInLoopBodyM ss σ
      r.1.1.map Stmt.cmd = havocStmts' entries
      ∧ r.1.2.1 = substOf' entries
      ∧ (∀ e ∈ entries, e.1 ∈ Block.initVars ss) := by
  refine ⟨Block.entriesOf ss σ, ?_, ?_, ?_⟩
  · exact (Block.lift_harvest_subst ss σ).1
  · exact (Block.lift_harvest_subst ss σ).2
  · intro e he; exact Block.entry_source_mem_initVars ss σ he

/-! ## Per-entry-metadata prelude bridge.

`havocStmts'`/`substOf'`/`targetsOf'` read only `e.1`/`e.2.1`.  We add the
`extendStoreMany` bindings the run lands at — `(y', mkFvar y')` per entry. -/

@[expose] def bindingsOf' [HasFvar P] (entries : List (Entry P)) :
    List (P.Ident × P.Expr) :=
  entries.map (fun e => (e.2.1, HasFvar.mkFvar e.2.1))

@[simp] theorem bindingsOf'_nil [HasFvar P] :
    bindingsOf' ([] : List (Entry P)) = [] := rfl

@[simp] theorem bindingsOf'_cons [HasFvar P] (e : Entry P) (rest : List (Entry P)) :
    bindingsOf' (e :: rest)
      = (e.2.1, HasFvar.mkFvar e.2.1) :: bindingsOf' rest := rfl

/-- `targetsOf' entries = (substOf' entries).map Prod.snd`. -/
theorem targetsOf'_eq_substOf'_snd (entries : List (Entry P)) :
    targetsOf' entries = (substOf' entries).map Prod.snd := by
  induction entries with
  | nil => rfl
  | cons e rest ih => simp [ih]

/-- Outside the targets, `extendStoreMany σ (bindingsOf' entries)` agrees with `σ`. -/
theorem extendStoreMany_bindingsOf'_outside [HasFvar P] [DecidableEq P.Ident]
    (σ : SemanticStore P) (entries : List (Entry P))
    {x : P.Ident} (hx : x ∉ targetsOf' entries) :
    extendStoreMany σ (bindingsOf' entries) x = σ x := by
  induction entries generalizing σ with
  | nil => rfl
  | cons e rest ih =>
    simp only [targetsOf'_cons, List.mem_cons, not_or] at hx
    rw [bindingsOf'_cons, extendStoreMany_cons, ih _ hx.2]
    exact extendStoreOne_other σ e.2.1 (HasFvar.mkFvar e.2.1) x hx.1

/-- At a target (with `Nodup` targets), `extendStoreMany σ (bindingsOf' entries)`
is defined. -/
theorem extendStoreMany_bindingsOf'_bound [HasFvar P] [DecidableEq P.Ident]
    (σ : SemanticStore P) (entries : List (Entry P))
    (h_nodup : (targetsOf' entries).Nodup)
    {b : P.Ident} (hb : b ∈ targetsOf' entries) :
    extendStoreMany σ (bindingsOf' entries) b ≠ none := by
  induction entries generalizing σ with
  | nil => simp only [targetsOf'_nil, List.not_mem_nil] at hb
  | cons e rest ih =>
    simp only [targetsOf'_cons, List.mem_cons] at hb
    simp only [targetsOf'_cons, List.nodup_cons] at h_nodup
    rw [bindingsOf'_cons, extendStoreMany_cons]
    rcases hb with h | h
    · subst h
      have h_notin : e.2.1 ∉ targetsOf' rest := h_nodup.1
      rw [extendStoreMany_bindingsOf'_outside _ rest h_notin, extendStoreOne_self]
      exact Option.some_ne_none _
    · exact ih _ h_nodup.2 h

/-- The prelude run reaches the `extendStoreMany` post-store.  Each head
`.init e.2.1 e.2.2.1 .nondet e.2.2.2` steps by
`StepStmt.step_cmd (EvalCmd.eval_init_unconstrained (InitState.init ...))`,
choosing witness `mkFvar e.2.1`, which is exactly
`extendStoreOne σ e.2.1 (mkFvar e.2.1)`. -/
theorem prelude_run_list_md [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    (entries : List (Entry P))
    (ρ_hoist : Env P)
    (h_targets_undef : ∀ e ∈ entries, ρ_hoist.store e.2.1 = none)
    (h_targets_nodup : (targetsOf' entries).Nodup)
    (h_wfvar : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval) :
    StepStmtStar P (EvalCmd P) extendEval
      (.stmts (havocStmts' entries) ρ_hoist)
      (.terminal
        { ρ_hoist with
          store := extendStoreMany ρ_hoist.store (bindingsOf' entries)
          hasFailure := ρ_hoist.hasFailure }) := by
  induction entries generalizing ρ_hoist with
  | nil =>
    simp only [havocStmts'_nil, bindingsOf'_nil, extendStoreMany_nil]
    have h_env : ({ ρ_hoist with store := ρ_hoist.store, hasFailure := ρ_hoist.hasFailure } : Env P) = ρ_hoist := rfl
    rw [h_env]
    exact ReflTrans.step _ _ _ StepStmt.step_stmts_nil (ReflTrans.refl _)
  | cons e rest ih =>
    rcases e with ⟨y, y', ty, md⟩
    let v : P.Expr := HasFvar.mkFvar y'
    let σ1 : SemanticStore P := extendStoreOne ρ_hoist.store y' v
    let ρ1 : Env P := { ρ_hoist with store := σ1, hasFailure := ρ_hoist.hasFailure || false }
    have h_y'_undef : ρ_hoist.store y' = none :=
      h_targets_undef (y, y', ty, md) List.mem_cons_self
    have h_is : InitState P ρ_hoist.store y' v σ1 :=
      InitState.init h_y'_undef (extendStoreOne_self ρ_hoist.store y' v)
        (fun z hz => extendStoreOne_other ρ_hoist.store y' v z (fun h => hz h.symm))
    have h_step : StepStmt P (EvalCmd P) extendEval
        (.stmt (.cmd (Cmd.init y' ty ExprOrNondet.nondet md)) ρ_hoist)
        (.terminal ρ1) :=
      StepStmt.step_cmd (EvalCmd.eval_init_unconstrained h_is (h_wfvar ρ_hoist))
    have h_nodup_tl : (targetsOf' rest).Nodup := by
      simp only [targetsOf'_cons, List.nodup_cons] at h_targets_nodup
      exact h_targets_nodup.2
    have h_y'_notin_tl : y' ∉ targetsOf' rest := by
      simp only [targetsOf'_cons, List.nodup_cons] at h_targets_nodup
      exact h_targets_nodup.1
    have h_targets_undef_tl : ∀ e ∈ rest, ρ1.store e.2.1 = none := by
      intro e' he'
      have h_e'_in_tgts : e'.2.1 ∈ targetsOf' rest :=
        List.mem_map.mpr ⟨e', he', rfl⟩
      have h_ne : e'.2.1 ≠ y' := by
        intro h; apply h_y'_notin_tl; rw [← h]; exact h_e'_in_tgts
      show (if e'.2.1 = y' then some v else ρ_hoist.store e'.2.1) = none
      rw [if_neg h_ne]
      exact h_targets_undef e' (List.mem_cons_of_mem _ he')
    have h_run_tl := ih ρ1 h_targets_undef_tl h_nodup_tl
    simp only [havocStmts'_cons]
    refine ReflTrans.step _ _ _ StepStmt.step_stmts_cons ?_
    refine ReflTrans.step _ _ _ (StepStmt.step_seq_inner h_step) ?_
    refine ReflTrans.step _ _ _ StepStmt.step_seq_done ?_
    have h_run_tl' :
        StepStmtStar P (EvalCmd P) extendEval
          (.stmts (havocStmts' rest) ρ1)
          (.terminal
            { ρ_hoist with
              store := extendStoreMany ρ_hoist.store (bindingsOf' ((y, y', ty, md) :: rest)),
              hasFailure := ρ_hoist.hasFailure }) := by
      have h_eq :
          ({ ρ_hoist with
              store := extendStoreMany ρ_hoist.store (bindingsOf' ((y, y', ty, md) :: rest)),
              hasFailure := ρ_hoist.hasFailure } : Env P)
            = { store := extendStoreMany ρ1.store (bindingsOf' rest), eval := ρ1.eval,
                hasFailure := ρ1.hasFailure } := by
        show (_ : Env P) = _
        rw [bindingsOf'_cons, extendStoreMany_cons]
        show (_ : Env P) = _
        simp only [ρ1, σ1, v, Bool.or_false]
      rw [h_eq]; exact h_run_tl
    exact h_run_tl'

/-- Frame-exposing prelude bridge.  Runs `havocStmts' entries` from a
store-equal env and establishes `HoistInv A (targetsOf' entries) (substOf'
entries)` together with the evaluator / failure agreement and
target-boundedness, and ALSO returns the unguarded off-targets agreement
`ρ_pre = ρ_run off targetsOf' entries`.  The §E `.loop` arm's union-entry
`HoistInv` builder needs this agreement (it lives outside the guarded
`HoistInv` frame, holding even on `A`), so the prelude's structural havoc-frame
is surfaced explicitly. -/
public theorem prelude_bridge_list_md_frame [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    (A : List P.Ident)
    (entries : List (Entry P))
    (ρ_src ρ_run : Env P)
    (h_store_eq : ρ_run.store = ρ_src.store)
    (h_eval_eq  : ρ_run.eval = ρ_src.eval)
    (h_hf_eq    : ρ_run.hasFailure = ρ_src.hasFailure)
    (h_src_undef : ∀ e ∈ entries, ρ_src.store e.1 = none)
    (h_tgt_undef : ∀ e ∈ entries, ρ_src.store e.2.1 = none)
    (h_tgt_nodup : (targetsOf' entries).Nodup)
    (h_wfvar : ∀ ρ : Env P, WellFormedSemanticEvalVar ρ.eval) :
    ∃ ρ_pre : Env P,
      StepStmtStar P (EvalCmd P) extendEval
        (.stmts (havocStmts' entries) ρ_run)
        (.terminal ρ_pre)
      ∧ HoistInv (P := P) A (targetsOf' entries) (substOf' entries)
          ρ_src.store ρ_pre.store
      ∧ ρ_src.eval = ρ_pre.eval
      ∧ ρ_src.hasFailure = ρ_pre.hasFailure
      ∧ (∀ b ∈ targetsOf' entries, ρ_pre.store b ≠ none)
      ∧ (∀ x, x ∉ targetsOf' entries → ρ_pre.store x = ρ_run.store x) := by
  have h_tgt_undef_h : ∀ e ∈ entries, ρ_run.store e.2.1 = none := by
    intro e he; rw [h_store_eq]; exact h_tgt_undef e he
  have h_run := prelude_run_list_md (extendEval := extendEval)
    entries ρ_run h_tgt_undef_h h_tgt_nodup h_wfvar
  -- `prelude_run_list_md` pins the run output to the concrete extend-store env;
  -- rebuild the HoistInv + agreements directly against that concrete env.
  refine ⟨{ ρ_run with
      store := extendStoreMany ρ_run.store (bindingsOf' entries)
      hasFailure := ρ_run.hasFailure }, h_run, ?_, ?_, ?_, ?_, ?_⟩
  · -- HoistInv A (targets) (substOf'E) ρ_src ρ_pre at the concrete env.
    have h_seed : HoistInv (P := P) A [] [] ρ_src.store ρ_run.store := by
      refine ⟨?_, ?_⟩
      · intro x _ _ _; rw [h_store_eq]
      · intro a b h_pair _; simp at h_pair
    have h_new_src_undef :
        ∀ a ∈ (substOf' entries).map Prod.fst, ρ_src.store a = none := by
      intro a ha
      rcases List.mem_map.mp ha with ⟨p, hp_mem, hp_eq⟩
      rcases List.mem_map.mp hp_mem with ⟨e, he, he_eq⟩
      subst he_eq; subst hp_eq; exact h_src_undef e he
    have h_extend : ∀ x, x ∉ targetsOf' entries →
        (extendStoreMany ρ_run.store (bindingsOf' entries)) x = ρ_run.store x := by
      intro x hx; exact extendStoreMany_bindingsOf'_outside ρ_run.store entries hx
    have h_inv :=
      HoistInv.add_vacuous_pairs (P := P) (A := A) (B := []) (B_new := targetsOf' entries)
        (subst := []) (subst_new := substOf' entries)
        (σ_src := ρ_src.store) (σ_h := ρ_run.store)
        (σ_h' := extendStoreMany ρ_run.store (bindingsOf' entries))
        h_new_src_undef
        (by intro b hb; simp at hb)
        h_extend
        (by intro b hb; simp at hb)
        h_seed
    simpa using h_inv
  · show ρ_src.eval = ρ_run.eval; exact h_eval_eq.symm
  · show ρ_src.hasFailure = ρ_run.hasFailure; exact h_hf_eq.symm
  · intro b hb
    show extendStoreMany ρ_run.store (bindingsOf' entries) b ≠ none
    exact extendStoreMany_bindingsOf'_bound ρ_run.store entries h_tgt_nodup hb
  · intro x hx
    show extendStoreMany ρ_run.store (bindingsOf' entries) x = ρ_run.store x
    exact extendStoreMany_bindingsOf'_outside ρ_run.store entries hx



/-- List-generalised HoistInv union bridge: Step A at the enclosing carriers
`Ao Bo so` composed with Step B at the new carriers `As Bs ss` yields `HoistInv`
at the union carriers, from disjointness facts. -/
public theorem bridge_out_union_list
    {Ao Bo As Bs : List P.Ident}
    {so ss : List (P.Ident × P.Ident)}
    {ρ_s' ρ₁' ρ_h' : Env P}
    (hA : HoistInv (P := P) Ao Bo so ρ_s'.store ρ₁'.store)
    (hB : HoistInv (P := P) As Bs ss ρ₁'.store ρ_h'.store)
    (h_so_wf : ∀ a b, (a, b) ∈ so → a ∈ Ao ∧ b ∈ Bo)
    (h_ss_wf : ∀ a b, (a, b) ∈ ss → a ∈ As ∧ b ∈ Bs)
    (h_As_notAo : ∀ x ∈ As, x ∉ Ao) (h_As_notBo : ∀ x ∈ As, x ∉ Bo)
    (h_Bo_notAs : ∀ b ∈ Bo, b ∉ As) (h_Bo_notBs : ∀ b ∈ Bo, b ∉ Bs) :
    HoistInv (P := P) (Ao ++ As) (Bo ++ Bs) (so ++ ss) ρ_s'.store ρ_h'.store := by
  refine ⟨?_, ?_⟩
  · intro x hxA hxB h_x_ne
    have hxAo : x ∉ Ao := fun h => hxA (List.mem_append.mpr (Or.inl h))
    have hxAs : x ∉ As := fun h => hxA (List.mem_append.mpr (Or.inr h))
    have hxBo : x ∉ Bo := fun h => hxB (List.mem_append.mpr (Or.inl h))
    have hxBs : x ∉ Bs := fun h => hxB (List.mem_append.mpr (Or.inr h))
    have e1 : ρ_s'.store x = ρ₁'.store x := hA.1 x hxAo hxBo h_x_ne
    have e2 : ρ₁'.store x = ρ_h'.store x := hB.1 x hxAs hxBs (e1 ▸ h_x_ne)
    rw [e1, e2]
  · intro a b h_pair h_ne
    rcases List.mem_append.mp h_pair with h_so | h_ss
    · obtain ⟨h_b_ne₁, h_eq₁⟩ := hA.2 a b h_so h_ne
      have h_b_in_Bo : b ∈ Bo := (h_so_wf a b h_so).2
      have h_b_notAs : b ∉ As := h_Bo_notAs b h_b_in_Bo
      have h_b_notBs : b ∉ Bs := h_Bo_notBs b h_b_in_Bo
      have h_b_move : ρ₁'.store b = ρ_h'.store b := hB.1 b h_b_notAs h_b_notBs h_b_ne₁
      exact ⟨h_b_move ▸ h_b_ne₁, by rw [h_eq₁, h_b_move]⟩
    · have h_a_in_As : a ∈ As := (h_ss_wf a b h_ss).1
      have h_a_notAo : a ∉ Ao := h_As_notAo a h_a_in_As
      have h_a_notBo : a ∉ Bo := h_As_notBo a h_a_in_As
      have h_ya : ρ_s'.store a = ρ₁'.store a := hA.1 a h_a_notAo h_a_notBo h_ne
      have h_ne₁ : ρ₁'.store a ≠ none := h_ya ▸ h_ne
      obtain ⟨h_b_ne, h_eq⟩ := hB.2 a b h_ss h_ne₁
      exact ⟨h_b_ne, by rw [h_ya]; exact h_eq⟩

/-- The composed body simulation must re-establish `Bo`-boundedness at `ρ_h'`.
Step A gives it at the mid env `ρ₁'`; Step B's frame transports it to `ρ_h'`
since `Bo` is disjoint from the new carriers. -/
public theorem bound_Bo_through_stepB
    {Bo As Bs : List P.Ident} {ss : List (P.Ident × P.Ident)}
    {ρ₁' ρ_h' : Env P}
    (hB : HoistInv (P := P) As Bs ss ρ₁'.store ρ_h'.store)
    (h_bnd₁_Bo : ∀ y ∈ Bo, ρ₁'.store y ≠ none)
    (h_Bo_notAs : ∀ b ∈ Bo, b ∉ As) (h_Bo_notBs : ∀ b ∈ Bo, b ∉ Bs) :
    ∀ y ∈ Bo, ρ_h'.store y ≠ none := by
  intro y hy
  have h_move : ρ₁'.store y = ρ_h'.store y :=
    hB.1 y (h_Bo_notAs y hy) (h_Bo_notBs y hy) (h_bnd₁_Bo y hy)
  exact h_move ▸ h_bnd₁_Bo y hy










/-- `bridge_in_guarded_undef` augmented with a `σ_sf`-relative HOIST-side
store-kind-freedom conjunct on the mid env `ρ₁`.  Because `ρ₁ = ρ_s` off the
enclosing carriers `Ao ∪ Bo`, and a `Q`-kind name `∉ σ_sf` avoids those carriers
(`h_sf_notAo` / `h_sf_notBo`), `ρ₁` agrees with `ρ_s` on every such name, so the
SOURCE kind-freedom (`h_src_sf`) transports to `ρ₁`. -/
public theorem bridge_in_guarded_undef_sf [HasIdent P] [DecidableEq P.Ident]
    {Q : String → Prop}
    {Vh : List P.Ident} {σ_sf : StringGenState}
    {Ao Bo As Bs : List P.Ident} {so ss : List (P.Ident × P.Ident)}
    (h_so_wf : ∀ a b, (a, b) ∈ so → a ∈ Ao ∧ b ∈ Bo)
    (h_ss_wf : ∀ a b, (a, b) ∈ ss → a ∈ As ∧ b ∈ Bs)
    (h_As_notAo : ∀ x ∈ As, x ∉ Ao) (h_As_notBo : ∀ x ∈ As, x ∉ Bo)
    (h_Vh_notAo : ∀ y ∈ Vh, y ∉ Ao) (h_Vh_notBo : ∀ y ∈ Vh, y ∉ Bo)
    (h_sf_notAo : ∀ str : String, Q str →
       str ∉ StringGenState.stringGens σ_sf → HasIdent.ident (P := P) str ∉ Ao)
    (h_sf_notBo : ∀ str : String, Q str →
       str ∉ StringGenState.stringGens σ_sf → HasIdent.ident (P := P) str ∉ Bo)
    (ρ_s ρ_h : Env P)
    (h_hinv : HoistInv (P := P) (Ao ++ As) (Bo ++ Bs) (so ++ ss) ρ_s.store ρ_h.store)
    (h_eval : ρ_s.eval = ρ_h.eval) (h_hf : ρ_s.hasFailure = ρ_h.hasFailure)
    (h_bnd : ∀ y ∈ Bo ++ Bs, ρ_h.store y ≠ none)
    (h_Vh_src : ∀ y ∈ Vh, ρ_s.store y = none)
    (h_src_sf : ∀ str : String, Q str →
       str ∉ StringGenState.stringGens σ_sf → ρ_s.store (HasIdent.ident (P := P) str) = none) :
    ∃ ρ₁ : Env P,
      HoistInv (P := P) Ao Bo so ρ_s.store ρ₁.store ∧
      ρ_s.eval = ρ₁.eval ∧ ρ_s.hasFailure = ρ₁.hasFailure ∧
      (∀ y ∈ Bo, ρ₁.store y ≠ none) ∧
      (∀ y ∈ Vh, ρ₁.store y = none) ∧
      (∀ str : String, Q str →
         str ∉ StringGenState.stringGens σ_sf → ρ₁.store (HasIdent.ident (P := P) str) = none) ∧
      HoistInv (P := P) As Bs ss ρ₁.store ρ_h.store ∧
      ρ₁.eval = ρ_h.eval ∧ ρ₁.hasFailure = ρ_h.hasFailure ∧
      (∀ y ∈ Bs, ρ_h.store y ≠ none) := by
  classical
  let σ₁ : SemanticStore P := fun x => if x ∈ Ao ∨ x ∈ Bo then ρ_h.store x else ρ_s.store x
  let ρ₁ : Env P := { store := σ₁, eval := ρ_h.eval, hasFailure := ρ_h.hasFailure }
  have hσ_in : ∀ x, x ∈ Ao ∨ x ∈ Bo → σ₁ x = ρ_h.store x := by
    intro x hx; show (if x ∈ Ao ∨ x ∈ Bo then _ else _) = _; rw [if_pos hx]
  have hσ_out : ∀ x, x ∉ Ao → x ∉ Bo → σ₁ x = ρ_s.store x := by
    intro x hA hB; show (if x ∈ Ao ∨ x ∈ Bo then _ else _) = _
    rw [if_neg (not_or.mpr ⟨hA, hB⟩)]
  refine ⟨ρ₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro x hxAo hxBo _; show ρ_s.store x = σ₁ x; rw [hσ_out x hxAo hxBo]
    · intro a b h_pair h_ne
      obtain ⟨ha_Ao, hb_Bo⟩ := h_so_wf a b h_pair
      obtain ⟨h_b_ne, h_eq⟩ := h_hinv.2 a b (List.mem_append.mpr (Or.inl h_pair)) h_ne
      have hσ : σ₁ b = ρ_h.store b := hσ_in b (Or.inr hb_Bo)
      exact ⟨by show σ₁ b ≠ none; rw [hσ]; exact h_b_ne,
             by show ρ_s.store a = σ₁ b; rw [hσ]; exact h_eq⟩
  · exact h_eval
  · exact h_hf
  · intro y hy
    show σ₁ y ≠ none
    rw [hσ_in y (Or.inr hy)]; exact h_bnd y (List.mem_append.mpr (Or.inl hy))
  · intro y hy
    show σ₁ y = none
    rw [hσ_out y (h_Vh_notAo y hy) (h_Vh_notBo y hy)]; exact h_Vh_src y hy
  · -- the new HOIST-side shape-freedom conjunct on `ρ₁`.
    intro str h_suf h_notσ
    show σ₁ (HasIdent.ident (P := P) str) = none
    rw [hσ_out (HasIdent.ident (P := P) str)
      (h_sf_notAo str h_suf h_notσ) (h_sf_notBo str h_suf h_notσ)]
    exact h_src_sf str h_suf h_notσ
  · refine ⟨?_, ?_⟩
    · intro x hxAs hxBs h_x_ne
      show σ₁ x = ρ_h.store x
      by_cases hAB : x ∈ Ao ∨ x ∈ Bo
      · rw [hσ_in x hAB]
      · have hxAo : x ∉ Ao := fun h => hAB (Or.inl h)
        have hxBo : x ∉ Bo := fun h => hAB (Or.inr h)
        have hσx : σ₁ x = ρ_s.store x := hσ_out x hxAo hxBo
        have hxAoAs : x ∉ Ao ++ As := by
          intro h; rcases List.mem_append.mp h with h | h
          · exact hxAo h
          · exact hxAs h
        have hxBoBs : x ∉ Bo ++ Bs := by
          intro h; rcases List.mem_append.mp h with h | h
          · exact hxBo h
          · exact hxBs h
        have h_s_ne : ρ_s.store x ≠ none := hσx ▸ h_x_ne
        rw [hσx]; exact h_hinv.1 x hxAoAs hxBoBs h_s_ne
    · intro a b h_pair h_ne
      obtain ⟨ha_As, hb_Bs⟩ := h_ss_wf a b h_pair
      have ha_notAo : a ∉ Ao := h_As_notAo a ha_As
      have ha_notBo : a ∉ Bo := h_As_notBo a ha_As
      have hσa : σ₁ a = ρ_s.store a := hσ_out a ha_notAo ha_notBo
      have h_s_ne : ρ_s.store a ≠ none := hσa ▸ h_ne
      obtain ⟨h_b_ne, h_eq⟩ := h_hinv.2 a b (List.mem_append.mpr (Or.inr h_pair)) h_s_ne
      refine ⟨h_b_ne, ?_⟩
      show σ₁ a = ρ_h.store b
      rw [hσa]; exact h_eq
  · rfl
  · rfl
  · intro y hy; exact h_bnd y (List.mem_append.mpr (Or.inr hy))




/-! ## Sum-typed shapefree-carrying body simulation + union compose + exiting driver.

The terminal-only stack above (`BodySimUSF` / `compose_union_sf` /
`loopDet_lift_sf_2g_undef_fuel`) rules out a loop body that breaks (it concludes
only the TERMINAL loop outcome and feeds Step B a TERMINAL-only `BodySim`).  The
following ADDITIVE stack is the sum-typed (terminal-OR-exiting) analogue, built by
combining the shapefree-carrying compose's per-iteration store-kind-freedom
bookkeeping with the sum-typed exiting outcome of `BodySimSum` / `loopDet_lift_2g_E_fuel`:

* `BodySimUSFSum` augments `BodySimUSF` with the parallel EXITING clause (a body
  run that breaks with label `l` is matched by a hoist body run that breaks with
  the SAME label, re-establishing `HoistInv` / `hasFailure` / `B`-boundedness at
  the body-exit stores).
* `compose_union_sf_sum` composes a sum-typed Step A (explicit ∀-shape with both
  outcomes) with a sum-typed Step B (`BodySimSum`) into a `BodySimUSFSum`; the
  exiting clause composes sequentially body→body₁→body₃ exactly as the terminal
  clause does (structurally parallel to the proven `bodySimES_cons`).
* `loopDet_lift_sf_2g_undef_E_fuel` is the EXITING-target driver: structurally
  `loopDet_lift_2g_E_fuel` with the `Vs`/`Vh`/`σ_sf` carriers threaded but UNUSED on
  the exit path (the exiting outcome caps both stores via `HoistInv.project_both`
  and never recurses on the inner loop), consuming a `BodySimUSFSum`.

This section is strictly ADDITIVE: the terminal-only stack and its support lemmas
are untouched, so existing call paths keep building unchanged. -/

/-- The sum-typed shapefree-carrying body simulation: `BodySimUSF` augmented with
the parallel EXITING clause.  A body run that TERMINATES is matched by a
terminating hoist run (the existing `BodySimUSF` clause); a body run that EXITS
with label `l` is matched by a hoist run that exits with the SAME label `l`,
re-establishing `HoistInv` / `hasFailure` / `B`-boundedness at the body-exit
stores.  The `σ_sf`-relative SOURCE store-kind-freedom invariant is assumed at
entry exactly as in `BodySimUSF` (it gates which `Q`-kind names may be undefined). -/
public def BodySimUSFSum [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendEval : ExtendEval P}
    (Q : String → Prop)
    (Vs Vh : List P.Ident) (σ_sf : StringGenState) (A B : List P.Ident)
    (subst : List (P.Ident × P.Ident))
    (bsrc bh : List (Stmt P (Cmd P))) : Prop :=
  ∀ (ρ_s ρ_h : Env P),
    HoistInv (P := P) A B subst ρ_s.store ρ_h.store →
    ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
    (∀ y ∈ B, ρ_h.store y ≠ none) →
    (∀ y ∈ Vs, ρ_s.store y = none) → (∀ y ∈ Vh, ρ_h.store y = none) →
    (∀ str : String, Q str →
       str ∉ StringGenState.stringGens σ_sf → ρ_s.store (HasIdent.ident (P := P) str) = none) →
    -- TERMINAL clause (exactly `BodySimUSF`):
    (∀ (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendEval (.stmts bsrc ρ_s) (.terminal ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendEval (.stmts bh ρ_h) (.terminal ρ_h') ∧
        HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
        ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none))
    ∧
    -- EXITING clause (new):
    (∀ (l : String) (ρ_s' : Env P),
      StepStmtStar P (EvalCmd P) extendEval (.stmts bsrc ρ_s) (.exiting l ρ_s') →
      ∃ ρ_h' : Env P,
        StepStmtStar P (EvalCmd P) extendEval (.stmts bh ρ_h) (.exiting l ρ_h') ∧
        HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
        ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none))

/-- The sum-typed shapefree-carrying union compose: `compose_union_sf` augmented
with the EXITING clause.  Step A is the explicit ∀-shape carrying BOTH outcomes
(terminal AND exiting), with the `σ_sf`-relative store-kind-freedom assumed on
both `ρ_s` and its hoist mid env `ρ₁`.  Step B is a sum-typed `BodySimSum`.  The
composed body simulation (`BodySimUSFSum`) carries both outcomes: the terminal
clause is `compose_union_sf` verbatim; the exiting clause composes sequentially
body→body₁→body₃ (Step A's exiting clause produces an exiting body₁ run at the
mid env `ρ₁`, then Step B's exiting clause produces an exiting body₃ run),
exactly parallel to `bodySimES_cons`' exiting head case. -/
public theorem compose_union_sf_sum [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendEval : ExtendEval P}
    {Q : String → Prop}
    {Vs Vh : List P.Ident} {σ_sf : StringGenState}
    {Ao Bo As Bs : List P.Ident}
    {so ss : List (P.Ident × P.Ident)}
    {body body₁ body₃ : List (Stmt P (Cmd P))}
    (stepA_term : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) Ao Bo so ρ_s.store ρ_h.store →
       ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
       (∀ y ∈ Bo, ρ_h.store y ≠ none) →
       (∀ y ∈ Vs, ρ_s.store y = none) → (∀ y ∈ Vh, ρ_h.store y = none) →
       (∀ str : String, Q str →
          str ∉ StringGenState.stringGens σ_sf → ρ_s.store (HasIdent.ident (P := P) str) = none) →
       (∀ str : String, Q str →
          str ∉ StringGenState.stringGens σ_sf → ρ_h.store (HasIdent.ident (P := P) str) = none) →
       ∀ (ρ_s' : Env P),
         StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ_s) (.terminal ρ_s') →
         ∃ ρ_h' : Env P,
           StepStmtStar P (EvalCmd P) extendEval (.stmts body₁ ρ_h) (.terminal ρ_h') ∧
           HoistInv (P := P) Ao Bo so ρ_s'.store ρ_h'.store ∧
           ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ Bo, ρ_h'.store y ≠ none))
    (stepA_exit : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) Ao Bo so ρ_s.store ρ_h.store →
       ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
       (∀ y ∈ Bo, ρ_h.store y ≠ none) →
       (∀ y ∈ Vs, ρ_s.store y = none) → (∀ y ∈ Vh, ρ_h.store y = none) →
       (∀ str : String, Q str →
          str ∉ StringGenState.stringGens σ_sf → ρ_s.store (HasIdent.ident (P := P) str) = none) →
       (∀ str : String, Q str →
          str ∉ StringGenState.stringGens σ_sf → ρ_h.store (HasIdent.ident (P := P) str) = none) →
       ∀ (l : String) (ρ_s' : Env P),
         StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ_s) (.exiting l ρ_s') →
         ∃ ρ_h' : Env P,
           StepStmtStar P (EvalCmd P) extendEval (.stmts body₁ ρ_h) (.exiting l ρ_h') ∧
           HoistInv (P := P) Ao Bo so ρ_s'.store ρ_h'.store ∧
           ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ Bo, ρ_h'.store y ≠ none))
    (stepB : BodySimSum (extendEval := extendEval) As Bs ss body₁ body₃)
    (h_so_wf : ∀ a b, (a, b) ∈ so → a ∈ Ao ∧ b ∈ Bo)
    (h_ss_wf : ∀ a b, (a, b) ∈ ss → a ∈ As ∧ b ∈ Bs)
    (h_As_notAo : ∀ x ∈ As, x ∉ Ao) (h_As_notBo : ∀ x ∈ As, x ∉ Bo)
    (h_Bo_notAs : ∀ b ∈ Bo, b ∉ As) (h_Bo_notBs : ∀ b ∈ Bo, b ∉ Bs)
    (h_Vh_sub_Vs : ∀ y ∈ Vh, y ∈ Vs)
    (bridge_in : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) (Ao ++ As) (Bo ++ Bs) (so ++ ss) ρ_s.store ρ_h.store →
       ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
       (∀ y ∈ Bo ++ Bs, ρ_h.store y ≠ none) →
       (∀ y ∈ Vh, ρ_s.store y = none) →
       (∀ str : String, Q str →
          str ∉ StringGenState.stringGens σ_sf → ρ_s.store (HasIdent.ident (P := P) str) = none) →
       ∃ ρ₁ : Env P,
         HoistInv (P := P) Ao Bo so ρ_s.store ρ₁.store ∧
         ρ_s.eval = ρ₁.eval ∧ ρ_s.hasFailure = ρ₁.hasFailure ∧
         (∀ y ∈ Bo, ρ₁.store y ≠ none) ∧
         (∀ y ∈ Vh, ρ₁.store y = none) ∧
         (∀ str : String, Q str →
            str ∉ StringGenState.stringGens σ_sf → ρ₁.store (HasIdent.ident (P := P) str) = none) ∧
         HoistInv (P := P) As Bs ss ρ₁.store ρ_h.store ∧
         ρ₁.eval = ρ_h.eval ∧ ρ₁.hasFailure = ρ_h.hasFailure ∧
         (∀ y ∈ Bs, ρ_h.store y ≠ none)) :
    BodySimUSFSum (extendEval := extendEval) Q Vs Vh σ_sf (Ao ++ As) (Bo ++ Bs) (so ++ ss) body body₃ := by
  intro ρ_s ρ_h h_hinv h_eval h_hf h_bnd h_Vs h_Vh h_src_sf
  obtain ⟨ρ₁, h_hinv_A, h_eval_A, h_hf_A, h_bnd_A, h_Vh_A, h_sf_A,
          h_hinv_B, h_eval_B, h_hf_B, h_bnd_B⟩ :=
    bridge_in ρ_s ρ_h h_hinv h_eval h_hf h_bnd
      (by intro y hy; exact h_Vs y (h_Vh_sub_Vs y hy)) h_src_sf
  refine ⟨?_, ?_⟩
  · -- TERMINAL clause: `compose_union_sf` verbatim.
    intro ρ_s' h_run
    obtain ⟨ρ₁', h_run₁, h_hinv₁, h_hf₁, h_bnd₁⟩ :=
      stepA_term ρ_s ρ₁ h_hinv_A h_eval_A h_hf_A h_bnd_A h_Vs h_Vh_A h_src_sf h_sf_A ρ_s' h_run
    obtain ⟨ρ_h', h_run₃, h_hinv₃, h_hf₃, h_bnd₃⟩ :=
      (stepB ρ₁ ρ_h h_hinv_B h_eval_B h_hf_B h_bnd_B).1 ρ₁' h_run₁
    refine ⟨ρ_h', h_run₃, ?_, ?_, ?_⟩
    · exact bridge_out_union_list h_hinv₁ h_hinv₃ h_so_wf h_ss_wf
        h_As_notAo h_As_notBo h_Bo_notAs h_Bo_notBs
    · rw [h_hf₁, h_hf₃]
    · intro y hy
      rcases List.mem_append.mp hy with hyBo | hyBs
      · exact bound_Bo_through_stepB h_hinv₃ h_bnd₁ h_Bo_notAs h_Bo_notBs y hyBo
      · exact h_bnd₃ y hyBs
  · -- EXITING clause: compose body→body₁→body₃ via the two exiting clauses.
    intro l ρ_s' h_run
    obtain ⟨ρ₁', h_run₁, h_hinv₁, h_hf₁, h_bnd₁⟩ :=
      stepA_exit ρ_s ρ₁ h_hinv_A h_eval_A h_hf_A h_bnd_A h_Vs h_Vh_A h_src_sf h_sf_A l ρ_s' h_run
    obtain ⟨ρ_h', h_run₃, h_hinv₃, h_hf₃, h_bnd₃⟩ :=
      (stepB ρ₁ ρ_h h_hinv_B h_eval_B h_hf_B h_bnd_B).2 l ρ₁' h_run₁
    refine ⟨ρ_h', h_run₃, ?_, ?_, ?_⟩
    · exact bridge_out_union_list h_hinv₁ h_hinv₃ h_so_wf h_ss_wf
        h_As_notAo h_As_notBo h_Bo_notAs h_Bo_notBs
    · rw [h_hf₁, h_hf₃]
    · intro y hy
      rcases List.mem_append.mp hy with hyBo | hyBs
      · exact bound_Bo_through_stepB h_hinv₃ h_bnd₁ h_Bo_notAs h_Bo_notBs y hyBo
      · exact h_bnd₃ y hyBs

/-- `BodySimUSFSum` unfolds definitionally to the ∀-shape the sum-typed exiting
driver `loopDet_lift_sf_2g_undef_E_fuel`'s `body_sim` parameter expects (a
`BodySimSum`-like predicate guarded by the `Vs`/`Vh`/`σ_sf` carriers). -/
public theorem bodySimUSFSum_is_driver_slot [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendEval : ExtendEval P}
    {Q : String → Prop}
    (Vs Vh : List P.Ident) (σ_sf : StringGenState) (A B : List P.Ident)
    (subst : List (P.Ident × P.Ident))
    (bsrc bh : List (Stmt P (Cmd P)))
    (h : BodySimUSFSum (extendEval := extendEval) Q Vs Vh σ_sf A B subst bsrc bh) :
    ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store →
       ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
       (∀ y ∈ B, ρ_h.store y ≠ none) →
       (∀ y ∈ Vs, ρ_s.store y = none) → (∀ y ∈ Vh, ρ_h.store y = none) →
       (∀ str : String, Q str →
          str ∉ StringGenState.stringGens σ_sf → ρ_s.store (HasIdent.ident (P := P) str) = none) →
       (∀ (ρ_s' : Env P),
         StepStmtStar P (EvalCmd P) extendEval (.stmts bsrc ρ_s) (.terminal ρ_s') →
         ∃ ρ_h' : Env P,
           StepStmtStar P (EvalCmd P) extendEval (.stmts bh ρ_h) (.terminal ρ_h') ∧
           HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
           ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none))
       ∧
       (∀ (l : String) (ρ_s' : Env P),
         StepStmtStar P (EvalCmd P) extendEval (.stmts bsrc ρ_s) (.exiting l ρ_s') →
         ∃ ρ_h' : Env P,
           StepStmtStar P (EvalCmd P) extendEval (.stmts bh ρ_h) (.exiting l ρ_h') ∧
           HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
           ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none)) :=
  h

/-- **The sum-typed shapefree-carrying two-guard EXITING-target fuel recursion.**

The EXITING analogue of `loopDet_lift_2g_E_fuel`, with the `Vs`/`Vh`/`σ_sf`
carriers of `loopDet_lift_sf_2g_undef_fuel` threaded through.  Given a source loop
run reaching `.exiting label ρ_post`, produces a hoist loop run reaching `.exiting
label ρ_post_h` with `HoistInv` / `hasFailure` / `B`-boundedness at the exit
stores.  The body simulation slot is the `BodySimUSFSum`-shaped predicate
(terminal AND exiting clauses, guarded by the carriers).

On the exit path the carriers play the same bookkeeping role as in
`loopDet_lift_sf_2g_undef_fuel`: each terminal intermediate iteration re-establishes
them at the projected store (`projectStore_undef_at`) before recursing; the
exiting final iteration consumes the body's exiting clause and caps both stores
via `HoistInv.project_both` (no further recursion). -/
public theorem loopDet_lift_sf_2g_undef_E_fuel [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {Q : String → Prop}
    {g_s g_h : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {Vs Vh : List P.Ident} {σ_sf : StringGenState}
    (h_guard_transport : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
       ρ_s.eval ρ_s.store g_s = .some HasBool.tt → ρ_h.eval ρ_h.store g_h = .some HasBool.tt)
    (h_wfb_transport : ∀ (ρ_s ρ_h : Env P),
       ρ_s.eval = ρ_h.eval → WellFormedSemanticEvalBool ρ_s.eval →
       WellFormedSemanticEvalBool ρ_h.eval)
    (body_sim : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store →
       ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
       (∀ y ∈ B, ρ_h.store y ≠ none) →
       (∀ y ∈ Vs, ρ_s.store y = none) → (∀ y ∈ Vh, ρ_h.store y = none) →
       (∀ str : String, Q str →
          str ∉ StringGenState.stringGens σ_sf → ρ_s.store (HasIdent.ident (P := P) str) = none) →
       (∀ (ρ_s' : Env P),
         StepStmtStar P (EvalCmd P) extendEval (.stmts body_src ρ_s) (.terminal ρ_s') →
         ∃ ρ_h' : Env P,
           StepStmtStar P (EvalCmd P) extendEval (.stmts body_h ρ_h) (.terminal ρ_h') ∧
           HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
           ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none))
       ∧
       (∀ (l : String) (ρ_s' : Env P),
         StepStmtStar P (EvalCmd P) extendEval (.stmts body_src ρ_s) (.exiting l ρ_s') →
         ∃ ρ_h' : Env P,
           StepStmtStar P (EvalCmd P) extendEval (.stmts body_h ρ_h) (.exiting l ρ_h') ∧
           HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
           ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none)))
    (h_src_body_nofd : Block.noFuncDecl body_src = true)
    (h_h_body_nofd : Block.noFuncDecl body_h = true) :
    ∀ (n : Nat) {ρ_src ρ_hoist ρ_post : Env P} {label : String},
      HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store →
      ρ_src.eval = ρ_hoist.eval → ρ_src.hasFailure = ρ_hoist.hasFailure →
      (∀ y ∈ B, ρ_hoist.store y ≠ none) →
      (∀ y ∈ Vs, ρ_src.store y = none) → (∀ y ∈ Vh, ρ_hoist.store y = none) →
      (∀ str : String, Q str →
         str ∉ StringGenState.stringGens σ_sf → ρ_src.store (HasIdent.ident (P := P) str) = none) →
      (h_run : ReflTransT (StepStmt P (EvalCmd P) extendEval)
        (.stmt (.loop (.det g_s) none [] body_src md_s) ρ_src) (.exiting label ρ_post)) →
      h_run.len ≤ n →
      ∃ ρ_post_h : Env P,
        StepStmtStar P (EvalCmd P) extendEval
          (.stmt (.loop (.det g_h) none [] body_h md_h) ρ_hoist) (.exiting label ρ_post_h) ∧
        HoistInv (P := P) A B subst ρ_post.store ρ_post_h.store ∧
        ρ_post.hasFailure = ρ_post_h.hasFailure ∧
        (∀ y ∈ B, ρ_post_h.store y ≠ none) := by
  intro n
  induction n with
  | zero =>
    intro ρ_src ρ_hoist ρ_post label _ _ _ _ _ _ _ h_run hlen
    match h_run with
    | .step _ _ _ _ _ => simp [ReflTransT.len] at hlen
  | succ n ih =>
    intro ρ_src ρ_hoist ρ_post label h_hinv h_eval h_hf h_bound h_Vs h_Vh h_src_sf h_run hlen
    match h_run with
    | .step _ _ _ step hrest =>
      cases step with
      | step_loop_exit ht hinv hiff hwf =>
        -- A `.terminal` target; `hrest : .terminal … →* .exiting …` is impossible.
        match hrest with
        | .step _ _ _ hd _ => exact nomatch hd
      | step_loop_enter ht hinv hiff hwf =>
        rename_i hasInvFailure
        have h_hif_false : hasInvFailure = false := by
          cases h_hif : hasInvFailure with
          | false => rfl
          | true => obtain ⟨le, hle_mem, _⟩ := hiff.mp h_hif; simp at hle_mem
        subst h_hif_false
        let ρ_src_body : Env P := { ρ_src with hasFailure := ρ_src.hasFailure || false }
        let ρ_h_body : Env P := { ρ_hoist with hasFailure := ρ_hoist.hasFailure || false }
        have h_hinv_body : HoistInv (P := P) A B subst ρ_src_body.store ρ_h_body.store := by
          show HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store; exact h_hinv
        have h_eval_body : ρ_src_body.eval = ρ_h_body.eval := h_eval
        have h_hf_body : ρ_src_body.hasFailure = ρ_h_body.hasFailure := by
          show (ρ_src.hasFailure || false) = (ρ_hoist.hasFailure || false); simp [h_hf]
        have h_bound_body : ∀ y ∈ B, ρ_h_body.store y ≠ none := h_bound
        have h_Vs_body : ∀ y ∈ Vs, ρ_src_body.store y = none := h_Vs
        have h_Vh_body : ∀ y ∈ Vh, ρ_h_body.store y = none := h_Vh
        have h_src_sf_body : ∀ str : String, Q str →
            str ∉ StringGenState.stringGens σ_sf →
            ρ_src_body.store (HasIdent.ident (P := P) str) = none := h_src_sf
        have h_guard_h : ρ_hoist.eval ρ_hoist.store g_h = .some HasBool.tt :=
          h_guard_transport ρ_src ρ_hoist h_hinv h_eval ht
        have h_wfb_h : WellFormedSemanticEvalBool ρ_hoist.eval :=
          h_wfb_transport ρ_src ρ_hoist h_eval hwf
        -- Decompose the seq run to `.exiting`: either this iteration's block exits
        -- (inl), or it terminates and the recursive loop exits (inr).
        rcases seqT_reaches_exiting' hrest with ⟨h_block_exit, hl⟩ | ⟨ρ₁, h_block_term, h_loop_stmts, hl⟩
        · -- inl: this iteration's body exits with `label`.
          obtain ⟨ρ_inner, h_body_exit_T, h_ρpost_eq, hl2⟩ := blockT_none_reaches_exiting' h_block_exit
          obtain ⟨ρ_h_inner, h_body_h_exit, h_hinv_inner, h_hf_inner, h_bound_inner⟩ :=
            (body_sim ρ_src_body ρ_h_body h_hinv_body h_eval_body h_hf_body h_bound_body
              h_Vs_body h_Vh_body h_src_sf_body).2
              label ρ_inner (reflTransT_to_prop h_body_exit_T)
          refine ⟨{ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store }, ?_, ?_, ?_, ?_⟩
          · refine ReflTrans.step _ _ _
              (.step_loop_enter (hasInvFailure := false)
                h_guard_h (by intro le hle; simp at hle) (by simp) h_wfb_h) ?_
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendEval _ _ _
                (block_inner_star P (EvalCmd P) extendEval _ _ (none : Option String) ρ_hoist.store
                  (show StepStmtStar P (EvalCmd P) extendEval
                      (.stmts body_h { ρ_hoist with hasFailure := ρ_hoist.hasFailure || false })
                      (.exiting label ρ_h_inner) from h_body_h_exit))) ?_
            refine ReflTrans.step _ _ _ (.step_seq_inner (.step_block_exit_mismatch ?_)) ?_
            · exact (by simp)
            · exact ReflTrans.step _ _ _ .step_seq_exit (.refl _)
          · subst h_ρpost_eq
            exact HoistInv.project_both h_hinv h_hinv_inner
          · subst h_ρpost_eq
            show ρ_inner.hasFailure = ρ_h_inner.hasFailure; exact h_hf_inner
          · intro y hy
            show projectStore ρ_hoist.store ρ_h_inner.store y ≠ none
            unfold projectStore
            have h_parent_some : (ρ_hoist.store y).isSome = true := by
              cases h : ρ_hoist.store y with
              | none => exact absurd h (h_bound y hy)
              | some _ => rfl
            rw [h_parent_some]; simp; exact h_bound_inner y hy
        · -- inr: this iteration's body terminates; recurse on the inner loop.
          obtain ⟨ρ_inner, h_body_term_T, h_ρ_block_eq, hl_blk⟩ := blockT_none_reaches_terminal h_block_term
          subst h_ρ_block_eq
          obtain ⟨ρ_h_inner, h_body_h_run, h_hinv_inner, h_hf_inner, h_bound_inner⟩ :=
            (body_sim ρ_src_body ρ_h_body h_hinv_body h_eval_body h_hf_body h_bound_body
              h_Vs_body h_Vh_body h_src_sf_body).1
              ρ_inner (reflTransT_to_prop h_body_term_T)
          have h_hoist_iter : StepStmtStar P (EvalCmd P) extendEval
              (.stmt (.loop (.det g_h) none [] body_h md_h) ρ_hoist)
              (.stmts [.loop (.det g_h) none [] body_h md_h]
                { ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store }) := by
            have hb : StepStmtStar P (EvalCmd P) extendEval
                (.stmts body_h ρ_h_body) (.terminal ρ_h_inner) := h_body_h_run
            have := buildLoopIterationDet (g := g_h) (body := body_h) (md := md_h)
              (ρ_pre := ρ_h_body) (ρ_body := ρ_h_inner) ?_ ?_ hb
            · simpa [ρ_h_body] using this
            · show ρ_h_body.eval ρ_h_body.store g_h = .some HasBool.tt
              show ρ_hoist.eval ρ_hoist.store g_h = .some HasBool.tt; exact h_guard_h
            · show WellFormedSemanticEvalBool ρ_h_body.eval
              show WellFormedSemanticEvalBool ρ_hoist.eval; exact h_wfb_h
          have h_hinv_block : HoistInv (P := P) A B subst
              (projectStore ρ_src.store ρ_inner.store)
              (projectStore ρ_hoist.store ρ_h_inner.store) :=
            HoistInv.project_both h_hinv h_hinv_inner
          have h_eval_block : ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P).eval
              = ({ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store } : Env P).eval := by
            show ρ_inner.eval = ρ_h_inner.eval
            have e1 : ρ_inner.eval = ρ_src_body.eval :=
              smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
                body_src ρ_src_body ρ_inner h_src_body_nofd (reflTransT_to_prop h_body_term_T)
            have e2 : ρ_h_inner.eval = ρ_h_body.eval :=
              smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
                body_h ρ_h_body ρ_h_inner h_h_body_nofd h_body_h_run
            rw [e1, e2]; exact h_eval_body
          have h_hf_block : ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P).hasFailure
              = ({ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store } : Env P).hasFailure := by
            show ρ_inner.hasFailure = ρ_h_inner.hasFailure; exact h_hf_inner
          have h_bound_block : ∀ y ∈ B,
              ({ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store } : Env P).store y ≠ none := by
            intro y hy
            show projectStore ρ_hoist.store ρ_h_inner.store y ≠ none
            unfold projectStore
            have h_parent_some : (ρ_hoist.store y).isSome = true := by
              cases h : ρ_hoist.store y with
              | none => exact absurd h (h_bound y hy)
              | some _ => rfl
            rw [h_parent_some]; simp; exact h_bound_inner y hy
          have h_Vs_block : ∀ y ∈ Vs,
              ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P).store y = none := by
            intro y hy; show projectStore ρ_src.store ρ_inner.store y = none
            exact projectStore_undef_at (h_Vs y hy)
          have h_Vh_block : ∀ y ∈ Vh,
              ({ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store } : Env P).store y = none := by
            intro y hy; show projectStore ρ_hoist.store ρ_h_inner.store y = none
            exact projectStore_undef_at (h_Vh y hy)
          have h_src_sf_block : ∀ str : String, Q str →
              str ∉ StringGenState.stringGens σ_sf →
              ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P).store
                (HasIdent.ident (P := P) str) = none := by
            intro str h_suf h_notσ
            show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) str) = none
            exact projectStore_undef_at (h_src_sf str h_suf h_notσ)
          rcases stmtsT_cons_exiting' h_loop_stmts with ⟨h_inner_loop_T, _⟩ | ⟨ρ₂, _, h_nil, _⟩
          · obtain ⟨ρ_post_h, h_post_h_run, h_hinv_post, h_hf_post, h_bound_post⟩ :=
              ih h_hinv_block h_eval_block h_hf_block h_bound_block h_Vs_block h_Vh_block
                h_src_sf_block h_inner_loop_T
                (by simp only [ReflTransT.len] at hlen; omega)
            refine ⟨ρ_post_h, ?_, h_hinv_post, h_hf_post, h_bound_post⟩
            refine ReflTrans_Transitive _ _ _ _ h_hoist_iter ?_
            refine ReflTrans.step _ _ _ .step_stmts_cons ?_
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendEval _ _ _ h_post_h_run) ?_
            exact ReflTrans.step _ _ _ .step_seq_exit (.refl _)
          · match h_nil with
            | .step _ _ _ .step_stmts_nil hr2 =>
              match hr2 with
              | .step _ _ _ hd _ => exact nomatch hd

/-- Prop-level wrapper of `loopDet_lift_sf_2g_undef_E_fuel` specialised to the
single-guard diagonal `g_s = g_h = g` (the shape the §E `.loop` arm produces:
the loop guard is UNCHANGED by the hoist pass).  The EXITING-target analogue of
`loopDet_lift_sf_undef_recovers_single`. -/
public theorem loopDet_lift_sf_undef_E_recovers_single [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {Q : String → Prop}
    {g : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {Vs Vh : List P.Ident} {σ_sf : StringGenState}
    (h_guard_transport : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
       ρ_s.eval ρ_s.store g = .some HasBool.tt → ρ_h.eval ρ_h.store g = .some HasBool.tt)
    (h_wfb_transport : ∀ (ρ_s ρ_h : Env P),
       ρ_s.eval = ρ_h.eval → WellFormedSemanticEvalBool ρ_s.eval →
       WellFormedSemanticEvalBool ρ_h.eval)
    (body_sim : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store →
       ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
       (∀ y ∈ B, ρ_h.store y ≠ none) →
       (∀ y ∈ Vs, ρ_s.store y = none) → (∀ y ∈ Vh, ρ_h.store y = none) →
       (∀ str : String, Q str →
          str ∉ StringGenState.stringGens σ_sf → ρ_s.store (HasIdent.ident (P := P) str) = none) →
       (∀ (ρ_s' : Env P),
         StepStmtStar P (EvalCmd P) extendEval (.stmts body_src ρ_s) (.terminal ρ_s') →
         ∃ ρ_h' : Env P,
           StepStmtStar P (EvalCmd P) extendEval (.stmts body_h ρ_h) (.terminal ρ_h') ∧
           HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
           ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none))
       ∧
       (∀ (l : String) (ρ_s' : Env P),
         StepStmtStar P (EvalCmd P) extendEval (.stmts body_src ρ_s) (.exiting l ρ_s') →
         ∃ ρ_h' : Env P,
           StepStmtStar P (EvalCmd P) extendEval (.stmts body_h ρ_h) (.exiting l ρ_h') ∧
           HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
           ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none)))
    (h_src_body_nofd : Block.noFuncDecl body_src = true)
    (h_h_body_nofd : Block.noFuncDecl body_h = true)
    {ρ_src ρ_hoist ρ_post : Env P} {label : String}
    (h_hinv : HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store)
    (h_eval : ρ_src.eval = ρ_hoist.eval) (h_hf : ρ_src.hasFailure = ρ_hoist.hasFailure)
    (h_bound : ∀ y ∈ B, ρ_hoist.store y ≠ none)
    (h_Vs : ∀ y ∈ Vs, ρ_src.store y = none) (h_Vh : ∀ y ∈ Vh, ρ_hoist.store y = none)
    (h_src_sf : ∀ str : String, Q str →
       str ∉ StringGenState.stringGens σ_sf → ρ_src.store (HasIdent.ident (P := P) str) = none)
    (h_run : StepStmtStar P (EvalCmd P) extendEval
        (.stmt (.loop (.det g) none [] body_src md_s) ρ_src) (.exiting label ρ_post)) :
    ∃ ρ_post_h : Env P,
      StepStmtStar P (EvalCmd P) extendEval
        (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist) (.exiting label ρ_post_h) ∧
      HoistInv (P := P) A B subst ρ_post.store ρ_post_h.store ∧
      ρ_post.hasFailure = ρ_post_h.hasFailure ∧
      (∀ y ∈ B, ρ_post_h.store y ≠ none) :=
  loopDet_lift_sf_2g_undef_E_fuel (g_s := g) (g_h := g)
    h_guard_transport h_wfb_transport body_sim h_src_body_nofd h_h_body_nofd
    (reflTrans_to_T h_run).len h_hinv h_eval h_hf h_bound h_Vs h_Vh h_src_sf
    (reflTrans_to_T h_run) (Nat.le_refl _)

/-- **The sum-typed shapefree-carrying two-guard TERMINAL-target fuel recursion.**

The TERMINAL analogue of `loopDet_lift_sf_2g_undef_E_fuel`: like
`loopDet_lift_sf_2g_undef_fuel` but DROPS `h_src_body_no_exit` and consumes the
sum-typed `BodySimUSFSum`-shaped `body_sim`.  A source loop run reaching `.terminal
ρ_post` means NO iteration's body broke (a body `.exit` would propagate the loop
to `.exiting`, not `.terminal`); so each peeled iteration's `.block .none` reaches
`.terminal` via `blockT_none_reaches_terminal` (which recovers the body's TERMINAL
run WITHOUT a no-exit hypothesis), the body's TERMINAL clause drives one hoist
iteration, and the recursion handles the residual loop.  The `Vs`/`Vh`/`σ_sf`
carriers are re-established at each projected iteration store exactly as in
`loopDet_lift_sf_2g_undef_fuel`. -/
public theorem loopDet_lift_sf_2g_undef_TE_fuel [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {Q : String → Prop}
    {g_s g_h : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {Vs Vh : List P.Ident} {σ_sf : StringGenState}
    (h_guard_transport : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
       ρ_s.eval ρ_s.store g_s = .some HasBool.tt → ρ_h.eval ρ_h.store g_h = .some HasBool.tt)
    (h_guard_transport_ff : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
       ρ_s.eval ρ_s.store g_s = .some HasBool.ff → ρ_h.eval ρ_h.store g_h = .some HasBool.ff)
    (h_wfb_transport : ∀ (ρ_s ρ_h : Env P),
       ρ_s.eval = ρ_h.eval → WellFormedSemanticEvalBool ρ_s.eval →
       WellFormedSemanticEvalBool ρ_h.eval)
    (body_sim : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store →
       ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
       (∀ y ∈ B, ρ_h.store y ≠ none) →
       (∀ y ∈ Vs, ρ_s.store y = none) → (∀ y ∈ Vh, ρ_h.store y = none) →
       (∀ str : String, Q str →
          str ∉ StringGenState.stringGens σ_sf → ρ_s.store (HasIdent.ident (P := P) str) = none) →
       (∀ (ρ_s' : Env P),
         StepStmtStar P (EvalCmd P) extendEval (.stmts body_src ρ_s) (.terminal ρ_s') →
         ∃ ρ_h' : Env P,
           StepStmtStar P (EvalCmd P) extendEval (.stmts body_h ρ_h) (.terminal ρ_h') ∧
           HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
           ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none))
       ∧
       (∀ (l : String) (ρ_s' : Env P),
         StepStmtStar P (EvalCmd P) extendEval (.stmts body_src ρ_s) (.exiting l ρ_s') →
         ∃ ρ_h' : Env P,
           StepStmtStar P (EvalCmd P) extendEval (.stmts body_h ρ_h) (.exiting l ρ_h') ∧
           HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
           ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none)))
    (h_src_body_nofd : Block.noFuncDecl body_src = true)
    (h_h_body_nofd : Block.noFuncDecl body_h = true) :
    ∀ (n : Nat) {ρ_src ρ_hoist ρ_post : Env P},
      HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store →
      ρ_src.eval = ρ_hoist.eval → ρ_src.hasFailure = ρ_hoist.hasFailure →
      (∀ y ∈ B, ρ_hoist.store y ≠ none) →
      (∀ y ∈ Vs, ρ_src.store y = none) → (∀ y ∈ Vh, ρ_hoist.store y = none) →
      (∀ str : String, Q str →
         str ∉ StringGenState.stringGens σ_sf → ρ_src.store (HasIdent.ident (P := P) str) = none) →
      (h_run : ReflTransT (StepStmt P (EvalCmd P) extendEval)
        (.stmt (.loop (.det g_s) none [] body_src md_s) ρ_src) (.terminal ρ_post)) →
      h_run.len ≤ n →
      ∃ ρ_post_h : Env P,
        StepStmtStar P (EvalCmd P) extendEval
          (.stmt (.loop (.det g_h) none [] body_h md_h) ρ_hoist) (.terminal ρ_post_h) ∧
        HoistInv (P := P) A B subst ρ_post.store ρ_post_h.store ∧
        ρ_post.hasFailure = ρ_post_h.hasFailure ∧
        (∀ y ∈ B, ρ_post_h.store y ≠ none) := by
  intro n
  induction n with
  | zero =>
    intro ρ_src ρ_hoist ρ_post _ _ _ _ _ _ _ h_run hlen
    match h_run with
    | .step _ _ _ _ _ => simp [ReflTransT.len] at hlen
  | succ n ih =>
    intro ρ_src ρ_hoist ρ_post h_hinv h_eval h_hf h_bound h_Vs h_Vh h_src_sf h_run hlen
    match h_run with
    | .step _ _ _ step hrest =>
      cases step with
      | step_loop_exit ht hinv hiff hwf =>
        rename_i hasInvFailure
        have h_hif_false : hasInvFailure = false := by
          cases h_hif : hasInvFailure with
          | false => rfl
          | true => obtain ⟨le, hle_mem, _⟩ := hiff.mp h_hif; simp at hle_mem
        have h_ρ_post_eq : ρ_post = { ρ_src with hasFailure := ρ_src.hasFailure || hasInvFailure } := by
          match hrest with
          | .refl _ => rfl
          | .step _ _ _ hd _ => exact nomatch hd
        subst h_ρ_post_eq
        subst h_hif_false
        have h_guard_h : ρ_hoist.eval ρ_hoist.store g_h = .some HasBool.ff :=
          h_guard_transport_ff ρ_src ρ_hoist h_hinv h_eval ht
        have h_wfb_h : WellFormedSemanticEvalBool ρ_hoist.eval :=
          h_wfb_transport ρ_src ρ_hoist h_eval hwf
        refine ⟨{ ρ_hoist with hasFailure := ρ_hoist.hasFailure || false }, ?_, ?_, ?_, ?_⟩
        · exact .step _ _ _
            (.step_loop_exit h_guard_h (by intro le hle; simp at hle) (by simp) h_wfb_h)
            (.refl _)
        · simpa using h_hinv
        · show (ρ_src.hasFailure || false) = (ρ_hoist.hasFailure || false); simp [h_hf]
        · intro y hy; show ρ_hoist.store y ≠ none; exact h_bound y hy
      | step_loop_enter ht hinv hiff hwf =>
        rename_i hasInvFailure
        have h_hif_false : hasInvFailure = false := by
          cases h_hif : hasInvFailure with
          | false => rfl
          | true => obtain ⟨le, hle_mem, _⟩ := hiff.mp h_hif; simp at hle_mem
        subst h_hif_false
        obtain ⟨ρ_block, h_block_term, h_loop_stmts, hlen_seq⟩ :=
          seqT_reaches_terminal extendEval hrest
        obtain ⟨ρ_inner, h_body_src_T, h_ρ_block_eq, hlen_block⟩ :=
          blockT_none_reaches_terminal h_block_term
        subst h_ρ_block_eq
        obtain ⟨ρ_x, h_loop_T, h_nil, hlen_cons⟩ :=
          stmtsT_cons_terminal extendEval h_loop_stmts
        have hρ_x_eq : ρ_x = ρ_post := by
          match h_nil with
          | .step _ _ _ .step_stmts_nil hr2 =>
            match hr2 with
            | .refl _ => rfl
            | .step _ _ _ h _ => exact nomatch h
        subst hρ_x_eq
        let ρ_src_body : Env P := { ρ_src with hasFailure := ρ_src.hasFailure || false }
        let ρ_h_body : Env P := { ρ_hoist with hasFailure := ρ_hoist.hasFailure || false }
        have h_hinv_body : HoistInv (P := P) A B subst ρ_src_body.store ρ_h_body.store := by
          show HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store; exact h_hinv
        have h_eval_body : ρ_src_body.eval = ρ_h_body.eval := h_eval
        have h_hf_body : ρ_src_body.hasFailure = ρ_h_body.hasFailure := by
          show (ρ_src.hasFailure || false) = (ρ_hoist.hasFailure || false); simp [h_hf]
        have h_bound_body : ∀ y ∈ B, ρ_h_body.store y ≠ none := h_bound
        have h_Vs_body : ∀ y ∈ Vs, ρ_src_body.store y = none := h_Vs
        have h_Vh_body : ∀ y ∈ Vh, ρ_h_body.store y = none := h_Vh
        have h_src_sf_body : ∀ str : String, Q str →
            str ∉ StringGenState.stringGens σ_sf →
            ρ_src_body.store (HasIdent.ident (P := P) str) = none := h_src_sf
        obtain ⟨ρ_h_inner, h_body_h_run, h_hinv_inner, h_hf_inner, h_bound_inner⟩ :=
          (body_sim ρ_src_body ρ_h_body h_hinv_body h_eval_body h_hf_body h_bound_body
            h_Vs_body h_Vh_body h_src_sf_body).1
            ρ_inner (reflTransT_to_prop h_body_src_T)
        have h_guard_h : ρ_hoist.eval ρ_hoist.store g_h = .some HasBool.tt :=
          h_guard_transport ρ_src ρ_hoist h_hinv h_eval ht
        have h_wfb_h : WellFormedSemanticEvalBool ρ_hoist.eval :=
          h_wfb_transport ρ_src ρ_hoist h_eval hwf
        have h_hoist_iter : StepStmtStar P (EvalCmd P) extendEval
            (.stmt (.loop (.det g_h) none [] body_h md_h) ρ_hoist)
            (.stmts [.loop (.det g_h) none [] body_h md_h]
              { ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store }) := by
          have hb : StepStmtStar P (EvalCmd P) extendEval
              (.stmts body_h ρ_h_body) (.terminal ρ_h_inner) := h_body_h_run
          have := buildLoopIterationDet (g := g_h) (body := body_h) (md := md_h)
            (ρ_pre := ρ_h_body) (ρ_body := ρ_h_inner) ?_ ?_ hb
          · simpa [ρ_h_body] using this
          · show ρ_h_body.eval ρ_h_body.store g_h = .some HasBool.tt
            show ρ_hoist.eval ρ_hoist.store g_h = .some HasBool.tt; exact h_guard_h
          · show WellFormedSemanticEvalBool ρ_h_body.eval
            show WellFormedSemanticEvalBool ρ_hoist.eval; exact h_wfb_h
        have h_hinv_block : HoistInv (P := P) A B subst
            (projectStore ρ_src.store ρ_inner.store)
            (projectStore ρ_hoist.store ρ_h_inner.store) :=
          HoistInv.project_both h_hinv h_hinv_inner
        have h_eval_block : ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P).eval
            = ({ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store } : Env P).eval := by
          show ρ_inner.eval = ρ_h_inner.eval
          have e1 : ρ_inner.eval = ρ_src_body.eval :=
            smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
              body_src ρ_src_body ρ_inner h_src_body_nofd (reflTransT_to_prop h_body_src_T)
          have e2 : ρ_h_inner.eval = ρ_h_body.eval :=
            smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
              body_h ρ_h_body ρ_h_inner h_h_body_nofd h_body_h_run
          rw [e1, e2]; exact h_eval_body
        have h_hf_block : ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P).hasFailure
            = ({ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store } : Env P).hasFailure := by
          show ρ_inner.hasFailure = ρ_h_inner.hasFailure; exact h_hf_inner
        have h_bound_block : ∀ y ∈ B,
            ({ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store } : Env P).store y ≠ none := by
          intro y hy
          show projectStore ρ_hoist.store ρ_h_inner.store y ≠ none
          unfold projectStore
          have h_parent_some : (ρ_hoist.store y).isSome = true := by
            cases h : ρ_hoist.store y with
            | none => exact absurd h (h_bound y hy)
            | some _ => rfl
          rw [h_parent_some]; simp; exact h_bound_inner y hy
        have h_Vs_block : ∀ y ∈ Vs,
            ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P).store y = none := by
          intro y hy; show projectStore ρ_src.store ρ_inner.store y = none
          exact projectStore_undef_at (h_Vs y hy)
        have h_Vh_block : ∀ y ∈ Vh,
            ({ ρ_h_inner with store := projectStore ρ_hoist.store ρ_h_inner.store } : Env P).store y = none := by
          intro y hy; show projectStore ρ_hoist.store ρ_h_inner.store y = none
          exact projectStore_undef_at (h_Vh y hy)
        have h_src_sf_block : ∀ str : String, Q str →
            str ∉ StringGenState.stringGens σ_sf →
            ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P).store
              (HasIdent.ident (P := P) str) = none := by
          intro str h_suf h_notσ
          show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) str) = none
          exact projectStore_undef_at (h_src_sf str h_suf h_notσ)
        obtain ⟨ρ_post_h, h_post_h_run, h_hinv_post, h_hf_post, h_bound_post⟩ :=
          ih h_hinv_block h_eval_block h_hf_block h_bound_block h_Vs_block h_Vh_block
            h_src_sf_block h_loop_T
            (by simp only [ReflTransT.len] at hlen; omega)
        refine ⟨ρ_post_h, ?_, h_hinv_post, h_hf_post, h_bound_post⟩
        refine ReflTrans_Transitive _ _ _ _ h_hoist_iter ?_
        refine ReflTrans.step _ _ _ .step_stmts_cons ?_
        refine ReflTrans_Transitive _ _ _ _
          (seq_inner_star P (EvalCmd P) extendEval _ _ _ h_post_h_run) ?_
        exact ReflTrans.step _ _ _ .step_seq_done
          (ReflTrans.step _ _ _ .step_stmts_nil (.refl _))

/-- Prop-level wrapper of `loopDet_lift_sf_2g_undef_TE_fuel` specialised to the
single-guard diagonal `g_s = g_h = g`.  The TERMINAL-target analogue of
`loopDet_lift_sf_undef_E_recovers_single` (consumes the sum-typed
`BodySimUSFSum`-shaped `body_sim`, no `h_src_body_no_exit`). -/
public theorem loopDet_lift_sf_undef_TE_recovers_single [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasIdent P] [HasSubstFvar P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {extendEval : ExtendEval P}
    {Q : String → Prop}
    {g : P.Expr} {body_src body_h : List (Stmt P (Cmd P))} {md_s md_h : MetaData P}
    {A B : List P.Ident} {subst : List (P.Ident × P.Ident)}
    {Vs Vh : List P.Ident} {σ_sf : StringGenState}
    (h_guard_transport : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
       ρ_s.eval ρ_s.store g = .some HasBool.tt → ρ_h.eval ρ_h.store g = .some HasBool.tt)
    (h_guard_transport_ff : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store → ρ_s.eval = ρ_h.eval →
       ρ_s.eval ρ_s.store g = .some HasBool.ff → ρ_h.eval ρ_h.store g = .some HasBool.ff)
    (h_wfb_transport : ∀ (ρ_s ρ_h : Env P),
       ρ_s.eval = ρ_h.eval → WellFormedSemanticEvalBool ρ_s.eval →
       WellFormedSemanticEvalBool ρ_h.eval)
    (body_sim : ∀ (ρ_s ρ_h : Env P),
       HoistInv (P := P) A B subst ρ_s.store ρ_h.store →
       ρ_s.eval = ρ_h.eval → ρ_s.hasFailure = ρ_h.hasFailure →
       (∀ y ∈ B, ρ_h.store y ≠ none) →
       (∀ y ∈ Vs, ρ_s.store y = none) → (∀ y ∈ Vh, ρ_h.store y = none) →
       (∀ str : String, Q str →
          str ∉ StringGenState.stringGens σ_sf → ρ_s.store (HasIdent.ident (P := P) str) = none) →
       (∀ (ρ_s' : Env P),
         StepStmtStar P (EvalCmd P) extendEval (.stmts body_src ρ_s) (.terminal ρ_s') →
         ∃ ρ_h' : Env P,
           StepStmtStar P (EvalCmd P) extendEval (.stmts body_h ρ_h) (.terminal ρ_h') ∧
           HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
           ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none))
       ∧
       (∀ (l : String) (ρ_s' : Env P),
         StepStmtStar P (EvalCmd P) extendEval (.stmts body_src ρ_s) (.exiting l ρ_s') →
         ∃ ρ_h' : Env P,
           StepStmtStar P (EvalCmd P) extendEval (.stmts body_h ρ_h) (.exiting l ρ_h') ∧
           HoistInv (P := P) A B subst ρ_s'.store ρ_h'.store ∧
           ρ_s'.hasFailure = ρ_h'.hasFailure ∧ (∀ y ∈ B, ρ_h'.store y ≠ none)))
    (h_src_body_nofd : Block.noFuncDecl body_src = true)
    (h_h_body_nofd : Block.noFuncDecl body_h = true)
    {ρ_src ρ_hoist ρ_post : Env P}
    (h_hinv : HoistInv (P := P) A B subst ρ_src.store ρ_hoist.store)
    (h_eval : ρ_src.eval = ρ_hoist.eval) (h_hf : ρ_src.hasFailure = ρ_hoist.hasFailure)
    (h_bound : ∀ y ∈ B, ρ_hoist.store y ≠ none)
    (h_Vs : ∀ y ∈ Vs, ρ_src.store y = none) (h_Vh : ∀ y ∈ Vh, ρ_hoist.store y = none)
    (h_src_sf : ∀ str : String, Q str →
       str ∉ StringGenState.stringGens σ_sf → ρ_src.store (HasIdent.ident (P := P) str) = none)
    (h_run : StepStmtStar P (EvalCmd P) extendEval
        (.stmt (.loop (.det g) none [] body_src md_s) ρ_src) (.terminal ρ_post)) :
    ∃ ρ_post_h : Env P,
      StepStmtStar P (EvalCmd P) extendEval
        (.stmt (.loop (.det g) none [] body_h md_h) ρ_hoist) (.terminal ρ_post_h) ∧
      HoistInv (P := P) A B subst ρ_post.store ρ_post_h.store ∧
      ρ_post.hasFailure = ρ_post_h.hasFailure ∧
      (∀ y ∈ B, ρ_post_h.store y ≠ none) :=
  loopDet_lift_sf_2g_undef_TE_fuel (g_s := g) (g_h := g)
    h_guard_transport h_guard_transport_ff h_wfb_transport body_sim h_src_body_nofd h_h_body_nofd
    (reflTrans_to_T h_run).len h_hinv h_eval h_hf h_bound h_Vs h_Vh h_src_sf
    (reflTrans_to_T h_run) (Nat.le_refl _)



/-! ## Step J: restrict the union-carrier `HoistInv` back to the ambient carriers.

The loop driver delivers `HoistInv (A++As)(B++Bs)(subst++ss) ρ_post ρ_post_h` at
the union carriers; the §E `.loop` arm needs it at the ambient `A B subst`.
Under the GUARDED frame this restriction is SOUND: the fresh sources/targets
`As`/`Bs` are undefined in the source loop post-store `ρ_post` (they are body
inits / generator names absent from the source store — see
`loopDet_preserves_none`), so the guarded ambient frame, whose obligation only
fires at `ρ_post x ≠ none`, never applies to them and the union frame covers
every remaining variable.  The pairing restricts directly (`subst ⊆ subst++ss`). -/
public theorem stepJ_restrict
    {A B As Bs : List P.Ident} {subst ss : List (P.Ident × P.Ident)}
    {ρ_post ρ_post_h : Env P}
    (h_hinv : HoistInv (P := P) (A ++ As) (B ++ Bs) (subst ++ ss) ρ_post.store ρ_post_h.store)
    (h_post_As_none : ∀ x ∈ As, ρ_post.store x = none)
    (h_post_Bs_none : ∀ x ∈ Bs, ρ_post.store x = none) :
    HoistInv (P := P) A B subst ρ_post.store ρ_post_h.store := by
  refine ⟨?_, ?_⟩
  · intro x hxA hxB h_x_ne
    have hxAs : x ∉ As := fun h => h_x_ne (h_post_As_none x h)
    have hxBs : x ∉ Bs := fun h => h_x_ne (h_post_Bs_none x h)
    refine h_hinv.1 x ?_ ?_ h_x_ne
    · intro h; rcases List.mem_append.mp h with h | h
      · exact hxA h
      · exact hxAs h
    · intro h; rcases List.mem_append.mp h with h | h
      · exact hxB h
      · exact hxBs h
  · intro a b h_pair h_ne
    exact h_hinv.2 a b (List.mem_append.mpr (Or.inl h_pair)) h_ne

end LoopInitHoistLoopDriver
end Imperative

end -- public section
