/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BigStep.SemProps
public import Strata.DL.Imperative.StmtSemanticsProps
public import Strata.DL.Imperative.StmtProps
import all Strata.DL.Imperative.StmtSemantics

/-! # The big-step semantics against the reference event semantics

A big-step run or reach (`BRun`/`BReach`, `BigStep.Sem`) gives a small-step run of
`StepStmtStarE` over `EvalE` (the event semantics of commands, no calls) with the same
trace (`brun_star`, `breach_star`).  Consequently a big-step failure (`Fails`) is a
failure under the reference event semantics (`fails_failsE`).  Conversely, a small-step run
emitting a nonempty trace is a big-step reach with that trace (`star_breach`), a small-step run
to a terminal or exiting configuration is a big-step run (`star_brun`), and a failure under the
reference event semantics is a big-step failure (`failsE_fails`).  A small-step run emitting
an event has a prefix ending at that event (`star_prefix`).

Key theorems: `brun_star`, `breach_star`, `fails_failsE`, `star_breach`, `star_brun`,
`failsE_fails`, `star_prefix`.

Key definitions: `FailsE`, `CRun`, `CReach`. -/

namespace Imperative
namespace BigStep

public section

variable {P : PureExpr} [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
  [HasBool P] [HasFvar P] [HasBoolOps P]

/-- The configuration a big-step outcome ends in. -/
@[expose] def oCfg (F : P.Factory) : (Outcome P) → Config P (CmdExt P)
  | .normal σ => .terminal { store := σ, factory := F }
  | .exit l σ => .exiting l { store := σ, factory := F }

variable {F : P.Factory}

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasBoolOps P] in
/-- An administrative step (no event) followed by a run is a run. -/
private theorem star_admin {a b c : Config P (CmdExt P)} {t : List (Event P)}
    (h1 : StepStmtE P EvalE a [] b) (h2 : StepStmtStarE P EvalE b t c) :
    StepStmtStarE P EvalE a t c := by
  simpa using ReflTransTrace.step _ _ _ _ _ h1 h2

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasBoolOps P] in
/-- Leaving a scope (an `ite` branch or a block) with the outcome of its body. -/
private theorem star_block_exit {σp : SemanticStore P} (lb : Option String)
    (o : (Outcome P)) :
    StepStmtStarE P EvalE (.block lb σp (oCfg F o)) []
      (oCfg F (match lb with
        | none => o.proj σp
        | some l => o.block l σp)) := by
  cases o with
  | normal σ =>
    cases lb <;> exact star_admin .step_block_done (.refl _)
  | exit l' σ =>
    cases lb with
    | none =>
      exact star_admin (.step_block_exit_mismatch (by simp)) (.refl _)
    | some l =>
      simp only [Outcome.block]
      split
      next h => exact star_admin (.step_block_exit_match (h ▸ rfl)) (.refl _)
      next h =>
        exact star_admin (.step_block_exit_mismatch (by simpa [eq_comm] using h)) (.refl _)

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasBoolOps P] in
/-- A run of the body of a scope (an `ite` branch, or a block labelled `lb`) to the
    configuration of outcome `o` is a run of the scope, from parent store `σ`, to the
    configuration of the outcome the scope leaves with. -/
private theorem star_scope {σ : SemanticStore P} (lb : Option String)
    {inner : Config P (CmdExt P)} {tr : List (Event P)} {o : Outcome P}
    (h : StepStmtStarE P EvalE inner tr (oCfg F o)) :
    StepStmtStarE P EvalE (.block lb σ inner) tr
      (oCfg F (match lb with
        | none => o.proj σ
        | some l => o.block l σ)) := by
  simpa using ReflTransTrace.trans _ (block_inner_starE h) (star_block_exit lb o)

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasBoolOps P] in
/-- A loop whose guard admits entering steps to its body, in a scope, followed by the loop. -/
private theorem step_loop_enter {σ : SemanticStore P} {g : ExprOrNondet P} {m : Option P.Expr}
    {inv : List (String × P.Expr)} {body : PStmts P} {md : MetaData P}
    (hg : guardEnters F σ g) :
    StepStmtE P EvalE (.stmt (.loop g m inv body md) { store := σ, factory := F }) []
      (.seq (.block none σ (.stmts body { store := σ, factory := F })) [.loop g m inv body md]) :=
  match g, hg with
  | .det _, hg => .step_loop_enter hg
  | .nondet, _ => .step_loop_nondet_enter

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasBoolOps P] in
/-- A loop whose guard admits stopping steps to the end. -/
private theorem step_loop_stop {σ : SemanticStore P} {g : ExprOrNondet P} {m : Option P.Expr}
    {inv : List (String × P.Expr)} {body : PStmts P} {md : MetaData P}
    (hg : guardExits F σ g) :
    StepStmtE P EvalE (.stmt (.loop g m inv body md) { store := σ, factory := F }) []
      (.terminal { store := σ, factory := F }) :=
  match g, hg with
  | .det _, hg => .step_loop_exit hg
  | .nondet, _ => .step_loop_nondet_exit

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasBoolOps P] in
/-- A run of a statement to the configuration of `o` is a run of the list of that statement. -/
private theorem star_singleton {s : PStmt P} {σ : SemanticStore P} {tr : List (Event P)}
    {o : Outcome P}
    (h : StepStmtStarE P EvalE (.stmt s { store := σ, factory := F }) tr (oCfg F o)) :
    StepStmtStarE P EvalE (.stmts [s] { store := σ, factory := F }) tr (oCfg F o) := by
  have hs := seq_inner_starE (P := P) EvalE (ss := []) h
  cases o with
  | normal σ' =>
    exact star_admin .step_stmts_cons (by
      simpa [oCfg] using ReflTransTrace.trans _ hs
        (star_admin .step_seq_done (star_admin .step_stmts_nil (.refl _))))
  | exit l σ' =>
    exact star_admin .step_stmts_cons (by
      simpa [oCfg] using ReflTransTrace.trans _ hs (star_admin .step_seq_exit (.refl _)))

section
omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
mutual
/-- A big-step run of a statement list is a small-step run with the same trace. -/
theorem brun_star (hWB : WellFormedSemanticEvalBool (P := P) F) :
    ∀ {L : (PStmts P)} {σ : SemanticStore P} {tr : List (Event P)} {o : (Outcome P)},
      BRun F L σ tr o → StepStmtStarE P EvalE
        (.stmts L { store := σ, factory := F }) tr (oCfg F o)
  | _, _, _, _, .nil => star_admin .step_stmts_nil (.refl _)
  | _, _, _, _, .cons_normal h1 h2 =>
    ReflTransTrace.trans _ (stmts_cons_stepE (P := P) EvalE _ _ _ _ (brun_starS hWB h1))
      (brun_star hWB h2)
  | _, _, _, _, .cons_exit (rest := rest) h1 => by
    have hexit := ReflTransTrace.trans _ (seq_inner_starE (P := P) EvalE (ss := rest)
      (brun_starS hWB h1)) (star_admin .step_seq_exit (.refl _))
    exact star_admin .step_stmts_cons (by simpa [oCfg] using hexit)
/-- A big-step run of a statement is a small-step run with the same trace. -/
private theorem brun_starS (hWB : WellFormedSemanticEvalBool (P := P) F) :
    ∀ {s : (PStmt P)} {σ : SemanticStore P} {tr : List (Event P)} {o : (Outcome P)},
      BRunS F s σ tr o → StepStmtStarE P EvalE
        (.stmt s { store := σ, factory := F }) tr (oCfg F o)
  | _, _, _, _, .cmd h => by
    simpa [oCfg] using ReflTransTrace.step _ _ _ _ _ (.step_cmd h) (.refl _)
  | _, _, _, _, .ite_true hc h =>
    star_admin (.step_ite_true hc) (star_scope none (brun_star hWB h))
  | _, _, _, _, .ite_false hc h =>
    star_admin (.step_ite_false hc) (star_scope none (brun_star hWB h))
  | _, _, _, _, .ite_nondet_true h =>
    star_admin .step_ite_nondet_true (star_scope none (brun_star hWB h))
  | _, _, _, _, .ite_nondet_false h =>
    star_admin .step_ite_nondet_false (star_scope none (brun_star hWB h))
  | _, _, _, _, .block (l := l) h =>
    star_admin .step_block (star_scope (some l) (brun_star hWB h))
  | _, _, _, _, .exit => star_admin .step_exit (.refl _)
  | _, _, _, _, .typeDecl => star_admin .step_typeDecl (.refl _)
  | _, _, _, _, .loop_exit hg => star_admin (step_loop_stop hg) (.refl _)
  | _, σ, _, _, .loop_iter hg h1 h2 => by
    have h1' := star_scope (σ := σ) none (brun_star hWB h1)
    have h2' := star_singleton (brun_starS hWB h2)
    exact star_admin (step_loop_enter hg) (by
      simpa [oCfg, Outcome.proj] using ReflTransTrace.trans _ (seq_inner_starE (P := P) EvalE h1')
        (star_admin .step_seq_done h2'))
  | _, σ, _, _, .loop_break hg h1 => by
    have h1' := star_scope (σ := σ) none (brun_star hWB h1)
    exact star_admin (step_loop_enter hg) (by
      simpa [oCfg, Outcome.proj] using ReflTransTrace.trans _ (seq_inner_starE (P := P) EvalE h1')
        (star_admin .step_seq_exit (.refl _)))
end

end

section
omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
mutual
/-- A big-step reach of a statement list is a small-step run with the same trace. -/
theorem breach_star (hWB : WellFormedSemanticEvalBool (P := P) F) :
    ∀ {L : (PStmts P)} {σ : SemanticStore P} {tr : List (Event P)},
      BReach F L σ tr → ∃ cfg, StepStmtStarE P EvalE
        (.stmts L { store := σ, factory := F }) tr cfg
  | _, _, _, .here (rest := rest) h => by
    obtain ⟨cfg, hc⟩ := breach_starS hWB h
    exact ⟨_, star_admin .step_stmts_cons (seq_inner_starE (P := P) EvalE (ss := rest) hc)⟩
  | _, _, _, .later h1 h2 => by
    obtain ⟨cfg, hc⟩ := breach_star hWB h2
    exact ⟨cfg, ReflTransTrace.trans _ (stmts_cons_stepE (P := P) EvalE _ _ _ _
      (brun_starS hWB h1)) hc⟩

/-- A big-step reach of a statement is a small-step run with the same trace. -/
private theorem breach_starS (hWB : WellFormedSemanticEvalBool (P := P) F) :
    ∀ {s : (PStmt P)} {σ : SemanticStore P} {tr : List (Event P)},
      BReachS F s σ tr → ∃ cfg, StepStmtStarE P EvalE
        (.stmt s { store := σ, factory := F }) tr cfg
  | _, _, _, .cmd h _ =>
    ⟨_, by simpa using ReflTransTrace.step _ _ _ _ _ (.step_cmd h) (.refl _)⟩
  | _, _, _, .ite_true hc h =>
    ⟨_, star_admin (.step_ite_true hc) (block_inner_starE (breach_star hWB h).choose_spec)⟩
  | _, _, _, .ite_false hc h => ⟨_, star_admin (.step_ite_false hc)
      (block_inner_starE (breach_star hWB h).choose_spec)⟩
  | _, _, _, .ite_nondet_true h =>
    ⟨_, star_admin .step_ite_nondet_true (block_inner_starE (breach_star hWB h).choose_spec)⟩
  | _, _, _, .ite_nondet_false h =>
    ⟨_, star_admin .step_ite_nondet_false (block_inner_starE (breach_star hWB h).choose_spec)⟩
  | _, _, _, .block (l := l) h =>
    ⟨_, star_admin .step_block (block_inner_starE (breach_star hWB h).choose_spec)⟩
  | _, _, _, .loop_here hg h =>
    ⟨_, star_admin (step_loop_enter hg)
      (seq_inner_starE (P := P) EvalE (block_inner_starE (breach_star hWB h).choose_spec))⟩
  | _, σ, _, .loop_later hg h1 h2 => by
    have h1' := star_scope (σ := σ) none (brun_star hWB h1)
    obtain ⟨cfg, h2'⟩ := breach_starS hWB h2
    exact ⟨_, star_admin (step_loop_enter hg) (by
      simpa [oCfg, Outcome.proj] using ReflTransTrace.trans _ (seq_inner_starE (P := P) EvalE h1')
        (star_admin .step_seq_done (star_admin .step_stmts_cons
          (seq_inner_starE (P := P) EvalE (ss := []) h2'))))⟩
end

end


/-! ## Failure over the reference event semantics -/

/-- `ss` run from `σ` (factory `F`) under the reference event semantics
    reaches a failing occurrence of `t` with the condition `e`, every assumption before it
    evaluating to `true`. -/
@[expose] def FailsE (F : P.Factory) (ss : (PStmts P))
    (σ : SemanticStore P) (t : AssertId P) (e : P.Expr) : Prop :=
  ∃ evs ev cfg, StepStmtStarE P EvalE (.stmts ss { store := σ, factory := F })
      (evs ++ [ev]) cfg ∧
    Trace.AssumptionsHold P evalInterp () evs ∧ FailsAt t e ev

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    in
/-- A big-step failure is a failure under the reference event semantics. -/
theorem fails_failsE {F : P.Factory} (hWB : WellFormedSemanticEvalBool (P := P) F)
    {ss : (PStmts P)} {σ : SemanticStore P} {t : AssertId P} {e : P.Expr}
    (h : Fails F ss σ t e) : FailsE F ss σ t e := by
  obtain ⟨evs, ev, hb, hfeas, hfe⟩ := h
  obtain ⟨cfg, hc⟩ := breach_star hWB hb
  exact ⟨evs, ev, cfg, hc, hfeas, hfe⟩

/-! ## Small-step failures are big-step failures

A small-step run gives a big-step reach with the same trace.  The proof reads the small-step
run backwards: each configuration carries the big-step meaning of the rest of its execution
(`CRun`, `CReach`), which one step backwards preserves. -/

/-- The outcome with which the body of a scope, ended with `o`, leaves it: an `ite` branch
    or a loop iteration (`none`) projects the store on the parent store `σp`; a block labelled
    `l` also consumes an `exit l`. -/
@[expose] def Outcome.leave (lb : Option String) (σp : SemanticStore P) (o : Outcome P) :
    Outcome P :=
  match lb with
  | none => o.proj σp
  | some l => o.block l σp

/-- What remains of the execution of a configuration is a big-step run emitting `evs` and
    ending with `o`. -/
inductive CRun (F : P.Factory) : Config P (CmdExt P) → List (Event P) → Outcome P → Prop where
  | stmt : BRunS F s ρ.store evs o → CRun F (.stmt s ρ) evs o
  | stmts : BRun F ss ρ.store evs o → CRun F (.stmts ss ρ) evs o
  | terminal : CRun F (.terminal ρ) [] (.normal ρ.store)
  | exiting : CRun F (.exiting l ρ) [] (.exit l ρ.store)
  | seq_normal : CRun F c evs1 (.normal σ1) → BRun F ss σ1 evs2 o →
      CRun F (.seq c ss) (evs1 ++ evs2) o
  | seq_exit : CRun F c evs (.exit l σ1) → CRun F (.seq c ss) evs (.exit l σ1)
  | block : CRun F c evs o → CRun F (.block lb σp c) evs (o.leave lb σp)

/-- What remains of the execution of a configuration is a big-step reach emitting `evs` (it
    stops right after a command emitting events). -/
inductive CReach (F : P.Factory) : Config P (CmdExt P) → List (Event P) → Prop where
  | stmt : BReachS F s ρ.store evs → CReach F (.stmt s ρ) evs
  | stmts : BReach F ss ρ.store evs → CReach F (.stmts ss ρ) evs
  | seq_here : CReach F c evs → CReach F (.seq c ss) evs
  | seq_later : CRun F c evs1 (.normal σ1) → BReach F ss σ1 evs2 →
      CReach F (.seq c ss) (evs1 ++ evs2)
  | block : CReach F c evs → CReach F (.block lb σp c) evs

variable {Lc : List P.Ident}

section
omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]

/-- Every configuration still to run has the factory `F`. -/
private def CInvN (F : P.Factory) : Config P (CmdExt P) → Prop
  | .stmt _ ρ => ρ.factory = F
  | .stmts _ ρ => ρ.factory = F
  | .terminal ρ => ρ.factory = F
  | .exiting _ ρ => ρ.factory = F
  | .block _ _ c => CInvN F c
  | .seq c _ => CInvN F c

omit [HasBoolOps P] in
/-- A step keeps the factory `F`. -/
private theorem cinvN_step {c c' : Config P (CmdExt P)} {e : List (Event P)}
    (hs : StepStmtE P EvalE c e c') (hI : CInvN F c) : CInvN F c' := by
  induction hs with
  | step_seq_inner _ ih => exact ih hI
  | step_block_body _ ih => exact ih hI
  | _ => simpa [CInvN] using hI

omit [HasBoolOps P] in
/-- The run of a scope is the run of its body, leaving the scope. -/
private theorem crun_block_inv {lb : Option String} {σp : SemanticStore P}
    {c : Config P (CmdExt P)} {evs : List (Event P)} {o : Outcome P}
    (h : CRun F (.block lb σp c) evs o) : ∃ o', CRun F c evs o' ∧ o = o'.leave lb σp := by
  cases h with
  | block h => exact ⟨_, h, rfl⟩

omit [HasBoolOps P] in
/-- What remains of a statement list to run is a run of it. -/
private theorem crun_stmts_inv {ss : PStmts P} {ρ : Env P} {evs : List (Event P)}
    {o : Outcome P} (h : CRun F (.stmts ss ρ) evs o) : BRun F ss ρ.store evs o := by
  cases h with
  | stmts h => exact h

omit [HasBoolOps P] in
/-- A run of a one-statement list is a run of the statement. -/
private theorem brun_singleton_inv {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P} (h : BRun F [s] σ evs o) : BRunS F s σ evs o := by
  cases h with
  | cons_normal h1 h2 => cases h2; simpa using h1
  | cons_exit h => exact h

omit [HasBool P] [HasFvar P] [HasBoolOps P] in
/-- An iteration of a loop body (an anonymous scope) ending normally ends its body normally. -/
private theorem leave_none_normal {σp σ1 : SemanticStore P} {o : Outcome P}
    (h : Outcome.normal σ1 = o.leave none σp) :
    ∃ σ1', o = .normal σ1' ∧ σ1 = projectStore σp σ1' := by
  cases o <;> simp_all [Outcome.leave, Outcome.proj]

omit [HasBool P] [HasFvar P] [HasBoolOps P] in
/-- An iteration of a loop body (an anonymous scope) exiting exits its body. -/
private theorem leave_none_exit {σp σ1 : SemanticStore P} {l : String} {o : Outcome P}
    (h : Outcome.exit l σ1 = o.leave none σp) :
    ∃ σ1', o = .exit l σ1' ∧ σ1 = projectStore σp σ1' := by
  cases o <;> simp_all [Outcome.leave, Outcome.proj]

omit [HasBoolOps P] in
/-- If what remains after a step is a big-step run (`CRun`), so is what remains before it,
    with the step's events prepended. -/
private theorem crun_step {c c' : Config P (CmdExt P)} {e evs : List (Event P)}
    {o : Outcome P} (hs : StepStmtE P EvalE c e c') (hI : CInvN F c) (hR : CRun F c' evs o) :
    CRun F c (e ++ evs) o := by
  induction hs generalizing evs o with
  | step_cmd h => cases hR; simpa using CRun.stmt (.cmd (hI ▸ h))
  | step_block => cases hR with | block h => cases h with | stmts h => exact .stmt (.block h)
  | step_ite_true hc =>
    cases hR with | block h => cases h with | stmts h => exact .stmt (.ite_true (hI ▸ hc) h)
  | step_ite_false hc =>
    cases hR with | block h => cases h with | stmts h => exact .stmt (.ite_false (hI ▸ hc) h)
  | step_ite_nondet_true =>
    cases hR with | block h => cases h with | stmts h => exact .stmt (.ite_nondet_true h)
  | step_ite_nondet_false =>
    cases hR with | block h => cases h with | stmts h => exact .stmt (.ite_nondet_false h)
  | step_loop_enter hg =>
    rw [List.nil_append]
    cases hR with
    | seq_normal h1 h2 =>
      obtain ⟨o', hb, ho⟩ := crun_block_inv h1
      obtain ⟨σ1', ho', hσ⟩ := leave_none_normal ho
      subst ho' hσ
      exact .stmt (.loop_iter (g := .det _) (hI ▸ hg) (crun_stmts_inv hb) (brun_singleton_inv h2))
    | seq_exit h =>
      obtain ⟨o', hb, ho⟩ := crun_block_inv h
      obtain ⟨σ1', ho', hσ⟩ := leave_none_exit ho
      subst ho' hσ
      exact .stmt (.loop_break (g := .det _) (hI ▸ hg) (crun_stmts_inv hb))
  | step_loop_nondet_enter =>
    rw [List.nil_append]
    cases hR with
    | seq_normal h1 h2 =>
      obtain ⟨o', hb, ho⟩ := crun_block_inv h1
      obtain ⟨σ1', ho', hσ⟩ := leave_none_normal ho
      subst ho' hσ
      exact .stmt (.loop_iter (g := .nondet) trivial (crun_stmts_inv hb) (brun_singleton_inv h2))
    | seq_exit h =>
      obtain ⟨o', hb, ho⟩ := crun_block_inv h
      obtain ⟨σ1', ho', hσ⟩ := leave_none_exit ho
      subst ho' hσ
      exact .stmt (.loop_break (g := .nondet) trivial (crun_stmts_inv hb))
  | step_loop_exit hg => cases hR; exact .stmt (.loop_exit (g := .det _) (hI ▸ hg))
  | step_loop_nondet_exit => cases hR; exact .stmt (.loop_exit (g := .nondet) trivial)
  | step_exit => cases hR; exact .stmt .exit
  | step_typeDecl => cases hR; exact .stmt .typeDecl
  | step_stmts_nil => cases hR; exact .stmts .nil
  | step_stmts_cons =>
    rw [List.nil_append]
    cases hR with
    | seq_normal h1 h2 => cases h1 with | stmt h1 => exact .stmts (.cons_normal h1 h2)
    | seq_exit h => cases h with | stmt h => exact .stmts (.cons_exit h)
  | step_seq_inner _ ih =>
    cases hR with
    | seq_normal h1 h2 => simpa using CRun.seq_normal (ih hI h1) h2
    | seq_exit h => exact .seq_exit (ih hI h)
  | step_seq_done => cases hR with | stmts h => simpa using CRun.seq_normal .terminal h
  | step_seq_exit => cases hR; exact .seq_exit .exiting
  | step_block_body _ ih => cases hR with | block h => exact .block (ih hI h)
  | step_block_done =>
    cases hR
    rename_i label _ _
    cases label <;> exact .block .terminal
  | @step_block_exit_match lb σp l ρ' hl =>
    cases hR
    have h := CRun.block (lb := lb) (σp := σp)
      (CRun.exiting (F := F) (l := l) (ρ := ρ'))
    simpa [hl, Outcome.leave, Outcome.block] using h
  | @step_block_exit_mismatch lb σp l ρ' hl =>
    cases hR
    have h := CRun.block (lb := lb) (σp := σp)
      (CRun.exiting (F := F) (l := l) (ρ := ρ'))
    cases lb <;> simp_all [Outcome.leave, Outcome.block, Outcome.proj, eq_comm]

omit [HasBoolOps P] in
/-- A reach of a one-statement list is a reach of the statement. -/
private theorem breach_singleton_inv {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)}
    (h : BReach F [s] σ evs) : BReachS F s σ evs := by
  cases h with
  | here h => exact h
  | later _ h => cases h

omit [HasBoolOps P] in
/-- If what remains after a step is a big-step reach (`CReach`), so is what remains before
    it, with the step's events prepended. -/
private theorem creach_step {c c' : Config P (CmdExt P)} {e evs : List (Event P)}
    (hs : StepStmtE P EvalE c e c') (hI : CInvN F c) (hR : CReach F c' evs) :
    CReach F c (e ++ evs) := by
  induction hs generalizing evs with
  | step_cmd => cases hR
  | step_block =>
    cases hR with | block h => cases h with | stmts h => exact .stmt (.block h)
  | step_ite_true hc => cases hR with
    | block h => cases h with | stmts h => exact .stmt (.ite_true (hI ▸ hc) h)
  | step_ite_false hc => cases hR with
    | block h => cases h with | stmts h => exact .stmt (.ite_false (hI ▸ hc) h)
  | step_ite_nondet_true =>
    cases hR with | block h => cases h with | stmts h => exact .stmt (.ite_nondet_true h)
  | step_ite_nondet_false =>
    cases hR with | block h => cases h with | stmts h => exact .stmt (.ite_nondet_false h)
  | step_loop_enter hg =>
    rw [List.nil_append]
    cases hR with
    | seq_here h =>
      cases h with
      | block h => cases h with
        | stmts h => exact .stmt (.loop_here (g := .det _) (hI ▸ hg) h)
    | seq_later h1 h2 =>
      obtain ⟨o', hb, ho⟩ := crun_block_inv h1
      obtain ⟨σ1', ho', hσ⟩ := leave_none_normal ho
      subst ho' hσ
      exact .stmt
        (.loop_later (g := .det _) (hI ▸ hg) (crun_stmts_inv hb) (breach_singleton_inv h2))
  | step_loop_nondet_enter =>
    rw [List.nil_append]
    cases hR with
    | seq_here h =>
      cases h with
      | block h => cases h with
        | stmts h => exact .stmt (.loop_here (g := .nondet) trivial h)
    | seq_later h1 h2 =>
      obtain ⟨o', hb, ho⟩ := crun_block_inv h1
      obtain ⟨σ1', ho', hσ⟩ := leave_none_normal ho
      subst ho' hσ
      exact .stmt (.loop_later (g := .nondet) trivial (crun_stmts_inv hb) (breach_singleton_inv h2))
  | step_stmts_cons =>
    rw [List.nil_append]
    cases hR with
    | seq_here h => cases h with | stmt h => exact .stmts (.here h)
    | seq_later h1 h2 => cases h1 with | stmt h1 => exact .stmts (.later h1 h2)
  | step_seq_inner hs ih =>
    cases hR with
    | seq_here h => exact .seq_here (ih hI h)
    | seq_later h1 h2 => simpa using CReach.seq_later (crun_step hs hI h1) h2
  | step_seq_done => cases hR with | stmts h => simpa using CReach.seq_later .terminal h
  | step_block_body _ ih => cases hR with | block h => exact .block (ih hI h)
  | _ => cases hR

omit [HasBoolOps P] in
/-- What remains of a configuration about to take a step emitting events is a big-step reach
    emitting them. -/
private theorem creach_emit {c c' : Config P (CmdExt P)} {e : List (Event P)}
    (hs : StepStmtE P EvalE c e c') (hI : CInvN F c) (he : e ≠ []) : CReach F c e := by
  induction hs with
  | step_cmd h => exact .stmt (.cmd (hI ▸ h) he)
  | step_seq_inner _ ih => exact .seq_here (ih hI he)
  | step_block_body _ ih => exact .block (ih hI he)
  | _ => exact absurd rfl he

omit [HasBoolOps P] in
/-- What remains of a configuration with a small-step run emitting a nonempty trace is a
    big-step reach emitting it. -/
private theorem creach_star {c c' : Config P (CmdExt P)} {tr : List (Event P)}
    (hs : StepStmtStarE P EvalE c tr c') (hI : CInvN F c) (htr : tr ≠ []) : CReach F c tr := by
  induction hs with
  | refl => exact absurd rfl htr
  | step _ e _ rest _ h1 _ ih =>
    by_cases hr : rest = []
    · subst hr
      simpa using creach_emit h1 hI (by simpa using htr)
    · exact creach_step h1 hI (ih (cinvN_step h1 hI) hr)

omit [HasBoolOps P] in
/-- What remains of a configuration with a small-step run to `c'` is a big-step run when what
    remains of `c'` is, with the run's events prepended. -/
private theorem crun_star {c c' : Config P (CmdExt P)} {tr evs : List (Event P)}
    {o : Outcome P} (hs : StepStmtStarE P EvalE c tr c') (hI : CInvN F c)
    (hR : CRun F c' evs o) :
    CRun F c (tr ++ evs) o := by
  induction hs with
  | refl => exact hR
  | step _ _ _ _ _ h1 _ ih => simpa using crun_step h1 hI (ih (cinvN_step h1 hI) hR)

omit [HasBoolOps P] in
/-- **Small-step to big-step adequacy.**  A list that fails the target `t` from `σ` under the
    reference event semantics (`FailsE`) fails it in the big-step semantics (`Fails`), with the
    same trace. -/
theorem failsE_fails {ss : PStmts P} {σ : SemanticStore P} {t : AssertId P} {e : P.Expr}
    (h : FailsE F ss σ t e) : Fails F ss σ t e := by
  obtain ⟨evs, ev, cfg, hr, hfeas, hfe⟩ := h
  cases creach_star hr rfl (by simp) with
  | stmts h => exact ⟨evs, ev, h, hfeas, hfe⟩

omit [HasBoolOps P] in
/-- **Small-step prefixes are big-step reaches.**  A small-step run of a list from `σ` emitting
    a nonempty trace `tr` gives a big-step reach of the list from `σ` emitting `tr`. -/
theorem star_breach {ss : PStmts P} {σ : SemanticStore P} {tr : List (Event P)}
    {cfg : Config P (CmdExt P)}
    (h : StepStmtStarE P EvalE (.stmts ss { store := σ, factory := F }) tr cfg)
    (htr : tr ≠ []) : BReach F ss σ tr := by
  cases creach_star h rfl htr with
  | stmts h => exact h

omit [HasBoolOps P] in
/-- **Small-step runs are big-step runs.**  A small-step run of a list from `σ` emitting `tr`
    to a terminal configuration with store `σ'` gives a big-step run of the list from `σ`
    emitting `tr` and ending normally with `σ'`; to an exiting configuration with label `l` and
    store `σ'`, one exiting with `l` and `σ'`. -/
theorem star_brun {ss : PStmts P} {σ : SemanticStore P} {tr : List (Event P)} :
    (∀ {ρ'}, StepStmtStarE P EvalE (.stmts ss { store := σ, factory := F }) tr
        (.terminal ρ') →
      BRun F ss σ tr (.normal ρ'.store)) ∧
    (∀ {l ρ'}, StepStmtStarE P EvalE (.stmts ss { store := σ, factory := F }) tr
        (.exiting l ρ') →
      BRun F ss σ tr (.exit l ρ'.store)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases crun_star h rfl .terminal with
    | stmts h => simpa using h
  · cases crun_star h rfl .exiting with
    | stmts h => simpa using h

end

/-! ## Prefixes of small-step runs -/

section
omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]

omit [HasBoolOps P] in
/-- A step emits at most one event. -/
private theorem step_emits {c c' : Config P (CmdExt P)} {evs : List (Event P)}
    (h : StepStmtE P EvalE c evs c') : evs = [] ∨ ∃ e, evs = [e] := by
  induction h with
  | step_cmd h =>
    rename_i cmd _ _ _
    cases cmd with
    | call => exact h.elim
    | cmd c =>
      change EvalCmdE P _ _ c _ _ at h
      cases h <;> simp
  | step_seq_inner _ ih => exact ih
  | step_block_body _ ih => exact ih
  | _ => exact .inl rfl

omit [HasBoolOps P] in
/-- **Small-step runs are closed under prefixes ending at an event.**  A run emitting
    `pre ++ e :: post` has a prefix emitting `pre ++ [e]`. -/
theorem star_prefix {c c' : Config P (CmdExt P)} {tr : List (Event P)}
    (h : StepStmtStarE P EvalE c tr c') :
    ∀ {pre : List (Event P)} {e : Event P} {post : List (Event P)}, tr = pre ++ e :: post →
      ∃ c'', StepStmtStarE P EvalE c (pre ++ [e]) c'' := by
  induction h with
  | refl => intro pre e post h; simp at h
  | step _ evs _ rest _ h1 _ ih =>
    intro pre e post htr
    rcases step_emits h1 with rfl | ⟨x, rfl⟩
    · obtain ⟨c'', h''⟩ := ih (by simpa using htr)
      exact ⟨c'', by simpa using ReflTransTrace.step _ _ _ _ _ h1 h''⟩
    · cases pre with
      | nil =>
        obtain ⟨rfl, -⟩ := by simpa using htr
        exact ⟨_, by simpa using ReflTransTrace.step _ _ _ _ _ h1 (.refl _)⟩
      | cons p pre =>
        obtain ⟨rfl, hrest⟩ := by simpa using htr
        obtain ⟨c'', h''⟩ := ih hrest
        exact ⟨c'', by simpa using ReflTransTrace.step _ _ _ _ _ h1 h''⟩

end


end -- public section

end BigStep
end Imperative
