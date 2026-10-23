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
failure under the reference event semantics (`fails_failsE`).  Conversely, for a list without
loops, a small-step run emitting a nonempty trace is a big-step reach with that trace
(`star_breach_noLoops`), a small-step run to a terminal or exiting configuration is a big-step run
(`star_brun_noLoops`), and a failure under the reference event semantics is a big-step failure
(`failsE_fails_noLoops`).  A small-step run keeps the factory and the failure flag
(`star_getEnv`).

Key theorems: `brun_star`, `breach_star`, `fails_failsE`, `star_breach_noLoops`,
`star_brun_noLoops`, `failsE_fails_noLoops`, `star_getEnv`.

Key definitions: `FailsE`, `CRun`, `CReach`. -/

namespace Imperative
namespace BigStep

public section

variable {P : PureExpr} [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
  [HasBool P] [HasFvar P] [HasBoolOps P]

/-- The configuration a big-step outcome ends in. -/
@[expose] def oCfg (F : P.Factory) (hf : Bool) : (Outcome P) → Config P (CmdExt P)
  | .normal σ => .terminal { store := σ, factory := F, hasFailure := hf }
  | .exit l σ => .exiting l { store := σ, factory := F, hasFailure := hf }

variable {F : P.Factory}

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasBoolOps P] in
/-- An administrative step (no event) followed by a run is a run. -/
private theorem star_admin {a b c : Config P (CmdExt P)} {t : List (Event P)}
    (h1 : StepStmt P (noCommandEvalE P (CmdExt P)) a b) (h2 : StepStmtStarE P EvalE b t c) :
    StepStmtStarE P EvalE a t c := by
  simpa using ReflTransTrace.step _ _ _ _ _ (.step_admin h1) h2

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    [HasBoolOps P] in
/-- Leaving a scope (an `ite` branch or a block) with the outcome of its body. -/
private theorem star_block_exit {σp : SemanticStore P} {hf : Bool} (lb : Option String)
    (o : (Outcome P)) :
    StepStmtStarE P EvalE (.block lb σp (oCfg F hf o)) []
      (oCfg F hf (match lb with
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
private theorem star_scope {σ : SemanticStore P} {hf : Bool} (lb : Option String)
    {inner : Config P (CmdExt P)} {tr : List (Event P)} {o : Outcome P}
    (h : StepStmtStarE P EvalE inner tr (oCfg F hf o)) :
    StepStmtStarE P EvalE (.block lb σ inner) tr
      (oCfg F hf (match lb with
        | none => o.proj σ
        | some l => o.block l σ)) := by
  simpa using ReflTransTrace.trans _ (block_inner_starE h) (star_block_exit lb o)

section
omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
mutual
/-- A big-step run of a statement list is a small-step run with the same trace. -/
theorem brun_star (hWB : WellFormedSemanticEvalBool (P := P) F) :
    ∀ {L : (PStmts P)} {σ : SemanticStore P} {tr : List (Event P)} {o : (Outcome P)},
      BRun F L σ tr o → ∀ hf, StepStmtStarE P EvalE
        (.stmts L { store := σ, factory := F, hasFailure := hf }) tr (oCfg F hf o)
  | _, _, _, _, .nil, hf => star_admin .step_stmts_nil (.refl _)
  | _, _, _, _, .cons_normal h1 h2, hf =>
    ReflTransTrace.trans _ (stmts_cons_stepE (P := P) EvalE _ _ _ _ (brun_starS hWB h1 hf))
      (brun_star hWB h2 hf)
  | _, _, _, _, .cons_exit (rest := rest) h1, hf => by
    have hexit := ReflTransTrace.trans _ (seq_inner_starE (P := P) EvalE (ss := rest)
      (brun_starS hWB h1 hf)) (star_admin .step_seq_exit (.refl _))
    exact star_admin .step_stmts_cons (by simpa [oCfg] using hexit)
/-- A big-step run of a statement is a small-step run with the same trace. -/
private theorem brun_starS (hWB : WellFormedSemanticEvalBool (P := P) F) :
    ∀ {s : (PStmt P)} {σ : SemanticStore P} {tr : List (Event P)} {o : (Outcome P)},
      BRunS F s σ tr o → ∀ hf, StepStmtStarE P EvalE
        (.stmt s { store := σ, factory := F, hasFailure := hf }) tr (oCfg F hf o)
  | _, _, _, _, .cmd h, hf => by
    simpa [oCfg] using ReflTransTrace.step _ _ _ _ _ (.step_cmd h) (.refl _)
  | _, _, _, _, .ite_true hc h, hf =>
    star_admin (.step_ite_true hc) (star_scope none (brun_star hWB h hf))
  | _, _, _, _, .ite_false hc h, hf =>
    star_admin (.step_ite_false hc) (star_scope none (brun_star hWB h hf))
  | _, _, _, _, .ite_nondet_true h, hf =>
    star_admin .step_ite_nondet_true (star_scope none (brun_star hWB h hf))
  | _, _, _, _, .ite_nondet_false h, hf =>
    star_admin .step_ite_nondet_false (star_scope none (brun_star hWB h hf))
  | _, _, _, _, .block (l := l) h, hf =>
    star_admin .step_block (star_scope (some l) (brun_star hWB h hf))
  | _, _, _, _, .exit, hf => star_admin .step_exit (.refl _)
  | _, _, _, _, .typeDecl, hf => star_admin .step_typeDecl (.refl _)
end

end

section
omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
mutual
/-- A big-step reach of a statement list is a small-step run with the same trace. -/
theorem breach_star (hWB : WellFormedSemanticEvalBool (P := P) F) :
    ∀ {L : (PStmts P)} {σ : SemanticStore P} {tr : List (Event P)},
      BReach F L σ tr → ∀ hf, ∃ cfg, StepStmtStarE P EvalE
        (.stmts L { store := σ, factory := F, hasFailure := hf }) tr cfg
  | _, _, _, .here (rest := rest) h, hf => by
    obtain ⟨cfg, hc⟩ := breach_starS hWB h hf
    exact ⟨_, star_admin .step_stmts_cons (seq_inner_starE (P := P) EvalE (ss := rest) hc)⟩
  | _, _, _, .later h1 h2, hf => by
    obtain ⟨cfg, hc⟩ := breach_star hWB h2 hf
    exact ⟨cfg, ReflTransTrace.trans _ (stmts_cons_stepE (P := P) EvalE _ _ _ _
      (brun_starS hWB h1 hf)) hc⟩
/-- A big-step reach of a statement is a small-step run with the same trace. -/
private theorem breach_starS (hWB : WellFormedSemanticEvalBool (P := P) F) :
    ∀ {s : (PStmt P)} {σ : SemanticStore P} {tr : List (Event P)},
      BReachS F s σ tr → ∀ hf, ∃ cfg, StepStmtStarE P EvalE
        (.stmt s { store := σ, factory := F, hasFailure := hf }) tr cfg
  | _, _, _, .cmd h, hf => ⟨_, by simpa using ReflTransTrace.step _ _ _ _ _ (.step_cmd h) (.refl _)⟩
  | _, _, _, .ite_true hc h, hf =>
    ⟨_, star_admin (.step_ite_true hc) (block_inner_starE (breach_star hWB h hf).choose_spec)⟩
  | _, _, _, .ite_false hc h, hf => ⟨_, star_admin (.step_ite_false hc)
      (block_inner_starE (breach_star hWB h hf).choose_spec)⟩
  | _, _, _, .ite_nondet_true h, hf =>
    ⟨_, star_admin .step_ite_nondet_true (block_inner_starE (breach_star hWB h hf).choose_spec)⟩
  | _, _, _, .ite_nondet_false h, hf =>
    ⟨_, star_admin .step_ite_nondet_false (block_inner_starE (breach_star hWB h hf).choose_spec)⟩
  | _, _, _, .block (l := l) h, hf =>
    ⟨_, star_admin .step_block (block_inner_starE (breach_star hWB h hf).choose_spec)⟩
end

end


/-! ## Failure over the reference event semantics -/

/-- `ss` run from `σ` (factory `F`, failure flag `hf`) under the reference event semantics
    reaches a failing occurrence of `t`, every assumption before it evaluating to `true`. -/
@[expose] def FailsE (F : P.Factory) (hf : Bool) (ss : (PStmts P))
    (σ : SemanticStore P) (t : AssertId P) : Prop :=
  ∃ evs e cfg, StepStmtStarE P EvalE (.stmts ss { store := σ, factory := F, hasFailure := hf })
      (evs ++ [e]) cfg ∧
    Trace.AssumptionsHold P evalInterp () evs ∧ FailsAt t e

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident]
    in
/-- A big-step failure is a failure under the reference event semantics. -/
theorem fails_failsE {F : P.Factory} (hWB : WellFormedSemanticEvalBool (P := P) F)
    (hf : Bool) {ss : (PStmts P)} {σ : SemanticStore P} {t : AssertId P}
    (h : Fails F ss σ t) : FailsE F hf ss σ t := by
  obtain ⟨evs, e, hb, hfeas, hfe⟩ := h
  obtain ⟨cfg, hc⟩ := breach_star hWB hb hf
  exact ⟨evs, e, cfg, hc, hfeas, hfe⟩

/-! ## Small-step failures are big-step failures

A small-step run of a list without loops (`Block.noLoops`) gives a big-step reach with the same
trace.  The proof reads the small-step run backwards: each configuration carries the big-step
meaning of the rest of its execution (`CRun`, `CReach`), which one step backwards
preserves. -/

/-- The outcome with which the body of a scope, ended with `o`, leaves it: an `ite` branch
    (`none`) projects the store on the parent store `σp`; a block labelled `l` also consumes
    an `exit l`. -/
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
    stops right after a command). -/
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

/-- Every statement still to run in the configuration has no loops, and its factory is
    `F`. -/
private def CInvN (F : P.Factory) : Config P (CmdExt P) → Prop
  | .stmt s ρ => Stmt.noLoops s = true ∧ ρ.factory = F
  | .stmts ss ρ => Block.noLoops ss = true ∧ ρ.factory = F
  | .terminal ρ => ρ.factory = F
  | .exiting _ ρ => ρ.factory = F
  | .block _ _ c => CInvN F c
  | .seq c ss => CInvN F c ∧ Block.noLoops ss = true

omit [HasBoolOps P] in
/-- If what remains after an administrative step is a big-step run (`CRun`), so is what
    remains before it, with the same events and outcome. -/
private theorem crun_adminN {c c' : Config P (CmdExt P)}
    (hs : StepStmt P (noCommandEvalE P (CmdExt P)) c c') (hI : CInvN F c)
    {evs : List (Event P)} {o : Outcome P} (hR : CRun F c' evs o) : CRun F c evs o := by
  induction hs generalizing evs o with
  | step_cmd h => exact h.elim
  | step_block => cases hR with | block h => cases h with | stmts h => exact .stmt (.block h)
  | step_ite_true hc =>
    cases hR with | block h => cases h with | stmts h => exact .stmt (.ite_true (hI.2 ▸ hc) h)
  | step_ite_false hc =>
    cases hR with | block h => cases h with | stmts h => exact .stmt (.ite_false (hI.2 ▸ hc) h)
  | step_ite_nondet_true =>
    cases hR with | block h => cases h with | stmts h => exact .stmt (.ite_nondet_true h)
  | step_ite_nondet_false =>
    cases hR with | block h => cases h with | stmts h => exact .stmt (.ite_nondet_false h)
  | step_exit => cases hR; exact .stmt .exit
  | step_typeDecl => cases hR; exact .stmt .typeDecl
  | step_stmts_nil => cases hR; exact .stmts .nil
  | step_stmts_cons =>
    cases hR with
    | seq_normal h1 h2 => cases h1 with | stmt h1 => exact .stmts (.cons_normal h1 h2)
    | seq_exit h => cases h with | stmt h => exact .stmts (.cons_exit h)
  | step_seq_inner _ ih =>
    cases hR with
    | seq_normal h1 h2 => exact .seq_normal (ih hI.1 h1) h2
    | seq_exit h => exact .seq_exit (ih hI.1 h)
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
  | _ => simp [CInvN, Stmt.noLoops_loop] at hI

omit [HasBoolOps P] in
/-- A step keeps every statement still to run free of loops, and the factory `F`. -/
private theorem cinvN_step {c c' : Config P (CmdExt P)} {e : List (Event P)}
    (hs : StepStmtE P EvalE c e c') (hI : CInvN F c) : CInvN F c' := by
  induction hs with
  | step_cmd => exact hI.2
  | step_admin hs =>
    induction hs with
    | step_cmd h => exact h.elim
    | step_block | step_ite_true | step_ite_false | step_ite_nondet_true
      | step_ite_nondet_false =>
        exact ⟨by simp_all [CInvN, Stmt.noLoops_ite, Stmt.noLoops_block], hI.2⟩
    | step_stmts_cons =>
      have h := hI.1
      rw [Block.noLoops_cons, Bool.and_eq_true] at h
      exact ⟨⟨h.1, hI.2⟩, h.2⟩
    | step_seq_inner _ ih => exact ⟨ih hI.1, hI.2⟩
    | step_seq_done => exact ⟨hI.2, hI.1⟩
    | step_block_body _ ih => exact ih hI
    | step_block_done | step_block_exit_match | step_block_exit_mismatch => exact hI
    | step_exit | step_typeDecl | step_stmts_nil => exact hI.2
    | step_seq_exit => exact hI.1
    | _ => simp [CInvN, Stmt.noLoops_loop] at hI
  | step_seq_inner _ ih => exact ⟨ih hI.1, hI.2⟩
  | step_block_body _ ih => exact ih hI

omit [HasBoolOps P] in
/-- If what remains after a step is a big-step run (`CRun`), so is what remains before it,
    with the step's events prepended. -/
private theorem crun_step {c c' : Config P (CmdExt P)} {e evs : List (Event P)}
    {o : Outcome P} (hs : StepStmtE P EvalE c e c') (hI : CInvN F c) (hR : CRun F c' evs o) :
    CRun F c (e ++ evs) o := by
  induction hs generalizing evs o with
  | step_cmd h => cases hR; simpa using CRun.stmt (.cmd (hI.2 ▸ h))
  | step_admin h => exact crun_adminN h hI hR
  | step_seq_inner _ ih =>
    cases hR with
    | seq_normal h1 h2 => simpa using CRun.seq_normal (ih hI.1 h1) h2
    | seq_exit h => exact .seq_exit (ih hI.1 h)
  | step_block_body _ ih => cases hR with | block h => exact .block (ih hI h)

omit [HasBoolOps P] in
/-- If what remains after a step is a big-step reach (`CReach`), so is what remains before
    it, with the step's events prepended. -/
private theorem creach_step {c c' : Config P (CmdExt P)} {e evs : List (Event P)}
    (hs : StepStmtE P EvalE c e c') (hI : CInvN F c) (hR : CReach F c' evs) :
    CReach F c (e ++ evs) := by
  induction hs generalizing evs with
  | step_cmd => cases hR
  | step_admin hs =>
    rw [List.nil_append]
    induction hs generalizing evs with
    | step_block =>
      cases hR with | block h => cases h with | stmts h => exact .stmt (.block h)
    | step_ite_true hc => cases hR with
      | block h => cases h with | stmts h => exact .stmt (.ite_true (hI.2 ▸ hc) h)
    | step_ite_false hc => cases hR with
      | block h => cases h with | stmts h => exact .stmt (.ite_false (hI.2 ▸ hc) h)
    | step_ite_nondet_true =>
      cases hR with | block h => cases h with | stmts h => exact .stmt (.ite_nondet_true h)
    | step_ite_nondet_false =>
      cases hR with | block h => cases h with | stmts h => exact .stmt (.ite_nondet_false h)
    | step_stmts_cons =>
      cases hR with
      | seq_here h => cases h with | stmt h => exact .stmts (.here h)
      | seq_later h1 h2 => cases h1 with | stmt h1 => exact .stmts (.later h1 h2)
    | step_seq_inner hs ih =>
      cases hR with
      | seq_here h => exact .seq_here (ih hI.1 h)
      | seq_later h1 h2 => exact .seq_later (crun_adminN hs hI.1 h1) h2
    | step_seq_done => cases hR with | stmts h => simpa using CReach.seq_later .terminal h
    | step_block_body _ ih => cases hR with | block h => exact .block (ih hI h)
    | _ => first | (cases hR; done) | simp [CInvN, Stmt.noLoops_loop] at hI
  | step_seq_inner hs ih =>
    cases hR with
    | seq_here h => exact .seq_here (ih hI.1 h)
    | seq_later h1 h2 => simpa using CReach.seq_later (crun_step hs hI.1 h1) h2
  | step_block_body _ ih => cases hR with | block h => exact .block (ih hI h)

omit [HasBoolOps P] in
/-- What remains of a configuration about to take a step emitting events is a big-step reach
    emitting them. -/
private theorem creach_emit {c c' : Config P (CmdExt P)} {e : List (Event P)}
    (hs : StepStmtE P EvalE c e c') (hI : CInvN F c) (he : e ≠ []) : CReach F c e := by
  induction hs with
  | step_cmd h => exact .stmt (.cmd (hI.2 ▸ h))
  | step_admin => exact absurd rfl he
  | step_seq_inner _ ih => exact .seq_here (ih hI.1 he)
  | step_block_body _ ih => exact .block (ih hI he)

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
/-- **Small-step to big-step adequacy for lists without loops.**  A list without loops
    (`Block.noLoops`) that fails the target `t` from `σ` under the reference event semantics
    (`FailsE`) fails it in the big-step semantics (`Fails`), with the same trace. -/
theorem failsE_fails_noLoops {ss : PStmts P} (hss : Block.noLoops ss = true) {hf : Bool}
    {σ : SemanticStore P} {t : AssertId P} (h : FailsE F hf ss σ t) : Fails F ss σ t := by
  obtain ⟨evs, e, cfg, hr, hfeas, hfe⟩ := h
  cases creach_star hr ⟨hss, rfl⟩ (by simp) with
  | stmts h => exact ⟨evs, e, h, hfeas, hfe⟩

omit [HasBoolOps P] in
/-- A step keeps the factory and the failure flag of the environment. -/
private theorem step_getEnv {c c' : Config P (CmdExt P)} {e : List (Event P)}
    (hs : StepStmtE P EvalE c e c') :
    c'.getEnv.factory = c.getEnv.factory ∧ c'.getEnv.hasFailure = c.getEnv.hasFailure := by
  induction hs with
  | step_cmd => exact ⟨rfl, rfl⟩
  | step_admin hs =>
    induction hs with
    | step_cmd h => exact h.elim
    | _ => simp_all [Config.getEnv]
  | step_seq_inner _ ih | step_block_body _ ih => exact ih

omit [HasBoolOps P] in
/-- A small-step run keeps the factory and the failure flag of the environment. -/
theorem star_getEnv {c c' : Config P (CmdExt P)} {tr : List (Event P)}
    (h : StepStmtStarE P EvalE c tr c') :
    c'.getEnv.factory = c.getEnv.factory ∧ c'.getEnv.hasFailure = c.getEnv.hasFailure := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | step _ _ _ _ _ h1 _ ih => exact ⟨ih.1.trans (step_getEnv h1).1, ih.2.trans (step_getEnv h1).2⟩

omit [HasBoolOps P] in
/-- **Small-step prefixes are big-step reaches.**  A small-step run of a list without loops
    (`Block.noLoops`) from `σ` emitting a nonempty trace `tr` gives a big-step reach of the list
    from `σ` emitting `tr`. -/
theorem star_breach_noLoops {ss : PStmts P} (hss : Block.noLoops ss = true) {hf : Bool}
    {σ : SemanticStore P} {tr : List (Event P)} {cfg : Config P (CmdExt P)}
    (h : StepStmtStarE P EvalE (.stmts ss { store := σ, factory := F, hasFailure := hf }) tr cfg)
    (htr : tr ≠ []) : BReach F ss σ tr := by
  cases creach_star h ⟨hss, rfl⟩ htr with
  | stmts h => exact h

omit [HasBoolOps P] in
/-- **Small-step runs are big-step runs.**  A small-step run of a list without loops
    (`Block.noLoops`) from `σ` emitting `tr` to a terminal configuration with store `σ'` gives a
    big-step run of the list from `σ` emitting `tr` and ending normally with `σ'`; to an exiting
    configuration with label `l` and store `σ'`, one exiting with `l` and `σ'`. -/
theorem star_brun_noLoops {ss : PStmts P} (hss : Block.noLoops ss = true) {hf : Bool}
    {σ : SemanticStore P} {tr : List (Event P)} :
    (∀ {ρ'}, StepStmtStarE P EvalE (.stmts ss { store := σ, factory := F, hasFailure := hf }) tr
        (.terminal ρ') →
      BRun F ss σ tr (.normal ρ'.store)) ∧
    (∀ {l ρ'}, StepStmtStarE P EvalE (.stmts ss { store := σ, factory := F, hasFailure := hf }) tr
        (.exiting l ρ') →
      BRun F ss σ tr (.exit l ρ'.store)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases crun_star h ⟨hss, rfl⟩ .terminal with
    | stmts h => simpa using h
  · cases crun_star h ⟨hss, rfl⟩ .exiting with
    | stmts h => simpa using h

end


end -- public section

end BigStep
end Imperative
