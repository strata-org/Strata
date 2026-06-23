/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.NondetElim
public import Strata.Transform.LoopInitHoist
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.StmtSemanticsProps
import all Strata.DL.Imperative.StmtSemanticsProps
import all Strata.DL.Util.StringGen
import all Strata.DL.Util.Relations

public section

namespace Imperative

/-- The simulated source/target outcome configuration, parametrized on an
`Option String` selector: `none` denotes the terminal outcome `.terminal ρ`,
`some lbl` denotes the exiting outcome `.exiting lbl ρ`.  Both mutual simulation
lemmas conclude over this shape so that a source run reaching *either* outcome is
matched by the rewritten program reaching the *same* outcome; the `.exiting`
selector is what lets the `.block` simulation arm discharge the case where the
block body exits to a non-matching label (caught by `step_block_exit_mismatch`)
or to the block's own label (caught by `step_block_exit_match`). -/
@[expose] def outcomeConfig {P : PureExpr} (oc : Option String) (ρ : Env P) :
    Config P (Cmd P) :=
  match oc with
  | none => .terminal ρ
  | some lbl => .exiting lbl ρ

/-! ## Structural postcondition: the pass output has no nondeterministic control

`Block.simpleShape` holds of every output of `Block.nondetElim` (spec guarantee
2): the rewrite replaces each nondeterministic `.ite`/`.loop` guard with a
deterministic read, so no `.ite .nondet`/`.loop .nondet` survives. -/

/-- `Block.simpleShape` distributes over `++`. -/
theorem Block.simpleShape_append {P : PureExpr} (xs ys : List (Stmt P (Cmd P))) :
    Block.simpleShape (xs ++ ys) =
      (Block.simpleShape xs && Block.simpleShape ys) := by
  induction xs with
  | nil => simp [Block.simpleShape]
  | cons x rest ih => simp [Block.simpleShape, ih, Bool.and_assoc]

mutual
/-- The output of `Stmt.nondetElimM s σ` satisfies `simpleShape` (no
nondeterministic control). -/
theorem Stmt.nondetElimM_simpleShape {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
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

theorem Block.nondetElimM_simpleShape {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
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
theorem nondetElim_simpleShape {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) :
    Block.simpleShape (Block.nondetElim ss) = true :=
  Block.nondetElimM_simpleShape ss StringGenState.emp

/-! ## Foundation lemmas for the simulation proof

These are fully-proved building blocks for `nondetElim_simulation`, reused
arm-by-arm.  They live outside the main inductive lemma so that each can be
verified independently. -/

section Foundation

/-- A terminating empty statement list leaves the environment unchanged. -/
theorem stmts_nil_terminal_eq {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    (ρ ρ' : Env P)
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmts [] ρ) (.terminal ρ')) :
    ρ = ρ' := by
  cases h with
  | step _ _ _ hstep hrest =>
    cases hstep with
    | step_stmts_nil =>
      cases hrest with
      | refl => rfl
      | step _ _ _ h _ => cases h

/-- A single statement that runs to terminal also runs to terminal when wrapped
as a singleton statement list.  This is the bridge from the `.stmt s` shape of
the source-side step rules to the `.stmts [s]` shape that the pass emits for the
pass-through `.cmd` arm. -/
theorem stmt_to_singleton_stmts {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    (s : Stmt P (Cmd P)) (ρ ρ' : Env P)
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ) (.terminal ρ')) :
    StepStmtStar P (EvalCmd P) extendEval (.stmts [s] ρ) (.terminal ρ') :=
  ReflTrans_Transitive _ _ _ _
    (stmts_cons_step P (EvalCmd P) extendEval s [] ρ ρ' h)
    (evalStmtsSmallNil P (EvalCmd P) extendEval ρ')

/-- Exiting variant of `stmt_to_singleton_stmts`: a single statement exiting
yields the singleton list exiting. -/
theorem stmt_to_singleton_stmts_exiting {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    (s : Stmt P (Cmd P)) (ρ ρ' : Env P) (lbl : String)
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ) (.exiting lbl ρ')) :
    StepStmtStar P (EvalCmd P) extendEval (.stmts [s] ρ) (.exiting lbl ρ') := by
  refine .step _ _ _ .step_stmts_cons ?_
  refine ReflTrans_Transitive _ _ _ _ (seq_inner_star P (EvalCmd P) extendEval _ _ [] h) ?_
  exact .step _ _ _ .step_seq_exit (.refl _)

/-- Outcome-generic variant of `stmt_to_singleton_stmts`: a single statement
reaching `outcomeConfig oc ρ'` yields the singleton list reaching the same
outcome. -/
theorem stmt_to_singleton_stmts_outcome {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendEval : ExtendEval P}
    (s : Stmt P (Cmd P)) (ρ ρ' : Env P) (oc : Option String)
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ) (outcomeConfig oc ρ')) :
    StepStmtStar P (EvalCmd P) extendEval (.stmts [s] ρ) (outcomeConfig oc ρ') := by
  cases oc with
  | none => exact stmt_to_singleton_stmts (extendEval := extendEval) s ρ ρ' h
  | some lbl => exact stmt_to_singleton_stmts_exiting (extendEval := extendEval) s ρ ρ' lbl h

/-- Outcome-generic decomposition of `.stmts (s :: rest)`: a run reaching
`outcomeConfig oc ρ'` either (a) had the head `s` exit (so `oc = some lbl` and
the whole list exits with that label, skipping `rest`), or (b) had `s` terminate
to some `ρ_mid` after which `rest` reached the same outcome. -/
theorem stmts_cons_outcome {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) (ρ ρ' : Env P) (oc : Option String)
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmts (s :: rest) ρ) (outcomeConfig oc ρ')) :
    (∃ lbl, oc = some lbl ∧
        StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ) (.exiting lbl ρ')) ∨
    (∃ ρ_mid, StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ) (.terminal ρ_mid) ∧
        StepStmtStar P (EvalCmd P) extendEval (.stmts rest ρ_mid) (outcomeConfig oc ρ')) := by
  -- Reduce `outcomeConfig` to a concrete constructor before inverting the run,
  -- so dependent elimination on the `.stmts (s :: rest)` head step succeeds.
  cases oc with
  | none =>
    simp only [outcomeConfig] at h ⊢
    cases h with
    | step _ _ _ hstep hrest =>
      cases hstep with
      | step_stmts_cons =>
        have ⟨ρ_mid, h_s, h_tail⟩ := seq_reaches_terminal P (EvalCmd P) extendEval hrest
        exact .inr ⟨ρ_mid, h_s, h_tail⟩
  | some lbl =>
    simp only [outcomeConfig] at h ⊢
    cases h with
    | step _ _ _ hstep hrest =>
      cases hstep with
      | step_stmts_cons =>
        rcases seq_reaches_exiting P (EvalCmd P) extendEval hrest with
          h_s | ⟨ρ_mid, h_s, h_tail⟩
        · exact .inl ⟨lbl, rfl, h_s⟩
        · exact .inr ⟨ρ_mid, h_s, h_tail⟩

/-- Forward: if a prefix list `pfx` exits with `lbl`, then `pfx ++ sfx` exits
with `lbl` (the suffix is skipped).  Mirrors `stmts_prefix_terminal_append` for
the exiting outcome. -/
theorem stmts_cons_head_exiting_append {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    (pfx sfx : List (Stmt P (Cmd P))) (ρ ρ' : Env P) (lbl : String)
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmts pfx ρ) (.exiting lbl ρ')) :
    StepStmtStar P (EvalCmd P) extendEval (.stmts (pfx ++ sfx) ρ) (.exiting lbl ρ') := by
  induction pfx generalizing ρ with
  | nil =>
    -- `.stmts [] ρ` cannot exit.
    exfalso
    cases h with
    | step _ _ _ hstep hrest =>
      cases hstep with
      | step_stmts_nil => cases hrest with | step _ _ _ h _ => cases h
  | cons s rest ih =>
    cases h with
    | step _ _ _ hstep hrest =>
      cases hstep with
      | step_stmts_cons =>
        rcases seq_reaches_exiting P (EvalCmd P) extendEval hrest with
          h_s | ⟨ρ₁, h_term, h_tail⟩
        · -- head `s` exits: lift through `step_stmts_cons`/`step_seq_exit`.
          refine .step _ _ _ .step_stmts_cons ?_
          refine ReflTrans_Transitive _ _ _ _
            (seq_inner_star P (EvalCmd P) extendEval _ _ (rest ++ sfx) h_s) ?_
          exact .step _ _ _ .step_seq_exit (.refl _)
        · -- head terminates to ρ₁, recurse on `rest`.
          exact ReflTrans_Transitive _ _ _ _
            (stmts_cons_step P (EvalCmd P) extendEval s (rest ++ sfx) ρ ρ₁ h_term)
            (ih ρ₁ h_tail)

/-- Store update that defines `ident := b`, leaving every other variable
untouched.  This is the post-state of `init $g := *` / `set $g := *` when the
havoc picks value `b`. -/
@[expose] def storeWith {P : PureExpr} [DecidableEq P.Ident] (σ : SemanticStore P) (ident : P.Ident) (b : P.Expr) :
    SemanticStore P :=
  fun y => if y = ident then some b else σ y

/-- Defining a fresh guard variable in the target store preserves
`StoreAgreement` with the source: the only changed slot is `ident`, which the
source store does not define (one-directionality of `StoreAgreement`).  This is
the mechanism by which the generated `$g` stays hidden from the source. -/
theorem storeAgreement_storeWith {P : PureExpr} [DecidableEq P.Ident]
    (σ_src σ_tgt : SemanticStore P) (ident : P.Ident) (b : P.Expr)
    (h_agree : StoreAgreement σ_src σ_tgt)
    (h_src_none : σ_src ident = none) :
    StoreAgreement σ_src (storeWith σ_tgt ident b) := by
  intro x h_def
  have h_x_def : (σ_src x).isSome = true := h_def x (List.mem_singleton.mpr rfl)
  have h_ne : x ≠ ident := by
    rintro rfl; rw [h_src_none] at h_x_def; exact absurd h_x_def (by simp)
  rw [h_agree x h_def]
  simp [storeWith, h_ne]

/-- `init $g := *` (havoc-init) with the chosen value `b` steps `.stmt (init …)`
to terminal with the slot defined to `b`, provided the slot was undefined.
The havoc value is existentially chosen by `eval_init_unconstrained`. -/
theorem step_init_havoc_to {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendEval : ExtendEval P}
    (ident : P.Ident) (ty : P.Ty) (b : P.Expr) (md : MetaData P) (ρ : Env P)
    (h_none : ρ.store ident = none)
    (hwf_var : WellFormedSemanticEvalVar ρ.eval) :
    StepStmtStar P (EvalCmd P) extendEval
      (.stmt (.cmd (HasInit.init ident ty (.nondet) md)) ρ)
      (.terminal ({ ρ with store := storeWith ρ.store ident b } : Env P)) := by
  have h_init : EvalCmd P ρ.eval ρ.store (.init ident ty .nondet md)
      (storeWith ρ.store ident b) false := by
    apply EvalCmd.eval_init_unconstrained (v := b)
    · exact InitState.init h_none (by simp [storeWith]) (by
        intro y hy; simp [storeWith, Ne.symm hy])
    · exact hwf_var
  have h_step := StepStmt.step_cmd (P := P) (EvalCmd := EvalCmd P)
    (extendEval := extendEval) (ρ := ρ) (c := HasInit.init ident ty .nondet md)
    (σ' := storeWith ρ.store ident b) (hasAssertFailure := false) h_init
  refine .step _ _ _ ?_ (.refl _)
  simpa [Bool.or_false] using h_step

/-- `havoc $g` (= `set $g := *`) with the chosen value `b` steps
`.stmt (.cmd (havoc ident))` to terminal with the slot re-defined to `b`,
provided the slot was *already* defined (UpdateState's precondition).  The
havoc value is existentially chosen by `eval_set_nondet`.  This is the
per-iteration re-havoc emitted at the body tail of the rewritten nondet loop. -/
theorem step_havoc_set_to {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendEval : ExtendEval P}
    (ident : P.Ident) (b : P.Expr) (md : MetaData P) (ρ : Env P)
    (v' : P.Expr) (h_def : ρ.store ident = some v')
    (hwf_var : WellFormedSemanticEvalVar ρ.eval) :
    StepStmtStar P (EvalCmd P) extendEval
      (.stmt (.cmd (HasHavoc.havoc ident md)) ρ)
      (.terminal ({ ρ with store := storeWith ρ.store ident b } : Env P)) := by
  have h_set : EvalCmd P ρ.eval ρ.store (.set ident .nondet md)
      (storeWith ρ.store ident b) false := by
    apply EvalCmd.eval_set_nondet (v := b)
    · exact UpdateState.update h_def (by simp [storeWith]) (by
        intro y hy; simp [storeWith, Ne.symm hy])
    · exact hwf_var
  have h_step := StepStmt.step_cmd (P := P) (EvalCmd := EvalCmd P)
    (extendEval := extendEval) (ρ := ρ) (c := HasHavoc.havoc ident md)
    (σ' := storeWith ρ.store ident b) (hasAssertFailure := false)
    (by simpa only [HasHavoc.havoc] using h_set)
  refine .step _ _ _ ?_ (.refl _)
  simpa [Bool.or_false] using h_step

/-- Reading the guard variable `mkFvar ident` out of a `storeWith _ ident b`
store yields exactly `b`.  Uses `WellFormedSemanticEvalVar` (the evaluator reads
free variables straight from the store) plus the `getFvar (mkFvar _)` round-trip
(`LawfulHasFvar`). -/
theorem eval_mkFvar_storeWith {P : PureExpr} [HasFvar P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasFvar P]
    (δ : SemanticEval P) (σ : SemanticStore P) (ident : P.Ident) (b : P.Expr)
    (hwf_var : WellFormedSemanticEvalVar δ) :
    δ (storeWith σ ident b) (HasFvar.mkFvar ident) = some b := by
  have h := hwf_var (HasFvar.mkFvar (P := P) ident) ident (storeWith σ ident b)
    (LawfulHasFvar.getFvar_mkFvar ident)
  rw [h]
  simp [storeWith]

/-! ### Agreement-preserving replay of a single source command

A source-side `EvalCmd c σ_src₀ σ_src₁ failed` can be replayed on a target store
`σ_tgt₀` that agrees with `σ_src₀` (in the `StoreAgreement` sense), producing a
`σ_tgt₁` that agrees with `σ_src₁`.  This is the workhorse of the pass-through
`.cmd` arm: the rewrite is the identity on `.cmd`, so the target replays the
exact same command, and we only need that the command's evaluation depends on
the store solely through the source-visible part.  Ported (self-contained) from
the analogous replay machinery in `structuredToUnstructured_sound_kind`. -/

/-- Invert a single `.cmd` execution: `.stmt (.cmd c) ρ →* .terminal ρ'` is
exactly one `step_cmd`, exposing the `EvalCmd` witness and the post-state. -/
theorem cmd_step_inv {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P} (c : Cmd P) (ρ ρ' : Env P)
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmt (.cmd c) ρ) (.terminal ρ')) :
    ∃ σ' haf, EvalCmd P ρ.eval ρ.store c σ' haf ∧
      ρ' = { ρ with store := σ', hasFailure := ρ.hasFailure || haf } := by
  cases h with
  | step _ _ _ hstep hrest =>
    cases hstep with
    | step_cmd hcmd =>
      cases hrest with
      | refl => exact ⟨_, _, hcmd, rfl⟩
      | step _ _ _ h _ => cases h

/-- Invert a single `.stmt s` execution to terminal: the first step is
`step_stmts_cons`-free; `s` itself steps to some `c`, then `c →* terminal`. -/
theorem stmt_step_first_inv {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P} (s : Stmt P (Cmd P)) (ρ ρ' : Env P)
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ) (.terminal ρ')) :
    ∃ c, StepStmt P (EvalCmd P) extendEval (.stmt s ρ) c ∧
      StepStmtStar P (EvalCmd P) extendEval c (.terminal ρ') := by
  cases h with
  | step _ mid _ hstep hrest => exact ⟨mid, hstep, hrest⟩

/-- First-step inversion to *any* target config: a `.stmt s ρ` reaching some
non-`.stmt`-shaped `tgt` must take at least one step (a `.stmt` is never itself a
terminal/exiting/etc. config), exposing the first step `c` and the residual run.
Used by the unified (terminal-or-exiting) simulation arms. -/
theorem stmt_step_first_inv_to {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P} (s : Stmt P (Cmd P)) (ρ : Env P) (tgt : Config P (Cmd P))
    (h_ne : ∀ ρ', tgt ≠ .stmt s ρ')
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ) tgt) :
    ∃ c, StepStmt P (EvalCmd P) extendEval (.stmt s ρ) c ∧
      StepStmtStar P (EvalCmd P) extendEval c tgt := by
  cases h with
  | refl => exact absurd rfl (h_ne ρ)
  | step _ mid _ hstep hrest => exact ⟨mid, hstep, hrest⟩

/-- Outcome-generic source nondeterministic-`ite` inversion: the chosen branch
runs to the same outcome (terminal or exiting). -/
theorem ite_nondet_step_inv_outcome {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendEval : ExtendEval P}
    (tss ess : List (Stmt P (Cmd P))) (md : MetaData P) (ρ ρ' : Env P) (oc : Option String)
    (h : StepStmtStar P (EvalCmd P) extendEval
      (.stmt (.ite .nondet tss ess md) ρ) (outcomeConfig oc ρ')) :
    StepStmtStar P (EvalCmd P) extendEval (.stmts tss ρ) (outcomeConfig oc ρ') ∨
    StepStmtStar P (EvalCmd P) extendEval (.stmts ess ρ) (outcomeConfig oc ρ') := by
  obtain ⟨c, hstep, hrest⟩ :=
    stmt_step_first_inv_to (extendEval := extendEval) _ ρ (outcomeConfig oc ρ')
      (by intro ρ'' h; cases oc <;> simp only [outcomeConfig] at h <;> cases h) h
  cases hstep with
  | step_ite_nondet_true => exact Or.inl hrest
  | step_ite_nondet_false => exact Or.inr hrest

/-- A `.seq` whose inner config runs to terminal and whose continuation list is
empty itself runs to that same terminal.  (The trailing `step_seq_done` lands on
`.stmts [] ρ'`, which is one `step_stmts_nil` from `.terminal ρ'`.) -/
theorem seq_nil_terminal {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    (inner : Config P (Cmd P)) (ρ' : Env P)
    (h : StepStmtStar P (EvalCmd P) extendEval inner (.terminal ρ')) :
    StepStmtStar P (EvalCmd P) extendEval (.seq inner []) (.terminal ρ') := by
  have h1 : StepStmtStar P (EvalCmd P) extendEval (.seq inner []) (.seq (.terminal ρ') []) :=
    seq_inner_star P (EvalCmd P) extendEval _ _ [] h
  refine ReflTrans_Transitive _ _ _ _ h1 ?_
  refine .step _ _ _ .step_seq_done ?_
  exact evalStmtsSmallNil P (EvalCmd P) extendEval ρ'

/-- Outcome-generic `.seq inner []`: if `inner` reaches `outcomeConfig oc ρ'`,
the seq with empty continuation reaches the same outcome (terminal flows through
`step_seq_done`; exiting flows through `step_seq_exit`). -/
theorem seq_nil_outcome {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendEval : ExtendEval P}
    (inner : Config P (Cmd P)) (ρ' : Env P) (oc : Option String)
    (h : StepStmtStar P (EvalCmd P) extendEval inner (outcomeConfig oc ρ')) :
    StepStmtStar P (EvalCmd P) extendEval (.seq inner []) (outcomeConfig oc ρ') := by
  cases oc with
  | none => exact seq_nil_terminal (extendEval := extendEval) inner ρ' h
  | some lbl =>
    have h1 : StepStmtStar P (EvalCmd P) extendEval (.seq inner []) (.seq (.exiting lbl ρ') []) :=
      seq_inner_star P (EvalCmd P) extendEval _ _ [] h
    refine ReflTrans_Transitive _ _ _ _ h1 ?_
    exact .step _ _ _ .step_seq_exit (.refl _)

/-- Outcome-generic `.ite .nondet` prefix replay (then side): the chosen branch
`tss` reaching `outcomeConfig oc ρt'` drives the emitted prefix to the same
outcome (havoc value `tt`). -/
theorem step_ndelim_ite_prefix_true_outcome {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasFvar P] {extendEval : ExtendEval P}
    (ident : P.Ident) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (ρ ρt' : Env P) (oc : Option String)
    (h_none : ρ.store ident = none)
    (hwf_var : WellFormedSemanticEvalVar ρ.eval)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (h_branch : StepStmtStar P (EvalCmd P) extendEval
      (.stmts tss ({ ρ with store := storeWith ρ.store ident HasBool.tt } : Env P))
      (outcomeConfig oc ρt')) :
    StepStmtStar P (EvalCmd P) extendEval
      (.stmts [.cmd (HasInit.init ident HasBool.boolTy (.nondet) md),
               .ite (.det (HasFvar.mkFvar ident)) tss ess md] ρ)
      (outcomeConfig oc ρt') := by
  let ρg : Env P := { ρ with store := storeWith ρ.store ident HasBool.tt }
  have h1 : StepStmtStar P (EvalCmd P) extendEval
      (.stmts [.cmd (HasInit.init ident HasBool.boolTy (.nondet) md),
               .ite (.det (HasFvar.mkFvar ident)) tss ess md] ρ)
      (.stmts [.ite (.det (HasFvar.mkFvar ident)) tss ess md] ρg) :=
    stmts_cons_step P (EvalCmd P) extendEval _ _ ρ ρg
      (step_init_havoc_to (extendEval := extendEval) ident HasBool.boolTy HasBool.tt md ρ h_none hwf_var)
  have h_guard : ρg.eval ρg.store (HasFvar.mkFvar ident) = some HasBool.tt :=
    eval_mkFvar_storeWith ρ.eval ρ.store ident HasBool.tt hwf_var
  have hwfb' : WellFormedSemanticEvalBool ρg.eval := hwfb
  have h2 : StepStmtStar P (EvalCmd P) extendEval
      (.stmts [.ite (.det (HasFvar.mkFvar ident)) tss ess md] ρg) (outcomeConfig oc ρt') := by
    refine .step _ _ _ .step_stmts_cons ?_
    refine .step _ _ _ (.step_seq_inner (.step_ite_true h_guard hwfb')) ?_
    exact seq_nil_outcome (extendEval := extendEval) _ _ oc h_branch
  exact ReflTrans_Transitive _ _ _ _ h1 h2

/-- Outcome-generic `.ite .nondet` prefix replay (else side). -/
theorem step_ndelim_ite_prefix_false_outcome {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasFvar P] {extendEval : ExtendEval P}
    (ident : P.Ident) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (ρ ρt' : Env P) (oc : Option String)
    (h_none : ρ.store ident = none)
    (hwf_var : WellFormedSemanticEvalVar ρ.eval)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (h_branch : StepStmtStar P (EvalCmd P) extendEval
      (.stmts ess ({ ρ with store := storeWith ρ.store ident HasBool.ff } : Env P))
      (outcomeConfig oc ρt')) :
    StepStmtStar P (EvalCmd P) extendEval
      (.stmts [.cmd (HasInit.init ident HasBool.boolTy (.nondet) md),
               .ite (.det (HasFvar.mkFvar ident)) tss ess md] ρ)
      (outcomeConfig oc ρt') := by
  let ρg : Env P := { ρ with store := storeWith ρ.store ident HasBool.ff }
  have h1 : StepStmtStar P (EvalCmd P) extendEval
      (.stmts [.cmd (HasInit.init ident HasBool.boolTy (.nondet) md),
               .ite (.det (HasFvar.mkFvar ident)) tss ess md] ρ)
      (.stmts [.ite (.det (HasFvar.mkFvar ident)) tss ess md] ρg) :=
    stmts_cons_step P (EvalCmd P) extendEval _ _ ρ ρg
      (step_init_havoc_to (extendEval := extendEval) ident HasBool.boolTy HasBool.ff md ρ h_none hwf_var)
  have h_guard : ρg.eval ρg.store (HasFvar.mkFvar ident) = some HasBool.ff :=
    eval_mkFvar_storeWith ρ.eval ρ.store ident HasBool.ff hwf_var
  have hwfb' : WellFormedSemanticEvalBool ρg.eval := hwfb
  have h2 : StepStmtStar P (EvalCmd P) extendEval
      (.stmts [.ite (.det (HasFvar.mkFvar ident)) tss ess md] ρg) (outcomeConfig oc ρt') := by
    refine .step _ _ _ .step_stmts_cons ?_
    refine .step _ _ _ (.step_seq_inner (.step_ite_false h_guard hwfb')) ?_
    exact seq_nil_outcome (extendEval := extendEval) _ _ oc h_branch
  exact ReflTrans_Transitive _ _ _ _ h1 h2

/-! ### ReflTransT decomposition helpers (for the loop fuel induction)

These are pure structured-semantics facts about `StepStmt`/`ReflTransT` (the
*Type*-valued, length-carrying multi-step closure).  They split a run that
reaches `.terminal` into its constituent sub-runs while exposing a strict
length decrease, which is what feeds the `decreasing_by`/`termination_by`
fuel induction used by the `.loop` simulation arms.  They are independent of
the rewritten (target) program shape, so they hold over the source semantics
verbatim. -/

/-- Split a `.seq inner ss` run reaching `.terminal` into a run of the inner
config to `.terminal` followed by a run of the remaining statements, with the
two sub-run lengths summing strictly below the original. -/
theorem seqT_reaches_terminal {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    {inner : Config P (Cmd P)} {ss : List (Stmt P (Cmd P))} {ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.seq inner ss) (.terminal ρ')) :
    ∃ (ρ₁ : Env P), ∃ (h1 : ReflTransT (StepStmt P (EvalCmd P) extendEval) inner (.terminal ρ₁)),
      ∃ (h2 : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.stmts ss ρ₁) (.terminal ρ')),
      h1.len + h2.len < hstar.len := by
  match hstar with
  | .step _ _ _ (.step_seq_inner h) hrest =>
    have ⟨ρ₁, hterm, htail, hlen⟩ := seqT_reaches_terminal hrest
    exact ⟨ρ₁, .step _ _ _ h hterm, htail, by simp [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_seq_done hrest =>
    exact ⟨_, .refl _, hrest, by show 0 + hrest.len < 1 + hrest.len; omega⟩
  | .step _ _ _ .step_seq_exit hrest =>
    match hrest with
    | .step _ _ _ h _ => exact nomatch h

/-- Split a `(s :: rest)` statement-list run reaching `.terminal` into a run of
the head statement to `.terminal` followed by a run of the tail, with a `+ 2`
length slack (the `step_stmts_cons` and `step_seq_done` administrative steps). -/
theorem stmtsT_cons_terminal {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendEval : ExtendEval P}
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))} {ρ₀ ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.stmts (s :: rest) ρ₀) (.terminal ρ')) :
    ∃ (ρ₁ : Env P), ∃ (h1 : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.stmt s ρ₀) (.terminal ρ₁)),
      ∃ (h2 : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.stmts rest ρ₁) (.terminal ρ')),
      h1.len + h2.len + 2 ≤ hstar.len := by
  match hstar with
  | .step _ _ _ .step_stmts_cons hrest =>
    have ⟨ρ₁, h1, h2, hlen⟩ := seqT_reaches_terminal (extendEval := extendEval) hrest
    exact ⟨ρ₁, h1, h2, by simp [ReflTransT.len]; omega⟩

/-- Invert a block execution reaching terminal when the inner config cannot
exit: the inner reaches terminal with a strictly shorter derivation, and the
block's result store is the inner store projected through the parent store. -/
theorem blockT_reaches_terminal_noExit {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    {inner : Config P (Cmd P)} {l : Option String} {σ_parent : SemanticStore P} {ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.block l σ_parent inner) (.terminal ρ'))
    (h_no_exit : ∀ lbl ρ_x,
      ¬ StepStmtStar P (EvalCmd P) extendEval inner (.exiting lbl ρ_x)) :
    ∃ (ρ_inner : Env P) (h : ReflTransT (StepStmt P (EvalCmd P) extendEval) inner (.terminal ρ_inner)),
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } ∧
      h.len < hstar.len := by
  match hstar with
  | .step _ (.block _ _ inner₁) _ (.step_block_body h) hrest =>
    have h_no_exit' : ∀ lbl ρ_x,
        ¬ StepStmtStar P (EvalCmd P) extendEval inner₁ (.exiting lbl ρ_x) := by
      intro lbl ρ_x hinner₁
      exact h_no_exit lbl ρ_x (.step _ _ _ h hinner₁)
    have ⟨ρ_inner, hterm, heq, hlen⟩ := blockT_reaches_terminal_noExit hrest h_no_exit'
    exact ⟨ρ_inner, .step _ _ _ h hterm, heq, by simp [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_block_done hrest =>
    match hrest with
    | .refl _ => exact ⟨_, .refl _, rfl, by simp [ReflTransT.len]⟩
    | .step _ _ _ h _ => exact nomatch h
  | .step _ _ _ (.step_block_exit_match _) hrest =>
    exfalso
    exact h_no_exit _ _ (.refl _)
  | .step _ _ _ (.step_block_exit_mismatch _) hrest =>
    match hrest with
    | .step _ _ _ h _ => exact nomatch h

/-- With an empty invariant list, the `hasInvFailure` flag returned by any
`step_loop_*` rule is vacuously `false`: the boolean iff cannot witness an
invariant in an empty list. -/
theorem empty_inv_no_failure
    {α : Type} {Q : α → Prop} {hasInvFailure : Bool}
    (hff_iff : hasInvFailure = true ↔ ∃ le, le ∈ ([] : List α) ∧ Q le) :
    hasInvFailure = false := by
  cases hb : hasInvFailure with
  | false => rfl
  | true =>
    rw [hb] at hff_iff
    have ⟨_, hmem, _⟩ := hff_iff.mp rfl
    exact ((List.mem_nil_iff _).mp hmem).elim

/-- Type-valued inversion of an *anonymous* (`.none`-labeled) block reaching
terminal: the inner config reaches terminal with a strictly shorter derivation,
and the block's result store is the inner store projected through the parent
store.  Unlike `blockT_reaches_terminal_noExit`, no `h_no_exit` premise is
needed — a `.none` block can never match an exiting label, so the only way to
reach `.terminal` is for the inner config to terminate. -/
theorem blockT_none_reaches_terminal {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    {inner : Config P (Cmd P)} {σ_parent : SemanticStore P} {ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.block .none σ_parent inner) (.terminal ρ')) :
    ∃ (ρ_inner : Env P) (h : ReflTransT (StepStmt P (EvalCmd P) extendEval) inner (.terminal ρ_inner)),
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
  | .step _ _ _ (.step_block_exit_match heq) hrest =>
    -- `.none = .some l` is impossible.
    exact nomatch heq
  | .step _ _ _ (.step_block_exit_mismatch _) hrest =>
    match hrest with
    | .step _ _ _ h _ => exact nomatch h

/-- Type-valued inversion of a `.seq inner ss` run reaching `.exiting lbl`:
either the inner config exits (skipping `ss`), or the inner config terminates
and `ss` reaches the exiting outcome.  Both pieces carry a strict len-decrease. -/
theorem seqT_reaches_exiting {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    {inner : Config P (Cmd P)} {ss : List (Stmt P (Cmd P))} {lbl : String} {ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.seq inner ss) (.exiting lbl ρ')) :
    (∃ (h : ReflTransT (StepStmt P (EvalCmd P) extendEval) inner (.exiting lbl ρ')),
        h.len < hstar.len) ∨
    (∃ (ρ₁ : Env P)
        (h1 : ReflTransT (StepStmt P (EvalCmd P) extendEval) inner (.terminal ρ₁))
        (h2 : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.stmts ss ρ₁) (.exiting lbl ρ')),
        h1.len + h2.len < hstar.len) := by
  match hstar with
  | .step _ _ _ (.step_seq_inner h) hrest =>
    rcases seqT_reaches_exiting hrest with ⟨hexit, hlen⟩ | ⟨ρ₁, h1, h2, hlen⟩
    · exact .inl ⟨.step _ _ _ h hexit, by simp only [ReflTransT.len]; omega⟩
    · exact .inr ⟨ρ₁, .step _ _ _ h h1, h2, by simp only [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_seq_done hrest =>
    exact .inr ⟨_, .refl _, hrest, by simp only [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_seq_exit hrest =>
    exact .inl ⟨hrest, by simp only [ReflTransT.len]; omega⟩

/-- Type-valued inversion of an anonymous (`.none`-labeled) block reaching
`.exiting lbl`: the inner config exits with the *same* label `lbl` (the `.none`
block never matches, so the exit propagates unchanged), with a strict
len-decrease.  The result store is projected through the parent store. -/
theorem blockT_none_reaches_exiting {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    {inner : Config P (Cmd P)} {σ_parent : SemanticStore P} {lbl : String} {ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.block .none σ_parent inner) (.exiting lbl ρ')) :
    ∃ (ρ_inner : Env P) (h : ReflTransT (StepStmt P (EvalCmd P) extendEval) inner (.exiting lbl ρ_inner)),
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } ∧
      h.len < hstar.len := by
  match hstar with
  | .step _ (.block _ _ inner₁) _ (.step_block_body h) hrest =>
    have ⟨ρ_inner, hexit, heq, hlen⟩ := blockT_none_reaches_exiting hrest
    exact ⟨ρ_inner, .step _ _ _ h hexit, heq, by simp only [ReflTransT.len]; omega⟩
  | .step _ _ _ (.step_block_exit_mismatch _) hrest =>
    match hrest with
    | .refl _ => exact ⟨_, .refl _, rfl, by simp [ReflTransT.len]⟩
    | .step _ _ _ h _ => exact nomatch h
  | .step _ _ _ (.step_block_exit_match heq) hrest =>
    exact nomatch heq
  | .step _ _ _ .step_block_done hrest =>
    match hrest with
    | .step _ _ _ h _ => exact nomatch h

/-- Type-valued inversion of a singleton statement-list `[s]` reaching
`.exiting lbl`: the head statement reaches the exiting outcome, with a strict
len-decrease (the `step_stmts_cons` administrative step). -/
theorem stmtsT_singleton_exiting {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendEval : ExtendEval P}
    {s : Stmt P (Cmd P)} {lbl : String} {ρ₀ ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.stmts [s] ρ₀) (.exiting lbl ρ')) :
    ∃ (h : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.stmt s ρ₀) (.exiting lbl ρ')),
      h.len < hstar.len := by
  match hstar with
  | .step _ _ _ .step_stmts_cons hrest =>
    rcases seqT_reaches_exiting (extendEval := extendEval) hrest with ⟨hexit, hlen⟩ | ⟨ρ₁, _, h2, hlen⟩
    · exact ⟨hexit, by simp only [ReflTransT.len]; omega⟩
    · -- The tail `[]` cannot reach `.exiting`: it steps to `.terminal` only.
      match h2 with
      | .step _ _ _ .step_stmts_nil hr =>
        match hr with
        | .step _ _ _ h _ => exact nomatch h

/-- First-step inversion of a deterministic loop run reaching an outcome
(`outcomeConfig oc ρ'`).  The first step is either `step_loop_exit` (guard `ff`,
residual run from `.terminal (ρ + false)`) or `step_loop_enter` (guard `tt`,
residual run from `.seq (.block .none ρ.store (.stmts body (ρ + false))) [loop]`).
With empty invariants the `hasInvFailure` flag is `false`, and the residual
carries a strict len-decrease.  Casing `oc` makes the outcome target a
constructor, so the `.refl` case (which would require `outcomeConfig oc ρ' =
.stmt (.loop …)`) is ruled out by constructor mismatch. -/
theorem loop_det_step_first_inv {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    {e : P.Expr} {m : Option P.Expr}
    {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {ρ ρ' : Env P} {oc : Option String}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval)
      (.stmt (.loop (.det e) m ([] : List (String × P.Expr)) body md) ρ) (outcomeConfig oc ρ')) :
    (ρ.eval ρ.store e = some HasBool.ff ∧ WellFormedSemanticEvalBool ρ.eval ∧
        ∃ (hrest : ReflTransT (StepStmt P (EvalCmd P) extendEval)
            (.terminal ({ ρ with hasFailure := ρ.hasFailure || false } : Env P))
            (outcomeConfig oc ρ')),
          hrest.len < hstar.len) ∨
    (ρ.eval ρ.store e = some HasBool.tt ∧ WellFormedSemanticEvalBool ρ.eval ∧
        ∃ (hrest : ReflTransT (StepStmt P (EvalCmd P) extendEval)
            (.seq (.block .none ρ.store (.stmts body
                ({ ρ with hasFailure := ρ.hasFailure || false } : Env P)))
              [.loop (.det e) m ([] : List (String × P.Expr)) body md])
            (outcomeConfig oc ρ')),
          hrest.len < hstar.len) := by
  cases oc with
  | none =>
    simp only [outcomeConfig] at hstar ⊢
    match hstar with
    | .step _ _ _ (@StepStmt.step_loop_exit _ _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure h_cond _ hff_iff hwfb_s) hrest =>
      have h_no : hasInvFailure = false := empty_inv_no_failure hff_iff
      subst h_no
      refine .inl ⟨h_cond, hwfb_s, hrest, ?_⟩
      simp only [ReflTransT.len]; omega
    | .step _ _ _ (@StepStmt.step_loop_enter _ _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure h_cond _ hff_iff hwfb_s) hrest =>
      have h_no : hasInvFailure = false := empty_inv_no_failure hff_iff
      subst h_no
      refine .inr ⟨h_cond, hwfb_s, hrest, ?_⟩
      simp only [ReflTransT.len]; omega
  | some lbl =>
    simp only [outcomeConfig] at hstar ⊢
    match hstar with
    | .step _ _ _ (@StepStmt.step_loop_exit _ _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure h_cond _ hff_iff hwfb_s) hrest =>
      have h_no : hasInvFailure = false := empty_inv_no_failure hff_iff
      subst h_no
      refine .inl ⟨h_cond, hwfb_s, hrest, ?_⟩
      simp only [ReflTransT.len]; omega
    | .step _ _ _ (@StepStmt.step_loop_enter _ _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure h_cond _ hff_iff hwfb_s) hrest =>
      have h_no : hasInvFailure = false := empty_inv_no_failure hff_iff
      subst h_no
      refine .inr ⟨h_cond, hwfb_s, hrest, ?_⟩
      simp only [ReflTransT.len]; omega

/-- First-step inversion of a *nondeterministic* loop run reaching an outcome
(`outcomeConfig oc ρ'`).  The first step is either `step_loop_nondet_exit`
(residual run from `.terminal (ρ + false)`) or `step_loop_nondet_enter`
(residual run from `.seq (.block .none ρ.store (.stmts body (ρ + false))) [loop]`).
With empty invariants the `hasInvFailure` flag is `false`, and the residual
carries a strict len-decrease.  Unlike the deterministic variant there is *no*
guard read: the enter/exit choice is genuinely nondeterministic. -/
theorem loop_nondet_step_first_inv {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] {extendEval : ExtendEval P}
    {m : Option P.Expr}
    {body : List (Stmt P (Cmd P))} {md : MetaData P}
    {ρ ρ' : Env P} {oc : Option String}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval)
      (.stmt (.loop .nondet m ([] : List (String × P.Expr)) body md) ρ) (outcomeConfig oc ρ')) :
    (∃ (hrest : ReflTransT (StepStmt P (EvalCmd P) extendEval)
        (.terminal ({ ρ with hasFailure := ρ.hasFailure || false } : Env P))
        (outcomeConfig oc ρ')),
      hrest.len < hstar.len) ∨
    (∃ (hrest : ReflTransT (StepStmt P (EvalCmd P) extendEval)
        (.seq (.block .none ρ.store (.stmts body
            ({ ρ with hasFailure := ρ.hasFailure || false } : Env P)))
          [.loop .nondet m ([] : List (String × P.Expr)) body md])
        (outcomeConfig oc ρ')),
      hrest.len < hstar.len) := by
  cases oc with
  | none =>
    simp only [outcomeConfig] at hstar ⊢
    match hstar with
    | .step _ _ _ (@StepStmt.step_loop_nondet_exit _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure _ hff_iff) hrest =>
      have h_no : hasInvFailure = false := empty_inv_no_failure hff_iff
      subst h_no
      exact .inl ⟨hrest, by simp only [ReflTransT.len]; omega⟩
    | .step _ _ _ (@StepStmt.step_loop_nondet_enter _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure _ hff_iff) hrest =>
      have h_no : hasInvFailure = false := empty_inv_no_failure hff_iff
      subst h_no
      exact .inr ⟨hrest, by simp only [ReflTransT.len]; omega⟩
  | some lbl =>
    simp only [outcomeConfig] at hstar ⊢
    match hstar with
    | .step _ _ _ (@StepStmt.step_loop_nondet_exit _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure _ hff_iff) hrest =>
      have h_no : hasInvFailure = false := empty_inv_no_failure hff_iff
      subst h_no
      exact .inl ⟨hrest, by simp only [ReflTransT.len]; omega⟩
    | .step _ _ _ (@StepStmt.step_loop_nondet_enter _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure _ hff_iff) hrest =>
      have h_no : hasInvFailure = false := empty_inv_no_failure hff_iff
      subst h_no
      exact .inr ⟨hrest, by simp only [ReflTransT.len]; omega⟩

/-! ### Slot-definedness frame (the gen guard survives the rewritten body)

The generated loop guard `$g` is `init`'d in the parent (target) scope before
the loop, so it is *defined* when the per-iteration block starts.  Running the
rewritten body `body'` cannot *undefine* it: `init`/`set` only ever assign
`some`, and the only operation that can turn a slot to `none` —
`projectStore` at a block boundary — gates on the block's recorded parent, where
`$g` was already defined.  Hence `$g` stays defined throughout `body'`, which is
exactly the precondition for the body-tail re-havoc `set $g := *`.  This frame
fact needs *no* characterization of what `body'` writes: it is a structural
property of the small-step semantics. -/

/-- A single `EvalCmd` never undefines a slot: any `y` that was `isSome` stays
`isSome` (`init`/`set` only assign `some`; `assert`/`assume`/`cover` keep the
store). -/
theorem EvalCmd_preserves_isSome {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {δ : SemanticEval P} {σ σ' : SemanticStore P} {c : Cmd P} {haf : Bool}
    (h : EvalCmd P δ σ c σ' haf)
    {y : P.Ident} (h_some : (σ y).isSome = true) :
    (σ' y).isSome = true := by
  cases h with
  | eval_init heval hinit hwfvar hwfcongr =>
    rename_i ty md x v e
    cases hinit with
    | init _ h_xv h_other =>
      by_cases hxy : x = y
      · subst hxy; rw [h_xv]; rfl
      · rw [h_other y hxy]; exact h_some
  | eval_init_unconstrained hinit hwfvar =>
    rename_i ty md x v
    cases hinit with
    | init _ h_xv h_other =>
      by_cases hxy : x = y
      · subst hxy; rw [h_xv]; rfl
      · rw [h_other y hxy]; exact h_some
  | eval_set heval hupd hwfvar hwfcongr =>
    rename_i md x v e
    cases hupd with
    | update _ h_xv h_other =>
      by_cases hxy : x = y
      · subst hxy; rw [h_xv]; rfl
      · rw [h_other y hxy]; exact h_some
  | eval_set_nondet hupd hwfvar =>
    rename_i md x v
    cases hupd with
    | update _ h_xv h_other =>
      by_cases hxy : x = y
      · subst hxy; rw [h_xv]; rfl
      · rw [h_other y hxy]; exact h_some
  | eval_assert_pass _ _ _ => exact h_some
  | eval_assert_fail _ _ _ => exact h_some
  | eval_assume _ _ _ => exact h_some
  | eval_cover _ => exact h_some

/-- `y` is defined in a config's operative store and in every block-parent on its
stack.  The invariant that makes "the gen guard stays defined" step-preservable. -/
@[expose] def GuardDefined {P : PureExpr} (y : P.Ident) : Config P (Cmd P) → Prop
  | .stmt _ ρ => (ρ.store y).isSome = true
  | .stmts _ ρ => (ρ.store y).isSome = true
  | .terminal ρ => (ρ.store y).isSome = true
  | .exiting _ ρ => (ρ.store y).isSome = true
  | .block _ σ_parent inner => (σ_parent y).isSome = true ∧ GuardDefined y inner
  | .seq inner _ => GuardDefined y inner

/-- A single step preserves `GuardDefined`. -/
theorem step_preserves_GuardDefined {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendEval : ExtendEval P}
    {y : P.Ident} {c c' : Config P (Cmd P)}
    (hstep : StepStmt P (EvalCmd P) extendEval c c')
    (h : GuardDefined y c) :
    GuardDefined y c' := by
  induction hstep with
  | step_cmd hcmd =>
    rename_i ρ cc σ' haf
    exact EvalCmd_preserves_isSome hcmd h
  | step_block =>
    rename_i label ss md ρ
    exact ⟨h, h⟩
  | step_ite_true _ _ => exact h
  | step_ite_false _ _ => exact h
  | step_ite_nondet_true => exact h
  | step_ite_nondet_false => exact h
  | step_loop_enter _ _ _ _ => exact ⟨h, h⟩
  | step_loop_exit _ _ _ _ => exact h
  | step_loop_nondet_enter _ _ => exact ⟨h, h⟩
  | step_loop_nondet_exit _ _ => exact h
  | step_exit => exact h
  | step_funcDecl => exact h
  | step_typeDecl => exact h
  | step_stmts_nil => exact h
  | step_stmts_cons => exact h
  | step_seq_inner _ ih => exact ih h
  | step_seq_done => exact h
  | step_seq_exit => exact h
  | step_block_body _ ih =>
    exact ⟨h.1, ih h.2⟩
  | step_block_done =>
    simp only [GuardDefined, projectStore] at h ⊢
    rw [if_pos h.1]; exact h.2
  | step_block_exit_match heq =>
    simp only [GuardDefined, projectStore] at h ⊢
    rw [if_pos h.1]; exact h.2
  | step_block_exit_mismatch hne =>
    simp only [GuardDefined, projectStore] at h ⊢
    rw [if_pos h.1]; exact h.2

/-- Multi-step preservation of `GuardDefined`. -/
theorem star_preserves_GuardDefined {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendEval : ExtendEval P}
    {y : P.Ident} {c c' : Config P (Cmd P)}
    (hstar : StepStmtStar P (EvalCmd P) extendEval c c')
    (h : GuardDefined y c) :
    GuardDefined y c' := by
  induction hstar with
  | refl => exact h
  | step _ _ _ hstep _ ih => exact ih (step_preserves_GuardDefined (extendEval := extendEval) hstep h)

/-- The gen guard `y`, defined in the start store, stays defined after running a
statement list to terminal. -/
theorem stmts_preserves_isSome {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] {extendEval : ExtendEval P}
    {y : P.Ident} {ss : List (Stmt P (Cmd P))} {ρ ρ' : Env P}
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ) (.terminal ρ'))
    (h_some : (ρ.store y).isSome = true) :
    (ρ'.store y).isSome = true :=
  star_preserves_GuardDefined (extendEval := extendEval) hstar (show GuardDefined y (.stmts ss ρ) from h_some)


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
composition argument restrict freshness to just the labels *this* pass mints. -/
@[expose] def GenFreshStore {P : PureExpr} [HasIdent P]
    (Q : String → Prop)
    (σ : StringGenState) (σ_tgt : SemanticStore P) : Prop :=
  ∀ s, Q s → s ∉ σ.stringGens →
    σ_tgt (HasIdent.ident (P := P) s) = none

/-- The freshly-generated guard's slot is undefined in a `GenFreshStore` target,
given `WF σ` and that the freshly minted label satisfies the kind predicate. -/
theorem GenFreshStore.gen_slot_none {P : PureExpr} [HasIdent P]
    {Q : String → Prop}
    {σ : StringGenState} {σ_tgt : SemanticStore P}
    (pf : String) (h_fresh : GenFreshStore Q σ σ_tgt) (hwf : StringGenState.WF σ)
    (hQ : Q (StringGenState.gen pf σ).1) :
    σ_tgt (HasIdent.ident (P := P) (StringGenState.gen pf σ).1) = none :=
  h_fresh _ hQ (StringGenState.stringGens_gen_not_in pf σ hwf)

/-- `GenFreshStore` is preserved across defining the freshly-generated guard
`g := (gen pf σ).1` (via `storeWith`), advancing the state to `(gen pf σ).2`. -/
theorem GenFreshStore.storeWith_gen {P : PureExpr} [HasIdent P] [DecidableEq P.Ident]
    [LawfulHasIdent P]
    {Q : String → Prop}
    {σ : StringGenState} {σ_tgt : SemanticStore P}
    (pf : String) (b : P.Expr) (h_fresh : GenFreshStore Q σ σ_tgt) :
    GenFreshStore Q (StringGenState.gen pf σ).2
      (storeWith σ_tgt (HasIdent.ident (P := P) (StringGenState.gen pf σ).1) b) := by
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
theorem GenFreshStore.mono {P : PureExpr} [HasIdent P]
    {Q : String → Prop}
    {σ σ' : StringGenState} {σ_tgt : SemanticStore P}
    (h_step : StringGenState.GenStep σ σ')
    (h_fresh : GenFreshStore Q σ σ_tgt) :
    GenFreshStore Q σ' σ_tgt := by
  intro s h_suf h_nin
  exact h_fresh s h_suf (fun h => h_nin (h_step.subset h))

end Freshness

/-! ### Source store-frame preservation

A source command/statement execution can only change store slots that the
command *defines* (for `init`) or *modifies* (for `set`); a slot that was
`none` and is neither defined nor a `set` target stays `none`.  This is the
mechanism by which the source side preserves freshness of gen-shaped names
across sequencing (the names a source program writes are user names, never
gen-shaped). -/

section SrcFrame

/-- A single `EvalCmd` preserves a `none` slot `y` that the command does not
define and does not assign to.  (`set`/`init` to `y` are the only writers; both
list `y` only when it is their target.) -/
theorem evalCmd_preserves_none {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVarsPure P P.Expr]
    {δ : SemanticEval P} {σ σ' : SemanticStore P} {c : Cmd P} {haf : Bool}
    (h : EvalCmd P δ σ c σ' haf)
    {y : P.Ident}
    (h_none : σ y = none)
    (h_not_def : y ∉ Cmd.definedVars c)
    (h_not_mod : y ∉ Cmd.modifiedVars c) :
    σ' y = none := by
  cases h with
  | eval_init heval hinit hwfvar hwfcongr =>
    rename_i ty md x v e
    have h_ne : x ≠ y := by
      intro h_eq; apply h_not_def
      rw [h_eq]; with_unfolding_all exact List.mem_singleton.mpr rfl
    cases hinit with
    | init _ _ h_other => rw [h_other y h_ne]; exact h_none
  | eval_init_unconstrained hinit hwfvar =>
    rename_i ty md x v
    have h_ne : x ≠ y := by
      intro h_eq; apply h_not_def
      rw [h_eq]; with_unfolding_all exact List.mem_singleton.mpr rfl
    cases hinit with
    | init _ _ h_other => rw [h_other y h_ne]; exact h_none
  | eval_set heval hupd hwfvar hwfcongr =>
    rename_i md x v e
    have h_ne : x ≠ y := by
      intro h_eq; apply h_not_mod
      rw [h_eq]; with_unfolding_all exact List.mem_singleton.mpr rfl
    cases hupd with
    | update _ _ h_other => rw [h_other y h_ne]; exact h_none
  | eval_set_nondet hupd hwfvar =>
    rename_i md x v
    have h_ne : x ≠ y := by
      intro h_eq; apply h_not_mod
      rw [h_eq]; with_unfolding_all exact List.mem_singleton.mpr rfl
    cases hupd with
    | update _ _ h_other => rw [h_other y h_ne]; exact h_none
  | eval_assert_pass _ _ _ => exact h_none
  | eval_assert_fail _ _ _ => exact h_none
  | eval_assume _ _ _ => exact h_none
  | eval_cover _ => exact h_none

end SrcFrame

/-! ### Source-shape precondition (spec §7)

The simulation is only sound for source programs that never `init`/`set` a
gen-shaped (`HasUnderscoreDigitSuffix`) variable.  Spec §7 states this as an
explicit assumption: the front-ends feeding this pipeline never write such
names, and a source program that re-`init`s a parent-scoped variable inside a
loop body is already stuck under the existing semantics, independent of this
pass.  Without it the theorem is false — a pass-through source
`.cmd (set "$g_0" .nondet)` defines a gen-shaped slot, after which a later
`.ite .nondet`'s inserted `init $g := *` would collide and be stuck.

We carry it as `NoGenSuffix` over the block's defined + modified variables
(mirroring `structuredToUnstructured_sound_kind`'s threaded `NoGenSuffix` on
`definedVars ++ initVars` / `modifiedVars`).  Membership in `++` distributes
the obligation across sequencing and recursion automatically. -/

/-- Every ident in `xs` was supplied by user source: it is `HasIdent.ident s`
only for strings `s` that do *not* satisfy the kind predicate `Q` (the kind of
label this pass mints).  Instantiating `Q := HasUnderscoreDigitSuffix` recovers
the blanket "no statement writes a gen-shaped variable" condition. -/
@[expose] def NoGenSuffix {P : PureExpr} [HasIdent P]
    (Q : String → Prop)
    (xs : List P.Ident) : Prop :=
  ∀ x ∈ xs, ∀ s : String,
    x = HasIdent.ident (P := P) s → ¬ Q s

/-- The source-shape precondition over a source block: no statement in `ss`
ever defines or modifies a `Q`-kind variable. -/
@[expose] def SrcNoGenWrites {P : PureExpr} [HasIdent P] [HasVarsPure P P.Expr]
    (Q : String → Prop)
    (ss : List (Stmt P (Cmd P))) : Prop :=
  NoGenSuffix (P := P) Q (Block.definedVars ss ++ Block.modifiedVars ss)

/-- A single `EvalCmd` whose command writes no `Q`-kind variable preserves the
"no `Q`-kind slot is defined" invariant on its store. -/
theorem evalCmd_preserves_src_fresh {P : PureExpr} [HasFvar P] [HasBool P]
    [HasNot P] [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {Q : String → Prop}
    {δ : SemanticEval P} {σ σ' : SemanticStore P} {c : Cmd P} {haf : Bool}
    (h : EvalCmd P δ σ c σ' haf)
    (h_src_fresh : ∀ s, Q s →
      σ (HasIdent.ident (P := P) s) = none)
    (h_no_writes : NoGenSuffix (P := P) Q (Cmd.definedVars c ++ Cmd.modifiedVars c)) :
    ∀ s, Q s →
      σ' (HasIdent.ident (P := P) s) = none := by
  intro s h_suf
  have h_none : σ (HasIdent.ident (P := P) s) = none := h_src_fresh s h_suf
  refine evalCmd_preserves_none (P := P) h h_none ?_ ?_
  · intro h_mem
    exact (h_no_writes _ (List.mem_append_left _ h_mem) s rfl) h_suf
  · intro h_mem
    exact (h_no_writes _ (List.mem_append_right _ h_mem) s rfl) h_suf

/-- Bidirectional agreement off the gen-shaped names: the target and source
stores assign the same value at every ident that is *definitely not* a
gen-shaped name (i.e. either not `HasIdent.ident _` of any string, or
`HasIdent.ident s` for a non-gen-shaped `s`).  Stronger than `StoreAgreement`
(which is one-directional and only on source-defined vars), but agrees with it
off the guards: the only slots on which target may differ from source are the
gen-shaped guard slots.  This is the invariant the `.cmd`/`init` arm needs (a
source-fresh user var stays fresh in the target). -/
@[expose] def AgreeOffGen {P : PureExpr} [HasIdent P]
    (Q : String → Prop)
    (σ_src σ_tgt : SemanticStore P) : Prop :=
  ∀ x : P.Ident,
    (∀ s : String, x = HasIdent.ident (P := P) s → ¬ Q s) →
    σ_tgt x = σ_src x

/-- `AgreeOffGen` is reflexive. -/
theorem AgreeOffGen.refl {P : PureExpr} [HasIdent P] {Q : String → Prop}
    (σ : SemanticStore P) :
    AgreeOffGen Q σ σ := fun _ _ => rfl

/-- Defining a gen-shaped guard `ident = HasIdent.ident g` (`g` gen-shaped) in the
target store preserves `AgreeOffGen`: the only changed slot is `ident`, which is
gen-shaped, so the off-gen equation (which constrains only non-gen idents) is
untouched. -/
theorem AgreeOffGen.storeWith_gen {P : PureExpr} [HasIdent P] [LawfulHasIdent P]
    [DecidableEq P.Ident]
    {Q : String → Prop}
    {σ_src σ_tgt : SemanticStore P} {g : String} {b : P.Expr}
    (h_off : AgreeOffGen Q σ_src σ_tgt)
    (h_gen : Q g) :
    AgreeOffGen Q σ_src (storeWith σ_tgt (HasIdent.ident (P := P) g) b) := by
  intro x h_nongen
  have h_ne : x ≠ HasIdent.ident (P := P) g := by
    rintro rfl
    exact (h_nongen g rfl) h_gen
  show (if x = HasIdent.ident (P := P) g then some b else σ_tgt x) = σ_src x
  rw [if_neg h_ne]; exact h_off x h_nongen

section CmdReplayOffGen

/-- `AgreeOffGen` implies pointwise equality on the variables of an expression
defined in the source — those vars are non-gen (defined ⇒ `isSome`, but a
gen-shaped slot is `none` by source-freshness). -/
theorem agreeOffGen_pointwise_on_expr_vars {P : PureExpr} [HasIdent P]
    [HasVarsPure P P.Expr]
    {Q : String → Prop}
    (σ_src σ_tgt : SemanticStore P) (e : P.Expr)
    (h_off : AgreeOffGen Q σ_src σ_tgt)
    (h_src_fresh : ∀ s, Q s →
      σ_src (HasIdent.ident (P := P) s) = none)
    (h_def : isDefined σ_src (HasVarsPure.getVars e)) :
    ∀ x ∈ HasVarsPure.getVars e, σ_src x = σ_tgt x := by
  intro x hx
  have h_x_some : (σ_src x).isSome = true := h_def x hx
  have h_nongen : ∀ s : String, x = HasIdent.ident (P := P) s →
      ¬ Q s := by
    intro s h_eq h_suf
    rw [h_eq, h_src_fresh s h_suf] at h_x_some
    exact absurd h_x_some (by simp)
  exact (h_off x h_nongen).symm

/-- Replay a source `EvalCmd` step on a target store that `AgreeOffGen`s the
source, given the command writes no gen-shaped variable.  Produces a target
post-store that still `AgreeOffGen`s the source post-store. -/
theorem cmd_replay_offgen {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasIdent P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    {Q : String → Prop}
    (δ : SemanticEval P) (σ_src₀ σ_tgt₀ : SemanticStore P)
    (c : Cmd P) (σ_src₁ : SemanticStore P) (failed : Bool)
    (h_off : AgreeOffGen Q σ_src₀ σ_tgt₀)
    (h_eval : EvalCmd P δ σ_src₀ c σ_src₁ failed)
    (h_wf_def : WellFormedSemanticEvalDef δ)
    (h_congr : WellFormedSemanticEvalExprCongr δ)
    (h_src_fresh : ∀ s, Q s →
      σ_src₀ (HasIdent.ident (P := P) s) = none)
    (h_no_writes : NoGenSuffix (P := P) Q (Cmd.definedVars c ++ Cmd.modifiedVars c)) :
    ∃ σ_tgt₁, EvalCmd P δ σ_tgt₀ c σ_tgt₁ failed
            ∧ AgreeOffGen Q σ_src₁ σ_tgt₁ := by
  -- The target keeps the same write var `x ↦ v`; off `x` the two post-stores
  -- agree off-gen by `h_off` (both unchanged off `x`).
  cases h_eval with
  | eval_init heval hinit hwfvar hwfcongr =>
    rename_i ty md x v e
    have h_x_nongen : ∀ s : String, x = HasIdent.ident (P := P) s →
        ¬ Q s := by
      intro s heq; apply h_no_writes x (List.mem_append_left _ ?_) s heq
      with_unfolding_all exact List.mem_singleton.mpr rfl
    have h_def_e : isDefined σ_src₀ (HasVarsPure.getVars e) := h_wf_def e v σ_src₀ heval
    have h_pointwise : ∀ y ∈ HasVarsPure.getVars e, σ_src₀ y = σ_tgt₀ y :=
      agreeOffGen_pointwise_on_expr_vars σ_src₀ σ_tgt₀ e h_off h_src_fresh h_def_e
    have h_eval_tgt : δ σ_tgt₀ e = .some v := by
      rw [← heval]; exact (h_congr e σ_src₀ σ_tgt₀ h_pointwise).symm
    cases hinit with
    | init h_xn h_xv h_other =>
      have h_tgt_x_none : σ_tgt₀ x = none := by rw [h_off x h_x_nongen]; exact h_xn
      let σ_tgt₁ : SemanticStore P := fun y => if y = x then some v else σ_tgt₀ y
      have h_tgt_x : σ_tgt₁ x = some v := by show (if x = x then _ else _) = _; simp
      have h_tgt_other : ∀ y, x ≠ y → σ_tgt₁ y = σ_tgt₀ y := by
        intro y hxy; show (if y = x then _ else _) = _; rw [if_neg (fun h => hxy h.symm)]
      refine ⟨σ_tgt₁, EvalCmd.eval_init h_eval_tgt (InitState.init h_tgt_x_none h_tgt_x h_tgt_other) hwfvar hwfcongr, ?_⟩
      intro y h_y_nongen
      by_cases hyx : y = x
      · subst hyx; rw [h_xv, h_tgt_x]
      · rw [h_other y (fun h => hyx h.symm), h_tgt_other y (fun h => hyx h.symm)]
        exact h_off y h_y_nongen
  | eval_init_unconstrained hinit hwfvar =>
    rename_i ty md x v
    have h_x_nongen : ∀ s : String, x = HasIdent.ident (P := P) s →
        ¬ Q s := by
      intro s heq; apply h_no_writes x (List.mem_append_left _ ?_) s heq
      with_unfolding_all exact List.mem_singleton.mpr rfl
    cases hinit with
    | init h_xn h_xv h_other =>
      have h_tgt_x_none : σ_tgt₀ x = none := by rw [h_off x h_x_nongen]; exact h_xn
      let σ_tgt₁ : SemanticStore P := fun y => if y = x then some v else σ_tgt₀ y
      have h_tgt_x : σ_tgt₁ x = some v := by show (if x = x then _ else _) = _; simp
      have h_tgt_other : ∀ y, x ≠ y → σ_tgt₁ y = σ_tgt₀ y := by
        intro y hxy; show (if y = x then _ else _) = _; rw [if_neg (fun h => hxy h.symm)]
      refine ⟨σ_tgt₁, EvalCmd.eval_init_unconstrained (InitState.init h_tgt_x_none h_tgt_x h_tgt_other) hwfvar, ?_⟩
      intro y h_y_nongen
      by_cases hyx : y = x
      · subst hyx; rw [h_xv, h_tgt_x]
      · rw [h_other y (fun h => hyx h.symm), h_tgt_other y (fun h => hyx h.symm)]
        exact h_off y h_y_nongen
  | eval_set heval hupd hwfvar hwfcongr =>
    rename_i md x v e
    have h_x_nongen : ∀ s : String, x = HasIdent.ident (P := P) s →
        ¬ Q s := by
      intro s heq; apply h_no_writes x (List.mem_append_right _ ?_) s heq
      with_unfolding_all exact List.mem_singleton.mpr rfl
    have h_def_e : isDefined σ_src₀ (HasVarsPure.getVars e) := h_wf_def e v σ_src₀ heval
    have h_pointwise : ∀ y ∈ HasVarsPure.getVars e, σ_src₀ y = σ_tgt₀ y :=
      agreeOffGen_pointwise_on_expr_vars σ_src₀ σ_tgt₀ e h_off h_src_fresh h_def_e
    have h_eval_tgt : δ σ_tgt₀ e = .some v := by
      rw [← heval]; exact (h_congr e σ_src₀ σ_tgt₀ h_pointwise).symm
    cases hupd with
    | update h_xv' h_xv h_other =>
      rename_i v'
      have h_tgt_x_old : σ_tgt₀ x = some v' := by rw [h_off x h_x_nongen]; exact h_xv'
      let σ_tgt₁ : SemanticStore P := fun y => if y = x then some v else σ_tgt₀ y
      have h_tgt_x : σ_tgt₁ x = some v := by show (if x = x then _ else _) = _; simp
      have h_tgt_other : ∀ y, x ≠ y → σ_tgt₁ y = σ_tgt₀ y := by
        intro y hxy; show (if y = x then _ else _) = _; rw [if_neg (fun h => hxy h.symm)]
      refine ⟨σ_tgt₁, EvalCmd.eval_set h_eval_tgt (UpdateState.update h_tgt_x_old h_tgt_x h_tgt_other) hwfvar hwfcongr, ?_⟩
      intro y h_y_nongen
      by_cases hyx : y = x
      · subst hyx; rw [h_xv, h_tgt_x]
      · rw [h_other y (fun h => hyx h.symm), h_tgt_other y (fun h => hyx h.symm)]
        exact h_off y h_y_nongen
  | eval_set_nondet hupd hwfvar =>
    rename_i md x v
    have h_x_nongen : ∀ s : String, x = HasIdent.ident (P := P) s →
        ¬ Q s := by
      intro s heq; apply h_no_writes x (List.mem_append_right _ ?_) s heq
      with_unfolding_all exact List.mem_singleton.mpr rfl
    cases hupd with
    | update h_xv' h_xv h_other =>
      rename_i v'
      have h_tgt_x_old : σ_tgt₀ x = some v' := by rw [h_off x h_x_nongen]; exact h_xv'
      let σ_tgt₁ : SemanticStore P := fun y => if y = x then some v else σ_tgt₀ y
      have h_tgt_x : σ_tgt₁ x = some v := by show (if x = x then _ else _) = _; simp
      have h_tgt_other : ∀ y, x ≠ y → σ_tgt₁ y = σ_tgt₀ y := by
        intro y hxy; show (if y = x then _ else _) = _; rw [if_neg (fun h => hxy h.symm)]
      refine ⟨σ_tgt₁, EvalCmd.eval_set_nondet (UpdateState.update h_tgt_x_old h_tgt_x h_tgt_other) hwfvar, ?_⟩
      intro y h_y_nongen
      by_cases hyx : y = x
      · subst hyx; rw [h_xv, h_tgt_x]
      · rw [h_other y (fun h => hyx h.symm), h_tgt_other y (fun h => hyx h.symm)]
        exact h_off y h_y_nongen
  | eval_assert_pass hcond hwfb hwfcongr =>
    rename_i l md e
    have h_def_e : isDefined σ_src₀ (HasVarsPure.getVars e) := h_wf_def e HasBool.tt σ_src₀ hcond
    have h_pointwise : ∀ y ∈ HasVarsPure.getVars e, σ_src₀ y = σ_tgt₀ y :=
      agreeOffGen_pointwise_on_expr_vars σ_src₀ σ_tgt₀ e h_off h_src_fresh h_def_e
    have h_eval_tgt : δ σ_tgt₀ e = .some HasBool.tt := by
      rw [← hcond]; exact (h_congr e σ_src₀ σ_tgt₀ h_pointwise).symm
    exact ⟨σ_tgt₀, EvalCmd.eval_assert_pass h_eval_tgt hwfb hwfcongr, h_off⟩
  | eval_assert_fail hcond hwfb hwfcongr =>
    rename_i l md e
    have h_def_e : isDefined σ_src₀ (HasVarsPure.getVars e) := h_wf_def e HasBool.ff σ_src₀ hcond
    have h_pointwise : ∀ y ∈ HasVarsPure.getVars e, σ_src₀ y = σ_tgt₀ y :=
      agreeOffGen_pointwise_on_expr_vars σ_src₀ σ_tgt₀ e h_off h_src_fresh h_def_e
    have h_eval_tgt : δ σ_tgt₀ e = .some HasBool.ff := by
      rw [← hcond]; exact (h_congr e σ_src₀ σ_tgt₀ h_pointwise).symm
    exact ⟨σ_tgt₀, EvalCmd.eval_assert_fail h_eval_tgt hwfb hwfcongr, h_off⟩
  | eval_assume hcond hwfb hwfcongr =>
    rename_i l md e
    have h_def_e : isDefined σ_src₀ (HasVarsPure.getVars e) := h_wf_def e HasBool.tt σ_src₀ hcond
    have h_pointwise : ∀ y ∈ HasVarsPure.getVars e, σ_src₀ y = σ_tgt₀ y :=
      agreeOffGen_pointwise_on_expr_vars σ_src₀ σ_tgt₀ e h_off h_src_fresh h_def_e
    have h_eval_tgt : δ σ_tgt₀ e = .some HasBool.tt := by
      rw [← hcond]; exact (h_congr e σ_src₀ σ_tgt₀ h_pointwise).symm
    exact ⟨σ_tgt₀, EvalCmd.eval_assume h_eval_tgt hwfb hwfcongr, h_off⟩
  | eval_cover hwfb =>
    exact ⟨σ_tgt₀, EvalCmd.eval_cover hwfb, h_off⟩

/-- Trace-level pass-through `.cmd` replay under `AgreeOffGen`: a terminating
source `.cmd c` execution is matched by a terminating target `.cmd c` execution
from any off-gen-agreeing store (matching evaluator and failure flag), with the
post-stores agreeing off-gen, the failure flags equal, the evaluators equal, the
source post-store still free of gen-shaped slots, and the target post-store still
`GenFreshStore` (the replayed `c` writes no gen-shaped variable). -/
theorem cmd_replay_agreement_offgen {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasIdent P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasIdent P]
    {Q : String → Prop}
    (extendEval : ExtendEval P)
    (c : Cmd P) (ρ_src ρ_src' ρ_tgt : Env P) (σ : StringGenState)
    (h_eval_eq : ρ_tgt.eval = ρ_src.eval)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_off : AgreeOffGen Q ρ_src.store ρ_tgt.store)
    (h_wf_def : WellFormedSemanticEvalDef ρ_src.eval)
    (h_congr : WellFormedSemanticEvalExprCongr ρ_src.eval)
    (h_src_fresh : ∀ s, Q s →
      ρ_src.store (HasIdent.ident (P := P) s) = none)
    (h_tgt_fresh : GenFreshStore Q σ ρ_tgt.store)
    (h_no_writes : NoGenSuffix (P := P) Q (Cmd.definedVars c ++ Cmd.modifiedVars c))
    (h_term : StepStmtStar P (EvalCmd P) extendEval
      (.stmt (.cmd c) ρ_src) (.terminal ρ_src')) :
    (∀ s, Q s →
        ρ_src'.store (HasIdent.ident (P := P) s) = none)
      ∧ ∃ ρ_tgt', StepStmtStar P (EvalCmd P) extendEval
          (.stmt (.cmd c) ρ_tgt) (.terminal ρ_tgt')
        ∧ AgreeOffGen Q ρ_src'.store ρ_tgt'.store
        ∧ ρ_tgt'.hasFailure = ρ_src'.hasFailure
        ∧ ρ_tgt'.eval = ρ_src'.eval
        ∧ GenFreshStore Q σ ρ_tgt'.store := by
  obtain ⟨σ', haf, h_cmd, h_eq⟩ := cmd_step_inv (extendEval := extendEval) c ρ_src ρ_src' h_term
  obtain ⟨σ_tgt', h_eval_tgt, h_off'⟩ :=
    cmd_replay_offgen ρ_src.eval ρ_src.store ρ_tgt.store c σ' haf
      h_off h_cmd h_wf_def h_congr h_src_fresh h_no_writes
  have h_eval_tgt' : EvalCmd P ρ_tgt.eval ρ_tgt.store c σ_tgt' haf := h_eval_eq ▸ h_eval_tgt
  -- Source post-store still has no gen-shaped slot.
  have h_src'_fresh : ∀ s, Q s →
      ρ_src'.store (HasIdent.ident (P := P) s) = none := by
    subst h_eq
    exact evalCmd_preserves_src_fresh h_cmd h_src_fresh h_no_writes
  refine ⟨h_src'_fresh, { ρ_tgt with store := σ_tgt', hasFailure := ρ_tgt.hasFailure || haf },
    .step _ _ _ (StepStmt.step_cmd h_eval_tgt') (.refl _), ?_, ?_, ?_, ?_⟩
  · subst h_eq; exact h_off'
  · subst h_eq; simp [h_fail_eq]
  · subst h_eq; exact h_eval_eq
  · -- GenFreshStore preserved on the target: replayed c writes no gen-shaped var.
    intro s h_suf h_nin
    have h_none : ρ_tgt.store (HasIdent.ident (P := P) s) = none := h_tgt_fresh s h_suf h_nin
    refine evalCmd_preserves_none (P := P) (h_eval_eq ▸ h_eval_tgt) h_none ?_ ?_
    · intro h_mem; exact (h_no_writes _ (List.mem_append_left _ h_mem) s rfl) h_suf
    · intro h_mem; exact (h_no_writes _ (List.mem_append_right _ h_mem) s rfl) h_suf

end CmdReplayOffGen

/-- A source store with no gen-shaped slot defined that `AgreeOffGen`s a target
store also `StoreAgreement`s it: every source-*defined* variable is non-gen
(else its slot would be `none`, contradicting `isDefined`), so the bidirectional
off-gen equation specializes to the one-directional agreement. -/
theorem StoreAgreement.of_agreeOffGen {P : PureExpr} [HasIdent P] [LawfulHasIdent P]
    {Q : String → Prop}
    {σ_src σ_tgt : SemanticStore P}
    (h_off : AgreeOffGen Q σ_src σ_tgt)
    (h_src_fresh : ∀ s, Q s →
      σ_src (HasIdent.ident (P := P) s) = none) :
    StoreAgreement σ_src σ_tgt := by
  intro x h_def
  have h_x_def : (σ_src x).isSome = true := h_def x (List.mem_singleton.mpr rfl)
  have h_nongen : ∀ s : String, x = HasIdent.ident (P := P) s →
      ¬ Q s := by
    intro s h_eq h_suf
    rw [h_eq, h_src_fresh s h_suf] at h_x_def
    exact absurd h_x_def (by simp)
  exact (h_off x h_nongen).symm

/-- Deterministic-loop forward simulation, by structural induction on a `Nat`
fuel bounding the *Type-valued* length of the source run.  The source loop
`.loop (.det e) m [] body md` is simulated by the target loop
`.loop (.det e) m [] body' md`, where `body'` is the rewritten body and the
per-iteration body simulation is supplied by `h_body_sim`.  Threading `body'`
and `h_body_sim` as parameters keeps this lemma outside the mutual block: the
`.loop (.det e)` arm instantiates `body' := (Block.nondetElimM body σ).1`,
`h_body_sim := nondetElim_simulation_gen` (the body output is fixed across
iterations).

The fuel is threaded over `hstarT.len`, the genuine Type-valued length of the
source run, so each ENTER iteration applies the IH to the loop tail at a
strictly smaller fuel (`omega` on the `seqT`/`blockT`/`stmtsT` length bounds).
The invariant list is empty (`h_lhni` provides `is = []`), so the `step_loop_*`
side-conditions on invariants are vacuous (`empty_inv_no_failure`). -/
private theorem nondetElim_loop_det_sim_iteration {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasBool P] [LawfulHasIdent P]
    [LawfulHasIntOrder P] [LawfulHasNot P]
    {Q : String → Prop}
    (extendEval : ExtendEval P)
    (e : P.Expr) (m : Option P.Expr)
    (body body' : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ : StringGenState)
    -- Per-iteration body simulation: a run of `body` reaching an outcome
    -- (`.terminal` or an `.exiting` propagated past the loop) from a
    -- source store / target store pair (agreeing off the gen names, with the
    -- usual freshness invariants) is simulated by a run of `body'`,
    -- re-establishing all five store/eval/failure/freshness conjuncts.
    -- Mirrors `nondetElim_simulation_gen` specialized to `body`/`body'`/`σ`.
    (h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
      ρb_tgt.eval = ρb_src.eval →
      ρb_tgt.hasFailure = ρb_src.hasFailure →
      AgreeOffGen Q ρb_src.store ρb_tgt.store →
      WellFormedSemanticEvalBool ρb_src.eval →
      WellFormedSemanticEvalVal ρb_src.eval →
      WellFormedSemanticEvalDef ρb_src.eval →
      WellFormedSemanticEvalExprCongr ρb_src.eval →
      WellFormedSemanticEvalVar ρb_src.eval →
      StringGenState.WF σ →
      (∀ t, Q t →
        ρb_src.store (HasIdent.ident (P := P) t) = none) →
      GenFreshStore Q σ ρb_tgt.store →
      StepStmtStar P (EvalCmd P) extendEval (.stmts body ρb_src) (outcomeConfig oc_b ρb') →
      (∀ t, Q t →
          ρb'.store (HasIdent.ident (P := P) t) = none)
        ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P) extendEval
            (.stmts body' ρb_tgt) (outcomeConfig oc_b ρb_out)
          ∧ AgreeOffGen Q ρb'.store ρb_out.store
          ∧ ρb_out.hasFailure = ρb'.hasFailure
          ∧ ρb_out.eval = ρb'.eval
          ∧ GenFreshStore Q σ_out ρb_out.store)
    (_σ_out : StringGenState)
    (h_nofd_body : Block.noFuncDecl body = true)
    (oc : Option String)
    (ρ_src ρ' ρ_tgt : Env P) (n : Nat)
    (h_eval_eq : ρ_tgt.eval = ρ_src.eval)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree : AgreeOffGen Q ρ_src.store ρ_tgt.store)
    (hwfb : WellFormedSemanticEvalBool ρ_src.eval)
    (hwfv : WellFormedSemanticEvalVal ρ_src.eval)
    (hwf_def : WellFormedSemanticEvalDef ρ_src.eval)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ_src.eval)
    (hwf_var : WellFormedSemanticEvalVar ρ_src.eval)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : GenFreshStore Q σ ρ_tgt.store)
    (hstarT : ReflTransT (StepStmt P (EvalCmd P) extendEval)
      (.stmt (.loop (.det e) m ([] : List (String × P.Expr)) body md) ρ_src) (outcomeConfig oc ρ'))
    (hlen : hstarT.len ≤ n) :
    (∀ t, Q t →
        ρ'.store (HasIdent.ident (P := P) t) = none)
      ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P) extendEval
          (.stmt (.loop (.det e) m ([] : List (String × P.Expr)) body' md) ρ_tgt)
          (outcomeConfig oc ρ_out)
        ∧ AgreeOffGen Q ρ'.store ρ_out.store
        ∧ ρ_out.hasFailure = ρ'.hasFailure
        ∧ ρ_out.eval = ρ'.eval
        ∧ GenFreshStore Q σ ρ_out.store := by
  induction n generalizing oc ρ_src ρ_tgt ρ' with
  | zero =>
    -- A run of length 0 has no first loop step; both inversion branches give a
    -- residual of strictly smaller length, contradicting `hlen : len ≤ 0`.
    rcases loop_det_step_first_inv (extendEval := extendEval) hstarT with
      ⟨_, _, _, hl⟩ | ⟨_, _, _, hl⟩
    · exact absurd (Nat.lt_of_lt_of_le hl hlen) (Nat.not_lt_zero _)
    · exact absurd (Nat.lt_of_lt_of_le hl hlen) (Nat.not_lt_zero _)
  | succ n ih =>
    rcases loop_det_step_first_inv (extendEval := extendEval) hstarT with
      ⟨h_cond, hwfb_s, hrest, hl⟩ | ⟨h_cond, hwfb_s, hrest, hl⟩
    · -- EXIT: guard reads `ff`; loop terminates.  The loop exit reaches
      -- `.terminal`, so the outcome must be `none` (a `.terminal →*T .exiting`
      -- run is impossible).
      have hlen : hstarT.len ≤ n + 1 := hlen
      cases oc with
      | none =>
        simp only [outcomeConfig] at hrest ⊢
        -- The remaining run `.terminal (ρ_src + false) →*T .terminal ρ'` forces ρ' = ρ_src.
        have hρ' : ρ' = ({ ρ_src with hasFailure := ρ_src.hasFailure || false } : Env P) := by
          match hrest with
          | .refl _ => rfl
          | .step _ _ _ h _ => exact nomatch h
        have hρ'_eq : ρ' = ρ_src := by rw [hρ', Bool.or_false]
        -- Target: guard reads ff too (AgreeOffGen Q on guard's source-defined vars).
        have h_def_e : isDefined ρ_src.store (HasVarsPure.getVars e) :=
          hwf_def e HasBool.ff ρ_src.store h_cond
        have h_pw : ∀ x ∈ HasVarsPure.getVars e, ρ_src.store x = ρ_tgt.store x :=
          agreeOffGen_pointwise_on_expr_vars ρ_src.store ρ_tgt.store e h_agree h_src_fresh h_def_e
        have h_cond_t : ρ_tgt.eval ρ_tgt.store e = some HasBool.ff := by
          rw [h_eval_eq, ← h_cond]; exact (hwf_congr e ρ_src.store ρ_tgt.store h_pw).symm
        subst hρ'_eq
        refine ⟨h_src_fresh, ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P), ?_, ?_, ?_, ?_, ?_⟩
        · refine .step _ _ _ (StepStmt.step_loop_exit (hasInvFailure := false)
            h_cond_t (by simp) (by simp) (h_eval_eq ▸ hwfb)) (.refl _)
        · -- AgreeOffGen: only hasFailure changed on both sides.
          simpa using h_agree
        · simp [h_fail_eq]
        · simpa using h_eval_eq
        · simpa using h_tgt_fresh
      | some lbl =>
        -- `.terminal (ρ_src + false) →*T .exiting lbl ρ'` is impossible.
        exfalso
        simp only [outcomeConfig] at hrest
        match hrest with
        | .step _ _ _ h _ => exact nomatch h
    · -- ENTER: guard reads `tt`; run one body iteration then recurse (terminal
      -- outcome) or propagate the body's exit (exiting outcome).
      have hlen : hstarT.len ≤ n + 1 := hlen
      -- ρ_src' is ρ_src with the (no-op) failure update from the empty invariants.
      let ρ_src' : Env P := { ρ_src with hasFailure := ρ_src.hasFailure || false }
      have hρ_src'_eq : ρ_src' = ρ_src := by simp [ρ_src', Bool.or_false]
      -- Guard reads tt in the target (used by both outcome subcases).
      have h_def_e : isDefined ρ_src.store (HasVarsPure.getVars e) :=
        hwf_def e HasBool.tt ρ_src.store h_cond
      have h_pw : ∀ x ∈ HasVarsPure.getVars e, ρ_src.store x = ρ_tgt.store x :=
        agreeOffGen_pointwise_on_expr_vars ρ_src.store ρ_tgt.store e h_agree h_src_fresh h_def_e
      have h_cond_t : ρ_tgt.eval ρ_tgt.store e = some HasBool.tt := by
        rw [h_eval_eq, ← h_cond]; exact (hwf_congr e ρ_src.store ρ_tgt.store h_pw).symm
      -- A reusable body-block-to-terminal transport for the target side.
      have h_block_tgt_to : ∀ (ρb_tgt : Env P),
          StepStmtStar P (EvalCmd P) extendEval
            (.stmts body' ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P))
            (.terminal ρb_tgt) →
          StepStmtStar P (EvalCmd P) extendEval
            (.block .none ρ_tgt.store (.stmts body'
              ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P)))
            (.terminal ({ ρb_tgt with store := projectStore ρ_tgt.store ρb_tgt.store } : Env P)) := by
        intro ρb_tgt h_run
        refine ReflTrans_Transitive _ _ _ _
          (block_inner_star P (EvalCmd P) extendEval _ _ .none ρ_tgt.store h_run) ?_
        exact .step _ _ _ StepStmt.step_block_done (.refl _)
      cases oc with
      | none =>
        simp only [outcomeConfig] at hrest ⊢
        -- Re-state `hl` against the now `.terminal`-typed `hrest` so the residual
        -- length appears as a single atom shared with the `seqT` split below.
        have hl : hrest.len < hstarT.len := hl
        -- Split the seq: body-block reaches ρ_block, then [loop] reaches ρ'.
        have ⟨ρ_block, h_block_term, h_loop_stmts, hlen_seq⟩ :=
          seqT_reaches_terminal (extendEval := extendEval) hrest
        -- Unwrap the anonymous body block.
        have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
          blockT_none_reaches_terminal (extendEval := extendEval) h_block_term
        -- Decompose [loop] ρ_block: head loop reaches ρ_x, then [] reaches ρ'.
        have ⟨ρ_x, h_loop_T_T, h_nil, hlen_cons⟩ :=
          stmtsT_cons_terminal (extendEval := extendEval) h_loop_stmts
        have hρ_x_eq : ρ_x = ρ' := by
          match h_nil with
          | .step _ _ _ .step_stmts_nil hr2 =>
            match hr2 with
            | .refl _ => rfl
            | .step _ _ _ h _ => exact nomatch h
        subst hρ_x_eq
        -- The body ran from ρ_src' (= ρ_src) to ρ_inner.
        have h_body_run : StepStmtStar P (EvalCmd P) extendEval
            (.stmts body ρ_src) (outcomeConfig none ρ_inner) :=
          hρ_src'_eq ▸ reflTransT_to_prop h_inner_term
        -- Simulate the body once via the provider (terminal outcome).
        obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner,
            h_eval_inner, h_fresh_inner⟩ :=
          h_body_sim none ρ_src ρ_inner ρ_tgt h_eval_eq h_fail_eq h_agree hwfb hwfv hwf_def hwf_congr
            hwf_var h_wf_gen h_src_fresh h_tgt_fresh h_body_run
        -- Eval is preserved across the (funcDecl-free) body.
        have h_eval_inner_src : ρ_inner.eval = ρ_src.eval :=
          block_noFuncDecl_preserves_eval P (EvalCmd P) extendEval body ρ_src ρ_inner h_nofd_body
            (by simpa only [outcomeConfig] using h_body_run)
        -- The next iteration's source env is the block-projected `ρ_block`.
        have heq_ρ_block_full :
            ρ_block = ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P) := by
          have hstore : ρ_src'.store = ρ_src.store := by rw [hρ_src'_eq]
          rw [heq_ρ_block, hstore]
        subst heq_ρ_block_full
        let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store }
        let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store }
        -- WF-eval facts at ρ_src_next (eval = ρ_inner.eval = ρ_src.eval).
        have h_eval_next : ρ_src_next.eval = ρ_src.eval := h_eval_inner_src
        have hwfb_next : WellFormedSemanticEvalBool ρ_src_next.eval := by rw [h_eval_next]; exact hwfb
        have hwfv_next : WellFormedSemanticEvalVal ρ_src_next.eval := by rw [h_eval_next]; exact hwfv
        have hwf_def_next : WellFormedSemanticEvalDef ρ_src_next.eval := by rw [h_eval_next]; exact hwf_def
        have hwf_congr_next : WellFormedSemanticEvalExprCongr ρ_src_next.eval := by rw [h_eval_next]; exact hwf_congr
        have hwf_var_next : WellFormedSemanticEvalVar ρ_src_next.eval := by rw [h_eval_next]; exact hwf_var
        -- eval/fail agreement between the two projected stores.
        have h_eval_eq_next : ρ_tgt_next.eval = ρ_src_next.eval := by
          show ρ_inner_tgt.eval = ρ_inner.eval; exact h_eval_inner
        have h_fail_eq_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
          show ρ_inner_tgt.hasFailure = ρ_inner.hasFailure; exact h_fail_inner
        -- AgreeOffGen Q survives projecting both stores through their agreeing parents.
        have h_agree_next : AgreeOffGen Q ρ_src_next.store ρ_tgt_next.store := by
          intro x h_nongen
          show projectStore ρ_tgt.store ρ_inner_tgt.store x
            = projectStore ρ_src.store ρ_inner.store x
          show (if (ρ_tgt.store x).isSome then ρ_inner_tgt.store x else none)
            = (if (ρ_src.store x).isSome then ρ_inner.store x else none)
          have h_par : ρ_tgt.store x = ρ_src.store x := h_agree x h_nongen
          have h_inn : ρ_inner_tgt.store x = ρ_inner.store x := h_off_inner x h_nongen
          rw [h_par, h_inn]
        -- Source freshness at the projected store.
        have h_src_fresh_next : ∀ t, Q t →
            ρ_src_next.store (HasIdent.ident (P := P) t) = none := by
          intro t h_suf
          show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
          show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
              then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
          by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
          · rw [if_pos hp]; exact h_inner_fresh t h_suf
          · rw [if_neg hp]
        -- Target freshness at the projected store: derived from the *parent*
        -- `h_tgt_fresh` (the gen slot is already `none` in the parent, so the
        -- projection wipes it regardless of the body's post-store).
        have h_tgt_fresh_next : GenFreshStore Q σ ρ_tgt_next.store := by
          intro s h_suf h_notin
          show projectStore ρ_tgt.store ρ_inner_tgt.store (HasIdent.ident (P := P) s) = none
          show (if (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
              then ρ_inner_tgt.store (HasIdent.ident (P := P) s) else none) = none
          rw [h_tgt_fresh s h_suf h_notin]; rfl
        -- Recurse on the loop tail at strictly smaller fuel.  (`subst hρ_x_eq`
        -- eliminated the conclusion's terminal env in favour of `ρ_x`;
        -- `h_loop_T_T` already targets `ρ_x` from the substituted `ρ_src_next`.)
        have hlen_tail : h_loop_T_T.len ≤ n := by omega
        obtain ⟨h_fresh', ρ_out, h_loop_tgt, h_off', h_fail', h_eval', h_fresh_out⟩ :=
          ih (oc := none) (ρ_src := ρ_src_next) (ρ' := ρ_x) (ρ_tgt := ρ_tgt_next)
            h_eval_eq_next h_fail_eq_next h_agree_next
            hwfb_next hwfv_next hwf_def_next hwf_congr_next hwf_var_next
            h_src_fresh_next h_tgt_fresh_next h_loop_T_T hlen_tail
        simp only [outcomeConfig] at h_loop_tgt
        refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', h_fresh_out⟩
        -- Build the target loop run: enter (guard tt, body-block) then recurse.
        refine .step _ _ _ (StepStmt.step_loop_enter (hasInvFailure := false)
          h_cond_t (by simp) (by simp) (h_eval_eq ▸ hwfb)) ?_
        have h_body_tgt' : StepStmtStar P (EvalCmd P) extendEval
            (.stmts body' ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P))
            (.terminal ρ_inner_tgt) := by
          have : ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P) = ρ_tgt := by
            simp [Bool.or_false]
          rw [this]; simpa only [outcomeConfig] using h_body_tgt
        -- After step_seq_done we reach `.stmts [loop] ρ_tgt_next`; loop tail runs
        -- to `.stmts []`, then `step_stmts_nil` to `.terminal ρ_out`.
        refine ReflTrans_Transitive _ _ _ _
          (ReflTrans_Transitive _ _ _ _
            (seq_inner_star P (EvalCmd P) extendEval _ _ _ (h_block_tgt_to ρ_inner_tgt h_body_tgt'))
            (.step _ _ _ StepStmt.step_seq_done (.refl _)))
          (ReflTrans_Transitive _ _ _ _
            (stmts_cons_step P (EvalCmd P) extendEval _ _ ρ_tgt_next ρ_out h_loop_tgt)
            (.step _ _ _ StepStmt.step_stmts_nil (.refl _)))
      | some lbl =>
        simp only [outcomeConfig] at hrest ⊢
        -- Re-state `hl` against the now `.exiting`-typed `hrest` so the residual
        -- length appears as a single atom shared with the `seqT` split below.
        have hl : hrest.len < hstarT.len := hl
        -- The loop exits with `lbl`.  Split the seq: either the body-block
        -- exits (skipping the loop tail), or the body terminates and the loop
        -- tail exits.
        rcases seqT_reaches_exiting (extendEval := extendEval) hrest with
          ⟨h_block_exit, hlen_be⟩ | ⟨ρ_block, h_block_term, h_loop_exit, hlen_te⟩
        · -- Body-block exits with `lbl`: the body exits, propagated past the loop.
          have ⟨ρ_inner, h_inner_exit, heq_ρ', hlen_inner⟩ :=
            blockT_none_reaches_exiting (extendEval := extendEval) h_block_exit
          -- The body ran from ρ_src' (= ρ_src) exiting `lbl` to ρ_inner.
          have h_body_run : StepStmtStar P (EvalCmd P) extendEval
              (.stmts body ρ_src) (outcomeConfig (some lbl) ρ_inner) :=
            hρ_src'_eq ▸ reflTransT_to_prop h_inner_exit
          obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner,
              h_eval_inner, h_fresh_inner⟩ :=
            h_body_sim (some lbl) ρ_src ρ_inner ρ_tgt h_eval_eq h_fail_eq h_agree hwfb hwfv hwf_def hwf_congr
              hwf_var h_wf_gen h_src_fresh h_tgt_fresh h_body_run
          subst heq_ρ'
          refine ⟨?_, ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store } : Env P),
            ?_, ?_, ?_, ?_, ?_⟩
          · -- Source freshness at the projected store.
            intro t h_suf
            show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
            show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
                then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
            by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
            · rw [if_pos hp]; exact h_inner_fresh t h_suf
            · rw [if_neg hp]
          · -- Target loop: enter (guard tt), body-block exits `lbl`, seq exits.
            refine .step _ _ _ (StepStmt.step_loop_enter (hasInvFailure := false)
              h_cond_t (by simp) (by simp) (h_eval_eq ▸ hwfb)) ?_
            have h_body_tgt' : StepStmtStar P (EvalCmd P) extendEval
                (.stmts body' ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P))
                (.exiting lbl ρ_inner_tgt) := by
              have : ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P) = ρ_tgt := by
                simp [Bool.or_false]
              rw [this]; simpa only [outcomeConfig] using h_body_tgt
            -- Lift body' exit through the block (block_inner_star), then
            -- step_block_exit_mismatch (`.none ≠ .some lbl`) propagates, then
            -- step_seq_exit skips the loop tail.
            have h_block_tgt_exit : StepStmtStar P (EvalCmd P) extendEval
                (.block .none ρ_tgt.store (.stmts body'
                  ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P)))
                (.exiting lbl ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store } : Env P)) := by
              refine ReflTrans_Transitive _ _ _ _
                (block_inner_star P (EvalCmd P) extendEval _ _ .none ρ_tgt.store h_body_tgt') ?_
              exact .step _ _ _ (StepStmt.step_block_exit_mismatch (by simp)) (.refl _)
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendEval _ _ _ h_block_tgt_exit) ?_
            exact .step _ _ _ StepStmt.step_seq_exit (.refl _)
          · -- AgreeOffGen Q at the projected stores.
            intro x h_nongen
            show projectStore ρ_tgt.store ρ_inner_tgt.store x
              = projectStore ρ_src.store ρ_inner.store x
            show (if (ρ_tgt.store x).isSome then ρ_inner_tgt.store x else none)
              = (if (ρ_src.store x).isSome then ρ_inner.store x else none)
            rw [h_agree x h_nongen, h_off_inner x h_nongen]
          · exact h_fail_inner
          · exact h_eval_inner
          · -- GenFreshStore Q at the projected store: from the parent `h_tgt_fresh`.
            intro s h_suf h_notin
            show projectStore ρ_tgt.store ρ_inner_tgt.store (HasIdent.ident (P := P) s) = none
            show (if (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
                then ρ_inner_tgt.store (HasIdent.ident (P := P) s) else none) = none
            rw [h_tgt_fresh s h_suf h_notin]; rfl
        · -- Body terminates, loop tail exits with `lbl`: recurse on the tail.
          have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
            blockT_none_reaches_terminal (extendEval := extendEval) h_block_term
          -- Decompose [loop] ρ_block exiting: the head loop exits `lbl`.
          have ⟨h_loop_T_exit, hlen_cons⟩ :=
            stmtsT_singleton_exiting (extendEval := extendEval) h_loop_exit
          have h_body_run : StepStmtStar P (EvalCmd P) extendEval
              (.stmts body ρ_src) (outcomeConfig none ρ_inner) :=
            hρ_src'_eq ▸ reflTransT_to_prop h_inner_term
          obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner,
              h_eval_inner, h_fresh_inner⟩ :=
            h_body_sim none ρ_src ρ_inner ρ_tgt h_eval_eq h_fail_eq h_agree hwfb hwfv hwf_def hwf_congr
              hwf_var h_wf_gen h_src_fresh h_tgt_fresh h_body_run
          have h_eval_inner_src : ρ_inner.eval = ρ_src.eval :=
            block_noFuncDecl_preserves_eval P (EvalCmd P) extendEval body ρ_src ρ_inner h_nofd_body
              (by simpa only [outcomeConfig] using h_body_run)
          have heq_ρ_block_full :
              ρ_block = ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P) := by
            have hstore : ρ_src'.store = ρ_src.store := by rw [hρ_src'_eq]
            rw [heq_ρ_block, hstore]
          subst heq_ρ_block_full
          let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store }
          let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store }
          have h_eval_next : ρ_src_next.eval = ρ_src.eval := h_eval_inner_src
          have hwfb_next : WellFormedSemanticEvalBool ρ_src_next.eval := by rw [h_eval_next]; exact hwfb
          have hwfv_next : WellFormedSemanticEvalVal ρ_src_next.eval := by rw [h_eval_next]; exact hwfv
          have hwf_def_next : WellFormedSemanticEvalDef ρ_src_next.eval := by rw [h_eval_next]; exact hwf_def
          have hwf_congr_next : WellFormedSemanticEvalExprCongr ρ_src_next.eval := by rw [h_eval_next]; exact hwf_congr
          have hwf_var_next : WellFormedSemanticEvalVar ρ_src_next.eval := by rw [h_eval_next]; exact hwf_var
          have h_eval_eq_next : ρ_tgt_next.eval = ρ_src_next.eval := by
            show ρ_inner_tgt.eval = ρ_inner.eval; exact h_eval_inner
          have h_fail_eq_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
            show ρ_inner_tgt.hasFailure = ρ_inner.hasFailure; exact h_fail_inner
          have h_agree_next : AgreeOffGen Q ρ_src_next.store ρ_tgt_next.store := by
            intro x h_nongen
            show projectStore ρ_tgt.store ρ_inner_tgt.store x
              = projectStore ρ_src.store ρ_inner.store x
            show (if (ρ_tgt.store x).isSome then ρ_inner_tgt.store x else none)
              = (if (ρ_src.store x).isSome then ρ_inner.store x else none)
            rw [h_agree x h_nongen, h_off_inner x h_nongen]
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
          have hlen_tail : h_loop_T_exit.len ≤ n := by omega
          obtain ⟨h_fresh', ρ_out, h_loop_tgt, h_off', h_fail', h_eval', h_fresh_out⟩ :=
            ih (oc := some lbl) (ρ_src := ρ_src_next) (ρ' := ρ') (ρ_tgt := ρ_tgt_next)
              h_eval_eq_next h_fail_eq_next h_agree_next
              hwfb_next hwfv_next hwf_def_next hwf_congr_next hwf_var_next
              h_src_fresh_next h_tgt_fresh_next h_loop_T_exit hlen_tail
          simp only [outcomeConfig] at h_loop_tgt
          refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', h_fresh_out⟩
          refine .step _ _ _ (StepStmt.step_loop_enter (hasInvFailure := false)
            h_cond_t (by simp) (by simp) (h_eval_eq ▸ hwfb)) ?_
          have h_body_tgt' : StepStmtStar P (EvalCmd P) extendEval
              (.stmts body' ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P))
              (.terminal ρ_inner_tgt) := by
            have : ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P) = ρ_tgt := by
              simp [Bool.or_false]
            rw [this]; simpa only [outcomeConfig] using h_body_tgt
          -- After step_seq_done we reach `.stmts [loop] ρ_tgt_next`; the loop
          -- tail exits with `lbl` (lift the `.stmt loop` exit into `.stmts
          -- [loop]` via step_stmts_cons / seq_inner_star / step_seq_exit).
          have h_loop_stmts_exit : StepStmtStar P (EvalCmd P) extendEval
              (.stmts [.loop (.det e) m ([] : List (String × P.Expr)) body' md] ρ_tgt_next)
              (.exiting lbl ρ_out) := by
            refine .step _ _ _ StepStmt.step_stmts_cons ?_
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendEval _ _ _ h_loop_tgt) ?_
            exact .step _ _ _ StepStmt.step_seq_exit (.refl _)
          refine ReflTrans_Transitive _ _ _ _
            (ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendEval _ _ _ (h_block_tgt_to ρ_inner_tgt h_body_tgt'))
              (.step _ _ _ StepStmt.step_seq_done (.refl _)))
            h_loop_stmts_exit


/-- Closes the EXIT case of the nondet-loop iteration: the source loop
terminates (so `oc = none` and `ρ' = ρ_src`), and the target deterministic loop
reads the guard `$g = ff` and exits via `step_loop_exit`.  Shared between the
fuel `zero` and `succ` cases. -/
private theorem loop_nondet_exit_close {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasBool P] [LawfulHasIdent P]
    [LawfulHasIntOrder P] [LawfulHasNot P]
    {Q : String → Prop}
    (extendEval : ExtendEval P)
    (ident : P.Ident) (m : Option P.Expr)
    (body' : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ : StringGenState)
    (oc : Option String)
    (ρ_src ρ' ρ_tgt : Env P)
    (h_eval_eq : ρ_tgt.eval = ρ_src.eval)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree : AgreeOffGen Q ρ_src.store ρ_tgt.store)
    (hwfb : WellFormedSemanticEvalBool ρ_src.eval)
    (hwf_var : WellFormedSemanticEvalVar ρ_src.eval)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : GenFreshStore Q σ ρ_tgt.store)
    (h_guard_def : ρ_tgt.store ident = some HasBool.ff)
    (hrest : ReflTransT (StepStmt P (EvalCmd P) extendEval)
      (.terminal ({ ρ_src with hasFailure := ρ_src.hasFailure || false } : Env P))
      (outcomeConfig oc ρ')) :
    (∀ t, Q t →
        ρ'.store (HasIdent.ident (P := P) t) = none)
      ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P) extendEval
          (.stmt (.loop (.det (HasFvar.mkFvar ident)) m ([] : List (String × P.Expr))
            (body' ++ [.cmd (HasHavoc.havoc ident md)]) md) ρ_tgt)
          (outcomeConfig oc ρ_out)
        ∧ AgreeOffGen Q ρ'.store ρ_out.store
        ∧ ρ_out.hasFailure = ρ'.hasFailure
        ∧ ρ_out.eval = ρ'.eval
        ∧ GenFreshStore Q σ ρ_out.store := by
  cases oc with
  | some lbl =>
    exfalso
    simp only [outcomeConfig] at hrest
    match hrest with
    | .step _ _ _ h _ => exact nomatch h
  | none =>
    simp only [outcomeConfig] at hrest ⊢
    have hρ' : ρ' = ({ ρ_src with hasFailure := ρ_src.hasFailure || false } : Env P) := by
      match hrest with
      | .refl _ => rfl
      | .step _ _ _ h _ => exact nomatch h
    have hρ'_eq : ρ' = ρ_src := by rw [hρ', Bool.or_false]
    have h_guard_ff : ρ_tgt.eval ρ_tgt.store (HasFvar.mkFvar ident) = some HasBool.ff := by
      have h := hwf_var (HasFvar.mkFvar (P := P) ident) ident ρ_tgt.store
        (LawfulHasFvar.getFvar_mkFvar ident)
      rw [h_eval_eq, h, h_guard_def]
    subst hρ'_eq
    refine ⟨h_src_fresh, ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P), ?_, ?_, ?_, ?_, ?_⟩
    · refine .step _ _ _ (StepStmt.step_loop_exit (hasInvFailure := false)
        h_guard_ff (by simp) (by simp) (h_eval_eq ▸ hwfb)) (.refl _)
    · simpa using h_agree
    · simp [h_fail_eq]
    · simpa using h_eval_eq
    · simpa using h_tgt_fresh

/-- Nondeterministic-loop forward simulation, by structural induction on a `Nat`
fuel bounding the *Type-valued* length of the source run.  The source loop
`.loop .nondet m [] body md` is simulated by the target *deterministic* loop
`.loop (.det $g) m [] (body' ++ [havoc $g]) md`, where `$g = mkFvar (ident g)`
(`g` gen-shaped, `g ∈ σ.stringGens`) is the generated guard, `body'` is the
rewritten body, and the per-iteration body simulation is supplied by
`h_body_sim`.

The guard `$g` lives in the *parent* (target) scope: it is `init`'d to a value
matching the source's first enter/exit choice *before* the loop (the caller),
then re-havoced (`set $g := *`) at each body tail to match the *next* choice
(spec §3.2/§3.3).  The relocated head-test reads/writes only the gen slot `$g`,
which `AgreeOffGen`/`GenFreshStore` quarantine from the source store, so the
relocation is invisible on the agreeing (off-gen) part.  Because `$g` is
parent-defined, it survives each block-scoped iteration's `projectStore`
(`stmts_preserves_isSome` over the body) and the body-tail havoc can fire.

The first iteration's matched guard is supplied as an explicit `entering : Bool`
plus the *already-inverted* source first step `h_src_first`, carrying a
`len ≤ n` fuel bound.  Each recursive step re-inverts the loop tail with
`loop_nondet_step_first_inv` and chooses the matching havoc value. -/
private theorem nondetElim_loop_nondet_sim_iteration {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasBool P] [LawfulHasIdent P]
    [LawfulHasIntOrder P] [LawfulHasNot P]
    {Q : String → Prop}
    (extendEval : ExtendEval P)
    (g : String) (m : Option P.Expr)
    (body body' : List (Stmt P (Cmd P))) (md : MetaData P)
    (σ σ_out : StringGenState)
    (h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
      ρb_tgt.eval = ρb_src.eval →
      ρb_tgt.hasFailure = ρb_src.hasFailure →
      AgreeOffGen Q ρb_src.store ρb_tgt.store →
      WellFormedSemanticEvalBool ρb_src.eval →
      WellFormedSemanticEvalVal ρb_src.eval →
      WellFormedSemanticEvalDef ρb_src.eval →
      WellFormedSemanticEvalExprCongr ρb_src.eval →
      WellFormedSemanticEvalVar ρb_src.eval →
      StringGenState.WF σ →
      (∀ t, Q t →
        ρb_src.store (HasIdent.ident (P := P) t) = none) →
      GenFreshStore Q σ ρb_tgt.store →
      StepStmtStar P (EvalCmd P) extendEval (.stmts body ρb_src) (outcomeConfig oc_b ρb') →
      (∀ t, Q t →
          ρb'.store (HasIdent.ident (P := P) t) = none)
        ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P) extendEval
            (.stmts body' ρb_tgt) (outcomeConfig oc_b ρb_out)
          ∧ AgreeOffGen Q ρb'.store ρb_out.store
          ∧ ρb_out.hasFailure = ρb'.hasFailure
          ∧ ρb_out.eval = ρb'.eval
          ∧ GenFreshStore Q σ_out ρb_out.store)
    (h_g_gen : Q g)
    (_h_g_in : g ∈ σ.stringGens)
    (h_nofd_body : Block.noFuncDecl body = true)
    (oc : Option String)
    (ρ_src ρ' ρ_tgt : Env P) (n : Nat)
    (h_eval_eq : ρ_tgt.eval = ρ_src.eval)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree : AgreeOffGen Q ρ_src.store ρ_tgt.store)
    (hwfb : WellFormedSemanticEvalBool ρ_src.eval)
    (hwfv : WellFormedSemanticEvalVal ρ_src.eval)
    (hwf_def : WellFormedSemanticEvalDef ρ_src.eval)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ_src.eval)
    (hwf_var : WellFormedSemanticEvalVar ρ_src.eval)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : GenFreshStore Q σ ρ_tgt.store)
    (entering : Bool)
    (h_guard_def : ρ_tgt.store (HasIdent.ident (P := P) g)
      = some (if entering then HasBool.tt else HasBool.ff))
    (h_src_first :
      (entering = false ∧ ∃ (hrest : ReflTransT (StepStmt P (EvalCmd P) extendEval)
          (.terminal ({ ρ_src with hasFailure := ρ_src.hasFailure || false } : Env P))
          (outcomeConfig oc ρ')), hrest.len ≤ n) ∨
      (entering = true ∧ ∃ (hrest : ReflTransT (StepStmt P (EvalCmd P) extendEval)
          (.seq (.block .none ρ_src.store (.stmts body
              ({ ρ_src with hasFailure := ρ_src.hasFailure || false } : Env P)))
            [.loop .nondet m ([] : List (String × P.Expr)) body md])
          (outcomeConfig oc ρ')), hrest.len ≤ n)) :
    (∀ t, Q t →
        ρ'.store (HasIdent.ident (P := P) t) = none)
      ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P) extendEval
          (.stmt (.loop (.det (HasFvar.mkFvar (HasIdent.ident (P := P) g))) m
            ([] : List (String × P.Expr))
            (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md) ρ_tgt)
          (outcomeConfig oc ρ_out)
        ∧ AgreeOffGen Q ρ'.store ρ_out.store
        ∧ ρ_out.hasFailure = ρ'.hasFailure
        ∧ ρ_out.eval = ρ'.eval
        ∧ GenFreshStore Q σ ρ_out.store := by
  induction n generalizing oc ρ_src ρ_tgt ρ' entering with
  | zero =>
    rcases h_src_first with ⟨h_ent, hrest, hl⟩ | ⟨h_ent, hrest, hl⟩
    · subst h_ent
      simp only [Bool.false_eq_true, if_false] at h_guard_def
      exact loop_nondet_exit_close extendEval (HasIdent.ident (P := P) g) m body' md σ
        oc ρ_src ρ' ρ_tgt h_eval_eq h_fail_eq h_agree hwfb hwf_var
        h_src_fresh h_tgt_fresh h_guard_def hrest
    · exfalso
      subst h_ent
      cases oc <;> simp only [outcomeConfig] at hrest <;>
        (match hrest with
         | .step _ _ _ _ _ => simp only [ReflTransT.len] at hl; omega)
  | succ n ih =>
    rcases h_src_first with ⟨h_ent, hrest, hl⟩ | ⟨h_ent, hrest, hl⟩
    · subst h_ent
      simp only [Bool.false_eq_true, if_false] at h_guard_def
      exact loop_nondet_exit_close extendEval (HasIdent.ident (P := P) g) m body' md σ
        oc ρ_src ρ' ρ_tgt h_eval_eq h_fail_eq h_agree hwfb hwf_var
        h_src_fresh h_tgt_fresh h_guard_def hrest
    · subst h_ent
      simp only [if_true] at h_guard_def
      -- Guard reads tt in target (via mkFvar / h_guard_def).
      have h_guard_tt : ρ_tgt.eval ρ_tgt.store (HasFvar.mkFvar (HasIdent.ident (P := P) g))
          = some HasBool.tt := by
        have h := hwf_var (HasFvar.mkFvar (P := P) (HasIdent.ident (P := P) g))
          (HasIdent.ident (P := P) g) ρ_tgt.store
          (LawfulHasFvar.getFvar_mkFvar (HasIdent.ident (P := P) g))
        rw [h_eval_eq, h, h_guard_def]
      have hwf_var_t : WellFormedSemanticEvalVar ρ_tgt.eval := h_eval_eq ▸ hwf_var
      have hρ_src'_eq : ({ ρ_src with hasFailure := ρ_src.hasFailure || false } : Env P) = ρ_src := by
        simp [Bool.or_false]
      cases oc with
      | none =>
        simp only [outcomeConfig] at hrest ⊢
        have hl : hrest.len ≤ n + 1 := hl
        have ⟨ρ_block, h_block_term, h_loop_stmts, hlen_seq⟩ :=
          seqT_reaches_terminal (extendEval := extendEval) hrest
        have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
          blockT_none_reaches_terminal (extendEval := extendEval) h_block_term
        have ⟨ρ_x, h_loop_T_T, h_nil, hlen_cons⟩ :=
          stmtsT_cons_terminal (extendEval := extendEval) h_loop_stmts
        have hρ_x_eq : ρ_x = ρ' := by
          match h_nil with
          | .step _ _ _ .step_stmts_nil hr2 =>
            match hr2 with
            | .refl _ => rfl
            | .step _ _ _ h _ => exact nomatch h
        subst hρ_x_eq
        have h_body_run : StepStmtStar P (EvalCmd P) extendEval
            (.stmts body ρ_src) (outcomeConfig none ρ_inner) :=
          hρ_src'_eq ▸ reflTransT_to_prop h_inner_term
        obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner,
            h_eval_inner, h_fresh_inner⟩ :=
          h_body_sim none ρ_src ρ_inner ρ_tgt h_eval_eq h_fail_eq h_agree hwfb hwfv hwf_def hwf_congr
            hwf_var h_wf_gen h_src_fresh h_tgt_fresh h_body_run
        have h_eval_inner_src : ρ_inner.eval = ρ_src.eval :=
          block_noFuncDecl_preserves_eval P (EvalCmd P) extendEval body ρ_src ρ_inner h_nofd_body
            (by simpa only [outcomeConfig] using h_body_run)
        have heq_ρ_block_full :
            ρ_block = ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P) := by
          rw [heq_ρ_block]
        subst heq_ρ_block_full
        -- $g stays defined in ρ_inner_tgt (it was defined in ρ_tgt = ρ_tgt+false).
        have h_g_some_tgt : (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome = true := by
          rw [h_guard_def]; rfl
        have h_body_tgt_term : StepStmtStar P (EvalCmd P) extendEval
            (.stmts body' ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P))
            (.terminal ρ_inner_tgt) := by
          have he : ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P) = ρ_tgt := by
            simp [Bool.or_false]
          rw [he]; simpa only [outcomeConfig] using h_body_tgt
        have h_g_some_inner : (ρ_inner_tgt.store (HasIdent.ident (P := P) g)).isSome = true := by
          have := stmts_preserves_isSome (extendEval := extendEval) h_body_tgt_term
            (y := HasIdent.ident (P := P) g)
          have he : (({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P).store
              (HasIdent.ident (P := P) g)).isSome = true := h_g_some_tgt
          exact this he
        obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp h_g_some_inner
        -- Invert the loop tail to learn the NEXT source decision.
        rcases loop_nondet_step_first_inv (extendEval := extendEval) (oc := none)
            h_loop_T_T with
          ⟨hrest_next, hlen_next⟩ | ⟨hrest_next, hlen_next⟩
        · -- NEXT = EXIT: re-havoc $g := ff.
          have hwf_var_inner : WellFormedSemanticEvalVar ρ_inner_tgt.eval := by
            rw [h_eval_inner, h_eval_inner_src]; exact hwf_var
          -- Build the per-iteration block run: body' to ρ_inner_tgt, then havoc $g := ff.
          have h_tail : StepStmtStar P (EvalCmd P) extendEval
              (.stmt (.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)) ρ_inner_tgt)
              (.terminal ({ ρ_inner_tgt with store := storeWith ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.ff } : Env P)) :=
            step_havoc_set_to (extendEval := extendEval) (HasIdent.ident (P := P) g) HasBool.ff md ρ_inner_tgt v' hv'
              hwf_var_inner
          have h_body_tail : StepStmtStar P (EvalCmd P) extendEval
              (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P))
              (.terminal ({ ρ_inner_tgt with store := storeWith ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.ff } : Env P)) :=
            ReflTrans_Transitive _ _ _ _
              (stmts_prefix_terminal_append P (EvalCmd P) extendEval _ _ _ ρ_inner_tgt h_body_tgt_term)
              (stmt_to_singleton_stmts (extendEval := extendEval) _ ρ_inner_tgt _ h_tail)
          let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store (storeWith ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) }
          let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store }
          -- $g slot in ρ_tgt_next.
          have h_guard_next : ρ_tgt_next.store (HasIdent.ident (P := P) g) = some HasBool.ff := by
            show (if (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome
                then storeWith ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.ff
                  (HasIdent.ident (P := P) g) else none) = some HasBool.ff
            rw [if_pos h_g_some_tgt]; simp [storeWith]
          -- WF facts and agreements at the projected envs.
          have h_eval_next : ρ_src_next.eval = ρ_src.eval := h_eval_inner_src
          have hwfb_next : WellFormedSemanticEvalBool ρ_src_next.eval := by rw [h_eval_next]; exact hwfb
          have hwfv_next : WellFormedSemanticEvalVal ρ_src_next.eval := by rw [h_eval_next]; exact hwfv
          have hwf_def_next : WellFormedSemanticEvalDef ρ_src_next.eval := by rw [h_eval_next]; exact hwf_def
          have hwf_congr_next : WellFormedSemanticEvalExprCongr ρ_src_next.eval := by rw [h_eval_next]; exact hwf_congr
          have hwf_var_next : WellFormedSemanticEvalVar ρ_src_next.eval := by rw [h_eval_next]; exact hwf_var
          have h_eval_eq_next : ρ_tgt_next.eval = ρ_src_next.eval := by
            show ρ_inner_tgt.eval = ρ_inner.eval; exact h_eval_inner
          have h_fail_eq_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
            show ρ_inner_tgt.hasFailure = ρ_inner.hasFailure; exact h_fail_inner
          have h_agree_next : AgreeOffGen Q ρ_src_next.store ρ_tgt_next.store := by
            intro x h_nongen
            show projectStore ρ_tgt.store
                (storeWith ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) x
              = projectStore ρ_src.store ρ_inner.store x
            have h_x_ne : x ≠ HasIdent.ident (P := P) g := by
              rintro rfl; exact (h_nongen g rfl) h_g_gen
            show (if (ρ_tgt.store x).isSome then
                (if x = HasIdent.ident (P := P) g then some HasBool.ff else ρ_inner_tgt.store x)
                else none)
              = (if (ρ_src.store x).isSome then ρ_inner.store x else none)
            rw [if_neg h_x_ne, h_agree x h_nongen, h_off_inner x h_nongen]
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
                then storeWith ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.ff
                  (HasIdent.ident (P := P) s) else none) = none
            rw [h_tgt_fresh s h_suf h_notin]; rfl
          -- Recurse with entering = false (exit) at smaller fuel.  `h_loop_T_T.len`
          -- shares its atom across the cons/seq bounds (no cast), so bound it
          -- first; the inversion's `< h_loop_T_T.len` then chains by defeq.
          have h_bound : h_loop_T_T.len ≤ n := by omega
          have hlen_tail : hrest_next.len ≤ n :=
            Nat.le_of_lt (Nat.lt_of_lt_of_le hlen_next h_bound)
          obtain ⟨h_fresh', ρ_out, h_loop_tgt, h_off', h_fail', h_eval', h_fresh_out⟩ :=
            ih (oc := none) (ρ_src := ρ_src_next) (ρ' := ρ_x) (ρ_tgt := ρ_tgt_next)
              h_eval_eq_next h_fail_eq_next h_agree_next
              hwfb_next hwfv_next hwf_def_next hwf_congr_next hwf_var_next
              h_src_fresh_next h_tgt_fresh_next false h_guard_next
              (.inl ⟨rfl, hrest_next, hlen_tail⟩)
          simp only [outcomeConfig] at h_loop_tgt
          refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', h_fresh_out⟩
          -- Assemble: enter (guard tt), block runs body'++[havoc], step_seq_done, recurse.
          refine .step _ _ _ (StepStmt.step_loop_enter (hasInvFailure := false)
            h_guard_tt (by simp) (by simp) (h_eval_eq ▸ hwfb)) ?_
          have h_block_run : StepStmtStar P (EvalCmd P) extendEval
              (.block .none ρ_tgt.store (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P)))
              (.terminal ρ_tgt_next) := by
            refine ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) extendEval _ _ .none ρ_tgt.store h_body_tail) ?_
            exact .step _ _ _ StepStmt.step_block_done (.refl _)
          refine ReflTrans_Transitive _ _ _ _
            (ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendEval _ _ _ h_block_run)
              (.step _ _ _ StepStmt.step_seq_done (.refl _)))
            (ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P (EvalCmd P) extendEval _ _ ρ_tgt_next ρ_out h_loop_tgt)
              (.step _ _ _ StepStmt.step_stmts_nil (.refl _)))
        · -- NEXT = ENTER: re-havoc $g := tt.
          have hwf_var_inner : WellFormedSemanticEvalVar ρ_inner_tgt.eval := by
            rw [h_eval_inner, h_eval_inner_src]; exact hwf_var
          have h_tail : StepStmtStar P (EvalCmd P) extendEval
              (.stmt (.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)) ρ_inner_tgt)
              (.terminal ({ ρ_inner_tgt with store := storeWith ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P)) :=
            step_havoc_set_to (extendEval := extendEval) (HasIdent.ident (P := P) g) HasBool.tt md ρ_inner_tgt v' hv'
              hwf_var_inner
          have h_body_tail : StepStmtStar P (EvalCmd P) extendEval
              (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P))
              (.terminal ({ ρ_inner_tgt with store := storeWith ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P)) :=
            ReflTrans_Transitive _ _ _ _
              (stmts_prefix_terminal_append P (EvalCmd P) extendEval _ _ _ ρ_inner_tgt h_body_tgt_term)
              (stmt_to_singleton_stmts (extendEval := extendEval) _ ρ_inner_tgt _ h_tail)
          let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store (storeWith ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) }
          let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store }
          have h_guard_next : ρ_tgt_next.store (HasIdent.ident (P := P) g) = some HasBool.tt := by
            show (if (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome
                then storeWith ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt
                  (HasIdent.ident (P := P) g) else none) = some HasBool.tt
            rw [if_pos h_g_some_tgt]; simp [storeWith]
          have h_eval_next : ρ_src_next.eval = ρ_src.eval := h_eval_inner_src
          have hwfb_next : WellFormedSemanticEvalBool ρ_src_next.eval := by rw [h_eval_next]; exact hwfb
          have hwfv_next : WellFormedSemanticEvalVal ρ_src_next.eval := by rw [h_eval_next]; exact hwfv
          have hwf_def_next : WellFormedSemanticEvalDef ρ_src_next.eval := by rw [h_eval_next]; exact hwf_def
          have hwf_congr_next : WellFormedSemanticEvalExprCongr ρ_src_next.eval := by rw [h_eval_next]; exact hwf_congr
          have hwf_var_next : WellFormedSemanticEvalVar ρ_src_next.eval := by rw [h_eval_next]; exact hwf_var
          have h_eval_eq_next : ρ_tgt_next.eval = ρ_src_next.eval := by
            show ρ_inner_tgt.eval = ρ_inner.eval; exact h_eval_inner
          have h_fail_eq_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
            show ρ_inner_tgt.hasFailure = ρ_inner.hasFailure; exact h_fail_inner
          have h_agree_next : AgreeOffGen Q ρ_src_next.store ρ_tgt_next.store := by
            intro x h_nongen
            have h_x_ne : x ≠ HasIdent.ident (P := P) g := by
              rintro rfl; exact (h_nongen g rfl) h_g_gen
            show (if (ρ_tgt.store x).isSome then
                (if x = HasIdent.ident (P := P) g then some HasBool.tt else ρ_inner_tgt.store x)
                else none)
              = (if (ρ_src.store x).isSome then ρ_inner.store x else none)
            rw [if_neg h_x_ne, h_agree x h_nongen, h_off_inner x h_nongen]
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
                then storeWith ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt
                  (HasIdent.ident (P := P) s) else none) = none
            rw [h_tgt_fresh s h_suf h_notin]; rfl
          have h_bound : h_loop_T_T.len ≤ n := by omega
          have hlen_tail : hrest_next.len ≤ n :=
            Nat.le_of_lt (Nat.lt_of_lt_of_le hlen_next h_bound)
          obtain ⟨h_fresh', ρ_out, h_loop_tgt, h_off', h_fail', h_eval', h_fresh_out⟩ :=
            ih (oc := none) (ρ_src := ρ_src_next) (ρ' := ρ_x) (ρ_tgt := ρ_tgt_next)
              h_eval_eq_next h_fail_eq_next h_agree_next
              hwfb_next hwfv_next hwf_def_next hwf_congr_next hwf_var_next
              h_src_fresh_next h_tgt_fresh_next true h_guard_next
              (.inr ⟨rfl, hrest_next, hlen_tail⟩)
          simp only [outcomeConfig] at h_loop_tgt
          refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', h_fresh_out⟩
          refine .step _ _ _ (StepStmt.step_loop_enter (hasInvFailure := false)
            h_guard_tt (by simp) (by simp) (h_eval_eq ▸ hwfb)) ?_
          have h_block_run : StepStmtStar P (EvalCmd P) extendEval
              (.block .none ρ_tgt.store (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P)))
              (.terminal ρ_tgt_next) := by
            refine ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) extendEval _ _ .none ρ_tgt.store h_body_tail) ?_
            exact .step _ _ _ StepStmt.step_block_done (.refl _)
          refine ReflTrans_Transitive _ _ _ _
            (ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendEval _ _ _ h_block_run)
              (.step _ _ _ StepStmt.step_seq_done (.refl _)))
            (ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P (EvalCmd P) extendEval _ _ ρ_tgt_next ρ_out h_loop_tgt)
              (.step _ _ _ StepStmt.step_stmts_nil (.refl _)))
      | some lbl =>
        simp only [outcomeConfig] at hrest ⊢
        have hl : hrest.len ≤ n + 1 := hl
        rcases seqT_reaches_exiting (extendEval := extendEval) hrest with
          ⟨h_block_exit, hlen_be⟩ | ⟨ρ_block, h_block_term, h_loop_exit, hlen_te⟩
        · -- Body-block exits with lbl: the body exits, propagated past the loop.
          have ⟨ρ_inner, h_inner_exit, heq_ρ', hlen_inner⟩ :=
            blockT_none_reaches_exiting (extendEval := extendEval) h_block_exit
          have h_body_run : StepStmtStar P (EvalCmd P) extendEval
              (.stmts body ρ_src) (outcomeConfig (some lbl) ρ_inner) :=
            hρ_src'_eq ▸ reflTransT_to_prop h_inner_exit
          obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner,
              h_eval_inner, h_fresh_inner⟩ :=
            h_body_sim (some lbl) ρ_src ρ_inner ρ_tgt h_eval_eq h_fail_eq h_agree hwfb hwfv hwf_def hwf_congr
              hwf_var h_wf_gen h_src_fresh h_tgt_fresh h_body_run
          subst heq_ρ'
          refine ⟨?_, ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store } : Env P),
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
            refine .step _ _ _ (StepStmt.step_loop_enter (hasInvFailure := false)
              h_guard_tt (by simp) (by simp) (h_eval_eq ▸ hwfb)) ?_
            have h_body_tgt' : StepStmtStar P (EvalCmd P) extendEval
                (.stmts body' ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P))
                (.exiting lbl ρ_inner_tgt) := by
              have he : ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P) = ρ_tgt := by
                simp [Bool.or_false]
              rw [he]; simpa only [outcomeConfig] using h_body_tgt
            -- body' ++ [havoc] exits lbl (the prefix exits, suffix skipped).
            have h_body_tail_exit : StepStmtStar P (EvalCmd P) extendEval
                (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                  ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P))
                (.exiting lbl ρ_inner_tgt) :=
              stmts_cons_head_exiting_append (extendEval := extendEval) _ _ _ ρ_inner_tgt lbl h_body_tgt'
            have h_block_tgt_exit : StepStmtStar P (EvalCmd P) extendEval
                (.block .none ρ_tgt.store (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                  ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P)))
                (.exiting lbl ({ ρ_inner_tgt with store := projectStore ρ_tgt.store ρ_inner_tgt.store } : Env P)) := by
              refine ReflTrans_Transitive _ _ _ _
                (block_inner_star P (EvalCmd P) extendEval _ _ .none ρ_tgt.store h_body_tail_exit) ?_
              exact .step _ _ _ (StepStmt.step_block_exit_mismatch (by simp)) (.refl _)
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendEval _ _ _ h_block_tgt_exit) ?_
            exact .step _ _ _ StepStmt.step_seq_exit (.refl _)
          · intro x h_nongen
            show projectStore ρ_tgt.store ρ_inner_tgt.store x
              = projectStore ρ_src.store ρ_inner.store x
            show (if (ρ_tgt.store x).isSome then ρ_inner_tgt.store x else none)
              = (if (ρ_src.store x).isSome then ρ_inner.store x else none)
            rw [h_agree x h_nongen, h_off_inner x h_nongen]
          · exact h_fail_inner
          · exact h_eval_inner
          · intro s h_suf h_notin
            show (if (ρ_tgt.store (HasIdent.ident (P := P) s)).isSome
                then ρ_inner_tgt.store (HasIdent.ident (P := P) s) else none) = none
            rw [h_tgt_fresh s h_suf h_notin]; rfl
        · -- Body terminates, loop tail exits with lbl: recurse on the tail.
          have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
            blockT_none_reaches_terminal (extendEval := extendEval) h_block_term
          have ⟨h_loop_T_exit, hlen_cons⟩ :=
            stmtsT_singleton_exiting (extendEval := extendEval) h_loop_exit
          have h_body_run : StepStmtStar P (EvalCmd P) extendEval
              (.stmts body ρ_src) (outcomeConfig none ρ_inner) :=
            hρ_src'_eq ▸ reflTransT_to_prop h_inner_term
          obtain ⟨h_inner_fresh, ρ_inner_tgt, h_body_tgt, h_off_inner, h_fail_inner,
              h_eval_inner, h_fresh_inner⟩ :=
            h_body_sim none ρ_src ρ_inner ρ_tgt h_eval_eq h_fail_eq h_agree hwfb hwfv hwf_def hwf_congr
              hwf_var h_wf_gen h_src_fresh h_tgt_fresh h_body_run
          have h_eval_inner_src : ρ_inner.eval = ρ_src.eval :=
            block_noFuncDecl_preserves_eval P (EvalCmd P) extendEval body ρ_src ρ_inner h_nofd_body
              (by simpa only [outcomeConfig] using h_body_run)
          have heq_ρ_block_full :
              ρ_block = ({ ρ_inner with store := projectStore ρ_src.store ρ_inner.store } : Env P) := by
            rw [heq_ρ_block]
          subst heq_ρ_block_full
          have h_g_some_tgt : (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome = true := by
            rw [h_guard_def]; rfl
          have h_body_tgt_term : StepStmtStar P (EvalCmd P) extendEval
              (.stmts body' ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P))
              (.terminal ρ_inner_tgt) := by
            have he : ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P) = ρ_tgt := by
              simp [Bool.or_false]
            rw [he]; simpa only [outcomeConfig] using h_body_tgt
          have h_g_some_inner : (ρ_inner_tgt.store (HasIdent.ident (P := P) g)).isSome = true :=
            stmts_preserves_isSome (extendEval := extendEval) h_body_tgt_term (y := HasIdent.ident (P := P) g)
              (show (({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P).store
                (HasIdent.ident (P := P) g)).isSome = true from h_g_some_tgt)
          obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp h_g_some_inner
          have hwf_var_inner : WellFormedSemanticEvalVar ρ_inner_tgt.eval := by
            rw [h_eval_inner, h_eval_inner_src]; exact hwf_var
          let ρ_src_next : Env P := { ρ_inner with store := projectStore ρ_src.store ρ_inner.store }
          -- Invert the loop tail (exiting lbl) to learn the next decision.  EXIT
          -- is impossible (`.terminal _ →* .exiting lbl`), so the next is ENTER:
          -- re-havoc $g := tt and recurse with entering = true.
          have hrest_enter :
              ∃ (hr : ReflTransT (StepStmt P (EvalCmd P) extendEval)
                (.seq (.block .none ρ_src_next.store (.stmts body
                    ({ ρ_src_next with hasFailure := ρ_src_next.hasFailure || false } : Env P)))
                  [.loop .nondet m ([] : List (String × P.Expr)) body md])
                (outcomeConfig (some lbl) ρ')), hr.len ≤ n := by
            rcases loop_nondet_step_first_inv (extendEval := extendEval) (oc := some lbl)
                h_loop_T_exit with
              ⟨hrest_next, _⟩ | ⟨hrest_next, hlen_next⟩
            · exfalso
              simp only [outcomeConfig] at hrest_next
              match hrest_next with
              | .step _ _ _ h _ => exact nomatch h
            · have h_bound : h_loop_T_exit.len ≤ n := by omega
              exact ⟨hrest_next, Nat.le_of_lt (Nat.lt_of_lt_of_le hlen_next h_bound)⟩
          obtain ⟨hrest_next, hlen_tail⟩ := hrest_enter
          have h_tail : StepStmtStar P (EvalCmd P) extendEval
              (.stmt (.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)) ρ_inner_tgt)
              (.terminal ({ ρ_inner_tgt with store := storeWith ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P)) :=
            step_havoc_set_to (extendEval := extendEval) (HasIdent.ident (P := P) g) HasBool.tt md ρ_inner_tgt v' hv'
              hwf_var_inner
          have h_body_tail : StepStmtStar P (EvalCmd P) extendEval
              (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P))
              (.terminal ({ ρ_inner_tgt with store := storeWith ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P)) :=
            ReflTrans_Transitive _ _ _ _
              (stmts_prefix_terminal_append P (EvalCmd P) extendEval _ _ _ ρ_inner_tgt h_body_tgt_term)
              (stmt_to_singleton_stmts (extendEval := extendEval) _ ρ_inner_tgt _ h_tail)
          let ρ_tgt_next : Env P := { ρ_inner_tgt with store := projectStore ρ_tgt.store (storeWith ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) }
          have h_guard_next : ρ_tgt_next.store (HasIdent.ident (P := P) g) = some HasBool.tt := by
            show (if (ρ_tgt.store (HasIdent.ident (P := P) g)).isSome
                then storeWith ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt
                  (HasIdent.ident (P := P) g) else none) = some HasBool.tt
            rw [if_pos h_g_some_tgt]; simp [storeWith]
          have h_eval_next : ρ_src_next.eval = ρ_src.eval := h_eval_inner_src
          have hwfb_next : WellFormedSemanticEvalBool ρ_src_next.eval := by rw [h_eval_next]; exact hwfb
          have hwfv_next : WellFormedSemanticEvalVal ρ_src_next.eval := by rw [h_eval_next]; exact hwfv
          have hwf_def_next : WellFormedSemanticEvalDef ρ_src_next.eval := by rw [h_eval_next]; exact hwf_def
          have hwf_congr_next : WellFormedSemanticEvalExprCongr ρ_src_next.eval := by rw [h_eval_next]; exact hwf_congr
          have hwf_var_next : WellFormedSemanticEvalVar ρ_src_next.eval := by rw [h_eval_next]; exact hwf_var
          have h_eval_eq_next : ρ_tgt_next.eval = ρ_src_next.eval := by
            show ρ_inner_tgt.eval = ρ_inner.eval; exact h_eval_inner
          have h_fail_eq_next : ρ_tgt_next.hasFailure = ρ_src_next.hasFailure := by
            show ρ_inner_tgt.hasFailure = ρ_inner.hasFailure; exact h_fail_inner
          have h_agree_next : AgreeOffGen Q ρ_src_next.store ρ_tgt_next.store := by
            intro x h_nongen
            have h_x_ne : x ≠ HasIdent.ident (P := P) g := by
              rintro rfl; exact (h_nongen g rfl) h_g_gen
            show (if (ρ_tgt.store x).isSome then
                (if x = HasIdent.ident (P := P) g then some HasBool.tt else ρ_inner_tgt.store x)
                else none)
              = (if (ρ_src.store x).isSome then ρ_inner.store x else none)
            rw [if_neg h_x_ne, h_agree x h_nongen, h_off_inner x h_nongen]
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
                then storeWith ρ_inner_tgt.store (HasIdent.ident (P := P) g) HasBool.tt
                  (HasIdent.ident (P := P) s) else none) = none
            rw [h_tgt_fresh s h_suf h_notin]; rfl
          obtain ⟨h_fresh', ρ_out, h_loop_tgt, h_off', h_fail', h_eval', h_fresh_out⟩ :=
            ih (oc := some lbl) (ρ_src := ρ_src_next) (ρ' := ρ') (ρ_tgt := ρ_tgt_next)
              h_eval_eq_next h_fail_eq_next h_agree_next
              hwfb_next hwfv_next hwf_def_next hwf_congr_next hwf_var_next
              h_src_fresh_next h_tgt_fresh_next true h_guard_next
              (.inr ⟨rfl, hrest_next, hlen_tail⟩)
          simp only [outcomeConfig] at h_loop_tgt
          refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', h_fresh_out⟩
          refine .step _ _ _ (StepStmt.step_loop_enter (hasInvFailure := false)
            h_guard_tt (by simp) (by simp) (h_eval_eq ▸ hwfb)) ?_
          have h_block_run : StepStmtStar P (EvalCmd P) extendEval
              (.block .none ρ_tgt.store (.stmts (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)])
                ({ ρ_tgt with hasFailure := ρ_tgt.hasFailure || false } : Env P)))
              (.terminal ρ_tgt_next) := by
            refine ReflTrans_Transitive _ _ _ _
              (block_inner_star P (EvalCmd P) extendEval _ _ .none ρ_tgt.store h_body_tail) ?_
            exact .step _ _ _ StepStmt.step_block_done (.refl _)
          have h_loop_stmts_exit : StepStmtStar P (EvalCmd P) extendEval
              (.stmts [.loop (.det (HasFvar.mkFvar (HasIdent.ident (P := P) g))) m
                ([] : List (String × P.Expr))
                (body' ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md] ρ_tgt_next)
              (.exiting lbl ρ_out) := by
            refine .step _ _ _ StepStmt.step_stmts_cons ?_
            refine ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendEval _ _ _ h_loop_tgt) ?_
            exact .step _ _ _ StepStmt.step_seq_exit (.refl _)
          refine ReflTrans_Transitive _ _ _ _
            (ReflTrans_Transitive _ _ _ _
              (seq_inner_star P (EvalCmd P) extendEval _ _ _ h_block_run)
              (.step _ _ _ StepStmt.step_seq_done (.refl _)))
            h_loop_stmts_exit


/- General forward simulation with **separate** source and target start stores
threading the generator state `σ`.  This is the inductive workhorse: a source
run from `ρ_src` is simulated by the rewritten block from any target store that
agrees with the source off the gen-shaped guards (`AgreeOffGen`) and matches its
evaluator and failure flag.  The generated guard variables are hidden from the
source by `AgreeOffGen`/`StoreAgreement`'s treatment of the gen slots.

Invariants threaded:
- `AgreeOffGen Q ρ_src.store ρ_tgt.store`: target = source off the guard slots
  (so a fresh user var stays fresh in the target — the `.cmd`/`init` arm);
- `GenFreshStore Q σ ρ_tgt.store`: the target store has no *ungenerated* gen-shaped
  slot defined (so each freshly-generated guard slot is `none` for the inserted
  `init`/`set`);
- `h_src_fresh`: the source store has *no* gen-shaped slot defined (so the
  generated guard is hidden from the source via `storeAgreement_storeWith`);
- `SrcNoGenWrites ss`: the source program never writes a gen-shaped variable
  (spec §7; preserves `h_src_fresh` across sequencing);
- `WF σ`: the generator is well-formed (so generated names are genuinely fresh).

The conclusion strengthens to `AgreeOffGen Q ρ'.store ρ_out.store` so the inductive
step composes; the public `StoreAgreement` corollary follows by
`StoreAgreement.of_agreeOffGen`.  See spec §4. -/
mutual
/-- Per-statement forward simulation (the workhorse companion of
`nondetElim_simulation_gen`).  A terminating source run of a single statement
`s` is simulated by the rewritten block `(Stmt.nondetElimM s σ).1`, threading the
same invariants and producing the advanced-state freshness for sequencing. -/
private theorem nondetElim_stmt_gen {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasBool P] [LawfulHasIdent P]
    [LawfulHasIntOrder P] [LawfulHasNot P]
    {Q : String → Prop}
    (hQmint : (∀ sg, Q (StringGenState.gen ndelimItePrefix sg).1)
            ∧ (∀ sg, Q (StringGenState.gen ndelimLoopPrefix sg).1))
    (extendEval : ExtendEval P)
    (s : Stmt P (Cmd P)) (σ : StringGenState)
    (ρ_src ρ' ρ_tgt : Env P)
    (h_eval_eq : ρ_tgt.eval = ρ_src.eval)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree : AgreeOffGen Q ρ_src.store ρ_tgt.store)
    (hwfb : WellFormedSemanticEvalBool ρ_src.eval)
    (hwfv : WellFormedSemanticEvalVal ρ_src.eval)
    (hwf_def : WellFormedSemanticEvalDef ρ_src.eval)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ_src.eval)
    (hwf_var : WellFormedSemanticEvalVar ρ_src.eval)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : GenFreshStore Q σ ρ_tgt.store)
    (h_no_writes : NoGenSuffix (P := P) Q (Stmt.definedVars s ++ Stmt.modifiedVars s))
    (h_nofd : Stmt.noFuncDecl s = true)
    (h_lhni : Stmt.loopHasNoInvariants s = true)
    (oc : Option String)
    (h_term : StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ_src) (outcomeConfig oc ρ')) :
    (∀ t, Q t →
        ρ'.store (HasIdent.ident (P := P) t) = none)
      ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P) extendEval
          (.stmts (Stmt.nondetElimM s σ).1 ρ_tgt) (outcomeConfig oc ρ_out)
        ∧ AgreeOffGen Q ρ'.store ρ_out.store
        ∧ ρ_out.hasFailure = ρ'.hasFailure
        ∧ ρ_out.eval = ρ'.eval
        ∧ GenFreshStore Q (Stmt.nondetElimM s σ).2 ρ_out.store := by
  match s, h_no_writes, h_nofd, h_lhni, oc, h_term with
  | .cmd c, h_no_writes, _, _, oc, h_term =>
    -- A `.cmd` only ever reaches `.terminal`, so the exiting outcome is vacuous.
    match oc, h_term with
    | none, h_term =>
    -- Output is the same `.cmd c`; replay it under `AgreeOffGen`.
    have h_no_writes_c : NoGenSuffix (P := P) Q (Cmd.definedVars c ++ Cmd.modifiedVars c) := by
      have h_dv : Stmt.definedVars (P := P) (.cmd c) = Cmd.definedVars c := by
        with_unfolding_all rfl
      have h_mv : Stmt.modifiedVars (P := P) (.cmd c) = Cmd.modifiedVars c := by
        with_unfolding_all rfl
      rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
    obtain ⟨h_src'_fresh, ρ_tgt', h_run, h_off', h_fail', h_eval', h_fresh'⟩ :=
      cmd_replay_agreement_offgen extendEval c ρ_src ρ' ρ_tgt σ
        h_eval_eq h_fail_eq h_agree hwf_def hwf_congr h_src_fresh h_tgt_fresh
        h_no_writes_c h_term
    refine ⟨h_src'_fresh, ρ_tgt', ?_, h_off', h_fail', h_eval', ?_⟩
    · simp only [Stmt.nondetElimM, outcomeConfig]
      exact stmt_to_singleton_stmts (extendEval := extendEval) (.cmd c) ρ_tgt ρ_tgt' h_run
    · simp only [Stmt.nondetElimM]; exact h_fresh'
    | some lbl, h_term =>
      -- `.cmd c` cannot reach `.exiting`: its only step is `step_cmd` to `.terminal`.
      exfalso
      obtain ⟨cfg, hstep, hrest⟩ :=
        stmt_step_first_inv_to (extendEval := extendEval) _ ρ_src (outcomeConfig (some lbl) ρ')
          (by intro ρ'' h; simp only [outcomeConfig] at h <;> cases h) h_term
      cases hstep with
      | step_cmd _ =>
        -- residual run: `.terminal _ →* .exiting lbl ρ'` is impossible.
        cases hrest with
        | step _ _ _ h _ => cases h
  | .block lbl bss md, h_no_writes, h_nofd, h_lhni, oc, h_term =>
    -- Source: `.stmt (.block lbl bss md) ρ_src` steps via `step_block` to the
    -- block context `.block (.some lbl) ρ_src.store (.stmts bss ρ_src)`, which
    -- then reaches the outer outcome.  Invert it to the inner body's run.
    obtain ⟨c, hstep, hrest⟩ :=
      stmt_step_first_inv_to (extendEval := extendEval) _ ρ_src (outcomeConfig oc ρ')
        (by intro ρ'' h; cases oc <;> simp only [outcomeConfig] at h <;> cases h) h_term
    cases hstep with
    | step_block =>
      -- Distribute the source side-conditions onto `bss`.
      have h_dv : Stmt.definedVars (P := P) (.block lbl bss md) = Block.definedVars bss := by
        with_unfolding_all rfl
      have h_mv : Stmt.modifiedVars (P := P) (.block lbl bss md) = Block.modifiedVars bss := by
        with_unfolding_all rfl
      have h_no_writes_bss : SrcNoGenWrites (P := P) Q bss := by
        show NoGenSuffix (P := P) Q (Block.definedVars bss ++ Block.modifiedVars bss)
        rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
      have h_nofd_bss : Block.noFuncDecl bss = true := by
        simpa only [Stmt.noFuncDecl] using h_nofd
      have h_lhni_bss : Block.loopHasNoInvariants bss = true :=
        Stmt.loopHasNoInvariants_block_body h_lhni
      -- In every subcase the inner body `bss` reaches some inner outcome
      -- `outcomeConfig oc_inner ρ_inner`, with `ρ' = ρ_inner ⊳ projectStore`.
      -- We first determine `oc_inner` from `oc` and the block inversion, then
      -- recurse on `bss`, then re-wrap with the matching block step rule.  The
      -- five store-level conjuncts are identical across subcases (both target and
      -- source project the inner store through their agreeing parents), so we
      -- discharge them through the shared `wrap` continuation.
      have wrap : ∀ (oc_inner : Option String) (ρ_inner : Env P),
          StepStmtStar P (EvalCmd P) extendEval
            (.stmts bss ρ_src) (outcomeConfig oc_inner ρ_inner) →
          (∀ (ρ_out_inner : Env P),
            StepStmtStar P (EvalCmd P) extendEval
              (.stmts (Block.nondetElimM bss σ).1 ρ_tgt) (outcomeConfig oc_inner ρ_out_inner) →
            StepStmtStar P (EvalCmd P) extendEval
              (.stmts (Stmt.nondetElimM (.block lbl bss md) σ).1 ρ_tgt)
              (outcomeConfig oc ({ ρ_out_inner with
                store := projectStore ρ_tgt.store ρ_out_inner.store } : Env P))) →
          ρ' = { ρ_inner with store := projectStore ρ_src.store ρ_inner.store } →
          (∀ t, Q t →
              ρ'.store (HasIdent.ident (P := P) t) = none)
            ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P) extendEval
                (.stmts (Stmt.nondetElimM (.block lbl bss md) σ).1 ρ_tgt)
                (outcomeConfig oc ρ_out)
              ∧ AgreeOffGen Q ρ'.store ρ_out.store
              ∧ ρ_out.hasFailure = ρ'.hasFailure
              ∧ ρ_out.eval = ρ'.eval
              ∧ GenFreshStore Q (Stmt.nondetElimM (.block lbl bss md) σ).2 ρ_out.store := by
        intro oc_inner ρ_inner h_inner_run wrap_run h_ρ'_eq
        obtain ⟨h_fresh_inner, ρ_out_inner, h_run_inner, h_off_inner, h_fail_inner,
            h_eval_inner, h_fresh_out⟩ :=
          nondetElim_simulation_gen hQmint extendEval bss σ ρ_src ρ_inner ρ_tgt
            h_eval_eq h_fail_eq h_agree hwfb hwfv hwf_def hwf_congr hwf_var
            h_wf_gen h_src_fresh h_tgt_fresh h_no_writes_bss h_nofd_bss h_lhni_bss
            oc_inner h_inner_run
        refine ⟨?_, ({ ρ_out_inner with
          store := projectStore ρ_tgt.store ρ_out_inner.store } : Env P),
          wrap_run ρ_out_inner h_run_inner, ?_, ?_, ?_, ?_⟩
        · -- ρ'.store is fresh: ρ' = ρ_inner projected through ρ_src.store.
          subst h_ρ'_eq
          intro t h_suf
          show projectStore ρ_src.store ρ_inner.store (HasIdent.ident (P := P) t) = none
          show (if (ρ_src.store (HasIdent.ident (P := P) t)).isSome
              then ρ_inner.store (HasIdent.ident (P := P) t) else none) = none
          by_cases hp : (ρ_src.store (HasIdent.ident (P := P) t)).isSome
          · rw [if_pos hp]; exact h_fresh_inner t h_suf
          · rw [if_neg hp]
        · -- AgreeOffGen Q survives projecting both stores through agreeing parents.
          subst h_ρ'_eq
          intro x h_nongen
          show projectStore ρ_tgt.store ρ_out_inner.store x
            = projectStore ρ_src.store ρ_inner.store x
          show (if (ρ_tgt.store x).isSome then ρ_out_inner.store x else none)
            = (if (ρ_src.store x).isSome then ρ_inner.store x else none)
          have h_par : ρ_tgt.store x = ρ_src.store x := h_agree x h_nongen
          have h_inn : ρ_out_inner.store x = ρ_inner.store x := h_off_inner x h_nongen
          rw [h_par, h_inn]
        · -- hasFailure unchanged: the record-update keeps `hasFailure`.
          subst h_ρ'_eq; exact h_fail_inner
        · -- eval unchanged.
          subst h_ρ'_eq; exact h_eval_inner
        · -- GenFreshStore Q at the block output state = (Block.nondetElimM bss σ).2.
          have h_out_eq : (Stmt.nondetElimM (.block lbl bss md) σ).2
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
      -- Now branch on the outer outcome.
      cases oc with
      | none =>
        -- Block terminates: body terminated, or exited matching `lbl`.
        rcases block_some_reaches_terminal P (EvalCmd P) extendEval hrest with
          ⟨ρ_inner, h_inner_term, h_ρ'_eq⟩ | ⟨ρ_inner, h_inner_exit, h_ρ'_eq⟩
        · -- TERMINAL inner: re-wrap with `step_block_done`.
          refine wrap none ρ_inner h_inner_term (fun ρ_out_inner h_run_inner => ?_) h_ρ'_eq
          rw [Stmt.nondetElimM_block_out]
          refine stmt_to_singleton_stmts (extendEval := extendEval) _ ρ_tgt _ ?_
          refine .step _ _ _ (StepStmt.step_block) ?_
          refine ReflTrans_Transitive _ _ _ _
            (block_inner_star P (EvalCmd P) extendEval _ _ (.some lbl) ρ_tgt.store
              (show StepStmtStar P (EvalCmd P) extendEval _ (.terminal ρ_out_inner) from
                h_run_inner)) ?_
          exact .step _ _ _ StepStmt.step_block_done (.refl _)
        · -- MATCHING-EXIT inner: re-wrap with `step_block_exit_match`.
          refine wrap (some lbl) ρ_inner h_inner_exit (fun ρ_out_inner h_run_inner => ?_) h_ρ'_eq
          rw [Stmt.nondetElimM_block_out]
          refine stmt_to_singleton_stmts (extendEval := extendEval) _ ρ_tgt _ ?_
          refine .step _ _ _ (StepStmt.step_block) ?_
          refine ReflTrans_Transitive _ _ _ _
            (block_inner_star P (EvalCmd P) extendEval _ _ (.some lbl) ρ_tgt.store
              (show StepStmtStar P (EvalCmd P) extendEval _ (.exiting lbl ρ_out_inner) from
                h_run_inner)) ?_
          exact .step _ _ _ (StepStmt.step_block_exit_match rfl) (.refl _)
      | some lbl' =>
        -- Block exits with `lbl'`: body exited with the same (non-matching) label.
        obtain ⟨ρ_inner, h_inner_exit, h_ne, h_ρ'_eq⟩ :=
          block_reaches_exiting_strong P (EvalCmd P) extendEval hrest
        refine wrap (some lbl') ρ_inner h_inner_exit
          (fun ρ_out_inner h_run_inner => ?_) h_ρ'_eq
        rw [Stmt.nondetElimM_block_out]
        refine stmt_to_singleton_stmts_exiting (extendEval := extendEval) _ ρ_tgt _ lbl' ?_
        refine .step _ _ _ (StepStmt.step_block) ?_
        refine ReflTrans_Transitive _ _ _ _
          (block_inner_star P (EvalCmd P) extendEval _ _ (.some lbl) ρ_tgt.store
            (show StepStmtStar P (EvalCmd P) extendEval _ (.exiting lbl' ρ_out_inner) from
              h_run_inner)) ?_
        exact .step _ _ _ (StepStmt.step_block_exit_mismatch h_ne) (.refl _)
  | .ite (.det e) tss ess md, h_no_writes, h_nofd, h_lhni, oc, h_term =>
    -- The deterministic guard reads the same value in the target (AgreeOffGen Q on
    -- the guard's source-defined vars), so the target takes the matching branch.
    obtain ⟨cfg, hstep, hbranch⟩ :=
      stmt_step_first_inv_to (extendEval := extendEval) _ ρ_src (outcomeConfig oc ρ')
        (by intro ρ'' h; cases oc <;> simp only [outcomeConfig] at h <;> cases h) h_term
    have hwf_var_t : WellFormedSemanticEvalVar ρ_tgt.eval := h_eval_eq ▸ hwf_var
    -- Source-shape and noFuncDecl split into the two branches.
    have h_dv : Stmt.definedVars (P := P) (.ite (.det e) tss ess md)
        = Block.definedVars tss ++ Block.definedVars ess := rfl
    have h_mv : Stmt.modifiedVars (P := P) (.ite (.det e) tss ess md)
        = Block.modifiedVars tss ++ Block.modifiedVars ess := rfl
    have h_nofd' : Block.noFuncDecl tss = true ∧ Block.noFuncDecl ess = true := by
      have : (Block.noFuncDecl tss && Block.noFuncDecl ess) = true := by
        simpa only [Stmt.noFuncDecl] using h_nofd
      exact Bool.and_eq_true _ _ |>.mp this
    -- The target output: [.ite (.det e) tss' ess'].
    cases hstep with
    | step_ite_true h_cond hwfb_s =>
      -- Branch `tss` runs to terminal `ρ'`; recurse on it via the block lemma.
      have h_no_writes_t : SrcNoGenWrites (P := P) Q tss := by
        intro x hx t heq
        rcases List.mem_append.mp hx with hd | hm
        · exact h_no_writes x (by rw [h_dv]; exact List.mem_append_left _ (List.mem_append_left _ hd)) t heq
        · exact h_no_writes x (by rw [h_mv]; exact List.mem_append_right _ (List.mem_append_left _ hm)) t heq
      obtain ⟨h_fresh', ρ_out, h_run, h_off', h_fail', h_eval', h_fresh_out⟩ :=
        nondetElim_simulation_gen hQmint extendEval tss σ ρ_src ρ' ρ_tgt
          h_eval_eq h_fail_eq h_agree hwfb hwfv hwf_def hwf_congr hwf_var
          h_wf_gen h_src_fresh h_tgt_fresh h_no_writes_t h_nofd'.1
          (Stmt.loopHasNoInvariants_branch_then h_lhni) oc hbranch
      refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', ?_⟩
      · -- Target: [.ite (.det e) (nondetElim tss) (nondetElim ess at σ₂)] reads tt.
        rw [Stmt.nondetElimM_ite_det_out]
        -- guard reads tt in target
        have h_def_e : isDefined ρ_src.store (HasVarsPure.getVars e) :=
          hwf_def e HasBool.tt ρ_src.store h_cond
        have h_pw : ∀ x ∈ HasVarsPure.getVars e, ρ_src.store x = ρ_tgt.store x :=
          agreeOffGen_pointwise_on_expr_vars ρ_src.store ρ_tgt.store e h_agree h_src_fresh h_def_e
        have h_cond_t : ρ_tgt.eval ρ_tgt.store e = some HasBool.tt := by
          rw [h_eval_eq, ← h_cond]; exact (hwf_congr e ρ_src.store ρ_tgt.store h_pw).symm
        refine stmt_to_singleton_stmts_outcome (extendEval := extendEval) _ ρ_tgt ρ_out oc ?_
        refine .step _ _ _ (StepStmt.step_ite_true h_cond_t (h_eval_eq ▸ hwfb)) ?_
        exact h_run
      · simp only [Stmt.nondetElimM]
        rcases h₁ : Block.nondetElimM tss σ with ⟨tss', σ₁⟩
        rcases h₂ : Block.nondetElimM ess σ₁ with ⟨ess', σ₂⟩
        simp only [h₂]
        -- Freshness at σ₂ ⊇ σ₁ = output of tss; ρ_out fresh at σ₁ (= (nondetElimM tss σ).2).
        have h_eq1 : σ₁ = (Block.nondetElimM tss σ).2 := by rw [h₁]
        have h_step12 : StringGenState.GenStep σ₁ σ₂ := by
          have := Block.nondetElimM_genStep ess σ₁; rw [h₂] at this; exact this
        have h_fresh_σ₁ : GenFreshStore Q σ₁ ρ_out.store := by
          rw [h_eq1]; exact h_fresh_out
        exact GenFreshStore.mono h_step12 h_fresh_σ₁
    | step_ite_false h_cond hwfb_s =>
      have h_no_writes_e : SrcNoGenWrites (P := P) Q ess := by
        intro x hx t heq
        rcases List.mem_append.mp hx with hd | hm
        · exact h_no_writes x (by rw [h_dv]; exact List.mem_append_left _ (List.mem_append_right _ hd)) t heq
        · exact h_no_writes x (by rw [h_mv]; exact List.mem_append_right _ (List.mem_append_right _ hm)) t heq
      -- The else branch runs from σ₁ = (Block.nondetElimM tss σ).2.
      have h_wf₁ : StringGenState.WF (Block.nondetElimM tss σ).2 :=
        (Block.nondetElimM_genStep tss σ).wf_mono h_wf_gen
      have h_tgt_fresh₁ : GenFreshStore Q (Block.nondetElimM tss σ).2 ρ_tgt.store :=
        GenFreshStore.mono (Block.nondetElimM_genStep tss σ) h_tgt_fresh
      obtain ⟨h_fresh', ρ_out, h_run, h_off', h_fail', h_eval', h_fresh_out⟩ :=
        nondetElim_simulation_gen hQmint extendEval ess (Block.nondetElimM tss σ).2 ρ_src ρ' ρ_tgt
          h_eval_eq h_fail_eq h_agree hwfb hwfv hwf_def hwf_congr hwf_var
          h_wf₁ h_src_fresh h_tgt_fresh₁ h_no_writes_e h_nofd'.2
          (Stmt.loopHasNoInvariants_branch_else h_lhni) oc hbranch
      refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', ?_⟩
      · rw [Stmt.nondetElimM_ite_det_out]
        have h_def_e : isDefined ρ_src.store (HasVarsPure.getVars e) :=
          hwf_def e HasBool.ff ρ_src.store h_cond
        have h_pw : ∀ x ∈ HasVarsPure.getVars e, ρ_src.store x = ρ_tgt.store x :=
          agreeOffGen_pointwise_on_expr_vars ρ_src.store ρ_tgt.store e h_agree h_src_fresh h_def_e
        have h_cond_t : ρ_tgt.eval ρ_tgt.store e = some HasBool.ff := by
          rw [h_eval_eq, ← h_cond]; exact (hwf_congr e ρ_src.store ρ_tgt.store h_pw).symm
        refine stmt_to_singleton_stmts_outcome (extendEval := extendEval) _ ρ_tgt ρ_out oc ?_
        refine .step _ _ _ (StepStmt.step_ite_false h_cond_t (h_eval_eq ▸ hwfb)) ?_
        exact h_run
      · simp only [Stmt.nondetElimM]
        rcases h₁ : Block.nondetElimM tss σ with ⟨tss', σ₁⟩
        rcases h₂ : Block.nondetElimM ess σ₁ with ⟨ess', σ₂⟩
        simp only [h₂]
        have h_eq2 : σ₂ = (Block.nondetElimM ess σ₁).2 := by rw [h₂]
        have h_eq1 : σ₁ = (Block.nondetElimM tss σ).2 := by rw [h₁]
        rw [h_eq2, h_eq1] at *
        exact h_fresh_out
  | .ite .nondet tss ess md, h_no_writes, h_nofd, h_lhni, oc, h_term =>
    -- Generated guard and advanced state.
    rcases hgen : StringGenState.gen ndelimItePrefix σ with ⟨g, σ₁⟩
    -- g is gen-shaped and the target guard slot is fresh.
    have h_g_gen : Q g := by
      have := hQmint.1 σ
      rw [hgen] at this; exact this
    have h_tgt_g_none : ρ_tgt.store (HasIdent.ident (P := P) g) = none := by
      have := GenFreshStore.gen_slot_none ndelimItePrefix h_tgt_fresh h_wf_gen (hQmint.1 σ)
      rw [hgen] at this; exact this
    have hwf_var_t : WellFormedSemanticEvalVar ρ_tgt.eval := h_eval_eq ▸ hwf_var
    have hwfb_t : WellFormedSemanticEvalBool ρ_tgt.eval := h_eval_eq ▸ hwfb
    -- GenStep facts.
    have h_step01 : StringGenState.GenStep σ σ₁ := by
      have := StringGenState.GenStep.of_gen ndelimItePrefix σ; rw [hgen] at this; exact this
    have h_wf₁ : StringGenState.WF σ₁ := h_step01.wf_mono h_wf_gen
    -- Branch source-shape splits.
    have h_dv : Stmt.definedVars (P := P) (.ite .nondet tss ess md)
        = Block.definedVars tss ++ Block.definedVars ess := rfl
    have h_mv : Stmt.modifiedVars (P := P) (.ite .nondet tss ess md)
        = Block.modifiedVars tss ++ Block.modifiedVars ess := rfl
    have h_nofd' : Block.noFuncDecl tss = true ∧ Block.noFuncDecl ess = true := by
      have : (Block.noFuncDecl tss && Block.noFuncDecl ess) = true := by
        simpa only [Stmt.noFuncDecl] using h_nofd
      exact Bool.and_eq_true _ _ |>.mp this
    have h_no_writes_t : SrcNoGenWrites (P := P) Q tss := by
      intro x hx t heq
      rcases List.mem_append.mp hx with hd | hm
      · exact h_no_writes x (by rw [h_dv]; exact List.mem_append_left _ (List.mem_append_left _ hd)) t heq
      · exact h_no_writes x (by rw [h_mv]; exact List.mem_append_right _ (List.mem_append_left _ hm)) t heq
    have h_no_writes_e : SrcNoGenWrites (P := P) Q ess := by
      intro x hx t heq
      rcases List.mem_append.mp hx with hd | hm
      · exact h_no_writes x (by rw [h_dv]; exact List.mem_append_left _ (List.mem_append_right _ hd)) t heq
      · exact h_no_writes x (by rw [h_mv]; exact List.mem_append_right _ (List.mem_append_right _ hm)) t heq
    -- Invert source nondet-ite: either tss or ess runs to the outcome.
    rcases ite_nondet_step_inv_outcome (extendEval := extendEval) tss ess md ρ_src ρ' oc h_term with h_br | h_br
    · -- True branch fired: choose havoc value tt.
      have h_off_g : AgreeOffGen Q ρ_src.store
          (storeWith ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) :=
        AgreeOffGen.storeWith_gen h_agree h_g_gen
      have h_fresh_g : GenFreshStore Q σ₁
          (storeWith ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) := by
        have := GenFreshStore.storeWith_gen (P := P) ndelimItePrefix HasBool.tt h_tgt_fresh
        rw [hgen] at this; exact this
      obtain ⟨h_fresh', ρ_out, h_run, h_off', h_fail', h_eval', h_fresh_out⟩ :=
        nondetElim_simulation_gen hQmint extendEval tss σ₁
          ρ_src ρ' ({ ρ_tgt with store := storeWith ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P)
          h_eval_eq h_fail_eq h_off_g hwfb hwfv hwf_def hwf_congr hwf_var
          h_wf₁ h_src_fresh h_fresh_g h_no_writes_t h_nofd'.1
          (Stmt.loopHasNoInvariants_branch_then h_lhni) oc h_br
      refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', ?_⟩
      · rw [Stmt.nondetElimM_ite_nondet_out]
        simp only [hgen]
        exact step_ndelim_ite_prefix_true_outcome (extendEval := extendEval) (HasIdent.ident (P := P) g)
          (Block.nondetElimM tss σ₁).1 (Block.nondetElimM ess (Block.nondetElimM tss σ₁).2).1 md
          ρ_tgt ρ_out oc h_tgt_g_none hwf_var_t hwfb_t h_run
      · simp only [Stmt.nondetElimM, hgen]
        rcases h₁ : Block.nondetElimM tss σ₁ with ⟨tss', σ₂⟩
        rcases h₂ : Block.nondetElimM ess σ₂ with ⟨ess', σ₃⟩
        simp only [h₂]
        have h_eq2 : σ₂ = (Block.nondetElimM tss σ₁).2 := by rw [h₁]
        have h_step23 : StringGenState.GenStep σ₂ σ₃ := by
          have := Block.nondetElimM_genStep ess σ₂; rw [h₂] at this; exact this
        have h_fresh_σ₂ : GenFreshStore Q σ₂ ρ_out.store := by rw [h_eq2]; exact h_fresh_out
        exact GenFreshStore.mono h_step23 h_fresh_σ₂
    · -- False branch fired: choose havoc value ff.  The output's else branch is
      -- generated at σ₂ = (nondetElimM tss σ₁).2, so recurse on `ess` at σ₂.
      have h_step12 : StringGenState.GenStep σ₁ (Block.nondetElimM tss σ₁).2 :=
        Block.nondetElimM_genStep tss σ₁
      have h_wf₂ : StringGenState.WF (Block.nondetElimM tss σ₁).2 := h_step12.wf_mono h_wf₁
      have h_off_g : AgreeOffGen Q ρ_src.store
          (storeWith ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) :=
        AgreeOffGen.storeWith_gen h_agree h_g_gen
      have h_fresh_g1 : GenFreshStore Q σ₁
          (storeWith ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) := by
        have := GenFreshStore.storeWith_gen (P := P) ndelimItePrefix HasBool.ff h_tgt_fresh
        rw [hgen] at this; exact this
      have h_fresh_g : GenFreshStore Q (Block.nondetElimM tss σ₁).2
          (storeWith ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) :=
        GenFreshStore.mono h_step12 h_fresh_g1
      obtain ⟨h_fresh', ρ_out, h_run, h_off', h_fail', h_eval', h_fresh_out⟩ :=
        nondetElim_simulation_gen hQmint extendEval ess (Block.nondetElimM tss σ₁).2
          ρ_src ρ' ({ ρ_tgt with store := storeWith ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff } : Env P)
          h_eval_eq h_fail_eq h_off_g hwfb hwfv hwf_def hwf_congr hwf_var
          h_wf₂ h_src_fresh h_fresh_g h_no_writes_e h_nofd'.2
          (Stmt.loopHasNoInvariants_branch_else h_lhni) oc h_br
      refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', ?_⟩
      · rw [Stmt.nondetElimM_ite_nondet_out]
        simp only [hgen]
        exact step_ndelim_ite_prefix_false_outcome (extendEval := extendEval) (HasIdent.ident (P := P) g)
          (Block.nondetElimM tss σ₁).1 (Block.nondetElimM ess (Block.nondetElimM tss σ₁).2).1 md
          ρ_tgt ρ_out oc h_tgt_g_none hwf_var_t hwfb_t h_run
      · simp only [Stmt.nondetElimM, hgen]
        rcases h₁ : Block.nondetElimM tss σ₁ with ⟨tss', σ₂⟩
        rcases h₂ : Block.nondetElimM ess σ₂ with ⟨ess', σ₃⟩
        simp only [h₂]
        simp only [h₁, h₂] at h_fresh_out
        exact h_fresh_out
  | .loop (.det e) m inv body md, h_no_writes, h_nofd, h_lhni, oc, h_term =>
    -- The invariant list is empty (`h_lhni`), so the loop matches the iteration
    -- lemma's shape.  The body output `(Block.nondetElimM body σ).1` is fixed
    -- across iterations; `nondetElim_simulation_gen` on `body` supplies the
    -- per-iteration body simulation.
    have h_inv_nil : inv = [] := Stmt.loopHasNoInvariants_loop_invs h_lhni
    subst h_inv_nil
    have h_lhni_body : Block.loopHasNoInvariants body = true :=
      Stmt.loopHasNoInvariants_loop_body_rec h_lhni
    have h_nofd_body : Block.noFuncDecl body = true := by
      simpa only [Stmt.noFuncDecl] using h_nofd
    have h_no_writes_body : SrcNoGenWrites (P := P) Q body := by
      have h_dv : Stmt.definedVars (P := P) (.loop (.det e) m ([] : List (String × P.Expr)) body md)
          = Block.definedVars body := rfl
      have h_mv : Stmt.modifiedVars (P := P) (.loop (.det e) m ([] : List (String × P.Expr)) body md)
          = Block.modifiedVars body := rfl
      show NoGenSuffix (P := P) Q (Block.definedVars body ++ Block.modifiedVars body)
      rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
    -- The per-iteration body simulation, from the mutual companion.
    have h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
        ρb_tgt.eval = ρb_src.eval →
        ρb_tgt.hasFailure = ρb_src.hasFailure →
        AgreeOffGen Q ρb_src.store ρb_tgt.store →
        WellFormedSemanticEvalBool ρb_src.eval →
        WellFormedSemanticEvalVal ρb_src.eval →
        WellFormedSemanticEvalDef ρb_src.eval →
        WellFormedSemanticEvalExprCongr ρb_src.eval →
        WellFormedSemanticEvalVar ρb_src.eval →
        StringGenState.WF σ →
        (∀ t, Q t →
          ρb_src.store (HasIdent.ident (P := P) t) = none) →
        GenFreshStore Q σ ρb_tgt.store →
        StepStmtStar P (EvalCmd P) extendEval (.stmts body ρb_src) (outcomeConfig oc_b ρb') →
        (∀ t, Q t →
            ρb'.store (HasIdent.ident (P := P) t) = none)
          ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P) extendEval
              (.stmts (Block.nondetElimM body σ).1 ρb_tgt) (outcomeConfig oc_b ρb_out)
            ∧ AgreeOffGen Q ρb'.store ρb_out.store
            ∧ ρb_out.hasFailure = ρb'.hasFailure
            ∧ ρb_out.eval = ρb'.eval
            ∧ GenFreshStore Q (Block.nondetElimM body σ).2 ρb_out.store :=
      fun oc_b ρb_src ρb' ρb_tgt h_ev h_fl h_ag hb hv hd hc hvar hwfg hsf htf hrun =>
        nondetElim_simulation_gen hQmint extendEval body σ ρb_src ρb' ρb_tgt
          h_ev h_fl h_ag hb hv hd hc hvar hwfg hsf htf
          h_no_writes_body h_nofd_body h_lhni_body oc_b hrun
    -- Run the iteration lemma, threading the Type-valued source-run length.
    have hstarT := reflTrans_to_T h_term
    obtain ⟨h_fresh', ρ_out, h_loop_run, h_off', h_fail', h_eval', h_fresh_out⟩ :=
      nondetElim_loop_det_sim_iteration extendEval e m body (Block.nondetElimM body σ).1 md σ
        h_body_sim (Block.nondetElimM body σ).2 h_nofd_body
        oc ρ_src ρ' ρ_tgt hstarT.len
        h_eval_eq h_fail_eq h_agree hwfb hwfv hwf_def hwf_congr hwf_var
        h_wf_gen h_src_fresh h_tgt_fresh hstarT (Nat.le_refl _)
    refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', ?_⟩
    · -- Target output is `[.loop (.det e) m [] (Block.nondetElimM body σ).1 md]`.
      rw [Stmt.nondetElimM_loop_det_out]
      exact stmt_to_singleton_stmts_outcome (extendEval := extendEval) _ ρ_tgt ρ_out oc h_loop_run
    · -- `(Stmt.nondetElimM (.loop …) σ).2 = (Block.nondetElimM body σ).2`; the loop
      -- keeps gen state at `σ`, so mono the freshness up to the advanced state.
      have h_out_eq : (Stmt.nondetElimM (.loop (.det e) m ([] : List (String × P.Expr)) body md) σ).2
          = (Block.nondetElimM body σ).2 := by
        rw [Stmt.nondetElimM]
        rcases hh : Block.nondetElimM body σ with ⟨body', σ'⟩
        simp only [hh]
      rw [h_out_eq]
      exact GenFreshStore.mono (Block.nondetElimM_genStep body σ) h_fresh_out
  | .loop .nondet m inv body md, h_no_writes, h_nofd, h_lhni, oc, h_term =>
    -- The invariant list is empty (`h_lhni`).  The pass emits an `init $g := *`
    -- before a deterministic loop whose guard reads `$g` and whose body tail is a
    -- re-havoc `set $g := *`.  Generate `$g`, init it to the value matching the
    -- source's first enter/exit choice, then run the nondet iteration lemma.
    have h_inv_nil : inv = [] := Stmt.loopHasNoInvariants_loop_invs h_lhni
    subst h_inv_nil
    have h_lhni_body : Block.loopHasNoInvariants body = true :=
      Stmt.loopHasNoInvariants_loop_body_rec h_lhni
    have h_nofd_body : Block.noFuncDecl body = true := by
      simpa only [Stmt.noFuncDecl] using h_nofd
    have h_no_writes_body : SrcNoGenWrites (P := P) Q body := by
      have h_dv : Stmt.definedVars (P := P) (.loop .nondet m ([] : List (String × P.Expr)) body md)
          = Block.definedVars body := rfl
      have h_mv : Stmt.modifiedVars (P := P) (.loop .nondet m ([] : List (String × P.Expr)) body md)
          = Block.modifiedVars body := rfl
      show NoGenSuffix (P := P) Q (Block.definedVars body ++ Block.modifiedVars body)
      rw [h_dv, h_mv] at h_no_writes; exact h_no_writes
    -- Generate the loop guard `$g` and advance the state to σ₁.
    rcases hgen : StringGenState.gen ndelimLoopPrefix σ with ⟨g, σ₁⟩
    have h_g_gen : Q g := by
      have := hQmint.2 σ
      rw [hgen] at this; exact this
    have h_g_in : g ∈ σ₁.stringGens := by
      have h := StringGenState.stringGens_gen ndelimLoopPrefix σ
      rw [hgen] at h; rw [h]; exact List.mem_cons_self
    have h_step01 : StringGenState.GenStep σ σ₁ := by
      have := StringGenState.GenStep.of_gen ndelimLoopPrefix σ; rw [hgen] at this; exact this
    have h_wf₁ : StringGenState.WF σ₁ := h_step01.wf_mono h_wf_gen
    have h_tgt_g_none : ρ_tgt.store (HasIdent.ident (P := P) g) = none := by
      have := GenFreshStore.gen_slot_none ndelimLoopPrefix h_tgt_fresh h_wf_gen (hQmint.2 σ)
      rw [hgen] at this; exact this
    have hwf_var_t : WellFormedSemanticEvalVar ρ_tgt.eval := h_eval_eq ▸ hwf_var
    -- The per-iteration body simulation, from the mutual companion at σ₁.
    have h_body_sim : ∀ (oc_b : Option String) (ρb_src ρb' ρb_tgt : Env P),
        ρb_tgt.eval = ρb_src.eval →
        ρb_tgt.hasFailure = ρb_src.hasFailure →
        AgreeOffGen Q ρb_src.store ρb_tgt.store →
        WellFormedSemanticEvalBool ρb_src.eval →
        WellFormedSemanticEvalVal ρb_src.eval →
        WellFormedSemanticEvalDef ρb_src.eval →
        WellFormedSemanticEvalExprCongr ρb_src.eval →
        WellFormedSemanticEvalVar ρb_src.eval →
        StringGenState.WF σ₁ →
        (∀ t, Q t →
          ρb_src.store (HasIdent.ident (P := P) t) = none) →
        GenFreshStore Q σ₁ ρb_tgt.store →
        StepStmtStar P (EvalCmd P) extendEval (.stmts body ρb_src) (outcomeConfig oc_b ρb') →
        (∀ t, Q t →
            ρb'.store (HasIdent.ident (P := P) t) = none)
          ∧ ∃ ρb_out, StepStmtStar P (EvalCmd P) extendEval
              (.stmts (Block.nondetElimM body σ₁).1 ρb_tgt) (outcomeConfig oc_b ρb_out)
            ∧ AgreeOffGen Q ρb'.store ρb_out.store
            ∧ ρb_out.hasFailure = ρb'.hasFailure
            ∧ ρb_out.eval = ρb'.eval
            ∧ GenFreshStore Q (Block.nondetElimM body σ₁).2 ρb_out.store :=
      fun oc_b ρb_src ρb' ρb_tgt h_ev h_fl h_ag hb hv hd hc hvar hwfg hsf htf hrun =>
        nondetElim_simulation_gen hQmint extendEval body σ₁ ρb_src ρb' ρb_tgt
          h_ev h_fl h_ag hb hv hd hc hvar hwfg hsf htf
          h_no_writes_body h_nofd_body h_lhni_body oc_b hrun
    -- Common tail: from the matched `init`/iteration result, build the full run
    -- (init $g := * then the loop) and discharge the output-freshness conjunct.
    have finish : ∀ (entering : Bool) (b : P.Expr)
        (h_b : b = (if entering then HasBool.tt else HasBool.ff)),
        ((∀ t, Q t →
            ρ'.store (HasIdent.ident (P := P) t) = none)
          ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P) extendEval
              (.stmt (.loop (.det (HasFvar.mkFvar (HasIdent.ident (P := P) g))) m
                ([] : List (String × P.Expr))
                ((Block.nondetElimM body σ₁).1 ++ [.cmd (HasHavoc.havoc (HasIdent.ident (P := P) g) md)]) md)
                ({ ρ_tgt with store := storeWith ρ_tgt.store (HasIdent.ident (P := P) g) b } : Env P))
              (outcomeConfig oc ρ_out)
            ∧ AgreeOffGen Q ρ'.store ρ_out.store
            ∧ ρ_out.hasFailure = ρ'.hasFailure
            ∧ ρ_out.eval = ρ'.eval
            ∧ GenFreshStore Q σ₁ ρ_out.store) →
        (∀ t, Q t →
            ρ'.store (HasIdent.ident (P := P) t) = none)
          ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P) extendEval
              (.stmts (Stmt.nondetElimM (.loop .nondet m ([] : List (String × P.Expr)) body md) σ).1 ρ_tgt)
              (outcomeConfig oc ρ_out)
            ∧ AgreeOffGen Q ρ'.store ρ_out.store
            ∧ ρ_out.hasFailure = ρ'.hasFailure
            ∧ ρ_out.eval = ρ'.eval
            ∧ GenFreshStore Q (Stmt.nondetElimM (.loop .nondet m ([] : List (String × P.Expr)) body md) σ).2 ρ_out.store := by
      intro entering b h_b ⟨h_fresh', ρ_out, h_loop_run, h_off', h_fail', h_eval', h_fresh_out⟩
      refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', ?_⟩
      · rw [Stmt.nondetElimM_loop_nondet_out]
        simp only [hgen]
        -- Prepend the `init $g := b` step, then the loop run.
        have h_init : StepStmtStar P (EvalCmd P) extendEval
            (.stmt (.cmd (HasInit.init (HasIdent.ident (P := P) g) HasBool.boolTy .nondet md)) ρ_tgt)
            (.terminal ({ ρ_tgt with store := storeWith ρ_tgt.store (HasIdent.ident (P := P) g) b } : Env P)) :=
          step_init_havoc_to (extendEval := extendEval) (HasIdent.ident (P := P) g) HasBool.boolTy b md ρ_tgt
            h_tgt_g_none hwf_var_t
        refine ReflTrans_Transitive _ _ _ _
          (stmts_cons_step P (EvalCmd P) extendEval _ _ ρ_tgt _ h_init) ?_
        exact stmt_to_singleton_stmts_outcome (extendEval := extendEval) _ _ ρ_out oc h_loop_run
      · -- Output gen state = (Block.nondetElimM body σ₁).2 ⊇ σ₁; mono.
        have h_out_eq2 : (Stmt.nondetElimM (.loop .nondet m ([] : List (String × P.Expr)) body md) σ).2
            = (Block.nondetElimM body σ₁).2 := by
          rw [Stmt.nondetElimM]
          rcases hh : Block.nondetElimM body σ₁ with ⟨body', σ₂⟩
          simp only [hgen, hh]
        rw [h_out_eq2]
        exact GenFreshStore.mono (Block.nondetElimM_genStep body σ₁) h_fresh_out
    -- Invert the source loop's first step to pick the matched guard value.
    have hstarT := reflTrans_to_T h_term
    rcases loop_nondet_step_first_inv (extendEval := extendEval) hstarT with
      ⟨hrest, hl⟩ | ⟨hrest, hl⟩
    · -- EXIT first: init $g := ff, entering = false.
      have h_off_g : AgreeOffGen Q ρ_src.store
          (storeWith ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) :=
        AgreeOffGen.storeWith_gen h_agree h_g_gen
      have h_fresh_g : GenFreshStore Q σ₁
          (storeWith ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff) := by
        have := GenFreshStore.storeWith_gen (P := P) ndelimLoopPrefix HasBool.ff h_tgt_fresh
        rw [hgen] at this; exact this
      have h_guard_def : (({ ρ_tgt with store := storeWith ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff } : Env P).store)
          (HasIdent.ident (P := P) g) = some (if false then HasBool.tt else HasBool.ff) := by
        simp [storeWith]
      exact finish false HasBool.ff (by simp)
        (nondetElim_loop_nondet_sim_iteration extendEval g m body (Block.nondetElimM body σ₁).1 md σ₁ (Block.nondetElimM body σ₁).2
          h_body_sim h_g_gen h_g_in h_nofd_body oc ρ_src ρ'
          ({ ρ_tgt with store := storeWith ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.ff } : Env P)
          hstarT.len h_eval_eq h_fail_eq h_off_g hwfb hwfv hwf_def hwf_congr hwf_var
          h_wf₁ h_src_fresh h_fresh_g false h_guard_def
          (.inl ⟨rfl, hrest, Nat.le_of_lt hl⟩))
    · -- ENTER first: init $g := tt, entering = true.
      have h_off_g : AgreeOffGen Q ρ_src.store
          (storeWith ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) :=
        AgreeOffGen.storeWith_gen h_agree h_g_gen
      have h_fresh_g : GenFreshStore Q σ₁
          (storeWith ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt) := by
        have := GenFreshStore.storeWith_gen (P := P) ndelimLoopPrefix HasBool.tt h_tgt_fresh
        rw [hgen] at this; exact this
      have h_guard_def : (({ ρ_tgt with store := storeWith ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P).store)
          (HasIdent.ident (P := P) g) = some (if true then HasBool.tt else HasBool.ff) := by
        simp [storeWith]
      exact finish true HasBool.tt (by simp)
        (nondetElim_loop_nondet_sim_iteration extendEval g m body (Block.nondetElimM body σ₁).1 md σ₁ (Block.nondetElimM body σ₁).2
          h_body_sim h_g_gen h_g_in h_nofd_body oc ρ_src ρ'
          ({ ρ_tgt with store := storeWith ρ_tgt.store (HasIdent.ident (P := P) g) HasBool.tt } : Env P)
          hstarT.len h_eval_eq h_fail_eq h_off_g hwfb hwfv hwf_def hwf_congr hwf_var
          h_wf₁ h_src_fresh h_fresh_g true h_guard_def
          (.inr ⟨rfl, hrest, Nat.le_of_lt hl⟩))
  | .exit lbl md, _, _, _, oc, h_term =>
    -- `.exit lbl` steps to `.exiting lbl ρ_src`: vacuous on `.terminal`, and on
    -- the exiting outcome the label/env are forced and the rewritten `[.exit lbl]`
    -- mirrors the step.
    cases oc with
    | none =>
      exfalso
      simp only [outcomeConfig] at h_term
      obtain ⟨c, hstep, hrest⟩ := stmt_step_first_inv (extendEval := extendEval) _ ρ_src ρ' h_term
      cases hstep
      -- `hrest : .exiting lbl ρ_src →* .terminal ρ'` is impossible.
      cases hrest with
      | step _ _ _ h _ => cases h
    | some lbl' =>
      simp only [outcomeConfig] at h_term
      obtain ⟨c, hstep, hrest⟩ :=
        stmt_step_first_inv_to (extendEval := extendEval) _ ρ_src (.exiting lbl' ρ')
          (by intro ρ'' h; cases h) h_term
      cases hstep
      -- `.exiting lbl ρ_src →* .exiting lbl' ρ'` forces `lbl' = lbl` and `ρ' = ρ_src`.
      have h_eq : lbl' = lbl ∧ ρ' = ρ_src := by
        cases hrest with
        | refl => exact ⟨rfl, rfl⟩
        | step _ _ _ h _ => cases h
      obtain ⟨h_lbl_eq, h_ρ_eq⟩ := h_eq
      subst h_lbl_eq; subst h_ρ_eq
      refine ⟨h_src_fresh, ρ_tgt, ?_, h_agree, h_fail_eq, h_eval_eq, ?_⟩
      · simp only [Stmt.nondetElimM, outcomeConfig]
        exact stmt_to_singleton_stmts_exiting (extendEval := extendEval) (.exit lbl' md) ρ_tgt ρ_tgt lbl'
          (.step _ _ _ StepStmt.step_exit (.refl _))
      · simp only [Stmt.nondetElimM]; exact h_tgt_fresh
  | .funcDecl d md, _, h_nofd, _, _, _ =>
    exact absurd h_nofd (by simp [Stmt.noFuncDecl])
  | .typeDecl t md, _, _, _, oc, h_term =>
    -- `.typeDecl` is a runtime no-op: it steps to `.terminal ρ_src`; exiting vacuous.
    cases oc with
    | none =>
      simp only [outcomeConfig] at h_term
      obtain ⟨c, hstep, hrest⟩ := stmt_step_first_inv (extendEval := extendEval) _ ρ_src ρ' h_term
      cases hstep
      have h_eq : ρ_src = ρ' := by
        cases hrest with
        | refl => rfl
        | step _ _ _ h _ => cases h
      subst h_eq
      refine ⟨h_src_fresh, ρ_tgt, ?_, h_agree, h_fail_eq, h_eval_eq, ?_⟩
      · simp only [Stmt.nondetElimM, outcomeConfig]
        exact stmt_to_singleton_stmts (extendEval := extendEval) (.typeDecl t md) ρ_tgt ρ_tgt
          (.step _ _ _ StepStmt.step_typeDecl (.refl _))
      · simp only [Stmt.nondetElimM]; exact h_tgt_fresh
    | some lbl =>
      exfalso
      simp only [outcomeConfig] at h_term
      obtain ⟨c, hstep, hrest⟩ :=
        stmt_step_first_inv_to (extendEval := extendEval) _ ρ_src (.exiting lbl ρ')
          (by intro ρ'' h; cases h) h_term
      cases hstep
      -- `.terminal ρ_src →* .exiting lbl ρ'` impossible.
      cases hrest with
      | step _ _ _ h _ => cases h
  termination_by sizeOf s

/-- General forward simulation over a statement list with separate source/target
start stores and threaded generator state.  See spec §4. -/
private theorem nondetElim_simulation_gen {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasBool P] [LawfulHasIdent P]
    [LawfulHasIntOrder P] [LawfulHasNot P]
    {Q : String → Prop}
    (hQmint : (∀ sg, Q (StringGenState.gen ndelimItePrefix sg).1)
            ∧ (∀ sg, Q (StringGenState.gen ndelimLoopPrefix sg).1))
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (ρ_src ρ' ρ_tgt : Env P)
    (h_eval_eq : ρ_tgt.eval = ρ_src.eval)
    (h_fail_eq : ρ_tgt.hasFailure = ρ_src.hasFailure)
    (h_agree : AgreeOffGen Q ρ_src.store ρ_tgt.store)
    (hwfb : WellFormedSemanticEvalBool ρ_src.eval)
    (hwfv : WellFormedSemanticEvalVal ρ_src.eval)
    (hwf_def : WellFormedSemanticEvalDef ρ_src.eval)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ_src.eval)
    (hwf_var : WellFormedSemanticEvalVar ρ_src.eval)
    (h_wf_gen : StringGenState.WF σ)
    (h_src_fresh : ∀ t, Q t →
      ρ_src.store (HasIdent.ident (P := P) t) = none)
    (h_tgt_fresh : GenFreshStore Q σ ρ_tgt.store)
    (h_no_writes : SrcNoGenWrites (P := P) Q ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_lhni : Block.loopHasNoInvariants ss = true)
    (oc : Option String)
    (h_term : StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ_src) (outcomeConfig oc ρ')) :
    (∀ t, Q t →
        ρ'.store (HasIdent.ident (P := P) t) = none)
      ∧ ∃ ρ_out, StepStmtStar P (EvalCmd P) extendEval
          (.stmts (Block.nondetElimM ss σ).1 ρ_tgt) (outcomeConfig oc ρ_out)
        ∧ AgreeOffGen Q ρ'.store ρ_out.store
        ∧ ρ_out.hasFailure = ρ'.hasFailure
        ∧ ρ_out.eval = ρ'.eval
        ∧ GenFreshStore Q (Block.nondetElimM ss σ).2 ρ_out.store := by
  match ss, h_no_writes, h_nofd, oc, h_term with
  | [], _, _, oc, h_term =>
    -- An empty list only reaches `.terminal`; the exiting outcome is vacuous.
    match oc, h_term with
    | none, h_term =>
      have h_eq : ρ_src = ρ' := stmts_nil_terminal_eq (extendEval := extendEval) ρ_src ρ' h_term
      subst h_eq
      refine ⟨h_src_fresh, ρ_tgt, ?_, h_agree, h_fail_eq, h_eval_eq, ?_⟩
      · simp only [Block.nondetElimM, outcomeConfig]
        exact evalStmtsSmallNil P (EvalCmd P) extendEval ρ_tgt
      · simp only [Block.nondetElimM]; exact h_tgt_fresh
    | some lbl, h_term =>
      exfalso
      -- `.stmts [] ρ_src` steps to `.terminal ρ_src`, never `.exiting`.
      simp only [outcomeConfig] at h_term
      cases h_term with
      | step _ _ _ h h2 =>
        cases h with
        | step_stmts_nil =>
          cases h2 with
          | step _ _ _ h3 _ => cases h3
  | s :: rest, h_no_writes, h_nofd, oc, h_term =>
    -- Decompose the source run: either the head `s` exits (skipping `rest`), or
    -- `s` terminates to `ρ_mid` then `rest` reaches the same outcome.
    rcases stmts_cons_outcome (extendEval := extendEval) s rest ρ_src ρ' oc h_term with
      ⟨lbl, h_oc_eq, h_s_exit⟩ | ⟨ρ_mid, h_s_run, h_rest_run⟩
    · -- Head exits: recurse on `s` with the exiting outcome, then `step_seq_exit`
      -- past the (rewritten) `rest`.
      subst h_oc_eq
      -- Source-shape split for `s` (head of the cons).
      have h_no_writes_s_e : NoGenSuffix (P := P) Q (Stmt.definedVars s ++ Stmt.modifiedVars s) := by
        intro x hx t heq
        rcases List.mem_append.mp hx with hd | hm
        · exact h_no_writes x (List.mem_append_left _ (List.mem_append_left _ hd)) t heq
        · exact h_no_writes x (List.mem_append_right _ (List.mem_append_left _ hm)) t heq
      have h_nofd_pair_e : Stmt.noFuncDecl s = true ∧ Block.noFuncDecl rest = true := by
        have : (Stmt.noFuncDecl s && Block.noFuncDecl rest) = true := by
          simpa only [Block.noFuncDecl] using h_nofd
        exact Bool.and_eq_true _ _ |>.mp this
      have h_lhni_pair_e : Stmt.loopHasNoInvariants s = true ∧
          Block.loopHasNoInvariants rest = true :=
        Block.loopHasNoInvariants_cons_iff.mp h_lhni
      obtain ⟨h_fresh', ρ_out, h_s_tgt, h_off', h_fail', h_eval', h_fresh_s⟩ :=
        nondetElim_stmt_gen hQmint extendEval s σ ρ_src ρ' ρ_tgt
          h_eval_eq h_fail_eq h_agree hwfb hwfv hwf_def hwf_congr hwf_var
          h_wf_gen h_src_fresh h_tgt_fresh h_no_writes_s_e h_nofd_pair_e.1 h_lhni_pair_e.1
          (some lbl) h_s_exit
      refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', ?_⟩
      · rw [Block.nondetElimM_cons_out]
        -- The rewritten head exits; `step_seq_exit` past the rewritten tail.
        refine stmts_cons_head_exiting_append (extendEval := extendEval) _ _ ρ_tgt ρ_out lbl ?_
        simpa only [outcomeConfig] using h_s_tgt
      · -- GenFreshStore Q at `(Block.nondetElimM (s :: rest) σ).2 ⊇ (Stmt.nondetElimM s σ).2`.
        have h_out_eq : (Block.nondetElimM (s :: rest) σ).2
            = (Block.nondetElimM rest (Stmt.nondetElimM s σ).2).2 := by
          rw [Block.nondetElimM]
          rcases hh : Stmt.nondetElimM s σ with ⟨ss_s, σ_s⟩
          rcases hk : Block.nondetElimM rest σ_s with ⟨ss_r, σ_r⟩
          simp only [hh, hk]
        rw [h_out_eq]
        exact GenFreshStore.mono (Block.nondetElimM_genStep rest (Stmt.nondetElimM s σ).2) h_fresh_s
    · -- Head terminates: original sequencing argument, now threading the outcome.
      have h_s_run' : StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ_src) (.terminal ρ_mid) :=
        h_s_run
      -- Source-shape splits.
      have h_no_writes_s : NoGenSuffix (P := P) Q (Stmt.definedVars s ++ Stmt.modifiedVars s) := by
        intro x hx t heq
        rcases List.mem_append.mp hx with hd | hm
        · exact h_no_writes x (List.mem_append_left _ (List.mem_append_left _ hd)) t heq
        · exact h_no_writes x (List.mem_append_right _ (List.mem_append_left _ hm)) t heq
      have h_no_writes_rest : SrcNoGenWrites (P := P) Q rest := by
        intro x hx t heq
        rcases List.mem_append.mp hx with hd | hm
        · exact h_no_writes x (List.mem_append_left _ (List.mem_append_right _ hd)) t heq
        · exact h_no_writes x (List.mem_append_right _ (List.mem_append_right _ hm)) t heq
      have h_nofd_pair : Stmt.noFuncDecl s = true ∧ Block.noFuncDecl rest = true := by
        have : (Stmt.noFuncDecl s && Block.noFuncDecl rest) = true := by
          simpa only [Block.noFuncDecl] using h_nofd
        exact Bool.and_eq_true _ _ |>.mp this
      have h_nofd_s : Stmt.noFuncDecl s = true := h_nofd_pair.1
      have h_nofd_rest : Block.noFuncDecl rest = true := h_nofd_pair.2
      have h_lhni_pair : Stmt.loopHasNoInvariants s = true ∧ Block.loopHasNoInvariants rest = true :=
        Block.loopHasNoInvariants_cons_iff.mp h_lhni
      have h_lhni_s : Stmt.loopHasNoInvariants s = true := h_lhni_pair.1
      have h_lhni_rest : Block.loopHasNoInvariants rest = true := h_lhni_pair.2
      -- Simulate `s` (to terminal).
      obtain ⟨h_mid_fresh, ρ_mid_tgt, h_s_tgt, h_off_mid, h_fail_mid, h_eval_mid, h_fresh_mid⟩ :=
        nondetElim_stmt_gen hQmint extendEval s σ ρ_src ρ_mid ρ_tgt
          h_eval_eq h_fail_eq h_agree hwfb hwfv hwf_def hwf_congr hwf_var
          h_wf_gen h_src_fresh h_tgt_fresh h_no_writes_s h_nofd_s h_lhni_s none h_s_run'
      -- Advance the generator: σ₁ := (Stmt.nondetElimM s σ).2.
      have h_step_s : StringGenState.GenStep σ (Stmt.nondetElimM s σ).2 :=
        Stmt.nondetElimM_genStep s σ
      have h_wf₁ : StringGenState.WF (Stmt.nondetElimM s σ).2 := h_step_s.wf_mono h_wf_gen
      -- Source eval is preserved across a single (funcDecl-free) statement.
      have h_eval_mid_src : ρ_mid.eval = ρ_src.eval :=
        smallStep_noFuncDecl_preserves_eval P (EvalCmd P) extendEval s ρ_src ρ_mid h_nofd_s h_s_run'
      have hwfb_mid : WellFormedSemanticEvalBool ρ_mid.eval := h_eval_mid_src ▸ hwfb
      have hwfv_mid : WellFormedSemanticEvalVal ρ_mid.eval := h_eval_mid_src ▸ hwfv
      have hwf_def_mid : WellFormedSemanticEvalDef ρ_mid.eval := h_eval_mid_src ▸ hwf_def
      have hwf_congr_mid : WellFormedSemanticEvalExprCongr ρ_mid.eval := h_eval_mid_src ▸ hwf_congr
      have hwf_var_mid : WellFormedSemanticEvalVar ρ_mid.eval := h_eval_mid_src ▸ hwf_var
      -- IH on `rest` at the advanced state from ρ_mid (src) and ρ_mid_tgt (tgt).
      have h_eval_eq' : ρ_mid_tgt.eval = ρ_mid.eval := h_eval_mid
      have h_fail_eq' : ρ_mid_tgt.hasFailure = ρ_mid.hasFailure := h_fail_mid
      obtain ⟨h_fresh', ρ_out, h_rest_tgt, h_off', h_fail', h_eval', h_fresh_out⟩ :=
        nondetElim_simulation_gen hQmint extendEval rest (Stmt.nondetElimM s σ).2 ρ_mid ρ' ρ_mid_tgt
          h_eval_eq' h_fail_eq' h_off_mid hwfb_mid hwfv_mid hwf_def_mid hwf_congr_mid hwf_var_mid
          h_wf₁ h_mid_fresh h_fresh_mid h_no_writes_rest h_nofd_rest h_lhni_rest oc h_rest_run
      -- Assemble: output = (Stmt.nondetElimM s σ).1 ++ (Block.nondetElimM rest (…).2).1.
      refine ⟨h_fresh', ρ_out, ?_, h_off', h_fail', h_eval', ?_⟩
      · rw [Block.nondetElimM_cons_out]
        exact ReflTrans_Transitive _ _ _ _
          (stmts_prefix_terminal_append P (EvalCmd P) extendEval _ _ ρ_tgt ρ_mid_tgt h_s_tgt)
          h_rest_tgt
      · -- GenFreshStore at (Block.nondetElimM (s::rest) σ).2.
        have h_out_eq : (Block.nondetElimM (s :: rest) σ).2
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
generated guard variables. See spec §4.

This is the substantive simulation lemma; `nondetElim_sound` is its top-level
corollary.  It instantiates `nondetElim_simulation_gen` at `ρ_tgt = ρ_src` and
the empty generator state. -/
private theorem nondetElim_simulation {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasBool P] [LawfulHasIdent P]
    [LawfulHasIntOrder P] [LawfulHasNot P]
    {Q : String → Prop}
    (hQmint : (∀ sg, Q (StringGenState.gen ndelimItePrefix sg).1)
            ∧ (∀ sg, Q (StringGenState.gen ndelimLoopPrefix sg).1))
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwf_def : WellFormedSemanticEvalDef ρ₀.eval)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (hwf_var : WellFormedSemanticEvalVar ρ₀.eval)
    (h_no_gen_suffix :
      ∀ s, Q s →
        ρ₀.store (HasIdent.ident (P := P) s) = none)
    (h_no_writes : SrcNoGenWrites (P := P) Q ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_lhni : Block.loopHasNoInvariants ss = true)
    (h_term : StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) (.terminal ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P) extendEval
        (.stmts (Block.nondetElim ss) ρ₀) (.terminal ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure := by
  have h_tgt_fresh : GenFreshStore Q StringGenState.emp ρ₀.store := by
    intro s h_suf _; exact h_no_gen_suffix s h_suf
  obtain ⟨h_fresh', ρ_out, h_run, h_off, h_fl, _, _⟩ :=
    nondetElim_simulation_gen hQmint extendEval ss StringGenState.emp ρ₀ ρ' ρ₀
      rfl rfl (AgreeOffGen.refl _) hwfb hwfv hwf_def hwf_congr hwf_var
      StringGenState.wf_emp h_no_gen_suffix h_tgt_fresh h_no_writes h_nofd h_lhni
      none h_term
  exact ⟨ρ_out, h_run, StoreAgreement.of_agreeOffGen h_off h_fresh', h_fl⟩

/-- Escaping sibling of `nondetElim_simulation`: surfaces the banked exiting
disjunct of `nondetElim_simulation_gen`.  Every *escaping* source run of `ss`
(reaching `.exiting lbl ρ'`) is matched by an escaping run of `Block.nondetElim ss`
to the *same* label, agreeing on the source's variables and the failure flag.
Identical to the terminal `nondetElim_simulation` except it instantiates the
outcome selector at `some lbl`. -/
private theorem nondetElim_simulation_exit {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasBool P] [LawfulHasIdent P]
    [LawfulHasIntOrder P] [LawfulHasNot P]
    {Q : String → Prop}
    (hQmint : (∀ sg, Q (StringGenState.gen ndelimItePrefix sg).1)
            ∧ (∀ sg, Q (StringGenState.gen ndelimLoopPrefix sg).1))
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwf_def : WellFormedSemanticEvalDef ρ₀.eval)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (hwf_var : WellFormedSemanticEvalVar ρ₀.eval)
    (h_no_gen_suffix :
      ∀ s, Q s →
        ρ₀.store (HasIdent.ident (P := P) s) = none)
    (h_no_writes : SrcNoGenWrites (P := P) Q ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_lhni : Block.loopHasNoInvariants ss = true)
    (lbl : String)
    (h_exit : StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) (.exiting lbl ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P) extendEval
        (.stmts (Block.nondetElim ss) ρ₀) (.exiting lbl ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure := by
  have h_tgt_fresh : GenFreshStore Q StringGenState.emp ρ₀.store := by
    intro s h_suf _; exact h_no_gen_suffix s h_suf
  obtain ⟨h_fresh', ρ_out, h_run, h_off, h_fl, _, _⟩ :=
    nondetElim_simulation_gen hQmint extendEval ss StringGenState.emp ρ₀ ρ' ρ₀
      rfl rfl (AgreeOffGen.refl _) hwfb hwfv hwf_def hwf_congr hwf_var
      StringGenState.wf_emp h_no_gen_suffix h_tgt_fresh h_no_writes h_nofd h_lhni
      (some lbl) (by simpa only [outcomeConfig] using h_exit)
  refine ⟨ρ_out, ?_, StoreAgreement.of_agreeOffGen h_off h_fresh', h_fl⟩
  simpa only [outcomeConfig] using h_run

/-- Forward simulation: every terminating source execution of `ss` has a
matching execution of `Block.nondetElim ss` agreeing on the source's variables
(`StoreAgreement`) and the failure flag. The existential picks each guard's
havoc value to match the source's nondeterministic choice; `StoreAgreement`'s
one-directionality hides the generated guard variables.

The instance and well-formed-eval hypothesis list mirrors
`structuredToUnstructured_sound_kind`
(`Strata/Transform/StructuredToUnstructuredCorrect.lean`) exactly, so this
theorem composes with that proof downstream. See spec §4. -/
theorem nondetElim_sound {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasBool P] [LawfulHasIdent P]
    [LawfulHasIntOrder P] [LawfulHasNot P]
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwf_def : WellFormedSemanticEvalDef ρ₀.eval)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (hwf_var : WellFormedSemanticEvalVar ρ₀.eval)
    (h_no_gen_suffix :
      ∀ s, String.HasUnderscoreDigitSuffix s →
        ρ₀.store (HasIdent.ident (P := P) s) = none)
    (h_no_writes : SrcNoGenWrites (P := P) String.HasUnderscoreDigitSuffix ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_lhni : Block.loopHasNoInvariants ss = true)
    (h_term : StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) (.terminal ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P) extendEval
        (.stmts (Block.nondetElim ss) ρ₀) (.terminal ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure :=
  nondetElim_simulation
    (Q := String.HasUnderscoreDigitSuffix)
    ⟨fun sg => StringGenState.gen_hasUnderscoreDigitSuffix ndelimItePrefix sg,
     fun sg => StringGenState.gen_hasUnderscoreDigitSuffix ndelimLoopPrefix sg⟩
    extendEval ss ρ₀ ρ'
    hwfb hwfv hwf_def hwf_congr hwf_var h_no_gen_suffix h_no_writes h_nofd h_lhni h_term

/-! ### The nondetElim label *kind*

`nondetElim` mints labels under exactly two prefixes: `ndelimItePrefix` and
`ndelimLoopPrefix`.  `ndelimKind s` is the precise predicate "`s` is a label this
pass could have minted": it carries the matching generator prefix and is equal to
some `gen`-output.  This is the per-kind `Q` to instantiate the kind-generalized
simulation at, replacing the blanket `HasUnderscoreDigitSuffix` (which would
overcommit a composition partner to keeping *every* gen-shaped name fresh). -/

/-- A label that `nondetElim` could have minted: it has the ite- or loop-prefix
and equals a corresponding `gen` output. -/
@[expose] def ndelimKind (s : String) : Prop :=
  (∃ sg, String.HasGenPrefix ndelimItePrefix s
      ∧ s = (StringGenState.gen ndelimItePrefix sg).1)
  ∨ (∃ sg, String.HasGenPrefix ndelimLoopPrefix s
      ∧ s = (StringGenState.gen ndelimLoopPrefix sg).1)

/-- The two prefixes `nondetElim` mints under both land inside `ndelimKind`:
this is exactly the `hQmint` conjunction at `Q := ndelimKind`. -/
theorem ndelimKind_gen :
    (∀ sg, ndelimKind (StringGenState.gen ndelimItePrefix sg).1)
  ∧ (∀ sg, ndelimKind (StringGenState.gen ndelimLoopPrefix sg).1) := by
  refine ⟨fun sg => ?_, fun sg => ?_⟩
  · exact Or.inl ⟨sg, StringGenState.gen_hasGenPrefix ndelimItePrefix sg, rfl⟩
  · exact Or.inr ⟨sg, StringGenState.gen_hasGenPrefix ndelimLoopPrefix sg, rfl⟩

/-- Kind-generalized soundness: `nondetElim` is sound for any source store whose
only `ndelimKind`-labelled slots are undefined, and any source block that never
writes an `ndelimKind` label.  Weaker entry precondition than `nondetElim_sound`
(it constrains only the labels this pass mints, not every gen-shaped name),
which is what lets a composition partner — e.g. one that mints under a disjoint
prefix — satisfy it vacuously. -/
theorem nondetElim_sound_kind {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasBool P] [LawfulHasIdent P]
    [LawfulHasIntOrder P] [LawfulHasNot P]
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwf_def : WellFormedSemanticEvalDef ρ₀.eval)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (hwf_var : WellFormedSemanticEvalVar ρ₀.eval)
    (h_no_gen_suffix : NoGenStore (P := P) ndelimKind ρ₀)
    (h_no_writes : SrcNoGenWrites (P := P) ndelimKind ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_lhni : Block.loopHasNoInvariants ss = true)
    (h_term : StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) (.terminal ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P) extendEval
        (.stmts (Block.nondetElim ss) ρ₀) (.terminal ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure :=
  nondetElim_simulation
    (Q := ndelimKind) ndelimKind_gen
    extendEval ss ρ₀ ρ'
    hwfb hwfv hwf_def hwf_congr hwf_var h_no_gen_suffix h_no_writes h_nofd h_lhni h_term

/-- Escaping companion of `nondetElim_sound_kind` (at `Q := ndelimKind`): every
escaping source run of `ss` reaching `.exiting lbl` is matched by an escaping run
of `Block.nondetElim ss` to the *same* label, agreeing on the source's variables
and the failure flag.  A thin forwarder to `nondetElim_simulation_exit`; the
`NoGenStore` store precondition unfolds to the explicit per-kind freshness fact
the simulation consumes. -/
theorem nondetElim_sound_kind_exit {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasBool P] [LawfulHasIdent P]
    [LawfulHasIntOrder P] [LawfulHasNot P]
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwf_def : WellFormedSemanticEvalDef ρ₀.eval)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (hwf_var : WellFormedSemanticEvalVar ρ₀.eval)
    (h_no_gen_suffix : NoGenStore (P := P) ndelimKind ρ₀)
    (h_no_writes : SrcNoGenWrites (P := P) ndelimKind ss)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_lhni : Block.loopHasNoInvariants ss = true)
    (lbl : String)
    (h_exit : StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) (.exiting lbl ρ')) :
    ∃ ρ_out, StepStmtStar P (EvalCmd P) extendEval
        (.stmts (Block.nondetElim ss) ρ₀) (.exiting lbl ρ_out)
      ∧ StoreAgreement ρ'.store ρ_out.store
      ∧ ρ_out.hasFailure = ρ'.hasFailure :=
  nondetElim_simulation_exit
    (Q := ndelimKind) ndelimKind_gen
    extendEval ss ρ₀ ρ'
    hwfb hwfv hwf_def hwf_congr hwf_var h_no_gen_suffix h_no_writes h_nofd h_lhni lbl h_exit

end Imperative
