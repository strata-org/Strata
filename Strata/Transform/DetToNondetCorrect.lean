/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.StmtSemanticsSmallStep
public import Strata.DL.Imperative.NondetStmt
public import Strata.DL.Imperative.NondetStmtSemantics
public import Strata.Transform.DetToNondet
public import Strata.Transform.Specification
import all Strata.Transform.Specification
import all Strata.Transform.DetToNondet
import all Strata.DL.Imperative.CmdSemantics

/-! # Deterministic-to-Nondeterministic Transformation Correctness (Small-Step) -/

public section

open Imperative Specification

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]

/-! ## Lang instances -/

abbrev Lang.det (extendEval : ExtendEval P) : Lang P :=
  Lang.imperative P (Cmd P) (EvalCmd P) extendEval (isAtAssert P)

def isAtNondetAssert : NondetConfig P (Cmd P) → AssertId P → Prop
  | .stmt (.cmd (.assert label expr _)) _, a => a.label = label ∧ a.expr = expr
  | .seq inner _, a => isAtNondetAssert inner a
  | _, _ => False

abbrev Lang.nondet : Lang P where
  StmtT := NondetStmt P (Cmd P)
  CfgT := NondetConfig P (Cmd P)
  star := StepNondetStar P (EvalCmd P)
  stmtCfg := .stmt
  stmtsCfg := fun ss ρ => match ss with
    | [] => .terminal ρ
    | s :: _ => .stmt (ss.foldl (init := s) fun acc s' => .seq acc s') ρ
  terminalCfg := .terminal
  exitingCfg := fun _ ρ => .terminal ρ
  isAtAssert := isAtNondetAssert
  getEval := NondetConfig.getEval
  getStore := NondetConfig.getStore

/-! ## Nondet small-step helpers -/

theorem nondet_seq_inner_star
    (inner inner' : NondetConfig P (Cmd P)) (s2 : NondetStmt P (Cmd P))
    (h : StepNondetStar P (EvalCmd P) inner inner') :
    StepNondetStar P (EvalCmd P) (.seq inner s2) (.seq inner' s2) := by
  induction h with
  | refl => exact .refl _
  | step _ mid _ hstep _ ih => exact .step _ _ _ (.step_seq_inner hstep) ih

theorem nondet_seq_terminal
    (s1 s2 : NondetStmt P (Cmd P)) (ρ ρ₁ ρ' : Env P)
    (h1 : StepNondetStar P (EvalCmd P) (.stmt s1 ρ) (.terminal ρ₁))
    (h2 : StepNondetStar P (EvalCmd P) (.stmt s2 ρ₁) (.terminal ρ')) :
    StepNondetStar P (EvalCmd P) (.stmt (.seq s1 s2) ρ) (.terminal ρ') :=
  .step _ _ _ .step_seq (reflTrans_trans
    (reflTrans_trans (nondet_seq_inner_star _ _ s2 h1)
      (.step _ _ _ .step_seq_done (.refl _))) h2)

private theorem assume_env_eq (ρ : Env P) :
    ({ ρ with store := ρ.store, hasFailure := ρ.hasFailure || false } : Env P) = ρ := by
  cases ρ; simp [Bool.or_false]

/-! ## exitsCoveredByBlocks from successful transform -/

private theorem stmtToNondet_some_exitsCovered
    (labels : List String)
    (st : Stmt P (Cmd P)) (ns : NondetStmt P (Cmd P))
    (ht : StmtToNondetStmt st = some ns) :
    Stmt.exitsCoveredByBlocks (P := P) (CmdT := Cmd P) labels st := by
  match st with
  | .cmd _ => simp [Stmt.exitsCoveredByBlocks]
  | .block l bss _ =>
    simp [Stmt.exitsCoveredByBlocks]; rw [StmtToNondetStmt.eq_2] at ht
    exact blockHelper (l :: labels) bss ns ht
  | .ite _ tss ess _ =>
    rw [StmtToNondetStmt.eq_3] at ht; simp [bind, Option.bind] at ht
    simp [Stmt.exitsCoveredByBlocks]
    match ht_t : BlockToNondetStmt tss, ht_e : BlockToNondetStmt ess with
    | some t, some e => exact ⟨blockHelper labels tss t ht_t, blockHelper labels ess e ht_e⟩
    | some _, none => simp [ht_t, ht_e] at ht
    | none, _ => simp [ht_t] at ht
  | .loop _ _ _ _ _ => simp [StmtToNondetStmt.eq_4] at ht
  | .typeDecl _ _ => simp [StmtToNondetStmt.eq_5] at ht
  | .exit _ _ => simp [StmtToNondetStmt.eq_6] at ht
  | .funcDecl _ _ => simp [StmtToNondetStmt.eq_7] at ht
where
  blockHelper (labels : List String) (bss : List (Stmt P (Cmd P))) (ns : NondetStmt P (Cmd P))
      (ht : BlockToNondetStmt bss = some ns) :
      Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks (P := P) (CmdT := Cmd P) labels bss := by
    match bss with
    | [] => simp [Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks]
    | s :: rest =>
      rw [BlockToNondetStmt.eq_2] at ht; simp [bind, Option.bind] at ht
      match hs : StmtToNondetStmt s, hr : BlockToNondetStmt rest with
      | some s', some r' =>
        simp [Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks]
        exact ⟨stmtToNondet_some_exitsCovered labels s s' hs, blockHelper labels rest r' hr⟩
      | some _, none => simp [hs, hr] at ht
      | none, _ => simp [hs] at ht

/-! ## noFuncDecl from successful transform -/

private theorem stmtToNondet_some_noFuncDecl
    (st : Stmt P (Cmd P)) (ns : NondetStmt P (Cmd P))
    (ht : StmtToNondetStmt st = some ns) :
    Stmt.noFuncDecl st = true := by
  match st with
  | .cmd _ => simp [Stmt.noFuncDecl]
  | .block _ bss _ =>
    simp [Stmt.noFuncDecl]; rw [StmtToNondetStmt.eq_2] at ht
    exact blockHelper bss ns ht
  | .ite _ tss ess _ =>
    rw [StmtToNondetStmt.eq_3] at ht; simp [bind, Option.bind] at ht
    simp [Stmt.noFuncDecl]
    match ht_t : BlockToNondetStmt tss, ht_e : BlockToNondetStmt ess with
    | some t, some e => exact ⟨blockHelper tss t ht_t, blockHelper ess e ht_e⟩
    | some _, none => simp [ht_t, ht_e] at ht
    | none, _ => simp [ht_t] at ht
  | .loop _ _ _ _ _ => simp [StmtToNondetStmt.eq_4] at ht
  | .typeDecl _ _ => simp [StmtToNondetStmt.eq_5] at ht
  | .exit _ _ => simp [StmtToNondetStmt.eq_6] at ht
  | .funcDecl _ _ => simp [StmtToNondetStmt.eq_7] at ht
where
  blockHelper (bss : List (Stmt P (Cmd P))) (ns : NondetStmt P (Cmd P))
      (ht : BlockToNondetStmt bss = some ns) :
      Block.noFuncDecl bss = true := by
    match bss with
    | [] => simp [Block.noFuncDecl]
    | s :: rest =>
      rw [BlockToNondetStmt.eq_2] at ht; simp [bind, Option.bind] at ht
      match hs : StmtToNondetStmt s, hr : BlockToNondetStmt rest with
      | some s', some r' =>
        simp [Block.noFuncDecl]
        exact ⟨stmtToNondet_some_noFuncDecl s s' hs, blockHelper rest r' hr⟩
      | some _, none => simp [hs, hr] at ht
      | none, _ => simp [hs] at ht

/-! ## Core simulation by strong induction on statement/block size -/

private theorem simulation
    (extendEval : ExtendEval P) (m : Nat) :
    (∀ (st : Stmt P (Cmd P)) (ns : NondetStmt P (Cmd P)),
      st.sizeOf ≤ m → StmtToNondetStmt st = some ns →
      ∀ (ρ₀ ρ' : Env P),
        StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) (.terminal ρ') →
        StepNondetStar P (EvalCmd P) (.stmt ns ρ₀) (.terminal ρ'))
    ∧
    (∀ (bss : List (Stmt P (Cmd P))) (ns : NondetStmt P (Cmd P)),
      Block.sizeOf bss ≤ m → BlockToNondetStmt bss = some ns →
      ∀ (ρ₀ ρ' : Env P),
        StepStmtStar P (EvalCmd P) extendEval (.stmts bss ρ₀) (.terminal ρ') →
        StepNondetStar P (EvalCmd P) (.stmt ns ρ₀) (.terminal ρ')) := by
  induction m with
  | zero =>
    constructor
    · intro st ns hsz ht ρ₀ ρ' hstar
      -- Stmt.sizeOf is always ≥ 1, so sizeOf ≤ 0 is impossible
      match st with
      | .cmd _ | .block .. | .ite .. | .loop .. | .exit .. | .funcDecl .. | .typeDecl .. =>
        simp [Stmt.sizeOf] at hsz
    · intro bss ns hsz ht ρ₀ ρ' hstar
      match bss with
      | [] =>
        -- BlockToNondetStmt [] = some (.loop _)
        simp [BlockToNondetStmt.eq_1] at ht; subst ht
        -- Det: .stmts [] ρ₀ → .terminal ρ₀
        cases hstar with
        | step _ _ _ h1 r1 => cases h1 with
          | step_stmts_nil =>
            cases r1 with
            | refl =>
              -- Nondet: .loop _ steps to .terminal ρ₀ via step_loop_zero
              exact .step _ _ _ .step_loop_zero (.refl _)
            | step _ _ _ h _ => exact nomatch h
      | s :: _ =>
        simp [Block.sizeOf] at hsz
  | succ n ih =>
    constructor

    -- ═══ Statement case ═══
    · intro st ns hsz ht ρ₀ ρ' hstar
      match st with
      | .cmd c =>
        simp [StmtToNondetStmt.eq_1] at ht; subst ht
        cases hstar with
        | step _ _ _ h1 r1 => cases h1 with
          | step_cmd hcmd =>
            cases r1 with
            | refl => exact .step _ _ _ (.step_cmd hcmd) (.refl _)
            | step _ _ _ h _ => exact nomatch h

      | .block _l bss _md =>
        rw [StmtToNondetStmt.eq_2] at ht
        cases hstar with
        | step _ _ _ h1 r1 => cases h1 with
          | step_block =>
            match block_reaches_terminal P (EvalCmd P) extendEval r1 with
            | .inl hterm =>
              -- Inner stmts terminated normally
              have : Block.sizeOf bss ≤ n := by simp [Stmt.sizeOf] at hsz; omega
              exact ih.2 bss ns this ht ρ₀ ρ' hterm
            | .inr ⟨lbl, hexit⟩ =>
              -- Inner stmts exited — impossible since no exits
              have hcov := stmtToNondet_some_exitsCovered [] (.block _l bss _md) _
                (by rw [StmtToNondetStmt.eq_2]; exact ht)
              simp [Stmt.exitsCoveredByBlocks] at hcov
              exact absurd (ReflTrans.step _ _ _ StepStmt.step_block
                (reflTrans_trans (block_inner_star P (EvalCmd P) extendEval _ _ _l hexit)
                  (.step _ _ _ StepStmt.step_block_exit_catch (.refl _))))
                (by intro h; sorry) -- TODO: need a simpler approach for this contradiction

      | .ite cond tss ess md =>
        rw [StmtToNondetStmt.eq_3] at ht; simp [bind, Option.bind] at ht
        match ht_tss : BlockToNondetStmt tss, ht_ess : BlockToNondetStmt ess with
        | some t, some e =>
          simp [ht_tss, ht_ess] at ht; subst ht
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_ite_true hcond hwfb =>
              have : Block.sizeOf tss ≤ n := by simp [Stmt.sizeOf] at hsz; omega
              have hnd := ih.2 tss t this ht_tss ρ₀ ρ' r1
              exact .step _ _ _ .step_choice_left
                (nondet_seq_terminal _ t ρ₀ ρ₀ ρ'
                  (.step _ _ _ (.step_cmd (EvalCmd.eval_assume hcond hwfb)) (.refl _))
                  (by rw [assume_env_eq]; exact hnd))
            | step_ite_false hcond hwfb =>
              have : Block.sizeOf ess ≤ n := by simp [Stmt.sizeOf] at hsz; omega
              have hnd := ih.2 ess e this ht_ess ρ₀ ρ' r1
              exact .step _ _ _ .step_choice_right
                (nondet_seq_terminal _ e ρ₀ ρ₀ ρ'
                  (.step _ _ _ (.step_cmd (EvalCmd.eval_assume ((hwfb ρ₀.store cond).2.mp hcond) hwfb)) (.refl _))
                  (by rw [assume_env_eq]; exact hnd))
        | some _, none => simp [ht_tss] at ht
        | none, _ => simp at ht

      | .loop _ _ _ _ _ => simp [StmtToNondetStmt.eq_4] at ht
      | .typeDecl _ _ => simp [StmtToNondetStmt.eq_5] at ht
      | .exit _ _ => simp [StmtToNondetStmt.eq_6] at ht
      | .funcDecl _ _ => simp [StmtToNondetStmt.eq_7] at ht

    -- ═══ Block case ═══
    · intro bss ns hsz ht ρ₀ ρ' hstar
      match bss with
      | [] =>
        simp [BlockToNondetStmt.eq_1] at ht; subst ht
        cases hstar with
        | step _ _ _ h1 r1 => cases h1 with
          | step_stmts_nil =>
            cases r1 with
            | refl => exact .step _ _ _ .step_loop_zero (.refl _)
            | step _ _ _ h _ => exact nomatch h

      | s :: rest =>
        rw [BlockToNondetStmt.eq_2] at ht; simp [bind, Option.bind] at ht
        match hs : StmtToNondetStmt s, hr : BlockToNondetStmt rest with
        | some s', some rest' =>
          simp [hs, hr] at ht; subst ht
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_stmts_cons =>
              have ⟨ρ₁, hterm_s, hterm_rest⟩ := seq_reaches_terminal P (EvalCmd P) extendEval r1
              have hsz_s : Stmt.sizeOf s ≤ n := by simp [Block.sizeOf] at hsz; omega
              have hsz_r : Block.sizeOf rest ≤ n := by simp [Block.sizeOf] at hsz; omega
              exact nondet_seq_terminal s' rest' ρ₀ ρ₁ ρ'
                (ih.1 s s' hsz_s hs ρ₀ ρ₁ hterm_s)
                (ih.2 rest rest' hsz_r hr ρ₁ ρ' hterm_rest)
        | some _, none => simp [hs] at ht
        | none, _ => simp at ht

/-- If det stmt reaches terminal, nondet transform reaches terminal. -/
theorem stmtToNondet_terminal
    (extendEval : ExtendEval P)
    (st : Stmt P (Cmd P)) (ns : NondetStmt P (Cmd P))
    (ht : StmtToNondetStmt st = some ns)
    (ρ₀ ρ' : Env P)
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) (.terminal ρ')) :
    StepNondetStar P (EvalCmd P) (.stmt ns ρ₀) (.terminal ρ') :=
  (simulation extendEval st.sizeOf).1 st ns (Nat.le_refl _) ht ρ₀ ρ' hstar

/-- If det block reaches terminal, nondet transform reaches terminal. -/
theorem blockToNondet_terminal
    (extendEval : ExtendEval P)
    (bss : List (Stmt P (Cmd P))) (ns : NondetStmt P (Cmd P))
    (ht : BlockToNondetStmt bss = some ns)
    (ρ₀ ρ' : Env P)
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.stmts bss ρ₀) (.terminal ρ')) :
    StepNondetStar P (EvalCmd P) (.stmt ns ρ₀) (.terminal ρ') :=
  (simulation extendEval (Block.sizeOf bss)).2 bss ns (Nat.le_refl _) ht ρ₀ ρ' hstar

/-! ## Main theorem -/

/-- `StmtToNondetStmt` overapproximates: any terminal env reachable from the
    deterministic execution is also reachable from the nondeterministic one.
    The exiting case is ruled out since the transform returns `none` for
    `.exit` sub-statements. -/
theorem detToNondet_overapproximates
    (extendEval : ExtendEval P) :
    Transform.Overapproximates (Lang.det extendEval) (Lang.nondet (P := P))
      (StmtToNondetStmt (P := P)) := by
  intro st ns ht ρ₀ ρ'
  refine ⟨fun hstar => ?_, fun lbl hstar => ?_⟩
  · exact stmtToNondet_terminal extendEval st ns ht ρ₀ ρ' hstar
  · exact absurd hstar (exitsCoveredByBlocks_noEscape P (EvalCmd P) extendEval st
      (stmtToNondet_some_exitsCovered [] st ns ht) ρ₀ lbl ρ')

end
