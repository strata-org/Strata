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
import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.StmtSemanticsSmallStep
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Util.Relations

/-! # Deterministic-to-Nondeterministic Transformation Correctness.

The top-level theorem is detToNondet_overapproximates.
-/

public section

open Imperative Specification

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]

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
  terminalCfg := .terminal
  exitingCfg := fun _ ρ => .terminal ρ
  isAtAssert := isAtNondetAssert
  getEval := NondetConfig.getEval
  getStore := NondetConfig.getStore

/-! ## Nondet small-step helpers -/

omit [HasVal P] [HasBoolVal P] in
theorem nondet_seq_inner_star
    (inner inner' : NondetConfig P (Cmd P)) (s2 : NondetStmt P (Cmd P))
    (h : StepNondetStar P (EvalCmd P) inner inner') :
    StepNondetStar P (EvalCmd P) (.seq inner s2) (.seq inner' s2) := by
  induction h with
  | refl => exact .refl _
  | step _ mid _ hstep _ ih => exact .step _ _ _ (.step_seq_inner hstep) ih

omit [HasVal P] [HasBoolVal P] in
theorem nondet_seq_terminal
    (s1 s2 : NondetStmt P (Cmd P)) (ρ ρ₁ ρ' : Env P)
    (h1 : StepNondetStar P (EvalCmd P) (.stmt s1 ρ) (.terminal ρ₁))
    (h2 : StepNondetStar P (EvalCmd P) (.stmt s2 ρ₁) (.terminal ρ')) :
    StepNondetStar P (EvalCmd P) (.stmt (.seq s1 s2) ρ) (.terminal ρ') :=
  .step _ _ _ .step_seq (ReflTrans_Transitive _ _ _ _
    (ReflTrans_Transitive _ _ _ _ (nondet_seq_inner_star _ _ s2 h1)
      (.step _ _ _ .step_seq_done (.refl _))) h2)

omit [HasFvar P] [HasVal P][HasBool P] [HasNot P] in
private theorem assume_env_eq (ρ : Env P) :
    ({ ρ with store := ρ.store, hasFailure := ρ.hasFailure || false } : Env P) = ρ := by
  cases ρ; simp [Bool.or_false]

omit [HasFvar P] [HasNot P] in
private theorem eval_tt_is_tt
    (δ : SemanticEval P) (σ : SemanticStore P)
    (hwfv : WellFormedSemanticEvalVal δ) :
    δ σ HasBool.tt = some HasBool.tt :=
  hwfv.2 HasBool.tt σ HasBoolVal.bool_is_val.1

/-! ## Transform-success helpers: extract sub-transform results -/

omit [HasFvar P] [HasVal P] [HasBoolVal P] in
private theorem ite_transform_some
    (cond : P.Expr) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (ns : NondetStmt P (Cmd P))
    (ht : StmtToNondetStmt (.ite cond tss ess md) = some ns) :
    ∃ t e, BlockToNondetStmt tss = some t ∧ BlockToNondetStmt ess = some e ∧
      ns = .choice
        (.seq (.cmd (.assume "true_cond" cond md)) t)
        (.seq (.cmd (.assume "false_cond" (HasNot.not cond) md)) e) := by
  rw [StmtToNondetStmt.eq_3] at ht
  match h1 : BlockToNondetStmt tss, h2 : BlockToNondetStmt ess with
  | some t, some e =>
    simp [h1, h2, bind, Option.bind] at ht
    exact ⟨t, e, rfl, rfl, ht.symm⟩
  | some _, none => simp [h1, h2, bind, Option.bind] at ht
  | none, _ => simp [h1, bind, Option.bind] at ht

omit [HasFvar P] [HasVal P] [HasBoolVal P] in
private theorem loop_transform_some
    (g : P.Expr) (m : Option P.Expr) (inv : List P.Expr)
    (body : List (Stmt P (Cmd P))) (md : MetaData P)
    (ns : NondetStmt P (Cmd P))
    (ht : StmtToNondetStmt (.loop g m inv body md) = some ns) :
    ∃ b, BlockToNondetStmt body = some b ∧
      ns = .loop (.seq (.cmd (.assume "guard" g md)) b) := by
  rw [StmtToNondetStmt.eq_4] at ht
  match hb : BlockToNondetStmt body with
  | some b => simp [hb, bind, Option.bind] at ht; exact ⟨b, rfl, ht.symm⟩
  | none => simp [hb, bind, Option.bind] at ht

omit [HasFvar P] [HasVal P] [HasBoolVal P] in
private theorem block_transform_some
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P)))
    (ns : NondetStmt P (Cmd P))
    (ht : BlockToNondetStmt (s :: rest) = some ns) :
    ∃ s' rest', StmtToNondetStmt s = some s' ∧ BlockToNondetStmt rest = some rest' ∧
      ns = .seq s' rest' := by
  rw [BlockToNondetStmt.eq_2] at ht
  match hs : StmtToNondetStmt s, hr : BlockToNondetStmt rest with
  | some s', some r' =>
    simp [hs, hr, bind, Option.bind] at ht
    exact ⟨s', r', rfl, rfl, ht.symm⟩
  | some _, none => simp [hs, hr, bind, Option.bind] at ht
  | none, _ => simp [hs, bind, Option.bind] at ht

/-! ## exitsCoveredByBlocks from successful transform -/

omit [HasFvar P] [HasVal P] [HasBoolVal P] in
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
    have ⟨t, e, ht_t, ht_e, _⟩ := ite_transform_some _ tss ess _ _ ht
    simp [Stmt.exitsCoveredByBlocks]
    exact ⟨blockHelper labels tss t ht_t, blockHelper labels ess e ht_e⟩
  | .loop _ _ _ body _ =>
    have ⟨b, hb, _⟩ := loop_transform_some _ _ _ body _ _ ht
    simp [Stmt.exitsCoveredByBlocks]
    exact blockHelper labels body b hb
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
      have ⟨s', r', hs, hr, _⟩ := block_transform_some s rest ns ht
      simp [Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks]
      exact ⟨stmtToNondet_some_exitsCovered labels s s' hs, blockHelper labels rest r' hr⟩

/-! ## noFuncDecl from successful transform -/

omit [HasFvar P] [HasVal P] [HasBoolVal P] in
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
    have ⟨t, e, ht_t, ht_e, _⟩ := ite_transform_some _ tss ess _ _ ht
    simp [Stmt.noFuncDecl]
    exact ⟨blockHelper tss t ht_t, blockHelper ess e ht_e⟩
  | .loop _ _ _ body _ =>
    have ⟨b, hb, _⟩ := loop_transform_some _ _ _ body _ _ ht
    simp [Stmt.noFuncDecl]
    exact blockHelper body b hb
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
      have ⟨s', r', hs, hr, _⟩ := block_transform_some s rest ns ht
      simp [Block.noFuncDecl]
      exact ⟨stmtToNondet_some_noFuncDecl s s' hs, blockHelper rest r' hr⟩

/-! ## ReflTransT decomposition helpers -/

omit [HasVal P] [HasBoolVal P] in
private theorem seqT_reaches_terminal
    (extendEval : ExtendEval P)
    {inner : Config P (Cmd P)} {ss : List (Stmt P (Cmd P))} {ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.seq inner ss) (.terminal ρ')) :
    ∃ (ρ₁ : Env P), ∃ (h1 : ReflTransT (StepStmt P (EvalCmd P) extendEval) inner (.terminal ρ₁)),
      ∃ (h2 : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.stmts ss ρ₁) (.terminal ρ')),
      h1.len + h2.len < hstar.len := by
  match hstar with
  | .step _ _ _ (.step_seq_inner h) hrest =>
    have ⟨ρ₁, hterm, htail, hlen⟩ := seqT_reaches_terminal extendEval hrest
    exact ⟨ρ₁, .step _ _ _ h hterm, htail, by simp [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_seq_done hrest => exact ⟨_, .refl _, hrest, by show 0 + hrest.len < 1 + hrest.len; omega⟩
  | .step _ _ _ .step_seq_exit hrest =>
    match hrest with
    | .step _ _ _ h _ => exact nomatch h

omit [HasVal P] [HasBoolVal P] in
private theorem stmtsT_cons_terminal
    (extendEval : ExtendEval P)
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))} {ρ₀ ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.stmts (s :: rest) ρ₀) (.terminal ρ')) :
    ∃ (ρ₁ : Env P), ∃ (h1 : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.stmt s ρ₀) (.terminal ρ₁)),
      ∃ (h2 : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.stmts rest ρ₁) (.terminal ρ')),
      h1.len + h2.len + 2 ≤ hstar.len := by
  match hstar with
  | .step _ _ _ .step_stmts_cons hrest =>
    have ⟨ρ₁, h1, h2, hlen⟩ := seqT_reaches_terminal extendEval hrest
    exact ⟨ρ₁, h1, h2, by simp [ReflTransT.len]; omega⟩

omit [HasVal P] [HasBoolVal P] in
private theorem stmtsT_append_terminal
    (extendEval : ExtendEval P)
    (ss₁ : List (Stmt P (Cmd P))) (s : Stmt P (Cmd P)) (ρ₀ ρ' : Env P)
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.stmts (ss₁ ++ [s]) ρ₀) (.terminal ρ'))
    (hcov : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks (P := P) (CmdT := Cmd P) [] ss₁) :
    ∃ (ρ₁ : Env P), ∃ (_ : StepStmtStar P (EvalCmd P) extendEval (.stmts ss₁ ρ₀) (.terminal ρ₁)),
      ∃ (hs : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.stmt s ρ₁) (.terminal ρ')),
      hs.len < hstar.len := by
  induction ss₁ generalizing ρ₀ with
  | nil =>
    have ⟨ρ₁, h1, h2, hlen⟩ := stmtsT_cons_terminal extendEval hstar
    -- h2 : ReflTransT ... (.stmts [] ρ₁) (.terminal ρ')
    -- Must be: step via step_stmts_nil then refl, so ρ₁ = ρ'
    have hρ : ρ₁ = ρ' := by
      match h2 with
      | .step _ _ _ .step_stmts_nil (.refl _) => rfl
    subst hρ
    exact ⟨ρ₀, .step _ _ _ .step_stmts_nil (.refl _), h1, by omega⟩
  | cons s' rest' ih =>
    -- Note: (s' :: rest') ++ [s] = s' :: (rest' ++ [s]) by definitional reduction
    have ⟨ρ₁, h_s', h_rest, hlen₁⟩ := stmtsT_cons_terminal extendEval hstar
    have ⟨ρ₂, h_rest', h_s, hlen₂⟩ := ih ρ₁ h_rest hcov.2
    exact ⟨ρ₂,
      ReflTrans_Transitive _ _ _ _
        (stmts_cons_step P (EvalCmd P) extendEval s' rest' ρ₀ ρ₁ (reflTransT_to_prop h_s'))
        h_rest',
      h_s, by omega⟩

/-! ## Loop simulation -/

/-- Prove that adding the loop guard 'g' as an extra assume statement 'assume g'
    in the beginning of loop body does not reduce the set of possible final
    states. Note that hstarT assumption is using the deterministic
    Imperative.Stmt whereas the conclusion is using NondetStmt. -/
private def loop_sim
    (extendEval : ExtendEval P)
    (g : P.Expr) (m : Option P.Expr) (inv : List P.Expr)
    (body : List (Stmt P (Cmd P))) (md : MetaData P)
    (b : NondetStmt P (Cmd P))
    (sim_body : ∀ ρ₀ ρ',
      WellFormedSemanticEvalBool ρ₀.eval → WellFormedSemanticEvalVal ρ₀.eval →
      StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ₀) (.terminal ρ') →
      StepNondetStar P (EvalCmd P) (.stmt b ρ₀) (.terminal ρ'))
    (hcov : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks (P := P) (CmdT := Cmd P) [] body)
    (hnofd_body : Block.noFuncDecl body = true)
    (ρ₀ ρ' : Env P)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hstarT : ReflTransT (StepStmt P (EvalCmd P) extendEval)
      (.stmt (.loop g m inv body md) ρ₀) (.terminal ρ')) :
    StepNondetStar P (EvalCmd P)
      (.stmt (.loop (.seq (.cmd (.assume "guard" g md)) b)) ρ₀) (.terminal ρ') :=
  match hstarT with
  | .step _ _ _ (.step_loop_exit _ _) (.refl _) =>
    .step _ _ _ .step_loop_zero (.refl _)
  | .step _ _ _ (.step_loop_exit _ _) (.step _ _ _ h _) => nomatch h
  | .step _ _ _ (.step_loop_enter hg hwfb) hrest =>
    let ⟨ρ₁, hbody, hloop_stmtT, hlen_loop⟩ :=
      stmtsT_append_terminal extendEval body (.loop g m inv body md) ρ₀ ρ' hrest hcov
    let nondet_body := sim_body ρ₀ ρ₁ hwfb hwfv hbody
    have heval_eq : ρ₁.eval = ρ₀.eval :=
      smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
        body ρ₀ ρ₁ hnofd_body hbody
    have hwfb₁ : WellFormedSemanticEvalBool ρ₁.eval := heval_eq ▸ hwfb
    have hwfv₁ : WellFormedSemanticEvalVal ρ₁.eval := heval_eq ▸ hwfv
    have h_assume : StepNondetStar P (EvalCmd P)
        (.stmt (.cmd (.assume "guard" g md)) ρ₀) (.terminal ρ₀) := by
      have raw : StepNondetStar P (EvalCmd P)
          (.stmt (.cmd (.assume "guard" g md)) ρ₀)
          (.terminal { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }) :=
        .step _ _ _ (.step_cmd (EvalCmd.eval_assume hg hwfb)) (.refl _)
      rwa [assume_env_eq] at raw
    let h_iter : StepNondetStar P (EvalCmd P)
        (.stmt (.seq (.cmd (.assume "guard" g md)) b) ρ₀) (.terminal ρ₁) :=
      nondet_seq_terminal _ b ρ₀ ρ₀ ρ₁ h_assume nondet_body
    let nondet_loop := loop_sim extendEval g m inv body md b sim_body hcov hnofd_body ρ₁ ρ' hwfv₁ hloop_stmtT
    .step _ _ _ .step_loop_step
      (ReflTrans_Transitive _ _ _ _
        (nondet_seq_inner_star _ _
          (.loop (.seq (.cmd (.assume "guard" g md)) b)) h_iter)
        (.step _ _ _ .step_seq_done nondet_loop))
  termination_by hstarT.len
  decreasing_by
    simp_all [ReflTransT.len]
    omega

/-! ## Core simulation by strong induction on statement/block size -/

private theorem simulation
    (extendEval : ExtendEval P) (sz : Nat) :
    (∀ (st : Stmt P (Cmd P)) (ns : NondetStmt P (Cmd P)),
      st.sizeOf ≤ sz → StmtToNondetStmt st = some ns →
      ∀ (ρ₀ ρ' : Env P),
        WellFormedSemanticEvalBool ρ₀.eval → WellFormedSemanticEvalVal ρ₀.eval →
        StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) (.terminal ρ') →
        StepNondetStar P (EvalCmd P) (.stmt ns ρ₀) (.terminal ρ'))
    ∧
    (∀ (bss : List (Stmt P (Cmd P))) (ns : NondetStmt P (Cmd P)),
      Block.sizeOf bss ≤ sz → BlockToNondetStmt bss = some ns →
      ∀ (ρ₀ ρ' : Env P),
        WellFormedSemanticEvalBool ρ₀.eval → WellFormedSemanticEvalVal ρ₀.eval →
        StepStmtStar P (EvalCmd P) extendEval (.stmts bss ρ₀) (.terminal ρ') →
        StepNondetStar P (EvalCmd P) (.stmt ns ρ₀) (.terminal ρ')) := by
  induction sz with
  | zero =>
    constructor
    · intro st ns hsz ht ρ₀ ρ' _ _ hstar
      match st with
      | .cmd _ | .block .. | .ite .. | .loop .. | .exit .. | .funcDecl .. | .typeDecl .. =>
        simp_all [Stmt.sizeOf]
    · intro bss ns hsz ht ρ₀ ρ' hwfb hwfv hstar
      match bss with
      | [] =>
        simp [BlockToNondetStmt.eq_1] at ht; subst ht
        cases hstar with
        | step _ _ _ h1 r1 => cases h1 with
          | step_stmts_nil =>
            cases r1 with
            | refl =>
              exact .step _ _ _
                (.step_cmd (EvalCmd.eval_assert_pass (eval_tt_is_tt ρ₀.eval ρ₀.store hwfv) hwfb))
                (by rw [assume_env_eq]; exact .refl _)
            | step _ _ _ h _ => exact nomatch h
      | s :: _ => simp_all [Block.sizeOf]
  | succ n ih =>
    constructor

    -- ═══ Statement case ═══
    · intro st ns hsz ht ρ₀ ρ' hwfb hwfv hstar
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
              have : Block.sizeOf bss ≤ n := by
                simp_all [Stmt.sizeOf]; omega
              exact ih.2 bss ns this ht ρ₀ ρ' hwfb hwfv hterm
            | .inr ⟨lbl, hexit⟩ =>
              exact absurd hexit (block_exitsCoveredByBlocks_noEscape P (EvalCmd P) extendEval bss
                (stmtToNondet_some_exitsCovered.blockHelper [] bss ns ht) ρ₀ lbl ρ')

      | .ite cond tss ess md =>
        have ⟨t, e, ht_tss, ht_ess, hns⟩ := ite_transform_some cond tss ess md ns ht
        subst hns
        cases hstar with
        | step _ _ _ h1 r1 => cases h1 with
          | step_ite_true hcond hwfb =>
            have : Block.sizeOf tss ≤ n := by
              simp_all [Stmt.sizeOf]; omega
            have hnd := ih.2 tss t this ht_tss ρ₀ ρ' hwfb hwfv r1
            have h_assume : StepNondetStar P (EvalCmd P)
                (.stmt (.cmd (.assume "true_cond" cond md)) ρ₀) (.terminal ρ₀) := by
              have heq := assume_env_eq ρ₀
              have : StepNondetStar P (EvalCmd P)
                  (.stmt (.cmd (.assume "true_cond" cond md)) ρ₀)
                  (.terminal { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }) :=
                .step _ _ _ (.step_cmd (EvalCmd.eval_assume hcond hwfb)) (.refl _)
              rw [heq] at this; exact this
            exact .step _ _ _ .step_choice_left
              (nondet_seq_terminal _ t ρ₀ ρ₀ ρ' h_assume hnd)
          | step_ite_false hcond hwfb =>
            have : Block.sizeOf ess ≤ n := by
              simp_all [Stmt.sizeOf]; omega
            have hnd := ih.2 ess e this ht_ess ρ₀ ρ' hwfb hwfv r1
            have hcond_neg := (hwfb ρ₀.store cond).2.mp hcond
            have h_assume : StepNondetStar P (EvalCmd P)
                (.stmt (.cmd (.assume "false_cond" (HasNot.not cond) md)) ρ₀) (.terminal ρ₀) := by
              have heq := assume_env_eq ρ₀
              have : StepNondetStar P (EvalCmd P)
                  (.stmt (.cmd (.assume "false_cond" (HasNot.not cond) md)) ρ₀)
                  (.terminal { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }) :=
                .step _ _ _ (.step_cmd (EvalCmd.eval_assume hcond_neg hwfb)) (.refl _)
              rw [heq] at this; exact this
            exact .step _ _ _ .step_choice_right
              (nondet_seq_terminal _ e ρ₀ ρ₀ ρ' h_assume hnd)

      | .loop g m' inv body md =>
        have ⟨b, hb, hns⟩ := loop_transform_some g m' inv body md ns ht
        subst hns
        have hsz_body : Block.sizeOf body ≤ n := by
          simp_all [Stmt.sizeOf]; omega
        have sim_body : ∀ ρ₀ ρ',
            WellFormedSemanticEvalBool ρ₀.eval → WellFormedSemanticEvalVal ρ₀.eval →
            StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ₀) (.terminal ρ') →
            StepNondetStar P (EvalCmd P) (.stmt b ρ₀) (.terminal ρ') :=
          fun ρ₀ ρ' hwfb' hwfv' h => ih.2 body b hsz_body hb ρ₀ ρ' hwfb' hwfv' h
        have hcov := stmtToNondet_some_exitsCovered.blockHelper [] body b hb
        have hnofd_body : Block.noFuncDecl body = true :=
          stmtToNondet_some_noFuncDecl.blockHelper body b hb
        exact loop_sim extendEval g m' inv body md b sim_body hcov hnofd_body ρ₀ ρ' hwfv
          (reflTrans_to_T hstar)

      | .typeDecl _ _ => simp [StmtToNondetStmt.eq_5] at ht
      | .exit _ _ => simp [StmtToNondetStmt.eq_6] at ht
      | .funcDecl _ _ => simp [StmtToNondetStmt.eq_7] at ht

    -- ═══ Block case ═══
    · intro bss ns hsz ht ρ₀ ρ' hwfb hwfv hstar
      match bss with
      | [] =>
        simp [BlockToNondetStmt.eq_1] at ht; subst ht
        cases hstar with
        | step _ _ _ h1 r1 => cases h1 with
          | step_stmts_nil =>
            cases r1 with
            | refl =>
              exact .step _ _ _
                (.step_cmd (EvalCmd.eval_assert_pass (eval_tt_is_tt ρ₀.eval ρ₀.store hwfv) hwfb))
                (by rw [assume_env_eq]; exact .refl _)
            | step _ _ _ h _ => exact nomatch h

      | s :: rest =>
        have ⟨s', rest', hs, hr, hns⟩ := block_transform_some s rest ns ht
        subst hns
        cases hstar with
        | step _ _ _ h1 r1 => cases h1 with
          | step_stmts_cons =>
            have ⟨ρ₁, hterm_s, hterm_rest⟩ := seq_reaches_terminal P (EvalCmd P) extendEval r1
            have hsz_s : Stmt.sizeOf s ≤ n := by
              simp_all [Block.sizeOf]; omega
            have hsz_r : Block.sizeOf rest ≤ n := by
              simp_all [Block.sizeOf]; omega
            have hnofd := stmtToNondet_some_noFuncDecl s s' hs
            have heval_eq := smallStep_noFuncDecl_preserves_eval P (EvalCmd P) extendEval
              s ρ₀ ρ₁ hnofd hterm_s
            have hwfb₁ : WellFormedSemanticEvalBool ρ₁.eval := heval_eq ▸ hwfb
            have hwfv₁ : WellFormedSemanticEvalVal ρ₁.eval := heval_eq ▸ hwfv
            exact nondet_seq_terminal s' rest' ρ₀ ρ₁ ρ'
              (ih.1 s s' hsz_s hs ρ₀ ρ₁ hwfb hwfv hterm_s)
              (ih.2 rest rest' hsz_r hr ρ₁ ρ' hwfb₁ hwfv₁ hterm_rest)

/-- If det stmt reaches terminal, nondet transform reaches terminal. -/
theorem stmtToNondet_terminal
    (extendEval : ExtendEval P)
    (st : Stmt P (Cmd P)) (ns : NondetStmt P (Cmd P))
    (ht : StmtToNondetStmt st = some ns)
    (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) (.terminal ρ')) :
    StepNondetStar P (EvalCmd P) (.stmt ns ρ₀) (.terminal ρ') :=
  (simulation extendEval st.sizeOf).1 st ns (Nat.le_refl _) ht ρ₀ ρ' hwfb hwfv hstar

/-- If det block reaches terminal, nondet transform reaches terminal. -/
theorem blockToNondet_terminal
    (extendEval : ExtendEval P)
    (bss : List (Stmt P (Cmd P))) (ns : NondetStmt P (Cmd P))
    (ht : BlockToNondetStmt bss = some ns)
    (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.stmts bss ρ₀) (.terminal ρ')) :
    StepNondetStar P (EvalCmd P) (.stmt ns ρ₀) (.terminal ρ') :=
  (simulation extendEval (Block.sizeOf bss)).2 bss ns (Nat.le_refl _) ht ρ₀ ρ' hwfb hwfv hstar

/-! ## Main theorem -/

/-- `StmtToNondetStmt` overapproximates: any terminal env reachable from the
    deterministic execution is also reachable from the nondeterministic one,
    provided the evaluator is well-formed.
    The exiting case is ruled out since the transform returns `none` for
    `.exit` sub-statements. -/
theorem detToNondet_overapproximates
    (extendEval : ExtendEval P) :
    Transform.Overapproximates (Lang.det extendEval) (Lang.nondet (P := P))
      (StmtToNondetStmt (P := P)) := by
  intro st ns ht ρ₀ ρ' hwfb hwfv
  refine ⟨fun hstar => ?_, fun lbl hstar => ?_⟩
  · exact stmtToNondet_terminal extendEval st ns ht ρ₀ ρ' hwfb hwfv hstar
  · exact absurd hstar (exitsCoveredByBlocks_noEscape P (EvalCmd P) extendEval st
      (stmtToNondet_some_exitsCovered [] st ns ht) ρ₀ lbl ρ')

end
