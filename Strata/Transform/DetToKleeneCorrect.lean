/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.KleeneStmtSemantics
public import Strata.Transform.DetToKleene
public import Strata.Transform.Specification
import all Strata.Transform.Specification
public import Strata.Transform.SpecificationProps
import all Strata.Transform.SpecificationProps
import all Strata.Transform.DetToKleene
import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.StmtSemanticsProps
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Util.Relations
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
import Strata.DL.Imperative.KleeneSemanticsProps

/-! # Deterministic-to-Kleene Transformation Correctness.

The top-level theorem is detToKleene_overapproximates.
-/

public section

open Imperative Specification

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P] [HasVarsPure P P.Expr]

/-! ## Lang instances -/

abbrev Lang.det (extendEval : ExtendEval P) : Lang P :=
  Lang.imperative P (Cmd P) (EvalCmd P) extendEval (isAtAssert P)

def isAtKleeneAssert : KleeneConfig P (Cmd P) → AssertId P → Prop
  | .stmt (.cmd (.assert label expr _)) _, a => a.label = label ∧ a.expr = expr
  | .seq inner _, a => isAtKleeneAssert inner a
  | .block _ inner, a => isAtKleeneAssert inner a
  | _, _ => False

abbrev Lang.kleene : Lang P where
  StmtT := KleeneStmt P (Cmd P)
  CfgT := KleeneConfig P (Cmd P)
  star := StepKleeneStar P (EvalCmd P)
  stmtCfg := .stmt
  terminalCfg := .terminal
  exitingCfg := fun _ ρ => .terminal ρ
  isAtAssert := isAtKleeneAssert
  getEnv := KleeneConfig.getEnv
  InitEnvWFParamsTy := Unit
  initEnvWF := fun _ _ _ => True

/-! ## Transform-success helpers: extract sub-transform results -/

omit [HasFvar P] [HasVal P] [HasBoolVal P] in
private theorem ite_transform_some_det
    (cond : P.Expr) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (ns : KleeneStmt P (Cmd P))
    (ht : StmtToKleeneStmt (.ite (.det cond) tss ess md) = some ns) :
    ∃ t e, BlockToKleeneStmt tss = some t ∧ BlockToKleeneStmt ess = some e ∧
      ns = .choice
        (.seq (.cmd (.assume "true_cond" cond md)) t)
        (.seq (.cmd (.assume "false_cond" (HasNot.not cond) md)) e) := by
  simp [StmtToKleeneStmt] at ht
  match h1 : BlockToKleeneStmt tss, h2 : BlockToKleeneStmt ess with
  | some t, some e =>
    simp [h1, h2, Option.bind] at ht
    exact ⟨t, e, rfl, rfl, ht.symm⟩
  | some _, none => simp [h1, h2, Option.bind] at ht
  | none, _ => simp [h1, Option.bind] at ht

omit [HasFvar P] [HasVal P] [HasBoolVal P] in
private theorem ite_transform_some_nondet
    (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (ns : KleeneStmt P (Cmd P))
    (ht : StmtToKleeneStmt (.ite .nondet tss ess md) = some ns) :
    ∃ t e, BlockToKleeneStmt tss = some t ∧ BlockToKleeneStmt ess = some e ∧
      ns = .choice t e := by
  simp [StmtToKleeneStmt] at ht
  match h1 : BlockToKleeneStmt tss, h2 : BlockToKleeneStmt ess with
  | some t, some e =>
    simp [h1, h2, Option.bind] at ht
    exact ⟨t, e, rfl, rfl, ht.symm⟩
  | some _, none => simp [h1, h2, Option.bind] at ht
  | none, _ => simp [h1, Option.bind] at ht

omit [HasFvar P] [HasVal P] [HasBoolVal P] in
private theorem loop_transform_some_det
    (g : P.Expr) (m : Option P.Expr) (inv : List (String × P.Expr))
    (body : List (Stmt P (Cmd P))) (md : MetaData P)
    (ns : KleeneStmt P (Cmd P))
    (ht : StmtToKleeneStmt (.loop (.det g) m inv body md) = some ns) :
    inv = [] ∧ ∃ b, BlockToKleeneStmt body = some b ∧
      ns = .loop (.seq (.cmd (.assume "guard" g md)) b) := by
  simp [StmtToKleeneStmt] at ht
  match hinv : inv with
  | [] =>
    simp [Option.bind] at ht
    match hb : BlockToKleeneStmt body with
    | some b => simp [hb] at ht; exact ⟨rfl, b, rfl, ht.symm⟩
    | none => simp [hb] at ht
  | _ :: _ => simp [Option.bind] at ht

omit [HasFvar P] [HasVal P] [HasBoolVal P] in
private theorem loop_transform_some_nondet
    (m : Option P.Expr) (inv : List (String × P.Expr))
    (body : List (Stmt P (Cmd P))) (md : MetaData P)
    (ns : KleeneStmt P (Cmd P))
    (ht : StmtToKleeneStmt (.loop .nondet m inv body md) = some ns) :
    inv = [] ∧ ∃ b, BlockToKleeneStmt body = some b ∧
      ns = .loop b := by
  simp [StmtToKleeneStmt] at ht
  match hinv : inv with
  | [] =>
    simp [Option.bind] at ht
    match hb : BlockToKleeneStmt body with
    | some b => simp [hb] at ht; exact ⟨rfl, b, rfl, ht.symm⟩
    | none => simp [hb] at ht
  | _ :: _ => simp [Option.bind] at ht

omit [HasFvar P] [HasVal P] [HasBoolVal P] in
private theorem block_transform_some
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P)))
    (ns : KleeneStmt P (Cmd P))
    (ht : BlockToKleeneStmt (s :: rest) = some ns) :
    ∃ s' rest', StmtToKleeneStmt s = some s' ∧ BlockToKleeneStmt rest = some rest' ∧
      ns = .seq s' rest' := by
  rw [BlockToKleeneStmt.eq_2] at ht
  match hs : StmtToKleeneStmt s, hr : BlockToKleeneStmt rest with
  | some s', some r' =>
    simp [hs, hr, bind, Option.bind] at ht
    exact ⟨s', r', rfl, rfl, ht.symm⟩
  | some _, none => simp [hs, hr, bind, Option.bind] at ht
  | none, _ => simp [hs, bind, Option.bind] at ht

/-! ## exitsCoveredByBlocks from successful transform -/

omit [HasFvar P] [HasVal P] [HasBoolVal P] in
private theorem stmtToKleene_some_exitsCovered
    (labels : List String)
    (st : Stmt P (Cmd P)) (ns : KleeneStmt P (Cmd P))
    (ht : StmtToKleeneStmt st = some ns) :
    Stmt.exitsCoveredByBlocks (P := P) (CmdT := Cmd P) labels st := by
  match st with
  | .cmd _ => simp [Stmt.exitsCoveredByBlocks]
  | .block l bss _ =>
    simp [StmtToKleeneStmt] at ht
    match hb : BlockToKleeneStmt bss, ht with
    | some b, ht =>
      simp at ht; subst ht
      simp [Stmt.exitsCoveredByBlocks]
      exact blockHelper (l :: labels) bss b hb
  | .ite cond tss ess md =>
    match cond with
    | .det _ =>
      have ⟨t, e, ht_t, ht_e, _⟩ := ite_transform_some_det _ tss ess _ _ ht
      simp [Stmt.exitsCoveredByBlocks]
      exact ⟨blockHelper labels tss t ht_t, blockHelper labels ess e ht_e⟩
    | .nondet =>
      have ⟨t, e, ht_t, ht_e, _⟩ := ite_transform_some_nondet tss ess _ _ ht
      simp [Stmt.exitsCoveredByBlocks]
      exact ⟨blockHelper labels tss t ht_t, blockHelper labels ess e ht_e⟩
  | .loop guard _ _ body _ =>
    match guard with
    | .det _ =>
      have ⟨_, b, hb, _⟩ := loop_transform_some_det _ _ _ body _ _ ht
      simp [Stmt.exitsCoveredByBlocks]
      exact blockHelper labels body b hb
    | .nondet =>
      have ⟨_, b, hb, _⟩ := loop_transform_some_nondet _ _ body _ _ ht
      simp [Stmt.exitsCoveredByBlocks]
      exact blockHelper labels body b hb
  | .typeDecl _ _ => simp [StmtToKleeneStmt.eq_5] at ht
  | .exit _ _ => simp [StmtToKleeneStmt.eq_6] at ht
  | .funcDecl _ _ => simp [StmtToKleeneStmt.eq_7] at ht
where
  blockHelper (labels : List String) (bss : List (Stmt P (Cmd P))) (ns : KleeneStmt P (Cmd P))
      (ht : BlockToKleeneStmt bss = some ns) :
      Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks (P := P) (CmdT := Cmd P) labels bss := by
    match bss with
    | [] => simp [Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks]
    | s :: rest =>
      have ⟨s', r', hs, hr, _⟩ := block_transform_some s rest ns ht
      simp [Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks]
      exact ⟨stmtToKleene_some_exitsCovered labels s s' hs, blockHelper labels rest r' hr⟩

/-! ## noFuncDecl from successful transform -/

omit [HasFvar P] [HasVal P] [HasBoolVal P] in
private theorem stmtToKleene_some_noFuncDecl
    (st : Stmt P (Cmd P)) (ns : KleeneStmt P (Cmd P))
    (ht : StmtToKleeneStmt st = some ns) :
    Stmt.noFuncDecl st = true := by
  match st with
  | .cmd _ => simp [Stmt.noFuncDecl]
  | .block _ bss _ =>
    simp [StmtToKleeneStmt] at ht
    match hb : BlockToKleeneStmt bss, ht with
    | some b, ht =>
      simp at ht; subst ht
      simp [Stmt.noFuncDecl]
      exact blockHelper bss b hb
  | .ite cond tss ess md =>
    match cond with
    | .det _ =>
      have ⟨t, e, ht_t, ht_e, _⟩ := ite_transform_some_det _ tss ess _ _ ht
      simp [Stmt.noFuncDecl]
      exact ⟨blockHelper tss t ht_t, blockHelper ess e ht_e⟩
    | .nondet =>
      have ⟨t, e, ht_t, ht_e, _⟩ := ite_transform_some_nondet tss ess _ _ ht
      simp [Stmt.noFuncDecl]
      exact ⟨blockHelper tss t ht_t, blockHelper ess e ht_e⟩
  | .loop guard _ _ body _ =>
    match guard with
    | .det _ =>
      have ⟨_, b, hb, _⟩ := loop_transform_some_det _ _ _ body _ _ ht
      simp [Stmt.noFuncDecl]
      exact blockHelper body b hb
    | .nondet =>
      have ⟨_, b, hb, _⟩ := loop_transform_some_nondet _ _ body _ _ ht
      simp [Stmt.noFuncDecl]
      exact blockHelper body b hb
  | .typeDecl _ _ => simp [StmtToKleeneStmt.eq_5] at ht
  | .exit _ _ => simp [StmtToKleeneStmt.eq_6] at ht
  | .funcDecl _ _ => simp [StmtToKleeneStmt.eq_7] at ht
where
  blockHelper (bss : List (Stmt P (Cmd P))) (ns : KleeneStmt P (Cmd P))
      (ht : BlockToKleeneStmt bss = some ns) :
      Block.noFuncDecl bss = true := by
    match bss with
    | [] => simp [Block.noFuncDecl]
    | s :: rest =>
      have ⟨s', r', hs, hr, _⟩ := block_transform_some s rest ns ht
      simp [Block.noFuncDecl]
      exact ⟨stmtToKleene_some_noFuncDecl s s' hs, blockHelper rest r' hr⟩

/-! ## ReflTransT decomposition helpers -/

omit [HasVal P] [HasBoolVal P] in
theorem seqT_reaches_terminal
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
theorem stmtsT_cons_terminal
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
/-- Invert a block execution reaching terminal when the inner config cannot
    exit: the inner reaches terminal with a strictly shorter derivation. -/
theorem blockT_reaches_terminal_noExit
    (extendEval : ExtendEval P)
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
    have ⟨ρ_inner, hterm, heq, hlen⟩ := blockT_reaches_terminal_noExit extendEval hrest h_no_exit'
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
    exact ⟨ρ₀, .step _ _ _ .step_stmts_nil (.refl _), h1, by grind⟩
  | cons s' rest' ih =>
    -- Note: (s' :: rest') ++ [s] = s' :: (rest' ++ [s]) by definitional reduction
    have ⟨ρ₁, h_s', h_rest, hlen₁⟩ := stmtsT_cons_terminal extendEval hstar
    have ⟨ρ₂, h_rest', h_s, hlen₂⟩ := ih ρ₁ h_rest hcov.2
    exact ⟨ρ₂,
      ReflTrans_Transitive _ _ _ _
        (stmts_cons_step P (EvalCmd P) extendEval s' rest' ρ₀ ρ₁ (reflTransT_to_prop h_s'))
        h_rest',
      h_s, by grind⟩

/-! ## Loop simulation -/

/-- With an empty invariant list, the `hasInvFailure` flag returned by any
    `step_loop_*` rule is vacuously `false`: the boolean iff cannot witness
    an invariant in an empty list. -/
private theorem empty_inv_no_failure
    {α : Type} {Q : α → Prop} {hasInvFailure : Bool}
    (hff_iff : hasInvFailure = true ↔ ∃ le, le ∈ ([] : List α) ∧ Q le) :
    hasInvFailure = false := by
  cases hb : hasInvFailure with
  | false => rfl
  | true =>
    rw [hb] at hff_iff
    have ⟨_, hmem, _⟩ := hff_iff.mp rfl
    exact ((List.mem_nil_iff _).mp hmem).elim

/-- Prove that adding the loop guard 'g' as an extra assume statement 'assume g'
    in the beginning of loop body does not reduce the set of possible final
    states. Note that hstarT assumption is using the deterministic
    Imperative.Stmt whereas the conclusion is using KleeneStmt. -/
private def loop_sim
    (extendEval : ExtendEval P)
    (g : P.Expr) (m : Option P.Expr)
    (body : List (Stmt P (Cmd P))) (md : MetaData P)
    (b : KleeneStmt P (Cmd P))
    (sim_body : ∀ ρ₀ ρ',
      WellFormedSemanticEvalBool ρ₀.eval → WellFormedSemanticEvalVal ρ₀.eval →
      WellFormedSemanticEvalExprCongr ρ₀.eval →
      StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ₀) (.terminal ρ') →
      StepKleeneStar P (EvalCmd P) (.stmt b ρ₀) (.terminal ρ'))
    (hcov : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks (P := P) (CmdT := Cmd P) [] body)
    (hnofd_body : Block.noFuncDecl body = true)
    (ρ₀ ρ' : Env P) (n : Nat)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwfcongr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (hstarT : ReflTransT (StepStmt P (EvalCmd P) extendEval)
      (.stmt (.loop (.det g) m ([] : List (String × P.Expr)) body md) ρ₀) (.terminal ρ'))
    (hlen : hstarT.len ≤ n) :
    StepKleeneStar P (EvalCmd P)
      (.stmt (.loop (.seq (.cmd (.assume "guard" g md)) b)) ρ₀) (.terminal ρ') := by
  induction n generalizing ρ₀ ρ' with
  | zero =>
    -- hstarT of length 0 = refl, impossible since src ≠ tgt.
    match hstarT, hlen with
    | .step _ _ _ _ _, hlen => simp [ReflTransT.len] at hlen
  | succ n ih =>
    match hstarT, hlen with
    | .step _ _ _ (@StepStmt.step_loop_exit _ _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure _ _ hff_iff _) hrest, hlen =>
      have h_no : hasInvFailure = false := empty_inv_no_failure hff_iff
      subst h_no
      have hρ : ({ ρ₀ with hasFailure := ρ₀.hasFailure || false } : Env P) = ρ₀ := by
        rw [Bool.or_false]
      rw [hρ] at hrest
      match hrest with
      | .refl _ => exact .step _ _ _ .step_loop_zero (.refl _)
      | .step _ _ _ h _ => exact nomatch h
    | .step _ _ _ (@StepStmt.step_loop_enter _ _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure hg _ hff_iff hwfb) hrest, hlen =>
      have h_no : hasInvFailure = false := empty_inv_no_failure hff_iff
      subst h_no
      let ρ₀' : Env P := {ρ₀ with hasFailure := ρ₀.hasFailure || false}
      have hρ₀_eq : ρ₀' = ρ₀ := by simp [ρ₀', Bool.or_false]
      -- New shape: hrest : .seq (.block .none ρ₀'.store (.stmts body ρ₀')) [loop] →*T .terminal ρ'.
      -- Step 1: Split via seqT_reaches_terminal:
      have ⟨ρ_block, h_block_term, h_loop_stmts, hlen_seq⟩ :=
        seqT_reaches_terminal extendEval hrest
      -- Step 2: Unwrap the block. Body cannot exit (by hcov).
      have h_noescape_body : ∀ lbl ρ_x,
          ¬ StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ₀') (.exiting lbl ρ_x) :=
        block_exitsCoveredByBlocks_noEscape P (EvalCmd P) extendEval body hcov ρ₀'
      have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
        blockT_reaches_terminal_noExit extendEval h_block_term h_noescape_body
      -- Step 3: Decompose [loop] ρ_block via stmtsT_cons_terminal.
      have ⟨ρ_x, h_loop_T_T, h_nil, hlen_cons⟩ :=
        stmtsT_cons_terminal extendEval h_loop_stmts
      -- h_nil is .stmts [] ρ_x →*T .terminal ρ' — must be step_stmts_nil + refl.
      have hρ_x_eq : ρ_x = ρ' := by
        match h_nil with
        | .step _ _ _ .step_stmts_nil hr2 =>
          match hr2 with
          | .refl _ => rfl
          | .step _ _ _ h _ => exact nomatch h
      subst hρ_x_eq
      -- Now: h_inner_term : .stmts body ρ₀' →*T .terminal ρ_inner
      --      heq_ρ_block : ρ_block = { ρ_inner with store := projectStore ρ₀'.store ρ_inner.store }
      --      h_loop_T_T : .stmt (.loop ...) ρ_block →*T .terminal ρ'
      have h_assume : StepKleeneStar P (EvalCmd P)
          (.stmt (.cmd (.assume "guard" g md)) ρ₀) (.terminal ρ₀) :=
        kleene_assume_terminal hg hwfb hwfcongr
      have hterm_body_eq : StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ₀) (.terminal ρ_inner) :=
        hρ₀_eq ▸ reflTransT_to_prop h_inner_term
      have h_sim_body : StepKleeneStar P (EvalCmd P) (.stmt b ρ₀) (.terminal ρ_inner) :=
        sim_body ρ₀ ρ_inner hwfb hwfv hwfcongr hterm_body_eq
      have h_kleene_assume_b : StepKleeneStar P (EvalCmd P)
          (.stmt (.seq (.cmd (.assume "guard" g md)) b) ρ₀) (.terminal ρ_inner) :=
        kleene_seq_terminal _ b ρ₀ ρ₀ ρ_inner h_assume h_sim_body
      have heval_eq : ρ_inner.eval = ρ₀.eval :=
        block_noFuncDecl_preserves_eval P (EvalCmd P) extendEval body ρ₀ ρ_inner hnofd_body hterm_body_eq
      have hwfv_inner : WellFormedSemanticEvalVal ρ_inner.eval := by
        rw [heval_eq]; exact hwfv
      have hwfcongr_inner : WellFormedSemanticEvalExprCongr ρ_inner.eval := by
        rw [heval_eq]; exact hwfcongr
      have hwfv_block : WellFormedSemanticEvalVal ρ_block.eval := by
        rw [heq_ρ_block]; exact hwfv_inner
      have hwfcongr_block : WellFormedSemanticEvalExprCongr ρ_block.eval := by
        rw [heq_ρ_block]; exact hwfcongr_inner
      have h_kleene_loop : StepKleeneStar P (EvalCmd P)
          (.stmt (.loop (.seq (.cmd (.assume "guard" g md)) b)) ρ_block) (.terminal _) :=
        ih ρ_block _ hwfv_block hwfcongr_block h_loop_T_T (by simp [ReflTransT.len] at hlen; omega)
      -- Build Kleene execution: step_loop_step → .seq (.block ρ₀.store (.stmt (assume; b) ρ₀)) (.loop ...)
      -- Then use seq+block to reach (.terminal ρ_block) via h_kleene_assume_b + project.
      have heq_ρ_block_full : ρ_block =
          { ρ_inner with store := projectStore ρ₀.store ρ_inner.store } := by
        have : ρ₀'.store = ρ₀.store := by rw [hρ₀_eq]
        rw [heq_ρ_block, this]
      have h_block_to_ρ_block : StepKleeneStar P (EvalCmd P)
          (.block ρ₀.store (.stmt (.seq (.cmd (.assume "guard" g md)) b) ρ₀))
          (.terminal ρ_block) := by
        rw [heq_ρ_block_full]
        exact kleene_block_terminal ρ₀.store _ ρ_inner h_kleene_assume_b
      have h_seq_to_ρ' : StepKleeneStar P (EvalCmd P)
          (.seq (.block ρ₀.store (.stmt (.seq (.cmd (.assume "guard" g md)) b) ρ₀))
                (.loop (.seq (.cmd (.assume "guard" g md)) b)))
          (.terminal _) :=
        ReflTrans_Transitive _ _ _ _
          (ReflTrans_Transitive _ _ _ _
            (kleene_seq_inner_star _ _ (.loop _) h_block_to_ρ_block)
            (.step _ _ _ .step_seq_done (.refl _)))
          h_kleene_loop
      exact .step _ _ _ .step_loop_step h_seq_to_ρ'

/-- Kleene loop simulation: the loop body is executed zero or more times
    non-deterministically. -/
private def loop_sim_kleene
    (extendEval : ExtendEval P)
    (m : Option P.Expr)
    (body : List (Stmt P (Cmd P))) (md : MetaData P)
    (b : KleeneStmt P (Cmd P))
    (sim_body : ∀ ρ₀ ρ',
      WellFormedSemanticEvalBool ρ₀.eval → WellFormedSemanticEvalVal ρ₀.eval →
      WellFormedSemanticEvalExprCongr ρ₀.eval →
      StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ₀) (.terminal ρ') →
      StepKleeneStar P (EvalCmd P) (.stmt b ρ₀) (.terminal ρ'))
    (hcov : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks (P := P) (CmdT := Cmd P) [] body)
    (hnofd_body : Block.noFuncDecl body = true)
    (ρ₀ ρ' : Env P) (n : Nat)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwfcongr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (hstarT : ReflTransT (StepStmt P (EvalCmd P) extendEval)
      (.stmt (.loop .nondet m ([] : List (String × P.Expr)) body md) ρ₀) (.terminal ρ'))
    (hlen : hstarT.len ≤ n) :
    StepKleeneStar P (EvalCmd P)
      (.stmt (.loop b) ρ₀) (.terminal ρ') := by
  induction n generalizing ρ₀ ρ' with
  | zero =>
    match hstarT, hlen with
    | .step _ _ _ _ _, hlen => simp [ReflTransT.len] at hlen
  | succ n ih =>
    match hstarT, hlen with
    | .step _ _ _ (@StepStmt.step_loop_nondet_exit _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure _ hff_iff) hrest, hlen =>
      have h_no : hasInvFailure = false := empty_inv_no_failure hff_iff
      subst h_no
      have hρ : ({ ρ₀ with hasFailure := ρ₀.hasFailure || false } : Env P) = ρ₀ := by
        rw [Bool.or_false]
      rw [hρ] at hrest
      match hrest with
      | .refl _ => exact .step _ _ _ .step_loop_zero (.refl _)
      | .step _ _ _ h _ => exact nomatch h
    | .step _ _ _ (@StepStmt.step_loop_nondet_enter _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure _ hff_iff) hrest, hlen =>
      have h_no : hasInvFailure = false := empty_inv_no_failure hff_iff
      subst h_no
      let ρ₀' : Env P := {ρ₀ with hasFailure := ρ₀.hasFailure || false}
      have hρ₀_eq : ρ₀' = ρ₀ := by simp [ρ₀', Bool.or_false]
      -- New shape: hrest : .seq (.block .none ρ₀'.store (.stmts body ρ₀')) [loop] →*T .terminal ρ'
      have ⟨ρ_block, h_block_term, h_loop_stmts, hlen_seq⟩ :=
        seqT_reaches_terminal extendEval hrest
      have h_noescape_body : ∀ lbl ρ_x,
          ¬ StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ₀') (.exiting lbl ρ_x) :=
        block_exitsCoveredByBlocks_noEscape P (EvalCmd P) extendEval body hcov ρ₀'
      have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
        blockT_reaches_terminal_noExit extendEval h_block_term h_noescape_body
      have ⟨ρ_x, h_loop_T_T, h_nil, hlen_cons⟩ :=
        stmtsT_cons_terminal extendEval h_loop_stmts
      have hρ_x_eq : ρ_x = ρ' := by
        match h_nil with
        | .step _ _ _ .step_stmts_nil hr2 =>
          match hr2 with
          | .refl _ => rfl
          | .step _ _ _ h _ => exact nomatch h
      subst hρ_x_eq
      have hterm_body_eq : StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ₀) (.terminal ρ_inner) :=
        hρ₀_eq ▸ reflTransT_to_prop h_inner_term
      have h_sim_body : StepKleeneStar P (EvalCmd P) (.stmt b ρ₀) (.terminal ρ_inner) :=
        sim_body ρ₀ ρ_inner hwfb hwfv hwfcongr hterm_body_eq
      have heval_eq : ρ_inner.eval = ρ₀.eval :=
        block_noFuncDecl_preserves_eval P (EvalCmd P) extendEval body ρ₀ ρ_inner hnofd_body hterm_body_eq
      have hwfv_inner : WellFormedSemanticEvalVal ρ_inner.eval := by
        rw [heval_eq]; exact hwfv
      have hwfb_inner : WellFormedSemanticEvalBool ρ_inner.eval := by
        rw [heval_eq]; exact hwfb
      have hwfcongr_inner : WellFormedSemanticEvalExprCongr ρ_inner.eval := by
        rw [heval_eq]; exact hwfcongr
      have hwfv_block : WellFormedSemanticEvalVal ρ_block.eval := by
        rw [heq_ρ_block]; exact hwfv_inner
      have hwfb_block : WellFormedSemanticEvalBool ρ_block.eval := by
        rw [heq_ρ_block]; exact hwfb_inner
      have hwfcongr_block : WellFormedSemanticEvalExprCongr ρ_block.eval := by
        rw [heq_ρ_block]; exact hwfcongr_inner
      have h_kleene_loop : StepKleeneStar P (EvalCmd P)
          (.stmt (.loop b) ρ_block) (.terminal _) :=
        ih ρ_block _ hwfb_block hwfv_block hwfcongr_block h_loop_T_T (by simp [ReflTransT.len] at hlen; omega)
      have heq_ρ_block_full : ρ_block =
          { ρ_inner with store := projectStore ρ₀.store ρ_inner.store } := by
        have : ρ₀'.store = ρ₀.store := by rw [hρ₀_eq]
        rw [heq_ρ_block, this]
      have h_block_to_ρ_block : StepKleeneStar P (EvalCmd P)
          (.block ρ₀.store (.stmt b ρ₀))
          (.terminal ρ_block) := by
        rw [heq_ρ_block_full]
        exact kleene_block_terminal ρ₀.store _ ρ_inner h_sim_body
      have h_seq_to_ρ' : StepKleeneStar P (EvalCmd P)
          (.seq (.block ρ₀.store (.stmt b ρ₀)) (.loop b))
          (.terminal _) :=
        ReflTrans_Transitive _ _ _ _
          (ReflTrans_Transitive _ _ _ _
            (kleene_seq_inner_star _ _ (.loop _) h_block_to_ρ_block)
            (.step _ _ _ .step_seq_done (.refl _)))
          h_kleene_loop
      exact .step _ _ _ .step_loop_step h_seq_to_ρ'

/-! ## Core simulation by strong induction on statement/block size -/

private theorem simulation
    (extendEval : ExtendEval P) (sz : Nat) :
    (∀ (st : Stmt P (Cmd P)) (ns : KleeneStmt P (Cmd P)),
      st.sizeOf ≤ sz → StmtToKleeneStmt st = some ns →
      ∀ (ρ₀ ρ' : Env P),
        WellFormedSemanticEvalBool ρ₀.eval → WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalExprCongr ρ₀.eval →
        StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) (.terminal ρ') →
        StepKleeneStar P (EvalCmd P) (.stmt ns ρ₀) (.terminal ρ'))
    ∧
    (∀ (bss : List (Stmt P (Cmd P))) (ns : KleeneStmt P (Cmd P)),
      Block.sizeOf bss ≤ sz → BlockToKleeneStmt bss = some ns →
      ∀ (ρ₀ ρ' : Env P),
        WellFormedSemanticEvalBool ρ₀.eval → WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalExprCongr ρ₀.eval →
        StepStmtStar P (EvalCmd P) extendEval (.stmts bss ρ₀) (.terminal ρ') →
        StepKleeneStar P (EvalCmd P) (.stmt ns ρ₀) (.terminal ρ')) := by
  induction sz with
  | zero =>
    constructor
    · intro st ns hsz ht ρ₀ ρ' _ _ _ hstar
      match st with
      | .cmd _ | .block .. | .ite .. | .loop .. | .exit .. | .funcDecl .. | .typeDecl .. =>
        simp_all [Stmt.sizeOf]
    · intro bss ns hsz ht ρ₀ ρ' hwfb hwfv hwfcongr hstar
      match bss with
      | [] =>
        simp [BlockToKleeneStmt.eq_1] at ht; subst ht
        cases hstar with
        | step _ _ _ h1 r1 => cases h1 with
          | step_stmts_nil =>
            cases r1 with
            | refl =>
              exact .step _ _ _
                (.step_cmd (EvalCmd.eval_assert_pass (eval_tt_is_tt ρ₀.eval ρ₀.store hwfv) hwfb hwfcongr))
                (by rw [assume_env_eq]; exact .refl _)
            | step _ _ _ h _ => exact nomatch h
      | s :: _ => simp_all [Block.sizeOf]
  | succ n ih =>
    constructor

    -- ═══ Statement case ═══
    · intro st ns hsz ht ρ₀ ρ' hwfb hwfv hwfcongr hstar
      match st with
      | .cmd c =>
        simp [StmtToKleeneStmt.eq_1] at ht; subst ht
        cases hstar with
        | step _ _ _ h1 r1 => cases h1 with
          | step_cmd hcmd =>
            cases r1 with
            | refl => exact .step _ _ _ (.step_cmd hcmd) (.refl _)
            | step _ _ _ h _ => exact nomatch h

      | .block _l bss _md =>
        simp [StmtToKleeneStmt] at ht
        match hb : BlockToKleeneStmt bss, ht with
        | some b, ht =>
          simp at ht; subst ht
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_block =>
              match block_reaches_terminal P (EvalCmd P) extendEval r1 with
              | .inl ⟨ρ_inner, hterm, heq_ρ'⟩ =>
                have hsz_bss : Block.sizeOf bss ≤ n := by
                  simp_all [Stmt.sizeOf]; omega
                subst heq_ρ'
                exact .step _ _ _ .step_block
                  (kleene_block_terminal ρ₀.store _ ρ_inner
                    (ih.2 bss b hsz_bss hb ρ₀ ρ_inner hwfb hwfv hwfcongr hterm))
              | .inr ⟨lbl, ρ_inner, hexit, _⟩ =>
                exact absurd hexit (block_exitsCoveredByBlocks_noEscape P (EvalCmd P) extendEval bss
                  (stmtToKleene_some_exitsCovered.blockHelper [] bss b hb) ρ₀ lbl ρ_inner)

      | .ite cond tss ess md =>
        match cond with
        | .det c =>
          have ⟨t, e, ht_tss, ht_ess, hns⟩ := ite_transform_some_det c tss ess md ns ht
          subst hns
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_ite_true hcond hwfb =>
              have : Block.sizeOf tss ≤ n := by
                simp_all [Stmt.sizeOf]; omega
              have hnd := ih.2 tss t this ht_tss ρ₀ ρ' hwfb hwfv hwfcongr r1
              have h_assume := kleene_assume_terminal (label := "true_cond") (md := md) hcond hwfb hwfcongr
              exact .step _ _ _ .step_choice_left
                (kleene_seq_terminal _ t ρ₀ ρ₀ ρ' h_assume hnd)
            | step_ite_false hcond hwfb =>
              have : Block.sizeOf ess ≤ n := by
                simp_all [Stmt.sizeOf]; omega
              have hnd := ih.2 ess e this ht_ess ρ₀ ρ' hwfb hwfv hwfcongr r1
              have h_assume := kleene_assume_terminal (label := "false_cond") (md := md) ((hwfb ρ₀.store c).2.mp hcond) hwfb hwfcongr
              exact .step _ _ _ .step_choice_right
                (kleene_seq_terminal _ e ρ₀ ρ₀ ρ' h_assume hnd)
        | .nondet =>
          have ⟨t, e, ht_tss, ht_ess, hns⟩ := ite_transform_some_nondet tss ess md ns ht
          subst hns
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_ite_nondet_true =>
              have : Block.sizeOf tss ≤ n := by
                simp_all [Stmt.sizeOf]; omega
              exact .step _ _ _ .step_choice_left
                (ih.2 tss t this ht_tss ρ₀ ρ' hwfb hwfv hwfcongr r1)
            | step_ite_nondet_false =>
              have : Block.sizeOf ess ≤ n := by
                simp_all [Stmt.sizeOf]; omega
              exact .step _ _ _ .step_choice_right
                (ih.2 ess e this ht_ess ρ₀ ρ' hwfb hwfv hwfcongr r1)

      | .loop guard m' inv body md =>
        match guard with
        | .det g =>
          have ⟨hinv_empty, b, hb, hns⟩ := loop_transform_some_det g m' inv body md ns ht
          subst hns
          subst hinv_empty
          have hsz_body : Block.sizeOf body ≤ n := by
            simp_all [Stmt.sizeOf]; omega
          have sim_body : ∀ ρ₀ ρ',
              WellFormedSemanticEvalBool ρ₀.eval → WellFormedSemanticEvalVal ρ₀.eval →
              WellFormedSemanticEvalExprCongr ρ₀.eval →
              StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ₀) (.terminal ρ') →
              StepKleeneStar P (EvalCmd P) (.stmt b ρ₀) (.terminal ρ') :=
            fun ρ₀ ρ' hwfb' hwfv' hwfcongr' h => ih.2 body b hsz_body hb ρ₀ ρ' hwfb' hwfv' hwfcongr' h
          have hcov := stmtToKleene_some_exitsCovered.blockHelper [] body b hb
          have hnofd_body : Block.noFuncDecl body = true :=
            stmtToKleene_some_noFuncDecl.blockHelper body b hb
          have hstarT := reflTrans_to_T hstar
          exact loop_sim extendEval g m' body md b sim_body hcov hnofd_body ρ₀ ρ' hstarT.len hwfv hwfcongr
            hstarT (Nat.le_refl _)
        | .nondet =>
          have ⟨hinv_empty, b, hb, hns⟩ := loop_transform_some_nondet m' inv body md ns ht
          subst hns
          subst hinv_empty
          have hsz_body : Block.sizeOf body ≤ n := by
            simp_all [Stmt.sizeOf]; omega
          have sim_body : ∀ ρ₀ ρ',
              WellFormedSemanticEvalBool ρ₀.eval → WellFormedSemanticEvalVal ρ₀.eval →
              WellFormedSemanticEvalExprCongr ρ₀.eval →
              StepStmtStar P (EvalCmd P) extendEval (.stmts body ρ₀) (.terminal ρ') →
              StepKleeneStar P (EvalCmd P) (.stmt b ρ₀) (.terminal ρ') :=
            fun ρ₀ ρ' hwfb' hwfv' hwfcongr' h => ih.2 body b hsz_body hb ρ₀ ρ' hwfb' hwfv' hwfcongr' h
          have hcov := stmtToKleene_some_exitsCovered.blockHelper [] body b hb
          have hnofd_body : Block.noFuncDecl body = true :=
            stmtToKleene_some_noFuncDecl.blockHelper body b hb
          have hstarT := reflTrans_to_T hstar
          exact loop_sim_kleene extendEval m' body md b sim_body hcov hnofd_body ρ₀ ρ'
            hstarT.len hwfb hwfv hwfcongr hstarT (Nat.le_refl _)

      | .typeDecl _ _ => simp [StmtToKleeneStmt.eq_5] at ht
      | .exit _ _ => simp [StmtToKleeneStmt.eq_6] at ht
      | .funcDecl _ _ => simp [StmtToKleeneStmt.eq_7] at ht

    -- ═══ Block case ═══
    · intro bss ns hsz ht ρ₀ ρ' hwfb hwfv hwfcongr hstar
      match bss with
      | [] =>
        simp [BlockToKleeneStmt.eq_1] at ht; subst ht
        cases hstar with
        | step _ _ _ h1 r1 => cases h1 with
          | step_stmts_nil =>
            cases r1 with
            | refl =>
              exact .step _ _ _
                (.step_cmd (EvalCmd.eval_assert_pass (eval_tt_is_tt ρ₀.eval ρ₀.store hwfv) hwfb hwfcongr))
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
            have hnofd := stmtToKleene_some_noFuncDecl s s' hs
            have heval_eq := smallStep_noFuncDecl_preserves_eval P (EvalCmd P) extendEval
              s ρ₀ ρ₁ hnofd hterm_s
            have hwfb₁ : WellFormedSemanticEvalBool ρ₁.eval := heval_eq ▸ hwfb
            have hwfv₁ : WellFormedSemanticEvalVal ρ₁.eval := heval_eq ▸ hwfv
            have hwfcongr₁ : WellFormedSemanticEvalExprCongr ρ₁.eval := heval_eq ▸ hwfcongr
            exact kleene_seq_terminal s' rest' ρ₀ ρ₁ ρ'
              (ih.1 s s' hsz_s hs ρ₀ ρ₁ hwfb hwfv hwfcongr hterm_s)
              (ih.2 rest rest' hsz_r hr ρ₁ ρ' hwfb₁ hwfv₁ hwfcongr₁ hterm_rest)

/-- If det stmt reaches terminal, Kleene transform reaches terminal. -/
theorem stmtToKleene_terminal
    (extendEval : ExtendEval P)
    (st : Stmt P (Cmd P)) (ns : KleeneStmt P (Cmd P))
    (ht : StmtToKleeneStmt st = some ns)
    (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwfcongr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) (.terminal ρ')) :
    StepKleeneStar P (EvalCmd P) (.stmt ns ρ₀) (.terminal ρ') :=
  (simulation extendEval st.sizeOf).1 st ns (Nat.le_refl _) ht ρ₀ ρ' hwfb hwfv hwfcongr hstar

/-- If det block reaches terminal, Kleene transform reaches terminal. -/
theorem blockToKleene_terminal
    (extendEval : ExtendEval P)
    (bss : List (Stmt P (Cmd P))) (ns : KleeneStmt P (Cmd P))
    (ht : BlockToKleeneStmt bss = some ns)
    (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwfcongr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.stmts bss ρ₀) (.terminal ρ')) :
    StepKleeneStar P (EvalCmd P) (.stmt ns ρ₀) (.terminal ρ') :=
  (simulation extendEval (Block.sizeOf bss)).2 bss ns (Nat.le_refl _) ht ρ₀ ρ' hwfb hwfv hwfcongr hstar

/-! ## Main theorem -/

/-- `StmtToKleeneStmt` overapproximates: any terminal env reachable from the
    deterministic execution is also reachable from the nondeterministic one,
    provided the evaluator is well-formed.
    The exiting case is ruled out since the transform returns `none` for
    `.exit` sub-statements. -/
theorem detToKleene_overapproximates
    (extendEval : ExtendEval P) :
    Transform.Overapproximates (Lang.det extendEval) (Lang.kleene (P := P))
      (StmtToKleeneStmt (P := P)) := by
  intro st ns ht ρ₀ ρ' hwfb hwfv hwfcongr
  refine ⟨?_, ?_⟩
  · exact stmtToKleene_terminal extendEval st ns ht ρ₀ ρ' hwfb hwfv hwfcongr
  · intro lbl hstar
    exact absurd hstar (exitsCoveredByBlocks_noEscape P (EvalCmd P) extendEval st
      (stmtToKleene_some_exitsCovered [] st ns ht) ρ₀ lbl ρ')

end
