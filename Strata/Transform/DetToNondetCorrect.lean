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
  | .loop _ _ _ bss _ =>
    rw [StmtToNondetStmt.eq_4] at ht; simp [bind, Option.bind] at ht
    simp [Stmt.exitsCoveredByBlocks]
    match hb : BlockToNondetStmt bss with
    | some b => exact blockHelper labels bss b hb
    | none => simp [hb] at ht
  | .typeDecl _ _ => simp [Stmt.exitsCoveredByBlocks]
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

/-! ## Core simulation lemma -/

/-- If det stmt reaches terminal, nondet transform reaches terminal.
    The proof requires well-formedness for `assume "skip" tt` (typeDecl, empty block)
    and loop unrolling. These are left as sorry. -/
theorem stmtToNondet_terminal
    (extendEval : ExtendEval P)
    (st : Stmt P (Cmd P)) (ns : NondetStmt P (Cmd P))
    (ht : StmtToNondetStmt st = some ns)
    (ρ₀ ρ' : Env P)
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) (.terminal ρ')) :
    StepNondetStar P (EvalCmd P) (.stmt ns ρ₀) (.terminal ρ') := by
  sorry

/-- If det block reaches terminal, nondet transform reaches terminal. -/
theorem blockToNondet_terminal
    (extendEval : ExtendEval P)
    (bss : List (Stmt P (Cmd P))) (ns : NondetStmt P (Cmd P))
    (ht : BlockToNondetStmt bss = some ns)
    (ρ₀ ρ' : Env P)
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.stmts bss ρ₀) (.terminal ρ')) :
    StepNondetStar P (EvalCmd P) (.stmt ns ρ₀) (.terminal ρ') := by
  sorry

/-! ## Main theorem -/

/-- `StmtToNondetStmt` is an `Overapproximates`. -/
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
