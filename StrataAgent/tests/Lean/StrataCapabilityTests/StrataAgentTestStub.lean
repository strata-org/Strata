import Strata.Transform.Specification
import Strata.Transform.DetToKleene
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.StmtSemantics
import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Imperative.KleeneStmt
import Strata.DL.Imperative.KleeneStmtSemantics
import Strata.DL.Imperative.KleeneSemanticsProps
import Strata.DL.Util.Relations

open Imperative Specification

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasIntOrder P] [HasVal P] [HasBoolVal P]

/-! ## Lang instances -/

abbrev Lang.det (extendEval : ExtendEval P) : Lang P :=
  Lang.imperative P (Cmd P) (EvalCmd P) extendEval (isAtAssert P)
    (initEnvWF := fun _ _ ρ =>
      WellFormedSemanticEvalBool ρ.eval ∧
      WellFormedSemanticEvalVal ρ.eval ∧
      WellFormedSemanticEvalVar ρ.eval)

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
  initEnvWF := fun _ _ ρ =>
    WellFormedSemanticEvalBool ρ.eval ∧
    WellFormedSemanticEvalVal ρ.eval ∧
    WellFormedSemanticEvalVar ρ.eval

theorem detToKleene_overapproximates
    (extendEval : ExtendEval P) (newPrefix : String) :
    Transform.Overapproximates (Lang.det extendEval) (Lang.kleene (P := P))
      (StmtToKleeneStmt (P := P)) newPrefix := by
  sorry
