/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.StmtSemanticsProps
public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.KleeneSemanticsProps
public import Strata.Transform.StructuredToUnstructured
public import Strata.Transform.GenSuffix
public import Strata.Transform.SpecificationProps
public import Strata.DL.Util.StringGen
public import Strata.Languages.Core.StatementSemantics
import Strata.DL.Imperative.BasicBlock
import all Strata.DL.Imperative.Cmd
import all Strata.DL.Util.Relations

/-! # Structured-to-Unstructured Transformation Correctness

This file proves that `stmtsToCFG` is semantics-preserving: the generated CFG
overapproximates the original structured statements. Specifically, any terminal
store reachable by executing the structured program is also reachable by
executing the CFG.

The top-level theorem is `structuredToUnstructured_sound_kind`.

## Proof Strategy

The proof is a forward simulation: we show that each structured execution trace
corresponds to a CFG execution trace reaching the same terminal store.

The key insight is that `stmtsToBlocks k ss exitConts accum` processes statements
backwards (CPS-style), threading a continuation label `k`. The simulation must
track the relationship between:
- The current position in the structured statement list
- The current CFG block label (entry point returned by `stmtsToBlocks`)
- The accumulated commands buffer (which becomes part of the next flushed block)

The proof proceeds by:
1. A generalized simulation lemma (`stmtsToBlocks_simulation`) over the structure
   of the statement list, parameterized by continuation and accumulator.
2. Per-constructor lemmas that show each statement kind's generated blocks
   correctly simulate that statement's structured semantics.
3. A `flushCmds` lemma that connects command accumulation to `EvalCmds`.
4. Composition via `ReflTrans` transitivity to build the full `StepCFGStar` trace.
-/

public section

namespace StructuredToUnstructuredCorrect

open Imperative Specification

/-! ## Abbreviations -/
abbrev StepDetCFGStar {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P)
    (cfg : CFG String (DetBlock String (Cmd P) P)) :=
  @StepCFGStar String (Cmd P) _ P (EvalCmd P) extendEval _ _ cfg

theorem StepDetCFGStar_trans {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {cfg : CFG String (DetBlock String (Cmd P) P)}
    {a b c : CFGConfig String (Cmd P) P}
    (h₁ : StepDetCFGStar extendEval cfg a b)
    (h₂ : StepDetCFGStar extendEval cfg b c) :
    StepDetCFGStar extendEval cfg a c :=
  ReflTrans_Transitive _ _ _ _ h₁ h₂

-- `NoGenSuffix` is defined in `Strata.Transform.GenSuffix` (a low base module
-- so multiple correctness passes can reuse it). Re-exported here so all in-file
-- and downstream `open StructuredToUnstructuredCorrect` references resolve
-- unchanged.
export Strata.Transform.GenSuffix (NoGenSuffix)

/-! ## Bridge: EvalCmds and connector to per-command StepCFG

`EvalCmds` is a structured-side helper inductive used by every simulation
lemma to package up the structured evaluation of an accumulated command list.
We bridge it into the new per-command `StepCFG` by lifting each
`eval_cmds_some` step into one `StepCFG.step_cmd` step inside `.inBlock`. -/

inductive EvalCmds
    {CmdT : Type}
    (P : PureExpr)
    (EvalCmdR : EvalCmdParam P CmdT) :
    SemanticEval P → SemanticStore P → List CmdT → SemanticStore P → Bool → Prop where
  | eval_cmds_none :
    EvalCmds P EvalCmdR δ σ [] σ false
  | eval_cmds_some :
    EvalCmdR δ σ c σ' failed →
    EvalCmds P EvalCmdR δ σ' cs σ'' failed' →
    EvalCmds P EvalCmdR δ σ (c :: cs) σ'' (failed || failed')

/-- Bridge: lift an `EvalCmds` derivation for the command list `cs` into a
chain of `StepCFG.step_cmd` steps inside `.inBlock`, threading the residual
list and accumulating failure on the right via `||`. -/
theorem EvalCmds_to_StepCFG_chain {P : PureExpr} [HasFvar P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {cfg : CFG String (DetBlock String (Cmd P) P)}
    {δ : SemanticEval P} {σ σ' : SemanticStore P}
    {cs : List (Cmd P)} {f : Bool}
    (h_cmds : EvalCmds P (EvalCmd P) δ σ cs σ' f) :
    ∀ (t : String) (tr : DetTransferCmd String P) (f_base : Bool),
      StepCFGStar P (EvalCmd P) extendEval cfg
        (.inBlock t cs tr σ f_base)
        (.inBlock t [] tr σ' (f_base || f)) := by
  induction h_cmds with
  | eval_cmds_none =>
    intro t tr f_base
    -- (.inBlock t [] tr σ f_base) ↦* (.inBlock t [] tr σ (f_base || false))
    rw [Bool.or_false]
    exact ReflTrans.refl _
  | eval_cmds_some hcmd hcmds ih =>
    rename_i δ' σ_in c σ_mid failed cs_t σ_out f_t
    intro t tr f_base
    -- one step_cmd consumes c
    have h1 : StepCFG (l := String) (CmdT := Cmd P) P (EvalCmd P) extendEval cfg
        (.inBlock t (c :: cs_t) tr σ_in f_base)
        (.inBlock t cs_t tr σ_mid (f_base || failed)) :=
      StepCFG.step_cmd (extendEval := extendEval) hcmd
    have h2 := ih t tr (f_base || failed)
    -- Recompute the failure flag: ((f_base || failed) || f_t) = (f_base || (failed || f_t))
    have h_or :
        ((f_base || failed) || f_t) = (f_base || (failed || f_t)) :=
      Bool.or_assoc _ _ _
    rw [h_or] at h2
    exact ReflTrans.step _ _ _ h1 h2

/-- Run a deterministic block from `.atBlock t` to `.atBlock tlbl` via the
true branch of a `condGoto`: fetch + chain + goto_true. -/
theorem run_block_goto_true {P : PureExpr} [HasFvar P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {cfg : CFG String (DetBlock String (Cmd P) P)}
    {δ : SemanticEval P} {σ σ' : SemanticStore P}
    {cs : List (Cmd P)} {c : P.Expr} {tlbl elbl : String} {md : MetaData P}
    {f_base f : Bool} {t : String}
    (h_lkp : List.lookup t cfg.blocks = .some ⟨cs, .condGoto c tlbl elbl md⟩)
    (h_cmds : EvalCmds P (EvalCmd P) δ σ cs σ' f)
    (h_cond : δ σ' c = .some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool δ)
    (hwfcongr : WellFormedSemanticEvalExprCongr δ) :
    StepCFGStar P (EvalCmd P) extendEval cfg
      (.atBlock t σ f_base)
      (.atBlock tlbl σ' (f_base || f)) := by
  have h_fetch : StepCFG (l := String) (CmdT := Cmd P) P (EvalCmd P) extendEval cfg
      (.atBlock t σ f_base)
      (.inBlock t cs (.condGoto c tlbl elbl md) σ f_base) :=
    StepCFG.fetch (extendEval := extendEval) h_lkp
  have h_chain := EvalCmds_to_StepCFG_chain (extendEval := extendEval)
                    (cfg := cfg) h_cmds t (.condGoto c tlbl elbl md) f_base
  have h_goto : StepCFG (l := String) (CmdT := Cmd P) P (EvalCmd P) extendEval cfg
      (.inBlock t [] (.condGoto c tlbl elbl md) σ' (f_base || f))
      (.atBlock tlbl σ' (f_base || f)) :=
    StepCFG.goto_true (extendEval := extendEval) h_cond hwfb hwfcongr
  exact ReflTrans.step _ _ _ h_fetch
    (ReflTrans_Transitive _ _ _ _ h_chain
      (ReflTrans.step _ _ _ h_goto (ReflTrans.refl _)))

/-- Run a deterministic block from `.atBlock t` to `.atBlock elbl` via the
false branch of a `condGoto`: fetch + chain + goto_false. -/
theorem run_block_goto_false {P : PureExpr} [HasFvar P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {cfg : CFG String (DetBlock String (Cmd P) P)}
    {δ : SemanticEval P} {σ σ' : SemanticStore P}
    {cs : List (Cmd P)} {c : P.Expr} {tlbl elbl : String} {md : MetaData P}
    {f_base f : Bool} {t : String}
    (h_lkp : List.lookup t cfg.blocks = .some ⟨cs, .condGoto c tlbl elbl md⟩)
    (h_cmds : EvalCmds P (EvalCmd P) δ σ cs σ' f)
    (h_cond : δ σ' c = .some HasBool.ff)
    (hwfb : WellFormedSemanticEvalBool δ)
    (hwfcongr : WellFormedSemanticEvalExprCongr δ) :
    StepCFGStar P (EvalCmd P) extendEval cfg
      (.atBlock t σ f_base)
      (.atBlock elbl σ' (f_base || f)) := by
  have h_fetch : StepCFG (l := String) (CmdT := Cmd P) P (EvalCmd P) extendEval cfg
      (.atBlock t σ f_base)
      (.inBlock t cs (.condGoto c tlbl elbl md) σ f_base) :=
    StepCFG.fetch (extendEval := extendEval) h_lkp
  have h_chain := EvalCmds_to_StepCFG_chain (extendEval := extendEval)
                    (cfg := cfg) h_cmds t (.condGoto c tlbl elbl md) f_base
  have h_goto : StepCFG (l := String) (CmdT := Cmd P) P (EvalCmd P) extendEval cfg
      (.inBlock t [] (.condGoto c tlbl elbl md) σ' (f_base || f))
      (.atBlock elbl σ' (f_base || f)) :=
    StepCFG.goto_false (extendEval := extendEval) h_cond hwfb hwfcongr
  exact ReflTrans.step _ _ _ h_fetch
    (ReflTrans_Transitive _ _ _ _ h_chain
      (ReflTrans.step _ _ _ h_goto (ReflTrans.refl _)))

/-- Run a deterministic block from `.atBlock t` to `.terminal`: fetch + chain
+ finish. -/
theorem run_block_finish {P : PureExpr} [HasFvar P] [HasNot P] [HasVarsPure P P.Expr]
    {extendEval : ExtendEval P}
    {cfg : CFG String (DetBlock String (Cmd P) P)}
    {δ : SemanticEval P} {σ σ' : SemanticStore P}
    {cs : List (Cmd P)} {md : MetaData P}
    {f_base f : Bool} {t : String}
    (h_lkp : List.lookup t cfg.blocks = .some ⟨cs, .finish md⟩)
    (h_cmds : EvalCmds P (EvalCmd P) δ σ cs σ' f) :
    StepCFGStar P (EvalCmd P) extendEval cfg
      (.atBlock t σ f_base)
      (.terminal σ' (f_base || f)) := by
  have h_fetch : StepCFG (l := String) (CmdT := Cmd P) P (EvalCmd P) extendEval cfg
      (.atBlock t σ f_base)
      (.inBlock t cs (.finish md) σ f_base) :=
    StepCFG.fetch (extendEval := extendEval) h_lkp
  have h_chain := EvalCmds_to_StepCFG_chain (extendEval := extendEval)
                    (cfg := cfg) h_cmds t (.finish md) f_base
  have h_finish : StepCFG (l := String) (CmdT := Cmd P) P (EvalCmd P) extendEval cfg
      (.inBlock t [] (.finish md) σ' (f_base || f))
      (.terminal σ' (f_base || f)) :=
    StepCFG.finish (extendEval := extendEval)
  exact ReflTrans.step _ _ _ h_fetch
    (ReflTrans_Transitive _ _ _ _ h_chain
      (ReflTrans.step _ _ _ h_finish (ReflTrans.refl _)))

theorem stmts_nil_terminal {P : PureExpr} [HasBool P] [HasNot P]
    {CmdT : Type}
    (EvalCmdR : EvalCmdParam P CmdT)
    (extendEval : ExtendEval P)
    (ρ₀ ρ' : Env P)
    (h : StepStmtStar P EvalCmdR extendEval (.stmts [] ρ₀) (.terminal ρ')) :
    ρ₀ = ρ' := by
  rcases h
  rename_i h₁ h₂ h₃
  cases h₂
  cases h₃
  · rfl
  · rename_i h₁ _
    cases h₁

theorem EvalCmds_snoc {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    (δ : SemanticEval P) (σ σ' σ'' : SemanticStore P)
    (cs : List (Cmd P)) (c : Cmd P) (f₁ f₂ : Bool)
    (h₁ : EvalCmds P (@EvalCmd P _ _ _ _) δ σ cs σ' f₁)
    (h₂ : @EvalCmd P _ _ _ _ δ σ' c σ'' f₂) :
    EvalCmds P (@EvalCmd P _ _ _ _) δ σ (cs ++ [c]) σ'' (f₁ || f₂) := by
  induction cs generalizing σ f₁ with
  | nil =>
    cases h₁
    simp
    have : f₂ = (f₂ || false) := by simp
    rw [this]
    exact EvalCmds.eval_cmds_some h₂ EvalCmds.eval_cmds_none
  | cons c' cs' ih =>
    cases h₁ with
    | eval_cmds_some hcmd hrest =>
      simp only [List.cons_append]
      rw [Bool.or_assoc]
      exact EvalCmds.eval_cmds_some hcmd (ih _ _ hrest)

theorem EvalCmds_inv {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    (δ : SemanticEval P) (σ σ' : SemanticStore P) (f : Bool)
    (h : EvalCmds P (@EvalCmd P _ _ _ _) δ σ [] σ' f) :
    σ = σ' ∧ f = false := by
  cases h;
  exact ⟨ rfl, rfl ⟩

/-! ## Agreement-preserving replay of `EvalCmd` / `EvalCmds`

A structured-side `EvalCmd c σ_struct₀ σ_struct₁ failed` can be replayed on
a CFG-side store `σ_cfg₀` that agrees with `σ_struct₀` (in the
`StoreAgreement` sense), yielding some `σ_cfg₁` that agrees with `σ_struct₁`.

For the `eval_init` case, we additionally require that the variable being
initialized is fresh in `σ_cfg₀` (otherwise the CFG-side `InitState`
constructor cannot fire).  At the higher-level chained version
(`EvalCmds_under_agreement`), this freshness is supplied by `Block.uniqueInits`
+ the property that any `init` only succeeds if the variable was unset.
-/

/-- Pointwise equality of two stores on the variables of a single expression
follows from `StoreAgreement` plus `isDefined` of those variables. -/
private theorem store_agreement_pointwise_on_expr_vars
    {P : PureExpr} [HasVarsPure P P.Expr]
    (σ_struct σ_cfg : SemanticStore P) (e : P.Expr)
    (h_agree : StoreAgreement σ_struct σ_cfg)
    (h_def : isDefined σ_struct (HasVarsPure.getVars e)) :
    ∀ x ∈ HasVarsPure.getVars e, σ_struct x = σ_cfg x := by
  intro x hx
  have h_def_x : isDefined σ_struct [x] := by
    intro v hv
    rw [List.mem_singleton] at hv
    rw [hv]
    exact h_def x hx
  exact h_agree x h_def_x

private theorem Cmds.definedVars_cons
    {P : PureExpr} (c : Cmd P) (cs : List (Cmd P)) :
    Cmds.definedVars (c :: cs) = Cmd.definedVars c ++ Cmds.definedVars cs := by
  rw [Cmds.definedVars.eq_def]

private theorem Cmds.modifiedVars_cons
    {P : PureExpr} (c : Cmd P) (cs : List (Cmd P)) :
    Cmds.modifiedVars (c :: cs) = Cmd.modifiedVars c ++ Cmds.modifiedVars cs := by
  rw [Cmds.modifiedVars.eq_def]

-- Local exposed mirror of `Block.modifiedVars` from `Stmt.lean` for the
-- transform proof. The library version is not `@[expose]`, which prevents
-- unfolding inside this file's mutual block. This local version is
-- `@[expose]` so its match cases are definitionally available.
-- Defined as `transformModVars` to avoid namespace clash with the library.
mutual
@[expose] def transformStmtModVars {P : PureExpr} :
    Stmt P (Cmd P) → List P.Ident
  | .cmd c => Cmd.modifiedVars c
  | .block _ bss _ => transformBlockModVars bss
  | .ite _ tss ess _ => transformBlockModVars tss ++ transformBlockModVars ess
  | .loop _ _ _ bss _ => transformBlockModVars bss
  | .exit _ _ => []
  | .funcDecl _ _ => []
  | .typeDecl _ _ => []
@[expose] def transformBlockModVars {P : PureExpr} :
    List (Stmt P (Cmd P)) → List P.Ident
  | [] => []
  | s :: rest => transformStmtModVars s ++ transformBlockModVars rest
end

-- Equation lemmas for transformStmtModVars / transformBlockModVars
-- (definitional via @[expose]).
private theorem transformBlockModVars_cons {P : PureExpr}
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) :
    transformBlockModVars (s :: rest) =
    transformStmtModVars s ++ transformBlockModVars rest := rfl

private theorem transformStmtModVars_cmd {P : PureExpr} (c : Cmd P) :
    transformStmtModVars (P := P) (Stmt.cmd c) = Cmd.modifiedVars c := rfl

private theorem transformStmtModVars_block {P : PureExpr}
    (label : String) (body : List (Stmt P (Cmd P))) (md : MetaData P) :
    transformStmtModVars (P := P) (Stmt.block label body md) =
    transformBlockModVars body := rfl

private theorem transformStmtModVars_ite {P : PureExpr}
    (c : ExprOrNondet P) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P) :
    transformStmtModVars (P := P) (Stmt.ite c tss ess md) =
    transformBlockModVars tss ++ transformBlockModVars ess := rfl

private theorem transformStmtModVars_typeDecl {P : PureExpr}
    (tc : TypeConstructor) (md : MetaData P) :
    transformStmtModVars (P := P) (Stmt.typeDecl tc md : Stmt P (Cmd P)) = [] := rfl

private theorem transformStmtModVars_loop {P : PureExpr}
    (c : ExprOrNondet P) (m : Option P.Expr) (is : List (String × P.Expr))
    (body : List (Stmt P (Cmd P))) (md : MetaData P) :
    transformStmtModVars (P := P) (Stmt.loop c m is body md) =
    transformBlockModVars body := rfl

/-- Single-command agreement-preservation. -/
private theorem EvalCmd_under_agreement {P : PureExpr}
    [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    (δ : SemanticEval P) (σ_struct₀ σ_cfg₀ : SemanticStore P)
    (c : Cmd P) (σ_struct₁ : SemanticStore P) (failed : Bool)
    (h_agree : StoreAgreement σ_struct₀ σ_cfg₀)
    (h_eval : @EvalCmd P _ _ _ _ δ σ_struct₀ c σ_struct₁ failed)
    (h_wf_def : WellFormedSemanticEvalDef δ)
    (h_congr : WellFormedSemanticEvalExprCongr δ)
    (h_fresh : ∀ x ∈ Cmd.definedVars c, σ_cfg₀ x = none) :
    ∃ σ_cfg₁, @EvalCmd P _ _ _ _ δ σ_cfg₀ c σ_cfg₁ failed
            ∧ StoreAgreement σ_struct₁ σ_cfg₁ := by
  cases h_eval with
  | eval_init heval hinit hwfvar hwfcongr =>
    -- Constructor: EvalCmd δ σ_struct₀ (.init x ty (.det e) md) σ_struct₁ false
    -- rename_i introduces in order: ty, md, x, v, e
    rename_i ty md x v e
    -- Need δ σ_cfg₀ e = some v. Use congr + agreement on e's vars.
    have h_def_e : isDefined σ_struct₀ (HasVarsPure.getVars e) :=
      h_wf_def e v σ_struct₀ heval
    have h_pointwise :
        ∀ y ∈ HasVarsPure.getVars e, σ_struct₀ y = σ_cfg₀ y :=
      store_agreement_pointwise_on_expr_vars σ_struct₀ σ_cfg₀ e h_agree h_def_e
    have h_eval_cfg : δ σ_cfg₀ e = .some v := by
      rw [← heval]; exact (h_congr e σ_struct₀ σ_cfg₀ h_pointwise).symm
    -- Witness σ_cfg₁
    let σ_cfg₁ : SemanticStore P := fun y => if y = x then some v else σ_cfg₀ y
    have h_x_fresh : σ_cfg₀ x = none := by
      apply h_fresh x
      have h_dv_eq : Cmd.definedVars (Cmd.init x ty (ExprOrNondet.det e) md) = [x] := by
        with_unfolding_all rfl
      rw [h_dv_eq]
      exact List.mem_singleton.mpr rfl
    have h_cfg_x : σ_cfg₁ x = some v := by
      show (if x = x then some v else σ_cfg₀ x) = some v
      simp
    have h_cfg_other : ∀ y, x ≠ y → σ_cfg₁ y = σ_cfg₀ y := by
      intro y hxy
      show (if y = x then some v else σ_cfg₀ y) = σ_cfg₀ y
      have hne : ¬ (y = x) := fun h => hxy h.symm
      rw [if_neg hne]
    have h_init_cfg : InitState P σ_cfg₀ x v σ_cfg₁ :=
      InitState.init h_x_fresh h_cfg_x h_cfg_other
    refine ⟨σ_cfg₁, EvalCmd.eval_init h_eval_cfg h_init_cfg hwfvar hwfcongr, ?_⟩
    -- StoreAgreement σ_struct₁ σ_cfg₁
    intro y h_def_y
    cases hinit with
    | init h_xn h_xv h_other =>
      by_cases hyx : y = x
      · subst hyx
        rw [h_xv, h_cfg_x]
      · have h_struct_y : σ_struct₁ y = σ_struct₀ y := h_other y (fun h => hyx h.symm)
        have h_cfg_y : σ_cfg₁ y = σ_cfg₀ y := h_cfg_other y (fun h => hyx h.symm)
        rw [h_struct_y, h_cfg_y]
        have h_def_y' : isDefined σ_struct₀ [y] := by
          intro w hw
          rw [List.mem_singleton] at hw
          rw [hw]
          have h_y_def_in_σ' : (σ_struct₁ y).isSome = true :=
            h_def_y y (List.mem_singleton.mpr rfl)
          exact h_struct_y ▸ h_y_def_in_σ'
        exact h_agree y h_def_y'
  | eval_init_unconstrained hinit hwfvar =>
    rename_i ty md x v
    let σ_cfg₁ : SemanticStore P := fun y => if y = x then some v else σ_cfg₀ y
    have h_x_fresh : σ_cfg₀ x = none := by
      apply h_fresh x
      have h_dv_eq : Cmd.definedVars (Cmd.init x ty ExprOrNondet.nondet md) = [x] := by
        with_unfolding_all rfl
      rw [h_dv_eq]
      exact List.mem_singleton.mpr rfl
    have h_cfg_x : σ_cfg₁ x = some v := by
      show (if x = x then some v else σ_cfg₀ x) = some v
      simp
    have h_cfg_other : ∀ y, x ≠ y → σ_cfg₁ y = σ_cfg₀ y := by
      intro y hxy
      show (if y = x then some v else σ_cfg₀ y) = σ_cfg₀ y
      have hne : ¬ (y = x) := fun h => hxy h.symm
      rw [if_neg hne]
    have h_init_cfg : InitState P σ_cfg₀ x v σ_cfg₁ :=
      InitState.init h_x_fresh h_cfg_x h_cfg_other
    refine ⟨σ_cfg₁, EvalCmd.eval_init_unconstrained h_init_cfg hwfvar, ?_⟩
    intro y h_def_y
    cases hinit with
    | init h_xn h_xv h_other =>
      by_cases hyx : y = x
      · subst hyx
        rw [h_xv, h_cfg_x]
      · have h_struct_y : σ_struct₁ y = σ_struct₀ y := h_other y (fun h => hyx h.symm)
        have h_cfg_y : σ_cfg₁ y = σ_cfg₀ y := h_cfg_other y (fun h => hyx h.symm)
        rw [h_struct_y, h_cfg_y]
        have h_def_y' : isDefined σ_struct₀ [y] := by
          intro w hw
          rw [List.mem_singleton] at hw
          rw [hw]
          have h_y_def_in_σ' : (σ_struct₁ y).isSome = true :=
            h_def_y y (List.mem_singleton.mpr rfl)
          exact h_struct_y ▸ h_y_def_in_σ'
        exact h_agree y h_def_y'
  | eval_set heval hupdate hwfvar hwfcongr =>
    rename_i md x v e
    have h_def_e : isDefined σ_struct₀ (HasVarsPure.getVars e) :=
      h_wf_def e v σ_struct₀ heval
    have h_pointwise :
        ∀ y ∈ HasVarsPure.getVars e, σ_struct₀ y = σ_cfg₀ y :=
      store_agreement_pointwise_on_expr_vars σ_struct₀ σ_cfg₀ e h_agree h_def_e
    have h_eval_cfg : δ σ_cfg₀ e = .some v := by
      rw [← heval]; exact (h_congr e σ_struct₀ σ_cfg₀ h_pointwise).symm
    cases hupdate with
    | update h_xv' h_xv h_other =>
      rename_i v'
      have h_x_def_struct : isDefined σ_struct₀ [x] := by
        intro y hy
        rw [List.mem_singleton] at hy
        rw [hy, h_xv']
        rfl
      have h_cfg_x_old : σ_cfg₀ x = some v' := by
        have h_eq : σ_struct₀ x = σ_cfg₀ x := h_agree x h_x_def_struct
        rw [← h_eq]; exact h_xv'
      let σ_cfg₁ : SemanticStore P := fun y => if y = x then some v else σ_cfg₀ y
      have h_cfg_x_new : σ_cfg₁ x = some v := by
        show (if x = x then some v else σ_cfg₀ x) = some v
        simp
      have h_cfg_other : ∀ y, x ≠ y → σ_cfg₁ y = σ_cfg₀ y := by
        intro y hxy
        show (if y = x then some v else σ_cfg₀ y) = σ_cfg₀ y
        have hne : ¬ (y = x) := fun h => hxy h.symm
        rw [if_neg hne]
      have h_upd : UpdateState P σ_cfg₀ x v σ_cfg₁ :=
        UpdateState.update h_cfg_x_old h_cfg_x_new h_cfg_other
      refine ⟨σ_cfg₁, EvalCmd.eval_set h_eval_cfg h_upd hwfvar hwfcongr, ?_⟩
      intro y h_def_y
      by_cases hyx : y = x
      · subst hyx
        rw [h_xv, h_cfg_x_new]
      · have h_struct_y : σ_struct₁ y = σ_struct₀ y := h_other y (fun h => hyx h.symm)
        have h_cfg_y : σ_cfg₁ y = σ_cfg₀ y := h_cfg_other y (fun h => hyx h.symm)
        rw [h_struct_y, h_cfg_y]
        have h_def_y' : isDefined σ_struct₀ [y] := by
          intro w hw
          rw [List.mem_singleton] at hw
          rw [hw]
          have h_y_def_in_σ' : (σ_struct₁ y).isSome = true :=
            h_def_y y (List.mem_singleton.mpr rfl)
          exact h_struct_y ▸ h_y_def_in_σ'
        exact h_agree y h_def_y'
  | eval_set_nondet hupdate hwfvar =>
    rename_i md x v
    cases hupdate with
    | update h_xv' h_xv h_other =>
      rename_i v'
      have h_x_def_struct : isDefined σ_struct₀ [x] := by
        intro y hy
        rw [List.mem_singleton] at hy
        rw [hy, h_xv']
        rfl
      have h_cfg_x_old : σ_cfg₀ x = some v' := by
        have h_eq : σ_struct₀ x = σ_cfg₀ x := h_agree x h_x_def_struct
        rw [← h_eq]; exact h_xv'
      let σ_cfg₁ : SemanticStore P := fun y => if y = x then some v else σ_cfg₀ y
      have h_cfg_x_new : σ_cfg₁ x = some v := by
        show (if x = x then some v else σ_cfg₀ x) = some v
        simp
      have h_cfg_other : ∀ y, x ≠ y → σ_cfg₁ y = σ_cfg₀ y := by
        intro y hxy
        show (if y = x then some v else σ_cfg₀ y) = σ_cfg₀ y
        have hne : ¬ (y = x) := fun h => hxy h.symm
        rw [if_neg hne]
      have h_upd : UpdateState P σ_cfg₀ x v σ_cfg₁ :=
        UpdateState.update h_cfg_x_old h_cfg_x_new h_cfg_other
      refine ⟨σ_cfg₁, EvalCmd.eval_set_nondet h_upd hwfvar, ?_⟩
      intro y h_def_y
      by_cases hyx : y = x
      · subst hyx
        rw [h_xv, h_cfg_x_new]
      · have h_struct_y : σ_struct₁ y = σ_struct₀ y := h_other y (fun h => hyx h.symm)
        have h_cfg_y : σ_cfg₁ y = σ_cfg₀ y := h_cfg_other y (fun h => hyx h.symm)
        rw [h_struct_y, h_cfg_y]
        have h_def_y' : isDefined σ_struct₀ [y] := by
          intro w hw
          rw [List.mem_singleton] at hw
          rw [hw]
          have h_y_def_in_σ' : (σ_struct₁ y).isSome = true :=
            h_def_y y (List.mem_singleton.mpr rfl)
          exact h_struct_y ▸ h_y_def_in_σ'
        exact h_agree y h_def_y'
  | eval_assert_pass hcond hwfb hwfcongr =>
    rename_i l md e
    have h_def_e : isDefined σ_struct₀ (HasVarsPure.getVars e) :=
      h_wf_def e HasBool.tt σ_struct₀ hcond
    have h_pointwise :
        ∀ y ∈ HasVarsPure.getVars e, σ_struct₀ y = σ_cfg₀ y :=
      store_agreement_pointwise_on_expr_vars σ_struct₀ σ_cfg₀ e h_agree h_def_e
    have h_eval_cfg : δ σ_cfg₀ e = .some HasBool.tt := by
      rw [← hcond]; exact (h_congr e σ_struct₀ σ_cfg₀ h_pointwise).symm
    exact ⟨σ_cfg₀, EvalCmd.eval_assert_pass h_eval_cfg hwfb hwfcongr, h_agree⟩
  | eval_assert_fail hcond hwfb hwfcongr =>
    rename_i l md e
    have h_def_e : isDefined σ_struct₀ (HasVarsPure.getVars e) :=
      h_wf_def e HasBool.ff σ_struct₀ hcond
    have h_pointwise :
        ∀ y ∈ HasVarsPure.getVars e, σ_struct₀ y = σ_cfg₀ y :=
      store_agreement_pointwise_on_expr_vars σ_struct₀ σ_cfg₀ e h_agree h_def_e
    have h_eval_cfg : δ σ_cfg₀ e = .some HasBool.ff := by
      rw [← hcond]; exact (h_congr e σ_struct₀ σ_cfg₀ h_pointwise).symm
    exact ⟨σ_cfg₀, EvalCmd.eval_assert_fail h_eval_cfg hwfb hwfcongr, h_agree⟩
  | eval_assume hcond hwfb hwfcongr =>
    rename_i l md e
    have h_def_e : isDefined σ_struct₀ (HasVarsPure.getVars e) :=
      h_wf_def e HasBool.tt σ_struct₀ hcond
    have h_pointwise :
        ∀ y ∈ HasVarsPure.getVars e, σ_struct₀ y = σ_cfg₀ y :=
      store_agreement_pointwise_on_expr_vars σ_struct₀ σ_cfg₀ e h_agree h_def_e
    have h_eval_cfg : δ σ_cfg₀ e = .some HasBool.tt := by
      rw [← hcond]; exact (h_congr e σ_struct₀ σ_cfg₀ h_pointwise).symm
    exact ⟨σ_cfg₀, EvalCmd.eval_assume h_eval_cfg hwfb hwfcongr, h_agree⟩
  | eval_cover hwfb =>
    exact ⟨σ_cfg₀, EvalCmd.eval_cover hwfb, h_agree⟩

/-- A helper: if `EvalCmd c σ σ' f` succeeds and `x` is not in `c`'s definedVars
(so `c` does not init x), and `σ x = none`, then `σ' x = none`.  This holds because
`c` either doesn't touch x, or modifies x via `set` (which requires `σ x = some _`,
contradicting `σ x = none`). -/
private theorem agreement_helper_unchanged_at_x {P : PureExpr}
    [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {δ : SemanticEval P} {σ σ' : SemanticStore P} {c : Cmd P} {failed : Bool}
    {x : P.Ident}
    (h_eval : @EvalCmd P _ _ _ _ δ σ c σ' failed)
    (h_x_not_def : x ∉ Cmd.definedVars c)
    (h_σ_x : σ x = none) :
    σ' x = none := by
  cases h_eval with
  | eval_init heval hinit hwfvar hwfcongr =>
    cases hinit with
    | init h_xn h_xv h_other =>
      -- After cases on hinit, anonymous vars (from EvalCmd's eval_init constructor):
      -- `x✝² : P.Ty`, `x✝¹ : MetaData`, `x✝ : P.Ident`, `v✝ e✝ : P.Expr`.
      rename_i ty md x_init v e
      have h_x_ne : x_init ≠ x := by
        intro h_eq
        apply h_x_not_def
        show x ∈ Cmd.definedVars (Cmd.init x_init ty (ExprOrNondet.det e) md)
        have h_dv :
            Cmd.definedVars (Cmd.init x_init ty (ExprOrNondet.det e) md) = [x_init] := by
          with_unfolding_all rfl
        rw [h_dv, h_eq]
        exact List.mem_singleton.mpr rfl
      rw [h_other x h_x_ne]; exact h_σ_x
  | eval_init_unconstrained hinit hwfvar =>
    cases hinit with
    | init h_xn h_xv h_other =>
      rename_i ty md x_init v
      have h_x_ne : x_init ≠ x := by
        intro h_eq
        apply h_x_not_def
        show x ∈ Cmd.definedVars (Cmd.init x_init ty ExprOrNondet.nondet md)
        have h_dv :
            Cmd.definedVars (Cmd.init x_init ty ExprOrNondet.nondet md) = [x_init] := by
          with_unfolding_all rfl
        rw [h_dv, h_eq]
        exact List.mem_singleton.mpr rfl
      rw [h_other x h_x_ne]; exact h_σ_x
  | eval_set heval hupdate hwfvar hwfcongr =>
    cases hupdate with
    | update h_xv' h_xv h_other =>
      rename_i md x_set v e v'
      by_cases h_eq : x_set = x
      · subst h_eq
        rw [h_σ_x] at h_xv'
        cases h_xv'
      · rw [h_other x h_eq]; exact h_σ_x
  | eval_set_nondet hupdate hwfvar =>
    cases hupdate with
    | update h_xv' h_xv h_other =>
      rename_i md x_set v v'
      by_cases h_eq : x_set = x
      · subst h_eq
        rw [h_σ_x] at h_xv'
        cases h_xv'
      · rw [h_other x h_eq]; exact h_σ_x
  | eval_assert_pass _ _ _ => exact h_σ_x
  | eval_assert_fail _ _ _ => exact h_σ_x
  | eval_assume _ _ _ => exact h_σ_x
  | eval_cover _ => exact h_σ_x

/-- Multi-command extension of `agreement_helper_unchanged_at_x`: if `EvalCmds`
takes σ to σ' over a list `cmds`, and `x` is not in `cmds.definedVars`, and
`σ x = none`, then `σ' x = none`. By induction on `EvalCmds`. -/
private theorem agreement_helper_unchanged_at_x_multi {P : PureExpr}
    [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {δ : SemanticEval P} {σ σ' : SemanticStore P} {cmds : List (Cmd P)} {failed : Bool}
    {x : P.Ident}
    (h_eval : EvalCmds P (@EvalCmd P _ _ _ _) δ σ cmds σ' failed)
    (h_x_not_def : x ∉ Cmds.definedVars cmds)
    (h_σ_x : σ x = none) :
    σ' x = none := by
  induction h_eval with
  | eval_cmds_none => exact h_σ_x
  | eval_cmds_some hcmd hrest ih =>
    rename_i σ_a c σ_b _ cs σ_c _
    -- σ_a x = none, want σ_c x = none
    -- step 1: σ_b x = none from single-cmd helper
    have h_x_not_in_head : x ∉ Cmd.definedVars c := by
      intro h_x_in_head
      apply h_x_not_def
      rw [Cmds.definedVars_cons]
      exact List.mem_append_left _ h_x_in_head
    have h_σ_b_x : σ_b x = none :=
      agreement_helper_unchanged_at_x hcmd h_x_not_in_head h_σ_x
    -- step 2: σ_c x = none from inductive hypothesis on rest
    have h_x_not_in_tail : x ∉ Cmds.definedVars cs := by
      intro h_x_in_tail
      apply h_x_not_def
      rw [Cmds.definedVars_cons]
      exact List.mem_append_right _ h_x_in_tail
    exact ih h_x_not_in_tail h_σ_b_x

/-- Multi-command agreement-preservation, by induction on `cs`. -/
private theorem EvalCmds_under_agreement {P : PureExpr}
    [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    (δ : SemanticEval P)
    (cs : List (Cmd P))
    (h_wf_def : WellFormedSemanticEvalDef δ)
    (h_congr : WellFormedSemanticEvalExprCongr δ) :
    ∀ (σ_struct₀ σ_cfg₀ σ_struct₁ : SemanticStore P) (failed : Bool),
      StoreAgreement σ_struct₀ σ_cfg₀ →
      EvalCmds P (@EvalCmd P _ _ _ _) δ σ_struct₀ cs σ_struct₁ failed →
      (∀ x ∈ Cmds.definedVars cs, σ_cfg₀ x = none) →
      (Cmds.definedVars cs).Nodup →
      ∃ σ_cfg₁, EvalCmds P (@EvalCmd P _ _ _ _) δ σ_cfg₀ cs σ_cfg₁ failed
              ∧ StoreAgreement σ_struct₁ σ_cfg₁ := by
  induction cs with
  | nil =>
    intro σ_struct₀ σ_cfg₀ σ_struct₁ failed h_agree h_eval _ _
    cases h_eval
    exact ⟨σ_cfg₀, EvalCmds.eval_cmds_none, h_agree⟩
  | cons c cs ih =>
    intro σ_struct₀ σ_cfg₀ σ_struct₁ failed h_agree h_eval h_fresh h_unique
    cases h_eval with
    | eval_cmds_some hcmd hrest =>
      rename_i σ_mid f f'
      have h_fresh_head : ∀ x ∈ Cmd.definedVars c, σ_cfg₀ x = none := by
        intro x hx
        have hx' : x ∈ Cmds.definedVars (c :: cs) := by
          rw [Cmds.definedVars_cons]
          exact List.mem_append_left _ hx
        exact h_fresh x hx'
      have h_fresh_tail_init : ∀ x ∈ Cmds.definedVars cs, σ_cfg₀ x = none := by
        intro x hx
        have hx' : x ∈ Cmds.definedVars (c :: cs) := by
          rw [Cmds.definedVars_cons]
          exact List.mem_append_right _ hx
        exact h_fresh x hx'
      -- Apply EvalCmd_under_agreement to head cmd c.
      have ⟨σ_cfg_mid, h_cmd_cfg, h_agree_mid⟩ :=
        EvalCmd_under_agreement δ σ_struct₀ σ_cfg₀ c σ_mid f h_agree hcmd h_wf_def h_congr
          h_fresh_head
      -- Now we need σ_cfg_mid to satisfy the freshness for the tail cs.
      have h_fresh_tail : ∀ x ∈ Cmds.definedVars cs, σ_cfg_mid x = none := by
        intro x hx
        have h_x_not_in_head : x ∉ Cmd.definedVars c := by
          intro h_x_in_head
          have h_nodup_split :
              ∀ a ∈ Cmd.definedVars c, ∀ b ∈ Cmds.definedVars cs, a ≠ b := by
            have h_unique' : (Cmds.definedVars (c :: cs)).Nodup := h_unique
            rw [Cmds.definedVars_cons] at h_unique'
            exact (List.nodup_append.mp h_unique').2.2
          exact h_nodup_split x h_x_in_head x hx rfl
        have h_cfg₀_x : σ_cfg₀ x = none := h_fresh_tail_init x hx
        exact agreement_helper_unchanged_at_x h_cmd_cfg h_x_not_in_head h_cfg₀_x
      have h_unique_tail : (Cmds.definedVars cs).Nodup := by
        have : (Cmds.definedVars (c :: cs)).Nodup := h_unique
        rw [Cmds.definedVars_cons] at this
        exact (List.nodup_append.mp this).2.1
      have ⟨σ_cfg_end, h_rest_cfg, h_agree_end⟩ :=
        ih σ_mid σ_cfg_mid σ_struct₁ f' h_agree_mid hrest h_fresh_tail
          h_unique_tail
      exact ⟨σ_cfg_end, EvalCmds.eval_cmds_some h_cmd_cfg h_rest_cfg, h_agree_end⟩

theorem single_cmd_eval {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P)
    (c : Cmd P) (ρ₀ ρ₁ : Env P)
    (h : StepStmtStar P (@EvalCmd P _ _ _ _) extendEval
      (.stmts [.cmd c] ρ₀) (.terminal ρ₁)) :
    ∃ σ' failed, @EvalCmd P _ _ _ _ ρ₀.eval ρ₀.store c σ' failed ∧
      ρ₁.store = σ' ∧ ρ₁.eval = ρ₀.eval ∧
      ρ₁.hasFailure = (ρ₀.hasFailure || failed) := by
  cases h with
  | step _ _ _ hstep1 hrest1 =>
    cases hstep1 with
    | step_stmts_cons =>
      have ⟨ρ_mid, h_inner, h_tail⟩ := seq_reaches_terminal P (@EvalCmd P _ _ _ _) extendEval hrest1
      have h_eq := stmts_nil_terminal (@EvalCmd P _ _ _ _) extendEval _ _ h_tail
      subst h_eq
      cases h_inner with
      | step _ _ _ hstep2 hrest2 =>
        cases hstep2 with
        | step_cmd heval =>
          cases hrest2 with
          | refl => exact ⟨_, _, heval, rfl, rfl, rfl⟩
          | step _ _ _ hstep3 _ => exact absurd hstep3 (by intro h; cases h)

/-! ## Sub-theorems for ite case -/

/-- If a list of pairs has unique keys (Nodup), then membership implies
the key can be looked up to find the corresponding value. -/
private theorem List.lookup_of_mem_nodup
    {α β : Type} [BEq α] [LawfulBEq α] (l : List (α × β))
    (h_nodup : (l.map Prod.fst).Nodup)
    (k : α) (v : β)
    (h_mem : (k, v) ∈ l) :
    l.lookup k = some v := by
  induction l with
  | nil => cases h_mem
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    rw [List.mem_cons] at h_mem
    rcases h_mem with h_eq | h_tl
    · simp [List.lookup]; injection h_eq with h1 h2; subst h1; subst h2; simp
    · simp at h_nodup
      obtain ⟨h_not_in, h_nodup_tl⟩ := h_nodup
      have h_neq : ¬(k == k') = true := by
        intro h_eq
        rw [beq_iff_eq] at h_eq
        subst h_eq
        exact h_not_in v h_tl
      simp [List.lookup, h_neq]
      exact ih h_nodup_tl h_tl

/-! ### Invariant about `stmtsToBlocks` and `flushCmds`

`GenInv gen gen' blocks` packages the invariant tying together a
`StringGenState` transition `gen → gen'` with the produced `blocks`. It
extends `StringGenState.GenStep` (well-formedness preservation + monotone
label list) with two block-specific properties:
- every block label was generated during this call (fresh w.r.t. `gen`),
- block labels are pairwise distinct. -/

/-- The invariant for `stmtsToBlocks` / `flushCmds` outputs.

`GenInv gen gen' userLabels blocks` means: starting in state `gen`, the
computation produced state `gen'` and emitted `blocks`, where every block
label is either freshly generated (in `stringGens gen' \ stringGens gen`)
or one of the supplied `userLabels` (provided by the user via `Stmt.block`).

`userLabels` is a list of user-supplied strings, all of which:
- are shape-free (no `_<digits>` suffix), and
- are not in `stringGens gen'` (hence not in `stringGens gen` either),
- are pairwise distinct.

This lets the `Stmt.block` case introduce a user label into the output
without breaking the freshness/Nodup tracking. -/
private structure GenInv {P : PureExpr} (gen gen' : StringGenState)
    (userLabels : List String)
    (blocks : List (String × DetBlock String (Cmd P) P)) : Prop
    extends StringGenState.GenStep gen gen' where
  /-- WF is preserved (and hence we also get WF gen' = wf_mono of gen). -/
  wf_in : StringGenState.WF gen
  /-- Every user label is shape-free. -/
  user_shape : ∀ l ∈ userLabels, ¬ String.HasUnderscoreDigitSuffix l
  /-- Every user label is absent from `stringGens gen'`. -/
  user_disj : ∀ l ∈ userLabels, l ∉ StringGenState.stringGens gen'
  /-- User labels are pairwise distinct. -/
  user_nodup : userLabels.Nodup
  /-- Each block label is either generated by this call or one of the user labels. -/
  fresh : ∀ l ∈ blocks.map Prod.fst,
    (l ∈ StringGenState.stringGens gen' ∧ l ∉ StringGenState.stringGens gen)
    ∨ l ∈ userLabels
  /-- Block labels are pairwise distinct. -/
  nodup : (blocks.map Prod.fst).Nodup

/-- Convenience: `WF gen'` follows from `GenInv` (since `WF gen` is carried
and `gen → gen'` is a `GenStep`). -/
private theorem GenInv.wf_out {P : PureExpr}
    {gen gen' : StringGenState} {userLabels : List String}
    {blocks : List (String × DetBlock String (Cmd P) P)}
    (h : @GenInv P gen gen' userLabels blocks) :
    StringGenState.WF gen' :=
  h.wf_mono h.wf_in

/-- A shape-free user label is never in `stringGens` of any WF state. -/
private theorem userLabel_not_in_stringGens_of_shape_free
    {σ : StringGenState} (hwf : StringGenState.WF σ)
    {l : String} (h_shape : ¬ String.HasUnderscoreDigitSuffix l) :
    l ∉ StringGenState.stringGens σ :=
  StringGenState.not_mem_stringGens_of_not_hasUnderscoreDigitSuffix hwf h_shape

/-- The invariant for `flushCmds`: emitted blocks have fresh, unique labels.
`flushCmds` produces no user-labeled blocks, so `userLabels = []`. -/
private theorem flushCmds_invariant {P : PureExpr} [HasBool P]
    (pfx : String) (accum : List (Cmd P))
    (tr? : Option (DetTransferCmd String P)) (k : String)
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : flushCmds pfx accum tr? k gen = ((entry, blocks), gen'))
    (hwf : StringGenState.WF gen) :
    @GenInv P gen gen' [] blocks := by
  unfold flushCmds at h_gen
  cases h_tr : tr? with
  | none =>
    rw [h_tr] at h_gen
    simp only at h_gen
    by_cases h_empty : accum.isEmpty
    · rw [if_pos h_empty] at h_gen
      simp only [pure, StateT.pure] at h_gen
      injection h_gen with h_pair h_gen_eq
      injection h_pair with h_entry_eq h_blocks_eq
      subst h_blocks_eq; subst h_gen_eq
      refine ⟨StringGenState.GenStep.refl _, hwf, ?_, ?_, ?_, ?_, ?_⟩
      · intros l hl; simp at hl
      · intros l hl; simp at hl
      · simp
      · intros l hl; simp at hl
      · simp
    · rw [if_neg h_empty] at h_gen
      simp only [bind, StateT.bind, pure, StateT.pure, Id] at h_gen
      injection h_gen with h_pair h_gen_eq
      injection h_pair with h_entry_eq h_blocks_eq
      subst h_entry_eq; subst h_blocks_eq; subst h_gen_eq
      refine ⟨StringGenState.GenStep.of_gen pfx gen, hwf, ?_, ?_, ?_, ?_, ?_⟩
      · intros l hl; simp at hl
      · intros l hl; simp at hl
      · simp
      · intro l hl
        simp at hl; subst hl
        left
        refine ⟨?_, ?_⟩
        · rw [StringGenState.stringGens_gen]; exact List.mem_cons.mpr (Or.inl rfl)
        · exact StringGenState.stringGens_gen_not_in pfx gen hwf
      · simp
  | some tr =>
    rw [h_tr] at h_gen
    simp only [bind, StateT.bind, pure, StateT.pure, Id] at h_gen
    injection h_gen with h_pair h_gen_eq
    injection h_pair with h_entry_eq h_blocks_eq
    subst h_entry_eq; subst h_blocks_eq; subst h_gen_eq
    refine ⟨StringGenState.GenStep.of_gen pfx gen, hwf, ?_, ?_, ?_, ?_, ?_⟩
    · intros l hl; simp at hl
    · intros l hl; simp at hl
    · simp
    · intro l hl
      simp at hl; subst hl
      left
      refine ⟨?_, ?_⟩
      · rw [StringGenState.stringGens_gen]; exact List.mem_cons.mpr (Or.inl rfl)
      · exact StringGenState.stringGens_gen_not_in pfx gen hwf
    · simp

/-- Composition lemma: if both `gen → gen_mid` (with `blocks₁`) and
`gen_mid → gen'` (with `blocks₂`) satisfy `GenInv`, then `gen → gen'`
with `blocks₁ ++ blocks₂` does too. -/
private theorem GenInv.trans {P : PureExpr}
    (gen gen_mid gen' : StringGenState)
    (userLabels₁ userLabels₂ : List String)
    (blocks₁ blocks₂ : List (String × DetBlock String (Cmd P) P))
    (h₁ : @GenInv P gen gen_mid userLabels₁ blocks₁)
    (h₂ : @GenInv P gen_mid gen' userLabels₂ blocks₂)
    -- Cross-disjointness premise: user labels in the two halves don't overlap.
    (h_user_disj : ∀ l ∈ userLabels₁, l ∉ userLabels₂) :
    @GenInv P gen gen' (userLabels₁ ++ userLabels₂) (blocks₁ ++ blocks₂) := by
  have hwf_mid : StringGenState.WF gen_mid := h₁.wf_out
  have hwf_out : StringGenState.WF gen' := h₂.wf_out
  refine ⟨h₁.toGenStep.trans h₂.toGenStep, h₁.wf_in, ?_, ?_, ?_, ?_, ?_⟩
  · -- user_shape
    intro l hl
    rw [List.mem_append] at hl
    exact hl.elim (fun h => h₁.user_shape l h) (fun h => h₂.user_shape l h)
  · -- user_disj: user labels are absent from stringGens gen'.
    -- Shape-free + WF gen' ⇒ not in stringGens gen'.
    intro l hl
    rw [List.mem_append] at hl
    have h_shape : ¬ String.HasUnderscoreDigitSuffix l := by
      exact hl.elim (fun h => h₁.user_shape l h) (fun h => h₂.user_shape l h)
    exact userLabel_not_in_stringGens_of_shape_free hwf_out h_shape
  · -- user_nodup
    rw [List.nodup_append]
    refine ⟨h₁.user_nodup, h₂.user_nodup, ?_⟩
    intro x hx y hy h_eq
    subst h_eq
    exact h_user_disj x hx hy
  · -- fresh
    intro l hl
    rw [List.map_append, List.mem_append] at hl
    rcases hl with h | h
    · rcases h₁.fresh l h with h_gen | h_user
      · left
        exact ⟨h₂.subset h_gen.1, h_gen.2⟩
      · right
        exact List.mem_append.mpr (Or.inl h_user)
    · rcases h₂.fresh l h with h_gen | h_user
      · left
        refine ⟨h_gen.1, ?_⟩
        intro h_in_gen
        exact h_gen.2 (h₁.subset h_in_gen)
      · right
        exact List.mem_append.mpr (Or.inr h_user)
  · -- nodup
    rw [List.map_append, List.nodup_append]
    refine ⟨h₁.nodup, h₂.nodup, ?_⟩
    intro x hx y hy h_eq
    subst h_eq
    rcases h₁.fresh x hx with h_x_gen₁ | h_x_user₁
    · rcases h₂.fresh x hy with h_x_gen₂ | h_x_user₂
      · exact h_x_gen₂.2 h_x_gen₁.1
      · -- x ∈ stringGens gen_mid (from h_x_gen₁.1) but x ∈ userLabels₂ (shape-free).
        -- WF gen_mid + shape-free ⇒ x ∉ stringGens gen_mid. Contradiction.
        exact (userLabel_not_in_stringGens_of_shape_free hwf_mid
                (h₂.user_shape x h_x_user₂)) h_x_gen₁.1 |>.elim
    · rcases h₂.fresh x hy with h_x_gen₂ | h_x_user₂
      · -- x ∈ userLabels₁ (shape-free), but x ∈ stringGens gen'.
        -- WF gen' + shape-free ⇒ x ∉ stringGens gen'. Contradiction.
        exact (userLabel_not_in_stringGens_of_shape_free hwf_out
                (h₁.user_shape x h_x_user₁)) h_x_gen₂.1 |>.elim
      · exact h_user_disj x h_x_user₁ h_x_user₂

/-- `GenInv` is closed under list permutation of the blocks (the freshness
and Nodup properties are permutation-invariant). -/
private theorem GenInv.perm {P : PureExpr}
    (gen gen' : StringGenState)
    (userLabels : List String)
    (blocks₁ blocks₂ : List (String × DetBlock String (Cmd P) P))
    (h : @GenInv P gen gen' userLabels blocks₁)
    (hperm : blocks₁.Perm blocks₂) :
    @GenInv P gen gen' userLabels blocks₂ := by
  refine ⟨h.toGenStep, h.wf_in, h.user_shape, h.user_disj, h.user_nodup, ?_, ?_⟩
  · intro l hl
    apply h.fresh
    rw [List.Perm.mem_iff (List.Perm.map _ hperm)]
    exact hl
  · rw [(List.Perm.map _ hperm).nodup_iff.symm]
    exact h.nodup

/-- Convenience: extending `GenInv` by prepending a single new block whose
label was just generated by `gen` from `gen_mid`. -/
private theorem GenInv.cons_gen {P : PureExpr}
    (gen gen_mid gen' : StringGenState)
    (userLabels : List String)
    (blocks : List (String × DetBlock String (Cmd P) P))
    (l : String) (b : DetBlock String (Cmd P) P)
    (hwf_gen : StringGenState.WF gen)
    (h_step : StringGenState.GenStep gen gen_mid)
    (h_blocks : @GenInv P gen_mid gen' userLabels blocks)
    (h_l_in : l ∈ StringGenState.stringGens gen')
    (h_l_notin_gen : l ∉ StringGenState.stringGens gen)
    (h_l_notin_blocks : l ∉ blocks.map Prod.fst) :
    @GenInv P gen gen' userLabels ((l, b) :: blocks) := by
  refine ⟨h_step.trans h_blocks.toGenStep, hwf_gen,
          h_blocks.user_shape, h_blocks.user_disj, h_blocks.user_nodup, ?_, ?_⟩
  · intro x hx
    rw [List.map_cons, List.mem_cons] at hx
    rcases hx with h_eq | h_in
    · subst h_eq
      exact .inl ⟨h_l_in, h_l_notin_gen⟩
    · rcases h_blocks.fresh _ h_in with h_gen | h_user
      · refine .inl ⟨h_gen.1, ?_⟩
        intro hgen
        exact h_gen.2 (h_step.subset hgen)
      · exact .inr h_user
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨h_l_notin_blocks, h_blocks.nodup⟩

/-- An empty-block invariant: a pure `GenStep gen gen'` (without emitting any
blocks or user labels) yields a trivial `GenInv`. Useful for absorbing
intermediate `gen` calls between sub-computations. -/
private theorem GenInv.empty_step {P : PureExpr}
    (gen gen' : StringGenState)
    (hwf : StringGenState.WF gen)
    (h_step : StringGenState.GenStep gen gen') :
    @GenInv P gen gen' [] [] := by
  refine ⟨h_step, hwf, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl; simp at hl
  · intro l hl; simp at hl
  · simp
  · intro l hl; simp at hl
  · simp

/-- A more general `mapM_genStep` for any function in `StringGenM` whose
single-step behaviour is a `GenStep`. The lemma traces through the entire
list, building a `GenStep` from the initial state to the final state. -/
private theorem mapM_genStep {α β : Type}
    (f : α → LabelGen.StringGenM β)
    (h_step : ∀ (a : α) (gen gen' : StringGenState) (b : β),
                f a gen = (b, gen') → StringGenState.GenStep gen gen')
    (xs : List α)
    (gen gen' : StringGenState) (ys : List β)
    (h_eq : xs.mapM f gen = (ys, gen')) :
    StringGenState.GenStep gen gen' := by
  -- Use List.mapM_cons / mapM_nil rewrites to reduce.
  induction xs generalizing gen gen' ys with
  | nil =>
    rw [List.mapM_nil] at h_eq
    -- (pure []) gen = ([], gen) for the StateM monad
    simp only [pure, StateT.pure] at h_eq
    have h_gen' : gen = gen' := (Prod.mk.inj h_eq).2
    exact h_gen' ▸ StringGenState.GenStep.refl gen
  | cons hd tl ih =>
    rw [List.mapM_cons] at h_eq
    simp only [bind, StateT.bind, pure, StateT.pure] at h_eq
    generalize h_f : f hd gen = r1 at h_eq
    obtain ⟨y, gen_mid⟩ := r1
    simp only at h_eq
    generalize h_tail : tl.mapM f gen_mid = r2 at h_eq
    obtain ⟨ys', gen_end⟩ := r2
    simp only at h_eq
    have h_gen' : gen_end = gen' := (Prod.mk.inj h_eq).2
    have h1 : StringGenState.GenStep gen gen_mid := h_step hd gen gen_mid y h_f
    have h2 : StringGenState.GenStep gen_mid gen_end :=
      ih gen_mid gen_end ys' h_tail
    exact h_gen' ▸ h1.trans h2

/-- Weakening: if `userLabels` shrinks (a sublist), the invariant still holds
provided the additional shape/disjointness/Nodup constraints transfer. The
common usage: a parent list of user labels is provided that includes the
actual user labels in `blocks` plus extras. -/
private theorem GenInv.weaken_userLabels {P : PureExpr}
    (gen gen' : StringGenState)
    (userLabels userLabels' : List String)
    (blocks : List (String × DetBlock String (Cmd P) P))
    (h : @GenInv P gen gen' userLabels blocks)
    (h_subset : ∀ l ∈ userLabels, l ∈ userLabels')
    (h_shape' : ∀ l ∈ userLabels', ¬ String.HasUnderscoreDigitSuffix l)
    (h_disj' : ∀ l ∈ userLabels', l ∉ StringGenState.stringGens gen')
    (h_nodup' : userLabels'.Nodup) :
    @GenInv P gen gen' userLabels' blocks := by
  refine ⟨h.toGenStep, h.wf_in, h_shape', h_disj', h_nodup', ?_, h.nodup⟩
  intro l hl
  cases h.fresh l hl with
  | inl h_gen => exact .inl h_gen
  | inr h_user => exact .inr (h_subset l h_user)

/-- Prepending a user-labeled block to `GenInv`. The new label `l` becomes
part of `userLabels` of the result. -/
private theorem GenInv.cons_user {P : PureExpr}
    (gen gen' : StringGenState)
    (userLabels : List String)
    (blocks : List (String × DetBlock String (Cmd P) P))
    (l : String) (b : DetBlock String (Cmd P) P)
    (h_blocks : @GenInv P gen gen' userLabels blocks)
    (h_l_shape : ¬ String.HasUnderscoreDigitSuffix l)
    (h_l_notin_user : l ∉ userLabels)
    (h_l_notin_blocks : l ∉ blocks.map Prod.fst) :
    @GenInv P gen gen' (l :: userLabels) ((l, b) :: blocks) := by
  have hwf_out := h_blocks.wf_out
  refine ⟨h_blocks.toGenStep, h_blocks.wf_in, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [List.mem_cons] at hx
    cases hx with
    | inl h_eq => subst h_eq; exact h_l_shape
    | inr h_in => exact h_blocks.user_shape x h_in
  · intro x hx
    rw [List.mem_cons] at hx
    rcases hx with h_eq | h_in
    · subst h_eq
      exact userLabel_not_in_stringGens_of_shape_free hwf_out h_l_shape
    · exact h_blocks.user_disj x h_in
  · rw [List.nodup_cons]
    exact ⟨h_l_notin_user, h_blocks.user_nodup⟩
  · intro x hx
    rw [List.map_cons, List.mem_cons] at hx
    rcases hx with h_eq | h_in
    · subst h_eq
      exact .inr (List.mem_cons.mpr (Or.inl rfl))
    · cases h_blocks.fresh _ h_in with
      | inl h_gen => exact .inl h_gen
      | inr h_user => exact .inr (List.mem_cons.mpr (Or.inr h_user))
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨h_l_notin_blocks, h_blocks.nodup⟩

/-- All user-provided `Stmt.block` labels appearing in a list of statements.
Uses a `where`-helper that recurses on the statement constructor; the helper
calls back into the list-level recursion for nested statement lists. -/
@[expose] def Block.userBlockLabels {P : PureExpr} :
    List (Stmt P (Cmd P)) → List String
  | [] => []
  | s :: rest => stmtUserBlockLabels s ++ Block.userBlockLabels rest
where
  stmtUserBlockLabels : Stmt P (Cmd P) → List String
    | .block l ss _ => l :: Block.userBlockLabels ss
    | .ite _ tss ess _ => Block.userBlockLabels tss ++ Block.userBlockLabels ess
    | .loop _ _ _ ss _ => Block.userBlockLabels ss
    | _ => []

/-! Equational lemmas for `userBlockLabels` (proved via `unfold`). -/

theorem Block.userBlockLabels_block_cons {P : PureExpr}
    (l : String) (bss : List (Stmt P (Cmd P))) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) :
    Block.userBlockLabels (.block l bss md :: rest) =
      (l :: Block.userBlockLabels bss) ++ Block.userBlockLabels rest := by
  show Block.userBlockLabels.stmtUserBlockLabels _ ++ _ = _
  rfl

theorem Block.userBlockLabels_ite_cons {P : PureExpr}
    (c : Imperative.ExprOrNondet P) (tss ess : List (Stmt P (Cmd P)))
    (md : MetaData P) (rest : List (Stmt P (Cmd P))) :
    Block.userBlockLabels (.ite c tss ess md :: rest) =
      (Block.userBlockLabels tss ++ Block.userBlockLabels ess)
        ++ Block.userBlockLabels rest := by
  show Block.userBlockLabels.stmtUserBlockLabels _ ++ _ = _
  rfl

theorem Block.userBlockLabels_loop_cons {P : PureExpr}
    (c : Imperative.ExprOrNondet P) (m : Option P.Expr)
    (is : List (String × P.Expr)) (bss : List (Stmt P (Cmd P)))
    (md : MetaData P) (rest : List (Stmt P (Cmd P))) :
    Block.userBlockLabels (.loop c m is bss md :: rest) =
      Block.userBlockLabels bss ++ Block.userBlockLabels rest := by
  show Block.userBlockLabels.stmtUserBlockLabels _ ++ _ = _
  rfl

theorem Block.userBlockLabels_cmd_cons {P : PureExpr}
    (c : Cmd P) (rest : List (Stmt P (Cmd P))) :
    Block.userBlockLabels (.cmd c :: rest) = Block.userBlockLabels rest := by
  show Block.userBlockLabels.stmtUserBlockLabels _ ++ _ = _
  rfl

theorem Block.userBlockLabels_funcDecl_cons {P : PureExpr}
    (decl : Imperative.PureFunc P) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) :
    Block.userBlockLabels (.funcDecl decl md :: rest) =
      Block.userBlockLabels rest := by
  show Block.userBlockLabels.stmtUserBlockLabels _ ++ _ = _
  rfl

theorem Block.userBlockLabels_typeDecl_cons {P : PureExpr}
    (tc : TypeConstructor) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) :
    Block.userBlockLabels (.typeDecl tc md :: rest) =
      Block.userBlockLabels rest := by
  show Block.userBlockLabels.stmtUserBlockLabels _ ++ _ = _
  rfl

theorem Block.userBlockLabels_exit_cons {P : PureExpr}
    (l : String) (md : MetaData P) (rest : List (Stmt P (Cmd P))) :
    Block.userBlockLabels (.exit l md :: rest) =
      Block.userBlockLabels rest := by
  show Block.userBlockLabels.stmtUserBlockLabels _ ++ _ = _
  rfl

/-- A predicate stating that user-provided block labels:
1. are shape-free (do not have the `_<digits>` generator suffix), and
2. consequently do not collide with any label in any WF generator state, and
3. are pairwise distinct (no two `Stmt.block` constructors share a label).

This is the precondition needed for `stmtsToBlocks` to produce a CFG with
unique block labels. The shape-free clause is what cleanly distinguishes user
labels from generator output: client code chooses readable labels (e.g.
`"my_block"`) which never collide with `gen`'s `pf_42`-style output. -/
@[expose] def Block.userLabelsDisjoint {P : PureExpr}
    (ss : List (Stmt P (Cmd P))) (gen' : StringGenState) : Prop :=
  (∀ l ∈ Block.userBlockLabels ss, ¬ String.HasUnderscoreDigitSuffix l) ∧
  (Block.userBlockLabels ss).Nodup ∧
  (∀ l ∈ Block.userBlockLabels ss, l ∉ StringGenState.stringGens gen')

/-- The gen-free core of `userLabelsDisjoint`: user-provided block labels are
shape-free (do not have the `_<digits>` generator suffix) and pairwise distinct.

This drops `userLabelsDisjoint`'s third conjunct (the universal "no user label
is in `gen'`'s `stringGens`"), which is *derivable* from the shape-free conjunct
together with well-formedness of `gen'`: a shape-free label is never in the
`stringGens` of any WF state.  Stating the precondition in this gen-free form lets
callers discharge it without quantifying over generator states. -/
@[expose] def Block.userLabelsShapeNodup {P : PureExpr}
    (ss : List (Stmt P (Cmd P))) : Prop :=
  (∀ l ∈ Block.userBlockLabels ss, ¬ String.HasUnderscoreDigitSuffix l) ∧
  (Block.userBlockLabels ss).Nodup

/-- `userLabelsShapeNodup` recovers `userLabelsDisjoint` at any WF generator
state: the third (disjointness) conjunct follows from the shape-free conjunct via
`userLabel_not_in_stringGens_of_shape_free`. -/
theorem Block.userLabelsDisjoint_of_shapeNodup {P : PureExpr}
    (ss : List (Stmt P (Cmd P)))
    (h : Block.userLabelsShapeNodup ss) :
    ∀ gen : StringGenState, StringGenState.WF gen →
      Block.userLabelsDisjoint ss gen := by
  intro gen hwf
  refine ⟨h.1, h.2, ?_⟩
  intro l hl
  exact userLabel_not_in_stringGens_of_shape_free hwf (h.1 l hl)

/-- `userLabelsDisjoint` distributes over `cons`: if a longer list is
disjoint, so is the tail. -/
private theorem Block.userLabelsDisjoint_tail {P : PureExpr}
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (s :: rest) gen') :
    Block.userLabelsDisjoint rest gen' := by
  obtain ⟨h_shape, h_nodup, h_disj⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro l hl; apply h_shape; unfold Block.userBlockLabels
    exact List.mem_append.mpr (Or.inr hl)
  · unfold Block.userBlockLabels at h_nodup
    exact (List.nodup_append.mp h_nodup).2.1
  · intro l hl; apply h_disj; unfold Block.userBlockLabels
    exact List.mem_append.mpr (Or.inr hl)

/-- `userLabelsDisjoint` is antitone in the generator state: a smaller
generator state can only have fewer labels, so disjointness is preserved
when restricting to a subset. -/
private theorem Block.userLabelsDisjoint_mono {P : PureExpr}
    (ss : List (Stmt P (Cmd P))) (gen gen' : StringGenState)
    (h : Block.userLabelsDisjoint ss gen')
    (h_sub : StringGenState.stringGens gen ⊆ StringGenState.stringGens gen') :
    Block.userLabelsDisjoint ss gen := by
  obtain ⟨h_shape, h_nodup, h_disj⟩ := h
  refine ⟨h_shape, h_nodup, ?_⟩
  intro l hl h_in_gen
  exact h_disj l hl (h_sub h_in_gen)

/-- `userLabelsDisjoint` for the body of a `Stmt.block`: if the outer
`Stmt.block l bss md :: rest` is disjoint, so are `bss`'s user labels. -/
private theorem Block.userLabelsDisjoint_block_body {P : PureExpr}
    (l : String) (bss : List (Stmt P (Cmd P))) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (Stmt.block l bss md :: rest) gen') :
    Block.userLabelsDisjoint bss gen' := by
  obtain ⟨h_shape, h_nodup, h_disj⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    apply h_shape
    unfold Block.userBlockLabels Block.userBlockLabels.stmtUserBlockLabels
    exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inr hx)))
  · -- bss's labels appear inside (l :: bss-labels) ++ rest-labels, so Nodup follows
    unfold Block.userBlockLabels Block.userBlockLabels.stmtUserBlockLabels at h_nodup
    have := (List.nodup_append.mp h_nodup).1
    exact (List.nodup_cons.mp this).2
  · intro x hx
    apply h_disj
    unfold Block.userBlockLabels Block.userBlockLabels.stmtUserBlockLabels
    exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inr hx)))

/-- `userLabelsDisjoint` for the then/else branches of a `Stmt.ite`. -/
private theorem Block.userLabelsDisjoint_ite_then {P : PureExpr}
    (c : Imperative.ExprOrNondet P) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (Stmt.ite c tss ess md :: rest) gen') :
    Block.userLabelsDisjoint tss gen' := by
  obtain ⟨h_shape, h_nodup, h_disj⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; apply h_shape
    unfold Block.userBlockLabels Block.userBlockLabels.stmtUserBlockLabels
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hx)))
  · unfold Block.userBlockLabels Block.userBlockLabels.stmtUserBlockLabels at h_nodup
    have := (List.nodup_append.mp h_nodup).1
    exact (List.nodup_append.mp this).1
  · intro x hx; apply h_disj
    unfold Block.userBlockLabels Block.userBlockLabels.stmtUserBlockLabels
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hx)))

private theorem Block.userLabelsDisjoint_ite_else {P : PureExpr}
    (c : Imperative.ExprOrNondet P) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (Stmt.ite c tss ess md :: rest) gen') :
    Block.userLabelsDisjoint ess gen' := by
  obtain ⟨h_shape, h_nodup, h_disj⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; apply h_shape
    unfold Block.userBlockLabels Block.userBlockLabels.stmtUserBlockLabels
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hx)))
  · unfold Block.userBlockLabels Block.userBlockLabels.stmtUserBlockLabels at h_nodup
    have := (List.nodup_append.mp h_nodup).1
    exact (List.nodup_append.mp this).2.1
  · intro x hx; apply h_disj
    unfold Block.userBlockLabels Block.userBlockLabels.stmtUserBlockLabels
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hx)))

/-- `userLabelsDisjoint` for the body of a `Stmt.loop`. -/
private theorem Block.userLabelsDisjoint_loop_body {P : PureExpr}
    (c : Imperative.ExprOrNondet P) (m : Option P.Expr) (is : List (String × P.Expr))
    (bss : List (Stmt P (Cmd P))) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (Stmt.loop c m is bss md :: rest) gen') :
    Block.userLabelsDisjoint bss gen' := by
  obtain ⟨h_shape, h_nodup, h_disj⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; apply h_shape
    unfold Block.userBlockLabels Block.userBlockLabels.stmtUserBlockLabels
    exact List.mem_append.mpr (Or.inl hx)
  · unfold Block.userBlockLabels Block.userBlockLabels.stmtUserBlockLabels at h_nodup
    exact (List.nodup_append.mp h_nodup).1
  · intro x hx; apply h_disj
    unfold Block.userBlockLabels Block.userBlockLabels.stmtUserBlockLabels
    exact List.mem_append.mpr (Or.inl hx)

/-- Cross-disjointness for `ite`: `tss`'s and `ess`'s user labels are
disjoint (lifted from the outer `Nodup`). -/
private theorem Block.userLabels_ite_cross_disj {P : PureExpr}
    (c : Imperative.ExprOrNondet P) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (Stmt.ite c tss ess md :: rest) gen') :
    (∀ x ∈ Block.userBlockLabels tss, x ∉ Block.userBlockLabels ess) ∧
    (∀ x ∈ Block.userBlockLabels tss, x ∉ Block.userBlockLabels rest) ∧
    (∀ x ∈ Block.userBlockLabels ess, x ∉ Block.userBlockLabels rest) := by
  obtain ⟨_, h_nodup, _⟩ := h
  rw [Block.userBlockLabels_ite_cons] at h_nodup
  -- h_nodup : ((tss-lbls ++ ess-lbls) ++ rest-lbls).Nodup
  have h_outer := List.nodup_append.mp h_nodup
  -- left = tss-lbls ++ ess-lbls; right = rest-lbls
  have h_te_nodup := h_outer.1
  have h_te_inner := List.nodup_append.mp h_te_nodup
  refine ⟨?_, ?_, ?_⟩
  · -- tss vs ess
    intro x h_t h_e
    exact h_te_inner.2.2 x h_t x h_e rfl
  · -- tss vs rest: x ∈ tss-lbls ⊆ left, x ∈ rest-lbls = right
    intro x h_t h_r
    exact h_outer.2.2 x (List.mem_append.mpr (Or.inl h_t)) x h_r rfl
  · -- ess vs rest
    intro x h_e h_r
    exact h_outer.2.2 x (List.mem_append.mpr (Or.inr h_e)) x h_r rfl

/-- Cross-disjointness for `loop`: `bss`'s user labels are disjoint from
`rest`'s user labels. -/
private theorem Block.userLabels_loop_cross_disj {P : PureExpr}
    (c : Imperative.ExprOrNondet P) (m : Option P.Expr) (is : List (String × P.Expr))
    (bss : List (Stmt P (Cmd P))) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (Stmt.loop c m is bss md :: rest) gen') :
    ∀ x ∈ Block.userBlockLabels bss, x ∉ Block.userBlockLabels rest := by
  obtain ⟨_, h_nodup, _⟩ := h
  rw [Block.userBlockLabels_loop_cons] at h_nodup
  have h_outer := List.nodup_append.mp h_nodup
  intro x h_b h_r
  exact h_outer.2.2 x h_b x h_r rfl

/-- The label `l` of a `Stmt.block l bss md` is in the user-label list, so we
can lift the shape-free, Nodup, and disjointness facts to it. -/
private theorem Block.userLabel_of_block_head {P : PureExpr}
    (l : String) (bss : List (Stmt P (Cmd P))) (md : MetaData P)
    (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (Stmt.block l bss md :: rest) gen') :
    ¬ String.HasUnderscoreDigitSuffix l ∧
    l ∉ StringGenState.stringGens gen' ∧
    l ∉ Block.userBlockLabels bss ∧
    l ∉ Block.userBlockLabels rest := by
  obtain ⟨h_shape, h_nodup, h_disj⟩ := h
  have h_l_in : l ∈ Block.userBlockLabels (Stmt.block l bss md :: rest) := by
    unfold Block.userBlockLabels Block.userBlockLabels.stmtUserBlockLabels
    exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inl rfl)))
  refine ⟨h_shape l h_l_in, h_disj l h_l_in, ?_, ?_⟩
  · -- l ∉ Block.userBlockLabels bss: from Nodup of (l :: bss-labels) ++ rest-labels
    unfold Block.userBlockLabels Block.userBlockLabels.stmtUserBlockLabels at h_nodup
    have h_left := (List.nodup_append.mp h_nodup).1
    exact (List.nodup_cons.mp h_left).1
  · -- l ∉ Block.userBlockLabels rest: from cross-list disjointness in Nodup append
    unfold Block.userBlockLabels Block.userBlockLabels.stmtUserBlockLabels at h_nodup
    have h_disj_lr := (List.nodup_append.mp h_nodup).2.2
    intro h_in
    exact h_disj_lr l (List.mem_cons.mpr (Or.inl rfl)) l h_in rfl

/-- `flushCmds` always produces a `GenStep`, regardless of WF. -/
private theorem flushCmds_genStep {P : PureExpr} [HasBool P]
    (pfx : String) (accum : List (Cmd P))
    (tr? : Option (DetTransferCmd String P)) (k : String)
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : flushCmds pfx accum tr? k gen = ((entry, blocks), gen')) :
    StringGenState.GenStep gen gen' := by
  unfold flushCmds at h_gen
  cases h_tr : tr? with
  | none =>
    rw [h_tr] at h_gen
    simp only at h_gen
    by_cases h_empty : accum.isEmpty
    · rw [if_pos h_empty] at h_gen
      simp only [pure, StateT.pure] at h_gen
      have : gen' = gen := (Prod.mk.inj h_gen).2.symm
      rw [this]
      exact StringGenState.GenStep.refl _
    · rw [if_neg h_empty] at h_gen
      simp only [bind, StateT.bind, pure, StateT.pure, Id] at h_gen
      have : gen' = (StringGenState.gen pfx gen).2 := (Prod.mk.inj h_gen).2.symm
      rw [this]
      exact StringGenState.GenStep.of_gen pfx gen
  | some tr =>
    rw [h_tr] at h_gen
    simp only [bind, StateT.bind, pure, StateT.pure, Id] at h_gen
    have : gen' = (StringGenState.gen pfx gen).2 := (Prod.mk.inj h_gen).2.symm
    rw [this]
    exact StringGenState.GenStep.of_gen pfx gen

/-- The invariant-assert generating `mapM` in the loop arm only ever calls
`StringGenState.gen "inv$"` (for empty source labels) or no generator at all,
so it produces a `GenStep` from its input to its output state. Shared by both
`stmtsToBlocks_genStep` and `stmtsToBlocks_invariant` across the none/some
measure branches. -/
private theorem invMapM_genStep {P : PureExpr} [HasPassiveCmds P (Cmd P)]
    (is : List (String × P.Expr)) (gen_b gen_i : StringGenState) (invCmds : List (Cmd P))
    (h_inv_def :
      ((is.mapM (fun (srcLabel, i) => do
          let assertLabel ←
            if srcLabel.isEmpty then StringGenState.gen "inv$"
            else pure srcLabel
          pure (HasPassiveCmds.assert (P := P) (CmdT := Cmd P) assertLabel i synthesizedMd)))
       : LabelGen.StringGenM (List (Cmd P))) gen_b = (invCmds, gen_i)) :
    StringGenState.GenStep gen_b gen_i := by
  apply mapM_genStep _ _ is gen_b gen_i invCmds h_inv_def
  intro a g g' b h_step
  obtain ⟨srcLabel, i⟩ := a
  by_cases h_empty : srcLabel.isEmpty
  · simp only [h_empty, if_true, bind, StateT.bind, pure, StateT.pure] at h_step
    have h_g_eq : g' = (StringGenState.gen "inv$" g).2 := (Prod.mk.inj h_step).2.symm
    rw [h_g_eq]; exact StringGenState.GenStep.of_gen "inv$" g
  · simp only [h_empty, bind, pure] at h_step
    have h_g_eq : g' = g := (Prod.mk.inj h_step).2.symm
    rw [h_g_eq]; exact StringGenState.GenStep.refl g

/-- A weaker invariant for `stmtsToBlocks`: just the `GenStep` part
(WF preservation + monotone label list). This holds without any
disjointness assumption and is used to bootstrap the full invariant. -/
private theorem stmtsToBlocks_genStep
    {P : PureExpr} [HasBool P] [HasIdent P] [HasFvar P] [HasIntOrder P] [HasNot P]
    (k : String) (ss : List (Stmt P (Cmd P)))
    (exitConts : List (Option String × String))
    (accum : List (Cmd P))
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : stmtsToBlocks k ss exitConts accum gen = ((entry, blocks), gen')) :
    StringGenState.GenStep gen gen' := by
  match h_match : ss with
  | [] =>
    unfold stmtsToBlocks at h_gen
    exact flushCmds_genStep "l$" accum .none k gen gen' entry blocks h_gen
  | .cmd c :: rest =>
    unfold stmtsToBlocks at h_gen
    exact stmtsToBlocks_genStep k rest exitConts (c :: accum) gen gen' entry blocks h_gen
  | .funcDecl _ _ :: rest =>
    unfold stmtsToBlocks at h_gen
    exact stmtsToBlocks_genStep k rest exitConts accum gen gen' entry blocks h_gen
  | .typeDecl _ _ :: rest =>
    unfold stmtsToBlocks at h_gen
    exact stmtsToBlocks_genStep k rest exitConts accum gen gen' entry blocks h_gen
  | .exit l? md :: _ =>
    unfold stmtsToBlocks at h_gen
    exact flushCmds_genStep _ accum _ _ gen gen' entry blocks h_gen
  | .block l bss md :: rest =>
    simp only [stmtsToBlocks, bind, StateT.bind, pure] at h_gen
    generalize h_rest_eq : stmtsToBlocks k rest exitConts [] gen = r_rest at h_gen
    obtain ⟨⟨kNext, bsNext⟩, gen_r⟩ := r_rest
    simp at h_gen
    generalize h_body_eq : stmtsToBlocks kNext bss
      ((some l, kNext) :: exitConts) [] gen_r = r_body at h_gen
    obtain ⟨⟨bl, bbs⟩, gen_b⟩ := r_body
    simp at h_gen
    generalize h_flush_eq : @flushCmds P (Cmd P) _ "blk$" accum .none bl gen_b = r_flush at h_gen
    obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
    have h_step_rest := stmtsToBlocks_genStep k rest exitConts [] gen gen_r
      kNext bsNext h_rest_eq
    have h_step_body := stmtsToBlocks_genStep kNext bss _ [] gen_r gen_b
      bl bbs h_body_eq
    have h_step_flush := flushCmds_genStep "blk$" accum .none bl gen_b gen_f
      accumEntry accumBlocks h_flush_eq
    have h_gen_eq : gen_f = gen' := by
      simp only at h_gen
      by_cases h_eq : l = bl
      · rw [if_pos h_eq] at h_gen
        simp only [pure, StateT.pure] at h_gen
        exact (Prod.mk.inj h_gen).2
      · rw [if_neg h_eq] at h_gen
        simp only [pure, StateT.pure] at h_gen
        exact (Prod.mk.inj h_gen).2
    exact h_gen_eq ▸ (h_step_rest.trans h_step_body).trans h_step_flush
  | .ite c tss fss md :: rest =>
    simp only [stmtsToBlocks, bind, StateT.bind, pure] at h_gen
    generalize h_rest_eq : stmtsToBlocks k rest exitConts [] gen = r_rest at h_gen
    obtain ⟨⟨kNext, bsNext⟩, gen_r⟩ := r_rest
    simp only at h_gen
    generalize h_ite_label : StringGenState.gen "ite" gen_r = r_ite at h_gen
    obtain ⟨l_ite, gen_ite⟩ := r_ite
    simp only at h_gen
    generalize h_then_eq : stmtsToBlocks kNext tss exitConts [] gen_ite = r_then at h_gen
    obtain ⟨⟨tl, tbs⟩, gen_t⟩ := r_then
    simp only at h_gen
    generalize h_else_eq : stmtsToBlocks kNext fss exitConts [] gen_t = r_else at h_gen
    obtain ⟨⟨fl, fbs⟩, gen_e⟩ := r_else
    simp only at h_gen
    have h_step_rest := stmtsToBlocks_genStep k rest exitConts [] gen gen_r
      kNext bsNext h_rest_eq
    have h_step_ite : StringGenState.GenStep gen_r gen_ite := by
      rw [show gen_ite = (StringGenState.gen "ite" gen_r).2 from
            (by rw [h_ite_label])]
      exact StringGenState.GenStep.of_gen "ite" gen_r
    have h_step_then := stmtsToBlocks_genStep kNext tss exitConts [] gen_ite gen_t
      tl tbs h_then_eq
    have h_step_else := stmtsToBlocks_genStep kNext fss exitConts [] gen_t gen_e
      fl fbs h_else_eq
    cases c with
    | det e =>
      simp only [bind, StateT.bind, pure, StateT.pure, List.append_nil] at h_gen
      generalize h_flush_eq : @flushCmds P (Cmd P) _ "ite$" accum
        (.some (DetTransferCmd.condGoto e tl fl md)) l_ite gen_e = r_flush at h_gen
      obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
      have h_step_flush : StringGenState.GenStep gen_e gen_f :=
        flushCmds_genStep "ite$" accum _ l_ite gen_e gen_f
          accumEntry accumBlocks h_flush_eq
      have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
      exact h_gen_eq ▸ ((((h_step_rest.trans h_step_ite).trans h_step_then).trans h_step_else).trans
              h_step_flush)
    | nondet =>
      simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
      generalize h_nondet_gen : StringGenState.gen "$__nondet_ite$" gen_e = r_nd at h_gen
      obtain ⟨freshName, gen_n⟩ := r_nd
      simp only at h_gen
      generalize h_flush_eq : @flushCmds P (Cmd P) _ "ite$"
        (accum ++ [HasInit.init (HasIdent.ident (P := P) freshName) HasBool.boolTy
            ExprOrNondet.nondet synthesizedMd])
        (.some (DetTransferCmd.condGoto
          (HasFvar.mkFvar (HasIdent.ident (P := P) freshName)) tl fl md)) l_ite gen_n =
        r_flush at h_gen
      obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
      have h_step_nondet : StringGenState.GenStep gen_e gen_n := by
        rw [show gen_n = (StringGenState.gen "$__nondet_ite$" gen_e).2 from
              (by rw [h_nondet_gen])]
        exact StringGenState.GenStep.of_gen "$__nondet_ite$" gen_e
      have h_step_flush : StringGenState.GenStep gen_n gen_f :=
        flushCmds_genStep "ite$" _ _ l_ite gen_n gen_f
          accumEntry accumBlocks h_flush_eq
      have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
      exact h_gen_eq ▸ (((((h_step_rest.trans h_step_ite).trans h_step_then).trans h_step_else).trans
              h_step_nondet).trans h_step_flush)
  | .loop c m is bss md :: rest =>
    simp only [stmtsToBlocks, bind, StateT.bind] at h_gen
    -- Decompose generic prefix: rest and lentry.
    generalize h_rest_eq : stmtsToBlocks k rest exitConts [] gen = r_rest at h_gen
    obtain ⟨⟨kNext, bsNext⟩, gen_r⟩ := r_rest
    simp only at h_gen
    generalize h_lentry_def : StringGenState.gen "loop_entry$" gen_r = r_le at h_gen
    obtain ⟨lentry, gen_le⟩ := r_le
    simp only at h_gen
    have h_step_rest := stmtsToBlocks_genStep k rest exitConts [] gen gen_r
      kNext bsNext h_rest_eq
    have h_step_le : StringGenState.GenStep gen_r gen_le := by
      rw [show gen_le = (StringGenState.gen "loop_entry$" gen_r).2 from
            (by rw [h_lentry_def])]
      exact StringGenState.GenStep.of_gen "loop_entry$" gen_r
    -- Split on m and c simultaneously to flatten nested matches.
    cases h_m_cases : m with
    | none =>
      rw [h_m_cases] at h_gen
      simp only [pure, StateT.pure, bind, StateT.bind] at h_gen
      -- Decompose body, mapM, and the c-cases.
      generalize h_body_eq :
        stmtsToBlocks lentry bss ((none, kNext) :: exitConts) [] gen_le = r_body at h_gen
      obtain ⟨⟨bl, bbs⟩, gen_b⟩ := r_body
      simp only at h_gen
      generalize h_inv_def :
        ((is.mapM (fun (srcLabel, i) => do
            let assertLabel ←
              if srcLabel.isEmpty then StringGenState.gen "inv$"
              else pure srcLabel
            pure (HasPassiveCmds.assert (P := P) (CmdT := Cmd P) assertLabel i synthesizedMd)))
         : LabelGen.StringGenM (List (Cmd P))) gen_b = r_inv at h_gen
      obtain ⟨invCmds, gen_i⟩ := r_inv
      have h_step_body := stmtsToBlocks_genStep lentry bss _ [] gen_le gen_b bl bbs h_body_eq
      have h_step_inv : StringGenState.GenStep gen_b gen_i :=
        invMapM_genStep is gen_b gen_i invCmds h_inv_def
      have h_step_prefix : StringGenState.GenStep gen gen_i :=
        ((h_step_rest.trans h_step_le).trans h_step_body).trans h_step_inv
      cases c with
      | det e =>
        simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
        generalize h_flush_eq : @flushCmds P (Cmd P) _ "before_loop$" accum
          Option.none lentry gen_i = r_flush at h_gen
        obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
        have h_step_flush : StringGenState.GenStep gen_i gen_f :=
          flushCmds_genStep "before_loop$" accum _ lentry gen_i gen_f
            accumEntry accumBlocks h_flush_eq
        have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
        exact h_gen_eq ▸ h_step_prefix.trans h_step_flush
      | nondet =>
        simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
        generalize h_nondet_gen : StringGenState.gen "$__nondet_loop$" gen_i = r_nd at h_gen
        obtain ⟨freshName, gen_n⟩ := r_nd
        generalize h_flush_eq : @flushCmds P (Cmd P) _ "before_loop$" accum
          Option.none lentry gen_n = r_flush at h_gen
        obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
        have h_step_nondet : StringGenState.GenStep gen_i gen_n := by
          rw [show gen_n = (StringGenState.gen "$__nondet_loop$" gen_i).2 from
                (by rw [h_nondet_gen])]
          exact StringGenState.GenStep.of_gen "$__nondet_loop$" gen_i
        have h_step_flush : StringGenState.GenStep gen_n gen_f :=
          flushCmds_genStep "before_loop$" accum _ lentry gen_n gen_f
            accumEntry accumBlocks h_flush_eq
        have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
        exact h_gen_eq ▸ (h_step_prefix.trans h_step_nondet).trans h_step_flush
    | some mExpr =>
      rw [h_m_cases] at h_gen
      simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
      generalize h_ml_def : StringGenState.gen "loop_measure$" gen_le = r_ml at h_gen
      obtain ⟨mLabel, gen_ml⟩ := r_ml
      simp only at h_gen
      generalize h_ldec_def : StringGenState.gen "measure_decrease$" gen_ml = r_ldec at h_gen
      obtain ⟨ldec, gen_ldec⟩ := r_ldec
      simp only at h_gen
      have h_step_ml : StringGenState.GenStep gen_le gen_ml := by
        rw [show gen_ml = (StringGenState.gen "loop_measure$" gen_le).2 from
              (by rw [h_ml_def])]
        exact StringGenState.GenStep.of_gen "loop_measure$" gen_le
      have h_step_ldec : StringGenState.GenStep gen_ml gen_ldec := by
        rw [show gen_ldec = (StringGenState.gen "measure_decrease$" gen_ml).2 from
              (by rw [h_ldec_def])]
        exact StringGenState.GenStep.of_gen "measure_decrease$" gen_ml
      generalize h_body_eq :
        stmtsToBlocks ldec bss ((none, kNext) :: exitConts) [] gen_ldec = r_body at h_gen
      obtain ⟨⟨bl, bbs⟩, gen_b⟩ := r_body
      simp only at h_gen
      generalize h_inv_def :
        ((is.mapM (fun (srcLabel, i) => do
            let assertLabel ←
              if srcLabel.isEmpty then StringGenState.gen "inv$"
              else pure srcLabel
            pure (HasPassiveCmds.assert (P := P) (CmdT := Cmd P) assertLabel i synthesizedMd)))
         : LabelGen.StringGenM (List (Cmd P))) gen_b = r_inv at h_gen
      obtain ⟨invCmds, gen_i⟩ := r_inv
      have h_step_body := stmtsToBlocks_genStep ldec bss _ [] gen_ldec gen_b bl bbs h_body_eq
      have h_step_inv : StringGenState.GenStep gen_b gen_i :=
        invMapM_genStep is gen_b gen_i invCmds h_inv_def
      have h_step_prefix : StringGenState.GenStep gen gen_i :=
        ((((h_step_rest.trans h_step_le).trans h_step_ml).trans h_step_ldec).trans
          h_step_body).trans h_step_inv
      cases c with
      | det e =>
        simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
        generalize h_flush_eq : @flushCmds P (Cmd P) _ "before_loop$" accum
          Option.none lentry gen_i = r_flush at h_gen
        obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
        have h_step_flush : StringGenState.GenStep gen_i gen_f :=
          flushCmds_genStep "before_loop$" accum _ lentry gen_i gen_f
            accumEntry accumBlocks h_flush_eq
        have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
        exact h_gen_eq ▸ h_step_prefix.trans h_step_flush
      | nondet =>
        simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
        generalize h_nondet_gen : StringGenState.gen "$__nondet_loop$" gen_i = r_nd at h_gen
        obtain ⟨freshName, gen_n⟩ := r_nd
        generalize h_flush_eq : @flushCmds P (Cmd P) _ "before_loop$" accum
          Option.none lentry gen_n = r_flush at h_gen
        obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
        have h_step_nondet : StringGenState.GenStep gen_i gen_n := by
          rw [show gen_n = (StringGenState.gen "$__nondet_loop$" gen_i).2 from
                (by rw [h_nondet_gen])]
          exact StringGenState.GenStep.of_gen "$__nondet_loop$" gen_i
        have h_step_flush : StringGenState.GenStep gen_n gen_f :=
          flushCmds_genStep "before_loop$" accum _ lentry gen_n gen_f
            accumEntry accumBlocks h_flush_eq
        have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
        exact h_gen_eq ▸ (h_step_prefix.trans h_step_nondet).trans h_step_flush
termination_by sizeOf ss
decreasing_by all_goals (subst h_match; simp_wf; omega)

/-! ### Pass-tracking: every label `stmtsToCFG` mints satisfies the label *kind*

`stmtsToCFG` mints block labels under exactly thirteen generator prefixes (the
twelve fixed ones listed in `s2uKind` plus the user-label-parameterised
`"block$⟨l⟩$"`).  The lemmas below track `AllMem R` across `flushCmds` and
`stmtsToBlocks` for *any* label-kind predicate `R` that holds of every
`gen`-output under those thirteen prefixes (the thirteen-conjunct mint witness
`hmints`, the same shape as `s2uKind_gen`/`hQmint`).  Starting from the empty
generator state (which satisfies `AllMem R` vacuously), every label this pass
produces satisfies `R`.  Instantiated at `R := s2uKind`, this lets a downstream
discharge a foreign-label obligation — any label that is *not* `s2uKind` is
absent from the output generator — by plain contraposition
(`not_mem_stringGens_of_not_allMem`), without assuming the consumer keeps *every*
gen-shaped name fresh. -/

/-- The thirteen-conjunct mint witness: `R` holds of every `gen`-output under each
of the thirteen prefixes `stmtsToCFG` mints under (twelve fixed and one
parameterised by the user block label being exited).  Identical in shape to
`s2uKind_gen` and to the `hQmint` hypothesis of `structuredToUnstructured_sound_kind`. -/
@[expose] def S2UMintWitness (R : String → Prop) : Prop :=
    (∀ sg, R (StringGenState.gen "ite" sg).1)
  ∧ (∀ sg, R (StringGenState.gen "$__nondet_ite$" sg).1)
  ∧ (∀ sg, R (StringGenState.gen "ite$" sg).1)
  ∧ (∀ sg, R (StringGenState.gen "loop_entry$" sg).1)
  ∧ (∀ sg, R (StringGenState.gen "loop_measure$" sg).1)
  ∧ (∀ sg, R (StringGenState.gen "measure_decrease$" sg).1)
  ∧ (∀ sg, R (StringGenState.gen "inv$" sg).1)
  ∧ (∀ sg, R (StringGenState.gen "$__nondet_loop$" sg).1)
  ∧ (∀ sg, R (StringGenState.gen "end$" sg).1)
  ∧ (∀ sg, R (StringGenState.gen "l$" sg).1)
  ∧ (∀ sg, R (StringGenState.gen "blk$" sg).1)
  ∧ (∀ sg, R (StringGenState.gen "before_loop$" sg).1)
  ∧ (∀ (l : String) sg, R (StringGenState.gen (s!"block${l}$") sg).1)

/-- `flushCmds` advancing under a mint prefix preserves `AllMem R`: it either
leaves the generator untouched (empty accumulator, no transfer) or mints a single
label `(gen pfx gen).1`, which `allMem_gen` absorbs via the per-prefix mint
witness `h_mint`. -/
private theorem flushCmds_allMem {P : PureExpr} [HasBool P] {R : String → Prop}
    (pfx : String) (accum : List (Cmd P))
    (tr? : Option (DetTransferCmd String P)) (k : String)
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : flushCmds pfx accum tr? k gen = ((entry, blocks), gen'))
    (h_mint : ∀ sg, R (StringGenState.gen pfx sg).1)
    (h_in : StringGenState.AllMem R gen) :
    StringGenState.AllMem R gen' := by
  unfold flushCmds at h_gen
  cases h_tr : tr? with
  | none =>
    rw [h_tr] at h_gen
    simp only at h_gen
    by_cases h_empty : accum.isEmpty
    · rw [if_pos h_empty] at h_gen
      simp only [pure, StateT.pure] at h_gen
      have : gen' = gen := (Prod.mk.inj h_gen).2.symm
      rw [this]; exact h_in
    · rw [if_neg h_empty] at h_gen
      simp only [bind, StateT.bind, pure, StateT.pure, Id] at h_gen
      have : gen' = (StringGenState.gen pfx gen).2 := (Prod.mk.inj h_gen).2.symm
      rw [this]
      exact StringGenState.allMem_gen R pfx gen h_in (h_mint gen)
  | some tr =>
    rw [h_tr] at h_gen
    simp only [bind, StateT.bind, pure, StateT.pure, Id] at h_gen
    have : gen' = (StringGenState.gen pfx gen).2 := (Prod.mk.inj h_gen).2.symm
    rw [this]
    exact StringGenState.allMem_gen R pfx gen h_in (h_mint gen)

/-- A generic `mapM_allMem`: if each step of a `StringGenM` computation
preserves `AllMem R`, the whole `mapM` does too. The analogue of
`mapM_genStep` for the membership-tracking invariant. -/
private theorem mapM_allMem {α β : Type} (Pred : String → Prop)
    (f : α → LabelGen.StringGenM β)
    (h_step : ∀ (a : α) (gen gen' : StringGenState) (b : β),
                f a gen = (b, gen') →
                StringGenState.AllMem Pred gen →
                StringGenState.AllMem Pred gen')
    (xs : List α)
    (gen gen' : StringGenState) (ys : List β)
    (h_eq : xs.mapM f gen = (ys, gen'))
    (h_in : StringGenState.AllMem Pred gen) :
    StringGenState.AllMem Pred gen' := by
  induction xs generalizing gen gen' ys with
  | nil =>
    rw [List.mapM_nil] at h_eq
    simp only [pure, StateT.pure] at h_eq
    have h_gen' : gen = gen' := (Prod.mk.inj h_eq).2
    exact h_gen' ▸ h_in
  | cons hd tl ih =>
    rw [List.mapM_cons] at h_eq
    simp only [bind, StateT.bind, pure, StateT.pure] at h_eq
    generalize h_f : f hd gen = r1 at h_eq
    obtain ⟨y, gen_mid⟩ := r1
    simp only at h_eq
    generalize h_tail : tl.mapM f gen_mid = r2 at h_eq
    obtain ⟨ys', gen_end⟩ := r2
    simp only at h_eq
    have h_gen' : gen_end = gen' := (Prod.mk.inj h_eq).2
    have h_mid : StringGenState.AllMem Pred gen_mid :=
      h_step hd gen gen_mid y h_f h_in
    exact h_gen' ▸ ih gen_mid gen_end ys' h_tail h_mid

/-- The invariant-assert `mapM` only mints under `"inv$"` (for empty source
labels) or not at all, so it preserves `AllMem R` whenever `R` holds of every
`"inv$"` `gen`-output. -/
private theorem invMapM_allMem {P : PureExpr} [HasPassiveCmds P (Cmd P)]
    {R : String → Prop}
    (is : List (String × P.Expr)) (gen_b gen_i : StringGenState) (invCmds : List (Cmd P))
    (h_inv_def :
      ((is.mapM (fun (srcLabel, i) => do
          let assertLabel ←
            if srcLabel.isEmpty then StringGenState.gen "inv$"
            else pure srcLabel
          pure (HasPassiveCmds.assert (P := P) (CmdT := Cmd P) assertLabel i synthesizedMd)))
       : LabelGen.StringGenM (List (Cmd P))) gen_b = (invCmds, gen_i))
    (h_inv_mint : ∀ sg, R (StringGenState.gen "inv$" sg).1)
    (h_in : StringGenState.AllMem R gen_b) :
    StringGenState.AllMem R gen_i := by
  apply mapM_allMem R _ _ is gen_b gen_i invCmds h_inv_def h_in
  intro a g g' b h_step h_g_in
  obtain ⟨srcLabel, i⟩ := a
  by_cases h_empty : srcLabel.isEmpty
  · simp only [h_empty, if_true, bind, StateT.bind, pure, StateT.pure] at h_step
    have h_g_eq : g' = (StringGenState.gen "inv$" g).2 := (Prod.mk.inj h_step).2.symm
    rw [h_g_eq]
    exact StringGenState.allMem_gen R "inv$" g h_g_in (h_inv_mint g)
  · simp only [h_empty, bind, pure] at h_step
    have h_g_eq : g' = g := (Prod.mk.inj h_step).2.symm
    rw [h_g_eq]; exact h_g_in

/-- `stmtsToBlocks` preserves `AllMem R`: every label it mints satisfies `R`,
given that `R` holds of every `gen`-output under the thirteen mint prefixes
(`hmints : S2UMintWitness R`).  Mirrors `stmtsToBlocks_genStep` arm-by-arm,
discharging each `flushCmds`/`gen` mint with the matching component of `hmints`
and composing recursive calls through the IH. -/
private theorem stmtsToBlocks_allMem
    {P : PureExpr} [HasBool P] [HasIdent P] [HasFvar P] [HasIntOrder P] [HasNot P]
    {R : String → Prop} (hmints : S2UMintWitness R)
    (k : String) (ss : List (Stmt P (Cmd P)))
    (exitConts : List (Option String × String))
    (accum : List (Cmd P))
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : stmtsToBlocks k ss exitConts accum gen = ((entry, blocks), gen'))
    (h_in : StringGenState.AllMem R gen) :
    StringGenState.AllMem R gen' := by
  match h_match : ss with
  | [] =>
    unfold stmtsToBlocks at h_gen
    exact flushCmds_allMem "l$" accum .none k gen gen' entry blocks h_gen
      hmints.2.2.2.2.2.2.2.2.2.1 h_in
  | .cmd c :: rest =>
    unfold stmtsToBlocks at h_gen
    exact stmtsToBlocks_allMem hmints k rest exitConts (c :: accum) gen gen' entry blocks
      h_gen h_in
  | .funcDecl _ _ :: rest =>
    unfold stmtsToBlocks at h_gen
    exact stmtsToBlocks_allMem hmints k rest exitConts accum gen gen' entry blocks h_gen h_in
  | .typeDecl _ _ :: rest =>
    unfold stmtsToBlocks at h_gen
    exact stmtsToBlocks_allMem hmints k rest exitConts accum gen gen' entry blocks h_gen h_in
  | .exit l? md :: _ =>
    unfold stmtsToBlocks at h_gen
    exact flushCmds_allMem _ accum _ _ gen gen' entry blocks h_gen
      (hmints.2.2.2.2.2.2.2.2.2.2.2.2 l?) h_in
  | .block l bss md :: rest =>
    simp only [stmtsToBlocks, bind, StateT.bind, pure] at h_gen
    generalize h_rest_eq : stmtsToBlocks k rest exitConts [] gen = r_rest at h_gen
    obtain ⟨⟨kNext, bsNext⟩, gen_r⟩ := r_rest
    simp at h_gen
    generalize h_body_eq : stmtsToBlocks kNext bss
      ((some l, kNext) :: exitConts) [] gen_r = r_body at h_gen
    obtain ⟨⟨bl, bbs⟩, gen_b⟩ := r_body
    simp at h_gen
    generalize h_flush_eq : @flushCmds P (Cmd P) _ "blk$" accum .none bl gen_b = r_flush at h_gen
    obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
    have h_in_rest := stmtsToBlocks_allMem hmints k rest exitConts [] gen gen_r
      kNext bsNext h_rest_eq h_in
    have h_in_body := stmtsToBlocks_allMem hmints kNext bss _ [] gen_r gen_b
      bl bbs h_body_eq h_in_rest
    have h_in_flush := flushCmds_allMem "blk$" accum .none bl gen_b gen_f
      accumEntry accumBlocks h_flush_eq
      hmints.2.2.2.2.2.2.2.2.2.2.1 h_in_body
    have h_gen_eq : gen_f = gen' := by
      simp only at h_gen
      by_cases h_eq : l = bl
      · rw [if_pos h_eq] at h_gen
        simp only [pure, StateT.pure] at h_gen
        exact (Prod.mk.inj h_gen).2
      · rw [if_neg h_eq] at h_gen
        simp only [pure, StateT.pure] at h_gen
        exact (Prod.mk.inj h_gen).2
    exact h_gen_eq ▸ h_in_flush
  | .ite c tss fss md :: rest =>
    simp only [stmtsToBlocks, bind, StateT.bind, pure] at h_gen
    generalize h_rest_eq : stmtsToBlocks k rest exitConts [] gen = r_rest at h_gen
    obtain ⟨⟨kNext, bsNext⟩, gen_r⟩ := r_rest
    simp only at h_gen
    generalize h_ite_label : StringGenState.gen "ite" gen_r = r_ite at h_gen
    obtain ⟨l_ite, gen_ite⟩ := r_ite
    simp only at h_gen
    generalize h_then_eq : stmtsToBlocks kNext tss exitConts [] gen_ite = r_then at h_gen
    obtain ⟨⟨tl, tbs⟩, gen_t⟩ := r_then
    simp only at h_gen
    generalize h_else_eq : stmtsToBlocks kNext fss exitConts [] gen_t = r_else at h_gen
    obtain ⟨⟨fl, fbs⟩, gen_e⟩ := r_else
    simp only at h_gen
    have h_in_rest := stmtsToBlocks_allMem hmints k rest exitConts [] gen gen_r
      kNext bsNext h_rest_eq h_in
    have h_in_ite : StringGenState.AllMem R gen_ite := by
      rw [show gen_ite = (StringGenState.gen "ite" gen_r).2 from (by rw [h_ite_label])]
      exact StringGenState.allMem_gen R "ite" gen_r h_in_rest (hmints.1 gen_r)
    have h_in_then := stmtsToBlocks_allMem hmints kNext tss exitConts [] gen_ite gen_t
      tl tbs h_then_eq h_in_ite
    have h_in_else := stmtsToBlocks_allMem hmints kNext fss exitConts [] gen_t gen_e
      fl fbs h_else_eq h_in_then
    cases c with
    | det e =>
      simp only [bind, StateT.bind, pure, StateT.pure, List.append_nil] at h_gen
      generalize h_flush_eq : @flushCmds P (Cmd P) _ "ite$" accum
        (.some (DetTransferCmd.condGoto e tl fl md)) l_ite gen_e = r_flush at h_gen
      obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
      have h_in_flush : StringGenState.AllMem R gen_f :=
        flushCmds_allMem "ite$" accum _ l_ite gen_e gen_f
          accumEntry accumBlocks h_flush_eq hmints.2.2.1 h_in_else
      have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
      exact h_gen_eq ▸ h_in_flush
    | nondet =>
      simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
      generalize h_nondet_gen : StringGenState.gen "$__nondet_ite$" gen_e = r_nd at h_gen
      obtain ⟨freshName, gen_n⟩ := r_nd
      simp only at h_gen
      generalize h_flush_eq : @flushCmds P (Cmd P) _ "ite$"
        (accum ++ [HasInit.init (HasIdent.ident (P := P) freshName) HasBool.boolTy
            ExprOrNondet.nondet synthesizedMd])
        (.some (DetTransferCmd.condGoto
          (HasFvar.mkFvar (HasIdent.ident (P := P) freshName)) tl fl md)) l_ite gen_n =
        r_flush at h_gen
      obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
      have h_in_nondet : StringGenState.AllMem R gen_n := by
        rw [show gen_n = (StringGenState.gen "$__nondet_ite$" gen_e).2 from
              (by rw [h_nondet_gen])]
        exact StringGenState.allMem_gen R "$__nondet_ite$" gen_e h_in_else
          (hmints.2.1 gen_e)
      have h_in_flush : StringGenState.AllMem R gen_f :=
        flushCmds_allMem "ite$" _ _ l_ite gen_n gen_f
          accumEntry accumBlocks h_flush_eq hmints.2.2.1 h_in_nondet
      have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
      exact h_gen_eq ▸ h_in_flush
  | .loop c m is bss md :: rest =>
    simp only [stmtsToBlocks, bind, StateT.bind] at h_gen
    generalize h_rest_eq : stmtsToBlocks k rest exitConts [] gen = r_rest at h_gen
    obtain ⟨⟨kNext, bsNext⟩, gen_r⟩ := r_rest
    simp only at h_gen
    generalize h_lentry_def : StringGenState.gen "loop_entry$" gen_r = r_le at h_gen
    obtain ⟨lentry, gen_le⟩ := r_le
    simp only at h_gen
    have h_in_rest := stmtsToBlocks_allMem hmints k rest exitConts [] gen gen_r
      kNext bsNext h_rest_eq h_in
    have h_in_le : StringGenState.AllMem R gen_le := by
      rw [show gen_le = (StringGenState.gen "loop_entry$" gen_r).2 from
            (by rw [h_lentry_def])]
      exact StringGenState.allMem_gen R "loop_entry$" gen_r h_in_rest
        (hmints.2.2.2.1 gen_r)
    cases h_m_cases : m with
    | none =>
      rw [h_m_cases] at h_gen
      simp only [pure, StateT.pure, bind, StateT.bind] at h_gen
      generalize h_body_eq :
        stmtsToBlocks lentry bss ((none, kNext) :: exitConts) [] gen_le = r_body at h_gen
      obtain ⟨⟨bl, bbs⟩, gen_b⟩ := r_body
      simp only at h_gen
      generalize h_inv_def :
        ((is.mapM (fun (srcLabel, i) => do
            let assertLabel ←
              if srcLabel.isEmpty then StringGenState.gen "inv$"
              else pure srcLabel
            pure (HasPassiveCmds.assert (P := P) (CmdT := Cmd P) assertLabel i synthesizedMd)))
         : LabelGen.StringGenM (List (Cmd P))) gen_b = r_inv at h_gen
      obtain ⟨invCmds, gen_i⟩ := r_inv
      have h_in_body := stmtsToBlocks_allMem hmints lentry bss _ [] gen_le gen_b bl bbs
        h_body_eq h_in_le
      have h_in_inv : StringGenState.AllMem R gen_i :=
        invMapM_allMem is gen_b gen_i invCmds h_inv_def hmints.2.2.2.2.2.2.1 h_in_body
      cases c with
      | det e =>
        simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
        generalize h_flush_eq : @flushCmds P (Cmd P) _ "before_loop$" accum
          Option.none lentry gen_i = r_flush at h_gen
        obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
        have h_in_flush : StringGenState.AllMem R gen_f :=
          flushCmds_allMem "before_loop$" accum _ lentry gen_i gen_f
            accumEntry accumBlocks h_flush_eq
            hmints.2.2.2.2.2.2.2.2.2.2.2.1 h_in_inv
        have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
        exact h_gen_eq ▸ h_in_flush
      | nondet =>
        simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
        generalize h_nondet_gen : StringGenState.gen "$__nondet_loop$" gen_i = r_nd at h_gen
        obtain ⟨freshName, gen_n⟩ := r_nd
        generalize h_flush_eq : @flushCmds P (Cmd P) _ "before_loop$" accum
          Option.none lentry gen_n = r_flush at h_gen
        obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
        have h_in_nondet : StringGenState.AllMem R gen_n := by
          rw [show gen_n = (StringGenState.gen "$__nondet_loop$" gen_i).2 from
                (by rw [h_nondet_gen])]
          exact StringGenState.allMem_gen R "$__nondet_loop$" gen_i h_in_inv
            (hmints.2.2.2.2.2.2.2.1 gen_i)
        have h_in_flush : StringGenState.AllMem R gen_f :=
          flushCmds_allMem "before_loop$" accum _ lentry gen_n gen_f
            accumEntry accumBlocks h_flush_eq
            hmints.2.2.2.2.2.2.2.2.2.2.2.1 h_in_nondet
        have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
        exact h_gen_eq ▸ h_in_flush
    | some mExpr =>
      rw [h_m_cases] at h_gen
      simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
      generalize h_ml_def : StringGenState.gen "loop_measure$" gen_le = r_ml at h_gen
      obtain ⟨mLabel, gen_ml⟩ := r_ml
      simp only at h_gen
      generalize h_ldec_def : StringGenState.gen "measure_decrease$" gen_ml = r_ldec at h_gen
      obtain ⟨ldec, gen_ldec⟩ := r_ldec
      simp only at h_gen
      have h_in_ml : StringGenState.AllMem R gen_ml := by
        rw [show gen_ml = (StringGenState.gen "loop_measure$" gen_le).2 from
              (by rw [h_ml_def])]
        exact StringGenState.allMem_gen R "loop_measure$" gen_le h_in_le
          (hmints.2.2.2.2.1 gen_le)
      have h_in_ldec : StringGenState.AllMem R gen_ldec := by
        rw [show gen_ldec = (StringGenState.gen "measure_decrease$" gen_ml).2 from
              (by rw [h_ldec_def])]
        exact StringGenState.allMem_gen R "measure_decrease$" gen_ml h_in_ml
          (hmints.2.2.2.2.2.1 gen_ml)
      generalize h_body_eq :
        stmtsToBlocks ldec bss ((none, kNext) :: exitConts) [] gen_ldec = r_body at h_gen
      obtain ⟨⟨bl, bbs⟩, gen_b⟩ := r_body
      simp only at h_gen
      generalize h_inv_def :
        ((is.mapM (fun (srcLabel, i) => do
            let assertLabel ←
              if srcLabel.isEmpty then StringGenState.gen "inv$"
              else pure srcLabel
            pure (HasPassiveCmds.assert (P := P) (CmdT := Cmd P) assertLabel i synthesizedMd)))
         : LabelGen.StringGenM (List (Cmd P))) gen_b = r_inv at h_gen
      obtain ⟨invCmds, gen_i⟩ := r_inv
      have h_in_body := stmtsToBlocks_allMem hmints ldec bss _ [] gen_ldec gen_b bl bbs
        h_body_eq h_in_ldec
      have h_in_inv : StringGenState.AllMem R gen_i :=
        invMapM_allMem is gen_b gen_i invCmds h_inv_def hmints.2.2.2.2.2.2.1 h_in_body
      cases c with
      | det e =>
        simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
        generalize h_flush_eq : @flushCmds P (Cmd P) _ "before_loop$" accum
          Option.none lentry gen_i = r_flush at h_gen
        obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
        have h_in_flush : StringGenState.AllMem R gen_f :=
          flushCmds_allMem "before_loop$" accum _ lentry gen_i gen_f
            accumEntry accumBlocks h_flush_eq
            hmints.2.2.2.2.2.2.2.2.2.2.2.1 h_in_inv
        have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
        exact h_gen_eq ▸ h_in_flush
      | nondet =>
        simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
        generalize h_nondet_gen : StringGenState.gen "$__nondet_loop$" gen_i = r_nd at h_gen
        obtain ⟨freshName, gen_n⟩ := r_nd
        generalize h_flush_eq : @flushCmds P (Cmd P) _ "before_loop$" accum
          Option.none lentry gen_n = r_flush at h_gen
        obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
        have h_in_nondet : StringGenState.AllMem R gen_n := by
          rw [show gen_n = (StringGenState.gen "$__nondet_loop$" gen_i).2 from
                (by rw [h_nondet_gen])]
          exact StringGenState.allMem_gen R "$__nondet_loop$" gen_i h_in_inv
            (hmints.2.2.2.2.2.2.2.1 gen_i)
        have h_in_flush : StringGenState.AllMem R gen_f :=
          flushCmds_allMem "before_loop$" accum _ lentry gen_n gen_f
            accumEntry accumBlocks h_flush_eq
            hmints.2.2.2.2.2.2.2.2.2.2.2.1 h_in_nondet
        have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
        exact h_gen_eq ▸ h_in_flush
termination_by sizeOf ss
decreasing_by all_goals (subst h_match; simp_wf; omega)

/-- The main invariant for `stmtsToBlocks`.
We require WF on `gen` and obtain WF on `gen'`, plus freshness/nodup of
the produced block labels.

The proof is by well-founded recursion on `sizeOf ss` (so that recursive
calls on sub-lists `tss`, `fss`, `bss`, `body` work). For each statement
constructor, we:
1. Decompose the monadic computation via `generalize` + `obtain`,
2. Apply the IH to recursive sub-calls and `flushCmds_invariant` to flushes,
3. Combine results via `GenInv.trans`.

We require `userLabelsDisjoint`: user-provided block labels (from
`Stmt.block l ...`) must not collide with any generated label in the
final state. Without this, the `block` case can produce duplicate keys. -/
private theorem stmtsToBlocks_invariant
    {P : PureExpr} [HasBool P] [HasIdent P] [HasFvar P] [HasIntOrder P] [HasNot P]
    (k : String) (ss : List (Stmt P (Cmd P)))
    (exitConts : List (Option String × String))
    (accum : List (Cmd P))
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : stmtsToBlocks k ss exitConts accum gen = ((entry, blocks), gen'))
    (hwf : StringGenState.WF gen)
    (h_disj : Block.userLabelsDisjoint ss gen') :
    @GenInv P gen gen' (Block.userBlockLabels ss) blocks := by
  match h_match : ss with
  | [] =>
    -- stmtsToBlocks reduces to flushCmds "l$" accum .none k
    unfold stmtsToBlocks at h_gen
    -- Block.userBlockLabels [] = []
    show @GenInv P gen gen' [] blocks
    exact flushCmds_invariant "l$" accum .none k gen gen' entry blocks h_gen hwf
  | .cmd c :: rest =>
    -- Recurse with extended accumulator
    unfold stmtsToBlocks at h_gen
    rw [Block.userBlockLabels_cmd_cons]
    exact stmtsToBlocks_invariant k rest exitConts (c :: accum) gen gen' entry blocks h_gen hwf
      (Block.userLabelsDisjoint_tail _ _ _ h_disj)
  | .funcDecl _ _ :: rest =>
    -- Skip funcDecl, recurse on rest
    unfold stmtsToBlocks at h_gen
    rw [Block.userBlockLabels_funcDecl_cons]
    exact stmtsToBlocks_invariant k rest exitConts accum gen gen' entry blocks h_gen hwf
      (Block.userLabelsDisjoint_tail _ _ _ h_disj)
  | .typeDecl _ _ :: rest =>
    -- Skip typeDecl, recurse on rest
    unfold stmtsToBlocks at h_gen
    rw [Block.userBlockLabels_typeDecl_cons]
    exact stmtsToBlocks_invariant k rest exitConts accum gen gen' entry blocks h_gen hwf
      (Block.userLabelsDisjoint_tail _ _ _ h_disj)
  | .exit l? md :: _ =>
    -- The bk computation is pure (no gen calls); only flushCmds is stateful.
    -- exit truncates so blocks only come from flushCmds (no user labels).
    unfold stmtsToBlocks at h_gen
    rw [Block.userBlockLabels_exit_cons]
    have h_inv : @GenInv P gen gen' [] blocks :=
      flushCmds_invariant _ accum _ _ gen gen' entry blocks h_gen hwf
    -- Weaken from [] to userBlockLabels of the rest (which we discard from h_disj).
    have h_disj_rest := Block.userLabelsDisjoint_tail _ _ _ h_disj
    apply GenInv.weaken_userLabels gen gen' [] _ blocks h_inv
    · intro l hl; simp at hl
    · exact h_disj_rest.1
    · exact h_disj_rest.2.2
    · exact h_disj_rest.2.1
  | .block l bss md :: rest =>
    simp only [stmtsToBlocks, bind, StateT.bind, pure] at h_gen
    -- Decompose the monadic chain
    generalize h_rest_eq : stmtsToBlocks k rest exitConts [] gen = r_rest at h_gen
    obtain ⟨⟨kNext, bsNext⟩, gen_r⟩ := r_rest
    simp at h_gen
    generalize h_body_eq : stmtsToBlocks kNext bss
      ((some l, kNext) :: exitConts) [] gen_r = r_body at h_gen
    obtain ⟨⟨bl, bbs⟩, gen_b⟩ := r_body
    simp at h_gen
    generalize h_flush_eq : @flushCmds P (Cmd P) _ "blk$" accum .none bl gen_b = r_flush at h_gen
    obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
    -- Disjointness for sub-lists w.r.t. gen' (the outer final state)
    have h_disj_rest_gen' : Block.userLabelsDisjoint rest gen' :=
      Block.userLabelsDisjoint_tail _ _ _ h_disj
    have h_disj_bss_gen' : Block.userLabelsDisjoint bss gen' :=
      Block.userLabelsDisjoint_block_body l bss md rest gen' h_disj
    -- Use the simpler `stmtsToBlocks_genStep` to get subset relations
    -- without needing the full GenInv (which requires disjointness premises).
    have h_step_rest := stmtsToBlocks_genStep k rest exitConts [] gen gen_r
      kNext bsNext h_rest_eq
    have h_step_body := stmtsToBlocks_genStep kNext bss _ [] gen_r gen_b
      bl bbs h_body_eq
    -- Also need genStep for flushCmds (without requiring WF)
    have h_step_flush : StringGenState.GenStep gen_b gen_f :=
      flushCmds_genStep "blk$" accum .none bl gen_b gen_f
        accumEntry accumBlocks h_flush_eq
    -- gen_r ⊆ gen_b ⊆ gen_f. We have userLabelsDisjoint w.r.t. gen' (outer),
    -- but for sub-calls we need it w.r.t. gen_r and gen_b respectively.
    -- We first establish gen_f = gen' from h_gen, then chain.
    simp only at h_gen
    have h_gen_eq : gen_f = gen' := by
      by_cases h_eq : l = bl
      · rw [if_pos h_eq] at h_gen
        simp only [pure, StateT.pure] at h_gen
        exact (Prod.mk.inj h_gen).2
      · rw [if_neg h_eq] at h_gen
        simp only [pure, StateT.pure] at h_gen
        exact (Prod.mk.inj h_gen).2
    -- Use h_gen_eq to derive subsets w.r.t. gen' (= gen_f)
    have h_subset_r_gen' : StringGenState.stringGens gen_r ⊆ StringGenState.stringGens gen' := by
      exact h_gen_eq ▸ (h_step_body.trans h_step_flush).subset
    have h_subset_b_gen' : StringGenState.stringGens gen_b ⊆ StringGenState.stringGens gen' := by
      exact h_gen_eq ▸ h_step_flush.subset
    have h_disj_rest_gen_r : Block.userLabelsDisjoint rest gen_r :=
      Block.userLabelsDisjoint_mono _ _ _ h_disj_rest_gen' h_subset_r_gen'
    have h_disj_bss_gen_b : Block.userLabelsDisjoint bss gen_b :=
      Block.userLabelsDisjoint_mono _ _ _ h_disj_bss_gen' h_subset_b_gen'
    -- Get invariants for each step using IH on smaller statement lists.
    -- Each IH returns GenInv ... (userBlockLabels <sublist>) <blocks>.
    have h_inv_rest :
        @GenInv P gen gen_r (Block.userBlockLabels rest) bsNext :=
      stmtsToBlocks_invariant k rest exitConts [] gen gen_r kNext bsNext h_rest_eq hwf
        h_disj_rest_gen_r
    have hwf_r := h_inv_rest.wf_out
    have h_inv_body :
        @GenInv P gen_r gen_b (Block.userBlockLabels bss) bbs :=
      stmtsToBlocks_invariant kNext bss _ [] gen_r gen_b bl bbs h_body_eq hwf_r
        h_disj_bss_gen_b
    have hwf_b := h_inv_body.wf_out
    have h_inv_flush : @GenInv P gen_b gen_f [] accumBlocks :=
      flushCmds_invariant "blk$" accum .none bl gen_b gen_f accumEntry accumBlocks
        h_flush_eq hwf_b
    -- Cross-disjointness premises for trans.
    -- userBlockLabels rest is disjoint from userBlockLabels bss because the
    -- outer userLabelsDisjoint contains pairwise-distinct labels.
    have h_user_disj_rest_bss :
        ∀ x ∈ Block.userBlockLabels rest, x ∉ Block.userBlockLabels bss := by
      intro x h_x_rest h_x_bss
      have h_block := h_disj
      obtain ⟨_, h_nodup_outer, _⟩ := h_block
      rw [Block.userBlockLabels_block_cons] at h_nodup_outer
      -- nodup_outer : (l :: userBlockLabels bss ++ userBlockLabels rest).Nodup
      have h_disj_lr := List.nodup_append.mp h_nodup_outer
      -- left = l :: userBlockLabels bss; right = userBlockLabels rest
      have h_cross := h_disj_lr.2.2
      exact h_cross x (List.mem_cons.mpr (Or.inr h_x_bss)) x h_x_rest rfl
    have h_user_disj_rb_flush :
        ∀ x ∈ Block.userBlockLabels rest ++ Block.userBlockLabels bss, x ∉ ([] : List String) := by
      intros _ _ h_in; simp at h_in
    -- Compose chronologically: gen → gen_r → gen_b → gen_f
    have h_inv_rb :
        @GenInv P gen gen_b
          (Block.userBlockLabels rest ++ Block.userBlockLabels bss)
          (bsNext ++ bbs) :=
      GenInv.trans gen gen_r gen_b _ _ _ _ h_inv_rest h_inv_body h_user_disj_rest_bss
    have h_inv_chron :
        @GenInv P gen gen_f
          ((Block.userBlockLabels rest ++ Block.userBlockLabels bss) ++ [])
          ((bsNext ++ bbs) ++ accumBlocks) :=
      GenInv.trans gen gen_b gen_f _ _ _ _ h_inv_rb h_inv_flush h_user_disj_rb_flush
    -- Simplify userLabels: rest++bss++[] = rest++bss
    have h_user_simp :
        Block.userBlockLabels rest ++ Block.userBlockLabels bss ++ ([] : List String)
        = Block.userBlockLabels rest ++ Block.userBlockLabels bss := by
      simp
    rw [h_user_simp] at h_inv_chron
    -- Permutation on blocks: (bsNext ++ bbs) ++ accumBlocks ~ accumBlocks ++ bbs ++ bsNext
    have h_perm : ((bsNext ++ bbs) ++ accumBlocks).Perm (accumBlocks ++ bbs ++ bsNext) := by
      have h1 : ((bsNext ++ bbs) ++ accumBlocks).Perm (accumBlocks ++ (bsNext ++ bbs)) :=
        List.perm_append_comm
      have h2 : (accumBlocks ++ (bsNext ++ bbs)).Perm (accumBlocks ++ (bbs ++ bsNext)) :=
        List.Perm.append_left accumBlocks List.perm_append_comm
      have h3 : (accumBlocks ++ (bbs ++ bsNext)) = (accumBlocks ++ bbs ++ bsNext) := by
        rw [List.append_assoc]
      exact (h1.trans h2).trans (h3 ▸ List.Perm.refl _)
    have h_inv_out :
        @GenInv P gen gen_f
          (Block.userBlockLabels rest ++ Block.userBlockLabels bss)
          (accumBlocks ++ bbs ++ bsNext) :=
      GenInv.perm gen gen_f _ _ _ h_inv_chron h_perm
    -- The expected userLabels in our goal is `userBlockLabels (.block l bss md :: rest)`
    -- = l :: userBlockLabels bss ++ userBlockLabels rest. We have rest ++ bss; we need to
    -- weaken/permute. Since `weaken` only requires sublist, we use it:
    have h_l_props := Block.userLabel_of_block_head l bss md rest gen' h_disj
    have h_subset :
        ∀ x ∈ Block.userBlockLabels rest ++ Block.userBlockLabels bss,
          x ∈ Block.userBlockLabels (.block l bss md :: rest) := by
      intro x hx
      rw [Block.userBlockLabels_block_cons]
      rw [List.mem_append] at hx
      exact hx.elim
        (fun h => List.mem_append.mpr (Or.inr h))
        (fun h => List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inr h))))
    -- Now case-split on the if l == bl
    by_cases h_eq : l = bl
    · -- l = bl: result blocks = accumBlocks ++ bbs ++ bsNext, no extra l-block
      rw [if_pos h_eq] at h_gen
      simp only [pure, StateT.pure] at h_gen
      have h_pair := (Prod.mk.inj h_gen).1
      have h_entry_eq : accumEntry = entry := (Prod.mk.inj h_pair).1
      have h_blocks_eq : accumBlocks ++ (bbs ++ bsNext) = blocks := (Prod.mk.inj h_pair).2
      subst h_entry_eq
      have h_blks : blocks = accumBlocks ++ bbs ++ bsNext := by
        rw [List.append_assoc]; exact h_blocks_eq.symm
      rw [h_blks, ← h_gen_eq]
      -- Weaken to the goal's userLabels.
      apply GenInv.weaken_userLabels gen gen_f _ _ _ h_inv_out h_subset
      · -- shape on the outer userLabels
        intro x hx
        exact h_disj.1 x hx
      · -- disj on the outer userLabels w.r.t. gen_f = gen'
        intro x hx h_in
        rw [h_gen_eq] at h_in
        exact h_disj.2.2 x hx h_in
      · exact h_disj.2.1
    · -- l ≠ bl: blocks = accumBlocks ++ (l, .goto bl md) :: (bbs ++ bsNext),
      -- entry = accumEntry (after the bug fix that uses accumEntry rather than l).
      rw [if_neg h_eq] at h_gen
      simp only [pure, StateT.pure] at h_gen
      have h_pair := (Prod.mk.inj h_gen).1
      -- Entry is `accumEntry`; we don't constrain entry in GenInv, so this hypothesis
      -- is unused below.
      have h_entry_eq : accumEntry = entry := (Prod.mk.inj h_pair).1
      let lBlk : DetBlock String (Cmd P) P :=
        { cmds := [], transfer := DetTransferCmd.goto bl md }
      have h_blocks_eq :
          accumBlocks ++ (l, lBlk) :: (bbs ++ bsNext) = blocks :=
        (Prod.mk.inj h_pair).2
      -- We have h_inv_out : GenInv ... (rest_lbls ++ bss_lbls) (accumBlocks ++ bbs ++ bsNext)
      -- Goal: GenInv ... (l :: bss_lbls ++ rest_lbls) blocks
      --     = GenInv ... (l :: bss_lbls ++ rest_lbls) (accumBlocks ++ [(l, lBlk)] ++ bbs ++ bsNext)
      -- The (l, lBlk) needs to be inserted as a USER-labeled block (label l).
      rw [← h_blocks_eq]
      -- First permute h_inv_out's blocks to put accumBlocks at the start, then bbs, bsNext.
      -- h_inv_out blocks = accumBlocks ++ bbs ++ bsNext (already this form).
      -- We use cons_user to add (l, lBlk):
      have h_l_props := Block.userLabel_of_block_head l bss md rest gen' h_disj
      -- l ∉ user labels of (rest ++ bss): from disjointness in the outer Nodup.
      have h_l_notin_user_combined : l ∉ Block.userBlockLabels rest ++ Block.userBlockLabels bss := by
        intro h_in
        rw [List.mem_append] at h_in
        exact h_in.elim (fun h => h_l_props.2.2.2 h) (fun h => h_l_props.2.2.1 h)
      -- l ∉ map fst of (accumBlocks ++ bbs ++ bsNext): from h_inv_out.fresh, none of those
      -- labels equal l (l is a user label, and the existing blocks' labels are either
      -- generated or in rest++bss user labels — both disjoint from l).
      have h_l_notin_blks : l ∉ List.map Prod.fst (accumBlocks ++ bbs ++ bsNext) := by
        intro h_in
        rcases h_inv_out.fresh l h_in with h_gen | h_user
        · -- l shape-free vs l ∈ stringGens gen_f (= gen'): contradiction via shape.
          have hwf_out : StringGenState.WF gen_f := h_inv_out.wf_out
          exact userLabel_not_in_stringGens_of_shape_free hwf_out h_l_props.1 h_gen.1
        · exact h_l_notin_user_combined h_user
      -- Now use cons_user, then perm to align block ordering.
      have h_inv_with_l :
          @GenInv P gen gen_f
            (l :: (Block.userBlockLabels rest ++ Block.userBlockLabels bss))
            ((l, lBlk) :: (accumBlocks ++ bbs ++ bsNext)) :=
        GenInv.cons_user gen gen_f _ _ l lBlk h_inv_out
          h_l_props.1 h_l_notin_user_combined h_l_notin_blks
      -- Permute blocks: (l, lBlk) :: (accumBlocks ++ bbs ++ bsNext)
      --   ~ accumBlocks ++ [(l, lBlk)] ++ bbs ++ bsNext
      have h_perm_l : ((l, lBlk) :: (accumBlocks ++ bbs ++ bsNext)).Perm
                      (accumBlocks ++ (l, lBlk) :: (bbs ++ bsNext)) := by
        rw [List.append_assoc accumBlocks bbs bsNext]
        exact (List.perm_middle (a := (l, lBlk))
                (l₁ := accumBlocks) (l₂ := bbs ++ bsNext)).symm
      have h_inv_perm := GenInv.perm gen gen_f _ _ _ h_inv_with_l h_perm_l
      rw [← h_gen_eq]
      -- Convert userLabels: l :: (rest ++ bss) ~ goal's userLabels (l :: bss ++ rest)
      apply GenInv.weaken_userLabels gen gen_f _ _ _ h_inv_perm
      · -- subset
        intro x hx
        rw [Block.userBlockLabels_block_cons]
        rw [List.mem_cons] at hx
        cases hx with
        | inl h => subst h; exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inl rfl)))
        | inr h =>
          rw [List.mem_append] at h
          exact h.elim
            (fun h => List.mem_append.mpr (Or.inr h))
            (fun h => List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inr h))))
      · -- shape on goal's userLabels
        intro x hx
        exact h_disj.1 x hx
      · -- disj on goal's userLabels
        intro x hx h_in
        rw [h_gen_eq] at h_in
        exact h_disj.2.2 x hx h_in
      · exact h_disj.2.1
  | .ite c tss fss md :: rest =>
    -- Sub-computations: rest, gen "ite", tss, fss, optional gen "$__nondet_ite$",
    -- flushCmds (with condGoto transfer). The output is
    -- accumBlocks ++ tbs ++ fbs ++ bsNext.
    simp only [stmtsToBlocks, bind, StateT.bind, pure] at h_gen
    -- Decompose monadic chain
    generalize h_rest_eq : stmtsToBlocks k rest exitConts [] gen = r_rest at h_gen
    obtain ⟨⟨kNext, bsNext⟩, gen_r⟩ := r_rest
    simp only at h_gen
    generalize h_ite_label : StringGenState.gen "ite" gen_r = r_ite at h_gen
    obtain ⟨l_ite, gen_ite⟩ := r_ite
    simp only at h_gen
    generalize h_then_eq : stmtsToBlocks kNext tss exitConts [] gen_ite = r_then at h_gen
    obtain ⟨⟨tl, tbs⟩, gen_t⟩ := r_then
    simp only at h_gen
    generalize h_else_eq : stmtsToBlocks kNext fss exitConts [] gen_t = r_else at h_gen
    obtain ⟨⟨fl, fbs⟩, gen_e⟩ := r_else
    simp only at h_gen
    -- Branch on c (det vs nondet) — this affects extraCmds and possibly an extra gen call.
    cases h_c : c with
    | det e =>
      rw [h_c] at h_gen
      -- After matching c, the structure is:
      -- (do let (e_, ec) ← pure (e, []); flushCmds ...) gen_e = ((entry, blocks), gen')
      -- Unfold pure-bind: this becomes flushCmds "ite$" (accum ++ []) ... gen_e = ...
      -- Then List.append_nil simplifies (accum ++ []) to accum.
      simp only [bind, StateT.bind, pure, StateT.pure, List.append_nil] at h_gen
      generalize h_flush_eq : @flushCmds P (Cmd P) _ "ite$" accum
        (.some (DetTransferCmd.condGoto e tl fl md)) l_ite gen_e = r_flush at h_gen
      obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
      have h_pair := (Prod.mk.inj h_gen).1
      have h_entry_eq : accumEntry = entry := (Prod.mk.inj h_pair).1
      have h_blocks_eq : accumBlocks ++ tbs ++ fbs ++ bsNext = blocks :=
        (Prod.mk.inj h_pair).2
      have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
      subst h_entry_eq
      -- GenStep chain: gen → gen_r → gen_ite → gen_t → gen_e → gen_f
      have h_step_rest := stmtsToBlocks_genStep k rest exitConts [] gen gen_r
        kNext bsNext h_rest_eq
      have h_step_ite : StringGenState.GenStep gen_r gen_ite := by
        rw [show gen_ite = (StringGenState.gen "ite" gen_r).2 from
              (by rw [h_ite_label])]
        exact StringGenState.GenStep.of_gen "ite" gen_r
      have h_step_then := stmtsToBlocks_genStep kNext tss exitConts [] gen_ite gen_t
        tl tbs h_then_eq
      have h_step_else := stmtsToBlocks_genStep kNext fss exitConts [] gen_t gen_e
        fl fbs h_else_eq
      have h_step_flush : StringGenState.GenStep gen_e gen_f :=
        flushCmds_genStep "ite$" accum _ l_ite gen_e gen_f
          accumEntry accumBlocks h_flush_eq
      -- Build subset relations w.r.t. gen' (= gen_f) for monotonicity of disjointness.
      have h_subset_r_gen' : StringGenState.stringGens gen_r ⊆ StringGenState.stringGens gen' := by
        exact h_gen_eq ▸ ((((h_step_ite.trans h_step_then).trans h_step_else)).trans h_step_flush).subset
      have h_subset_ite_gen' : StringGenState.stringGens gen_ite ⊆ StringGenState.stringGens gen' := by
        exact h_gen_eq ▸ (((h_step_then.trans h_step_else)).trans h_step_flush).subset
      have h_subset_t_gen' : StringGenState.stringGens gen_t ⊆ StringGenState.stringGens gen' := by
        exact h_gen_eq ▸ (h_step_else.trans h_step_flush).subset
      have h_subset_e_gen' : StringGenState.stringGens gen_e ⊆ StringGenState.stringGens gen' := by
        exact h_gen_eq ▸ h_step_flush.subset
      -- Disjointness of sub-statements w.r.t. their respective gen states.
      have h_disj_rest_gen' : Block.userLabelsDisjoint rest gen' :=
        Block.userLabelsDisjoint_tail _ _ _ h_disj
      have h_disj_tss_gen' : Block.userLabelsDisjoint tss gen' :=
        Block.userLabelsDisjoint_ite_then c tss fss md rest gen' h_disj
      have h_disj_fss_gen' : Block.userLabelsDisjoint fss gen' :=
        Block.userLabelsDisjoint_ite_else c tss fss md rest gen' h_disj
      have h_disj_rest_gen_r : Block.userLabelsDisjoint rest gen_r :=
        Block.userLabelsDisjoint_mono _ _ _ h_disj_rest_gen' h_subset_r_gen'
      -- For sub-IH inputs we need disjointness w.r.t. each call's OUTPUT state
      -- (since stmtsToBlocks_invariant takes h_disj : disj ss gen').
      have h_disj_tss_gen_t : Block.userLabelsDisjoint tss gen_t :=
        Block.userLabelsDisjoint_mono _ _ _ h_disj_tss_gen' h_subset_t_gen'
      have h_disj_fss_gen_e : Block.userLabelsDisjoint fss gen_e :=
        Block.userLabelsDisjoint_mono _ _ _ h_disj_fss_gen' h_subset_e_gen'
      -- Apply IH to each sub-list.
      have h_inv_rest :
          @GenInv P gen gen_r (Block.userBlockLabels rest) bsNext :=
        stmtsToBlocks_invariant k rest exitConts [] gen gen_r kNext bsNext h_rest_eq hwf
          h_disj_rest_gen_r
      have hwf_r := h_inv_rest.wf_out
      -- Step gen_r → gen_ite has no blocks emitted: build empty GenInv.
      have h_inv_ite_step : @GenInv P gen_r gen_ite [] [] :=
        GenInv.empty_step gen_r gen_ite hwf_r h_step_ite
      have hwf_ite : StringGenState.WF gen_ite := h_inv_ite_step.wf_out
      have h_inv_then :
          @GenInv P gen_ite gen_t (Block.userBlockLabels tss) tbs :=
        stmtsToBlocks_invariant kNext tss exitConts [] gen_ite gen_t tl tbs h_then_eq
          hwf_ite h_disj_tss_gen_t
      have hwf_t := h_inv_then.wf_out
      have h_inv_else :
          @GenInv P gen_t gen_e (Block.userBlockLabels fss) fbs :=
        stmtsToBlocks_invariant kNext fss exitConts [] gen_t gen_e fl fbs h_else_eq
          hwf_t h_disj_fss_gen_e
      have hwf_e := h_inv_else.wf_out
      have h_inv_flush : @GenInv P gen_e gen_f [] accumBlocks :=
        flushCmds_invariant "ite$" accum _ l_ite gen_e gen_f accumEntry accumBlocks
          h_flush_eq hwf_e
      -- Cross-disjointness premises for trans: extract from outer Nodup.
      have ⟨h_te, h_tr, h_er⟩ :=
        Block.userLabels_ite_cross_disj c tss fss md rest gen' h_disj
      -- Compose chronologically: gen → gen_r → gen_ite → gen_t → gen_e → gen_f
      -- Step 1: gen → gen_ite, blocks = bsNext, user = userBlockLabels rest.
      have h_inv_r_ite :
          @GenInv P gen gen_ite (Block.userBlockLabels rest ++ []) (bsNext ++ []) :=
        GenInv.trans gen gen_r gen_ite _ _ _ _ h_inv_rest h_inv_ite_step
          (by intros _ _ h_in; simp at h_in)
      have h_user_r_simp :
          Block.userBlockLabels rest ++ ([] : List String) = Block.userBlockLabels rest := by simp
      have h_blks_r_simp : bsNext ++ ([] : List (String × DetBlock String (Cmd P) P)) = bsNext := by simp
      rw [h_user_r_simp, h_blks_r_simp] at h_inv_r_ite
      -- Step 2: gen → gen_t, blocks = bsNext ++ tbs, user = userBlockLabels rest ++ userBlockLabels tss
      have h_inv_r_t :
          @GenInv P gen gen_t
            (Block.userBlockLabels rest ++ Block.userBlockLabels tss)
            (bsNext ++ tbs) :=
        GenInv.trans gen gen_ite gen_t _ _ _ _ h_inv_r_ite h_inv_then
          (by intro x h_x_r h_x_t; exact h_tr x h_x_t h_x_r)
      -- Step 3: gen → gen_e, blocks = bsNext ++ tbs ++ fbs, user = ... ++ userBlockLabels fss
      have h_inv_r_e :
          @GenInv P gen gen_e
            (Block.userBlockLabels rest ++ Block.userBlockLabels tss ++
              Block.userBlockLabels fss)
            ((bsNext ++ tbs) ++ fbs) := by
        apply GenInv.trans gen gen_t gen_e _ _ _ _ h_inv_r_t h_inv_else
        intro x h_x_in h_x_f
        rw [List.mem_append] at h_x_in
        exact h_x_in.elim (fun h_x_r => h_er x h_x_f h_x_r) (fun h_x_t => h_te x h_x_t h_x_f)
      -- Step 4: gen → gen_f, blocks = ... ++ accumBlocks, user unchanged (flush has [])
      have h_inv_chron :
          @GenInv P gen gen_f
            ((Block.userBlockLabels rest ++ Block.userBlockLabels tss ++
              Block.userBlockLabels fss) ++ [])
            (((bsNext ++ tbs) ++ fbs) ++ accumBlocks) :=
        GenInv.trans gen gen_e gen_f _ _ _ _ h_inv_r_e h_inv_flush
          (by intros _ _ h_in; simp at h_in)
      have h_user_simp :
          Block.userBlockLabels rest ++ Block.userBlockLabels tss ++
            Block.userBlockLabels fss ++ ([] : List String)
          = Block.userBlockLabels rest ++ Block.userBlockLabels tss ++
            Block.userBlockLabels fss := by simp
      rw [h_user_simp] at h_inv_chron
      -- Permute blocks: bsNext ++ tbs ++ fbs ++ accumBlocks ~ accumBlocks ++ tbs ++ fbs ++ bsNext
      have h_perm_blocks :
          (((bsNext ++ tbs) ++ fbs) ++ accumBlocks).Perm
            (accumBlocks ++ tbs ++ fbs ++ bsNext) := by
        -- Reassociate: ((bsNext ++ tbs) ++ fbs) ++ accumBlocks = bsNext ++ (tbs ++ fbs ++ accumBlocks)
        -- And we want: accumBlocks ++ tbs ++ fbs ++ bsNext = (accumBlocks ++ tbs ++ fbs) ++ bsNext
        -- These are perm via "rotate bsNext to the end".
        have h1 : (((bsNext ++ tbs) ++ fbs) ++ accumBlocks).Perm
                  (accumBlocks ++ ((bsNext ++ tbs) ++ fbs)) := List.perm_append_comm
        have h2 : (accumBlocks ++ ((bsNext ++ tbs) ++ fbs)).Perm
                  (accumBlocks ++ ((tbs ++ fbs) ++ bsNext)) :=
          List.Perm.append_left accumBlocks (by
            -- (bsNext ++ tbs) ++ fbs ~ (tbs ++ fbs) ++ bsNext
            have hh1 : ((bsNext ++ tbs) ++ fbs).Perm (fbs ++ (bsNext ++ tbs)) :=
              List.perm_append_comm
            have hh2 : (fbs ++ (bsNext ++ tbs)).Perm (fbs ++ (tbs ++ bsNext)) :=
              List.Perm.append_left fbs List.perm_append_comm
            -- (tbs ++ fbs) ++ bsNext = tbs ++ fbs ++ bsNext = tbs ++ (fbs ++ bsNext)
            -- Need to massage to fbs ++ tbs ++ bsNext. They differ.
            -- Instead, just compute: ((bsNext ++ tbs) ++ fbs) ~ (tbs ++ fbs) ++ bsNext
            have hh3 : (fbs ++ (tbs ++ bsNext)).Perm ((tbs ++ fbs) ++ bsNext) := by
              -- fbs ++ tbs ++ bsNext ~ tbs ++ fbs ++ bsNext via swap of fbs/tbs
              have a : (fbs ++ (tbs ++ bsNext)) = (fbs ++ tbs) ++ bsNext := by
                rw [List.append_assoc]
              have b : ((tbs ++ fbs) ++ bsNext) = (tbs ++ fbs) ++ bsNext := rfl
              rw [a]
              exact List.Perm.append_right bsNext List.perm_append_comm
            exact (hh1.trans hh2).trans hh3)
        have h3 : accumBlocks ++ ((tbs ++ fbs) ++ bsNext) = accumBlocks ++ tbs ++ fbs ++ bsNext := by
          rw [← List.append_assoc, ← List.append_assoc]
        exact (h1.trans h2).trans (h3 ▸ List.Perm.refl _)
      -- The blocks in `blocks` are: accumBlocks ++ tbs ++ fbs ++ bsNext (from h_blocks_eq).
      have h_blks : blocks = accumBlocks ++ tbs ++ fbs ++ bsNext := h_blocks_eq.symm
      rw [h_blks, ← h_gen_eq]
      have h_inv_perm :=
        GenInv.perm gen gen_f _ _ _ h_inv_chron h_perm_blocks
      -- Convert userLabels: (rest ++ tss ++ fss) ⊆ goal's userLabels = (tss ++ fss ++ rest)
      apply GenInv.weaken_userLabels gen gen_f _ _ _ h_inv_perm
      · -- subset
        intro x hx
        rw [Block.userBlockLabels_ite_cons]
        rw [List.mem_append, List.mem_append] at hx
        rcases hx with (h_r | h_t) | h_f
        · exact List.mem_append.mpr (Or.inr h_r)
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h_t)))
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h_f)))
      · -- shape on goal's userLabels (the outer ones from h_disj)
        intro x hx
        exact h_disj.1 x hx
      · -- disj on goal's userLabels w.r.t. gen_f = gen'
        intro x hx h_in
        rw [h_gen_eq] at h_in
        exact h_disj.2.2 x hx h_in
      · exact h_disj.2.1
    | nondet =>
      -- Nondet adds an extra `gen "$__nondet_ite$"` call before flushCmds, plus an init
      -- command in extraCmds. The structure is otherwise identical.
      rw [h_c] at h_gen
      simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
      generalize h_nondet_gen : StringGenState.gen "$__nondet_ite$" gen_e = r_nd at h_gen
      obtain ⟨freshName, gen_n⟩ := r_nd
      simp only at h_gen
      generalize h_flush_eq : @flushCmds P (Cmd P) _ "ite$"
        (accum ++ [HasInit.init (HasIdent.ident (P := P) freshName) HasBool.boolTy
            ExprOrNondet.nondet synthesizedMd])
        (.some (DetTransferCmd.condGoto
          (HasFvar.mkFvar (HasIdent.ident (P := P) freshName)) tl fl md)) l_ite gen_n =
        r_flush at h_gen
      obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
      have h_pair := (Prod.mk.inj h_gen).1
      have h_entry_eq : accumEntry = entry := (Prod.mk.inj h_pair).1
      have h_blocks_eq : accumBlocks ++ tbs ++ fbs ++ bsNext = blocks :=
        (Prod.mk.inj h_pair).2
      have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
      subst h_entry_eq
      -- GenStep chain: gen → gen_r → gen_ite → gen_t → gen_e → gen_n → gen_f
      have h_step_rest := stmtsToBlocks_genStep k rest exitConts [] gen gen_r
        kNext bsNext h_rest_eq
      have h_step_ite : StringGenState.GenStep gen_r gen_ite := by
        rw [show gen_ite = (StringGenState.gen "ite" gen_r).2 from
              (by rw [h_ite_label])]
        exact StringGenState.GenStep.of_gen "ite" gen_r
      have h_step_then := stmtsToBlocks_genStep kNext tss exitConts [] gen_ite gen_t
        tl tbs h_then_eq
      have h_step_else := stmtsToBlocks_genStep kNext fss exitConts [] gen_t gen_e
        fl fbs h_else_eq
      have h_step_nondet : StringGenState.GenStep gen_e gen_n := by
        rw [show gen_n = (StringGenState.gen "$__nondet_ite$" gen_e).2 from
              (by rw [h_nondet_gen])]
        exact StringGenState.GenStep.of_gen "$__nondet_ite$" gen_e
      have h_step_flush : StringGenState.GenStep gen_n gen_f :=
        flushCmds_genStep "ite$" _ _ l_ite gen_n gen_f
          accumEntry accumBlocks h_flush_eq
      -- Subset relations w.r.t. gen' (= gen_f)
      have h_step_r_to_f : StringGenState.GenStep gen_r gen_f :=
        (((h_step_ite.trans h_step_then).trans h_step_else).trans h_step_nondet).trans
          h_step_flush
      have h_subset_r_gen' : StringGenState.stringGens gen_r ⊆ StringGenState.stringGens gen' := by
        exact h_gen_eq ▸ h_step_r_to_f.subset
      have h_subset_ite_gen' : StringGenState.stringGens gen_ite ⊆ StringGenState.stringGens gen' := by
        exact h_gen_eq ▸ (((h_step_then.trans h_step_else).trans h_step_nondet).trans h_step_flush).subset
      have h_subset_t_gen' : StringGenState.stringGens gen_t ⊆ StringGenState.stringGens gen' := by
        exact h_gen_eq ▸ ((h_step_else.trans h_step_nondet).trans h_step_flush).subset
      have h_subset_e_gen' : StringGenState.stringGens gen_e ⊆ StringGenState.stringGens gen' := by
        exact h_gen_eq ▸ (h_step_nondet.trans h_step_flush).subset
      -- Disjointness of sub-statements (extracted from outer ite).
      have h_disj_rest_gen' : Block.userLabelsDisjoint rest gen' :=
        Block.userLabelsDisjoint_tail _ _ _ h_disj
      have h_disj_tss_gen' : Block.userLabelsDisjoint tss gen' :=
        Block.userLabelsDisjoint_ite_then c tss fss md rest gen' h_disj
      have h_disj_fss_gen' : Block.userLabelsDisjoint fss gen' :=
        Block.userLabelsDisjoint_ite_else c tss fss md rest gen' h_disj
      have h_disj_rest_gen_r : Block.userLabelsDisjoint rest gen_r :=
        Block.userLabelsDisjoint_mono _ _ _ h_disj_rest_gen' h_subset_r_gen'
      have h_disj_tss_gen_t : Block.userLabelsDisjoint tss gen_t :=
        Block.userLabelsDisjoint_mono _ _ _ h_disj_tss_gen' h_subset_t_gen'
      have h_disj_fss_gen_e : Block.userLabelsDisjoint fss gen_e :=
        Block.userLabelsDisjoint_mono _ _ _ h_disj_fss_gen' h_subset_e_gen'
      -- Apply IH to each sub-list.
      have h_inv_rest :
          @GenInv P gen gen_r (Block.userBlockLabels rest) bsNext :=
        stmtsToBlocks_invariant k rest exitConts [] gen gen_r kNext bsNext h_rest_eq hwf
          h_disj_rest_gen_r
      have hwf_r := h_inv_rest.wf_out
      have h_inv_ite_step : @GenInv P gen_r gen_ite [] [] :=
        GenInv.empty_step gen_r gen_ite hwf_r h_step_ite
      have hwf_ite : StringGenState.WF gen_ite := h_inv_ite_step.wf_out
      have h_inv_then :
          @GenInv P gen_ite gen_t (Block.userBlockLabels tss) tbs :=
        stmtsToBlocks_invariant kNext tss exitConts [] gen_ite gen_t tl tbs h_then_eq
          hwf_ite h_disj_tss_gen_t
      have hwf_t := h_inv_then.wf_out
      have h_inv_else :
          @GenInv P gen_t gen_e (Block.userBlockLabels fss) fbs :=
        stmtsToBlocks_invariant kNext fss exitConts [] gen_t gen_e fl fbs h_else_eq
          hwf_t h_disj_fss_gen_e
      have hwf_e := h_inv_else.wf_out
      have h_inv_nondet_step : @GenInv P gen_e gen_n [] [] :=
        GenInv.empty_step gen_e gen_n hwf_e h_step_nondet
      have hwf_n : StringGenState.WF gen_n := h_inv_nondet_step.wf_out
      have h_inv_flush : @GenInv P gen_n gen_f [] accumBlocks :=
        flushCmds_invariant "ite$" _ _ l_ite gen_n gen_f accumEntry accumBlocks
          h_flush_eq hwf_n
      -- Cross-disjointness premises for trans: extract from outer Nodup.
      have ⟨h_te, h_tr, h_er⟩ :=
        Block.userLabels_ite_cross_disj c tss fss md rest gen' h_disj
      -- Compose chronologically
      have h_inv_r_ite :
          @GenInv P gen gen_ite (Block.userBlockLabels rest ++ []) (bsNext ++ []) :=
        GenInv.trans gen gen_r gen_ite _ _ _ _ h_inv_rest h_inv_ite_step
          (by intros _ _ h_in; simp at h_in)
      have h_user_r_simp :
          Block.userBlockLabels rest ++ ([] : List String) = Block.userBlockLabels rest := by simp
      have h_blks_r_simp : bsNext ++ ([] : List (String × DetBlock String (Cmd P) P)) = bsNext := by simp
      rw [h_user_r_simp, h_blks_r_simp] at h_inv_r_ite
      have h_inv_r_t :
          @GenInv P gen gen_t
            (Block.userBlockLabels rest ++ Block.userBlockLabels tss)
            (bsNext ++ tbs) :=
        GenInv.trans gen gen_ite gen_t _ _ _ _ h_inv_r_ite h_inv_then
          (by intro x h_x_r h_x_t; exact h_tr x h_x_t h_x_r)
      have h_inv_r_e :
          @GenInv P gen gen_e
            (Block.userBlockLabels rest ++ Block.userBlockLabels tss ++
              Block.userBlockLabels fss)
            ((bsNext ++ tbs) ++ fbs) := by
        apply GenInv.trans gen gen_t gen_e _ _ _ _ h_inv_r_t h_inv_else
        intro x h_x_in h_x_f
        rw [List.mem_append] at h_x_in
        exact h_x_in.elim (fun h_x_r => h_er x h_x_f h_x_r) (fun h_x_t => h_te x h_x_t h_x_f)
      -- Step 4: gen → gen_n via empty step
      have h_inv_r_n :
          @GenInv P gen gen_n
            ((Block.userBlockLabels rest ++ Block.userBlockLabels tss ++
              Block.userBlockLabels fss) ++ [])
            (((bsNext ++ tbs) ++ fbs) ++ []) :=
        GenInv.trans gen gen_e gen_n _ _ _ _ h_inv_r_e h_inv_nondet_step
          (by intros _ _ h_in; simp at h_in)
      have h_user_simp_n :
          Block.userBlockLabels rest ++ Block.userBlockLabels tss ++
            Block.userBlockLabels fss ++ ([] : List String)
          = Block.userBlockLabels rest ++ Block.userBlockLabels tss ++
            Block.userBlockLabels fss := by simp
      have h_blks_simp_n :
          (bsNext ++ tbs) ++ fbs ++ ([] : List (String × DetBlock String (Cmd P) P))
          = (bsNext ++ tbs) ++ fbs := by simp
      rw [h_user_simp_n, h_blks_simp_n] at h_inv_r_n
      -- Step 5: gen → gen_f via flush
      have h_inv_chron :
          @GenInv P gen gen_f
            ((Block.userBlockLabels rest ++ Block.userBlockLabels tss ++
              Block.userBlockLabels fss) ++ [])
            (((bsNext ++ tbs) ++ fbs) ++ accumBlocks) :=
        GenInv.trans gen gen_n gen_f _ _ _ _ h_inv_r_n h_inv_flush
          (by intros _ _ h_in; simp at h_in)
      have h_user_simp :
          Block.userBlockLabels rest ++ Block.userBlockLabels tss ++
            Block.userBlockLabels fss ++ ([] : List String)
          = Block.userBlockLabels rest ++ Block.userBlockLabels tss ++
            Block.userBlockLabels fss := by simp
      rw [h_user_simp] at h_inv_chron
      -- Permute blocks: identical to det case
      have h_perm_blocks :
          (((bsNext ++ tbs) ++ fbs) ++ accumBlocks).Perm
            (accumBlocks ++ tbs ++ fbs ++ bsNext) := by
        have h1 : (((bsNext ++ tbs) ++ fbs) ++ accumBlocks).Perm
                  (accumBlocks ++ ((bsNext ++ tbs) ++ fbs)) := List.perm_append_comm
        have h2 : (accumBlocks ++ ((bsNext ++ tbs) ++ fbs)).Perm
                  (accumBlocks ++ ((tbs ++ fbs) ++ bsNext)) :=
          List.Perm.append_left accumBlocks (by
            have hh1 : ((bsNext ++ tbs) ++ fbs).Perm (fbs ++ (bsNext ++ tbs)) :=
              List.perm_append_comm
            have hh2 : (fbs ++ (bsNext ++ tbs)).Perm (fbs ++ (tbs ++ bsNext)) :=
              List.Perm.append_left fbs List.perm_append_comm
            have hh3 : (fbs ++ (tbs ++ bsNext)).Perm ((tbs ++ fbs) ++ bsNext) := by
              have a : (fbs ++ (tbs ++ bsNext)) = (fbs ++ tbs) ++ bsNext := by
                rw [List.append_assoc]
              rw [a]
              exact List.Perm.append_right bsNext List.perm_append_comm
            exact (hh1.trans hh2).trans hh3)
        have h3 : accumBlocks ++ ((tbs ++ fbs) ++ bsNext) = accumBlocks ++ tbs ++ fbs ++ bsNext := by
          rw [← List.append_assoc, ← List.append_assoc]
        exact (h1.trans h2).trans (h3 ▸ List.Perm.refl _)
      have h_blks : blocks = accumBlocks ++ tbs ++ fbs ++ bsNext := h_blocks_eq.symm
      rw [h_blks, ← h_gen_eq]
      have h_inv_perm :=
        GenInv.perm gen gen_f _ _ _ h_inv_chron h_perm_blocks
      apply GenInv.weaken_userLabels gen gen_f _ _ _ h_inv_perm
      · intro x hx
        rw [Block.userBlockLabels_ite_cons]
        rw [List.mem_append, List.mem_append] at hx
        rcases hx with (h_r | h_t) | h_f
        · exact List.mem_append.mpr (Or.inr h_r)
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h_t)))
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h_f)))
      · intro x hx
        exact h_disj.1 x hx
      · intro x hx h_in
        rw [h_gen_eq] at h_in
        exact h_disj.2.2 x hx h_in
      · exact h_disj.2.1
  | .loop c m is bss md :: rest =>
    -- Chronological pipeline:
    --   gen → gen_r:    stmtsToBlocks rest
    --   gen_r → gen_le: gen "loop_entry$"
    --   gen_le → gen_m: match m (none: id; some: gen "loop_measure$" then gen "measure_decrease$")
    --   gen_m → gen_b:  stmtsToBlocks bss
    --   gen_b → gen_i:  is.mapM
    --   gen_i → gen_? : match c (det: id; nondet: gen "$__nondet_loop$")
    --   gen_? → gen_f:  flushCmds "before_loop$"
    --
    -- We split on `m` first (this also reduces the contractMd `match m`),
    -- then on `c`, giving 4 sub-branches (none/some × det/nondet).
    simp only [stmtsToBlocks, bind, StateT.bind] at h_gen
    -- Decompose: rest and lentry.
    generalize h_rest_eq : stmtsToBlocks k rest exitConts [] gen = r_rest at h_gen
    obtain ⟨⟨kNext, bsNext⟩, gen_r⟩ := r_rest
    simp only at h_gen
    generalize h_lentry_def : StringGenState.gen "loop_entry$" gen_r = r_le at h_gen
    obtain ⟨lentry, gen_le⟩ := r_le
    simp only at h_gen
    -- GenStep helpers (for subset relations and monotonicity).
    have h_step_rest := stmtsToBlocks_genStep k rest exitConts [] gen gen_r
      kNext bsNext h_rest_eq
    have h_step_le : StringGenState.GenStep gen_r gen_le := by
      rw [show gen_le = (StringGenState.gen "loop_entry$" gen_r).2 from
            (by rw [h_lentry_def])]
      exact StringGenState.GenStep.of_gen "loop_entry$" gen_r
    -- Disjointness for sub-lists w.r.t. gen' (the outer final state).
    have h_disj_rest_gen' : Block.userLabelsDisjoint rest gen' :=
      Block.userLabelsDisjoint_tail _ _ _ h_disj
    have h_disj_bss_gen' : Block.userLabelsDisjoint bss gen' :=
      Block.userLabelsDisjoint_loop_body c m is bss md rest gen' h_disj
    have h_user_disj_bss_rest :
        ∀ x ∈ Block.userBlockLabels bss, x ∉ Block.userBlockLabels rest :=
      Block.userLabels_loop_cross_disj c m is bss md rest gen' h_disj
    -- Now branch on m, then on c.
    cases h_m_cases : m with
    | none =>
      rw [h_m_cases] at h_gen
      simp only [pure, StateT.pure, bind, StateT.bind] at h_gen
      -- Decompose body, mapM.
      generalize h_body_eq :
        stmtsToBlocks lentry bss ((none, kNext) :: exitConts) [] gen_le = r_body at h_gen
      obtain ⟨⟨bl, bbs⟩, gen_b⟩ := r_body
      simp only at h_gen
      generalize h_inv_def :
        ((is.mapM (fun (srcLabel, i) => do
            let assertLabel ←
              if srcLabel.isEmpty then StringGenState.gen "inv$"
              else pure srcLabel
            pure (HasPassiveCmds.assert (P := P) (CmdT := Cmd P) assertLabel i synthesizedMd)))
         : LabelGen.StringGenM (List (Cmd P))) gen_b = r_inv at h_gen
      obtain ⟨invCmds, gen_i⟩ := r_inv
      simp only at h_gen
      have h_step_body := stmtsToBlocks_genStep lentry bss _ [] gen_le gen_b bl bbs h_body_eq
      have h_step_inv : StringGenState.GenStep gen_b gen_i :=
        invMapM_genStep is gen_b gen_i invCmds h_inv_def
      cases h_c : c with
      | det e =>
        rw [h_c] at h_gen
        simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
        generalize h_flush_eq : @flushCmds P (Cmd P) _ "before_loop$" accum
          Option.none lentry gen_i = r_flush at h_gen
        obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
        have h_pair := (Prod.mk.inj h_gen).1
        have h_entry_eq : accumEntry = entry := (Prod.mk.inj h_pair).1
        have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
        subst h_entry_eq
        -- The lentry block content.
        let contractMd : MetaData P := is.foldl (fun md (_, inv) =>
            md.pushElem MetaData.specLoopInvariant (.expr inv)) md
        let lentryBlk : DetBlock String (Cmd P) P :=
          { cmds := invCmds ++ [],
            transfer := DetTransferCmd.condGoto e bl kNext contractMd }
        have h_blocks_eq :
            accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ [] ++ bsNext = blocks :=
          (Prod.mk.inj h_pair).2
        have h_step_flush : StringGenState.GenStep gen_i gen_f :=
          flushCmds_genStep "before_loop$" accum _ lentry gen_i gen_f
            accumEntry accumBlocks h_flush_eq
        -- Subset relations w.r.t. gen' = gen_f.
        have h_step_chain_r_to_f : StringGenState.GenStep gen_r gen_f :=
          (((h_step_le.trans h_step_body).trans h_step_inv).trans h_step_flush)
        have h_subset_r_gen' : StringGenState.stringGens gen_r ⊆ StringGenState.stringGens gen' := by
          rw [← h_gen_eq]; exact h_step_chain_r_to_f.subset
        have h_subset_le_gen' : StringGenState.stringGens gen_le ⊆ StringGenState.stringGens gen' := by
          rw [← h_gen_eq]; exact ((h_step_body.trans h_step_inv).trans h_step_flush).subset
        have h_subset_b_gen' : StringGenState.stringGens gen_b ⊆ StringGenState.stringGens gen' := by
          rw [← h_gen_eq]; exact (h_step_inv.trans h_step_flush).subset
        have h_subset_i_gen' : StringGenState.stringGens gen_i ⊆ StringGenState.stringGens gen' := by
          rw [← h_gen_eq]; exact h_step_flush.subset
        -- Disjointness for sub-IH inputs.
        have h_disj_rest_gen_r : Block.userLabelsDisjoint rest gen_r :=
          Block.userLabelsDisjoint_mono _ _ _ h_disj_rest_gen' h_subset_r_gen'
        have h_disj_bss_gen_b : Block.userLabelsDisjoint bss gen_b :=
          Block.userLabelsDisjoint_mono _ _ _ h_disj_bss_gen' h_subset_b_gen'
        -- IH on rest.
        have h_inv_rest :
            @GenInv P gen gen_r (Block.userBlockLabels rest) bsNext :=
          stmtsToBlocks_invariant k rest exitConts [] gen gen_r kNext bsNext h_rest_eq hwf
            h_disj_rest_gen_r
        have hwf_r := h_inv_rest.wf_out
        -- gen_r → gen_le via empty_step.
        have h_inv_le_step : @GenInv P gen_r gen_le [] [] :=
          GenInv.empty_step gen_r gen_le hwf_r h_step_le
        have hwf_le : StringGenState.WF gen_le := h_inv_le_step.wf_out
        -- IH on body (bss).
        have h_inv_body :
            @GenInv P gen_le gen_b (Block.userBlockLabels bss) bbs :=
          stmtsToBlocks_invariant lentry bss _ [] gen_le gen_b bl bbs h_body_eq hwf_le
            h_disj_bss_gen_b
        have hwf_b := h_inv_body.wf_out
        -- gen_b → gen_i via empty_step.
        have h_inv_inv_step : @GenInv P gen_b gen_i [] [] :=
          GenInv.empty_step gen_b gen_i hwf_b h_step_inv
        have hwf_i : StringGenState.WF gen_i := h_inv_inv_step.wf_out
        -- gen_i → gen_f via flush invariant.
        have h_inv_flush : @GenInv P gen_i gen_f [] accumBlocks :=
          flushCmds_invariant "before_loop$" accum _ lentry gen_i gen_f
            accumEntry accumBlocks h_flush_eq hwf_i
        -- Compose chronologically: gen → gen_r → gen_le → gen_b → gen_i → gen_f.
        have h_inv_r_le :
            @GenInv P gen gen_le (Block.userBlockLabels rest ++ []) (bsNext ++ []) :=
          GenInv.trans gen gen_r gen_le _ _ _ _ h_inv_rest h_inv_le_step
            (by intros _ _ h_in; simp at h_in)
        have h_user_r_simp :
            Block.userBlockLabels rest ++ ([] : List String) = Block.userBlockLabels rest := by simp
        have h_blks_r_simp : bsNext ++ ([] : List (String × DetBlock String (Cmd P) P)) = bsNext := by simp
        rw [h_user_r_simp, h_blks_r_simp] at h_inv_r_le
        have h_inv_r_b :
            @GenInv P gen gen_b
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss)
              (bsNext ++ bbs) :=
          GenInv.trans gen gen_le gen_b _ _ _ _ h_inv_r_le h_inv_body
            (by intro x h_x_r h_x_b; exact h_user_disj_bss_rest x h_x_b h_x_r)
        have h_inv_r_i :
            @GenInv P gen gen_i
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss ++ [])
              ((bsNext ++ bbs) ++ []) :=
          GenInv.trans gen gen_b gen_i _ _ _ _ h_inv_r_b h_inv_inv_step
            (by intros _ _ h_in; simp at h_in)
        have h_user_simp_i :
            Block.userBlockLabels rest ++ Block.userBlockLabels bss ++ ([] : List String)
            = Block.userBlockLabels rest ++ Block.userBlockLabels bss := by simp
        have h_blks_simp_i :
            (bsNext ++ bbs) ++ ([] : List (String × DetBlock String (Cmd P) P))
            = bsNext ++ bbs := by simp
        rw [h_user_simp_i, h_blks_simp_i] at h_inv_r_i
        have h_inv_chron :
            @GenInv P gen gen_f
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss ++ [])
              ((bsNext ++ bbs) ++ accumBlocks) :=
          GenInv.trans gen gen_i gen_f _ _ _ _ h_inv_r_i h_inv_flush
            (by intros _ _ h_in; simp at h_in)
        have h_user_simp :
            Block.userBlockLabels rest ++ Block.userBlockLabels bss ++ ([] : List String)
            = Block.userBlockLabels rest ++ Block.userBlockLabels bss := by simp
        rw [h_user_simp] at h_inv_chron
        -- Prepend (lentry, lentryBlk) using cons_gen. lentry is generated from gen_r.
        have h_lentry_in_gen_le : lentry ∈ StringGenState.stringGens gen_le := by
          rw [show lentry = (StringGenState.gen "loop_entry$" gen_r).1 from
                (by rw [h_lentry_def])]
          rw [show gen_le = (StringGenState.gen "loop_entry$" gen_r).2 from
                (by rw [h_lentry_def])]
          rw [StringGenState.stringGens_gen]
          exact List.mem_cons.mpr (Or.inl rfl)
        have h_lentry_in_gen_f : lentry ∈ StringGenState.stringGens gen_f :=
          ((h_step_body.trans h_step_inv).trans h_step_flush).subset h_lentry_in_gen_le
        have h_lentry_notin_gen_r : lentry ∉ StringGenState.stringGens gen_r := by
          intro h_in
          have h_lentry_eq : lentry = (StringGenState.gen "loop_entry$" gen_r).1 := by
            rw [h_lentry_def]
          have h_notin :=
            StringGenState.stringGens_gen_not_in "loop_entry$" gen_r hwf_r
          rw [h_lentry_eq] at h_in
          exact h_notin h_in
        have h_lentry_notin_gen : lentry ∉ StringGenState.stringGens gen := by
          intro h_in; exact h_lentry_notin_gen_r (h_step_rest.subset h_in)
        -- lentry not in any of the existing block labels (bsNext, bbs, accumBlocks).
        have h_lentry_notin_blks : lentry ∉ List.map Prod.fst ((bsNext ++ bbs) ++ accumBlocks) := by
          intro h_in
          rcases h_inv_chron.fresh lentry h_in with h_g | h_user
          · -- lentry ∈ gen_f \ gen — but lentry was generated from gen_r, so
            -- lentry was generated before this whole computation? No, lentry IS
            -- in gen_le ⊆ gen_f, but we've shown lentry ∉ gen_r. So
            -- lentry ∉ gen ⇒ contradicts h_g.2. Actually h_g.2 says lentry ∉ gen,
            -- which is true. So this branch tells us nothing inconsistent;
            -- we need to show this lentry-as-block-label is impossible.
            -- Actually the issue: cons_gen requires lentry ∉ existing block labels.
            -- One of bsNext, bbs, accumBlocks could have lentry as a label.
            -- But: bsNext came from gen → gen_r (so its labels are in gen_r),
            --      bbs came from gen_le → gen_b (labels in gen_b),
            --      accumBlocks came from gen_i → gen_f (labels in gen_f \ gen_i).
            -- bsNext's labels ⊆ gen_r: but lentry ∉ gen_r. Good.
            -- bbs's labels: each is in gen_b \ gen_le or in user labels of bss.
            --   (a) gen_b \ gen_le: lentry ∈ gen_le, so excludes lentry.
            --   (b) user labels of bss: would mean lentry has user shape, but
            --       lentry was just generated, so it has gen-shape from gen_le.
            --       More precisely, by user_disj of h_disj on bss, user-labels
            --       are not in gen' = gen_f. But lentry ∈ gen_f, so lentry is
            --       NOT a user label.
            -- accumBlocks's labels ⊆ gen_f \ gen_i. lentry ∈ gen_le ⊆ gen_i, so
            --   lentry is in gen_i. Contradicts the freshness condition.
            -- We have h_g.2 : lentry ∉ stringGens gen. That's just true, not contradictory.
            -- We need the deeper fact: lentry is not in any of these block-label sets.
            -- The cleanest route: show separately for each of the three block lists.
            rw [List.map_append, List.map_append, List.mem_append, List.mem_append] at h_in
            rcases h_in with (h_bs | h_bb) | h_ac
            · -- bsNext: from h_inv_rest.fresh
              rcases h_inv_rest.fresh lentry h_bs with h_gr | h_user
              · exact h_lentry_notin_gen_r h_gr.1
              · have h_shape := h_inv_rest.user_shape lentry h_user
                have h_shape_lentry : String.HasUnderscoreDigitSuffix lentry :=
                  StringGenState.hasUnderscoreDigitSuffix_of_mem_generated
                    h_inv_le_step.wf_out h_lentry_in_gen_le
                exact h_shape h_shape_lentry
            · -- bbs: from h_inv_body.fresh
              rcases h_inv_body.fresh lentry h_bb with h_gb | h_user
              · -- lentry ∉ stringGens gen_le (= h_gb.2): but h_lentry_in_gen_le says lentry ∈ gen_le.
                exact h_gb.2 h_lentry_in_gen_le
              · -- lentry would be a user label of bss
                have h_shape := h_inv_body.user_shape lentry h_user
                have h_shape_lentry :
                    String.HasUnderscoreDigitSuffix lentry :=
                  StringGenState.hasUnderscoreDigitSuffix_of_mem_generated
                    (h_inv_le_step.wf_out) h_lentry_in_gen_le
                exact h_shape h_shape_lentry
            · -- accumBlocks: from h_inv_flush.fresh
              cases h_inv_flush.fresh lentry h_ac with
              | inl h_gf => exact h_gf.2 ((h_step_body.trans h_step_inv).subset h_lentry_in_gen_le)
              | inr h_user => simp at h_user
          · -- lentry would be in (rest ++ bss) user labels: shape contradiction.
            have h_shape : ¬ String.HasUnderscoreDigitSuffix lentry := by
              rw [List.mem_append] at h_user
              exact h_user.elim
                (fun h_r => h_inv_rest.user_shape lentry h_r)
                (fun h_b => h_inv_body.user_shape lentry h_b)
            have h_shape_lentry :
                String.HasUnderscoreDigitSuffix lentry :=
              StringGenState.hasUnderscoreDigitSuffix_of_mem_generated
                (h_inv_le_step.wf_out) h_lentry_in_gen_le
            exact h_shape h_shape_lentry
        -- Now apply cons_gen.
        have h_inv_with_lentry :
            @GenInv P gen gen_f
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss)
              ((lentry, lentryBlk) :: ((bsNext ++ bbs) ++ accumBlocks)) :=
          GenInv.cons_gen gen gen gen_f _ _ lentry lentryBlk hwf
            (StringGenState.GenStep.refl gen) h_inv_chron h_lentry_in_gen_f
            h_lentry_notin_gen h_lentry_notin_blks
        -- Permute to align with output ordering: accumBlocks ++ [(lentry,_)] ++ bbs ++ [] ++ bsNext
        --   ~ (lentry,_) :: (bsNext ++ bbs ++ accumBlocks).
        have h_perm :
            ((lentry, lentryBlk) :: ((bsNext ++ bbs) ++ accumBlocks)).Perm
              (accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ [] ++ bsNext) := by
          have h_target :
              accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ ([] : List (String × DetBlock String (Cmd P) P)) ++ bsNext
              = accumBlocks ++ ((lentry, lentryBlk) :: (bbs ++ bsNext)) := by
            simp [List.append_assoc]
          rw [h_target]
          have h1 : ((lentry, lentryBlk) :: ((bsNext ++ bbs) ++ accumBlocks)).Perm
                    ((lentry, lentryBlk) :: (accumBlocks ++ (bsNext ++ bbs))) :=
            List.Perm.cons _ List.perm_append_comm
          have h2 : ((lentry, lentryBlk) :: (accumBlocks ++ (bsNext ++ bbs))).Perm
                    (accumBlocks ++ (lentry, lentryBlk) :: (bsNext ++ bbs)) :=
            (List.perm_middle (a := (lentry, lentryBlk))
              (l₁ := accumBlocks) (l₂ := bsNext ++ bbs)).symm
          have h3 : (accumBlocks ++ (lentry, lentryBlk) :: (bsNext ++ bbs)).Perm
                    (accumBlocks ++ (lentry, lentryBlk) :: (bbs ++ bsNext)) :=
            List.Perm.append_left accumBlocks
              (List.Perm.cons _ List.perm_append_comm)
          exact (h1.trans h2).trans h3
        have h_inv_perm := GenInv.perm gen gen_f _ _ _ h_inv_with_lentry h_perm
        rw [← h_blocks_eq, ← h_gen_eq]
        -- Goal userLabels: userBlockLabels (.loop ...) = bss-labels ++ rest-labels
        rw [Block.userBlockLabels_loop_cons]
        apply GenInv.weaken_userLabels gen gen_f _ _ _ h_inv_perm
        · intro x hx
          rw [List.mem_append] at hx
          rw [List.mem_append]
          exact hx.elim (fun h_r => Or.inr h_r) (fun h_b => Or.inl h_b)
        · intro x hx; exact h_disj.1 x hx
        · intro x hx h_in
          rw [h_gen_eq] at h_in
          exact h_disj.2.2 x hx h_in
        · exact h_disj.2.1
      | nondet =>
        rw [h_c] at h_gen
        simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
        generalize h_nondet_gen : StringGenState.gen "$__nondet_loop$" gen_i = r_nd at h_gen
        obtain ⟨freshName, gen_n⟩ := r_nd
        simp only at h_gen
        generalize h_flush_eq : @flushCmds P (Cmd P) _ "before_loop$" accum
          Option.none lentry gen_n = r_flush at h_gen
        obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
        have h_pair := (Prod.mk.inj h_gen).1
        have h_entry_eq : accumEntry = entry := (Prod.mk.inj h_pair).1
        have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
        subst h_entry_eq
        let contractMd : MetaData P := is.foldl (fun md (_, inv) =>
            md.pushElem MetaData.specLoopInvariant (.expr inv)) md
        let lentryBlk : DetBlock String (Cmd P) P :=
          { cmds := [HasInit.init (HasIdent.ident (P := P) freshName)
                       HasBool.boolTy ExprOrNondet.nondet synthesizedMd] ++ invCmds ++ [],
            transfer := DetTransferCmd.condGoto
                          (HasFvar.mkFvar (HasIdent.ident (P := P) freshName)) bl kNext contractMd }
        have h_blocks_eq :
            accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ [] ++ bsNext = blocks :=
          (Prod.mk.inj h_pair).2
        have h_step_nondet : StringGenState.GenStep gen_i gen_n := by
          rw [show gen_n = (StringGenState.gen "$__nondet_loop$" gen_i).2 from
                (by rw [h_nondet_gen])]
          exact StringGenState.GenStep.of_gen "$__nondet_loop$" gen_i
        have h_step_flush : StringGenState.GenStep gen_n gen_f :=
          flushCmds_genStep "before_loop$" accum _ lentry gen_n gen_f
            accumEntry accumBlocks h_flush_eq
        -- Subset relations.
        have h_step_chain_r_to_f : StringGenState.GenStep gen_r gen_f :=
          ((((h_step_le.trans h_step_body).trans h_step_inv).trans h_step_nondet).trans
            h_step_flush)
        have h_subset_r_gen' : StringGenState.stringGens gen_r ⊆ StringGenState.stringGens gen' := by
          rw [← h_gen_eq]; exact h_step_chain_r_to_f.subset
        have h_subset_b_gen' : StringGenState.stringGens gen_b ⊆ StringGenState.stringGens gen' := by
          exact h_gen_eq ▸ ((h_step_inv.trans h_step_nondet).trans h_step_flush).subset
        -- Disjointness for sub-IH.
        have h_disj_rest_gen_r : Block.userLabelsDisjoint rest gen_r :=
          Block.userLabelsDisjoint_mono _ _ _ h_disj_rest_gen' h_subset_r_gen'
        have h_disj_bss_gen_b : Block.userLabelsDisjoint bss gen_b :=
          Block.userLabelsDisjoint_mono _ _ _ h_disj_bss_gen' h_subset_b_gen'
        have h_inv_rest :
            @GenInv P gen gen_r (Block.userBlockLabels rest) bsNext :=
          stmtsToBlocks_invariant k rest exitConts [] gen gen_r kNext bsNext h_rest_eq hwf
            h_disj_rest_gen_r
        have hwf_r := h_inv_rest.wf_out
        have h_inv_le_step : @GenInv P gen_r gen_le [] [] :=
          GenInv.empty_step gen_r gen_le hwf_r h_step_le
        have hwf_le : StringGenState.WF gen_le := h_inv_le_step.wf_out
        have h_inv_body :
            @GenInv P gen_le gen_b (Block.userBlockLabels bss) bbs :=
          stmtsToBlocks_invariant lentry bss _ [] gen_le gen_b bl bbs h_body_eq hwf_le
            h_disj_bss_gen_b
        have hwf_b := h_inv_body.wf_out
        have h_inv_inv_step : @GenInv P gen_b gen_i [] [] :=
          GenInv.empty_step gen_b gen_i hwf_b h_step_inv
        have hwf_i : StringGenState.WF gen_i := h_inv_inv_step.wf_out
        have h_inv_nondet_step : @GenInv P gen_i gen_n [] [] :=
          GenInv.empty_step gen_i gen_n hwf_i h_step_nondet
        have hwf_n : StringGenState.WF gen_n := h_inv_nondet_step.wf_out
        have h_inv_flush : @GenInv P gen_n gen_f [] accumBlocks :=
          flushCmds_invariant "before_loop$" accum _ lentry gen_n gen_f
            accumEntry accumBlocks h_flush_eq hwf_n
        -- Compose chronologically.
        have h_inv_r_le :
            @GenInv P gen gen_le (Block.userBlockLabels rest ++ []) (bsNext ++ []) :=
          GenInv.trans gen gen_r gen_le _ _ _ _ h_inv_rest h_inv_le_step
            (by intros _ _ h_in; simp at h_in)
        have h_user_r_simp :
            Block.userBlockLabels rest ++ ([] : List String) = Block.userBlockLabels rest := by simp
        have h_blks_r_simp : bsNext ++ ([] : List (String × DetBlock String (Cmd P) P)) = bsNext := by simp
        rw [h_user_r_simp, h_blks_r_simp] at h_inv_r_le
        have h_inv_r_b :
            @GenInv P gen gen_b
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss)
              (bsNext ++ bbs) :=
          GenInv.trans gen gen_le gen_b _ _ _ _ h_inv_r_le h_inv_body
            (by intro x h_x_r h_x_b; exact h_user_disj_bss_rest x h_x_b h_x_r)
        have h_inv_r_i :
            @GenInv P gen gen_i
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss ++ [])
              ((bsNext ++ bbs) ++ []) :=
          GenInv.trans gen gen_b gen_i _ _ _ _ h_inv_r_b h_inv_inv_step
            (by intros _ _ h_in; simp at h_in)
        have h_user_simp_i :
            Block.userBlockLabels rest ++ Block.userBlockLabels bss ++ ([] : List String)
            = Block.userBlockLabels rest ++ Block.userBlockLabels bss := by simp
        have h_blks_simp_i :
            (bsNext ++ bbs) ++ ([] : List (String × DetBlock String (Cmd P) P))
            = bsNext ++ bbs := by simp
        rw [h_user_simp_i, h_blks_simp_i] at h_inv_r_i
        have h_inv_r_n :
            @GenInv P gen gen_n
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss ++ [])
              ((bsNext ++ bbs) ++ []) :=
          GenInv.trans gen gen_i gen_n _ _ _ _ h_inv_r_i h_inv_nondet_step
            (by intros _ _ h_in; simp at h_in)
        rw [h_user_simp_i, h_blks_simp_i] at h_inv_r_n
        have h_inv_chron :
            @GenInv P gen gen_f
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss ++ [])
              ((bsNext ++ bbs) ++ accumBlocks) :=
          GenInv.trans gen gen_n gen_f _ _ _ _ h_inv_r_n h_inv_flush
            (by intros _ _ h_in; simp at h_in)
        rw [h_user_simp_i] at h_inv_chron
        -- Prepend lentry block via cons_gen.
        have h_lentry_in_gen_le : lentry ∈ StringGenState.stringGens gen_le := by
          rw [show lentry = (StringGenState.gen "loop_entry$" gen_r).1 from
                (by rw [h_lentry_def])]
          rw [show gen_le = (StringGenState.gen "loop_entry$" gen_r).2 from
                (by rw [h_lentry_def])]
          rw [StringGenState.stringGens_gen]
          exact List.mem_cons.mpr (Or.inl rfl)
        have h_lentry_in_gen_f : lentry ∈ StringGenState.stringGens gen_f :=
          (((h_step_body.trans h_step_inv).trans h_step_nondet).trans h_step_flush).subset
            h_lentry_in_gen_le
        have h_lentry_notin_gen_r : lentry ∉ StringGenState.stringGens gen_r := by
          intro h_in
          have h_lentry_eq : lentry = (StringGenState.gen "loop_entry$" gen_r).1 := by
            rw [h_lentry_def]
          have h_notin :=
            StringGenState.stringGens_gen_not_in "loop_entry$" gen_r hwf_r
          rw [h_lentry_eq] at h_in
          exact h_notin h_in
        have h_lentry_notin_gen : lentry ∉ StringGenState.stringGens gen := by
          intro h_in; exact h_lentry_notin_gen_r (h_step_rest.subset h_in)
        have h_lentry_notin_blks : lentry ∉ List.map Prod.fst ((bsNext ++ bbs) ++ accumBlocks) := by
          intro h_in
          rw [List.map_append, List.map_append, List.mem_append, List.mem_append] at h_in
          rcases h_in with (h_bs | h_bb) | h_ac
          · rcases h_inv_rest.fresh lentry h_bs with h_gr | h_user
            · exact h_lentry_notin_gen_r h_gr.1
            · have h_shape := h_inv_rest.user_shape lentry h_user
              exact h_shape (StringGenState.hasUnderscoreDigitSuffix_of_mem_generated
                                (h_inv_le_step.wf_out) h_lentry_in_gen_le)
          · rcases h_inv_body.fresh lentry h_bb with h_gb | h_user
            · exact h_gb.2 h_lentry_in_gen_le
            · have h_shape := h_inv_body.user_shape lentry h_user
              exact h_shape (StringGenState.hasUnderscoreDigitSuffix_of_mem_generated
                                (h_inv_le_step.wf_out) h_lentry_in_gen_le)
          · rcases h_inv_flush.fresh lentry h_ac with h_gf | h_user
            · -- lentry ∈ gen_le ⊆ gen_n: contradicts h_gf.2 (lentry ∉ gen_n).
              exact h_gf.2 (((h_step_body.trans h_step_inv).trans h_step_nondet).subset
                              h_lentry_in_gen_le)
            · simp at h_user
        have h_inv_with_lentry :
            @GenInv P gen gen_f
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss)
              ((lentry, lentryBlk) :: ((bsNext ++ bbs) ++ accumBlocks)) :=
          GenInv.cons_gen gen gen gen_f _ _ lentry lentryBlk hwf
            (StringGenState.GenStep.refl gen) h_inv_chron h_lentry_in_gen_f
            h_lentry_notin_gen h_lentry_notin_blks
        have h_perm :
            ((lentry, lentryBlk) :: ((bsNext ++ bbs) ++ accumBlocks)).Perm
              (accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ [] ++ bsNext) := by
          have h_target :
              accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ ([] : List (String × DetBlock String (Cmd P) P)) ++ bsNext
              = accumBlocks ++ ((lentry, lentryBlk) :: (bbs ++ bsNext)) := by
            simp [List.append_assoc]
          rw [h_target]
          have h1 : ((lentry, lentryBlk) :: ((bsNext ++ bbs) ++ accumBlocks)).Perm
                    ((lentry, lentryBlk) :: (accumBlocks ++ (bsNext ++ bbs))) :=
            List.Perm.cons _ List.perm_append_comm
          have h2 : ((lentry, lentryBlk) :: (accumBlocks ++ (bsNext ++ bbs))).Perm
                    (accumBlocks ++ (lentry, lentryBlk) :: (bsNext ++ bbs)) :=
            (List.perm_middle (a := (lentry, lentryBlk))
              (l₁ := accumBlocks) (l₂ := bsNext ++ bbs)).symm
          have h3 : (accumBlocks ++ (lentry, lentryBlk) :: (bsNext ++ bbs)).Perm
                    (accumBlocks ++ (lentry, lentryBlk) :: (bbs ++ bsNext)) :=
            List.Perm.append_left accumBlocks
              (List.Perm.cons _ List.perm_append_comm)
          exact (h1.trans h2).trans h3
        have h_inv_perm := GenInv.perm gen gen_f _ _ _ h_inv_with_lentry h_perm
        rw [← h_blocks_eq, ← h_gen_eq, Block.userBlockLabels_loop_cons]
        apply GenInv.weaken_userLabels gen gen_f _ _ _ h_inv_perm
        · intro x hx
          rw [List.mem_append] at hx
          rw [List.mem_append]
          exact hx.elim (fun h_r => Or.inr h_r) (fun h_b => Or.inl h_b)
        · intro x hx; exact h_disj.1 x hx
        · intro x hx h_in
          rw [h_gen_eq] at h_in
          exact h_disj.2.2 x hx h_in
        · exact h_disj.2.1
    | some mExpr =>
      rw [h_m_cases] at h_gen
      simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
      generalize h_ml_def : StringGenState.gen "loop_measure$" gen_le = r_ml at h_gen
      obtain ⟨mLabel, gen_ml⟩ := r_ml
      simp only at h_gen
      generalize h_ldec_def : StringGenState.gen "measure_decrease$" gen_ml = r_ldec at h_gen
      obtain ⟨ldec, gen_ldec⟩ := r_ldec
      simp only at h_gen
      have h_step_ml : StringGenState.GenStep gen_le gen_ml := by
        rw [show gen_ml = (StringGenState.gen "loop_measure$" gen_le).2 from
              (by rw [h_ml_def])]
        exact StringGenState.GenStep.of_gen "loop_measure$" gen_le
      have h_step_ldec : StringGenState.GenStep gen_ml gen_ldec := by
        rw [show gen_ldec = (StringGenState.gen "measure_decrease$" gen_ml).2 from
              (by rw [h_ldec_def])]
        exact StringGenState.GenStep.of_gen "measure_decrease$" gen_ml
      generalize h_body_eq :
        stmtsToBlocks ldec bss ((none, kNext) :: exitConts) [] gen_ldec = r_body at h_gen
      obtain ⟨⟨bl, bbs⟩, gen_b⟩ := r_body
      simp only at h_gen
      generalize h_inv_def :
        ((is.mapM (fun (srcLabel, i) => do
            let assertLabel ←
              if srcLabel.isEmpty then StringGenState.gen "inv$"
              else pure srcLabel
            pure (HasPassiveCmds.assert (P := P) (CmdT := Cmd P) assertLabel i synthesizedMd)))
         : LabelGen.StringGenM (List (Cmd P))) gen_b = r_inv at h_gen
      obtain ⟨invCmds, gen_i⟩ := r_inv
      simp only at h_gen
      have h_step_body := stmtsToBlocks_genStep ldec bss _ [] gen_ldec gen_b bl bbs h_body_eq
      have h_step_inv : StringGenState.GenStep gen_b gen_i :=
        invMapM_genStep is gen_b gen_i invCmds h_inv_def
      cases h_c : c with
      | det e =>
        rw [h_c] at h_gen
        simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
        generalize h_flush_eq : @flushCmds P (Cmd P) _ "before_loop$" accum
          Option.none lentry gen_i = r_flush at h_gen
        obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
        have h_pair := (Prod.mk.inj h_gen).1
        have h_entry_eq : accumEntry = entry := (Prod.mk.inj h_pair).1
        have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
        subst h_entry_eq
        let mIdent := HasIdent.ident (P := P) mLabel
        let mOldExpr := HasFvar.mkFvar (P := P) mIdent
        let initCmd : Cmd P :=
          HasInit.init mIdent HasIntOrder.intTy ExprOrNondet.nondet synthesizedMd
        let assumeCmd : Cmd P :=
          HasPassiveCmds.assume s!"assume_{mLabel}"
            (HasIntOrder.eq mOldExpr mExpr) synthesizedMd
        let lbCmd : Cmd P :=
          HasPassiveCmds.assert s!"measure_lb_{mLabel}"
            (HasNot.not (HasIntOrder.lt mOldExpr HasIntOrder.zero)) synthesizedMd
        let decCmd : Cmd P :=
          HasPassiveCmds.assert s!"measure_decrease_{mLabel}"
            (HasIntOrder.lt mExpr mOldExpr) synthesizedMd
        let measureCmds : List (Cmd P) := [initCmd, assumeCmd, lbCmd]
        let decBlock : String × DetBlock String (Cmd P) P :=
          (ldec, { cmds := [decCmd], transfer := DetTransferCmd.goto lentry synthesizedMd })
        let contractMd : MetaData P :=
          (is.foldl (fun md (_, inv) =>
            md.pushElem MetaData.specLoopInvariant (.expr inv)) md).pushElem
            MetaData.specDecreases (.expr mExpr)
        let lentryBlk : DetBlock String (Cmd P) P :=
          { cmds := invCmds ++ measureCmds,
            transfer := DetTransferCmd.condGoto e bl kNext contractMd }
        have h_blocks_eq :
            accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ [decBlock] ++ bsNext = blocks :=
          (Prod.mk.inj h_pair).2
        have h_step_flush : StringGenState.GenStep gen_i gen_f :=
          flushCmds_genStep "before_loop$" accum _ lentry gen_i gen_f
            accumEntry accumBlocks h_flush_eq
        have h_step_le_to_b : StringGenState.GenStep gen_le gen_b :=
          ((h_step_ml.trans h_step_ldec).trans h_step_body)
        have h_step_chain_r_to_f : StringGenState.GenStep gen_r gen_f :=
          ((((h_step_le.trans h_step_le_to_b).trans h_step_inv)).trans h_step_flush)
        have h_subset_r_gen' : StringGenState.stringGens gen_r ⊆ StringGenState.stringGens gen' := by
          rw [← h_gen_eq]; exact h_step_chain_r_to_f.subset
        have h_subset_b_gen' : StringGenState.stringGens gen_b ⊆ StringGenState.stringGens gen' := by
          rw [← h_gen_eq]; exact (h_step_inv.trans h_step_flush).subset
        have h_disj_rest_gen_r : Block.userLabelsDisjoint rest gen_r :=
          Block.userLabelsDisjoint_mono _ _ _ h_disj_rest_gen' h_subset_r_gen'
        have h_disj_bss_gen_b : Block.userLabelsDisjoint bss gen_b :=
          Block.userLabelsDisjoint_mono _ _ _ h_disj_bss_gen' h_subset_b_gen'
        have h_inv_rest :
            @GenInv P gen gen_r (Block.userBlockLabels rest) bsNext :=
          stmtsToBlocks_invariant k rest exitConts [] gen gen_r kNext bsNext h_rest_eq hwf
            h_disj_rest_gen_r
        have hwf_r := h_inv_rest.wf_out
        have h_inv_le_step : @GenInv P gen_r gen_le [] [] :=
          GenInv.empty_step gen_r gen_le hwf_r h_step_le
        have hwf_le : StringGenState.WF gen_le := h_inv_le_step.wf_out
        -- After cases on m has simplified, the match-result here is
        -- (measureCmds, ldec, [decBlock]) at gen_ldec. Build it directly via cons_gen.
        have hwf_ml : StringGenState.WF gen_ml := h_step_ml.wf_mono hwf_le
        have h_inv_ml_step : @GenInv P gen_le gen_ml [] [] :=
          GenInv.empty_step gen_le gen_ml hwf_le h_step_ml
        have h_inv_ldec_step : @GenInv P gen_ml gen_ldec [] [] :=
          GenInv.empty_step gen_ml gen_ldec hwf_ml h_step_ldec
        have hwf_ldec : StringGenState.WF gen_ldec := h_inv_ldec_step.wf_out
        -- ldec freshly generated from gen_ml.
        have h_ldec_in_gen_ldec : ldec ∈ StringGenState.stringGens gen_ldec := by
          rw [show ldec = (StringGenState.gen "measure_decrease$" gen_ml).1 from
                (by rw [h_ldec_def])]
          rw [show gen_ldec = (StringGenState.gen "measure_decrease$" gen_ml).2 from
                (by rw [h_ldec_def])]
          rw [StringGenState.stringGens_gen]
          exact List.mem_cons.mpr (Or.inl rfl)
        have h_ldec_notin_gen_ml : ldec ∉ StringGenState.stringGens gen_ml := by
          intro h_in
          have h_ldec_eq : ldec = (StringGenState.gen "measure_decrease$" gen_ml).1 := by
            rw [h_ldec_def]
          have h_notin :=
            StringGenState.stringGens_gen_not_in "measure_decrease$" gen_ml hwf_ml
          rw [h_ldec_eq] at h_in
          exact h_notin h_in
        -- IH on body.
        have h_inv_body :
            @GenInv P gen_ldec gen_b (Block.userBlockLabels bss) bbs :=
          stmtsToBlocks_invariant ldec bss _ [] gen_ldec gen_b bl bbs h_body_eq hwf_ldec
            h_disj_bss_gen_b
        have hwf_b := h_inv_body.wf_out
        have h_inv_inv_step : @GenInv P gen_b gen_i [] [] :=
          GenInv.empty_step gen_b gen_i hwf_b h_step_inv
        have hwf_i : StringGenState.WF gen_i := h_inv_inv_step.wf_out
        have h_inv_flush : @GenInv P gen_i gen_f [] accumBlocks :=
          flushCmds_invariant "before_loop$" accum _ lentry gen_i gen_f
            accumEntry accumBlocks h_flush_eq hwf_i
        -- Compose chain.
        have h_inv_r_le :
            @GenInv P gen gen_le (Block.userBlockLabels rest ++ []) (bsNext ++ []) :=
          GenInv.trans gen gen_r gen_le _ _ _ _ h_inv_rest h_inv_le_step
            (by intros _ _ h_in; simp at h_in)
        have h_user_r_simp :
            Block.userBlockLabels rest ++ ([] : List String) = Block.userBlockLabels rest := by simp
        have h_blks_r_simp : bsNext ++ ([] : List (String × DetBlock String (Cmd P) P)) = bsNext := by simp
        rw [h_user_r_simp, h_blks_r_simp] at h_inv_r_le
        have h_inv_r_ml :
            @GenInv P gen gen_ml (Block.userBlockLabels rest ++ []) (bsNext ++ []) :=
          GenInv.trans gen gen_le gen_ml _ _ _ _ h_inv_r_le h_inv_ml_step
            (by intros _ _ h_in; simp at h_in)
        rw [h_user_r_simp, h_blks_r_simp] at h_inv_r_ml
        -- Build GenInv at gen_ldec including the decrease block.
        -- decrease block lives in gen_ldec only (ldec freshly generated).
        have h_inv_ldec_only : @GenInv P gen_ml gen_ldec [] [decBlock] := by
          apply GenInv.cons_gen gen_ml gen_ml gen_ldec [] [] ldec _
            hwf_ml (StringGenState.GenStep.refl gen_ml) h_inv_ldec_step
            h_ldec_in_gen_ldec h_ldec_notin_gen_ml
          simp
        have h_inv_r_ldec :
            @GenInv P gen gen_ldec
              (Block.userBlockLabels rest ++ [])
              (bsNext ++ [decBlock]) :=
          GenInv.trans gen gen_ml gen_ldec _ _ _ _ h_inv_r_ml h_inv_ldec_only
            (by intros _ _ h_in; simp at h_in)
        rw [h_user_r_simp] at h_inv_r_ldec
        -- gen_ldec → gen_b via IH on body.
        have h_inv_r_b :
            @GenInv P gen gen_b
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss)
              ((bsNext ++ [decBlock]) ++ bbs) := by
          apply GenInv.trans gen gen_ldec gen_b _ _ _ _ h_inv_r_ldec h_inv_body
          intro x h_x_r h_x_b; exact h_user_disj_bss_rest x h_x_b h_x_r
        have h_inv_r_i :
            @GenInv P gen gen_i
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss ++ [])
              (((bsNext ++ [decBlock]) ++ bbs) ++ []) :=
          GenInv.trans gen gen_b gen_i _ _ _ _ h_inv_r_b h_inv_inv_step
            (by intros _ _ h_in; simp at h_in)
        have h_user_simp_i :
            Block.userBlockLabels rest ++ Block.userBlockLabels bss ++ ([] : List String)
            = Block.userBlockLabels rest ++ Block.userBlockLabels bss := by simp
        rw [h_user_simp_i] at h_inv_r_i
        have h_blks_simp :
            ((bsNext ++ [decBlock]) ++ bbs) ++ ([] : List (String × DetBlock String (Cmd P) P))
            = bsNext ++ [decBlock] ++ bbs := by simp
        rw [h_blks_simp] at h_inv_r_i
        have h_inv_chron :
            @GenInv P gen gen_f
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss ++ [])
              ((bsNext ++ [decBlock] ++ bbs) ++ accumBlocks) :=
          GenInv.trans gen gen_i gen_f _ _ _ _ h_inv_r_i h_inv_flush
            (by intros _ _ h_in; simp at h_in)
        rw [h_user_simp_i] at h_inv_chron
        -- Now prepend (lentry, lentryBlk) via cons_gen.
        have h_lentry_in_gen_le : lentry ∈ StringGenState.stringGens gen_le := by
          rw [show lentry = (StringGenState.gen "loop_entry$" gen_r).1 from
                (by rw [h_lentry_def])]
          rw [show gen_le = (StringGenState.gen "loop_entry$" gen_r).2 from
                (by rw [h_lentry_def])]
          rw [StringGenState.stringGens_gen]
          exact List.mem_cons.mpr (Or.inl rfl)
        have h_lentry_in_gen_f : lentry ∈ StringGenState.stringGens gen_f :=
          ((h_step_le_to_b.trans h_step_inv).trans h_step_flush).subset h_lentry_in_gen_le
        have h_lentry_notin_gen_r : lentry ∉ StringGenState.stringGens gen_r := by
          intro h_in
          have h_lentry_eq : lentry = (StringGenState.gen "loop_entry$" gen_r).1 := by
            rw [h_lentry_def]
          have h_notin :=
            StringGenState.stringGens_gen_not_in "loop_entry$" gen_r hwf_r
          rw [h_lentry_eq] at h_in
          exact h_notin h_in
        have h_lentry_notin_gen : lentry ∉ StringGenState.stringGens gen := by
          intro h_in; exact h_lentry_notin_gen_r (h_step_rest.subset h_in)
        have h_lentry_notin_blks :
            lentry ∉ List.map Prod.fst ((bsNext ++ [decBlock] ++ bbs) ++ accumBlocks) := by
          intro h_in
          rw [List.map_append, List.map_append, List.map_append, List.mem_append, List.mem_append,
              List.mem_append] at h_in
          rcases h_in with ((h_bs | h_dec) | h_bb) | h_ac
          · rcases h_inv_rest.fresh lentry h_bs with h_gr | h_user
            · exact h_lentry_notin_gen_r h_gr.1
            · have h_shape := h_inv_rest.user_shape lentry h_user
              exact h_shape (StringGenState.hasUnderscoreDigitSuffix_of_mem_generated
                                (h_inv_le_step.wf_out) h_lentry_in_gen_le)
          · -- decBlock: lentry = ldec? ldec was generated from gen_ml, lentry from gen_r
            -- We need: lentry ≠ ldec.
            simp only [List.map_cons, List.map_nil, List.mem_singleton] at h_dec
            -- h_dec : lentry = ldec.fst = ldec; this means lentry = ldec (= decBlock.1)
            -- ldec ∈ gen_ldec, lentry ∈ gen_le ⊆ gen_ml. ldec ∉ gen_ml.
            -- So if lentry = ldec then ldec ∈ gen_ml — contradicting h_ldec_notin_gen_ml.
            rw [h_dec] at h_lentry_in_gen_le
            -- h_lentry_in_gen_le : ldec ∈ gen_le
            exact h_ldec_notin_gen_ml (h_step_ml.subset h_lentry_in_gen_le)
          · rcases h_inv_body.fresh lentry h_bb with h_gb | h_user
            · -- lentry ∈ gen_le ⊆ gen_ldec, but h_gb.2 says lentry ∉ gen_ldec.
              exact h_gb.2 ((h_step_ml.trans h_step_ldec).subset h_lentry_in_gen_le)
            · have h_shape := h_inv_body.user_shape lentry h_user
              exact h_shape (StringGenState.hasUnderscoreDigitSuffix_of_mem_generated
                                (h_inv_le_step.wf_out) h_lentry_in_gen_le)
          · rcases h_inv_flush.fresh lentry h_ac with h_gf | h_user
            · exact h_gf.2 ((h_step_le_to_b.trans h_step_inv).subset h_lentry_in_gen_le)
            · simp at h_user
        have h_inv_with_lentry :
            @GenInv P gen gen_f
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss)
              ((lentry, lentryBlk) :: ((bsNext ++ [decBlock] ++ bbs) ++ accumBlocks)) :=
          GenInv.cons_gen gen gen gen_f _ _ lentry lentryBlk hwf
            (StringGenState.GenStep.refl gen) h_inv_chron h_lentry_in_gen_f
            h_lentry_notin_gen h_lentry_notin_blks
        -- Permute to align with output ordering.
        -- accumBlocks ++ [(lentry, _)] ++ bbs ++ [decBlock] ++ bsNext
        have h_perm :
            ((lentry, lentryBlk) :: ((bsNext ++ [decBlock] ++ bbs) ++ accumBlocks)).Perm
              (accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ [decBlock] ++ bsNext) := by
          have h_target :
              accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ [decBlock] ++ bsNext
              = accumBlocks ++ ((lentry, lentryBlk) :: (bbs ++ [decBlock] ++ bsNext)) := by
            simp [List.append_assoc]
          rw [h_target]
          have h1 : ((lentry, lentryBlk) :: ((bsNext ++ [decBlock] ++ bbs) ++ accumBlocks)).Perm
                    ((lentry, lentryBlk) :: (accumBlocks ++ (bsNext ++ [decBlock] ++ bbs))) :=
            List.Perm.cons _ List.perm_append_comm
          have h2 : ((lentry, lentryBlk) :: (accumBlocks ++ (bsNext ++ [decBlock] ++ bbs))).Perm
                    (accumBlocks ++ (lentry, lentryBlk) :: (bsNext ++ [decBlock] ++ bbs)) :=
            (List.perm_middle (a := (lentry, lentryBlk))
              (l₁ := accumBlocks) (l₂ := bsNext ++ [decBlock] ++ bbs)).symm
          have h3 : (accumBlocks ++ (lentry, lentryBlk) :: (bsNext ++ [decBlock] ++ bbs)).Perm
                    (accumBlocks ++ (lentry, lentryBlk) :: (bbs ++ [decBlock] ++ bsNext)) :=
            List.Perm.append_left accumBlocks
              (List.Perm.cons _ (by
                -- bsNext ++ [decBlock] ++ bbs ~ bbs ++ [decBlock] ++ bsNext
                have hh1 : (bsNext ++ [decBlock] ++ bbs).Perm
                            (bbs ++ (bsNext ++ [decBlock])) :=
                  List.perm_append_comm
                have hh2 : (bbs ++ (bsNext ++ [decBlock])).Perm
                            (bbs ++ ([decBlock] ++ bsNext)) :=
                  List.Perm.append_left bbs List.perm_append_comm
                have hh3 : (bbs ++ ([decBlock] ++ bsNext)) = (bbs ++ [decBlock] ++ bsNext) := by
                  rw [List.append_assoc]
                exact (hh1.trans hh2).trans (hh3 ▸ List.Perm.refl _)))
          exact (h1.trans h2).trans h3
        have h_inv_perm := GenInv.perm gen gen_f _ _ _ h_inv_with_lentry h_perm
        rw [← h_blocks_eq, ← h_gen_eq, Block.userBlockLabels_loop_cons]
        apply GenInv.weaken_userLabels gen gen_f _ _ _ h_inv_perm
        · intro x hx
          rw [List.mem_append] at hx
          rw [List.mem_append]
          exact hx.elim (fun h_r => Or.inr h_r) (fun h_b => Or.inl h_b)
        · intro x hx; exact h_disj.1 x hx
        · intro x hx h_in
          rw [h_gen_eq] at h_in
          exact h_disj.2.2 x hx h_in
        · exact h_disj.2.1
      | nondet =>
        rw [h_c] at h_gen
        simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
        generalize h_nondet_gen : StringGenState.gen "$__nondet_loop$" gen_i = r_nd at h_gen
        obtain ⟨freshName, gen_n⟩ := r_nd
        simp only at h_gen
        generalize h_flush_eq : @flushCmds P (Cmd P) _ "before_loop$" accum
          Option.none lentry gen_n = r_flush at h_gen
        obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
        have h_pair := (Prod.mk.inj h_gen).1
        have h_entry_eq : accumEntry = entry := (Prod.mk.inj h_pair).1
        have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_gen).2
        subst h_entry_eq
        let mIdent := HasIdent.ident (P := P) mLabel
        let mOldExpr := HasFvar.mkFvar (P := P) mIdent
        let initCmd : Cmd P :=
          HasInit.init mIdent HasIntOrder.intTy ExprOrNondet.nondet synthesizedMd
        let assumeCmd : Cmd P :=
          HasPassiveCmds.assume s!"assume_{mLabel}"
            (HasIntOrder.eq mOldExpr mExpr) synthesizedMd
        let lbCmd : Cmd P :=
          HasPassiveCmds.assert s!"measure_lb_{mLabel}"
            (HasNot.not (HasIntOrder.lt mOldExpr HasIntOrder.zero)) synthesizedMd
        let decCmd : Cmd P :=
          HasPassiveCmds.assert s!"measure_decrease_{mLabel}"
            (HasIntOrder.lt mExpr mOldExpr) synthesizedMd
        let measureCmds : List (Cmd P) := [initCmd, assumeCmd, lbCmd]
        let decBlock : String × DetBlock String (Cmd P) P :=
          (ldec, { cmds := [decCmd], transfer := DetTransferCmd.goto lentry synthesizedMd })
        let contractMd : MetaData P :=
          (is.foldl (fun md (_, inv) =>
            md.pushElem MetaData.specLoopInvariant (.expr inv)) md).pushElem
            MetaData.specDecreases (.expr mExpr)
        let lentryBlk : DetBlock String (Cmd P) P :=
          { cmds := [HasInit.init (HasIdent.ident (P := P) freshName)
                       HasBool.boolTy ExprOrNondet.nondet synthesizedMd] ++ invCmds ++ measureCmds,
            transfer := DetTransferCmd.condGoto
                          (HasFvar.mkFvar (HasIdent.ident (P := P) freshName)) bl kNext contractMd }
        have h_blocks_eq :
            accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ [decBlock] ++ bsNext = blocks :=
          (Prod.mk.inj h_pair).2
        have h_step_nondet : StringGenState.GenStep gen_i gen_n := by
          rw [show gen_n = (StringGenState.gen "$__nondet_loop$" gen_i).2 from
                (by rw [h_nondet_gen])]
          exact StringGenState.GenStep.of_gen "$__nondet_loop$" gen_i
        have h_step_flush : StringGenState.GenStep gen_n gen_f :=
          flushCmds_genStep "before_loop$" accum _ lentry gen_n gen_f
            accumEntry accumBlocks h_flush_eq
        have h_step_le_to_b : StringGenState.GenStep gen_le gen_b :=
          ((h_step_ml.trans h_step_ldec).trans h_step_body)
        have h_step_chain_r_to_f : StringGenState.GenStep gen_r gen_f :=
          (((((h_step_le.trans h_step_le_to_b).trans h_step_inv)).trans h_step_nondet).trans
            h_step_flush)
        have h_subset_r_gen' : StringGenState.stringGens gen_r ⊆ StringGenState.stringGens gen' := by
          rw [← h_gen_eq]; exact h_step_chain_r_to_f.subset
        have h_subset_b_gen' : StringGenState.stringGens gen_b ⊆ StringGenState.stringGens gen' := by
          exact h_gen_eq ▸ ((h_step_inv.trans h_step_nondet).trans h_step_flush).subset
        have h_disj_rest_gen_r : Block.userLabelsDisjoint rest gen_r :=
          Block.userLabelsDisjoint_mono _ _ _ h_disj_rest_gen' h_subset_r_gen'
        have h_disj_bss_gen_b : Block.userLabelsDisjoint bss gen_b :=
          Block.userLabelsDisjoint_mono _ _ _ h_disj_bss_gen' h_subset_b_gen'
        have h_inv_rest :
            @GenInv P gen gen_r (Block.userBlockLabels rest) bsNext :=
          stmtsToBlocks_invariant k rest exitConts [] gen gen_r kNext bsNext h_rest_eq hwf
            h_disj_rest_gen_r
        have hwf_r := h_inv_rest.wf_out
        have h_inv_le_step : @GenInv P gen_r gen_le [] [] :=
          GenInv.empty_step gen_r gen_le hwf_r h_step_le
        have hwf_le : StringGenState.WF gen_le := h_inv_le_step.wf_out
        have hwf_ml : StringGenState.WF gen_ml := h_step_ml.wf_mono hwf_le
        have h_inv_ml_step : @GenInv P gen_le gen_ml [] [] :=
          GenInv.empty_step gen_le gen_ml hwf_le h_step_ml
        have h_inv_ldec_step : @GenInv P gen_ml gen_ldec [] [] :=
          GenInv.empty_step gen_ml gen_ldec hwf_ml h_step_ldec
        have hwf_ldec : StringGenState.WF gen_ldec := h_inv_ldec_step.wf_out
        have h_ldec_in_gen_ldec : ldec ∈ StringGenState.stringGens gen_ldec := by
          rw [show ldec = (StringGenState.gen "measure_decrease$" gen_ml).1 from
                (by rw [h_ldec_def])]
          rw [show gen_ldec = (StringGenState.gen "measure_decrease$" gen_ml).2 from
                (by rw [h_ldec_def])]
          rw [StringGenState.stringGens_gen]
          exact List.mem_cons.mpr (Or.inl rfl)
        have h_ldec_notin_gen_ml : ldec ∉ StringGenState.stringGens gen_ml := by
          intro h_in
          have h_ldec_eq : ldec = (StringGenState.gen "measure_decrease$" gen_ml).1 := by
            rw [h_ldec_def]
          have h_notin :=
            StringGenState.stringGens_gen_not_in "measure_decrease$" gen_ml hwf_ml
          rw [h_ldec_eq] at h_in
          exact h_notin h_in
        have h_inv_body :
            @GenInv P gen_ldec gen_b (Block.userBlockLabels bss) bbs :=
          stmtsToBlocks_invariant ldec bss _ [] gen_ldec gen_b bl bbs h_body_eq hwf_ldec
            h_disj_bss_gen_b
        have hwf_b := h_inv_body.wf_out
        have h_inv_inv_step : @GenInv P gen_b gen_i [] [] :=
          GenInv.empty_step gen_b gen_i hwf_b h_step_inv
        have hwf_i : StringGenState.WF gen_i := h_inv_inv_step.wf_out
        have h_inv_nondet_step : @GenInv P gen_i gen_n [] [] :=
          GenInv.empty_step gen_i gen_n hwf_i h_step_nondet
        have hwf_n : StringGenState.WF gen_n := h_inv_nondet_step.wf_out
        have h_inv_flush : @GenInv P gen_n gen_f [] accumBlocks :=
          flushCmds_invariant "before_loop$" accum _ lentry gen_n gen_f
            accumEntry accumBlocks h_flush_eq hwf_n
        -- Compose chain: gen → gen_r → gen_le → gen_ml → gen_ldec → gen_b → gen_i → gen_n → gen_f
        have h_inv_r_le :
            @GenInv P gen gen_le (Block.userBlockLabels rest ++ []) (bsNext ++ []) :=
          GenInv.trans gen gen_r gen_le _ _ _ _ h_inv_rest h_inv_le_step
            (by intros _ _ h_in; simp at h_in)
        have h_user_r_simp :
            Block.userBlockLabels rest ++ ([] : List String) = Block.userBlockLabels rest := by simp
        have h_blks_r_simp : bsNext ++ ([] : List (String × DetBlock String (Cmd P) P)) = bsNext := by simp
        rw [h_user_r_simp, h_blks_r_simp] at h_inv_r_le
        have h_inv_r_ml :
            @GenInv P gen gen_ml (Block.userBlockLabels rest ++ []) (bsNext ++ []) :=
          GenInv.trans gen gen_le gen_ml _ _ _ _ h_inv_r_le h_inv_ml_step
            (by intros _ _ h_in; simp at h_in)
        rw [h_user_r_simp, h_blks_r_simp] at h_inv_r_ml
        have h_inv_ldec_only : @GenInv P gen_ml gen_ldec [] [decBlock] := by
          apply GenInv.cons_gen gen_ml gen_ml gen_ldec [] [] ldec _
            hwf_ml (StringGenState.GenStep.refl gen_ml) h_inv_ldec_step
            h_ldec_in_gen_ldec h_ldec_notin_gen_ml
          simp
        have h_inv_r_ldec :
            @GenInv P gen gen_ldec
              (Block.userBlockLabels rest ++ [])
              (bsNext ++ [decBlock]) :=
          GenInv.trans gen gen_ml gen_ldec _ _ _ _ h_inv_r_ml h_inv_ldec_only
            (by intros _ _ h_in; simp at h_in)
        rw [h_user_r_simp] at h_inv_r_ldec
        have h_inv_r_b :
            @GenInv P gen gen_b
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss)
              ((bsNext ++ [decBlock]) ++ bbs) := by
          apply GenInv.trans gen gen_ldec gen_b _ _ _ _ h_inv_r_ldec h_inv_body
          intro x h_x_r h_x_b; exact h_user_disj_bss_rest x h_x_b h_x_r
        have h_inv_r_i :
            @GenInv P gen gen_i
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss ++ [])
              (((bsNext ++ [decBlock]) ++ bbs) ++ []) :=
          GenInv.trans gen gen_b gen_i _ _ _ _ h_inv_r_b h_inv_inv_step
            (by intros _ _ h_in; simp at h_in)
        have h_user_simp_i :
            Block.userBlockLabels rest ++ Block.userBlockLabels bss ++ ([] : List String)
            = Block.userBlockLabels rest ++ Block.userBlockLabels bss := by simp
        rw [h_user_simp_i] at h_inv_r_i
        have h_blks_simp :
            ((bsNext ++ [decBlock]) ++ bbs) ++ ([] : List (String × DetBlock String (Cmd P) P))
            = bsNext ++ [decBlock] ++ bbs := by simp
        rw [h_blks_simp] at h_inv_r_i
        have h_inv_r_n :
            @GenInv P gen gen_n
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss ++ [])
              ((bsNext ++ [decBlock] ++ bbs) ++ []) :=
          GenInv.trans gen gen_i gen_n _ _ _ _ h_inv_r_i h_inv_nondet_step
            (by intros _ _ h_in; simp at h_in)
        rw [h_user_simp_i] at h_inv_r_n
        have h_blks_simp_n :
            bsNext ++ [decBlock] ++ bbs ++ ([] : List (String × DetBlock String (Cmd P) P))
            = bsNext ++ [decBlock] ++ bbs := by simp
        rw [h_blks_simp_n] at h_inv_r_n
        have h_inv_chron :
            @GenInv P gen gen_f
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss ++ [])
              ((bsNext ++ [decBlock] ++ bbs) ++ accumBlocks) :=
          GenInv.trans gen gen_n gen_f _ _ _ _ h_inv_r_n h_inv_flush
            (by intros _ _ h_in; simp at h_in)
        rw [h_user_simp_i] at h_inv_chron
        -- Prepend lentry block.
        have h_lentry_in_gen_le : lentry ∈ StringGenState.stringGens gen_le := by
          rw [show lentry = (StringGenState.gen "loop_entry$" gen_r).1 from
                (by rw [h_lentry_def])]
          rw [show gen_le = (StringGenState.gen "loop_entry$" gen_r).2 from
                (by rw [h_lentry_def])]
          rw [StringGenState.stringGens_gen]
          exact List.mem_cons.mpr (Or.inl rfl)
        have h_lentry_in_gen_f : lentry ∈ StringGenState.stringGens gen_f :=
          (((h_step_le_to_b.trans h_step_inv).trans h_step_nondet).trans h_step_flush).subset
            h_lentry_in_gen_le
        have h_lentry_notin_gen_r : lentry ∉ StringGenState.stringGens gen_r := by
          intro h_in
          have h_lentry_eq : lentry = (StringGenState.gen "loop_entry$" gen_r).1 := by
            rw [h_lentry_def]
          have h_notin :=
            StringGenState.stringGens_gen_not_in "loop_entry$" gen_r hwf_r
          rw [h_lentry_eq] at h_in
          exact h_notin h_in
        have h_lentry_notin_gen : lentry ∉ StringGenState.stringGens gen := by
          intro h_in; exact h_lentry_notin_gen_r (h_step_rest.subset h_in)
        have h_lentry_notin_blks :
            lentry ∉ List.map Prod.fst ((bsNext ++ [decBlock] ++ bbs) ++ accumBlocks) := by
          intro h_in
          rw [List.map_append, List.map_append, List.map_append, List.mem_append, List.mem_append,
              List.mem_append] at h_in
          rcases h_in with ((h_bs | h_dec) | h_bb) | h_ac
          · rcases h_inv_rest.fresh lentry h_bs with h_gr | h_user
            · exact h_lentry_notin_gen_r h_gr.1
            · have h_shape := h_inv_rest.user_shape lentry h_user
              exact h_shape (StringGenState.hasUnderscoreDigitSuffix_of_mem_generated
                                (h_inv_le_step.wf_out) h_lentry_in_gen_le)
          · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h_dec
            rw [h_dec] at h_lentry_in_gen_le
            exact h_ldec_notin_gen_ml (h_step_ml.subset h_lentry_in_gen_le)
          · rcases h_inv_body.fresh lentry h_bb with h_gb | h_user
            · exact h_gb.2 ((h_step_ml.trans h_step_ldec).subset h_lentry_in_gen_le)
            · have h_shape := h_inv_body.user_shape lentry h_user
              exact h_shape (StringGenState.hasUnderscoreDigitSuffix_of_mem_generated
                                (h_inv_le_step.wf_out) h_lentry_in_gen_le)
          · rcases h_inv_flush.fresh lentry h_ac with h_gf | h_user
            · exact h_gf.2 (((h_step_le_to_b.trans h_step_inv).trans h_step_nondet).subset
                              h_lentry_in_gen_le)
            · simp at h_user
        have h_inv_with_lentry :
            @GenInv P gen gen_f
              (Block.userBlockLabels rest ++ Block.userBlockLabels bss)
              ((lentry, lentryBlk) :: ((bsNext ++ [decBlock] ++ bbs) ++ accumBlocks)) :=
          GenInv.cons_gen gen gen gen_f _ _ lentry lentryBlk hwf
            (StringGenState.GenStep.refl gen) h_inv_chron h_lentry_in_gen_f
            h_lentry_notin_gen h_lentry_notin_blks
        have h_perm :
            ((lentry, lentryBlk) :: ((bsNext ++ [decBlock] ++ bbs) ++ accumBlocks)).Perm
              (accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ [decBlock] ++ bsNext) := by
          have h_target :
              accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ [decBlock] ++ bsNext
              = accumBlocks ++ ((lentry, lentryBlk) :: (bbs ++ [decBlock] ++ bsNext)) := by
            simp [List.append_assoc]
          rw [h_target]
          have h1 : ((lentry, lentryBlk) :: ((bsNext ++ [decBlock] ++ bbs) ++ accumBlocks)).Perm
                    ((lentry, lentryBlk) :: (accumBlocks ++ (bsNext ++ [decBlock] ++ bbs))) :=
            List.Perm.cons _ List.perm_append_comm
          have h2 : ((lentry, lentryBlk) :: (accumBlocks ++ (bsNext ++ [decBlock] ++ bbs))).Perm
                    (accumBlocks ++ (lentry, lentryBlk) :: (bsNext ++ [decBlock] ++ bbs)) :=
            (List.perm_middle (a := (lentry, lentryBlk))
              (l₁ := accumBlocks) (l₂ := bsNext ++ [decBlock] ++ bbs)).symm
          have h3 : (accumBlocks ++ (lentry, lentryBlk) :: (bsNext ++ [decBlock] ++ bbs)).Perm
                    (accumBlocks ++ (lentry, lentryBlk) :: (bbs ++ [decBlock] ++ bsNext)) :=
            List.Perm.append_left accumBlocks
              (List.Perm.cons _ (by
                have hh1 : (bsNext ++ [decBlock] ++ bbs).Perm
                            (bbs ++ (bsNext ++ [decBlock])) :=
                  List.perm_append_comm
                have hh2 : (bbs ++ (bsNext ++ [decBlock])).Perm
                            (bbs ++ ([decBlock] ++ bsNext)) :=
                  List.Perm.append_left bbs List.perm_append_comm
                have hh3 : (bbs ++ ([decBlock] ++ bsNext)) = (bbs ++ [decBlock] ++ bsNext) := by
                  rw [List.append_assoc]
                exact (hh1.trans hh2).trans (hh3 ▸ List.Perm.refl _)))
          exact (h1.trans h2).trans h3
        have h_inv_perm := GenInv.perm gen gen_f _ _ _ h_inv_with_lentry h_perm
        rw [← h_blocks_eq, ← h_gen_eq, Block.userBlockLabels_loop_cons]
        apply GenInv.weaken_userLabels gen gen_f _ _ _ h_inv_perm
        · intro x hx
          rw [List.mem_append] at hx
          rw [List.mem_append]
          exact hx.elim (fun h_r => Or.inr h_r) (fun h_b => Or.inl h_b)
        · intro x hx; exact h_disj.1 x hx
        · intro x hx h_in
          rw [h_gen_eq] at h_in
          exact h_disj.2.2 x hx h_in
        · exact h_disj.2.1
termination_by sizeOf ss
decreasing_by all_goals (subst h_match; simp_wf; omega)

/-- The CFG produced by `stmtsToCFG` has unique labels.
This holds because all labels are generated fresh by `StringGenState`,
which is monotone (each generated label is fresh w.r.t. previously generated ones).

Reduces to `stmtsToBlocks_invariant`: the final block label `lend` is generated
*before* the `stmtsToBlocks` call, so it is in `gen0.gens`. The invariant says
the inner blocks' labels are NOT in `gen0.gens`, so `lend` is disjoint from them. -/
private theorem stmtsToCFG_nodup_keys {P : PureExpr}
    [HasBool P] [HasIdent P] [HasFvar P] [HasIntOrder P] [HasNot P]
    (ss : List (Stmt P (Cmd P)))
    (h_disj : ∀ gen', StringGenState.WF gen' → Block.userLabelsDisjoint ss gen') :
    ((stmtsToCFG ss).blocks.map Prod.fst).Nodup := by
  -- Define the generator state after generating "end$" and the resulting label.
  let p_end := StringGenState.gen "end$" StringGenState.emp
  let lend : String := p_end.1
  let gen0 : StringGenState := p_end.2
  let r := stmtsToBlocks (P := P) (CmdT := Cmd P) lend ss
    ([] : List (Option String × String)) ([] : List (Cmd P)) gen0
  -- The blocks of stmtsToCFG ss are r.1.2 ++ [(lend, ...)]
  have h_unfold : ((stmtsToCFG ss).blocks.map Prod.fst) =
      (r.1.2.map Prod.fst) ++ [lend] := by
    show List.map Prod.fst ((stmtsToCFG ss).blocks) = _
    unfold stmtsToCFG stmtsToCFGM
    simp only [bind, StateT.bind, pure, StateT.pure, Id]
    show List.map Prod.fst (_ ++ [(lend, _)]) = _
    rw [List.map_append]
    rfl
  rw [h_unfold]
  -- WF of empty state
  have hwf_emp : StringGenState.WF StringGenState.emp := StringGenState.wf_emp
  -- WF of gen0
  have hwf0 : StringGenState.WF gen0 :=
    StringGenState.WFMono hwf_emp rfl
  -- lend ∈ StringGenState.stringGens gen0
  have h_lend_in_gen0 : lend ∈ StringGenState.stringGens gen0 := by
    show lend ∈ StringGenState.stringGens p_end.2
    rw [StringGenState.stringGens_gen]; exact List.mem_cons.mpr (Or.inl rfl)
  -- Get invariant from the helper
  have h_eq : stmtsToBlocks lend ss [] [] gen0 = ((r.1.1, r.1.2), r.2) := rfl
  have hwf_r2 : StringGenState.WF r.2 :=
    (stmtsToBlocks_genStep lend ss [] [] gen0 r.2 r.1.1 r.1.2 h_eq).wf_mono hwf0
  have h_inv : @GenInv P gen0 r.2 (Block.userBlockLabels ss) r.1.2 :=
    stmtsToBlocks_invariant lend ss [] [] gen0 r.2 _ _ h_eq hwf0 (h_disj _ hwf_r2)
  -- Build Nodup of r.1.2.map Prod.fst ++ [lend]
  rw [List.nodup_append]
  refine ⟨h_inv.nodup, ?_, ?_⟩
  · simp
  · -- disjointness: lend not in r.1.2.map Prod.fst
    intro x hx y hy h_eq
    rw [List.mem_singleton] at hy
    subst hy
    subst h_eq
    rcases h_inv.fresh _ hx with h_gen | h_user
    · -- lend ∈ stringGens r.2 \ stringGens gen0; but lend ∈ stringGens gen0. Contradiction.
      exact h_gen.2 h_lend_in_gen0
    · -- lend is a user label of ss; but lend = (gen "end$" emp).1 has shape, so it's not user.
      -- We instead use that user labels are disjoint from stringGens (h_inv.user_disj)
      have h_lend_in_r2 : lend ∈ StringGenState.stringGens r.2 := by
        have h_step := h_inv.toGenStep
        exact h_step.subset h_lend_in_gen0
      exact h_inv.user_disj _ h_user h_lend_in_r2



/-- Evaluator well-formedness (Bool) is preserved by structured execution when
no `funcDecl` statements are executed (i.e., the evaluator doesn't change).
This holds because only `step_funcDecl` modifies `eval`. -/
private theorem StepStmtStar_wfb_preserved {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P] [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) (.terminal ρ'))
    (hnofd : Block.noFuncDecl ss = true)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval) :
    WellFormedSemanticEvalBool ρ'.eval := by
  have h_eval_eq : ρ'.eval = ρ₀.eval :=
    smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval ss ρ₀ ρ' hnofd h
  rw [h_eval_eq]
  exact hwfb

/-- Same as above but for `WellFormedSemanticEvalVal`. -/
private theorem StepStmtStar_wfv_preserved {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P] [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P)
    (h : StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) (.terminal ρ'))
    (hnofd : Block.noFuncDecl ss = true)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval) :
    WellFormedSemanticEvalVal ρ'.eval := by
  have h_eval_eq : ρ'.eval = ρ₀.eval :=
    smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval ss ρ₀ ρ' hnofd h
  rw [h_eval_eq]
  exact hwfv

/-! ## Agreement-based condGoto flushing

This lemma takes the CFG-side accumulated trace pre-lifted via
`EvalCmds_under_agreement`, allowing the agreement gap (between structured and
CFG entry stores) to be threaded through the simulation. -/

/-- Runs the flushed `condGoto` block under StoreAgreement: the input accum
trace is on the CFG side (lifted via `EvalCmds_under_agreement`) and reaches
`σ_cfg_after`, which agrees with `ρ₀.store`. The boolean `b` selects the taken
branch (`tl` when `tt`, `fl` when `ff`). -/
private theorem flushCmds_condGoto_agree {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P)
    (b : Bool)
    (accum : List (Cmd P))
    (e : P.Expr) (tl fl : String) (md : MetaData P)
    (l_ite : String) (gen_e gen_f : StringGenState)
    (accumEntry : String) (accumBlocks : DetBlocks String (Cmd P) P)
    (h_flush_eq : flushCmds "ite$" accum
      (some (DetTransferCmd.condGoto e tl fl md)) l_ite gen_e = ((accumEntry, accumBlocks), gen_f))
    (σ_base σ_cfg_after : SemanticStore P) (hf_base hf_accum : Bool)
    (ρ₀ : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (h_wf_def : WellFormedSemanticEvalDef ρ₀.eval)
    (h_congr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (h_accum_cfg : EvalCmds P (EvalCmd P) ρ₀.eval σ_base accum.reverse σ_cfg_after hf_accum)
    (h_agree_after : StoreAgreement ρ₀.store σ_cfg_after)
    (h_hf : ρ₀.hasFailure = (hf_base || hf_accum))
    (h_cond : ρ₀.eval ρ₀.store e = .some (if b then HasBool.tt else HasBool.ff))
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (h_cfg_accum : ∀ b ∈ accumBlocks, b ∈ cfg.blocks)
    (h_lookup : ∀ lbl blk, (lbl, blk) ∈ cfg.blocks →
      cfg.blocks.lookup lbl = some blk) :
    StepDetCFGStar extendEval cfg
      (.atBlock accumEntry σ_base hf_base)
      (.atBlock (if b then tl else fl) σ_cfg_after ρ₀.hasFailure) := by
  simp only [flushCmds, bind, StateT.bind, pure, StateT.pure, Id] at h_flush_eq
  injection h_flush_eq with h_pair h_gen_eq
  injection h_pair with h_entry_eq h_blks_eq
  subst h_entry_eq; subst h_blks_eq
  have h_def_e : isDefined ρ₀.store (HasVarsPure.getVars e) :=
    h_wf_def e _ ρ₀.store h_cond
  have h_pointwise :
      ∀ y ∈ HasVarsPure.getVars e, ρ₀.store y = σ_cfg_after y :=
    store_agreement_pointwise_on_expr_vars ρ₀.store σ_cfg_after e h_agree_after h_def_e
  have h_cond_cfg : ρ₀.eval σ_cfg_after e = .some (if b then HasBool.tt else HasBool.ff) :=
    h_cond ▸ (h_congr e ρ₀.store σ_cfg_after h_pointwise).symm
  have h_mem := h_cfg_accum _ (List.Mem.head _)
  have h_lkp := h_lookup _ _ h_mem
  rw [h_hf]
  cases b with
  | true => exact run_block_goto_true (extendEval := extendEval) (cfg := cfg)
              (f_base := hf_base) h_lkp h_accum_cfg h_cond_cfg hwfb h_congr
  | false => exact run_block_goto_false (extendEval := extendEval) (cfg := cfg)
              (f_base := hf_base) h_lkp h_accum_cfg h_cond_cfg hwfb h_congr
/-! ## Block.uniqueInits projection helpers

`Block.uniqueInits ss` is a Nodup property of the cumulative `Block.initVars ss`
list. These mechanical helpers project Nodup down to sub-lists that recursive
simulation calls produce. -/

private theorem Block.uniqueInits.tail {P : PureExpr}
    {s : Stmt P (Cmd P)} {ss : List (Stmt P (Cmd P))}
    (h : Block.uniqueInits (s :: ss)) : Block.uniqueInits ss := by
  unfold Block.uniqueInits at h ⊢
  rw [Block.initVars] at h
  exact (List.nodup_append.mp h).2.1

private theorem Block.uniqueInits.head_stmt {P : PureExpr}
    {s : Stmt P (Cmd P)} {ss : List (Stmt P (Cmd P))}
    (h : Block.uniqueInits (s :: ss)) : (Stmt.initVars s).Nodup := by
  unfold Block.uniqueInits at h
  rw [Block.initVars] at h
  exact (List.nodup_append.mp h).1

private theorem Block.uniqueInits.block_body {P : PureExpr}
    {label : String} {bss : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))}
    (h : Block.uniqueInits (.block label bss md :: rest)) :
    Block.uniqueInits bss := by
  have h_head := Block.uniqueInits.head_stmt h
  -- Stmt.initVars (.block ...) = Block.initVars bss; so Nodup carries over.
  unfold Stmt.initVars at h_head
  exact h_head

private theorem Block.uniqueInits.ite_then {P : PureExpr}
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))}
    (h : Block.uniqueInits (.ite g tss ess md :: rest)) :
    Block.uniqueInits tss := by
  have h_head := Block.uniqueInits.head_stmt h
  -- Stmt.initVars (.ite _ tss ess _) = Block.initVars tss ++ Block.initVars ess
  unfold Stmt.initVars at h_head
  exact (List.nodup_append.mp h_head).1

private theorem Block.uniqueInits.ite_else {P : PureExpr}
    {g : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))}
    (h : Block.uniqueInits (.ite g tss ess md :: rest)) :
    Block.uniqueInits ess := by
  have h_head := Block.uniqueInits.head_stmt h
  unfold Stmt.initVars at h_head
  exact (List.nodup_append.mp h_head).2.1


/-! ## Generalized simulation

The central lemma: for any continuation `k`, exit-continuation stack, and
accumulated commands, if the structured execution of `ss` from `ρ₀` terminates
(or exits), then the CFG blocks produced by `stmtsToBlocks` can step from the
entry label to the continuation `k` (or the resolved exit target). -/

/-- Simulation lemma operating under StoreAgreement: the input accum trace
runs from `σ_struct_base` (struct side) to `ρ₀.store` (struct side), and
`StoreAgreement σ_struct_base σ_base` holds at the entry. -/
private theorem flushCmds_simulation_agree {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    (extendEval : ExtendEval P)
    (pfx : String)
    (k : String)
    (accum : List (Cmd P))
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : (flushCmds pfx accum .none k gen) = ((entry, blocks), gen'))
    (σ_struct_base σ_base : SemanticStore P)
    (hf_base hf_accum : Bool)
    (ρ₀ : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (h_wf_def : WellFormedSemanticEvalDef ρ₀.eval)
    (h_congr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (h_accum : EvalCmds P (EvalCmd P) ρ₀.eval σ_struct_base accum.reverse ρ₀.store hf_accum)
    (h_agree_entry : StoreAgreement σ_struct_base σ_base)
    (h_fresh_accum : ∀ x ∈ Cmds.definedVars accum.reverse, σ_base x = none)
    (h_unique_accum : (Cmds.definedVars accum.reverse).Nodup)
    (h_hf : ρ₀.hasFailure = (hf_base || hf_accum))
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (h_cfg_blocks : ∀ b ∈ blocks, b ∈ cfg.blocks)
    (h_cfg_nodup : (cfg.blocks.map Prod.fst).Nodup) :
    ∃ σ_cfg, StepDetCFGStar extendEval cfg
      (.atBlock entry σ_base hf_base)
      (.atBlock k σ_cfg ρ₀.hasFailure)
      ∧ StoreAgreement ρ₀.store σ_cfg
      ∧ (∀ x, σ_base x = none → x ∉ Cmds.definedVars accum.reverse → σ_cfg x = none) := by
  unfold flushCmds at h_gen
  simp only at h_gen
  split at h_gen
  case isTrue h_empty =>
    have ⟨h_entry, h_blocks⟩ := Prod.mk.inj (Prod.mk.inj h_gen).1
    subst h_entry; subst h_blocks
    have h_nil : accum.reverse = [] := by
      simp [List.isEmpty_iff] at h_empty; simp [h_empty]
    have ⟨h_store, h_fail⟩ := EvalCmds_inv ρ₀.eval σ_struct_base ρ₀.store hf_accum
      (h_nil ▸ h_accum)
    subst h_store; subst h_fail
    simp [Bool.or_false] at h_hf
    rw [h_hf]
    refine ⟨σ_base, ReflTrans.refl _, h_agree_entry, ?_⟩
    intro x h_σ_x _
    exact h_σ_x
  case isFalse h_nonempty =>
    simp only [bind, StateT.bind, pure, StateT.pure, Id] at h_gen
    injection h_gen with h_pair h_gen_eq
    injection h_pair with h_entry_eq h_blks_eq
    subst h_entry_eq; subst h_blks_eq
    have ⟨σ_cfg_after, h_accum_cfg, h_agree_after⟩ :=
      EvalCmds_under_agreement ρ₀.eval accum.reverse h_wf_def h_congr
        σ_struct_base σ_base ρ₀.store hf_accum h_agree_entry h_accum h_fresh_accum
        h_unique_accum
    have h_mem :
        ((StringGenState.gen pfx gen).fst,
          ({ cmds := accum.reverse, transfer := DetTransferCmd.goto k .empty }
            : DetBlock String (Cmd P) P)) ∈ cfg.blocks :=
      h_cfg_blocks _ (List.Mem.head _)
    have h_cond_tt : ρ₀.eval σ_cfg_after HasBool.tt = .some HasBool.tt :=
      eval_tt_is_tt ρ₀.eval σ_cfg_after hwfv
    have h_lkp : cfg.blocks.lookup (StringGenState.gen pfx gen).fst =
        some { cmds := accum.reverse, transfer := DetTransferCmd.goto k .empty } :=
      List.lookup_of_mem_nodup cfg.blocks h_cfg_nodup _ _ h_mem
    -- `.goto k .empty` ≡ `.condGoto tt k k .empty`; reuse `run_block_goto_true`.
    have h_lkp' : cfg.blocks.lookup (StringGenState.gen pfx gen).fst =
        some { cmds := accum.reverse,
               transfer := DetTransferCmd.condGoto HasBool.tt k k .empty } := h_lkp
    have h_run := run_block_goto_true (extendEval := extendEval) (cfg := cfg)
                    (f_base := hf_base) h_lkp' h_accum_cfg h_cond_tt hwfb h_congr
    rw [← h_hf] at h_run
    refine ⟨σ_cfg_after, h_run, h_agree_after, ?_⟩
    intro x h_σ_base_x h_x_not_def
    exact agreement_helper_unchanged_at_x_multi h_accum_cfg h_x_not_def h_σ_base_x

/-- Helper: variant of `flushCmds_simulation_agree` for the `flushCmds` shape
where the transfer is provided as `.some (.goto bk md)` (used in the `.exit`
constructor of `stmtsToBlocks`).  The block always materializes a single
fresh block (regardless of whether `accum` is empty), since the transfer is
explicit. -/
private theorem flushCmds_goto_simulation_agree {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    (extendEval : ExtendEval P)
    (pfx : String) (accum : List (Cmd P)) (md : MetaData P) (bk : String)
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : flushCmds pfx accum (.some (.goto bk md)) bk gen
      = ((entry, blocks), gen'))
    (σ_struct_base σ_base : SemanticStore P)
    (hf_base hf_accum : Bool)
    (ρ₀ : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (h_wf_def : WellFormedSemanticEvalDef ρ₀.eval)
    (h_congr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (h_accum : EvalCmds P (EvalCmd P) ρ₀.eval σ_struct_base accum.reverse ρ₀.store hf_accum)
    (h_agree_entry : StoreAgreement σ_struct_base σ_base)
    (h_fresh_accum : ∀ x ∈ Cmds.definedVars accum.reverse, σ_base x = none)
    (h_unique_accum : (Cmds.definedVars accum.reverse).Nodup)
    (h_hf : ρ₀.hasFailure = (hf_base || hf_accum))
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (h_cfg_blocks : ∀ b ∈ blocks, b ∈ cfg.blocks)
    (h_cfg_nodup : (cfg.blocks.map Prod.fst).Nodup) :
    ∃ σ_cfg, StepDetCFGStar extendEval cfg
      (.atBlock entry σ_base hf_base)
      (.atBlock bk σ_cfg ρ₀.hasFailure)
      ∧ StoreAgreement ρ₀.store σ_cfg
      ∧ (∀ x, σ_base x = none → x ∉ Cmds.definedVars accum.reverse → σ_cfg x = none) := by
  unfold flushCmds at h_gen
  simp only [bind, StateT.bind, pure, StateT.pure, Id] at h_gen
  injection h_gen with h_pair h_gen_eq
  injection h_pair with h_entry_eq h_blks_eq
  subst h_entry_eq; subst h_blks_eq
  have ⟨σ_cfg_after, h_accum_cfg, h_agree_after⟩ :=
    EvalCmds_under_agreement ρ₀.eval accum.reverse h_wf_def h_congr
      σ_struct_base σ_base ρ₀.store hf_accum h_agree_entry h_accum h_fresh_accum
      h_unique_accum
  have h_mem :
      ((StringGenState.gen pfx gen).fst,
        ({ cmds := accum.reverse, transfer := DetTransferCmd.goto bk md }
          : DetBlock String (Cmd P) P)) ∈ cfg.blocks :=
    h_cfg_blocks _ (List.Mem.head _)
  have h_cond_tt : ρ₀.eval σ_cfg_after HasBool.tt = .some HasBool.tt :=
    eval_tt_is_tt ρ₀.eval σ_cfg_after hwfv
  have h_lkp : cfg.blocks.lookup (StringGenState.gen pfx gen).fst =
      some { cmds := accum.reverse, transfer := DetTransferCmd.goto bk md } :=
    List.lookup_of_mem_nodup cfg.blocks h_cfg_nodup _ _ h_mem
  -- `.goto bk md` ≡ `.condGoto tt bk bk md`; reuse `run_block_goto_true`.
  have h_lkp' : cfg.blocks.lookup (StringGenState.gen pfx gen).fst =
      some { cmds := accum.reverse,
             transfer := DetTransferCmd.condGoto HasBool.tt bk bk md } := h_lkp
  have h_run := run_block_goto_true (extendEval := extendEval) (cfg := cfg)
                  (f_base := hf_base) h_lkp' h_accum_cfg h_cond_tt hwfb h_congr
  rw [← h_hf] at h_run
  refine ⟨σ_cfg_after, h_run, h_agree_after, ?_⟩
  intro x h_σ_base_x h_x_not_def
  exact agreement_helper_unchanged_at_x_multi h_accum_cfg h_x_not_def h_σ_base_x

/-- Stronger inversion of `.block (.some label') σ_parent inner → .exiting lbl ρ'`:
    when the block has an explicit label and propagates an exit, the inner exit
    label `lbl_inner` is exactly the propagated `lbl`, AND the block's own label
    `label'` differs from `lbl` (since the propagation rule
    `step_block_exit_mismatch` requires `.some label' ≠ .some lbl`). -/
private theorem block_some_reaches_exiting {P : PureExpr} {CmdT : Type}
    [HasBool P] [HasNot P]
    {EvalCmd : EvalCmdParam P CmdT} {extendEval : ExtendEval P}
    {inner : Config P CmdT} {label' : String} {σ_parent : SemanticStore P}
    {lbl : String} {ρ' : Env P}
    (hstar : StepStmtStar P EvalCmd extendEval
      (.block (.some label') σ_parent inner) (.exiting lbl ρ')) :
    label' ≠ lbl ∧
    ∃ ρ_inner, StepStmtStar P EvalCmd extendEval inner (.exiting lbl ρ_inner) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } := by
  suffices ∀ src tgt, StepStmtStar P EvalCmd extendEval src tgt →
      ∀ inner lbl ρ', src = .block (.some label') σ_parent inner →
        tgt = .exiting lbl ρ' →
      label' ≠ lbl ∧
      ∃ ρ_inner, StepStmtStar P EvalCmd extendEval inner (.exiting lbl ρ_inner) ∧
        ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } from
    this _ _ hstar _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner lbl ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      have ⟨hne, ρ_inner, hexit, heq⟩ := ih _ _ _ rfl htgt
      exact ⟨hne, ρ_inner, .step _ _ _ h hexit, heq⟩
    | step_block_exit_mismatch hne =>
      subst htgt
      cases hrest with
      | refl =>
        refine ⟨?_, _, .refl _, rfl⟩
        intro h
        apply hne
        exact congrArg some h
      | step _ _ _ h _ => cases h
    | step_block_done | step_block_exit_match =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h

/-- Helper for cascading the `h_store_no_gens` precondition from `σ_base`
to `σ_cfg_after = (lifted accum)` after running accum on the CFG side.
Uses the digit-suffix property of `s` together with the assumption that no
accum-defined variable has a digit-suffixed shape to argue that
`ident s ∉ Cmds.definedVars accum.reverse`, then invokes
`agreement_helper_unchanged_at_x_multi`. -/
private theorem store_no_gens_lift_after_accum {P : PureExpr}
    [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [HasIdent P] [DecidableEq P.Ident]
    {Q : String → Prop}
    {δ : SemanticEval P} {σ_base σ_cfg_after : SemanticStore P}
    {accum : List (Cmd P)} {failed : Bool}
    (h_accum_cfg : EvalCmds P (@EvalCmd P _ _ _ _) δ σ_base accum.reverse σ_cfg_after failed)
    (gen : StringGenState)
    (h_store_no_gens : ∀ x : String,
        Q x →
        x ∉ StringGenState.stringGens gen →
        σ_base (HasIdent.ident (P := P) x) = none)
    (h_accum_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars accum.reverse)) :
    ∀ x : String,
        Q x →
        x ∉ StringGenState.stringGens gen →
        σ_cfg_after (HasIdent.ident (P := P) x) = none := by
  intro x h_suf h_not_in
  have h_x_not_def : HasIdent.ident (P := P) x ∉ Cmds.definedVars accum.reverse := by
    intro h_in
    exact h_accum_no_gen_suffix _ h_in x rfl h_suf
  exact agreement_helper_unchanged_at_x_multi h_accum_cfg h_x_not_def
    (h_store_no_gens x h_suf h_not_in)

/-- Sibling of `store_no_gens_lift_after_accum` that lifts `h_store_no_gens`
through the freshness-preservation clause produced by `flushCmds_simulation_agree`,
i.e. `h_preserve_flush : ∀ x, σ_base x = none → x ∉ Cmds.definedVars accum.reverse →
σ_cfg_after x = none`. -/
private theorem store_no_gens_lift_after_flush {P : PureExpr}
    [HasIdent P]
    {Q : String → Prop}
    {σ_base σ_cfg_after : SemanticStore P}
    {accum : List (Cmd P)}
    (h_preserve_flush : ∀ x : P.Ident,
        σ_base x = none → x ∉ Cmds.definedVars accum.reverse → σ_cfg_after x = none)
    (gen : StringGenState)
    (h_store_no_gens : ∀ x : String,
        Q x →
        x ∉ StringGenState.stringGens gen →
        σ_base (HasIdent.ident (P := P) x) = none)
    (h_accum_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars accum.reverse)) :
    ∀ x : String,
        Q x →
        x ∉ StringGenState.stringGens gen →
        σ_cfg_after (HasIdent.ident (P := P) x) = none := by
  intro x h_suf h_not_in
  have h_x_not_accum : HasIdent.ident (P := P) x ∉ Cmds.definedVars accum.reverse := by
    intro h_in
    exact h_accum_no_gen_suffix _ h_in x rfl h_suf
  exact h_preserve_flush _ (h_store_no_gens x h_suf h_not_in) h_x_not_accum

/-- Helper for cascading `h_store_no_gens_upper` through a sub-simulation
that runs `(empty accum)` and produces a final store `σ_branch` agreeing with
the sub's terminal structured store.

Consumes the strengthened (4-premise) `h_preserve` from the sub-simulation
directly.  Discharges the disjunction-guard premise using the upper-bound
subset chain `gen_inner' ⊆ genUpperBound`: at a gen-suffix `x` with
`x ∉ stringGens genUpperBound`, the disjunction `s ∈ gen_inner ∨
s ∉ gen_inner'` is discharged by `Or.inr` since `gen_inner' ⊆ genUpperBound`. -/
private theorem store_no_gens_upper_lift_through_subsim {P : PureExpr}
    [HasIdent P] [LawfulHasIdent P]
    {Q : String → Prop}
    {σ_in σ_branch : SemanticStore P}
    {sub_init : List P.Ident}
    (gen_inner gen_inner' genUpperBound : StringGenState)
    (h_outer_upper : StringGenState.stringGens gen_inner' ⊆
        StringGenState.stringGens genUpperBound)
    (h_preserve : ∀ x : P.Ident, σ_in x = none →
        x ∉ Cmds.definedVars ([] : List (Cmd P)).reverse → x ∉ sub_init →
        (∀ s : String, x = HasIdent.ident (P := P) s →
            s ∈ StringGenState.stringGens gen_inner ∨
            s ∉ StringGenState.stringGens gen_inner') →
        σ_branch x = none)
    (h_store_no_gens_upper : ∀ x : String,
        Q x →
        x ∉ StringGenState.stringGens genUpperBound →
        σ_in (HasIdent.ident (P := P) x) = none)
    (h_sub_no_gen_suffix : NoGenSuffix (P := P) Q sub_init) :
    ∀ x : String,
        Q x →
        x ∉ StringGenState.stringGens genUpperBound →
        σ_branch (HasIdent.ident (P := P) x) = none := by
  intro x h_suf h_not_in
  have h_nil : HasIdent.ident (P := P) x ∉ Cmds.definedVars ([] : List (Cmd P)).reverse := by
    simp [Cmds.definedVars]
  have h_not_sub : HasIdent.ident (P := P) x ∉ sub_init := by
    intro h_in
    exact h_sub_no_gen_suffix _ h_in x rfl h_suf
  refine h_preserve _ (h_store_no_gens_upper x h_suf h_not_in) h_nil h_not_sub ?_
  intro s heq
  have hxs : x = s := LawfulHasIdent.ident_inj heq
  exact Or.inr (fun h_in_inner' => h_not_in (h_outer_upper (hxs ▸ h_in_inner')))
/-- Snoc/cons rebracketing bundle for the `.cmd c :: rest` arm of
`stmtsToBlocks_simulation`. -/
private theorem cmd_arm_combined_lemmas {P : PureExpr}
    [HasIdent P] [HasVarsPure P P.Expr]
    {Q : String → Prop}
    (c : Cmd P) (accum : List (Cmd P)) (rest : List (Stmt P (Cmd P)))
    (σ_base : SemanticStore P)
    (h_fresh : ∀ x ∈ Cmds.definedVars accum.reverse ++ Block.initVars (.cmd c :: rest), σ_base x = none)
    (h_uniq  : (Cmds.definedVars accum.reverse ++ Block.initVars (.cmd c :: rest)).Nodup)
    (h_no_d  : NoGenSuffix (P := P) Q (Cmds.definedVars accum.reverse ++ Block.initVars (.cmd c :: rest)))
    (h_no_m  : NoGenSuffix (P := P) Q (Cmds.modifiedVars accum.reverse ++ transformBlockModVars (.cmd c :: rest))) :
    Cmds.definedVars (accum.reverse ++ [c]) = Cmds.definedVars accum.reverse ++ Cmd.definedVars c
      ∧ (∀ x ∈ Cmds.definedVars (c :: accum).reverse ++ Block.initVars rest, σ_base x = none)
      ∧ (Cmds.definedVars (c :: accum).reverse ++ Block.initVars rest).Nodup
      ∧ (NoGenSuffix (P := P) Q (Cmds.definedVars (c :: accum).reverse ++ Block.initVars rest))
      ∧ (NoGenSuffix (P := P) Q (Cmds.modifiedVars (c :: accum).reverse ++ transformBlockModVars rest)) := by
  have h_d_snoc : Cmds.definedVars (accum.reverse ++ [c]) =
      Cmds.definedVars accum.reverse ++ Cmd.definedVars c := by
    induction accum.reverse with
    | nil => simp [Cmds.definedVars]
    | cons hd tl ih =>
      rw [List.cons_append, Cmds.definedVars_cons, Cmds.definedVars_cons, ih, List.append_assoc]
  have h_d : Cmds.definedVars (c :: accum).reverse ++ Block.initVars rest =
      Cmds.definedVars accum.reverse ++ Block.initVars (.cmd c :: rest) := by
    rw [List.reverse_cons, h_d_snoc, Block.initVars]
    cases c <;> simp [Stmt.initVars, Cmd.definedVars, List.append_assoc]
  have h_m_snoc : Cmds.modifiedVars (accum.reverse ++ [c]) =
      Cmds.modifiedVars accum.reverse ++ Cmd.modifiedVars c := by
    induction accum.reverse with
    | nil => simp [Cmds.modifiedVars]
    | cons hd tl ih =>
      rw [List.cons_append, Cmds.modifiedVars_cons, Cmds.modifiedVars_cons, ih, List.append_assoc]
  have h_m : Cmds.modifiedVars (c :: accum).reverse ++ transformBlockModVars rest =
      Cmds.modifiedVars accum.reverse ++ transformBlockModVars (.cmd c :: rest) := by
    rw [List.reverse_cons, h_m_snoc, transformBlockModVars_cons,
        transformStmtModVars_cmd, List.append_assoc]
  exact ⟨h_d_snoc,
        fun x hx => h_fresh x (h_d ▸ hx),
        h_d ▸ h_uniq,
        fun x hx s heq => h_no_d x (h_d ▸ hx) s heq,
        fun x hx s heq => h_no_m x (h_m ▸ hx) s heq⟩

/-- Lift the outer guard `gen → gen'` to the inner guard `gen_r → gen_b`,
    given the GenStep chain `gen → gen_r` and `gen_b → gen_f = gen'`.
    Used after every body/then/else recursive arm in `stmtsToBlocks_simulation`. -/
private theorem inner_guard_step_b {P : PureExpr} [HasIdent P]
    {gen gen_r gen_b gen_f gen' : StringGenState} {x : P.Ident}
    (h_step_gen_to_r : StringGenState.GenStep gen gen_r)
    (h_step_b_to_f : StringGenState.GenStep gen_b gen_f)
    (h_gen_eq_f : gen_f = gen')
    (h_outer_guard : ∀ s : String, x = HasIdent.ident (P := P) s →
        s ∈ StringGenState.stringGens gen ∨
        s ∉ StringGenState.stringGens gen') :
    ∀ s : String, x = HasIdent.ident (P := P) s →
        s ∈ StringGenState.stringGens gen_r ∨
        s ∉ StringGenState.stringGens gen_b :=
  fun s heq => match h_outer_guard s heq with
  | Or.inl h_in => Or.inl (h_step_gen_to_r.subset h_in)
  | Or.inr h_not_in => Or.inr (fun h_in_b => h_not_in
      (h_gen_eq_f ▸ h_step_b_to_f.subset h_in_b))

/-- Lift the outer guard `gen → gen'` to the inner guard `gen → gen_r`,
    given the GenStep chain `gen_r → gen_b → gen_f = gen'`.
    Used after every body/then/else recursive arm in `stmtsToBlocks_simulation`. -/
private theorem inner_guard_step_r {P : PureExpr} [HasIdent P]
    {gen gen_r gen_b gen_f gen' : StringGenState} {x : P.Ident}
    (h_step_b_to_f : StringGenState.GenStep gen_b gen_f)
    (h_step_r_to_b : StringGenState.GenStep gen_r gen_b)
    (h_gen_eq_f : gen_f = gen')
    (h_outer_guard : ∀ s : String, x = HasIdent.ident (P := P) s →
        s ∈ StringGenState.stringGens gen ∨
        s ∉ StringGenState.stringGens gen') :
    ∀ s : String, x = HasIdent.ident (P := P) s →
        s ∈ StringGenState.stringGens gen ∨
        s ∉ StringGenState.stringGens gen_r :=
  fun s heq => match h_outer_guard s heq with
  | Or.inl h_in => Or.inl h_in
  | Or.inr h_not_in => Or.inr (fun h_in_r => h_not_in
      (h_gen_eq_f ▸ h_step_b_to_f.subset (h_step_r_to_b.subset h_in_r)))

/-- Freshness lift through `flushCmds` for both the `body` and `rest` slots'
    init vars, given the standard combined-Nodup, fresh-on-combined, and
    `flushCmds`-preservation hypotheses, plus the 2-way `h_initvars_eq` shape.
    The `.1` component covers `body`, `.2` covers `rest`.
    Used at every body/then/else paired site in `stmtsToBlocks_simulation`. -/
private theorem fresh_inits_after_step {P : PureExpr} [HasIdent P]
    {accum : List (Cmd P)}
    {head : Stmt P (Cmd P)} {body rest : List (Stmt P (Cmd P))}
    {σ_base σ_cfg_after : SemanticStore P}
    (h_initvars_eq : Block.initVars (head :: rest) =
        Block.initVars body ++ Block.initVars rest)
    (h_unique_combined :
        (Cmds.definedVars accum.reverse ++ Block.initVars (head :: rest)).Nodup)
    (h_fresh_combined :
        ∀ x ∈ Cmds.definedVars accum.reverse ++ Block.initVars (head :: rest),
        σ_base x = none)
    (h_preserve_flush : ∀ x : P.Ident,
        σ_base x = none → x ∉ Cmds.definedVars accum.reverse → σ_cfg_after x = none) :
    (∀ x ∈ Block.initVars body, σ_cfg_after x = none)
      ∧ (∀ x ∈ Block.initVars rest, σ_cfg_after x = none) := by
  -- Both slots share the same proof; `h_mem` selects the append side.
  have lift : ∀ (seg : List (Stmt P (Cmd P))),
      (∀ x, x ∈ Block.initVars seg →
        x ∈ Block.initVars body ++ Block.initVars rest) →
      ∀ x ∈ Block.initVars seg, σ_cfg_after x = none := by
    intro seg h_mem x hx
    have h_x_in : x ∈ Block.initVars (head :: rest) := h_initvars_eq ▸ h_mem x hx
    have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := fun h_in_accum =>
      (List.nodup_append.mp h_unique_combined).2.2 x h_in_accum x h_x_in rfl
    have h_σ_base_x : σ_base x = none :=
      h_fresh_combined x (List.mem_append_right _ h_x_in)
    exact h_preserve_flush x h_σ_base_x h_x_not_accum
  exact ⟨lift body (fun _ hx => List.mem_append_left _ hx),
         lift rest (fun _ hx => List.mem_append_right _ hx)⟩

/-- Freshness lift through the body sub-simulation's `h_preserve_body` for
    `rest`'s init vars.  Consumes the `_after` freshness from
    `fresh_inits_after_step`, plus `h_unique`, the 2-way `h_initvars_eq`,
    `h_preserve_body` (5-premise form), the `gen_b`-foreign discharge
    `h_foreign_b`, and the per-element no-gen-suffix discharge.

    The disjunction-guard premise of `h_preserve_body` is discharged via
    `Or.inr (s ∉ stringGens gen_b)`: a `rest`-init var `s` fails the kind
    predicate `Q` (it is user source), and `h_foreign_b` certifies that any
    non-`Q` string is absent from this pass's generated labels.  Instantiating
    `Q := HasUnderscoreDigitSuffix` recovers the blanket discharge via a WF
    generator (every generated label is gen-shaped, so a non-gen-shaped `s`
    cannot have been minted).
    Used at every body/then/else paired site in `stmtsToBlocks_simulation`. -/
private theorem fresh_rest_inits_body_step {P : PureExpr} [HasIdent P]
    {Q : String → Prop}
    {head : Stmt P (Cmd P)} {body rest : List (Stmt P (Cmd P))}
    {σ_cfg_after σ_cfg_body : SemanticStore P}
    {gen_pre gen_b : StringGenState}
    (h_initvars_eq : Block.initVars (head :: rest) =
        Block.initVars body ++ Block.initVars rest)
    (h_unique : Block.uniqueInits (head :: rest))
    (h_preserve_body : ∀ x : P.Ident,
        σ_cfg_after x = none →
        x ∉ Cmds.definedVars ([] : List (Cmd P)).reverse →
        x ∉ Block.initVars body →
        (∀ s : String, x = HasIdent.ident (P := P) s →
            s ∈ StringGenState.stringGens gen_pre ∨
            s ∉ StringGenState.stringGens gen_b) →
        σ_cfg_body x = none)
    (h_foreign_b : ∀ s : String, ¬ Q s → s ∉ StringGenState.stringGens gen_b)
    (h_rest_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars ([] : List (Cmd P)).reverse ++ Block.initVars rest))
    (h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none) :
    ∀ x ∈ Block.initVars rest, σ_cfg_body x = none := by
  intro x hx
  have h_x_not_body : x ∉ Block.initVars body := by
    intro h_in_body
    unfold Block.uniqueInits at h_unique
    rw [h_initvars_eq] at h_unique
    have h_disj_lr := (List.nodup_append.mp h_unique).2.2
    exact h_disj_lr x h_in_body x hx rfl
  have h_σ_after_x : σ_cfg_after x = none := h_fresh_rest_inits_after x hx
  have h_nil_not : x ∉ Cmds.definedVars ([] : List (Cmd P)).reverse := by
    simp [Cmds.definedVars]
  exact h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
    (fun s heq => Or.inr
      (h_foreign_b s
        (h_rest_no_gen_suffix x (by simp [Cmds.definedVars]; exact hx) s heq)))

/-- Project all three slot init-vars `Nodup` facts (`thenBranch`, `elseBranch`,
    `rest`) out of the .ite-arm `h_unique_outer_inits`.  Components are consumed
    via `.1` / `.2.1` / `.2.2` for `h_unique_combined_{then,else,rest}`. -/
private theorem unique_combined_ite {P : PureExpr} [HasIdent P]
    {accum : List (Cmd P)} {thenBranch elseBranch rest : List (Stmt P (Cmd P))}
    (h_unique_outer_inits :
        (Cmds.definedVars accum.reverse ++
          ((Block.initVars thenBranch ++ Block.initVars elseBranch) ++
            Block.initVars rest)).Nodup) :
    (Cmds.definedVars ([] : List (Cmd P)).reverse ++ Block.initVars thenBranch).Nodup
      ∧ (Cmds.definedVars ([] : List (Cmd P)).reverse ++ Block.initVars elseBranch).Nodup
      ∧ (Cmds.definedVars ([] : List (Cmd P)).reverse ++ Block.initVars rest).Nodup := by
  simp only [Cmds.definedVars, List.reverse_nil, List.nil_append]
  refine ⟨?_, ?_, ?_⟩
  · exact (List.nodup_append.mp
      (List.nodup_append.mp (List.nodup_append.mp h_unique_outer_inits).2.1).1).1
  · exact (List.nodup_append.mp
      (List.nodup_append.mp (List.nodup_append.mp h_unique_outer_inits).2.1).1).2.1
  · exact (List.nodup_append.mp (List.nodup_append.mp h_unique_outer_inits).2.1).2.1

/-- No-op-prepend bundle for the `.typeDecl` arm of `stmtsToBlocks_simulation`. -/
private theorem typeDecl_arm_combined_lemmas {P : PureExpr}
    [HasIdent P] [HasVarsPure P P.Expr]
    {Q : String → Prop}
    (tc : TypeConstructor) (md : MetaData P) (accum : List (Cmd P))
    (rest : List (Stmt P (Cmd P))) (σ_base : SemanticStore P)
    (h_fresh : ∀ x ∈ Cmds.definedVars accum.reverse ++ Block.initVars (.typeDecl tc md :: rest), σ_base x = none)
    (h_uniq  : (Cmds.definedVars accum.reverse ++ Block.initVars (.typeDecl tc md :: rest)).Nodup)
    (h_no_d  : NoGenSuffix (P := P) Q (Cmds.definedVars accum.reverse ++ Block.initVars (.typeDecl tc md :: rest)))
    (h_no_m  : NoGenSuffix (P := P) Q (Cmds.modifiedVars accum.reverse ++ transformBlockModVars (.typeDecl tc md :: rest))) :
    (∀ x ∈ Cmds.definedVars accum.reverse ++ Block.initVars rest, σ_base x = none)
      ∧ (Cmds.definedVars accum.reverse ++ Block.initVars rest).Nodup
      ∧ (NoGenSuffix (P := P) Q (Cmds.definedVars accum.reverse ++ Block.initVars rest))
      ∧ (NoGenSuffix (P := P) Q (Cmds.modifiedVars accum.reverse ++ transformBlockModVars rest)) := by
  have h_d : Cmds.definedVars accum.reverse ++ Block.initVars rest =
      Cmds.definedVars accum.reverse ++ Block.initVars (.typeDecl tc md :: rest) := by
    simp [Stmt.initVars]
  have h_m : Cmds.modifiedVars accum.reverse ++ transformBlockModVars rest =
      Cmds.modifiedVars accum.reverse ++ transformBlockModVars (.typeDecl tc md :: rest) := by
    rw [transformBlockModVars_cons, transformStmtModVars_typeDecl, List.nil_append]
  exact ⟨fun x hx => h_fresh x (h_d ▸ hx),
        h_d ▸ h_uniq,
        fun x hx s heq => h_no_d x (h_d ▸ hx) s heq,
        fun x hx s heq => h_no_m x (h_m ▸ hx) s heq⟩

/-! ### InlineLoopHelpers

Non-recursive helpers that the inlined `.loop` arm proofs in
`stmtsToBlocks_simulation` / `stmtsToBlocks_simulation_to_cont` rely on.

These helpers MUST NOT call `stmtsToBlocks_simulation` or
`stmtsToBlocks_simulation_to_cont` (those are inside the mutual block
below). Helpers may freely use CFG semantics, small-step stmt semantics,
and any prior file-level lemmas. -/

namespace InlineLoopHelpers

/-! ### ReflTransT structured-side peeling helpers

These are length-indexed (Type-valued) variants of the `seq`/`block`/`stmts`
inversion lemmas, used to drive the loop-iteration induction on the structured
derivation length.  They are re-declared here (verbatim ports of the `private`
versions in `DetToKleeneCorrect.lean` and the smoke-test) because the upstream
ones are `private`. -/

private theorem seqT_reaches_terminal' {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P)
    {inner : Config P (Cmd P)} {ss : List (Stmt P (Cmd P))} {ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.seq inner ss) (.terminal ρ')) :
    ∃ (ρ₁ : Env P), ∃ (h1 : ReflTransT (StepStmt P (EvalCmd P) extendEval) inner (.terminal ρ₁)),
      ∃ (h2 : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.stmts ss ρ₁) (.terminal ρ')),
      h1.len + h2.len < hstar.len := by
  match hstar with
  | .step _ _ _ (.step_seq_inner h) hrest =>
    have ⟨ρ₁, hterm, htail, hlen⟩ := seqT_reaches_terminal' extendEval hrest
    exact ⟨ρ₁, .step _ _ _ h hterm, htail, by simp [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_seq_done hrest =>
    exact ⟨_, .refl _, hrest, by show 0 + hrest.len < 1 + hrest.len; omega⟩
  | .step _ _ _ .step_seq_exit hrest =>
    match hrest with
    | .step _ _ _ h _ => exact nomatch h

private theorem stmtsT_cons_terminal' {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P)
    {s : Stmt P (Cmd P)} {rest : List (Stmt P (Cmd P))} {ρ₀ ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.stmts (s :: rest) ρ₀) (.terminal ρ')) :
    ∃ (ρ₁ : Env P), ∃ (h1 : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.stmt s ρ₀) (.terminal ρ₁)),
      ∃ (h2 : ReflTransT (StepStmt P (EvalCmd P) extendEval) (.stmts rest ρ₁) (.terminal ρ')),
      h1.len + h2.len + 2 ≤ hstar.len := by
  match hstar with
  | .step _ _ _ .step_stmts_cons hrest =>
    have ⟨ρ₁, h1, h2, hlen⟩ := seqT_reaches_terminal' extendEval hrest
    exact ⟨ρ₁, h1, h2, by simp [ReflTransT.len]; omega⟩

private theorem seqT_reaches_exiting' {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P)
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
    match seqT_reaches_exiting' extendEval hrest with
    | .inl ⟨hexit, hlen⟩ =>
      exact .inl ⟨.step _ _ _ h hexit, by simp [ReflTransT.len]; omega⟩
    | .inr ⟨ρ₁, h1, h2, hlen⟩ =>
      exact .inr ⟨ρ₁, .step _ _ _ h h1, h2, by simp [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_seq_done hrest =>
    exact .inr ⟨_, .refl _, hrest, by show 0 + hrest.len < 1 + hrest.len; omega⟩
  | .step _ _ _ .step_seq_exit hrest =>
    match hrest with
    | .refl _ => exact .inl ⟨.refl _, by show 0 < 1; omega⟩
    | .step _ _ _ h _ => exact nomatch h

private theorem stmtsT_cons_exiting' {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P)
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
    match seqT_reaches_exiting' extendEval hrest with
    | .inl ⟨hexit, hlen⟩ =>
      exact .inl ⟨hexit, by simp [ReflTransT.len]; omega⟩
    | .inr ⟨ρ₁, h1, h2, hlen⟩ =>
      exact .inr ⟨ρ₁, h1, h2, by simp [ReflTransT.len]; omega⟩

private theorem blockT_none_reaches_terminal' {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P)
    {inner : Config P (Cmd P)} {σ_parent : SemanticStore P} {ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P) extendEval)
              (.block .none σ_parent inner) (.terminal ρ')) :
    ∃ (ρ_inner : Env P) (h : ReflTransT (StepStmt P (EvalCmd P) extendEval) inner (.terminal ρ_inner)),
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } ∧
      h.len < hstar.len := by
  match hstar with
  | .step _ (.block _ _ inner₁) _ (.step_block_body h) hrest =>
    have ⟨ρ_inner, hterm, heq, hlen⟩ := blockT_none_reaches_terminal' extendEval hrest
    exact ⟨ρ_inner, .step _ _ _ h hterm, heq, by simp [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_block_done hrest =>
    match hrest with
    | .refl _ => exact ⟨_, .refl _, rfl, by simp [ReflTransT.len]⟩
    | .step _ _ _ h _ => exact nomatch h
  | .step _ _ _ (.step_block_exit_match heq) hrest => exact (nomatch heq)
  | .step _ _ _ (.step_block_exit_mismatch _) hrest =>
    match hrest with
    | .step _ _ _ h _ => exact nomatch h

private theorem blockT_none_reaches_exiting' {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P)
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
    have ⟨ρ_inner, hexit, heq, hlen⟩ := blockT_none_reaches_exiting' extendEval hrest
    exact ⟨ρ_inner, .step _ _ _ h hexit, heq, by simp [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_block_done hrest =>
    match hrest with
    | .step _ _ _ h _ => exact nomatch h
  | .step _ _ _ (.step_block_exit_match heq) _ => exact (nomatch heq)
  | .step _ _ _ (.step_block_exit_mismatch hne) hrest =>
    match hrest with
    | .refl _ => exact ⟨_, .refl _, rfl, by simp [ReflTransT.len]⟩
    | .step _ _ _ h _ => exact nomatch h

/-- Decompose `h_gen` for the
`.loop (.det g) none [] body md :: rest` arm of the translator.
Splits the monadic state-thread into named witnesses for each generation
step, plus equalities matching the translator's output shape.

Specialized to `measure = .none` and `invariants = []` (the only forms
admitted under `noMeasureLoops` and `loopHasNoInvariants`).  Under these
preconditions: `measureCmds = []`, `decreaseBlocks = []`, `invCmds = []`,
`bodyK = lentry`, `contractMd = md`. The block list is
`accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ bsRest` where
`bsRest`'s entry label is `kNext`. -/
theorem loop_det_decompose_h_gen
    {P : PureExpr} [HasFvar P] [HasNot P] [HasVal P] [HasBoolVal P]
    [HasIdent P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasBool P] [LawfulHasIdent P]
    [LawfulHasIntOrder P] [LawfulHasNot P]
    (k : String) (gen gen' : StringGenState)
    (entry : String) (blocks : List (String × DetBlock String (Cmd P) P))
    (accum : List (Cmd P))
    (g : P.Expr) (body : List (Stmt P (Cmd P))) (md : MetaData P)
    (exitConts : List (Option String × String))
    (rest : List (Stmt P (Cmd P)))
    (h_gen : stmtsToBlocks k (.loop (.det g) none [] body md :: rest)
              exitConts accum gen = ((entry, blocks), gen')) :
    ∃ kNext lentry bl bbs bsRest accumEntry accumBlocks,
      ∃ gen_r gen_le gen_b gen_f,
        stmtsToBlocks k rest exitConts [] gen = ((kNext, bsRest), gen_r) ∧
        StringGenState.gen "loop_entry$" gen_r = (lentry, gen_le) ∧
        stmtsToBlocks lentry body ((.none, kNext) :: exitConts) [] gen_le
          = ((bl, bbs), gen_b) ∧
        flushCmds (P := P) (CmdT := Cmd P) "before_loop$" accum .none lentry gen_b
          = ((accumEntry, accumBlocks), gen_f) ∧
        gen_f = gen' ∧
        accumEntry = entry ∧
        let lentryBlk : DetBlock String (Cmd P) P :=
          { cmds := [],
            transfer := DetTransferCmd.condGoto g bl kNext md }
        accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ bsRest = blocks := by
  -- Provide all witness terms as projections so the witness equations
  -- become `rfl`. For the structural part we compute via the translator.
  -- Translator order: rest first, then loop_entry, then body, then flush.
  let restStep := stmtsToBlocks k rest exitConts [] gen
  let kNext := restStep.1.1
  let bsRest := restStep.1.2
  let gen_r := restStep.2
  let lentry := (StringGenState.gen "loop_entry$" gen_r).1
  let gen_le := (StringGenState.gen "loop_entry$" gen_r).2
  let body_step := stmtsToBlocks lentry body ((none, kNext) :: exitConts) [] gen_le
  let bl := body_step.1.1
  let bbs := body_step.1.2
  let gen_b := body_step.2
  let flushStep := @flushCmds P (Cmd P) _ "before_loop$" accum Option.none lentry gen_b
  let accumEntry := flushStep.1.1
  let accumBlocks := flushStep.1.2
  let gen_f := flushStep.2
  have h_rest_eq : stmtsToBlocks k rest exitConts [] gen = ((kNext, bsRest), gen_r) := by
    show restStep = ((restStep.1.1, restStep.1.2), restStep.2); rfl
  have h_le_eq : StringGenState.gen "loop_entry$" gen_r = (lentry, gen_le) := by
    show StringGenState.gen "loop_entry$" gen_r
        = ((StringGenState.gen "loop_entry$" gen_r).1, (StringGenState.gen "loop_entry$" gen_r).2)
    rfl
  have h_body_eq :
      stmtsToBlocks lentry body ((none, kNext) :: exitConts) [] gen_le = ((bl, bbs), gen_b) := by
    show body_step = ((body_step.1.1, body_step.1.2), body_step.2); rfl
  have h_flush_eq :
      flushCmds (P := P) (CmdT := Cmd P) "before_loop$" accum .none lentry gen_b
        = ((accumEntry, accumBlocks), gen_f) := by
    show flushStep = ((flushStep.1.1, flushStep.1.2), flushStep.2); rfl
  let lentryBlk : DetBlock String (Cmd P) P :=
    { cmds := ([] : List (Cmd P)),
      transfer := DetTransferCmd.condGoto g bl kNext md }
  have h_gen_red :
      stmtsToBlocks k (.loop (.det g) none [] body md :: rest) exitConts accum gen
        = ((accumEntry, accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ bsRest), gen_f) := by
    unfold stmtsToBlocks
    simp only [bind, StateT.bind, pure, StateT.pure, List.append_nil,
      List.foldl_nil]
    rfl
  have h_eq_full := h_gen_red.symm.trans h_gen
  have h_pair := (Prod.mk.inj h_eq_full).1
  have h_entry_eq : accumEntry = entry := (Prod.mk.inj h_pair).1
  have h_blocks_eq := (Prod.mk.inj h_pair).2
  have h_gen_eq : gen_f = gen' := (Prod.mk.inj h_eq_full).2
  exact ⟨kNext, lentry, bl, bbs, bsRest, accumEntry, accumBlocks,
         gen_r, gen_le, gen_b, gen_f,
         h_rest_eq, h_le_eq, h_body_eq, h_flush_eq, h_gen_eq, h_entry_eq, h_blocks_eq⟩

/-- Run the (empty-cmds) loop-entry `condGoto` to the branch selected by `b`:
from `.atBlock lentry σ hf` to `.atBlock bl σ hf` (when `b = true`) or
`.atBlock kNext σ hf` (when `b = false`).  Bridges the structured guard
`ρ.eval ρ.store g = (if b then tt else ff)` to the CFG store via
`StoreAgreement` + congruence. -/
private theorem lentry_condGoto {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P)
    (b : Bool)
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (lentry bl kNext : String) (md : MetaData P) (g : P.Expr)
    (δ : SemanticEval P) (σ_struct σ_cfg : SemanticStore P) (hf : Bool)
    (h_lkp : cfg.blocks.lookup lentry = some ⟨[], .condGoto g bl kNext md⟩)
    (h_agree : StoreAgreement σ_struct σ_cfg)
    (hwfb : WellFormedSemanticEvalBool δ)
    (h_wf_def : WellFormedSemanticEvalDef δ)
    (h_congr : WellFormedSemanticEvalExprCongr δ)
    (h_cond : δ σ_struct g = .some (if b then HasBool.tt else HasBool.ff)) :
    StepDetCFGStar extendEval cfg
      (.atBlock lentry σ_cfg hf) (.atBlock (if b then bl else kNext) σ_cfg hf) := by
  have h_def_g : isDefined σ_struct (HasVarsPure.getVars g) :=
    h_wf_def g _ σ_struct h_cond
  have h_pointwise : ∀ y ∈ HasVarsPure.getVars g, σ_struct y = σ_cfg y :=
    store_agreement_pointwise_on_expr_vars σ_struct σ_cfg g h_agree h_def_g
  have h_cond_cfg : δ σ_cfg g = .some (if b then HasBool.tt else HasBool.ff) :=
    h_cond ▸ (h_congr g σ_struct σ_cfg h_pointwise).symm
  cases b with
  | true => simpa using run_block_goto_true (extendEval := extendEval) (cfg := cfg)
              (f_base := hf) h_lkp (EvalCmds.eval_cmds_none) h_cond_cfg hwfb h_congr
  | false => simpa using run_block_goto_false (extendEval := extendEval) (cfg := cfg)
              (f_base := hf) h_lkp (EvalCmds.eval_cmds_none) h_cond_cfg hwfb h_congr

/-- Peel one iteration off a det loop's body+continuation derivation.  Given
the `step_loop_enter` continuation `.seq (.block .none ρ_pre.store (.stmts body
ρ_body_init)) [.loop ...]` reaches terminal, decompose into: the body's stmts
run reaches `.terminal ρ_inner`; the block projection produces `ρ_block`; and
the next loop iteration's `.stmt loop ρ_block` derivation reaches the same
terminal with strictly smaller length.  Specialized to `inv = []`, `m = none`,
and `ρ_body_init = ρ_pre` (the `|| false` collapse). -/
private theorem peel_off_one_iteration_det {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P)
    (g : P.Expr) (body : List (Stmt P (Cmd P))) (md : MetaData P)
    (ρ_pre ρ_post_loop : Env P)
    (hrest : ReflTransT (StepStmt P (EvalCmd P) extendEval)
       (.seq (.block .none ρ_pre.store
                (.stmts body { ρ_pre with hasFailure := ρ_pre.hasFailure || false }))
             [.loop (.det g) none [] body md])
       (.terminal ρ_post_loop)) :
    ∃ (ρ_inner : Env P) (ρ_block : Env P),
      StepStmtStar P (EvalCmd P) extendEval
        (.stmts body { ρ_pre with hasFailure := ρ_pre.hasFailure || false })
        (.terminal ρ_inner) ∧
      ρ_block = { ρ_inner with store := projectStore ρ_pre.store ρ_inner.store } ∧
      ∃ (h_inner_T : ReflTransT (StepStmt P (EvalCmd P) extendEval)
                      (.stmt (Stmt.loop (.det g) none [] body md) ρ_block)
                      (.terminal ρ_post_loop)),
        h_inner_T.len < hrest.len := by
  have ⟨ρ_block_temp, h_block_term, h_loop_stmts, hlen_seq⟩ :=
    seqT_reaches_terminal' extendEval hrest
  have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
    blockT_none_reaches_terminal' extendEval h_block_term
  have ⟨ρ_x, h_loop_T_T, h_nil, hlen_cons⟩ :=
    stmtsT_cons_terminal' extendEval h_loop_stmts
  have hρ_x_eq : ρ_x = ρ_post_loop := by
    match h_nil with
    | .step _ _ _ .step_stmts_nil hr2 =>
      match hr2 with
      | .refl _ => rfl
      | .step _ _ _ h _ => exact nomatch h
  subst hρ_x_eq
  refine ⟨ρ_inner, ρ_block_temp, ?_, heq_ρ_block, h_loop_T_T, ?_⟩
  · exact reflTransT_to_prop h_inner_term
  · omega

/-- `_to_cont` peel for the det loop: given the body+continuation derivation
reaches `.exiting label`, decompose into a `Sum`: either this iteration's body
exits (caseA), or this iteration terminates and the next loop iteration exits
(caseB, with strictly smaller derivation length). -/
private theorem peel_off_one_iteration_to_cont_det {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P)
    (g : P.Expr) (body : List (Stmt P (Cmd P))) (md : MetaData P)
    (ρ_pre ρ_post_loop : Env P) (label : String)
    (hrest : ReflTransT (StepStmt P (EvalCmd P) extendEval)
       (.seq (.block .none ρ_pre.store
                (.stmts body { ρ_pre with hasFailure := ρ_pre.hasFailure || false }))
             [.loop (.det g) none [] body md])
       (.exiting label ρ_post_loop)) :
    (∃ ρ_body_exit,
      StepStmtStar P (EvalCmd P) extendEval
        (.stmts body { ρ_pre with hasFailure := ρ_pre.hasFailure || false })
        (.exiting label ρ_body_exit) ∧
      ρ_post_loop = { ρ_body_exit with
        store := projectStore ρ_pre.store ρ_body_exit.store }) ∨
    (∃ (ρ_inner : Env P) (ρ_block : Env P),
      StepStmtStar P (EvalCmd P) extendEval
        (.stmts body { ρ_pre with hasFailure := ρ_pre.hasFailure || false })
        (.terminal ρ_inner) ∧
      ρ_block = { ρ_inner with store := projectStore ρ_pre.store ρ_inner.store } ∧
      ∃ (h_inner_T : ReflTransT (StepStmt P (EvalCmd P) extendEval)
                      (.stmt (Stmt.loop (.det g) none [] body md) ρ_block)
                      (.exiting label ρ_post_loop)),
        h_inner_T.len < hrest.len) := by
  match seqT_reaches_exiting' extendEval hrest with
  | .inl ⟨h_block_exit, hlen_seq⟩ =>
    have ⟨ρ_body_exit, h_body_exit_T, heq_ρ_post, hlen_block⟩ :=
      blockT_none_reaches_exiting' extendEval h_block_exit
    exact .inl ⟨ρ_body_exit, reflTransT_to_prop h_body_exit_T, heq_ρ_post⟩
  | .inr ⟨ρ_block_temp, h_block_term, h_loop_stmts, hlen_seq⟩ =>
    have ⟨ρ_inner, h_inner_term, heq_ρ_block, hlen_inner⟩ :=
      blockT_none_reaches_terminal' extendEval h_block_term
    match stmtsT_cons_exiting' extendEval h_loop_stmts with
    | .inl ⟨h_loop_T_E, hlen_cons⟩ =>
      refine .inr ⟨ρ_inner, ρ_block_temp, reflTransT_to_prop h_inner_term,
        heq_ρ_block, h_loop_T_E, ?_⟩
      omega
    | .inr ⟨ρ_x, h_loop_T_T, h_nil, hlen_cons⟩ =>
      exfalso
      match h_nil with
      | .step _ _ _ .step_stmts_nil hr2 =>
        match hr2 with
        | .step _ _ _ h _ => exact nomatch h

/-- Iterate the deterministic loop until termination (small-step).  Inducts on
the structured-loop derivation length; each iteration consumes a
`step_loop_enter` prefix of `h_term`, leaving a strictly shorter tail.
Base case: `step_loop_exit` (guard false), where lentry's condGoto picks
`kNext`.  The CFG side of each iteration is `lentry →(cond true) bl →(body
sim) lentry`; the failure flag tracks `ρ_pre'.hasFailure` per iteration. -/
private theorem loop_iterations_det
    {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasBool P] [LawfulHasIdent P]
    [LawfulHasIntOrder P] [LawfulHasNot P]
    (extendEval : ExtendEval P)
    (g : P.Expr) (body : List (Stmt P (Cmd P))) (md : MetaData P)
    (ρ_pre ρ_post_loop : Env P)
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (lentry kNext bl : String)
    (σ_cfg_pre : SemanticStore P)
    (storeInv : SemanticStore P → Prop)
    (h_lentry_lkp : cfg.blocks.lookup lentry = some ⟨[], .condGoto g bl kNext md⟩)
    (h_agree_pre : StoreAgreement ρ_pre.store σ_cfg_pre)
    (h_inv_pre : storeInv σ_cfg_pre)
    (h_term : StepStmtStar P (EvalCmd P) extendEval
       (.stmt (Stmt.loop (.det g) none [] body md) ρ_pre)
       (.terminal ρ_post_loop))
    (h_nofd_body : Block.noFuncDecl body = true)
    (h_body_sim_at :
       ∀ (ρ_iter : Env P) (σ_cfg_iter : SemanticStore P),
         ρ_iter.eval = ρ_pre.eval →
         StoreAgreement ρ_iter.store σ_cfg_iter →
         storeInv σ_cfg_iter →
         ∀ (ρ_body : Env P), StepStmtStar P (EvalCmd P) extendEval
             (.stmts body ρ_iter) (.terminal ρ_body) →
           ∃ σ_cfg_after_body,
             StepDetCFGStar extendEval cfg
               (.atBlock bl σ_cfg_iter ρ_iter.hasFailure)
               (.atBlock lentry σ_cfg_after_body ρ_body.hasFailure) ∧
             StoreAgreement ρ_body.store σ_cfg_after_body ∧
             storeInv σ_cfg_after_body)
    (hwfb_pre : WellFormedSemanticEvalBool ρ_pre.eval)
    (hwf_def_pre : WellFormedSemanticEvalDef ρ_pre.eval)
    (hwfcongr_pre : WellFormedSemanticEvalExprCongr ρ_pre.eval) :
    ∃ σ_cfg_kNext,
      StepDetCFGStar extendEval cfg
        (.atBlock lentry σ_cfg_pre ρ_pre.hasFailure)
        (.atBlock kNext σ_cfg_kNext ρ_post_loop.hasFailure) ∧
      StoreAgreement ρ_post_loop.store σ_cfg_kNext ∧
      storeInv σ_cfg_kNext := by
  have hT : ReflTransT (StepStmt P (EvalCmd P) extendEval)
      (.stmt (Stmt.loop (.det g) none [] body md) ρ_pre)
      (.terminal ρ_post_loop) := reflTrans_to_T h_term
  suffices h_inner :
    ∀ n (ρ_pre' ρ_post' : Env P) (σ_cfg_pre' : SemanticStore P),
      ρ_pre'.eval = ρ_pre.eval →
      WellFormedSemanticEvalBool ρ_pre'.eval →
      WellFormedSemanticEvalDef ρ_pre'.eval →
      WellFormedSemanticEvalExprCongr ρ_pre'.eval →
      StoreAgreement ρ_pre'.store σ_cfg_pre' →
      storeInv σ_cfg_pre' →
      ∀ (hT' : ReflTransT (StepStmt P (EvalCmd P) extendEval)
                 (.stmt (Stmt.loop (.det g) none [] body md) ρ_pre')
                 (.terminal ρ_post')),
        hT'.len ≤ n →
        ∃ σ_cfg_kNext',
          StepDetCFGStar extendEval cfg
            (.atBlock lentry σ_cfg_pre' ρ_pre'.hasFailure)
            (.atBlock kNext σ_cfg_kNext' ρ_post'.hasFailure) ∧
          StoreAgreement ρ_post'.store σ_cfg_kNext' ∧
          storeInv σ_cfg_kNext' from
    h_inner hT.len ρ_pre ρ_post_loop σ_cfg_pre rfl
      hwfb_pre hwf_def_pre hwfcongr_pre h_agree_pre h_inv_pre hT (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intros ρ_pre' ρ_post' σ_cfg_pre' h_eval_eq hwfb' hwf_def' hwfcongr' h_agree' h_inv' hT' hlen'
    match hT', hlen' with
    | .step _ _ _ hab hbc, hl => simp [ReflTransT.len] at hl
  | succ n ih =>
    intros ρ_pre' ρ_post' σ_cfg_pre' h_eval_eq hwfb' hwf_def' hwfcongr' h_agree' h_inv' hT' hlen'
    match hT', hlen' with
    | .step _ _ _ (@StepStmt.step_loop_exit _ _ _ _ _ _ _ _ _ _ _ _
                    hasInvFailure hg_false hinv_eval hff_iff hwfb_step) hrest, hl_succ =>
      -- BASE CASE: guard false.  inv = [], so hasInvFailure = false.
      have h_hif : hasInvFailure = false := by
        cases hasInvFailure with
        | false => rfl
        | true =>
          obtain ⟨le, hle, _⟩ := hff_iff.mp rfl
          simp at hle
      subst h_hif
      have hρ_eq : ρ_post' = ρ_pre' := by
        have : ρ_post' = { ρ_pre' with hasFailure := ρ_pre'.hasFailure || false } := by
          match hrest with
          | .refl _ => rfl
          | .step _ _ _ h _ => exact nomatch h
        simpa using this
      subst hρ_eq
      refine ⟨σ_cfg_pre', ?_, h_agree', h_inv'⟩
      exact lentry_condGoto extendEval false cfg lentry bl kNext md g
        ρ_post'.eval ρ_post'.store σ_cfg_pre' ρ_post'.hasFailure h_lentry_lkp h_agree'
        hwfb' hwf_def' hwfcongr' hg_false
    | .step _ _ _ (@StepStmt.step_loop_enter _ _ _ _ _ _ _ _ _ _ _ _
                    hasInvFailure hg_true hinv_eval hff_iff hwfb_step) hrest, hl_succ =>
      -- INDUCTIVE CASE: guard true.  inv = [], so hasInvFailure = false.
      have h_hif : hasInvFailure = false := by
        cases hasInvFailure with
        | false => rfl
        | true =>
          obtain ⟨le, hle, _⟩ := hff_iff.mp rfl
          simp at hle
      subst h_hif
      -- Peel one iteration off the structured derivation.
      have ⟨ρ_inner, ρ_block, h_body_struct, hρ_block_eq, h_inner_T, h_inner_len⟩ :=
        peel_off_one_iteration_det extendEval g body md ρ_pre' ρ_post' hrest
      -- The body runs from ρ_body_init := { ρ_pre' with hasFailure := ρ_pre'.hasFailure || false }.
      -- Simplify: ρ_body_init = ρ_pre' (since || false is identity on hasFailure).
      have h_body_init_eq :
          ({ ρ_pre' with hasFailure := ρ_pre'.hasFailure || false } : Env P) = ρ_pre' := by
        simp
      rw [h_body_init_eq] at h_body_struct
      -- CFG step 1: lentry → bl (guard true).
      have h_step_enter : StepDetCFGStar extendEval cfg
          (.atBlock lentry σ_cfg_pre' ρ_pre'.hasFailure)
          (.atBlock bl σ_cfg_pre' ρ_pre'.hasFailure) :=
        lentry_condGoto extendEval true cfg lentry bl kNext md g
          ρ_pre'.eval ρ_pre'.store σ_cfg_pre' ρ_pre'.hasFailure h_lentry_lkp h_agree'
          hwfb' hwf_def' hwfcongr' hg_true
      -- CFG step 2: bl → lentry (body sim).
      have ⟨σ_cfg_after_body, h_step_body, h_agree_after_body, h_inv_after⟩ :=
        h_body_sim_at ρ_pre' σ_cfg_pre' h_eval_eq h_agree' h_inv' ρ_inner h_body_struct
      -- ρ_block = { ρ_inner with store := projectStore ρ_pre'.store ρ_inner.store }.
      -- Block.initVars body = [], so projection leaves the store agreement intact.
      have h_agree_block : StoreAgreement ρ_block.store σ_cfg_after_body :=
        StoreAgreement.through_projectStore hρ_block_eq h_agree_after_body
      have h_hf_block : ρ_block.hasFailure = ρ_inner.hasFailure := by rw [hρ_block_eq]
      have hρ_block_eval : ρ_block.eval = ρ_pre'.eval := by
        rw [hρ_block_eq]
        show ρ_inner.eval = ρ_pre'.eval
        have := smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval body
                ρ_pre' ρ_inner h_nofd_body h_body_struct
        rw [this]
      have h_eval_eq_block : ρ_block.eval = ρ_pre.eval := by
        rw [hρ_block_eval]; exact h_eval_eq
      have hwfb_block : WellFormedSemanticEvalBool ρ_block.eval := by
        rw [hρ_block_eval]; exact hwfb'
      have hwf_def_block : WellFormedSemanticEvalDef ρ_block.eval := by
        rw [hρ_block_eval]; exact hwf_def'
      have hwfcongr_block : WellFormedSemanticEvalExprCongr ρ_block.eval := by
        rw [hρ_block_eval]; exact hwfcongr'
      have h_inner_le_n : h_inner_T.len ≤ n := by
        simp [ReflTransT.len] at hl_succ; omega
      -- Recurse on the next iteration.
      have ⟨σ_cfg_kNext, h_run_recurse, h_agree_post, h_inv_post⟩ :=
        ih ρ_block ρ_post' σ_cfg_after_body h_eval_eq_block
           hwfb_block hwf_def_block hwfcongr_block
           h_agree_block h_inv_after h_inner_T h_inner_le_n
      refine ⟨σ_cfg_kNext, ?_, h_agree_post, h_inv_post⟩
      -- Compose: lentry → bl → lentry → ... → kNext.
      -- Transport h_run_recurse's start flag ρ_block.hasFailure to ρ_inner.hasFailure.
      rw [h_hf_block] at h_run_recurse
      exact StepDetCFGStar_trans (StepDetCFGStar_trans h_step_enter h_step_body) h_run_recurse

/-- `_to_cont` iteration helper for the det loop: the loop runs some number of
terminating iterations, then on some iteration the body exits with `label`,
propagating out of the surrounding `.block .none` and hence out of the loop.
The CFG side runs `lentry →(true) bl →(body terminal sim) lentry` for each
completed iteration, then `lentry →(true) bl →(body _to_cont sim) bk_target`
for the exiting iteration. -/
private theorem loop_iterations_to_cont_det
    {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasBool P] [LawfulHasIdent P]
    [LawfulHasIntOrder P] [LawfulHasNot P]
    (extendEval : ExtendEval P)
    (g : P.Expr) (body : List (Stmt P (Cmd P))) (md : MetaData P)
    (ρ_pre ρ_post_loop : Env P) (label : String)
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (lentry kNext bl bk_target : String)
    (σ_cfg_pre : SemanticStore P)
    (storeInv : SemanticStore P → Prop)
    (h_lentry_lkp : cfg.blocks.lookup lentry = some ⟨[], .condGoto g bl kNext md⟩)
    (h_agree_pre : StoreAgreement ρ_pre.store σ_cfg_pre)
    (h_inv_pre : storeInv σ_cfg_pre)
    (h_exit : StepStmtStar P (EvalCmd P) extendEval
       (.stmt (Stmt.loop (.det g) none [] body md) ρ_pre)
       (.exiting label ρ_post_loop))
    (h_nofd_body : Block.noFuncDecl body = true)
    (h_body_sim_at :
       ∀ (ρ_iter : Env P) (σ_cfg_iter : SemanticStore P),
         ρ_iter.eval = ρ_pre.eval →
         StoreAgreement ρ_iter.store σ_cfg_iter →
         storeInv σ_cfg_iter →
         ∀ (ρ_body : Env P), StepStmtStar P (EvalCmd P) extendEval
             (.stmts body ρ_iter) (.terminal ρ_body) →
           ∃ σ_cfg_after_body,
             StepDetCFGStar extendEval cfg
               (.atBlock bl σ_cfg_iter ρ_iter.hasFailure)
               (.atBlock lentry σ_cfg_after_body ρ_body.hasFailure) ∧
             StoreAgreement ρ_body.store σ_cfg_after_body ∧
             storeInv σ_cfg_after_body)
    (h_body_sim_exit_at :
       ∀ (ρ_iter : Env P) (σ_cfg_iter : SemanticStore P),
         ρ_iter.eval = ρ_pre.eval →
         StoreAgreement ρ_iter.store σ_cfg_iter →
         storeInv σ_cfg_iter →
         ∀ (ρ_body : Env P), StepStmtStar P (EvalCmd P) extendEval
             (.stmts body ρ_iter) (.exiting label ρ_body) →
           ∃ σ_cfg_after_body,
             StepDetCFGStar extendEval cfg
               (.atBlock bl σ_cfg_iter ρ_iter.hasFailure)
               (.atBlock bk_target σ_cfg_after_body ρ_body.hasFailure) ∧
             StoreAgreement ρ_body.store σ_cfg_after_body ∧
             storeInv σ_cfg_after_body)
    (hwfb_pre : WellFormedSemanticEvalBool ρ_pre.eval)
    (hwf_def_pre : WellFormedSemanticEvalDef ρ_pre.eval)
    (hwfcongr_pre : WellFormedSemanticEvalExprCongr ρ_pre.eval) :
    ∃ σ_cfg_bk,
      StepDetCFGStar extendEval cfg
        (.atBlock lentry σ_cfg_pre ρ_pre.hasFailure)
        (.atBlock bk_target σ_cfg_bk ρ_post_loop.hasFailure) ∧
      StoreAgreement ρ_post_loop.store σ_cfg_bk ∧
      storeInv σ_cfg_bk := by
  have hT : ReflTransT (StepStmt P (EvalCmd P) extendEval)
      (.stmt (Stmt.loop (.det g) none [] body md) ρ_pre)
      (.exiting label ρ_post_loop) := reflTrans_to_T h_exit
  suffices h_inner :
    ∀ n (ρ_pre' ρ_post' : Env P) (σ_cfg_pre' : SemanticStore P),
      ρ_pre'.eval = ρ_pre.eval →
      WellFormedSemanticEvalBool ρ_pre'.eval →
      WellFormedSemanticEvalDef ρ_pre'.eval →
      WellFormedSemanticEvalExprCongr ρ_pre'.eval →
      StoreAgreement ρ_pre'.store σ_cfg_pre' →
      storeInv σ_cfg_pre' →
      ∀ (hT' : ReflTransT (StepStmt P (EvalCmd P) extendEval)
                 (.stmt (Stmt.loop (.det g) none [] body md) ρ_pre')
                 (.exiting label ρ_post')),
        hT'.len ≤ n →
        ∃ σ_cfg_bk',
          StepDetCFGStar extendEval cfg
            (.atBlock lentry σ_cfg_pre' ρ_pre'.hasFailure)
            (.atBlock bk_target σ_cfg_bk' ρ_post'.hasFailure) ∧
          StoreAgreement ρ_post'.store σ_cfg_bk' ∧
          storeInv σ_cfg_bk' from
    h_inner hT.len ρ_pre ρ_post_loop σ_cfg_pre rfl
      hwfb_pre hwf_def_pre hwfcongr_pre h_agree_pre h_inv_pre hT (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intros ρ_pre' ρ_post' σ_cfg_pre' h_eval_eq hwfb' hwf_def' hwfcongr' h_agree' h_inv' hT' hlen'
    match hT', hlen' with
    | .step _ _ _ hab hbc, hl => simp [ReflTransT.len] at hl
  | succ n ih =>
    intros ρ_pre' ρ_post' σ_cfg_pre' h_eval_eq hwfb' hwf_def' hwfcongr' h_agree' h_inv' hT' hlen'
    match hT', hlen' with
    | .step _ _ _ (@StepStmt.step_loop_exit _ _ _ _ _ _ _ _ _ _ _ _
                    hasInvFailure hg_false hinv_eval hff_iff hwfb_step) hrest, hl_succ =>
      -- A loop that exits via guard-false would reach .terminal, not .exiting.
      exfalso
      match hrest with
      | .step _ _ _ h _ => exact nomatch h
    | .step _ _ _ (@StepStmt.step_loop_enter _ _ _ _ _ _ _ _ _ _ _ _
                    hasInvFailure hg_true hinv_eval hff_iff hwfb_step) hrest, hl_succ =>
      have h_hif : hasInvFailure = false := by
        cases hasInvFailure with
        | false => rfl
        | true =>
          obtain ⟨le, hle, _⟩ := hff_iff.mp rfl
          simp at hle
      subst h_hif
      have h_body_init_eq :
          ({ ρ_pre' with hasFailure := ρ_pre'.hasFailure || false } : Env P) = ρ_pre' := by
        simp
      -- CFG step 1: lentry → bl (guard true).
      have h_step_enter : StepDetCFGStar extendEval cfg
          (.atBlock lentry σ_cfg_pre' ρ_pre'.hasFailure)
          (.atBlock bl σ_cfg_pre' ρ_pre'.hasFailure) :=
        lentry_condGoto extendEval true cfg lentry bl kNext md g
          ρ_pre'.eval ρ_pre'.store σ_cfg_pre' ρ_pre'.hasFailure h_lentry_lkp h_agree'
          hwfb' hwf_def' hwfcongr' hg_true
      rcases peel_off_one_iteration_to_cont_det extendEval g body md ρ_pre' ρ_post' label hrest with
        h_caseA | h_caseB
      · -- caseA: this iteration's body exits with label.
        obtain ⟨ρ_body_exit, h_body_exit_struct, hρ_post_eq⟩ := h_caseA
        rw [h_body_init_eq] at h_body_exit_struct
        have ⟨σ_cfg_after_body, h_step_body, h_agree_after_body, h_inv_after⟩ :=
          h_body_sim_exit_at ρ_pre' σ_cfg_pre' h_eval_eq h_agree' h_inv' ρ_body_exit h_body_exit_struct
        -- ρ_post' = { ρ_body_exit with store := projectStore ρ_pre'.store ρ_body_exit.store }.
        have h_agree_post : StoreAgreement ρ_post'.store σ_cfg_after_body :=
          StoreAgreement.through_projectStore hρ_post_eq h_agree_after_body
        have h_hf_post : ρ_post'.hasFailure = ρ_body_exit.hasFailure := by rw [hρ_post_eq]
        refine ⟨σ_cfg_after_body, ?_, h_agree_post, h_inv_after⟩
        rw [h_hf_post]
        exact StepDetCFGStar_trans h_step_enter h_step_body
      · -- caseB: this iteration terminates; recurse on next iteration's exit.
        obtain ⟨ρ_inner, ρ_block, h_body_struct, hρ_block_eq, h_inner_T, h_inner_len⟩ := h_caseB
        rw [h_body_init_eq] at h_body_struct
        have ⟨σ_cfg_after_body, h_step_body, h_agree_after_body, h_inv_after⟩ :=
          h_body_sim_at ρ_pre' σ_cfg_pre' h_eval_eq h_agree' h_inv' ρ_inner h_body_struct
        have h_agree_block : StoreAgreement ρ_block.store σ_cfg_after_body :=
          StoreAgreement.through_projectStore hρ_block_eq h_agree_after_body
        have h_hf_block : ρ_block.hasFailure = ρ_inner.hasFailure := by rw [hρ_block_eq]
        have hρ_block_eval : ρ_block.eval = ρ_pre'.eval := by
          rw [hρ_block_eq]
          show ρ_inner.eval = ρ_pre'.eval
          have := smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval body
                  ρ_pre' ρ_inner h_nofd_body h_body_struct
          rw [this]
        have h_eval_eq_block : ρ_block.eval = ρ_pre.eval := by
          rw [hρ_block_eval]; exact h_eval_eq
        have hwfb_block : WellFormedSemanticEvalBool ρ_block.eval := by
          rw [hρ_block_eval]; exact hwfb'
        have hwf_def_block : WellFormedSemanticEvalDef ρ_block.eval := by
          rw [hρ_block_eval]; exact hwf_def'
        have hwfcongr_block : WellFormedSemanticEvalExprCongr ρ_block.eval := by
          rw [hρ_block_eval]; exact hwfcongr'
        have h_inner_le_n : h_inner_T.len ≤ n := by
          simp [ReflTransT.len] at hl_succ; omega
        have ⟨σ_cfg_bk, h_run_recurse, h_agree_post, h_inv_post⟩ :=
          ih ρ_block ρ_post' σ_cfg_after_body h_eval_eq_block
             hwfb_block hwf_def_block hwfcongr_block
             h_agree_block h_inv_after h_inner_T h_inner_le_n
        refine ⟨σ_cfg_bk, ?_, h_agree_post, h_inv_post⟩
        rw [h_hf_block] at h_run_recurse
        exact StepDetCFGStar_trans (StepDetCFGStar_trans h_step_enter h_step_body) h_run_recurse

end InlineLoopHelpers

/-- Project the four shape predicates (`simpleShape`, `loopBodyNoInits`,
`loopHasNoInvariants`, `noMeasureLoops`) of an `.ite (.det e)` statement down to
its `then`/`else` branches, given each predicate's head fact. -/
private theorem ite_branch_shape {P : PureExpr}
    {e : P.Expr} {thenBranch elseBranch : List (Stmt P (Cmd P))} {md : MetaData P}
    (h_simple_head : Stmt.simpleShape (.ite (.det e) thenBranch elseBranch md) = true)
    (h_lbni_head : Stmt.loopBodyNoInits (.ite (.det e) thenBranch elseBranch md) = true)
    (h_lhni_head : Stmt.loopHasNoInvariants (.ite (.det e) thenBranch elseBranch md) = true)
    (h_nml_head : Stmt.noMeasureLoops (.ite (.det e) thenBranch elseBranch md) = true) :
    Block.simpleShape thenBranch = true ∧ Block.simpleShape elseBranch = true ∧
    Block.loopBodyNoInits thenBranch = true ∧ Block.loopBodyNoInits elseBranch = true ∧
    Block.loopHasNoInvariants thenBranch = true ∧ Block.loopHasNoInvariants elseBranch = true ∧
    Block.noMeasureLoops thenBranch = true ∧ Block.noMeasureLoops elseBranch = true :=
  ⟨Stmt.simpleShape_branch_then h_simple_head, Stmt.simpleShape_branch_else h_simple_head,
   Stmt.loopBodyNoInits_branch_then h_lbni_head, Stmt.loopBodyNoInits_branch_else h_lbni_head,
   Stmt.loopHasNoInvariants_branch_then h_lhni_head, Stmt.loopHasNoInvariants_branch_else h_lhni_head,
   Stmt.noMeasureLoops_branch_then h_nml_head, Stmt.noMeasureLoops_branch_else h_nml_head⟩

set_option maxHeartbeats 12800000 in
set_option maxRecDepth 1024 in
mutual
/-- The central simulation lemma, written in a StoreAgreement-based shape.

The structured execution runs `accum.reverse` from `σ_struct_base` to `ρ₀.store`,
then continues into `ss` reaching `ρ'`. The CFG starts at `entry` with store
`σ_base` (which agrees with `σ_struct_base`) and the same accumulated commands
get folded into block prefixes. We require:

- `h_agree_entry : StoreAgreement σ_struct_base σ_base` — the CFG-side store
  agrees with the structured-side accum-base.
- `h_fresh_combined : ∀ x ∈ Cmds.definedVars accum.reverse ++ Block.initVars ss,
  σ_base x = none` — every variable that will be initialized (either by accum
  or by upcoming `ss`) is currently fresh on the CFG side.
- `h_unique_combined : (Cmds.definedVars accum.reverse ++ Block.initVars ss).Nodup`
  — those initialized variables form a Nodup list.

The conclusion adds a freshness-preservation conjunct: if `σ_base x = none`
and `x` is not in either accum's defs or `ss`'s inits, then the CFG-side
`σ_cfg x = none`.  This propagates freshness through CFG transitions into
the recursive call on the rest of the program. -/
private theorem stmtsToBlocks_simulation {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasBool P] [LawfulHasIdent P]
    [LawfulHasIntOrder P] [LawfulHasNot P]
    {Q : String → Prop}
    (extendEval : ExtendEval P)
    (k : String) (ss : List (Stmt P (Cmd P)))
    (exitConts : List (Option String × String))
    (accum : List (Cmd P))
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : (stmtsToBlocks k ss exitConts accum gen) = ((entry, blocks), gen'))
    (h_nofd : Block.noFuncDecl ss = true)
    (h_simple : Block.simpleShape ss = true)
    (h_unique : Block.uniqueInits ss)
    (h_lbni : Block.loopBodyNoInits ss = true)
    (h_lhni : Block.loopHasNoInvariants ss = true)
    (h_nml : Block.noMeasureLoops ss = true)
    (σ_struct_base σ_base : SemanticStore P)
    (hf_base : Bool)
    (hf_accum : Bool)
    (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwf_def : WellFormedSemanticEvalDef ρ₀.eval)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (hwf_var : WellFormedSemanticEvalVar ρ₀.eval)
    (h_term : StepStmtStar P (EvalCmd P) extendEval
      (.stmts ss ρ₀) (.terminal ρ'))
    (h_accum : EvalCmds P (EvalCmd P) ρ₀.eval σ_struct_base accum.reverse ρ₀.store hf_accum)
    (h_agree_entry : StoreAgreement σ_struct_base σ_base)
    (h_fresh_combined :
      ∀ x ∈ Cmds.definedVars accum.reverse ++ Block.initVars ss, σ_base x = none)
    (h_unique_combined :
      (Cmds.definedVars accum.reverse ++ Block.initVars ss).Nodup)
    (h_hf : ρ₀.hasFailure = (hf_base || hf_accum))
    (h_wf_gen : StringGenState.WF gen)
    (h_combined_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars accum.reverse ++ Block.initVars ss))
    (h_combined_no_gen_suffix_mod :
        NoGenSuffix (P := P) Q (Cmds.modifiedVars accum.reverse ++ transformBlockModVars ss))
    (genUpperBound : StringGenState)
    (h_outer_upper : StringGenState.stringGens gen' ⊆ StringGenState.stringGens genUpperBound)
    (h_store_no_gens_upper : ∀ x : String,
        Q x →
        x ∉ StringGenState.stringGens genUpperBound →
        σ_base (HasIdent.ident (P := P) x) = none)
    (h_foreign : ∀ s : String, ¬ Q s → s ∉ StringGenState.stringGens genUpperBound)
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (h_cfg_blocks : ∀ b ∈ blocks, b ∈ cfg.blocks)
    (h_cfg_nodup : (cfg.blocks.map Prod.fst).Nodup) :
    ∃ σ_cfg, StepDetCFGStar extendEval cfg
      (.atBlock entry σ_base hf_base)
      (.atBlock k σ_cfg ρ'.hasFailure)
      ∧ StoreAgreement ρ'.store σ_cfg
      ∧ (∀ x, σ_base x = none →
          x ∉ Cmds.definedVars accum.reverse → x ∉ Block.initVars ss →
          (∀ s : String, x = HasIdent.ident (P := P) s →
              s ∈ StringGenState.stringGens gen ∨
              s ∉ StringGenState.stringGens gen') →
          σ_cfg x = none) := by
  match h_match : ss with
  | [] =>
    -- stmtsToBlocks k [] exitConts accum = flushCmds "l$" accum .none k
    unfold stmtsToBlocks at h_gen
    have h_ρ : ρ₀ = ρ' := stmts_nil_terminal (EvalCmd P) extendEval _ _ h_term
    subst h_ρ
    -- Block.initVars [] = [], so combined-fresh reduces to fresh on accum.
    have h_fresh_accum : ∀ x ∈ Cmds.definedVars accum.reverse, σ_base x = none := by
      intro x hx
      apply h_fresh_combined x
      simp [Block.initVars]
      exact hx
    have h_unique_accum : (Cmds.definedVars accum.reverse).Nodup := by
      have h := h_unique_combined
      simp [Block.initVars] at h
      exact h
    have ⟨σ_cfg, h_step, h_agree, h_preserve⟩ :=
      flushCmds_simulation_agree extendEval "l$" k accum gen gen' entry blocks h_gen
        σ_struct_base σ_base hf_base hf_accum ρ₀ hwfb hwfv hwf_def hwf_congr h_accum
        h_agree_entry h_fresh_accum h_unique_accum h_hf cfg h_cfg_blocks h_cfg_nodup
    refine ⟨σ_cfg, h_step, h_agree, ?_⟩
    intro x h_σ_x h_x_not_accum _ _
    exact h_preserve x h_σ_x h_x_not_accum
  | .cmd c :: rest =>
    unfold stmtsToBlocks at h_gen
    -- Structured semantics: execute c then rest
    have ⟨ρ₁, h_c_star, h_rest_star⟩ :=
      stmts_append_terminates P (EvalCmd P) extendEval [.cmd c] rest ρ₀ ρ'
        (by simp at h_term ⊢; exact h_term)
    have ⟨σ_c, failed_c, heval_c, hstore_c, heval_eq_c, hfail_c⟩ :=
      single_cmd_eval extendEval c ρ₀ ρ₁ h_c_star
    have h_accum' : EvalCmds P (EvalCmd P) ρ₁.eval σ_struct_base
        (c :: accum).reverse ρ₁.store (hf_accum || failed_c) := by
      simp [List.reverse_cons]
      rw [heval_eq_c, hstore_c]
      exact EvalCmds_snoc ρ₀.eval σ_struct_base ρ₀.store σ_c accum.reverse c hf_accum failed_c
        h_accum heval_c
    have h_hf' : ρ₁.hasFailure = (hf_base || (hf_accum || failed_c)) := by
      rw [hfail_c, h_hf, Bool.or_assoc]
    have hwfb' : WellFormedSemanticEvalBool ρ₁.eval := heval_eq_c ▸ hwfb
    have hwfv' : WellFormedSemanticEvalVal ρ₁.eval := heval_eq_c ▸ hwfv
    have hwf_def' : WellFormedSemanticEvalDef ρ₁.eval := heval_eq_c ▸ hwf_def
    have hwf_congr' : WellFormedSemanticEvalExprCongr ρ₁.eval := heval_eq_c ▸ hwf_congr
    have hwf_var' : WellFormedSemanticEvalVar ρ₁.eval := heval_eq_c ▸ hwf_var
    have h_nofd_rest : Block.noFuncDecl rest = true := by
      simp [Block.noFuncDecl] at h_nofd; exact h_nofd.2
    have h_simple_rest : Block.simpleShape rest = true :=
      (Block.simpleShape_cons_iff.mp h_simple).2
    have h_unique_rest : Block.uniqueInits rest := Block.uniqueInits.tail h_unique
    have h_lbni_rest : Block.loopBodyNoInits rest = true :=
      (Block.loopBodyNoInits_cons_iff.mp h_lbni).2
    have h_lhni_rest : Block.loopHasNoInvariants rest = true :=
      (Block.loopHasNoInvariants_cons_iff.mp h_lhni).2
    have h_nml_rest : Block.noMeasureLoops rest = true :=
      (Block.noMeasureLoops_cons_iff.mp h_nml).2
    -- Snoc/cons rebracketing facts shared between _simulation and _to_cont.
    have ⟨h_definedVars_snoc, h_fresh_combined', h_unique_combined',
          h_combined_no_gen_suffix', h_combined_no_gen_suffix_mod'⟩ :=
      cmd_arm_combined_lemmas c accum rest σ_base
        h_fresh_combined h_unique_combined
        h_combined_no_gen_suffix h_combined_no_gen_suffix_mod
    have ⟨σ_cfg, h_step, h_agree, h_preserve⟩ :=
      stmtsToBlocks_simulation extendEval k rest exitConts (c :: accum) gen gen'
        entry blocks h_gen h_nofd_rest h_simple_rest h_unique_rest
        h_lbni_rest h_lhni_rest h_nml_rest
        σ_struct_base σ_base hf_base (hf_accum || failed_c)
        ρ₁ ρ' hwfb' hwfv' hwf_def' hwf_congr' hwf_var'
       h_rest_star h_accum'
        h_agree_entry h_fresh_combined' h_unique_combined' h_hf'
        h_wf_gen h_combined_no_gen_suffix' h_combined_no_gen_suffix_mod'
        genUpperBound h_outer_upper h_store_no_gens_upper h_foreign
        cfg h_cfg_blocks h_cfg_nodup
    refine ⟨σ_cfg, h_step, h_agree, ?_⟩
    intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
    -- σ_base x = none ∧ x ∉ accum ∧ x ∉ Block.initVars (.cmd c :: rest)
    -- Need: σ_cfg x = none.
    -- Goal premises for h_preserve:
    --   x ∉ Cmds.definedVars (c :: accum).reverse ∧ x ∉ Block.initVars rest
    have h_x_not_new_accum : x ∉ Cmds.definedVars (c :: accum).reverse := by
      rw [List.reverse_cons, h_definedVars_snoc]
      intro h_in
      cases List.mem_append.mp h_in with
      | inl h => exact h_x_not_accum h
      | inr h =>
        -- x in Cmd.definedVars c; this means c is .init x ...
        cases c with
        | init x' _ _ _ =>
          simp [Cmd.definedVars] at h
          subst h
          apply h_x_not_inits
          simp [Stmt.initVars]
        | _ => simp [Cmd.definedVars] at h
    have h_x_not_rest_inits : x ∉ Block.initVars rest := by
      intro h
      apply h_x_not_inits
      rw [Block.initVars]
      -- Stmt.initVars (.cmd _) is either [x'] or [], in either case x ∈ rhs ∪ Block.initVars rest
      cases c <;> simp [Stmt.initVars] <;> first | right; exact h | exact h
    exact h_preserve x h_σ_x h_x_not_new_accum h_x_not_rest_inits h_outer_guard
  | .ite (.det e) thenBranch elseBranch md :: rest =>
    unfold stmtsToBlocks at h_gen
    simp [bind, StateT.bind, pure, StateT.pure, List.append_nil] at h_gen
    -- Decompose the monadic h_gen into component computations
    generalize h_rest_eq : stmtsToBlocks k rest exitConts [] gen = r_rest at h_gen
    obtain ⟨⟨kNext, bsNext⟩, gen_r⟩ := r_rest
    simp at h_gen
    generalize h_ite_label : StringGenState.gen "ite" gen_r = r_ite at h_gen
    obtain ⟨l_ite, gen_ite⟩ := r_ite
    simp at h_gen
    generalize h_then_eq : stmtsToBlocks kNext thenBranch exitConts [] gen_ite = r_then at h_gen
    obtain ⟨⟨tl, tbs⟩, gen_t⟩ := r_then
    simp at h_gen
    generalize h_else_eq : stmtsToBlocks kNext elseBranch exitConts [] gen_t = r_else at h_gen
    obtain ⟨⟨fl, fbs⟩, gen_e⟩ := r_else
    simp at h_gen
    generalize h_flush_eq : flushCmds "ite$" accum
      (some (DetTransferCmd.condGoto e tl fl md)) l_ite gen_e = r_flush at h_gen
    obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
    have h_entry : accumEntry = entry := (Prod.mk.inj (Prod.mk.inj h_gen).1).1
    have h_blocks : accumBlocks ++ (tbs ++ (fbs ++ bsNext)) = blocks :=
      (Prod.mk.inj (Prod.mk.inj h_gen).1).2
    subst h_entry
    -- Decompose the structured execution of (ite :: rest)
    have ⟨ρ₁, h_ite_star, h_rest_star⟩ :=
      stmts_append_terminates P (EvalCmd P) extendEval
        [.ite (.det e) thenBranch elseBranch md] rest ρ₀ ρ'
        (by simp at h_term ⊢; exact h_term)
    -- Invert: the ite steps to either then-branch or else-branch
    have h_ite_inv : (StepStmtStar P (EvalCmd P) extendEval
          (.stmts thenBranch ρ₀) (.terminal ρ₁) ∧
          ρ₀.eval ρ₀.store e = .some HasBool.tt) ∨
        (StepStmtStar P (EvalCmd P) extendEval
          (.stmts elseBranch ρ₀) (.terminal ρ₁) ∧
          ρ₀.eval ρ₀.store e = .some HasBool.ff) := by
      cases h_ite_star with
      | step _ _ _ hstep1 hrest1 =>
        cases hstep1 with
        | step_stmts_cons =>
          have ⟨ρ_mid, h_inner, h_nil⟩ :=
            seq_reaches_terminal P (EvalCmd P) extendEval hrest1
          have h_eq := stmts_nil_terminal (EvalCmd P) extendEval _ _ h_nil
          subst h_eq
          cases h_inner with
          | step _ _ _ hstep2 hrest2 =>
            cases hstep2 with
            | step_ite_true h_eval_tt _ =>
              exact Or.inl ⟨hrest2, h_eval_tt⟩
            | step_ite_false h_eval_ff _ =>
              exact Or.inr ⟨hrest2, h_eval_ff⟩
    -- Block membership: distribute h_cfg_blocks over concatenated blocks
    subst h_blocks
    have h_cfg_accum : ∀ b ∈ accumBlocks, b ∈ cfg.blocks := fun b hb =>
      h_cfg_blocks b (List.mem_append_left _ hb)
    have h_cfg_tbs : ∀ b ∈ tbs, b ∈ cfg.blocks := fun b hb =>
      h_cfg_blocks b (List.mem_append_right _
        (List.mem_append_left _ hb))
    have h_cfg_fbs : ∀ b ∈ fbs, b ∈ cfg.blocks := fun b hb =>
      h_cfg_blocks b (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hb)))
    have h_cfg_rest : ∀ b ∈ bsNext, b ∈ cfg.blocks := fun b hb =>
      h_cfg_blocks b (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_right _ hb)))
    -- Extract noFuncDecl for sub-blocks from h_nofd
    have h_nofd_then : Block.noFuncDecl thenBranch = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.1.1
    have h_nofd_else : Block.noFuncDecl elseBranch = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.1.2
    have h_nofd_rest : Block.noFuncDecl rest = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.2
    -- Extract simpleShape for sub-blocks from h_simple
    have h_simple_head : Stmt.simpleShape (.ite (.det e) thenBranch elseBranch md) = true :=
      (Block.simpleShape_cons_iff.mp h_simple).1
    have h_simple_rest : Block.simpleShape rest = true :=
      (Block.simpleShape_cons_iff.mp h_simple).2
    -- Extract loopBodyNoInits / loopHasNoInvariants / noMeasureLoops for sub-blocks.
    have h_lbni_head : Stmt.loopBodyNoInits (.ite (.det e) thenBranch elseBranch md) = true :=
      (Block.loopBodyNoInits_cons_iff.mp h_lbni).1
    have h_lbni_rest : Block.loopBodyNoInits rest = true :=
      (Block.loopBodyNoInits_cons_iff.mp h_lbni).2
    have h_lhni_head : Stmt.loopHasNoInvariants (.ite (.det e) thenBranch elseBranch md) = true :=
      (Block.loopHasNoInvariants_cons_iff.mp h_lhni).1
    have h_lhni_rest : Block.loopHasNoInvariants rest = true :=
      (Block.loopHasNoInvariants_cons_iff.mp h_lhni).2
    have h_nml_head : Stmt.noMeasureLoops (.ite (.det e) thenBranch elseBranch md) = true :=
      (Block.noMeasureLoops_cons_iff.mp h_nml).1
    have h_nml_rest : Block.noMeasureLoops rest = true :=
      (Block.noMeasureLoops_cons_iff.mp h_nml).2
    obtain ⟨h_simple_then, h_simple_else, h_lbni_then, h_lbni_else,
            h_lhni_then, h_lhni_else, h_nml_then, h_nml_else⟩ :=
      ite_branch_shape h_simple_head h_lbni_head h_lhni_head h_nml_head
    -- Eval well-formedness preservation through ite branch
    have h_eval_eq : ρ₁.eval = ρ₀.eval := by
      rcases h_ite_inv with h | h
      · exact smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
          thenBranch ρ₀ ρ₁ h_nofd_then h.1
      · exact smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
          elseBranch ρ₀ ρ₁ h_nofd_else h.1
    have hwfb₁ : WellFormedSemanticEvalBool ρ₁.eval := h_eval_eq ▸ hwfb
    have hwfv₁ : WellFormedSemanticEvalVal ρ₁.eval := h_eval_eq ▸ hwfv
    have hwf_def₁ : WellFormedSemanticEvalDef ρ₁.eval := h_eval_eq ▸ hwf_def
    have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ₁.eval := h_eval_eq ▸ hwf_congr
    have hwf_var₁ : WellFormedSemanticEvalVar ρ₁.eval := h_eval_eq ▸ hwf_var
    have h_unique_then : Block.uniqueInits thenBranch :=
      Block.uniqueInits.ite_then h_unique
    have h_unique_else : Block.uniqueInits elseBranch :=
      Block.uniqueInits.ite_else h_unique
    have h_unique_rest : Block.uniqueInits rest := Block.uniqueInits.tail h_unique
    -- Lift accum to the CFG side via EvalCmds_under_agreement.
    -- This produces σ_cfg_after, the CFG store after running accum.
    have h_fresh_accum : ∀ x ∈ Cmds.definedVars accum.reverse, σ_base x = none := by
      intro x hx
      exact h_fresh_combined x (List.mem_append_left _ hx)
    have h_unique_accum : (Cmds.definedVars accum.reverse).Nodup :=
      (List.nodup_append.mp h_unique_combined).1
    have ⟨σ_cfg_after, h_accum_cfg, h_agree_after⟩ :=
      EvalCmds_under_agreement ρ₀.eval accum.reverse hwf_def hwf_congr
        σ_struct_base σ_base ρ₀.store hf_accum h_agree_entry h_accum h_fresh_accum
        h_unique_accum
    -- Freshness preservation through the lifted accum.
    have h_preserve_after :
        ∀ x, σ_base x = none → x ∉ Cmds.definedVars accum.reverse →
          σ_cfg_after x = none := by
      intro x h_σ h_x_not
      exact agreement_helper_unchanged_at_x_multi h_accum_cfg h_x_not h_σ
    -- Block.initVars decomposition: outer ss = .ite ... :: rest, so
    -- Block.initVars ss = Block.initVars tss ++ Block.initVars ess ++ Block.initVars rest
    have h_initvars_eq :
        Block.initVars (Stmt.ite (ExprOrNondet.det e) thenBranch elseBranch md :: rest) =
        (Block.initVars thenBranch ++ Block.initVars elseBranch) ++ Block.initVars rest := by
      rw [Block.initVars]
      simp
    have h_unique_outer_inits :
        (Cmds.definedVars accum.reverse ++
          ((Block.initVars thenBranch ++ Block.initVars elseBranch) ++ Block.initVars rest)).Nodup := by
      rw [← h_initvars_eq]; exact h_unique_combined
    -- Freshness for sub-branch and rest recursions.
    have h_fresh_then_inits : ∀ x ∈ Block.initVars thenBranch, σ_cfg_after x = none := by
      intro x hx
      have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := fun hx_acc =>
        (List.nodup_append.mp h_unique_outer_inits).2.2 x hx_acc x
          (List.mem_append_left _ (List.mem_append_left _ hx)) rfl
      have h_σ_x : σ_base x = none :=
        h_fresh_combined x (List.mem_append_right _
          (h_initvars_eq ▸ List.mem_append_left _ (List.mem_append_left _ hx)))
      exact h_preserve_after x h_σ_x h_x_not_accum
    have h_fresh_else_inits : ∀ x ∈ Block.initVars elseBranch, σ_cfg_after x = none := by
      intro x hx
      have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := fun hx_acc =>
        (List.nodup_append.mp h_unique_outer_inits).2.2 x hx_acc x
          (List.mem_append_left _ (List.mem_append_right _ hx)) rfl
      have h_σ_x : σ_base x = none :=
        h_fresh_combined x (List.mem_append_right _
          (h_initvars_eq ▸ List.mem_append_left _ (List.mem_append_right _ hx)))
      exact h_preserve_after x h_σ_x h_x_not_accum
    have h_fresh_rest_inits_after :
        ∀ x ∈ Block.initVars rest, σ_cfg_after x = none := by
      intro x hx
      have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := fun hx_acc =>
        (List.nodup_append.mp h_unique_outer_inits).2.2 x hx_acc x
          (List.mem_append_right _ hx) rfl
      have h_σ_x : σ_base x = none :=
        h_fresh_combined x (List.mem_append_right _
          (h_initvars_eq ▸ List.mem_append_right _ hx))
      exact h_preserve_after x h_σ_x h_x_not_accum
    -- Combined freshness for branch recursion (empty accum + branch's inits).
    have h_combined_then :
        ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars thenBranch,
        σ_cfg_after x = none :=
      fun x hx => h_fresh_then_inits x (by simpa [Cmds.definedVars] using hx)
    have h_unique_combined_ite := unique_combined_ite h_unique_outer_inits
    have h_unique_combined_then :
        (Cmds.definedVars [].reverse ++ Block.initVars thenBranch).Nodup :=
      h_unique_combined_ite.1
    have h_combined_else :
        ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars elseBranch,
        σ_cfg_after x = none :=
      fun x hx => h_fresh_else_inits x (by simpa [Cmds.definedVars] using hx)
    have h_unique_combined_else :
        (Cmds.definedVars [].reverse ++ Block.initVars elseBranch).Nodup :=
      h_unique_combined_ite.2.1
    -- Lookup helper for the condGoto helpers
    have h_lookup : ∀ lbl blk, (lbl, blk) ∈ cfg.blocks →
        cfg.blocks.lookup lbl = some blk :=
      fun lbl blk h_mem => List.lookup_of_mem_nodup cfg.blocks h_cfg_nodup lbl blk h_mem
    -- GenStep chains for WF and subset.
    have h_gen_eq_f : gen_f = gen' := (Prod.mk.inj h_gen).2
    have h_step_e_to_f : StringGenState.GenStep gen_e gen_f :=
      flushCmds_genStep _ _ _ _ _ _ _ _ h_flush_eq
    have h_step_t_to_e : StringGenState.GenStep gen_t gen_e :=
      stmtsToBlocks_genStep _ _ _ _ _ _ _ _ h_else_eq
    have h_step_ite_to_t : StringGenState.GenStep gen_ite gen_t :=
      stmtsToBlocks_genStep _ _ _ _ _ _ _ _ h_then_eq
    have h_step_r_to_ite : StringGenState.GenStep gen_r gen_ite := by
      have h_eq : (StringGenState.gen "ite" gen_r).2 = gen_ite := congrArg Prod.snd h_ite_label
      exact h_eq ▸ StringGenState.GenStep.of_gen "ite" gen_r
    have h_step_gen_to_r : StringGenState.GenStep gen gen_r :=
      stmtsToBlocks_genStep _ _ _ _ _ _ _ _ h_rest_eq
    have h_step_gen_to_ite : StringGenState.GenStep gen gen_ite :=
      h_step_gen_to_r.trans h_step_r_to_ite
    have h_step_gen_to_t : StringGenState.GenStep gen gen_t :=
      h_step_gen_to_ite.trans h_step_ite_to_t
    have h_step_gen_to_e : StringGenState.GenStep gen gen_e :=
      h_step_gen_to_t.trans h_step_t_to_e
    have h_wf_t : StringGenState.WF gen_t := h_step_gen_to_t.wf_mono h_wf_gen
    have h_wf_e : StringGenState.WF gen_e := h_step_gen_to_e.wf_mono h_wf_gen
    have h_wf_r : StringGenState.WF gen_r := h_step_gen_to_r.wf_mono h_wf_gen
    have h_wf_ite : StringGenState.WF gen_ite := h_step_gen_to_ite.wf_mono h_wf_gen
    -- Lift store-no-gens-upper to σ_cfg_after for the upper-bound form.
    have h_store_no_gens_upper_after :
        ∀ x : String, Q x →
          x ∉ StringGenState.stringGens genUpperBound →
          σ_cfg_after (HasIdent.ident (P := P) x) = none :=
      store_no_gens_lift_after_accum h_accum_cfg genUpperBound h_store_no_gens_upper
        (fun x hx => h_combined_no_gen_suffix x (List.mem_append_left _ hx))
    -- Subset chains lifting outer upper-bound to inner gen' subsets.
    have h_outer_upper_e : StringGenState.stringGens gen_e ⊆ StringGenState.stringGens genUpperBound :=
      h_step_e_to_f.subset.trans (h_gen_eq_f ▸ h_outer_upper)
    have h_outer_upper_t : StringGenState.stringGens gen_t ⊆ StringGenState.stringGens genUpperBound :=
      h_step_t_to_e.subset.trans h_outer_upper_e
    have h_outer_upper_r : StringGenState.stringGens gen_r ⊆ StringGenState.stringGens genUpperBound :=
      h_step_r_to_ite.subset.trans (h_step_ite_to_t.subset.trans h_outer_upper_t)
    -- Sub-branch and rest combined-no-gen-suffix discharges.
    have h_then_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars [].reverse ++ Block.initVars thenBranch) := fun x hx s heq =>
      h_combined_no_gen_suffix x (List.mem_append_right _ (h_initvars_eq ▸
        List.mem_append_left _ (List.mem_append_left _ (by simpa [Cmds.definedVars] using hx)))) s heq
    have h_else_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars [].reverse ++ Block.initVars elseBranch) := fun x hx s heq =>
      h_combined_no_gen_suffix x (List.mem_append_right _ (h_initvars_eq ▸
        List.mem_append_left _ (List.mem_append_right _ (by simpa [Cmds.definedVars] using hx)))) s heq
    have h_rest_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars [].reverse ++ Block.initVars rest) := fun x hx s heq =>
      h_combined_no_gen_suffix x (List.mem_append_right _ (h_initvars_eq ▸
        List.mem_append_right _ (by simpa [Cmds.definedVars] using hx))) s heq
    -- Mirror of h_initvars_eq / no_gen_suffix discharges for modifiedVars.
    have h_modvars_eq :
        transformBlockModVars (Stmt.ite (ExprOrNondet.det e) thenBranch elseBranch md :: rest) =
        (transformBlockModVars thenBranch ++ transformBlockModVars elseBranch) ++ transformBlockModVars rest := by
      rw [transformBlockModVars_cons, transformStmtModVars_ite]
    have h_then_no_gen_suffix_mod :
        NoGenSuffix (P := P) Q (Cmds.modifiedVars [].reverse ++ transformBlockModVars thenBranch) := fun x hx s heq =>
      h_combined_no_gen_suffix_mod x (List.mem_append_right _ (h_modvars_eq ▸
        List.mem_append_left _ (List.mem_append_left _ (by simpa [Cmds.modifiedVars] using hx)))) s heq
    have h_else_no_gen_suffix_mod :
        NoGenSuffix (P := P) Q (Cmds.modifiedVars [].reverse ++ transformBlockModVars elseBranch) := fun x hx s heq =>
      h_combined_no_gen_suffix_mod x (List.mem_append_right _ (h_modvars_eq ▸
        List.mem_append_left _ (List.mem_append_right _ (by simpa [Cmds.modifiedVars] using hx)))) s heq
    have h_rest_no_gen_suffix_mod :
        NoGenSuffix (P := P) Q (Cmds.modifiedVars [].reverse ++ transformBlockModVars rest) := fun x hx s heq =>
      h_combined_no_gen_suffix_mod x (List.mem_append_right _ (h_modvars_eq ▸
        List.mem_append_right _ (by simpa [Cmds.modifiedVars] using hx))) s heq
    rcases h_ite_inv with h_true | h_false
    · obtain ⟨h_then_term, h_cond_tt⟩ := h_true
      -- Step from accumEntry to tl via the lifted accum + condGoto.
      have h_flush_sim : StepDetCFGStar extendEval cfg
          (.atBlock accumEntry σ_base hf_base)
          (.atBlock tl σ_cfg_after ρ₀.hasFailure) :=
        flushCmds_condGoto_agree extendEval true accum e tl fl md l_ite gen_e gen_f
          accumEntry accumBlocks h_flush_eq σ_base σ_cfg_after hf_base hf_accum ρ₀
          hwfb hwf_def hwf_congr h_accum_cfg h_agree_after h_hf h_cond_tt cfg
          h_cfg_accum h_lookup
      -- Recurse on thenBranch.
      have h_accum_nil_t : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
          [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
      have ⟨σ_branch, h_then_step, h_agree_then, h_preserve_then⟩ :=
        stmtsToBlocks_simulation extendEval kNext thenBranch exitConts []
          gen_ite gen_t tl tbs h_then_eq h_nofd_then h_simple_then h_unique_then
          h_lbni_then h_lhni_then h_nml_then
          ρ₀.store σ_cfg_after ρ₀.hasFailure false
          ρ₀ ρ₁ hwfb hwfv hwf_def hwf_congr hwf_var
          h_then_term h_accum_nil_t h_agree_after
          h_combined_then h_unique_combined_then (by simp)
          h_wf_ite h_then_no_gen_suffix h_then_no_gen_suffix_mod
          genUpperBound h_outer_upper_t h_store_no_gens_upper_after h_foreign
          cfg h_cfg_tbs h_cfg_nodup
      -- Freshness of rest's inits at σ_branch.
      have h_fresh_rest_inits_branch :
          ∀ x ∈ Block.initVars rest, σ_branch x = none := by
        intro x hx
        have h_x_not_then : x ∉ Block.initVars thenBranch := by
          intro h_in_then
          have h1 : ((Block.initVars thenBranch ++ Block.initVars elseBranch) ++
                      Block.initVars rest).Nodup :=
            (List.nodup_append.mp h_unique_outer_inits).2.1
          have h_disj_lr := (List.nodup_append.mp h1).2.2
          have h_in_then_else : x ∈ Block.initVars thenBranch ++ Block.initVars elseBranch :=
            List.mem_append_left _ h_in_then
          exact h_disj_lr x h_in_then_else x hx rfl
        have h_σ_after_x : σ_cfg_after x = none := h_fresh_rest_inits_after x hx
        have : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
        exact h_preserve_then x h_σ_after_x this h_x_not_then
          (fun s heq => Or.inr
            (fun h_in => h_foreign s
              (h_rest_no_gen_suffix x (by simp [Cmds.definedVars]; exact hx) s heq)
              (h_outer_upper_t h_in)))
      -- Combined freshness for rest recursion.
      have h_combined_rest :
          ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
          σ_branch x = none := fun x hx =>
        h_fresh_rest_inits_branch x (by simpa [Cmds.definedVars] using hx)
      have h_unique_combined_rest :
          (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup :=
        (unique_combined_ite h_unique_outer_inits).2.2
      -- Recurse on rest.
      have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ₁.eval ρ₁.store
          [].reverse ρ₁.store false := EvalCmds.eval_cmds_none
      -- Lift `h_store_no_gens_upper` through the thenBranch sub-simulation
      -- using the strengthened (4-premise) `h_preserve_then` directly.
      have h_store_no_gens_upper_branch_t :
          ∀ x : String, Q x →
            x ∉ StringGenState.stringGens genUpperBound →
            σ_branch (HasIdent.ident (P := P) x) = none :=
        store_no_gens_upper_lift_through_subsim gen_ite gen_t genUpperBound
          h_outer_upper_t h_preserve_then h_store_no_gens_upper_after
          (fun x hx s heq => h_then_no_gen_suffix x (List.mem_append_right _ hx) s heq)
      have ⟨σ_cfg, h_rest_sim, h_agree_rest, h_preserve_rest⟩ :=
        stmtsToBlocks_simulation extendEval k rest exitConts [] gen gen_r kNext bsNext
          h_rest_eq h_nofd_rest h_simple_rest h_unique_rest
          h_lbni_rest h_lhni_rest h_nml_rest
          ρ₁.store σ_branch ρ₁.hasFailure false
          ρ₁ ρ' hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁ hwf_var₁
          h_rest_star h_accum_nil_r h_agree_then
          h_combined_rest h_unique_combined_rest (by simp)
          h_wf_gen h_rest_no_gen_suffix h_rest_no_gen_suffix_mod
          genUpperBound h_outer_upper_r h_store_no_gens_upper_branch_t h_foreign
          cfg h_cfg_rest h_cfg_nodup
      refine ⟨σ_cfg, ?_, h_agree_rest, ?_⟩
      · exact StepDetCFGStar_trans
          (StepDetCFGStar_trans h_flush_sim h_then_step) h_rest_sim
      · -- Freshness preservation for the outer call.
        intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
        -- Decompose h_x_not_inits: x ∉ Block.initVars (.ite ... :: rest)
        --   = x ∉ Block.initVars tss ∧ x ∉ Block.initVars ess ∧ x ∉ Block.initVars rest
        have h_x_not_then : x ∉ Block.initVars thenBranch := fun hx =>
          h_x_not_inits (h_initvars_eq ▸ List.mem_append_left _ (List.mem_append_left _ hx))
        have h_x_not_else : x ∉ Block.initVars elseBranch := fun hx =>
          h_x_not_inits (h_initvars_eq ▸ List.mem_append_left _ (List.mem_append_right _ hx))
        have h_x_not_rest : x ∉ Block.initVars rest := fun hx =>
          h_x_not_inits (h_initvars_eq ▸ List.mem_append_right _ hx)
        have h_σ_after_x : σ_cfg_after x = none := h_preserve_after x h_σ_x h_x_not_accum
        have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
        -- Build inner guards from the outer guard via GenStep monotonicity.
        -- Chain: gen → gen_r → gen_ite → gen_t → gen_e → gen_f = gen'.
        have h_inner_guard_t : ∀ s : String, x = HasIdent.ident (P := P) s →
            s ∈ StringGenState.stringGens gen_ite ∨
            s ∉ StringGenState.stringGens gen_t :=
          fun s heq => match h_outer_guard s heq with
          | Or.inl h_in => Or.inl (h_step_gen_to_ite.subset h_in)
          | Or.inr h_not_in => Or.inr
              (fun h_in_t => h_not_in
                (h_gen_eq_f ▸ h_step_e_to_f.subset (h_step_t_to_e.subset h_in_t)))
        have h_inner_guard_r : ∀ s : String, x = HasIdent.ident (P := P) s →
            s ∈ StringGenState.stringGens gen ∨
            s ∉ StringGenState.stringGens gen_r :=
          fun s heq => match h_outer_guard s heq with
          | Or.inl h_in => Or.inl h_in
          | Or.inr h_not_in => Or.inr (fun h_in_r => h_not_in
              (h_gen_eq_f ▸ h_step_e_to_f.subset (h_step_t_to_e.subset
                (h_step_ite_to_t.subset (h_step_r_to_ite.subset h_in_r)))))
        have h_σ_branch_x : σ_branch x = none :=
          h_preserve_then x h_σ_after_x h_nil_not h_x_not_then h_inner_guard_t
        exact h_preserve_rest x h_σ_branch_x h_nil_not h_x_not_rest h_inner_guard_r
    · obtain ⟨h_else_term, h_cond_ff⟩ := h_false
      -- Step from accumEntry to fl via the lifted accum + condGoto.
      have h_flush_sim : StepDetCFGStar extendEval cfg
          (.atBlock accumEntry σ_base hf_base)
          (.atBlock fl σ_cfg_after ρ₀.hasFailure) :=
        flushCmds_condGoto_agree extendEval false accum e tl fl md l_ite gen_e gen_f
          accumEntry accumBlocks h_flush_eq σ_base σ_cfg_after hf_base hf_accum ρ₀
          hwfb hwf_def hwf_congr h_accum_cfg h_agree_after h_hf h_cond_ff cfg
          h_cfg_accum h_lookup
      -- Recurse on elseBranch.
      have h_accum_nil_f : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
          [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
      have ⟨σ_branch, h_else_step, h_agree_else, h_preserve_else⟩ :=
        stmtsToBlocks_simulation extendEval kNext elseBranch exitConts []
          gen_t gen_e fl fbs h_else_eq h_nofd_else h_simple_else h_unique_else
          h_lbni_else h_lhni_else h_nml_else
          ρ₀.store σ_cfg_after ρ₀.hasFailure false
          ρ₀ ρ₁ hwfb hwfv hwf_def hwf_congr hwf_var
          h_else_term h_accum_nil_f h_agree_after
          h_combined_else h_unique_combined_else (by simp)
          h_wf_t h_else_no_gen_suffix h_else_no_gen_suffix_mod
          genUpperBound h_outer_upper_e h_store_no_gens_upper_after h_foreign
          cfg h_cfg_fbs h_cfg_nodup
      -- Freshness of rest's inits at σ_branch.
      have h_fresh_rest_inits_branch :
          ∀ x ∈ Block.initVars rest, σ_branch x = none := by
        intro x hx
        have h_x_not_else : x ∉ Block.initVars elseBranch := by
          intro h_in_else
          have h1 : ((Block.initVars thenBranch ++ Block.initVars elseBranch) ++
                      Block.initVars rest).Nodup :=
            (List.nodup_append.mp h_unique_outer_inits).2.1
          have h_disj_lr := (List.nodup_append.mp h1).2.2
          have h_in_then_else : x ∈ Block.initVars thenBranch ++ Block.initVars elseBranch :=
            List.mem_append_right _ h_in_else
          exact h_disj_lr x h_in_then_else x hx rfl
        have h_σ_after_x : σ_cfg_after x = none := h_fresh_rest_inits_after x hx
        have : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
        exact h_preserve_else x h_σ_after_x this h_x_not_else
          (fun s heq => Or.inr
            (fun h_in => h_foreign s
              (h_rest_no_gen_suffix x (by simp [Cmds.definedVars]; exact hx) s heq)
              (h_outer_upper_e h_in)))
      -- Combined freshness for rest recursion.
      have h_combined_rest :
          ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
          σ_branch x = none := fun x hx =>
        h_fresh_rest_inits_branch x (by simpa [Cmds.definedVars] using hx)
      have h_unique_combined_rest :
          (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup :=
        (unique_combined_ite h_unique_outer_inits).2.2
      -- Recurse on rest.
      have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ₁.eval ρ₁.store
          [].reverse ρ₁.store false := EvalCmds.eval_cmds_none
      -- Lift `h_store_no_gens_upper` through the elseBranch sub-simulation
      -- using the strengthened (4-premise) `h_preserve_else` directly.
      have h_store_no_gens_upper_branch_e :
          ∀ x : String, Q x →
            x ∉ StringGenState.stringGens genUpperBound →
            σ_branch (HasIdent.ident (P := P) x) = none :=
        store_no_gens_upper_lift_through_subsim gen_t gen_e genUpperBound
          h_outer_upper_e h_preserve_else h_store_no_gens_upper_after
          (fun x hx s heq => h_else_no_gen_suffix x (List.mem_append_right _ hx) s heq)
      have ⟨σ_cfg, h_rest_sim, h_agree_rest, h_preserve_rest⟩ :=
        stmtsToBlocks_simulation extendEval k rest exitConts [] gen gen_r kNext bsNext
          h_rest_eq h_nofd_rest h_simple_rest h_unique_rest
          h_lbni_rest h_lhni_rest h_nml_rest
          ρ₁.store σ_branch ρ₁.hasFailure false
          ρ₁ ρ' hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁ hwf_var₁
          h_rest_star h_accum_nil_r h_agree_else
          h_combined_rest h_unique_combined_rest (by simp)
          h_wf_gen h_rest_no_gen_suffix h_rest_no_gen_suffix_mod
          genUpperBound h_outer_upper_r h_store_no_gens_upper_branch_e h_foreign
          cfg h_cfg_rest h_cfg_nodup
      refine ⟨σ_cfg, ?_, h_agree_rest, ?_⟩
      · exact StepDetCFGStar_trans
          (StepDetCFGStar_trans h_flush_sim h_else_step) h_rest_sim
      · intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
        have h_x_not_else : x ∉ Block.initVars elseBranch := fun hx =>
          h_x_not_inits (h_initvars_eq ▸ List.mem_append_left _ (List.mem_append_right _ hx))
        have h_x_not_rest : x ∉ Block.initVars rest := fun hx =>
          h_x_not_inits (h_initvars_eq ▸ List.mem_append_right _ hx)
        have h_σ_after_x : σ_cfg_after x = none := h_preserve_after x h_σ_x h_x_not_accum
        have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
        -- Build inner guards from outer guard via GenStep monotonicity.
        -- Chain: gen → gen_r → gen_ite → gen_t → gen_e → gen_f = gen'.
        have h_inner_guard_e : ∀ s : String, x = HasIdent.ident (P := P) s →
            s ∈ StringGenState.stringGens gen_t ∨
            s ∉ StringGenState.stringGens gen_e :=
          fun s heq => match h_outer_guard s heq with
          | Or.inl h_in => Or.inl (h_step_gen_to_t.subset h_in)
          | Or.inr h_not_in => Or.inr (fun h_in_e => h_not_in
              (h_gen_eq_f ▸ h_step_e_to_f.subset h_in_e))
        have h_inner_guard_r : ∀ s : String, x = HasIdent.ident (P := P) s →
            s ∈ StringGenState.stringGens gen ∨
            s ∉ StringGenState.stringGens gen_r :=
          fun s heq => match h_outer_guard s heq with
          | Or.inl h_in => Or.inl h_in
          | Or.inr h_not_in => Or.inr (fun h_in_r => h_not_in
              (h_gen_eq_f ▸ h_step_e_to_f.subset (h_step_t_to_e.subset
                (h_step_ite_to_t.subset (h_step_r_to_ite.subset h_in_r)))))
        have h_σ_branch_x : σ_branch x = none :=
          h_preserve_else x h_σ_after_x h_nil_not h_x_not_else h_inner_guard_e
        exact h_preserve_rest x h_σ_branch_x h_nil_not h_x_not_rest h_inner_guard_r
  | .ite .nondet _ _ _ :: _ =>
    exact absurd (Block.simpleShape_cons_iff.mp h_simple).1 (by simp [Stmt.simpleShape])
  | .loop guard measure invariants body md :: rest =>
    -- Subdispatch on guard: .nondet is excluded by strengthened simpleShape.
    -- Only `.det _` reaches the main proof.
    have h_simple_head : Stmt.simpleShape (.loop guard measure invariants body md) = true :=
      (Block.simpleShape_cons_iff.mp h_simple).1
    have ⟨guardExpr, hg_eq⟩ : ∃ ge, guard = .det ge :=
      Stmt.simpleShape_loop_guard_det h_simple_head
    subst hg_eq
    -- Subdispatch on measure: only `.none` is admitted by noMeasureLoops.
    have h_nml_head : Stmt.noMeasureLoops (.loop (.det guardExpr) measure invariants body md) = true :=
      (Block.noMeasureLoops_cons_iff.mp h_nml).1
    have h_measure_none : measure = .none := by
      simp only [Stmt.noMeasureLoops, Bool.and_eq_true, Option.isNone_iff_eq_none] at h_nml_head
      exact h_nml_head.1
    subst h_measure_none
    -- Subdispatch on invariants: only `[]` is admitted by loopHasNoInvariants.
    have h_lhni_head : Stmt.loopHasNoInvariants
        (.loop (.det guardExpr) (none : Option P.Expr) invariants body md) = true :=
      (Block.loopHasNoInvariants_cons_iff.mp h_lhni).1
    have h_invs_nil : invariants = [] :=
      Stmt.loopHasNoInvariants_loop_invs h_lhni_head
    subst h_invs_nil
    -- Now we have `.loop (.det guardExpr) none [] body md :: rest` to handle.
    -- === STEP 1: Decompose h_gen. ===
    obtain ⟨kNext, lentry, bl, bbs, bsRest, accumEntry, accumBlocks,
           gen_r, gen_le, gen_b, gen_f,
           h_rest_eq, h_le_eq, h_body_eq, h_flush_eq, h_gen_eq, h_entry_eq, h_blocks_eq⟩ :=
      InlineLoopHelpers.loop_det_decompose_h_gen k gen gen' entry blocks accum
        guardExpr body md exitConts rest h_gen
    -- === STEP 2: Project sub-block preconditions. ===
    have h_body_no_inits : Block.initVars body = [] :=
      Stmt.loopBodyNoInits_loop_body ((Block.loopBodyNoInits_cons_iff.mp h_lbni).1)
    have h_nofd_body : Block.noFuncDecl body = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.1
    have h_nofd_rest : Block.noFuncDecl rest = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.2
    have h_simple_body : Block.simpleShape body = true :=
      Stmt.simpleShape_loop_body h_simple_head
    have h_simple_rest : Block.simpleShape rest = true :=
      (Block.simpleShape_cons_iff.mp h_simple).2
    have h_unique_body : Block.uniqueInits body := by
      have h := Block.uniqueInits.head_stmt h_unique
      simp only [Stmt.initVars] at h; exact h
    have h_unique_rest : Block.uniqueInits rest := Block.uniqueInits.tail h_unique
    have h_lbni_body : Block.loopBodyNoInits body = true :=
      Stmt.loopBodyNoInits_loop_body_rec ((Block.loopBodyNoInits_cons_iff.mp h_lbni).1)
    have h_lbni_rest : Block.loopBodyNoInits rest = true :=
      (Block.loopBodyNoInits_cons_iff.mp h_lbni).2
    have h_lhni_body : Block.loopHasNoInvariants body = true :=
      Stmt.loopHasNoInvariants_loop_body_rec h_lhni_head
    have h_lhni_rest : Block.loopHasNoInvariants rest = true :=
      (Block.loopHasNoInvariants_cons_iff.mp h_lhni).2
    have h_nml_body : Block.noMeasureLoops body = true :=
      Stmt.noMeasureLoops_loop_body_rec h_nml_head
    have h_nml_rest : Block.noMeasureLoops rest = true :=
      (Block.noMeasureLoops_cons_iff.mp h_nml).2
    -- Block.initVars (.loop ... :: rest) = Block.initVars rest (since body has no inits).
    have h_initvars_eq :
        Block.initVars (Stmt.loop (.det guardExpr) none [] body md :: rest) =
        Block.initVars rest := by
      rw [Block.initVars]; simp only [Stmt.initVars, h_body_no_inits, List.nil_append]
    -- === STEP 3: Split h_term into loop run + rest run. ===
    have ⟨ρ_loop_post, h_loop_term, h_rest_term⟩ :=
      stmts_append_terminates P (EvalCmd P) extendEval
        [.loop (.det guardExpr) none [] body md] rest ρ₀ ρ'
        (by simpa using h_term)
    -- Convert loop run from `.stmts [loop]` to `.stmt loop`.
    have h_loop_stmt : StepStmtStar P (EvalCmd P) extendEval
        (.stmt (Stmt.loop (.det guardExpr) none [] body md) ρ₀) (.terminal ρ_loop_post) := by
      cases h_loop_term with
      | step _ _ _ hstep1 hrest1 =>
        cases hstep1 with
        | step_stmts_cons =>
          have ⟨ρ_mid, h_inner, h_nil2⟩ := seq_reaches_terminal P (EvalCmd P) extendEval hrest1
          have h_eq := stmts_nil_terminal (EvalCmd P) extendEval _ _ h_nil2
          subst h_eq; exact h_inner
    -- === STEP 3b: GenStep chain  gen → gen_r → gen_le → gen_b → gen_f = gen'. ===
    subst h_entry_eq
    subst h_gen_eq
    have h_step_gen_to_r : StringGenState.GenStep gen gen_r :=
      stmtsToBlocks_genStep _ _ _ _ _ _ _ _ h_rest_eq
    have h_step_r_to_le : StringGenState.GenStep gen_r gen_le := by
      rw [show gen_le = (StringGenState.gen "loop_entry$" gen_r).2 from (by rw [h_le_eq])]
      exact StringGenState.GenStep.of_gen "loop_entry$" gen_r
    have h_step_le_to_b : StringGenState.GenStep gen_le gen_b :=
      stmtsToBlocks_genStep _ _ _ _ _ _ _ _ h_body_eq
    have h_step_b_to_f : StringGenState.GenStep gen_b gen_f :=
      flushCmds_genStep _ _ _ _ _ _ _ _ h_flush_eq
    have h_step_gen_to_le : StringGenState.GenStep gen gen_le := h_step_gen_to_r.trans h_step_r_to_le
    have h_step_gen_to_b : StringGenState.GenStep gen gen_b := h_step_gen_to_le.trans h_step_le_to_b
    have h_wf_r : StringGenState.WF gen_r := h_step_gen_to_r.wf_mono h_wf_gen
    have h_wf_le : StringGenState.WF gen_le := h_step_gen_to_le.wf_mono h_wf_gen
    have h_wf_b : StringGenState.WF gen_b := h_step_gen_to_b.wf_mono h_wf_gen
    have h_outer_upper_b : StringGenState.stringGens gen_b ⊆ StringGenState.stringGens genUpperBound :=
      h_step_b_to_f.subset.trans h_outer_upper
    have h_outer_upper_le : StringGenState.stringGens gen_le ⊆ StringGenState.stringGens genUpperBound :=
      h_step_le_to_b.subset.trans h_outer_upper_b
    have h_outer_upper_r : StringGenState.stringGens gen_r ⊆ StringGenState.stringGens genUpperBound :=
      h_step_r_to_le.subset.trans h_outer_upper_le
    -- === STEP 3c: Block-list membership distribution. ===
    -- blocks = accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ bsRest.
    let lentryBlk : DetBlock String (Cmd P) P :=
      { cmds := ([] : List (Cmd P)), transfer := DetTransferCmd.condGoto guardExpr bl kNext md }
    have h_blocks_full :
        accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ bsRest = blocks := h_blocks_eq
    subst h_blocks_full
    have h_cfg_accum : ∀ b ∈ accumBlocks, b ∈ cfg.blocks := fun b hb =>
      h_cfg_blocks b (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hb)))
    have h_cfg_lentry : (lentry, lentryBlk) ∈ cfg.blocks :=
      h_cfg_blocks _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.Mem.head _))))
    have h_cfg_bbs : ∀ b ∈ bbs, b ∈ cfg.blocks := fun b hb =>
      h_cfg_blocks b (List.mem_append_left _ (List.mem_append_right _ hb))
    have h_cfg_bsRest : ∀ b ∈ bsRest, b ∈ cfg.blocks := fun b hb =>
      h_cfg_blocks b (List.mem_append_right _ hb)
    have h_lentry_lkp : cfg.blocks.lookup lentry = some lentryBlk :=
      List.lookup_of_mem_nodup cfg.blocks h_cfg_nodup _ _ h_cfg_lentry
    -- === STEP 4: Lift accum to CFG (accumEntry → lentry). ===
    have h_fresh_accum : ∀ x ∈ Cmds.definedVars accum.reverse, σ_base x = none := fun x hx =>
      h_fresh_combined x (List.mem_append_left _ hx)
    have h_unique_accum : (Cmds.definedVars accum.reverse).Nodup :=
      (List.nodup_append.mp h_unique_combined).1
    have ⟨σ_cfg_after, h_step_flush, h_agree_after, h_preserve_flush⟩ :=
      flushCmds_simulation_agree extendEval "before_loop$" lentry accum gen_b gen_f
        accumEntry accumBlocks h_flush_eq σ_struct_base σ_base hf_base hf_accum ρ₀
        hwfb hwfv hwf_def hwf_congr h_accum h_agree_entry h_fresh_accum h_unique_accum
        h_hf cfg h_cfg_accum h_cfg_nodup
    -- === STEP 5: no-gen-suffix discharges for body and rest. ===
    -- Block.initVars (.loop... :: rest) = Block.initVars rest, so the loop arm's
    -- defined-vars list is rest's.  body's defined-vars list is empty.
    have h_body_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars [].reverse ++ Block.initVars body) := by
      rw [h_body_no_inits]; intro x hx; simp [Cmds.definedVars] at hx
    have h_rest_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars [].reverse ++ Block.initVars rest) := fun x hx s heq =>
      h_combined_no_gen_suffix x (List.mem_append_right _ (h_initvars_eq ▸
        (by simpa [Cmds.definedVars] using hx))) s heq
    have h_body_no_gen_suffix_mod :
        NoGenSuffix (P := P) Q (Cmds.modifiedVars [].reverse ++ transformBlockModVars body) :=
      fun x hx s heq => h_combined_no_gen_suffix_mod x
        (List.mem_append_right _ (by
          rw [transformBlockModVars_cons, transformStmtModVars_loop]
          exact List.mem_append_left _ (by simpa [Cmds.modifiedVars] using hx))) s heq
    -- The store invariant threaded through the loop preserves freshness (relative
    -- to σ_cfg_after) for any var satisfying the body's gen-guard `P_keep`.  Both
    -- rest's inits and the outer-call's fresh var satisfy `P_keep`.
    let P_keep : P.Ident → Prop := fun x =>
      ∀ s : String, x = HasIdent.ident (P := P) s →
        s ∈ StringGenState.stringGens gen_le ∨ s ∉ StringGenState.stringGens gen_b
    let storeInv : SemanticStore P → Prop := fun σ =>
      ∀ x, P_keep x → σ_cfg_after x = none → σ x = none
    have h_inv_after : storeInv σ_cfg_after := fun x _ h => h
    -- === STEP 6: Build the body-sim oracle (recurse on body). ===
    have h_body_sim_at :
        ∀ (ρ_iter : Env P) (σ_cfg_iter : SemanticStore P),
          ρ_iter.eval = ρ₀.eval →
          StoreAgreement ρ_iter.store σ_cfg_iter →
          storeInv σ_cfg_iter →
          ∀ (ρ_body : Env P), StepStmtStar P (EvalCmd P) extendEval
              (.stmts body ρ_iter) (.terminal ρ_body) →
            ∃ σ_cfg_after_body,
              StepDetCFGStar extendEval cfg
                (.atBlock bl σ_cfg_iter ρ_iter.hasFailure)
                (.atBlock lentry σ_cfg_after_body ρ_body.hasFailure) ∧
              StoreAgreement ρ_body.store σ_cfg_after_body ∧
              storeInv σ_cfg_after_body := by
      intro ρ_iter σ_cfg_iter h_eval_iter h_agree_iter h_inv_iter ρ_body h_body_run
      -- WF facts on ρ_iter.eval lifted from ρ₀.eval.
      have hwfb_iter : WellFormedSemanticEvalBool ρ_iter.eval := h_eval_iter ▸ hwfb
      have hwfv_iter : WellFormedSemanticEvalVal ρ_iter.eval := h_eval_iter ▸ hwfv
      have hwf_def_iter : WellFormedSemanticEvalDef ρ_iter.eval := h_eval_iter ▸ hwf_def
      have hwf_congr_iter : WellFormedSemanticEvalExprCongr ρ_iter.eval := h_eval_iter ▸ hwf_congr
      have hwf_var_iter : WellFormedSemanticEvalVar ρ_iter.eval := h_eval_iter ▸ hwf_var
      have h_combined_body : ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
          σ_cfg_iter x = none := by
        intro x hx; rw [h_body_no_inits] at hx; simp [Cmds.definedVars] at hx
      have h_unique_combined_body : (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
        rw [h_body_no_inits]; simp [Cmds.definedVars]
      have h_accum_nil : EvalCmds P (EvalCmd P) ρ_iter.eval ρ_iter.store
          [].reverse ρ_iter.store false := EvalCmds.eval_cmds_none
      have h_hf_iter : ρ_iter.hasFailure = (ρ_iter.hasFailure || false) := by simp
      -- The body sim needs its own store-no-gens at gen_b's upper-bound.  We use the
      -- bound `gen_b` itself: any gen-suffix var outside gen_b's gens that's fresh at
      -- σ_cfg_after stays fresh at σ_cfg_iter (storeInv), hence fresh.  But we need it
      -- at arbitrary gen-suffix x ∉ genUpperBound.  Such x satisfy P_keep (s ∉ gen_b
      -- because gen_b ⊆ genUpperBound), and are fresh at σ_cfg_after (store_no_gens),
      -- so storeInv gives σ_cfg_iter freshness.
      have h_sng_iter : ∀ x : String, Q x →
          x ∉ StringGenState.stringGens genUpperBound →
          σ_cfg_iter (HasIdent.ident (P := P) x) = none := by
        intro x hx_sfx hx_notin
        have h_keep : P_keep (HasIdent.ident (P := P) x) := by
          intro s heq
          have hs_eq : x = s := LawfulHasIdent.ident_inj heq
          subst hs_eq
          exact Or.inr (fun h_in_b => hx_notin (h_outer_upper_b h_in_b))
        have h_after_x : σ_cfg_after (HasIdent.ident (P := P) x) = none := by
          have := store_no_gens_lift_after_flush h_preserve_flush genUpperBound h_store_no_gens_upper
            (fun y hy => h_combined_no_gen_suffix y (List.mem_append_left _ hy))
          exact this x hx_sfx hx_notin
        exact h_inv_iter _ h_keep h_after_x
      -- Recurse on body.  body's k = lentry, exitConts = (.none, kNext) :: exitConts,
      -- entry = bl, gen = gen_le, gen' = gen_b.
      have ⟨σ_cfg_after_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
        stmtsToBlocks_simulation extendEval lentry body ((.none, kNext) :: exitConts) []
          gen_le gen_b bl bbs h_body_eq h_nofd_body h_simple_body h_unique_body
          h_lbni_body h_lhni_body h_nml_body
          ρ_iter.store σ_cfg_iter ρ_iter.hasFailure false
          ρ_iter ρ_body hwfb_iter hwfv_iter hwf_def_iter hwf_congr_iter hwf_var_iter
          h_body_run h_accum_nil h_agree_iter
          h_combined_body h_unique_combined_body h_hf_iter
          h_wf_le h_body_no_gen_suffix h_body_no_gen_suffix_mod
          genUpperBound h_outer_upper_b h_sng_iter h_foreign
          cfg h_cfg_bbs h_cfg_nodup
      refine ⟨σ_cfg_after_body, h_step_body, h_agree_body, ?_⟩
      -- storeInv preserved: for x with P_keep and σ_cfg_after x = none, derive
      -- σ_cfg_after_body x = none from σ_cfg_iter x = none (via storeInv) + body preserve.
      intro x h_keep h_after_x
      have h_iter_x : σ_cfg_iter x = none := h_inv_iter x h_keep h_after_x
      have h_nil_not : x ∉ Cmds.definedVars ([] : List (Cmd P)).reverse := by simp [Cmds.definedVars]
      have h_not_body : x ∉ Block.initVars body := by rw [h_body_no_inits]; simp
      exact h_preserve_body x h_iter_x h_nil_not h_not_body h_keep
    -- store-no-gens at σ_cfg_after (after the flush), reused below.
    have h_store_no_gens_upper_after :
        ∀ x : String, Q x →
          x ∉ StringGenState.stringGens genUpperBound →
          σ_cfg_after (HasIdent.ident (P := P) x) = none :=
      store_no_gens_lift_after_flush h_preserve_flush genUpperBound h_store_no_gens_upper
        (fun y hy => h_combined_no_gen_suffix y (List.mem_append_left _ hy))
    have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none := by
      intro x hx
      have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := fun h_in_accum =>
        (List.nodup_append.mp (h_initvars_eq ▸ h_unique_combined)).2.2 x h_in_accum x hx rfl
      have h_σ_base_x : σ_base x = none :=
        h_fresh_combined x (h_initvars_eq ▸ List.mem_append_right _ hx)
      exact h_preserve_flush x h_σ_base_x h_x_not_accum
    -- === STEP 7: Iterate the loop (lentry → kNext). ===
    have ⟨σ_cfg_kNext, h_loop_run, h_agree_loop, h_inv_loop⟩ :=
      InlineLoopHelpers.loop_iterations_det extendEval guardExpr body md ρ₀ ρ_loop_post
        cfg lentry kNext bl σ_cfg_after storeInv h_lentry_lkp h_agree_after h_inv_after
        h_loop_stmt h_nofd_body h_body_sim_at
        hwfb hwf_def hwf_congr
    -- Recover store-no-gens and rest-freshness at σ_cfg_kNext from storeInv.
    have h_sng_loop : ∀ x : String, Q x →
        x ∉ StringGenState.stringGens genUpperBound →
        σ_cfg_kNext (HasIdent.ident (P := P) x) = none := by
      intro x hx_sfx hx_notin
      have h_keep : P_keep (HasIdent.ident (P := P) x) := by
        intro s heq
        have hs_eq : x = s := LawfulHasIdent.ident_inj heq
        subst hs_eq
        exact Or.inr (fun h_in_b => hx_notin (h_outer_upper_b h_in_b))
      exact h_inv_loop _ h_keep (h_store_no_gens_upper_after x hx_sfx hx_notin)
    have h_fresh_rest_loop : ∀ x ∈ Block.initVars rest, σ_cfg_kNext x = none := by
      intro x hx
      have h_keep : P_keep x := by
        intro s heq
        exact Or.inr (fun h_in_b =>
          h_foreign s
            (h_rest_no_gen_suffix x (by simpa [Cmds.definedVars] using hx) s heq)
            (h_outer_upper_b h_in_b))
      exact h_inv_loop x h_keep (h_fresh_rest_inits_after x hx)
    -- ρ_loop_post.eval = ρ₀.eval (loop body has no funcDecls).
    have h_eval_loop : ρ_loop_post.eval = ρ₀.eval :=
      smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
        [.loop (.det guardExpr) none [] body md] ρ₀ ρ_loop_post
        (by simp [Block.noFuncDecl, Stmt.noFuncDecl, h_nofd_body])
        (by simpa using h_loop_term)
    have hwfb_loop : WellFormedSemanticEvalBool ρ_loop_post.eval := h_eval_loop ▸ hwfb
    have hwfv_loop : WellFormedSemanticEvalVal ρ_loop_post.eval := h_eval_loop ▸ hwfv
    have hwf_def_loop : WellFormedSemanticEvalDef ρ_loop_post.eval := h_eval_loop ▸ hwf_def
    have hwf_congr_loop : WellFormedSemanticEvalExprCongr ρ_loop_post.eval := h_eval_loop ▸ hwf_congr
    have hwf_var_loop : WellFormedSemanticEvalVar ρ_loop_post.eval := h_eval_loop ▸ hwf_var
    -- === STEP 8: Recurse on rest (kNext → k). ===
    have h_combined_rest : ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
        σ_cfg_kNext x = none := fun x hx =>
      h_fresh_rest_loop x (by simpa [Cmds.definedVars] using hx)
    have h_unique_combined_rest : (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
      simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_rest
    have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_loop_post.eval ρ_loop_post.store
        [].reverse ρ_loop_post.store false := EvalCmds.eval_cmds_none
    have h_hf_loop : ρ_loop_post.hasFailure = (ρ_loop_post.hasFailure || false) := by simp
    have h_rest_no_gen_suffix_mod :
        NoGenSuffix (P := P) Q (Cmds.modifiedVars [].reverse ++ transformBlockModVars rest) :=
      fun x hx s heq => h_combined_no_gen_suffix_mod x
        (List.mem_append_right _ (by
          rw [transformBlockModVars_cons, transformStmtModVars_loop]
          exact List.mem_append_right _ (by simpa [Cmds.modifiedVars] using hx))) s heq
    have ⟨σ_cfg, h_rest_sim, h_agree_rest, h_preserve_rest⟩ :=
      stmtsToBlocks_simulation extendEval k rest exitConts [] gen gen_r kNext bsRest
        h_rest_eq h_nofd_rest h_simple_rest h_unique_rest
        h_lbni_rest h_lhni_rest h_nml_rest
        ρ_loop_post.store σ_cfg_kNext ρ_loop_post.hasFailure false
        ρ_loop_post ρ' hwfb_loop hwfv_loop hwf_def_loop hwf_congr_loop hwf_var_loop
        h_rest_term h_accum_nil_r h_agree_loop
        h_combined_rest h_unique_combined_rest h_hf_loop
        h_wf_gen h_rest_no_gen_suffix h_rest_no_gen_suffix_mod
        genUpperBound h_outer_upper_r h_sng_loop h_foreign
        cfg h_cfg_bsRest h_cfg_nodup
    -- === STEP 9: Compose and discharge. ===
    refine ⟨σ_cfg, ?_, h_agree_rest, ?_⟩
    · exact StepDetCFGStar_trans (StepDetCFGStar_trans h_step_flush h_loop_run) h_rest_sim
    · -- Freshness preservation for the outer call.
      intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
      -- x ∉ Block.initVars (.loop ... :: rest) = Block.initVars rest.
      have h_x_not_rest : x ∉ Block.initVars rest := fun hx =>
        h_x_not_inits (h_initvars_eq ▸ hx)
      have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
      have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
      -- x satisfies P_keep: the outer guard gives s ∈ gens gen ∨ s ∉ gens gen'.
      -- gen ⊆ gen_le (so s ∈ gen → s ∈ gen_le), and gen_b ⊆ gen' = gen_f (so
      -- s ∉ gen' → s ∉ gen_b).  Hence the body's gen-guard `s ∈ gen_le ∨ s ∉ gen_b`.
      have h_keep : P_keep x := by
        intro s heq
        rcases h_outer_guard s heq with h_in_gen | h_notin_gen'
        · exact Or.inl (h_step_gen_to_le.subset h_in_gen)
        · exact Or.inr (fun h_in_b => h_notin_gen' (h_step_b_to_f.subset h_in_b))
      -- The loop preserves x's freshness (storeInv applied to σ_cfg_kNext).
      have h_x_fresh_loop : σ_cfg_kNext x = none := h_inv_loop x h_keep h_σ_after_x
      -- The rest sim's gen-guard is over gen_r (rest's gen'); weaken from gen_f.
      -- gen_r ⊆ gen_f, so s ∉ gen_f → s ∉ gen_r.
      have h_guard_rest : ∀ s : String, x = HasIdent.ident (P := P) s →
          s ∈ StringGenState.stringGens gen ∨ s ∉ StringGenState.stringGens gen_r :=
        fun s heq => match h_outer_guard s heq with
          | Or.inl h_in => Or.inl h_in
          | Or.inr h_notin => Or.inr (fun h_in_r => h_notin
              (h_step_b_to_f.subset (h_step_le_to_b.subset (h_step_r_to_le.subset h_in_r))))
      exact h_preserve_rest x h_x_fresh_loop h_nil_not h_x_not_rest h_guard_rest
  | .block label body md :: rest =>
    simp only [stmtsToBlocks, bind, StateT.bind, pure] at h_gen
    -- Decompose the monadic chain
    generalize h_rest_eq : stmtsToBlocks k rest exitConts [] gen = r_rest at h_gen
    obtain ⟨⟨kNext, bsNext⟩, gen_r⟩ := r_rest
    simp at h_gen
    generalize h_body_eq : stmtsToBlocks kNext body
      ((some label, kNext) :: exitConts) [] gen_r = r_body at h_gen
    obtain ⟨⟨bl, bbs⟩, gen_b⟩ := r_body
    simp at h_gen
    generalize h_flush_eq : @flushCmds P (Cmd P) _ "blk$" accum .none bl gen_b
      = r_flush at h_gen
    obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
    -- Decompose structured execution of [.block label body md :: rest]
    have ⟨ρ_blk, h_block_star, h_rest_star⟩ :=
      stmts_append_terminates P (EvalCmd P) extendEval
        [.block label body md] rest ρ₀ ρ'
        (by simp at h_term ⊢; exact h_term)
    -- Invert: structured execution of [.block label body md] to terminal ρ_blk.
    -- Step 1: step_stmts_cons.
    -- Step 2: step_block enters the block (saves parent store ρ₀.store).
    -- Step 3: body executes in the block context.
    -- Step 4: step_block_done OR step_block_exit_match terminates the block,
    --         producing { ρ_inner with store := projectStore ρ₀.store ρ_inner.store }.
    -- Use the stronger inversion `block_some_reaches_terminal` for our explicitly-labelled
    -- block; this constrains the exit-match label to equal `label`.
    have h_block_inv :
        (∃ ρ_inner, StepStmtStar P (EvalCmd P) extendEval
          (.stmts body ρ₀) (.terminal ρ_inner) ∧
          ρ_blk = { ρ_inner with store := projectStore ρ₀.store ρ_inner.store }) ∨
        (∃ ρ_inner, StepStmtStar P (EvalCmd P) extendEval
          (.stmts body ρ₀) (.exiting label ρ_inner) ∧
          ρ_blk = { ρ_inner with store := projectStore ρ₀.store ρ_inner.store }) := by
      cases h_block_star with
      | step _ _ _ hstep1 hrest1 =>
        cases hstep1 with
        | step_stmts_cons =>
          have ⟨ρ_mid, h_inner, h_nil⟩ :=
            seq_reaches_terminal P (EvalCmd P) extendEval hrest1
          have h_eq := stmts_nil_terminal (EvalCmd P) extendEval _ _ h_nil
          subst h_eq
          cases h_inner with
          | step _ _ _ hstep2 hrest2 =>
            cases hstep2 with
            | step_block =>
              exact block_some_reaches_terminal P (EvalCmd P) extendEval hrest2
    -- Extract ρ_inner. In both cases (terminal/exit-match), the projection eq holds.
    obtain ⟨ρ_inner, h_body_term_or_exit, h_ρ_blk_eq⟩ : ∃ ρ_inner,
        (StepStmtStar P (EvalCmd P) extendEval
          (.stmts body ρ₀) (.terminal ρ_inner) ∨
         StepStmtStar P (EvalCmd P) extendEval
          (.stmts body ρ₀) (.exiting label ρ_inner)) ∧
        ρ_blk = { ρ_inner with store := projectStore ρ₀.store ρ_inner.store } := by
      rcases h_block_inv with h | h
      · obtain ⟨ρ_i, hterm, heq⟩ := h
        exact ⟨ρ_i, Or.inl hterm, heq⟩
      · obtain ⟨ρ_i, hexit, heq⟩ := h
        exact ⟨ρ_i, Or.inr hexit, heq⟩
    -- noFuncDecl projections.
    have h_nofd_body : Block.noFuncDecl body = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.1
    have h_nofd_rest : Block.noFuncDecl rest = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.2
    -- simpleShape projections.
    have h_simple_head : Stmt.simpleShape (.block label body md) = true :=
      (Block.simpleShape_cons_iff.mp h_simple).1
    have h_simple_rest : Block.simpleShape rest = true :=
      (Block.simpleShape_cons_iff.mp h_simple).2
    have h_simple_body : Block.simpleShape body = true := by
      simp only [Stmt.simpleShape] at h_simple_head; exact h_simple_head
    -- loopBodyNoInits/loopHasNoInvariants/noMeasureLoops projections for body and rest.
    have h_lbni_head : Stmt.loopBodyNoInits (.block label body md) = true :=
      (Block.loopBodyNoInits_cons_iff.mp h_lbni).1
    have h_lbni_rest : Block.loopBodyNoInits rest = true :=
      (Block.loopBodyNoInits_cons_iff.mp h_lbni).2
    have h_lbni_body : Block.loopBodyNoInits body = true :=
      Stmt.loopBodyNoInits_block_body h_lbni_head
    have h_lhni_head : Stmt.loopHasNoInvariants (.block label body md) = true :=
      (Block.loopHasNoInvariants_cons_iff.mp h_lhni).1
    have h_lhni_rest : Block.loopHasNoInvariants rest = true :=
      (Block.loopHasNoInvariants_cons_iff.mp h_lhni).2
    have h_lhni_body : Block.loopHasNoInvariants body = true :=
      Stmt.loopHasNoInvariants_block_body h_lhni_head
    have h_nml_head : Stmt.noMeasureLoops (.block label body md) = true :=
      (Block.noMeasureLoops_cons_iff.mp h_nml).1
    have h_nml_rest : Block.noMeasureLoops rest = true :=
      (Block.noMeasureLoops_cons_iff.mp h_nml).2
    have h_nml_body : Block.noMeasureLoops body = true :=
      Stmt.noMeasureLoops_block_body h_nml_head
    -- uniqueInits projections.
    have h_unique_body : Block.uniqueInits body :=
      Block.uniqueInits.block_body h_unique
    have h_unique_rest : Block.uniqueInits rest := Block.uniqueInits.tail h_unique
    -- Block.initVars decomposition: outer ss = .block label body md :: rest, so
    -- Block.initVars ss = Block.initVars body ++ Block.initVars rest.
    have h_initvars_eq :
        Block.initVars (Stmt.block label body md :: rest) =
        Block.initVars body ++ Block.initVars rest := by
      rw [Block.initVars]
      simp
    -- Sub-block and rest combined-no-gen-suffix discharges (used for both
    -- `label = bl` and `label ≠ bl` sub-cases).
    have h_body_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars [].reverse ++ Block.initVars body) := fun x hx s heq =>
      h_combined_no_gen_suffix x (List.mem_append_right _ (h_initvars_eq ▸
        List.mem_append_left _ (by simpa [Cmds.definedVars] using hx))) s heq
    have h_rest_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars [].reverse ++ Block.initVars rest) := fun x hx s heq =>
      h_combined_no_gen_suffix x (List.mem_append_right _ (h_initvars_eq ▸
        List.mem_append_right _ (by simpa [Cmds.definedVars] using hx))) s heq
    -- Mirror of h_initvars_eq / no_gen_suffix discharges for modifiedVars.
    have h_modvars_eq :
        transformBlockModVars (Stmt.block label body md :: rest) =
        transformBlockModVars body ++ transformBlockModVars rest := by
      rw [transformBlockModVars_cons, transformStmtModVars_block]
    have h_body_no_gen_suffix_mod :
        NoGenSuffix (P := P) Q (Cmds.modifiedVars [].reverse ++ transformBlockModVars body) := fun x hx s heq =>
      h_combined_no_gen_suffix_mod x (List.mem_append_right _ (h_modvars_eq ▸
        List.mem_append_left _ (by simpa [Cmds.modifiedVars] using hx))) s heq
    have h_rest_no_gen_suffix_mod :
        NoGenSuffix (P := P) Q (Cmds.modifiedVars [].reverse ++ transformBlockModVars rest) := fun x hx s heq =>
      h_combined_no_gen_suffix_mod x (List.mem_append_right _ (h_modvars_eq ▸
        List.mem_append_right _ (by simpa [Cmds.modifiedVars] using hx))) s heq
    -- GenStep chains for WF and subset (block case).
    have h_step_b_to_f : StringGenState.GenStep gen_b gen_f :=
      flushCmds_genStep _ _ _ _ _ _ _ _ h_flush_eq
    have h_step_r_to_b : StringGenState.GenStep gen_r gen_b :=
      stmtsToBlocks_genStep _ _ _ _ _ _ _ _ h_body_eq
    have h_step_gen_to_r : StringGenState.GenStep gen gen_r :=
      stmtsToBlocks_genStep _ _ _ _ _ _ _ _ h_rest_eq
    have h_step_gen_to_b : StringGenState.GenStep gen gen_b :=
      h_step_gen_to_r.trans h_step_r_to_b
    have h_wf_r : StringGenState.WF gen_r := h_step_gen_to_r.wf_mono h_wf_gen
    have h_wf_b : StringGenState.WF gen_b := h_step_gen_to_b.wf_mono h_wf_gen
    -- Block membership distribution. We split based on l = bl vs l ≠ bl.
    -- Convert h_gen via the if: extract entry and the blocks shape.
    by_cases h_l_eq_bl : label = bl
    · -- Case l = bl: blocks = accumBlocks ++ bbs ++ bsNext, entry = accumEntry.
      simp [h_l_eq_bl] at h_gen
      have h_entry_eq : accumEntry = entry :=
        (Prod.mk.inj (Prod.mk.inj h_gen).1).1
      have h_gen_eq_f : gen_f = gen' := (Prod.mk.inj h_gen).2
      have h_outer_upper_b : StringGenState.stringGens gen_b ⊆ StringGenState.stringGens genUpperBound :=
        h_step_b_to_f.subset.trans (h_gen_eq_f ▸ h_outer_upper)
      have h_outer_upper_r : StringGenState.stringGens gen_r ⊆ StringGenState.stringGens genUpperBound :=
        h_step_r_to_b.subset.trans h_outer_upper_b
      have h_blocks_eq : accumBlocks ++ (bbs ++ bsNext) = blocks :=
        (Prod.mk.inj (Prod.mk.inj h_gen).1).2
      subst h_entry_eq
      subst h_blocks_eq
      -- Lift store-no-gens to σ_cfg_after using the new helper.
      -- (Bound after `flushCmds_simulation_agree` produces σ_cfg_after; introduced below.)
      -- Block membership for sub-blocks.
      have h_cfg_accum : ∀ b ∈ accumBlocks, b ∈ cfg.blocks := fun b hb =>
        h_cfg_blocks b (List.mem_append_left _ hb)
      have h_cfg_bbs : ∀ b ∈ bbs, b ∈ cfg.blocks := fun b hb =>
        h_cfg_blocks b (List.mem_append_right _ (List.mem_append_left _ hb))
      have h_cfg_rest : ∀ b ∈ bsNext, b ∈ cfg.blocks := fun b hb =>
        h_cfg_blocks b (List.mem_append_right _ (List.mem_append_right _ hb))
      -- Case analysis: in the case l = bl, we use flushCmds_simulation_agree directly.
      -- Compute h_fresh_accum / h_unique_accum from h_fresh_combined / h_unique_combined.
      have h_fresh_accum : ∀ x ∈ Cmds.definedVars accum.reverse, σ_base x = none := by
        intro x hx
        exact h_fresh_combined x (List.mem_append_left _ hx)
      have h_unique_accum : (Cmds.definedVars accum.reverse).Nodup :=
        (List.nodup_append.mp h_unique_combined).1
      -- Flush phase: step from accumEntry (= entry) to bl using flushCmds_simulation_agree.
      have ⟨σ_cfg_after, h_step_flush, h_agree_after, h_preserve_flush⟩ :=
        flushCmds_simulation_agree extendEval "blk$" bl accum gen_b gen_f accumEntry
          accumBlocks h_flush_eq σ_struct_base σ_base hf_base hf_accum ρ₀
          hwfb hwfv hwf_def hwf_congr h_accum h_agree_entry h_fresh_accum h_unique_accum
          h_hf cfg h_cfg_accum h_cfg_nodup
      -- Now we have: (.atBlock accumEntry σ_base hf_base) → (.atBlock bl σ_cfg_after ρ₀.hasFailure)
      -- Body recursion: from (.atBlock bl σ_cfg_after ρ₀.hasFailure) to (.atBlock kNext σ_cfg_body _).
      -- Body's structured run is from ρ₀ to ρ_inner.
      -- Need to handle both terminal and exit-match cases for body.
      rcases h_body_term_or_exit with h_body_term | h_body_exit_star
      · -- Body terminates with ρ_inner; use that for the sim.
        -- Freshness for body recursion (initVars body must be fresh in σ_cfg_after).
        have h_fresh_body_inits_after : ∀ x ∈ Block.initVars body, σ_cfg_after x = none := by
          intro x hx
          have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := fun h_in_accum =>
            -- x in body's initVars and accum's defs both, contradicting Nodup.
            (h_initvars_eq ▸ List.nodup_append.mp h_unique_combined).2.2
              x h_in_accum x (List.mem_append_left _ hx) rfl
          have h_σ_base_x : σ_base x = none := by
            apply h_fresh_combined
            apply List.mem_append_right
            rw [h_initvars_eq]
            exact List.mem_append_left _ hx
          exact h_preserve_flush x h_σ_base_x h_x_not_accum
        have h_combined_body :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
            σ_cfg_after x = none :=
          fun x hx => h_fresh_body_inits_after x (by simpa [Cmds.definedVars] using hx)
        have h_unique_combined_body :
            (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
          simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_body
        have h_accum_nil : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        -- Lift store-no-gens-upper to σ_cfg_after.
        have h_store_no_gens_upper_after :
            ∀ x : String, Q x →
              x ∉ StringGenState.stringGens genUpperBound →
              σ_cfg_after (HasIdent.ident (P := P) x) = none :=
          store_no_gens_lift_after_flush h_preserve_flush genUpperBound h_store_no_gens_upper
            (fun x hx => h_combined_no_gen_suffix x (List.mem_append_left _ hx))
        -- Recurse on body.
        have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
          stmtsToBlocks_simulation extendEval kNext body
            ((some label, kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
            h_nofd_body h_simple_body h_unique_body
            h_lbni_body h_lhni_body h_nml_body
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ_inner hwfb hwfv hwf_def hwf_congr hwf_var
            h_body_term h_accum_nil h_agree_after
            h_combined_body h_unique_combined_body (by simp)
            h_wf_r h_body_no_gen_suffix h_body_no_gen_suffix_mod
            genUpperBound h_outer_upper_b h_store_no_gens_upper_after h_foreign
            cfg h_cfg_bbs h_cfg_nodup
        -- h_agree_body : StoreAgreement ρ_inner.store σ_cfg_body
        -- Bridge structured-side projection to CFG.
        have h_agree_block_body : StoreAgreement ρ_blk.store σ_cfg_body :=
          StoreAgreement.through_projectStore h_ρ_blk_eq h_agree_body
        -- Eval well-formedness preservation through body.
        have h_eval_blk : ρ_blk.eval = ρ₀.eval := by
          rw [h_ρ_blk_eq]
          exact smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
            body ρ₀ ρ_inner h_nofd_body h_body_term
        have hwfb₁ : WellFormedSemanticEvalBool ρ_blk.eval := h_eval_blk ▸ hwfb
        have hwfv₁ : WellFormedSemanticEvalVal ρ_blk.eval := h_eval_blk ▸ hwfv
        have hwf_def₁ : WellFormedSemanticEvalDef ρ_blk.eval := h_eval_blk ▸ hwf_def
        have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_blk.eval := h_eval_blk ▸ hwf_congr
        have hwf_var₁ : WellFormedSemanticEvalVar ρ_blk.eval := h_eval_blk ▸ hwf_var
        -- Freshness for rest's inits at σ_cfg_body.
        have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none :=
          (fresh_inits_after_step h_initvars_eq h_unique_combined h_fresh_combined
            h_preserve_flush).2
        have h_fresh_rest_inits_body : ∀ x ∈ Block.initVars rest, σ_cfg_body x = none :=
          fresh_rest_inits_body_step h_initvars_eq h_unique h_preserve_body
            (fun s hns h_in => h_foreign s hns (h_outer_upper_b h_in))
            h_rest_no_gen_suffix h_fresh_rest_inits_after
        have h_combined_rest :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
            σ_cfg_body x = none := fun x hx =>
          h_fresh_rest_inits_body x (by simpa [Cmds.definedVars] using hx)
        have h_unique_combined_rest :
            (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
          simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_rest
        have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_blk.eval ρ_blk.store
            [].reverse ρ_blk.store false := EvalCmds.eval_cmds_none
        -- ρ_blk.hasFailure = ρ_inner.hasFailure (since projection only changes store)
        have h_hasFail_blk : ρ_blk.hasFailure = ρ_inner.hasFailure := by
          rw [h_ρ_blk_eq]
        -- Lift `h_store_no_gens_upper` through the body sub-simulation
        -- using the strengthened (4-premise) `h_preserve_body` directly.
        have h_store_no_gens_upper_body :
            ∀ x : String, Q x →
              x ∉ StringGenState.stringGens genUpperBound →
              σ_cfg_body (HasIdent.ident (P := P) x) = none :=
          store_no_gens_upper_lift_through_subsim gen_r gen_b genUpperBound
            h_outer_upper_b h_preserve_body h_store_no_gens_upper_after
            (fun x hx s heq => h_body_no_gen_suffix x (List.mem_append_right _ hx) s heq)
        -- Recurse on rest.
        have ⟨σ_cfg_rest, h_step_rest, h_agree_rest, h_preserve_rest⟩ :=
          stmtsToBlocks_simulation extendEval k rest exitConts [] gen gen_r kNext bsNext
            h_rest_eq h_nofd_rest h_simple_rest h_unique_rest
            h_lbni_rest h_lhni_rest h_nml_rest
            ρ_blk.store σ_cfg_body
            ρ_blk.hasFailure false ρ_blk ρ' hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁ hwf_var₁
            h_rest_star h_accum_nil_r h_agree_block_body
            h_combined_rest h_unique_combined_rest (by simp)
            h_wf_gen h_rest_no_gen_suffix h_rest_no_gen_suffix_mod
            genUpperBound h_outer_upper_r h_store_no_gens_upper_body h_foreign
            cfg h_cfg_rest h_cfg_nodup
        refine ⟨σ_cfg_rest, ?_, h_agree_rest, ?_⟩
        · -- Compose the CFG steps. h_step_body returns at ρ_inner.hasFailure;
          -- transport to ρ_blk.hasFailure via h_hasFail_blk.symm.
          exact StepDetCFGStar_trans
            (StepDetCFGStar_trans h_step_flush (h_hasFail_blk.symm ▸ h_step_body)) h_step_rest
        · -- Freshness preservation for the outer call.
          intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
          have h_x_not_body : x ∉ Block.initVars body := fun hx =>
            h_x_not_inits (h_initvars_eq ▸ List.mem_append_left _ hx)
          have h_x_not_rest : x ∉ Block.initVars rest := fun hx =>
            h_x_not_inits (h_initvars_eq ▸ List.mem_append_right _ hx)
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          -- Build inner guards from outer guard via GenStep monotonicity.
          -- Chain: gen → gen_r → gen_b → gen_f = gen'.
          have h_inner_guard_b :=
            inner_guard_step_b h_step_gen_to_r h_step_b_to_f h_gen_eq_f h_outer_guard
          have h_inner_guard_r :=
            inner_guard_step_r h_step_b_to_f h_step_r_to_b h_gen_eq_f h_outer_guard
          have h_σ_body_x : σ_cfg_body x = none :=
            h_preserve_body x h_σ_after_x h_nil_not h_x_not_body h_inner_guard_b
          exact h_preserve_rest x h_σ_body_x h_nil_not h_x_not_rest h_inner_guard_r
      · -- Body exits with matching label.  Same final-store shape as inl:
        -- ρ_blk = { ρ_inner with store := projectStore ρ₀.store ρ_inner.store }.
        -- CFG-side: body's exitCont (some label, kNext) resolves `.exit label`
        -- inside body to a goto-kNext, so body's CFG reaches kNext.  Use
        -- `stmtsToBlocks_simulation_to_cont` for the body recursion.
        -- exitConts for body = (some label, kNext) :: exitConts.
        have h_label_lookup :
            ((some label, kNext) :: exitConts).lookup (some label) = some kNext := by
          simp [List.lookup]
        -- Freshness for body recursion.
        have h_fresh_body_inits_after : ∀ x ∈ Block.initVars body, σ_cfg_after x = none :=
          (fresh_inits_after_step h_initvars_eq h_unique_combined h_fresh_combined
            h_preserve_flush).1
        have h_combined_body :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
            σ_cfg_after x = none :=
          fun x hx => h_fresh_body_inits_after x (by simpa [Cmds.definedVars] using hx)
        have h_unique_combined_body :
            (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
          simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_body
        have h_accum_nil : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        -- Lift store-no-gens-upper to σ_cfg_after.
        have h_store_no_gens_upper_after :
            ∀ x : String, Q x →
              x ∉ StringGenState.stringGens genUpperBound →
              σ_cfg_after (HasIdent.ident (P := P) x) = none :=
          store_no_gens_lift_after_flush h_preserve_flush genUpperBound h_store_no_gens_upper
            (fun x hx => h_combined_no_gen_suffix x (List.mem_append_left _ hx))
        -- Recurse on body with _to_cont.
        have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
          stmtsToBlocks_simulation_to_cont extendEval kNext body
            ((some label, kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
            h_nofd_body h_simple_body h_unique_body
            h_lbni_body h_lhni_body h_nml_body
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ_inner label kNext h_label_lookup hwfb hwfv hwf_def hwf_congr hwf_var
            h_body_exit_star h_accum_nil h_agree_after
            h_combined_body h_unique_combined_body (by simp)
            h_wf_r h_body_no_gen_suffix h_body_no_gen_suffix_mod
            genUpperBound h_outer_upper_b h_store_no_gens_upper_after h_foreign
            cfg h_cfg_bbs h_cfg_nodup
        -- Bridge structured-side projection to CFG.
        have h_agree_block_body : StoreAgreement ρ_blk.store σ_cfg_body :=
          StoreAgreement.through_projectStore h_ρ_blk_eq h_agree_body
        -- Eval well-formedness preservation through body (to .exiting).
        have h_eval_blk : ρ_blk.eval = ρ₀.eval := by
          rw [h_ρ_blk_eq]
          exact smallStep_noFuncDecl_preserves_eval_block_exiting P (EvalCmd P) extendEval
            body ρ₀ ρ_inner label h_nofd_body h_body_exit_star
        have hwfb₁ : WellFormedSemanticEvalBool ρ_blk.eval := h_eval_blk ▸ hwfb
        have hwfv₁ : WellFormedSemanticEvalVal ρ_blk.eval := h_eval_blk ▸ hwfv
        have hwf_def₁ : WellFormedSemanticEvalDef ρ_blk.eval := h_eval_blk ▸ hwf_def
        have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_blk.eval := h_eval_blk ▸ hwf_congr
        have hwf_var₁ : WellFormedSemanticEvalVar ρ_blk.eval := h_eval_blk ▸ hwf_var
        -- Freshness for rest's inits at σ_cfg_body.
        have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none :=
          (fresh_inits_after_step h_initvars_eq h_unique_combined h_fresh_combined
            h_preserve_flush).2
        have h_fresh_rest_inits_body : ∀ x ∈ Block.initVars rest, σ_cfg_body x = none :=
          fresh_rest_inits_body_step h_initvars_eq h_unique h_preserve_body
            (fun s hns h_in => h_foreign s hns (h_outer_upper_b h_in))
            h_rest_no_gen_suffix h_fresh_rest_inits_after
        have h_combined_rest :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
            σ_cfg_body x = none := fun x hx =>
          h_fresh_rest_inits_body x (by simpa [Cmds.definedVars] using hx)
        have h_unique_combined_rest :
            (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
          simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_rest
        have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_blk.eval ρ_blk.store
            [].reverse ρ_blk.store false := EvalCmds.eval_cmds_none
        have h_hasFail_blk : ρ_blk.hasFailure = ρ_inner.hasFailure := by
          rw [h_ρ_blk_eq]
        -- Lift `h_store_no_gens_upper` through the body sub-simulation
        -- using the strengthened (4-premise) `h_preserve_body` directly.
        have h_store_no_gens_upper_body :
            ∀ x : String, Q x →
              x ∉ StringGenState.stringGens genUpperBound →
              σ_cfg_body (HasIdent.ident (P := P) x) = none :=
          store_no_gens_upper_lift_through_subsim gen_r gen_b genUpperBound
            h_outer_upper_b h_preserve_body h_store_no_gens_upper_after
            (fun x hx s heq => h_body_no_gen_suffix x (List.mem_append_right _ hx) s heq)
        -- Recurse on rest with _simulation.
        have ⟨σ_cfg_rest, h_step_rest, h_agree_rest, h_preserve_rest⟩ :=
          stmtsToBlocks_simulation extendEval k rest exitConts [] gen gen_r kNext bsNext
            h_rest_eq h_nofd_rest h_simple_rest h_unique_rest
            h_lbni_rest h_lhni_rest h_nml_rest
            ρ_blk.store σ_cfg_body
            ρ_blk.hasFailure false ρ_blk ρ' hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁ hwf_var₁
            h_rest_star h_accum_nil_r h_agree_block_body
            h_combined_rest h_unique_combined_rest (by simp)
            h_wf_gen h_rest_no_gen_suffix h_rest_no_gen_suffix_mod
            genUpperBound h_outer_upper_r h_store_no_gens_upper_body h_foreign
            cfg h_cfg_rest h_cfg_nodup
        refine ⟨σ_cfg_rest, ?_, h_agree_rest, ?_⟩
        · -- Transport h_step_body from ρ_inner.hasFailure to ρ_blk.hasFailure.
          exact StepDetCFGStar_trans
            (StepDetCFGStar_trans h_step_flush (h_hasFail_blk.symm ▸ h_step_body)) h_step_rest
        · intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
          have h_x_not_body : x ∉ Block.initVars body := fun hx =>
            h_x_not_inits (h_initvars_eq ▸ List.mem_append_left _ hx)
          have h_x_not_rest : x ∉ Block.initVars rest := fun hx =>
            h_x_not_inits (h_initvars_eq ▸ List.mem_append_right _ hx)
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          -- Build inner guards from outer guard via GenStep monotonicity.
          -- Chain: gen → gen_r → gen_b → gen_f = gen'.
          have h_inner_guard_b :=
            inner_guard_step_b h_step_gen_to_r h_step_b_to_f h_gen_eq_f h_outer_guard
          have h_inner_guard_r :=
            inner_guard_step_r h_step_b_to_f h_step_r_to_b h_gen_eq_f h_outer_guard
          have h_σ_body_x : σ_cfg_body x = none :=
            h_preserve_body x h_σ_after_x h_nil_not h_x_not_body h_inner_guard_b
          exact h_preserve_rest x h_σ_body_x h_nil_not h_x_not_rest h_inner_guard_r
    · -- Case l ≠ bl: blocks = accumBlocks ++ [(label, {cmds:=[], goto bl})] ++ bbs ++ bsNext,
      -- entry = accumEntry (after the bug fix).  CFG flow is the same as l = bl:
      -- accumEntry → bl (via accumBlocks) → kNext (via body) → k (via rest).
      -- The (label, ...) block is vestigial — not on the reachable path.
      simp [h_l_eq_bl] at h_gen
      have h_entry_eq : accumEntry = entry :=
        (Prod.mk.inj (Prod.mk.inj h_gen).1).1
      let lBlk : DetBlock String (Cmd P) P :=
        { cmds := [], transfer := DetTransferCmd.goto bl md }
      have h_blocks_eq :
          accumBlocks ++ (label, lBlk) :: (bbs ++ bsNext) = blocks :=
        (Prod.mk.inj (Prod.mk.inj h_gen).1).2
      have h_gen_eq_f : gen_f = gen' := (Prod.mk.inj h_gen).2
      subst h_entry_eq
      have h_outer_upper_b : StringGenState.stringGens gen_b ⊆ StringGenState.stringGens genUpperBound :=
        h_step_b_to_f.subset.trans (h_gen_eq_f ▸ h_outer_upper)
      have h_outer_upper_r : StringGenState.stringGens gen_r ⊆ StringGenState.stringGens genUpperBound :=
        h_step_r_to_b.subset.trans h_outer_upper_b
      -- Block membership: extract from h_cfg_blocks.
      -- blocks = accumBlocks ++ (label, lBlk) :: (bbs ++ bsNext)
      have h_cfg_accum : ∀ b ∈ accumBlocks, b ∈ cfg.blocks := by
        intro b hb
        exact h_cfg_blocks b (h_blocks_eq ▸ List.mem_append_left _ hb)
      have h_cfg_bbs : ∀ b ∈ bbs, b ∈ cfg.blocks := by
        intro b hb
        exact h_cfg_blocks b
          (h_blocks_eq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hb)))
      have h_cfg_rest : ∀ b ∈ bsNext, b ∈ cfg.blocks := by
        intro b hb
        exact h_cfg_blocks b
          (h_blocks_eq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ hb)))
      -- Now the proof proceeds exactly as in l = bl.
      have h_fresh_accum : ∀ x ∈ Cmds.definedVars accum.reverse, σ_base x = none := by
        intro x hx
        exact h_fresh_combined x (List.mem_append_left _ hx)
      have h_unique_accum : (Cmds.definedVars accum.reverse).Nodup :=
        (List.nodup_append.mp h_unique_combined).1
      have ⟨σ_cfg_after, h_step_flush, h_agree_after, h_preserve_flush⟩ :=
        flushCmds_simulation_agree extendEval "blk$" bl accum gen_b gen_f accumEntry
          accumBlocks h_flush_eq σ_struct_base σ_base hf_base hf_accum ρ₀
          hwfb hwfv hwf_def hwf_congr h_accum h_agree_entry h_fresh_accum h_unique_accum
          h_hf cfg h_cfg_accum h_cfg_nodup
      have h_store_no_gens_upper_after :
          ∀ x : String, Q x →
            x ∉ StringGenState.stringGens genUpperBound →
            σ_cfg_after (HasIdent.ident (P := P) x) = none :=
        store_no_gens_lift_after_flush h_preserve_flush genUpperBound h_store_no_gens_upper
          (fun x hx => h_combined_no_gen_suffix x (List.mem_append_left _ hx))
      rcases h_body_term_or_exit with h_body_term | h_body_exit_star
      · -- Body terminates with ρ_inner.
        have h_fresh_body_inits_after : ∀ x ∈ Block.initVars body, σ_cfg_after x = none :=
          (fresh_inits_after_step h_initvars_eq h_unique_combined h_fresh_combined
            h_preserve_flush).1
        have h_combined_body :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
            σ_cfg_after x = none :=
          fun x hx => h_fresh_body_inits_after x (by simpa [Cmds.definedVars] using hx)
        have h_unique_combined_body :
            (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
          simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_body
        have h_accum_nil : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
          stmtsToBlocks_simulation extendEval kNext body
            ((some label, kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
            h_nofd_body h_simple_body h_unique_body
            h_lbni_body h_lhni_body h_nml_body
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ_inner hwfb hwfv hwf_def hwf_congr hwf_var
            h_body_term h_accum_nil h_agree_after
            h_combined_body h_unique_combined_body (by simp)
            h_wf_r h_body_no_gen_suffix h_body_no_gen_suffix_mod
            genUpperBound h_outer_upper_b h_store_no_gens_upper_after h_foreign
            cfg h_cfg_bbs h_cfg_nodup
        have h_agree_block_body : StoreAgreement ρ_blk.store σ_cfg_body :=
          StoreAgreement.through_projectStore h_ρ_blk_eq h_agree_body
        have h_eval_blk : ρ_blk.eval = ρ₀.eval := by
          rw [h_ρ_blk_eq]
          exact smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
            body ρ₀ ρ_inner h_nofd_body h_body_term
        have hwfb₁ : WellFormedSemanticEvalBool ρ_blk.eval := h_eval_blk ▸ hwfb
        have hwfv₁ : WellFormedSemanticEvalVal ρ_blk.eval := h_eval_blk ▸ hwfv
        have hwf_def₁ : WellFormedSemanticEvalDef ρ_blk.eval := h_eval_blk ▸ hwf_def
        have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_blk.eval := h_eval_blk ▸ hwf_congr
        have hwf_var₁ : WellFormedSemanticEvalVar ρ_blk.eval := h_eval_blk ▸ hwf_var
        have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none :=
          (fresh_inits_after_step h_initvars_eq h_unique_combined h_fresh_combined
            h_preserve_flush).2
        have h_fresh_rest_inits_body : ∀ x ∈ Block.initVars rest, σ_cfg_body x = none :=
          fresh_rest_inits_body_step h_initvars_eq h_unique h_preserve_body
            (fun s hns h_in => h_foreign s hns (h_outer_upper_b h_in))
            h_rest_no_gen_suffix h_fresh_rest_inits_after
        have h_combined_rest :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
            σ_cfg_body x = none := fun x hx =>
          h_fresh_rest_inits_body x (by simpa [Cmds.definedVars] using hx)
        have h_unique_combined_rest :
            (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
          simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_rest
        have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_blk.eval ρ_blk.store
            [].reverse ρ_blk.store false := EvalCmds.eval_cmds_none
        have h_hasFail_blk : ρ_blk.hasFailure = ρ_inner.hasFailure := by
          rw [h_ρ_blk_eq]
        -- Lift `h_store_no_gens_upper` through the body sub-simulation
        -- using the strengthened (4-premise) `h_preserve_body` directly.
        have h_store_no_gens_upper_body :
            ∀ x : String, Q x →
              x ∉ StringGenState.stringGens genUpperBound →
              σ_cfg_body (HasIdent.ident (P := P) x) = none :=
          store_no_gens_upper_lift_through_subsim gen_r gen_b genUpperBound
            h_outer_upper_b h_preserve_body h_store_no_gens_upper_after
            (fun x hx s heq => h_body_no_gen_suffix x (List.mem_append_right _ hx) s heq)
        have ⟨σ_cfg_rest, h_step_rest, h_agree_rest, h_preserve_rest⟩ :=
          stmtsToBlocks_simulation extendEval k rest exitConts [] gen gen_r kNext bsNext
            h_rest_eq h_nofd_rest h_simple_rest h_unique_rest
            h_lbni_rest h_lhni_rest h_nml_rest ρ_blk.store σ_cfg_body
            ρ_blk.hasFailure false ρ_blk ρ' hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁ hwf_var₁
            h_rest_star h_accum_nil_r h_agree_block_body
            h_combined_rest h_unique_combined_rest (by simp)
            h_wf_gen h_rest_no_gen_suffix h_rest_no_gen_suffix_mod
            genUpperBound h_outer_upper_r h_store_no_gens_upper_body h_foreign
            cfg h_cfg_rest h_cfg_nodup
        refine ⟨σ_cfg_rest, ?_, h_agree_rest, ?_⟩
        · -- Transport h_step_body from ρ_inner.hasFailure to ρ_blk.hasFailure.
          exact StepDetCFGStar_trans
            (StepDetCFGStar_trans h_step_flush (h_hasFail_blk.symm ▸ h_step_body)) h_step_rest
        · intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
          have h_x_not_body : x ∉ Block.initVars body := fun hx =>
            h_x_not_inits (h_initvars_eq ▸ List.mem_append_left _ hx)
          have h_x_not_rest : x ∉ Block.initVars rest := fun hx =>
            h_x_not_inits (h_initvars_eq ▸ List.mem_append_right _ hx)
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          -- Build inner guards from outer guard via GenStep monotonicity.
          have h_inner_guard_b :=
            inner_guard_step_b h_step_gen_to_r h_step_b_to_f h_gen_eq_f h_outer_guard
          have h_inner_guard_r :=
            inner_guard_step_r h_step_b_to_f h_step_r_to_b h_gen_eq_f h_outer_guard
          have h_σ_body_x : σ_cfg_body x = none :=
            h_preserve_body x h_σ_after_x h_nil_not h_x_not_body h_inner_guard_b
          exact h_preserve_rest x h_σ_body_x h_nil_not h_x_not_rest h_inner_guard_r
      · -- Body exits with matching label; same as l = bl body-exit case.
        have h_label_lookup :
            ((some label, kNext) :: exitConts).lookup (some label) = some kNext := by
          simp [List.lookup]
        have h_fresh_body_inits_after : ∀ x ∈ Block.initVars body, σ_cfg_after x = none :=
          (fresh_inits_after_step h_initvars_eq h_unique_combined h_fresh_combined
            h_preserve_flush).1
        have h_combined_body :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
            σ_cfg_after x = none :=
          fun x hx => h_fresh_body_inits_after x (by simpa [Cmds.definedVars] using hx)
        have h_unique_combined_body :
            (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
          simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_body
        have h_accum_nil : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
          stmtsToBlocks_simulation_to_cont extendEval kNext body
            ((some label, kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
            h_nofd_body h_simple_body h_unique_body
            h_lbni_body h_lhni_body h_nml_body
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ_inner label kNext h_label_lookup hwfb hwfv hwf_def hwf_congr hwf_var
            h_body_exit_star h_accum_nil h_agree_after
            h_combined_body h_unique_combined_body (by simp)
            h_wf_r h_body_no_gen_suffix h_body_no_gen_suffix_mod
            genUpperBound h_outer_upper_b h_store_no_gens_upper_after h_foreign
            cfg h_cfg_bbs h_cfg_nodup
        have h_agree_block_body : StoreAgreement ρ_blk.store σ_cfg_body :=
          StoreAgreement.through_projectStore h_ρ_blk_eq h_agree_body
        have h_eval_blk : ρ_blk.eval = ρ₀.eval := by
          rw [h_ρ_blk_eq]
          exact smallStep_noFuncDecl_preserves_eval_block_exiting P (EvalCmd P) extendEval
            body ρ₀ ρ_inner label h_nofd_body h_body_exit_star
        have hwfb₁ : WellFormedSemanticEvalBool ρ_blk.eval := h_eval_blk ▸ hwfb
        have hwfv₁ : WellFormedSemanticEvalVal ρ_blk.eval := h_eval_blk ▸ hwfv
        have hwf_def₁ : WellFormedSemanticEvalDef ρ_blk.eval := h_eval_blk ▸ hwf_def
        have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_blk.eval := h_eval_blk ▸ hwf_congr
        have hwf_var₁ : WellFormedSemanticEvalVar ρ_blk.eval := h_eval_blk ▸ hwf_var
        have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none :=
          (fresh_inits_after_step h_initvars_eq h_unique_combined h_fresh_combined
            h_preserve_flush).2
        have h_fresh_rest_inits_body : ∀ x ∈ Block.initVars rest, σ_cfg_body x = none :=
          fresh_rest_inits_body_step h_initvars_eq h_unique h_preserve_body
            (fun s hns h_in => h_foreign s hns (h_outer_upper_b h_in))
            h_rest_no_gen_suffix h_fresh_rest_inits_after
        have h_combined_rest :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
            σ_cfg_body x = none := fun x hx =>
          h_fresh_rest_inits_body x (by simpa [Cmds.definedVars] using hx)
        have h_unique_combined_rest :
            (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
          simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_rest
        have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_blk.eval ρ_blk.store
            [].reverse ρ_blk.store false := EvalCmds.eval_cmds_none
        have h_hasFail_blk : ρ_blk.hasFailure = ρ_inner.hasFailure := by
          rw [h_ρ_blk_eq]
        -- Lift `h_store_no_gens_upper` through the body sub-simulation
        -- using the strengthened (4-premise) `h_preserve_body` directly.
        have h_store_no_gens_upper_body :
            ∀ x : String, Q x →
              x ∉ StringGenState.stringGens genUpperBound →
              σ_cfg_body (HasIdent.ident (P := P) x) = none :=
          store_no_gens_upper_lift_through_subsim gen_r gen_b genUpperBound
            h_outer_upper_b h_preserve_body h_store_no_gens_upper_after
            (fun x hx s heq => h_body_no_gen_suffix x (List.mem_append_right _ hx) s heq)
        have ⟨σ_cfg_rest, h_step_rest, h_agree_rest, h_preserve_rest⟩ :=
          stmtsToBlocks_simulation extendEval k rest exitConts [] gen gen_r kNext bsNext
            h_rest_eq h_nofd_rest h_simple_rest h_unique_rest
            h_lbni_rest h_lhni_rest h_nml_rest ρ_blk.store σ_cfg_body
            ρ_blk.hasFailure false ρ_blk ρ' hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁ hwf_var₁
            h_rest_star h_accum_nil_r h_agree_block_body
            h_combined_rest h_unique_combined_rest (by simp)
            h_wf_gen h_rest_no_gen_suffix h_rest_no_gen_suffix_mod
            genUpperBound h_outer_upper_r h_store_no_gens_upper_body h_foreign
            cfg h_cfg_rest h_cfg_nodup
        refine ⟨σ_cfg_rest, ?_, h_agree_rest, ?_⟩
        · -- Transport h_step_body from ρ_inner.hasFailure to ρ_blk.hasFailure.
          exact StepDetCFGStar_trans
            (StepDetCFGStar_trans h_step_flush (h_hasFail_blk.symm ▸ h_step_body)) h_step_rest
        · intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
          have h_x_not_body : x ∉ Block.initVars body := fun hx =>
            h_x_not_inits (h_initvars_eq ▸ List.mem_append_left _ hx)
          have h_x_not_rest : x ∉ Block.initVars rest := fun hx =>
            h_x_not_inits (h_initvars_eq ▸ List.mem_append_right _ hx)
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          -- Build inner guards from outer guard via GenStep monotonicity.
          have h_inner_guard_b :=
            inner_guard_step_b h_step_gen_to_r h_step_b_to_f h_gen_eq_f h_outer_guard
          have h_inner_guard_r :=
            inner_guard_step_r h_step_b_to_f h_step_r_to_b h_gen_eq_f h_outer_guard
          have h_σ_body_x : σ_cfg_body x = none :=
            h_preserve_body x h_σ_after_x h_nil_not h_x_not_body h_inner_guard_b
          exact h_preserve_rest x h_σ_body_x h_nil_not h_x_not_rest h_inner_guard_r
  | .exit label md :: rest =>
    -- Vacuous: structured semantics for .exit produces .exiting, never .terminal.
    exfalso
    cases h_term with
    | step _ _ _ hstep1 hrest1 =>
      cases hstep1 with
      | step_stmts_cons =>
        have ⟨ρ_mid, h_inner, _h_tail⟩ :=
          seq_reaches_terminal P (EvalCmd P) extendEval hrest1
        cases h_inner with
        | step _ _ _ hstep2 hrest2 =>
          cases hstep2 with
          | step_exit =>
            -- After step_exit the config is .exiting label ρ₀, which cannot
            -- step further to .terminal.
            cases hrest2 with
            | step _ _ _ h _ => cases h
  | .funcDecl decl md :: rest =>
    -- Precluded by h_nofd : Block.noFuncDecl ss = true
    simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd
  | .typeDecl tc md :: rest =>
    unfold stmtsToBlocks at h_gen
    -- typeDecl is a no-op; structured semantics steps to terminal with unchanged env
    have ⟨ρ₁, h_td_star, h_rest_star⟩ :=
      stmts_append_terminates P (EvalCmd P) extendEval [.typeDecl tc md] rest ρ₀ ρ'
        (by simp at h_term ⊢; exact h_term)
    have h_ρ₁ : ρ₁ = ρ₀ := by
      cases h_td_star with
      | step _ _ _ hstep1 hrest1 =>
        cases hstep1 with
        | step_stmts_cons =>
          have ⟨ρ_mid, h_inner, h_nil⟩ := seq_reaches_terminal P (EvalCmd P) extendEval hrest1
          have h_eq := stmts_nil_terminal (EvalCmd P) extendEval _ _ h_nil
          subst h_eq
          cases h_inner with
          | step _ _ _ hstep2 hrest2 =>
            cases hstep2 with
            | step_typeDecl =>
              cases hrest2 with
              | refl => rfl
              | step _ _ _ h _ => exact absurd h (by intro h; cases h)
    rw [h_ρ₁] at h_rest_star
    have h_nofd_rest : Block.noFuncDecl rest = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd
    have h_simple_rest : Block.simpleShape rest = true :=
      (Block.simpleShape_cons_iff.mp h_simple).2
    have h_unique_rest : Block.uniqueInits rest := Block.uniqueInits.tail h_unique
    have h_lbni_rest : Block.loopBodyNoInits rest = true :=
      (Block.loopBodyNoInits_cons_iff.mp h_lbni).2
    have h_lhni_rest : Block.loopHasNoInvariants rest = true :=
      (Block.loopHasNoInvariants_cons_iff.mp h_lhni).2
    have h_nml_rest : Block.noMeasureLoops rest = true :=
      (Block.noMeasureLoops_cons_iff.mp h_nml).2
    have ⟨h_fresh_combined', h_unique_combined',
          h_combined_no_gen_suffix', h_combined_no_gen_suffix_mod'⟩ :=
      typeDecl_arm_combined_lemmas tc md accum rest σ_base
        h_fresh_combined h_unique_combined
        h_combined_no_gen_suffix h_combined_no_gen_suffix_mod
    have ⟨σ_cfg, h_step, h_agree, h_preserve⟩ :=
      stmtsToBlocks_simulation extendEval k rest exitConts accum gen gen'
        entry blocks h_gen h_nofd_rest h_simple_rest h_unique_rest
        h_lbni_rest h_lhni_rest h_nml_rest
        σ_struct_base σ_base hf_base hf_accum
        ρ₀ ρ' hwfb hwfv hwf_def hwf_congr hwf_var
       h_rest_star h_accum h_agree_entry
        h_fresh_combined' h_unique_combined' h_hf
        h_wf_gen h_combined_no_gen_suffix' h_combined_no_gen_suffix_mod'
        genUpperBound h_outer_upper h_store_no_gens_upper h_foreign
        cfg h_cfg_blocks h_cfg_nodup
    refine ⟨σ_cfg, h_step, h_agree, ?_⟩
    intro x h_σ_x h_x_not_accum h_x_not_inits
    have h_x_not_rest : x ∉ Block.initVars rest := by
      intro hx
      apply h_x_not_inits
      simp [Stmt.initVars]; exact hx
    exact h_preserve x h_σ_x h_x_not_accum h_x_not_rest
termination_by sizeOf ss
decreasing_by
  all_goals (subst h_match; simp_wf; omega)

/-- Sibling lemma to `stmtsToBlocks_simulation`: handles the case where the
structured execution `.exiting label` is caught by an entry in `exitConts`.
The CFG-side reaches the labeled continuation `bk_target` (the cont stored
in `exitConts`).

Same accum/agreement/freshness preconditions as `stmtsToBlocks_simulation`.

Used by `.block` simulation when the body exits with the block's matching
label: body's exitConts contains `(some label, kNext) :: outerExitConts`,
so the body's exit resolves to a goto to `kNext`. -/
private theorem stmtsToBlocks_simulation_to_cont {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasBool P] [LawfulHasIdent P]
    [LawfulHasIntOrder P] [LawfulHasNot P]
    {Q : String → Prop}
    (extendEval : ExtendEval P)
    (k : String) (ss : List (Stmt P (Cmd P)))
    (exitConts : List (Option String × String))
    (accum : List (Cmd P))
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : (stmtsToBlocks k ss exitConts accum gen) = ((entry, blocks), gen'))
    (h_nofd : Block.noFuncDecl ss = true)
    (h_simple : Block.simpleShape ss = true)
    (h_unique : Block.uniqueInits ss)
    (h_lbni : Block.loopBodyNoInits ss = true)
    (h_lhni : Block.loopHasNoInvariants ss = true)
    (h_nml : Block.noMeasureLoops ss = true)
    (σ_struct_base σ_base : SemanticStore P)
    (hf_base : Bool)
    (hf_accum : Bool)
    (ρ₀ ρ' : Env P)
    (label : String)
    (bk_target : String)
    (h_label : exitConts.lookup (some label) = some bk_target)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwf_def : WellFormedSemanticEvalDef ρ₀.eval)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (hwf_var : WellFormedSemanticEvalVar ρ₀.eval)
    (h_exit : StepStmtStar P (EvalCmd P) extendEval
      (.stmts ss ρ₀) (.exiting label ρ'))
    (h_accum : EvalCmds P (EvalCmd P) ρ₀.eval σ_struct_base accum.reverse ρ₀.store hf_accum)
    (h_agree_entry : StoreAgreement σ_struct_base σ_base)
    (h_fresh_combined :
      ∀ x ∈ Cmds.definedVars accum.reverse ++ Block.initVars ss, σ_base x = none)
    (h_unique_combined :
      (Cmds.definedVars accum.reverse ++ Block.initVars ss).Nodup)
    (h_hf : ρ₀.hasFailure = (hf_base || hf_accum))
    (h_wf_gen : StringGenState.WF gen)
    (h_combined_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars accum.reverse ++ Block.initVars ss))
    (h_combined_no_gen_suffix_mod :
        NoGenSuffix (P := P) Q (Cmds.modifiedVars accum.reverse ++ transformBlockModVars ss))
    (genUpperBound : StringGenState)
    (h_outer_upper : StringGenState.stringGens gen' ⊆ StringGenState.stringGens genUpperBound)
    (h_store_no_gens_upper : ∀ x : String,
        Q x →
        x ∉ StringGenState.stringGens genUpperBound →
        σ_base (HasIdent.ident (P := P) x) = none)
    (h_foreign : ∀ s : String, ¬ Q s → s ∉ StringGenState.stringGens genUpperBound)
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (h_cfg_blocks : ∀ b ∈ blocks, b ∈ cfg.blocks)
    (h_cfg_nodup : (cfg.blocks.map Prod.fst).Nodup) :
    ∃ σ_cfg, StepDetCFGStar extendEval cfg
      (.atBlock entry σ_base hf_base)
      (.atBlock bk_target σ_cfg ρ'.hasFailure)
      ∧ StoreAgreement ρ'.store σ_cfg
      ∧ (∀ x, σ_base x = none →
          x ∉ Cmds.definedVars accum.reverse → x ∉ Block.initVars ss →
          (∀ s : String, x = HasIdent.ident (P := P) s →
              s ∈ StringGenState.stringGens gen ∨
              s ∉ StringGenState.stringGens gen') →
          σ_cfg x = none) := by
  match h_match : ss with
  | [] =>
    -- Empty stmt list cannot reach .exiting (only .terminal via stmts_nil_terminal-style)
    exfalso
    rcases h_exit with _ | ⟨_, _, _, hstep, hrest⟩
    cases hstep
    cases hrest with
    | step _ _ _ h _ => cases h
  | .cmd c :: rest =>
    -- Same shape as _simulation: head executes, then recurse on rest with _to_cont.
    unfold stmtsToBlocks at h_gen
    -- Decompose `.cmd c :: rest` exit: cmd cannot exit, so it must terminate at ρ₁,
    -- then rest exits.
    have ⟨ρ₁, h_c_star, h_rest_exit⟩ : ∃ ρ₁,
        StepStmtStar P (EvalCmd P) extendEval (.stmts [.cmd c] ρ₀) (.terminal ρ₁) ∧
        StepStmtStar P (EvalCmd P) extendEval (.stmts rest ρ₁) (.exiting label ρ') := by
      cases h_exit with
      | step _ _ _ hstep1 hrest1 =>
        cases hstep1 with
        | step_stmts_cons =>
          have h_seq_inv := seq_reaches_exiting P (EvalCmd P) extendEval hrest1
          rcases h_seq_inv with h_inner_exit | h_term_exit
          · -- Inner is `.stmt (.cmd c) ρ₀` which can only terminate; cannot exit.
            exfalso
            cases h_inner_exit with
            | step _ _ _ hstep2 hrest2 =>
              cases hstep2 with
              | step_cmd _ =>
                cases hrest2 with
                | step _ _ _ h _ => cases h
          · obtain ⟨ρ_mid, h_inner_term, h_rest_exit⟩ := h_term_exit
            -- ρ_mid = ρ₁; .stmt (.cmd c) ρ₀ → .terminal ρ_mid via step_cmd
            -- Then .stmts rest ρ_mid → .exiting label ρ'
            refine ⟨ρ_mid, ?_, h_rest_exit⟩
            -- .stmts [.cmd c] ρ₀ → .stmts [] ρ_mid (via stmts_cons_step) → .terminal ρ_mid (step_stmts_nil)
            have h_stp : StepStmtStar P (EvalCmd P) extendEval
                (.stmts [.cmd c] ρ₀) (.stmts [] ρ_mid) :=
              stmts_cons_step P (EvalCmd P) extendEval (.cmd c) [] ρ₀ ρ_mid h_inner_term
            exact ReflTrans_Transitive _ _ _ _ h_stp
              (.step _ _ _ .step_stmts_nil (.refl _))
    have ⟨σ_c, failed_c, heval_c, hstore_c, heval_eq_c, hfail_c⟩ :=
      single_cmd_eval extendEval c ρ₀ ρ₁ h_c_star
    have h_accum' : EvalCmds P (EvalCmd P) ρ₁.eval σ_struct_base
        (c :: accum).reverse ρ₁.store (hf_accum || failed_c) := by
      simp [List.reverse_cons]
      rw [heval_eq_c, hstore_c]
      exact EvalCmds_snoc ρ₀.eval σ_struct_base ρ₀.store σ_c accum.reverse c hf_accum failed_c
        h_accum heval_c
    have h_hf' : ρ₁.hasFailure = (hf_base || (hf_accum || failed_c)) := by
      rw [hfail_c, h_hf, Bool.or_assoc]
    have hwfb' : WellFormedSemanticEvalBool ρ₁.eval := heval_eq_c ▸ hwfb
    have hwfv' : WellFormedSemanticEvalVal ρ₁.eval := heval_eq_c ▸ hwfv
    have hwf_def' : WellFormedSemanticEvalDef ρ₁.eval := heval_eq_c ▸ hwf_def
    have hwf_congr' : WellFormedSemanticEvalExprCongr ρ₁.eval := heval_eq_c ▸ hwf_congr
    have hwf_var' : WellFormedSemanticEvalVar ρ₁.eval := heval_eq_c ▸ hwf_var
    have h_nofd_rest : Block.noFuncDecl rest = true := by
      simp [Block.noFuncDecl] at h_nofd; exact h_nofd.2
    have h_simple_rest : Block.simpleShape rest = true :=
      (Block.simpleShape_cons_iff.mp h_simple).2
    have h_unique_rest : Block.uniqueInits rest := Block.uniqueInits.tail h_unique
    have h_lbni_rest : Block.loopBodyNoInits rest = true :=
      (Block.loopBodyNoInits_cons_iff.mp h_lbni).2
    have h_lhni_rest : Block.loopHasNoInvariants rest = true :=
      (Block.loopHasNoInvariants_cons_iff.mp h_lhni).2
    have h_nml_rest : Block.noMeasureLoops rest = true :=
      (Block.noMeasureLoops_cons_iff.mp h_nml).2
    -- Snoc/cons rebracketing facts shared between _simulation and _to_cont.
    have ⟨h_definedVars_snoc, h_fresh_combined', h_unique_combined',
          h_combined_no_gen_suffix', h_combined_no_gen_suffix_mod'⟩ :=
      cmd_arm_combined_lemmas c accum rest σ_base
        h_fresh_combined h_unique_combined
        h_combined_no_gen_suffix h_combined_no_gen_suffix_mod
    have ⟨σ_cfg, h_step, h_agree, h_preserve⟩ :=
      stmtsToBlocks_simulation_to_cont extendEval k rest exitConts (c :: accum) gen gen'
        entry blocks h_gen h_nofd_rest h_simple_rest h_unique_rest
        h_lbni_rest h_lhni_rest h_nml_rest
        σ_struct_base σ_base hf_base (hf_accum || failed_c)
        ρ₁ ρ' label bk_target h_label hwfb' hwfv' hwf_def' hwf_congr' hwf_var'
       h_rest_exit h_accum'
        h_agree_entry h_fresh_combined' h_unique_combined' h_hf'
        h_wf_gen h_combined_no_gen_suffix' h_combined_no_gen_suffix_mod'
        genUpperBound h_outer_upper h_store_no_gens_upper h_foreign
        cfg h_cfg_blocks h_cfg_nodup
    refine ⟨σ_cfg, h_step, h_agree, ?_⟩
    intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
    have h_x_not_new_accum : x ∉ Cmds.definedVars (c :: accum).reverse := by
      rw [List.reverse_cons, h_definedVars_snoc]
      intro h_in
      cases List.mem_append.mp h_in with
      | inl h => exact h_x_not_accum h
      | inr h =>
        cases c with
        | init x' _ _ _ =>
          simp [Cmd.definedVars] at h
          subst h
          apply h_x_not_inits
          simp [Stmt.initVars]
        | _ => simp [Cmd.definedVars] at h
    have h_x_not_rest : x ∉ Block.initVars rest := by
      intro h
      apply h_x_not_inits
      rw [Block.initVars]
      cases c <;> simp [Stmt.initVars] <;> first | right; exact h | exact h
    exact h_preserve x h_σ_x h_x_not_new_accum h_x_not_rest h_outer_guard
  | .funcDecl _ _ :: _ =>
    -- Excluded by h_nofd
    simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd
  | .typeDecl tc md :: rest =>
    unfold stmtsToBlocks at h_gen
    -- typeDecl is a no-op in structured semantics; recurse on rest.
    -- Decompose: typeDecl steps to .terminal ρ₀, then rest exits at ρ'.
    have h_rest_exit : StepStmtStar P (EvalCmd P) extendEval
        (.stmts rest ρ₀) (.exiting label ρ') := by
      cases h_exit with
      | step _ _ _ hstep1 hrest1 =>
        cases hstep1 with
        | step_stmts_cons =>
          have h_seq_inv := seq_reaches_exiting P (EvalCmd P) extendEval hrest1
          rcases h_seq_inv with h_inner_exit | h_term_exit
          · -- inner is .stmt (.typeDecl ..) ρ₀; cannot exit.
            exfalso
            cases h_inner_exit with
            | step _ _ _ hstep2 hrest2 =>
              cases hstep2 with
              | step_typeDecl =>
                cases hrest2 with
                | step _ _ _ h _ => cases h
          · obtain ⟨ρ_mid, h_inner_term, h_rest_exit⟩ := h_term_exit
            -- .stmt (.typeDecl ..) ρ₀ → .terminal ρ_mid via step_typeDecl, so ρ_mid = ρ₀.
            cases h_inner_term with
            | step _ _ _ hstep2 hrest2 =>
              cases hstep2 with
              | step_typeDecl =>
                cases hrest2 with
                | refl => exact h_rest_exit
                | step _ _ _ h _ => exact absurd h (by intro h; cases h)
    have h_nofd_rest : Block.noFuncDecl rest = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd
    have h_simple_rest : Block.simpleShape rest = true :=
      (Block.simpleShape_cons_iff.mp h_simple).2
    have h_unique_rest : Block.uniqueInits rest := Block.uniqueInits.tail h_unique
    have h_lbni_rest : Block.loopBodyNoInits rest = true :=
      (Block.loopBodyNoInits_cons_iff.mp h_lbni).2
    have h_lhni_rest : Block.loopHasNoInvariants rest = true :=
      (Block.loopHasNoInvariants_cons_iff.mp h_lhni).2
    have h_nml_rest : Block.noMeasureLoops rest = true :=
      (Block.noMeasureLoops_cons_iff.mp h_nml).2
    have ⟨h_fresh_combined', h_unique_combined',
          h_combined_no_gen_suffix', h_combined_no_gen_suffix_mod'⟩ :=
      typeDecl_arm_combined_lemmas tc md accum rest σ_base
        h_fresh_combined h_unique_combined
        h_combined_no_gen_suffix h_combined_no_gen_suffix_mod
    have ⟨σ_cfg, h_step, h_agree, h_preserve⟩ :=
      stmtsToBlocks_simulation_to_cont extendEval k rest exitConts accum gen gen'
        entry blocks h_gen h_nofd_rest h_simple_rest h_unique_rest
        h_lbni_rest h_lhni_rest h_nml_rest
        σ_struct_base σ_base hf_base hf_accum
        ρ₀ ρ' label bk_target h_label hwfb hwfv hwf_def hwf_congr hwf_var
       h_rest_exit h_accum h_agree_entry
        h_fresh_combined' h_unique_combined' h_hf
        h_wf_gen h_combined_no_gen_suffix' h_combined_no_gen_suffix_mod'
        genUpperBound h_outer_upper h_store_no_gens_upper h_foreign
        cfg h_cfg_blocks h_cfg_nodup
    refine ⟨σ_cfg, h_step, h_agree, ?_⟩
    intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
    have h_x_not_rest : x ∉ Block.initVars rest := by
      intro hx
      apply h_x_not_inits
      simp [Stmt.initVars]; exact hx
    exact h_preserve x h_σ_x h_x_not_accum h_x_not_rest h_outer_guard
  | .exit l' md :: _ =>
    -- The structured side: `.exit l'` produces `.exiting l'`.  For the trace
    -- to reach `.exiting label`, we need `l' = label`.
    -- Also: ρ' = ρ₀ (.exit doesn't modify the environment).
    have h_combined : l' = label ∧ ρ' = ρ₀ := by
      cases h_exit with
      | step _ _ _ hstep1 hrest1 =>
        cases hstep1 with
        | step_stmts_cons =>
          have h_seq_inv := seq_reaches_exiting P (EvalCmd P) extendEval hrest1
          rcases h_seq_inv with h_inner_exit | h_term
          · cases h_inner_exit with
            | step _ _ _ hstep2 hrest2 =>
              cases hstep2 with
              | step_exit =>
                cases hrest2 with
                | refl => exact ⟨rfl, rfl⟩
                | step _ _ _ h _ => cases h
          · obtain ⟨ρ_mid, h_inner_term, _⟩ := h_term
            cases h_inner_term with
            | step _ _ _ hstep2 hrest2 =>
              cases hstep2 with
              | step_exit =>
                cases hrest2 with
                | step _ _ _ h _ => cases h
    obtain ⟨h_l'_eq, h_ρ_eq⟩ := h_combined
    -- We want to keep `label` as the canonical name; rewrite l' → label in h_gen.
    rw [h_l'_eq] at h_gen
    rw [h_ρ_eq]
    -- stmtsToBlocks for .exit label: flushCmds with .some (.goto bk md), where
    -- bk = lookup (.some label) exitConts = bk_target.
    unfold stmtsToBlocks at h_gen
    -- Simplify the lookup using h_label.
    rw [h_label] at h_gen
    simp only at h_gen
    -- Now h_gen : flushCmds "block$..." accum (.some (.goto bk_target md)) bk_target gen
    --             = ((entry, blocks), gen')
    have h_fresh_accum : ∀ x ∈ Cmds.definedVars accum.reverse, σ_base x = none := by
      intro x hx
      apply h_fresh_combined
      apply List.mem_append_left
      exact hx
    have h_unique_accum : (Cmds.definedVars accum.reverse).Nodup :=
      (List.nodup_append.mp h_unique_combined).1
    have ⟨σ_cfg, h_step, h_agree, h_preserve⟩ :=
      flushCmds_goto_simulation_agree extendEval (s!"block${label}$") accum md bk_target
        gen gen' entry blocks h_gen σ_struct_base σ_base hf_base hf_accum ρ₀
        hwfb hwfv hwf_def hwf_congr h_accum h_agree_entry h_fresh_accum h_unique_accum h_hf
        cfg h_cfg_blocks h_cfg_nodup
    refine ⟨σ_cfg, h_step, h_agree, ?_⟩
    intro x h_σ_x h_x_not_accum _ _
    exact h_preserve x h_σ_x h_x_not_accum
  | .block label' body md :: rest =>
    simp only [stmtsToBlocks, bind, StateT.bind, pure] at h_gen
    -- Decompose the monadic chain
    generalize h_rest_eq : stmtsToBlocks k rest exitConts [] gen = r_rest at h_gen
    obtain ⟨⟨kNext, bsNext⟩, gen_r⟩ := r_rest
    simp at h_gen
    generalize h_body_eq : stmtsToBlocks kNext body
      ((some label', kNext) :: exitConts) [] gen_r = r_body at h_gen
    obtain ⟨⟨bl, bbs⟩, gen_b⟩ := r_body
    simp at h_gen
    generalize h_flush_eq : @flushCmds P (Cmd P) _ "blk$" accum .none bl gen_b
      = r_flush at h_gen
    obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
    -- Decompose `.stmts (.block label' body md :: rest) ρ₀ → .exiting label ρ'`.
    -- Two cases via seq_reaches_exiting on the inner-step:
    --   (A) `.stmt (.block ..) ρ₀ → .exiting label ρ'` (block propagates exit;
    --       requires label' ≠ label, body exits with `label`, rest does not run).
    --   (B) `.stmt (.block ..) ρ₀ → .terminal ρ_blk` then
    --       `.stmts rest ρ_blk → .exiting label ρ'`.  Body either terminates
    --       (B1) or exits matching `label'` (B2).
    have h_decomp :
        -- (A): body exits with `label`, label' ≠ label, ρ' is projected.
        (label' ≠ label ∧
         ∃ ρ_inner, StepStmtStar P (EvalCmd P) extendEval
            (.stmts body ρ₀) (.exiting label ρ_inner) ∧
          ρ' = { ρ_inner with store := projectStore ρ₀.store ρ_inner.store }) ∨
        -- (B): block terminates then rest exits.
        (∃ ρ_blk, ((∃ ρ_inner, StepStmtStar P (EvalCmd P) extendEval
              (.stmts body ρ₀) (.terminal ρ_inner) ∧
            ρ_blk = { ρ_inner with store := projectStore ρ₀.store ρ_inner.store }) ∨
          (∃ ρ_inner, StepStmtStar P (EvalCmd P) extendEval
              (.stmts body ρ₀) (.exiting label' ρ_inner) ∧
            ρ_blk = { ρ_inner with store := projectStore ρ₀.store ρ_inner.store })) ∧
          StepStmtStar P (EvalCmd P) extendEval (.stmts rest ρ_blk) (.exiting label ρ')) := by
      cases h_exit with
      | step _ _ _ hstep1 hrest1 =>
        cases hstep1 with
        | step_stmts_cons =>
          have h_seq_inv := seq_reaches_exiting P (EvalCmd P) extendEval hrest1
          rcases h_seq_inv with h_inner_exit | h_term_exit
          · -- inner = .stmt (.block ..) ρ₀ → .exiting label ρ'
            cases h_inner_exit with
            | step _ _ _ hstep2 hrest2 =>
              cases hstep2 with
              | step_block =>
                -- hrest2 : .block (.some label') ρ₀.store (.stmts body ρ₀) → .exiting label ρ'
                have ⟨h_ne, ρ_inner, h_body_exit, h_eq⟩ :=
                  block_some_reaches_exiting hrest2
                exact Or.inl ⟨h_ne, ρ_inner, h_body_exit, h_eq⟩
          · obtain ⟨ρ_blk, h_inner_term, h_rest_exit⟩ := h_term_exit
            cases h_inner_term with
            | step _ _ _ hstep2 hrest2 =>
              cases hstep2 with
              | step_block =>
                -- hrest2 : .block (.some label') ρ₀.store (.stmts body ρ₀) → .terminal ρ_blk
                have h_blk_inv := block_some_reaches_terminal P (EvalCmd P) extendEval hrest2
                rcases h_blk_inv with h_term | h_match
                · obtain ⟨ρ_i, h_body_term, heq⟩ := h_term
                  exact Or.inr ⟨ρ_blk, Or.inl ⟨ρ_i, h_body_term, heq⟩, h_rest_exit⟩
                · obtain ⟨ρ_i, h_body_match, heq⟩ := h_match
                  exact Or.inr ⟨ρ_blk, Or.inr ⟨ρ_i, h_body_match, heq⟩, h_rest_exit⟩
    -- noFuncDecl projections.
    have h_nofd_body : Block.noFuncDecl body = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.1
    have h_nofd_rest : Block.noFuncDecl rest = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.2
    -- simpleShape projections.
    have h_simple_head : Stmt.simpleShape (.block label' body md) = true :=
      (Block.simpleShape_cons_iff.mp h_simple).1
    have h_simple_rest : Block.simpleShape rest = true :=
      (Block.simpleShape_cons_iff.mp h_simple).2
    have h_simple_body : Block.simpleShape body = true := by
      simp only [Stmt.simpleShape] at h_simple_head; exact h_simple_head
    -- loopBodyNoInits/loopHasNoInvariants/noMeasureLoops projections for body and rest.
    have h_lbni_head : Stmt.loopBodyNoInits (.block label' body md) = true :=
      (Block.loopBodyNoInits_cons_iff.mp h_lbni).1
    have h_lbni_rest : Block.loopBodyNoInits rest = true :=
      (Block.loopBodyNoInits_cons_iff.mp h_lbni).2
    have h_lbni_body : Block.loopBodyNoInits body = true :=
      Stmt.loopBodyNoInits_block_body h_lbni_head
    have h_lhni_head : Stmt.loopHasNoInvariants (.block label' body md) = true :=
      (Block.loopHasNoInvariants_cons_iff.mp h_lhni).1
    have h_lhni_rest : Block.loopHasNoInvariants rest = true :=
      (Block.loopHasNoInvariants_cons_iff.mp h_lhni).2
    have h_lhni_body : Block.loopHasNoInvariants body = true :=
      Stmt.loopHasNoInvariants_block_body h_lhni_head
    have h_nml_head : Stmt.noMeasureLoops (.block label' body md) = true :=
      (Block.noMeasureLoops_cons_iff.mp h_nml).1
    have h_nml_rest : Block.noMeasureLoops rest = true :=
      (Block.noMeasureLoops_cons_iff.mp h_nml).2
    have h_nml_body : Block.noMeasureLoops body = true :=
      Stmt.noMeasureLoops_block_body h_nml_head
    have h_unique_body : Block.uniqueInits body :=
      Block.uniqueInits.block_body h_unique
    have h_unique_rest : Block.uniqueInits rest := Block.uniqueInits.tail h_unique
    have h_initvars_eq :
        Block.initVars (Stmt.block label' body md :: rest) =
        Block.initVars body ++ Block.initVars rest := by
      rw [Block.initVars]
      simp
    -- Sub-block and rest combined-no-gen-suffix discharges.
    have h_body_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars [].reverse ++ Block.initVars body) := fun x hx s heq =>
      h_combined_no_gen_suffix x (List.mem_append_right _ (h_initvars_eq ▸
        List.mem_append_left _ (by simpa [Cmds.definedVars] using hx))) s heq
    have h_rest_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars [].reverse ++ Block.initVars rest) := fun x hx s heq =>
      h_combined_no_gen_suffix x (List.mem_append_right _ (h_initvars_eq ▸
        List.mem_append_right _ (by simpa [Cmds.definedVars] using hx))) s heq
    -- Mirror of h_initvars_eq / no_gen_suffix discharges for modifiedVars.
    have h_modvars_eq :
        transformBlockModVars (Stmt.block label' body md :: rest) =
        transformBlockModVars body ++ transformBlockModVars rest := by
      rw [transformBlockModVars_cons, transformStmtModVars_block]
    have h_body_no_gen_suffix_mod :
        NoGenSuffix (P := P) Q (Cmds.modifiedVars [].reverse ++ transformBlockModVars body) := fun x hx s heq =>
      h_combined_no_gen_suffix_mod x (List.mem_append_right _ (h_modvars_eq ▸
        List.mem_append_left _ (by simpa [Cmds.modifiedVars] using hx))) s heq
    have h_rest_no_gen_suffix_mod :
        NoGenSuffix (P := P) Q (Cmds.modifiedVars [].reverse ++ transformBlockModVars rest) := fun x hx s heq =>
      h_combined_no_gen_suffix_mod x (List.mem_append_right _ (h_modvars_eq ▸
        List.mem_append_right _ (by simpa [Cmds.modifiedVars] using hx))) s heq
    -- GenStep chains for WF and subset (block case).
    have h_step_b_to_f : StringGenState.GenStep gen_b gen_f :=
      flushCmds_genStep _ _ _ _ _ _ _ _ h_flush_eq
    have h_step_r_to_b : StringGenState.GenStep gen_r gen_b :=
      stmtsToBlocks_genStep _ _ _ _ _ _ _ _ h_body_eq
    have h_step_gen_to_r : StringGenState.GenStep gen gen_r :=
      stmtsToBlocks_genStep _ _ _ _ _ _ _ _ h_rest_eq
    have h_step_gen_to_b : StringGenState.GenStep gen gen_b :=
      h_step_gen_to_r.trans h_step_r_to_b
    have h_wf_r : StringGenState.WF gen_r := h_step_gen_to_r.wf_mono h_wf_gen
    have h_wf_b : StringGenState.WF gen_b := h_step_gen_to_b.wf_mono h_wf_gen
    -- Block membership distribution. Split on l = bl vs l ≠ bl.
    by_cases h_l_eq_bl : label' = bl
    · -- Case label' = bl: blocks = accumBlocks ++ bbs ++ bsNext, entry = accumEntry.
      simp [h_l_eq_bl] at h_gen
      have h_entry_eq : accumEntry = entry :=
        (Prod.mk.inj (Prod.mk.inj h_gen).1).1
      have h_blocks_eq : accumBlocks ++ (bbs ++ bsNext) = blocks :=
        (Prod.mk.inj (Prod.mk.inj h_gen).1).2
      have h_gen_eq_f : gen_f = gen' := (Prod.mk.inj h_gen).2
      subst h_entry_eq
      subst h_blocks_eq
      have h_outer_upper_b : StringGenState.stringGens gen_b ⊆ StringGenState.stringGens genUpperBound :=
        h_step_b_to_f.subset.trans (h_gen_eq_f ▸ h_outer_upper)
      have h_outer_upper_r : StringGenState.stringGens gen_r ⊆ StringGenState.stringGens genUpperBound :=
        h_step_r_to_b.subset.trans h_outer_upper_b
      have h_cfg_accum : ∀ b ∈ accumBlocks, b ∈ cfg.blocks := fun b hb =>
        h_cfg_blocks b (List.mem_append_left _ hb)
      have h_cfg_bbs : ∀ b ∈ bbs, b ∈ cfg.blocks := fun b hb =>
        h_cfg_blocks b (List.mem_append_right _ (List.mem_append_left _ hb))
      have h_cfg_rest : ∀ b ∈ bsNext, b ∈ cfg.blocks := fun b hb =>
        h_cfg_blocks b (List.mem_append_right _ (List.mem_append_right _ hb))
      have h_fresh_accum : ∀ x ∈ Cmds.definedVars accum.reverse, σ_base x = none := by
        intro x hx
        exact h_fresh_combined x (List.mem_append_left _ hx)
      have h_unique_accum : (Cmds.definedVars accum.reverse).Nodup :=
        (List.nodup_append.mp h_unique_combined).1
      have ⟨σ_cfg_after, h_step_flush, h_agree_after, h_preserve_flush⟩ :=
        flushCmds_simulation_agree extendEval "blk$" bl accum gen_b gen_f accumEntry
          accumBlocks h_flush_eq σ_struct_base σ_base hf_base hf_accum ρ₀
          hwfb hwfv hwf_def hwf_congr h_accum h_agree_entry h_fresh_accum h_unique_accum
          h_hf cfg h_cfg_accum h_cfg_nodup
      have h_store_no_gens_upper_after :
          ∀ x : String, Q x →
            x ∉ StringGenState.stringGens genUpperBound →
            σ_cfg_after (HasIdent.ident (P := P) x) = none :=
        store_no_gens_lift_after_flush h_preserve_flush genUpperBound h_store_no_gens_upper
          (fun x hx => h_combined_no_gen_suffix x (List.mem_append_left _ hx))
      rcases h_decomp with h_caseA | h_caseB
      · -- (A) Body exits with `label`, label' ≠ label.  Use _to_cont on body.
        obtain ⟨h_label_ne, ρ_inner, h_body_exit, h_ρ'_eq⟩ := h_caseA
        -- Body's exitConts: ((some label', kNext) :: exitConts).
        -- Lookup of (some label) yields exitConts.lookup (some label) = bk_target.
        have h_label_lookup :
            ((some label', kNext) :: exitConts).lookup (some label) = some bk_target := by
          show (match label == label' with
                | true => some kNext
                | false => List.lookup (some label) exitConts) = some bk_target
          have h_beq : (label == label') = false := by
            rw [beq_eq_false_iff_ne]; intro h; exact h_label_ne h.symm
          rw [h_beq]; exact h_label
        -- Freshness for body recursion at σ_cfg_after.
        have h_fresh_body_inits_after : ∀ x ∈ Block.initVars body, σ_cfg_after x = none :=
          (fresh_inits_after_step h_initvars_eq h_unique_combined h_fresh_combined
            h_preserve_flush).1
        have h_combined_body :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
            σ_cfg_after x = none :=
          fun x hx => h_fresh_body_inits_after x (by simpa [Cmds.definedVars] using hx)
        have h_unique_combined_body :
            (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
          simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_body
        have h_accum_nil : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        -- Recurse on body with _to_cont (target = bk_target).
        have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
          stmtsToBlocks_simulation_to_cont extendEval kNext body
            ((some label', kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
            h_nofd_body h_simple_body h_unique_body
            h_lbni_body h_lhni_body h_nml_body
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ_inner label bk_target h_label_lookup hwfb hwfv hwf_def hwf_congr hwf_var
            h_body_exit h_accum_nil h_agree_after
            h_combined_body h_unique_combined_body (by simp)
            h_wf_r h_body_no_gen_suffix h_body_no_gen_suffix_mod
            genUpperBound h_outer_upper_b h_store_no_gens_upper_after h_foreign
            cfg h_cfg_bbs h_cfg_nodup
        -- Bridge structured-side projection to CFG.
        have h_agree_ρ' : StoreAgreement ρ'.store σ_cfg_body :=
          StoreAgreement.through_projectStore h_ρ'_eq h_agree_body
        refine ⟨σ_cfg_body, ?_, h_agree_ρ', ?_⟩
        · -- Compose: entry → bl (flush) → bk_target. Transport h_step_body from
          -- ρ_inner.hasFailure to ρ'.hasFailure (equal since projectStore preserves hasFailure).
          have h_hasFail_ρ' : ρ'.hasFailure = ρ_inner.hasFailure := by rw [h_ρ'_eq]
          exact StepDetCFGStar_trans h_step_flush (h_hasFail_ρ'.symm ▸ h_step_body)
        · intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
          have h_x_not_body : x ∉ Block.initVars body := fun hx =>
            h_x_not_inits (h_initvars_eq ▸ List.mem_append_left _ hx)
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          -- Build inner guard at (gen_r, gen_b) from outer guard at (gen, gen').
          have h_inner_guard_b :=
            inner_guard_step_b h_step_gen_to_r h_step_b_to_f h_gen_eq_f h_outer_guard
          exact h_preserve_body x h_σ_after_x h_nil_not h_x_not_body h_inner_guard_b
      · -- (B) Block terminates with ρ_blk, then rest exits.
        obtain ⟨ρ_blk, h_body_or_match, h_rest_exit⟩ := h_caseB
        -- Freshness for body recursion at σ_cfg_after.
        have h_fresh_body_inits_after : ∀ x ∈ Block.initVars body, σ_cfg_after x = none :=
          (fresh_inits_after_step h_initvars_eq h_unique_combined h_fresh_combined
            h_preserve_flush).1
        have h_combined_body :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
            σ_cfg_after x = none :=
          fun x hx => h_fresh_body_inits_after x (by simpa [Cmds.definedVars] using hx)
        have h_unique_combined_body :
            (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
          simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_body
        have h_accum_nil : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have h_hf_body : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
        have h_label_lookup :
            ((some label', kNext) :: exitConts).lookup (some label') = some kNext := by
          simp [List.lookup]
        -- Run body to σ_cfg_body via either _simulation (terminate) or _to_cont (match exit).
        -- Use a manual case-split to avoid binding ρ_inner with elaboration ambiguity.
        rcases h_body_or_match with h_term | h_match_branch
        · obtain ⟨ρ_inner, h_body_term, h_ρ_blk_eq⟩ := h_term
          have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
            stmtsToBlocks_simulation extendEval kNext body
              ((some label', kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
              h_nofd_body h_simple_body h_unique_body
            h_lbni_body h_lhni_body h_nml_body
              ρ₀.store σ_cfg_after ρ₀.hasFailure false
              ρ₀ ρ_inner hwfb hwfv hwf_def hwf_congr hwf_var
              h_body_term h_accum_nil h_agree_after
              h_combined_body h_unique_combined_body h_hf_body
              h_wf_r h_body_no_gen_suffix h_body_no_gen_suffix_mod
              genUpperBound h_outer_upper_b h_store_no_gens_upper_after h_foreign
              cfg h_cfg_bbs h_cfg_nodup
          have h_agree_block_body : StoreAgreement ρ_blk.store σ_cfg_body :=
            StoreAgreement.through_projectStore h_ρ_blk_eq h_agree_body
          have h_eval_blk : ρ_blk.eval = ρ₀.eval := by
            rw [h_ρ_blk_eq]
            exact smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
              body ρ₀ ρ_inner h_nofd_body h_body_term
          have hwfb₁ : WellFormedSemanticEvalBool ρ_blk.eval := h_eval_blk ▸ hwfb
          have hwfv₁ : WellFormedSemanticEvalVal ρ_blk.eval := h_eval_blk ▸ hwfv
          have hwf_def₁ : WellFormedSemanticEvalDef ρ_blk.eval := h_eval_blk ▸ hwf_def
          have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_blk.eval := h_eval_blk ▸ hwf_congr
          have hwf_var₁ : WellFormedSemanticEvalVar ρ_blk.eval := h_eval_blk ▸ hwf_var
          have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none :=
            (fresh_inits_after_step h_initvars_eq h_unique_combined h_fresh_combined
              h_preserve_flush).2
          have h_fresh_rest_inits_body : ∀ x ∈ Block.initVars rest, σ_cfg_body x = none :=
            fresh_rest_inits_body_step h_initvars_eq h_unique h_preserve_body
            (fun s hns h_in => h_foreign s hns (h_outer_upper_b h_in))
              h_rest_no_gen_suffix h_fresh_rest_inits_after
          have h_combined_rest :
              ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
              σ_cfg_body x = none := fun x hx =>
            h_fresh_rest_inits_body x (by simpa [Cmds.definedVars] using hx)
          have h_unique_combined_rest :
              (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
            simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_rest
          have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_blk.eval ρ_blk.store
              [].reverse ρ_blk.store false := EvalCmds.eval_cmds_none
          have h_hasFail_blk : ρ_blk.hasFailure = ρ_inner.hasFailure := by
            rw [h_ρ_blk_eq]
          -- Lift `h_store_no_gens_upper` through the body sub-simulation
          -- using the strengthened (4-premise) `h_preserve_body` directly.
          have h_store_no_gens_upper_body :
              ∀ x : String, Q x →
                x ∉ StringGenState.stringGens genUpperBound →
                σ_cfg_body (HasIdent.ident (P := P) x) = none :=
            store_no_gens_upper_lift_through_subsim gen_r gen_b genUpperBound
              h_outer_upper_b h_preserve_body h_store_no_gens_upper_after
              (fun x hx s heq => h_body_no_gen_suffix x (List.mem_append_right _ hx) s heq)
          have ⟨σ_cfg_rest, h_step_rest, h_agree_rest, h_preserve_rest⟩ :=
            stmtsToBlocks_simulation_to_cont extendEval k rest exitConts [] gen gen_r kNext bsNext
              h_rest_eq h_nofd_rest h_simple_rest h_unique_rest
              h_lbni_rest h_lhni_rest h_nml_rest ρ_blk.store σ_cfg_body
              ρ_blk.hasFailure false ρ_blk ρ' label bk_target h_label
              hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁ hwf_var₁
              h_rest_exit h_accum_nil_r h_agree_block_body
              h_combined_rest h_unique_combined_rest (by simp)
              h_wf_gen h_rest_no_gen_suffix h_rest_no_gen_suffix_mod
              genUpperBound h_outer_upper_r h_store_no_gens_upper_body h_foreign
              cfg h_cfg_rest h_cfg_nodup
          refine ⟨σ_cfg_rest, ?_, h_agree_rest, ?_⟩
          · -- Transport h_step_body from ρ_inner.hasFailure to ρ_blk.hasFailure.
            exact StepDetCFGStar_trans
              (StepDetCFGStar_trans h_step_flush (h_hasFail_blk.symm ▸ h_step_body)) h_step_rest
          · intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
            have h_x_not_body : x ∉ Block.initVars body := fun hx =>
              h_x_not_inits (h_initvars_eq ▸ List.mem_append_left _ hx)
            have h_x_not_rest : x ∉ Block.initVars rest := fun hx =>
              h_x_not_inits (h_initvars_eq ▸ List.mem_append_right _ hx)
            have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
            have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
            -- Build inner guards from outer guard via GenStep monotonicity.
            have h_inner_guard_b :=
              inner_guard_step_b h_step_gen_to_r h_step_b_to_f h_gen_eq_f h_outer_guard
            have h_inner_guard_r :=
              inner_guard_step_r h_step_b_to_f h_step_r_to_b h_gen_eq_f h_outer_guard
            have h_σ_body_x : σ_cfg_body x = none :=
              h_preserve_body x h_σ_after_x h_nil_not h_x_not_body h_inner_guard_b
            exact h_preserve_rest x h_σ_body_x h_nil_not h_x_not_rest h_inner_guard_r
        · obtain ⟨ρ_inner, h_body_match, h_ρ_blk_eq⟩ := h_match_branch
          have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
            stmtsToBlocks_simulation_to_cont extendEval kNext body
              ((some label', kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
              h_nofd_body h_simple_body h_unique_body
            h_lbni_body h_lhni_body h_nml_body
              ρ₀.store σ_cfg_after ρ₀.hasFailure false
              ρ₀ ρ_inner label' kNext h_label_lookup hwfb hwfv hwf_def hwf_congr hwf_var
              h_body_match h_accum_nil h_agree_after
              h_combined_body h_unique_combined_body h_hf_body
              h_wf_r h_body_no_gen_suffix h_body_no_gen_suffix_mod
              genUpperBound h_outer_upper_b h_store_no_gens_upper_after h_foreign
              cfg h_cfg_bbs h_cfg_nodup
          have h_agree_block_body : StoreAgreement ρ_blk.store σ_cfg_body :=
            StoreAgreement.through_projectStore h_ρ_blk_eq h_agree_body
          have h_eval_blk : ρ_blk.eval = ρ₀.eval := by
            rw [h_ρ_blk_eq]
            exact smallStep_noFuncDecl_preserves_eval_block_exiting P (EvalCmd P) extendEval
              body ρ₀ ρ_inner label' h_nofd_body h_body_match
          have hwfb₁ : WellFormedSemanticEvalBool ρ_blk.eval := h_eval_blk ▸ hwfb
          have hwfv₁ : WellFormedSemanticEvalVal ρ_blk.eval := h_eval_blk ▸ hwfv
          have hwf_def₁ : WellFormedSemanticEvalDef ρ_blk.eval := h_eval_blk ▸ hwf_def
          have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_blk.eval := h_eval_blk ▸ hwf_congr
          have hwf_var₁ : WellFormedSemanticEvalVar ρ_blk.eval := h_eval_blk ▸ hwf_var
          have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none :=
            (fresh_inits_after_step h_initvars_eq h_unique_combined h_fresh_combined
              h_preserve_flush).2
          have h_fresh_rest_inits_body : ∀ x ∈ Block.initVars rest, σ_cfg_body x = none :=
            fresh_rest_inits_body_step h_initvars_eq h_unique h_preserve_body
            (fun s hns h_in => h_foreign s hns (h_outer_upper_b h_in))
              h_rest_no_gen_suffix h_fresh_rest_inits_after
          have h_combined_rest :
              ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
              σ_cfg_body x = none := fun x hx =>
            h_fresh_rest_inits_body x (by simpa [Cmds.definedVars] using hx)
          have h_unique_combined_rest :
              (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
            simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_rest
          have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_blk.eval ρ_blk.store
              [].reverse ρ_blk.store false := EvalCmds.eval_cmds_none
          have h_hasFail_blk : ρ_blk.hasFailure = ρ_inner.hasFailure := by
            rw [h_ρ_blk_eq]
          -- Lift `h_store_no_gens_upper` through the body sub-simulation
          -- using the strengthened (4-premise) `h_preserve_body` directly.
          have h_store_no_gens_upper_body :
              ∀ x : String, Q x →
                x ∉ StringGenState.stringGens genUpperBound →
                σ_cfg_body (HasIdent.ident (P := P) x) = none :=
            store_no_gens_upper_lift_through_subsim gen_r gen_b genUpperBound
              h_outer_upper_b h_preserve_body h_store_no_gens_upper_after
              (fun x hx s heq => h_body_no_gen_suffix x (List.mem_append_right _ hx) s heq)
          have ⟨σ_cfg_rest, h_step_rest, h_agree_rest, h_preserve_rest⟩ :=
            stmtsToBlocks_simulation_to_cont extendEval k rest exitConts [] gen gen_r kNext bsNext
              h_rest_eq h_nofd_rest h_simple_rest h_unique_rest
              h_lbni_rest h_lhni_rest h_nml_rest ρ_blk.store σ_cfg_body
              ρ_blk.hasFailure false ρ_blk ρ' label bk_target h_label
              hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁ hwf_var₁
              h_rest_exit h_accum_nil_r h_agree_block_body
              h_combined_rest h_unique_combined_rest (by simp)
              h_wf_gen h_rest_no_gen_suffix h_rest_no_gen_suffix_mod
              genUpperBound h_outer_upper_r h_store_no_gens_upper_body h_foreign
              cfg h_cfg_rest h_cfg_nodup
          refine ⟨σ_cfg_rest, ?_, h_agree_rest, ?_⟩
          · -- Transport h_step_body from ρ_inner.hasFailure to ρ_blk.hasFailure.
            exact StepDetCFGStar_trans
              (StepDetCFGStar_trans h_step_flush (h_hasFail_blk.symm ▸ h_step_body)) h_step_rest
          · intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
            have h_x_not_body : x ∉ Block.initVars body := fun hx =>
              h_x_not_inits (h_initvars_eq ▸ List.mem_append_left _ hx)
            have h_x_not_rest : x ∉ Block.initVars rest := fun hx =>
              h_x_not_inits (h_initvars_eq ▸ List.mem_append_right _ hx)
            have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
            have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
            -- Build inner guards from outer guard via GenStep monotonicity.
            have h_inner_guard_b :=
              inner_guard_step_b h_step_gen_to_r h_step_b_to_f h_gen_eq_f h_outer_guard
            have h_inner_guard_r :=
              inner_guard_step_r h_step_b_to_f h_step_r_to_b h_gen_eq_f h_outer_guard
            have h_σ_body_x : σ_cfg_body x = none :=
              h_preserve_body x h_σ_after_x h_nil_not h_x_not_body h_inner_guard_b
            exact h_preserve_rest x h_σ_body_x h_nil_not h_x_not_rest h_inner_guard_r
    · -- Case label' ≠ bl: blocks = accumBlocks ++ (label', lBlk) :: (bbs ++ bsNext),
      -- entry = accumEntry.  Same flow as label' = bl plus a vestigial (label', goto bl) block.
      simp [h_l_eq_bl] at h_gen
      have h_entry_eq : accumEntry = entry :=
        (Prod.mk.inj (Prod.mk.inj h_gen).1).1
      let lBlk : DetBlock String (Cmd P) P :=
        { cmds := [], transfer := DetTransferCmd.goto bl md }
      have h_blocks_eq :
          accumBlocks ++ (label', lBlk) :: (bbs ++ bsNext) = blocks :=
        (Prod.mk.inj (Prod.mk.inj h_gen).1).2
      have h_gen_eq_f : gen_f = gen' := (Prod.mk.inj h_gen).2
      subst h_entry_eq
      have h_outer_upper_b : StringGenState.stringGens gen_b ⊆ StringGenState.stringGens genUpperBound :=
        h_step_b_to_f.subset.trans (h_gen_eq_f ▸ h_outer_upper)
      have h_outer_upper_r : StringGenState.stringGens gen_r ⊆ StringGenState.stringGens genUpperBound :=
        h_step_r_to_b.subset.trans h_outer_upper_b
      have h_cfg_accum : ∀ b ∈ accumBlocks, b ∈ cfg.blocks := by
        intro b hb
        exact h_cfg_blocks b (h_blocks_eq ▸ List.mem_append_left _ hb)
      have h_cfg_bbs : ∀ b ∈ bbs, b ∈ cfg.blocks := by
        intro b hb
        exact h_cfg_blocks b
          (h_blocks_eq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hb)))
      have h_cfg_rest : ∀ b ∈ bsNext, b ∈ cfg.blocks := by
        intro b hb
        exact h_cfg_blocks b
          (h_blocks_eq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ hb)))
      have h_fresh_accum : ∀ x ∈ Cmds.definedVars accum.reverse, σ_base x = none := by
        intro x hx
        exact h_fresh_combined x (List.mem_append_left _ hx)
      have h_unique_accum : (Cmds.definedVars accum.reverse).Nodup :=
        (List.nodup_append.mp h_unique_combined).1
      have ⟨σ_cfg_after, h_step_flush, h_agree_after, h_preserve_flush⟩ :=
        flushCmds_simulation_agree extendEval "blk$" bl accum gen_b gen_f accumEntry
          accumBlocks h_flush_eq σ_struct_base σ_base hf_base hf_accum ρ₀
          hwfb hwfv hwf_def hwf_congr h_accum h_agree_entry h_fresh_accum h_unique_accum
          h_hf cfg h_cfg_accum h_cfg_nodup
      have h_store_no_gens_upper_after :
          ∀ x : String, Q x →
            x ∉ StringGenState.stringGens genUpperBound →
            σ_cfg_after (HasIdent.ident (P := P) x) = none :=
        store_no_gens_lift_after_flush h_preserve_flush genUpperBound h_store_no_gens_upper
          (fun x hx => h_combined_no_gen_suffix x (List.mem_append_left _ hx))
      rcases h_decomp with h_caseA | h_caseB
      · obtain ⟨h_label_ne, ρ_inner, h_body_exit, h_ρ'_eq⟩ := h_caseA
        have h_label_lookup :
            ((some label', kNext) :: exitConts).lookup (some label) = some bk_target := by
          show (match label == label' with
                | true => some kNext
                | false => List.lookup (some label) exitConts) = some bk_target
          have h_beq : (label == label') = false := by
            rw [beq_eq_false_iff_ne]; intro h; exact h_label_ne h.symm
          rw [h_beq]; exact h_label
        have h_fresh_body_inits_after : ∀ x ∈ Block.initVars body, σ_cfg_after x = none :=
          (fresh_inits_after_step h_initvars_eq h_unique_combined h_fresh_combined
            h_preserve_flush).1
        have h_combined_body :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
            σ_cfg_after x = none :=
          fun x hx => h_fresh_body_inits_after x (by simpa [Cmds.definedVars] using hx)
        have h_unique_combined_body :
            (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
          simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_body
        have h_accum_nil : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
          stmtsToBlocks_simulation_to_cont extendEval kNext body
            ((some label', kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
            h_nofd_body h_simple_body h_unique_body
            h_lbni_body h_lhni_body h_nml_body
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ_inner label bk_target h_label_lookup hwfb hwfv hwf_def hwf_congr hwf_var
            h_body_exit h_accum_nil h_agree_after
            h_combined_body h_unique_combined_body (by simp)
            h_wf_r h_body_no_gen_suffix h_body_no_gen_suffix_mod
            genUpperBound h_outer_upper_b h_store_no_gens_upper_after h_foreign
            cfg h_cfg_bbs h_cfg_nodup
        have h_agree_ρ' : StoreAgreement ρ'.store σ_cfg_body :=
          StoreAgreement.through_projectStore h_ρ'_eq h_agree_body
        refine ⟨σ_cfg_body, ?_, h_agree_ρ', ?_⟩
        · -- Transport h_step_body from ρ_inner.hasFailure to ρ'.hasFailure.
          have h_hasFail_ρ' : ρ'.hasFailure = ρ_inner.hasFailure := by rw [h_ρ'_eq]
          exact StepDetCFGStar_trans h_step_flush (h_hasFail_ρ'.symm ▸ h_step_body)
        · intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
          have h_x_not_body : x ∉ Block.initVars body := fun hx =>
            h_x_not_inits (h_initvars_eq ▸ List.mem_append_left _ hx)
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          -- Build inner guard at (gen_r, gen_b) from outer guard at (gen, gen').
          have h_inner_guard_b :=
            inner_guard_step_b h_step_gen_to_r h_step_b_to_f h_gen_eq_f h_outer_guard
          exact h_preserve_body x h_σ_after_x h_nil_not h_x_not_body h_inner_guard_b
      · obtain ⟨ρ_blk, h_body_or_match, h_rest_exit⟩ := h_caseB
        have h_fresh_body_inits_after : ∀ x ∈ Block.initVars body, σ_cfg_after x = none :=
          (fresh_inits_after_step h_initvars_eq h_unique_combined h_fresh_combined
            h_preserve_flush).1
        have h_combined_body :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
            σ_cfg_after x = none :=
          fun x hx => h_fresh_body_inits_after x (by simpa [Cmds.definedVars] using hx)
        have h_unique_combined_body :
            (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
          simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_body
        have h_accum_nil : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have h_hf_body : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
        have h_label_lookup :
            ((some label', kNext) :: exitConts).lookup (some label') = some kNext := by
          simp [List.lookup]
        rcases h_body_or_match with h_term | h_match_branch
        · obtain ⟨ρ_inner, h_body_term, h_ρ_blk_eq⟩ := h_term
          have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
            stmtsToBlocks_simulation extendEval kNext body
              ((some label', kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
              h_nofd_body h_simple_body h_unique_body
            h_lbni_body h_lhni_body h_nml_body
              ρ₀.store σ_cfg_after ρ₀.hasFailure false
              ρ₀ ρ_inner hwfb hwfv hwf_def hwf_congr hwf_var
              h_body_term h_accum_nil h_agree_after
              h_combined_body h_unique_combined_body h_hf_body
              h_wf_r h_body_no_gen_suffix h_body_no_gen_suffix_mod
              genUpperBound h_outer_upper_b h_store_no_gens_upper_after h_foreign
              cfg h_cfg_bbs h_cfg_nodup
          have h_agree_block_body : StoreAgreement ρ_blk.store σ_cfg_body :=
            StoreAgreement.through_projectStore h_ρ_blk_eq h_agree_body
          have h_eval_blk : ρ_blk.eval = ρ₀.eval := by
            rw [h_ρ_blk_eq]
            exact smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
              body ρ₀ ρ_inner h_nofd_body h_body_term
          have hwfb₁ : WellFormedSemanticEvalBool ρ_blk.eval := h_eval_blk ▸ hwfb
          have hwfv₁ : WellFormedSemanticEvalVal ρ_blk.eval := h_eval_blk ▸ hwfv
          have hwf_def₁ : WellFormedSemanticEvalDef ρ_blk.eval := h_eval_blk ▸ hwf_def
          have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_blk.eval := h_eval_blk ▸ hwf_congr
          have hwf_var₁ : WellFormedSemanticEvalVar ρ_blk.eval := h_eval_blk ▸ hwf_var
          have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none :=
            (fresh_inits_after_step h_initvars_eq h_unique_combined h_fresh_combined
              h_preserve_flush).2
          have h_fresh_rest_inits_body : ∀ x ∈ Block.initVars rest, σ_cfg_body x = none :=
            fresh_rest_inits_body_step h_initvars_eq h_unique h_preserve_body
            (fun s hns h_in => h_foreign s hns (h_outer_upper_b h_in))
              h_rest_no_gen_suffix h_fresh_rest_inits_after
          have h_combined_rest :
              ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
              σ_cfg_body x = none := fun x hx =>
            h_fresh_rest_inits_body x (by simpa [Cmds.definedVars] using hx)
          have h_unique_combined_rest :
              (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
            simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_rest
          have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_blk.eval ρ_blk.store
              [].reverse ρ_blk.store false := EvalCmds.eval_cmds_none
          have h_hasFail_blk : ρ_blk.hasFailure = ρ_inner.hasFailure := by
            rw [h_ρ_blk_eq]
          -- Lift `h_store_no_gens_upper` through the body sub-simulation
          -- using the strengthened (4-premise) `h_preserve_body` directly.
          have h_store_no_gens_upper_body :
              ∀ x : String, Q x →
                x ∉ StringGenState.stringGens genUpperBound →
                σ_cfg_body (HasIdent.ident (P := P) x) = none :=
            store_no_gens_upper_lift_through_subsim gen_r gen_b genUpperBound
              h_outer_upper_b h_preserve_body h_store_no_gens_upper_after
              (fun x hx s heq => h_body_no_gen_suffix x (List.mem_append_right _ hx) s heq)
          have ⟨σ_cfg_rest, h_step_rest, h_agree_rest, h_preserve_rest⟩ :=
            stmtsToBlocks_simulation_to_cont extendEval k rest exitConts [] gen gen_r kNext bsNext
              h_rest_eq h_nofd_rest h_simple_rest h_unique_rest
              h_lbni_rest h_lhni_rest h_nml_rest ρ_blk.store σ_cfg_body
              ρ_blk.hasFailure false ρ_blk ρ' label bk_target h_label
              hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁ hwf_var₁
              h_rest_exit h_accum_nil_r h_agree_block_body
              h_combined_rest h_unique_combined_rest (by simp)
              h_wf_gen h_rest_no_gen_suffix h_rest_no_gen_suffix_mod
              genUpperBound h_outer_upper_r h_store_no_gens_upper_body h_foreign
              cfg h_cfg_rest h_cfg_nodup
          refine ⟨σ_cfg_rest, ?_, h_agree_rest, ?_⟩
          · -- Transport h_step_body from ρ_inner.hasFailure to ρ_blk.hasFailure.
            exact StepDetCFGStar_trans
              (StepDetCFGStar_trans h_step_flush (h_hasFail_blk.symm ▸ h_step_body)) h_step_rest
          · intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
            have h_x_not_body : x ∉ Block.initVars body := fun hx =>
              h_x_not_inits (h_initvars_eq ▸ List.mem_append_left _ hx)
            have h_x_not_rest : x ∉ Block.initVars rest := fun hx =>
              h_x_not_inits (h_initvars_eq ▸ List.mem_append_right _ hx)
            have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
            have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
            -- Build inner guards from outer guard via GenStep monotonicity.
            have h_inner_guard_b :=
              inner_guard_step_b h_step_gen_to_r h_step_b_to_f h_gen_eq_f h_outer_guard
            have h_inner_guard_r :=
              inner_guard_step_r h_step_b_to_f h_step_r_to_b h_gen_eq_f h_outer_guard
            have h_σ_body_x : σ_cfg_body x = none :=
              h_preserve_body x h_σ_after_x h_nil_not h_x_not_body h_inner_guard_b
            exact h_preserve_rest x h_σ_body_x h_nil_not h_x_not_rest h_inner_guard_r
        · obtain ⟨ρ_inner, h_body_match, h_ρ_blk_eq⟩ := h_match_branch
          have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
            stmtsToBlocks_simulation_to_cont extendEval kNext body
              ((some label', kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
              h_nofd_body h_simple_body h_unique_body
            h_lbni_body h_lhni_body h_nml_body
              ρ₀.store σ_cfg_after ρ₀.hasFailure false
              ρ₀ ρ_inner label' kNext h_label_lookup hwfb hwfv hwf_def hwf_congr hwf_var
              h_body_match h_accum_nil h_agree_after
              h_combined_body h_unique_combined_body h_hf_body
              h_wf_r h_body_no_gen_suffix h_body_no_gen_suffix_mod
              genUpperBound h_outer_upper_b h_store_no_gens_upper_after h_foreign
              cfg h_cfg_bbs h_cfg_nodup
          have h_agree_block_body : StoreAgreement ρ_blk.store σ_cfg_body :=
            StoreAgreement.through_projectStore h_ρ_blk_eq h_agree_body
          have h_eval_blk : ρ_blk.eval = ρ₀.eval := by
            rw [h_ρ_blk_eq]
            exact smallStep_noFuncDecl_preserves_eval_block_exiting P (EvalCmd P) extendEval
              body ρ₀ ρ_inner label' h_nofd_body h_body_match
          have hwfb₁ : WellFormedSemanticEvalBool ρ_blk.eval := h_eval_blk ▸ hwfb
          have hwfv₁ : WellFormedSemanticEvalVal ρ_blk.eval := h_eval_blk ▸ hwfv
          have hwf_def₁ : WellFormedSemanticEvalDef ρ_blk.eval := h_eval_blk ▸ hwf_def
          have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_blk.eval := h_eval_blk ▸ hwf_congr
          have hwf_var₁ : WellFormedSemanticEvalVar ρ_blk.eval := h_eval_blk ▸ hwf_var
          have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none :=
            (fresh_inits_after_step h_initvars_eq h_unique_combined h_fresh_combined
              h_preserve_flush).2
          have h_fresh_rest_inits_body : ∀ x ∈ Block.initVars rest, σ_cfg_body x = none :=
            fresh_rest_inits_body_step h_initvars_eq h_unique h_preserve_body
            (fun s hns h_in => h_foreign s hns (h_outer_upper_b h_in))
              h_rest_no_gen_suffix h_fresh_rest_inits_after
          have h_combined_rest :
              ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
              σ_cfg_body x = none := fun x hx =>
            h_fresh_rest_inits_body x (by simpa [Cmds.definedVars] using hx)
          have h_unique_combined_rest :
              (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
            simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_rest
          have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_blk.eval ρ_blk.store
              [].reverse ρ_blk.store false := EvalCmds.eval_cmds_none
          have h_hasFail_blk : ρ_blk.hasFailure = ρ_inner.hasFailure := by
            rw [h_ρ_blk_eq]
          -- Lift `h_store_no_gens_upper` through the body sub-simulation
          -- using the strengthened (4-premise) `h_preserve_body` directly.
          have h_store_no_gens_upper_body :
              ∀ x : String, Q x →
                x ∉ StringGenState.stringGens genUpperBound →
                σ_cfg_body (HasIdent.ident (P := P) x) = none :=
            store_no_gens_upper_lift_through_subsim gen_r gen_b genUpperBound
              h_outer_upper_b h_preserve_body h_store_no_gens_upper_after
              (fun x hx s heq => h_body_no_gen_suffix x (List.mem_append_right _ hx) s heq)
          have ⟨σ_cfg_rest, h_step_rest, h_agree_rest, h_preserve_rest⟩ :=
            stmtsToBlocks_simulation_to_cont extendEval k rest exitConts [] gen gen_r kNext bsNext
              h_rest_eq h_nofd_rest h_simple_rest h_unique_rest
              h_lbni_rest h_lhni_rest h_nml_rest ρ_blk.store σ_cfg_body
              ρ_blk.hasFailure false ρ_blk ρ' label bk_target h_label
              hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁ hwf_var₁
              h_rest_exit h_accum_nil_r h_agree_block_body
              h_combined_rest h_unique_combined_rest (by simp)
              h_wf_gen h_rest_no_gen_suffix h_rest_no_gen_suffix_mod
              genUpperBound h_outer_upper_r h_store_no_gens_upper_body h_foreign
              cfg h_cfg_rest h_cfg_nodup
          refine ⟨σ_cfg_rest, ?_, h_agree_rest, ?_⟩
          · -- Transport h_step_body from ρ_inner.hasFailure to ρ_blk.hasFailure.
            exact StepDetCFGStar_trans
              (StepDetCFGStar_trans h_step_flush (h_hasFail_blk.symm ▸ h_step_body)) h_step_rest
          · intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
            have h_x_not_body : x ∉ Block.initVars body := fun hx =>
              h_x_not_inits (h_initvars_eq ▸ List.mem_append_left _ hx)
            have h_x_not_rest : x ∉ Block.initVars rest := fun hx =>
              h_x_not_inits (h_initvars_eq ▸ List.mem_append_right _ hx)
            have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
            have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
            -- Build inner guards from outer guard via GenStep monotonicity.
            have h_inner_guard_b :=
              inner_guard_step_b h_step_gen_to_r h_step_b_to_f h_gen_eq_f h_outer_guard
            have h_inner_guard_r :=
              inner_guard_step_r h_step_b_to_f h_step_r_to_b h_gen_eq_f h_outer_guard
            have h_σ_body_x : σ_cfg_body x = none :=
              h_preserve_body x h_σ_after_x h_nil_not h_x_not_body h_inner_guard_b
            exact h_preserve_rest x h_σ_body_x h_nil_not h_x_not_rest h_inner_guard_r
  | .ite (.det e) thenBranch elseBranch md :: rest =>
    unfold stmtsToBlocks at h_gen
    simp [bind, StateT.bind, pure, StateT.pure, List.append_nil] at h_gen
    -- Decompose the monadic h_gen
    generalize h_rest_eq : stmtsToBlocks k rest exitConts [] gen = r_rest at h_gen
    obtain ⟨⟨kNext, bsNext⟩, gen_r⟩ := r_rest
    simp at h_gen
    generalize h_ite_label : StringGenState.gen "ite" gen_r = r_ite at h_gen
    obtain ⟨l_ite, gen_ite⟩ := r_ite
    simp at h_gen
    generalize h_then_eq : stmtsToBlocks kNext thenBranch exitConts [] gen_ite = r_then at h_gen
    obtain ⟨⟨tl, tbs⟩, gen_t⟩ := r_then
    simp at h_gen
    generalize h_else_eq : stmtsToBlocks kNext elseBranch exitConts [] gen_t = r_else at h_gen
    obtain ⟨⟨fl, fbs⟩, gen_e⟩ := r_else
    simp at h_gen
    generalize h_flush_eq : flushCmds "ite$" accum
      (some (DetTransferCmd.condGoto e tl fl md)) l_ite gen_e = r_flush at h_gen
    obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
    have h_entry : accumEntry = entry := (Prod.mk.inj (Prod.mk.inj h_gen).1).1
    have h_blocks : accumBlocks ++ (tbs ++ (fbs ++ bsNext)) = blocks :=
      (Prod.mk.inj (Prod.mk.inj h_gen).1).2
    subst h_entry
    -- Decompose the structured execution of (.ite ... :: rest) reaching .exiting label.
    -- Two outer cases via seq_reaches_exiting:
    --   (caseA) inner `.stmt (.ite ..) ρ₀` already exits with `label`; rest doesn't run.
    --   (caseB) inner terminates at ρ_mid, then rest exits.
    have h_decomp :
        -- caseA: branch itself exits with `label`. Either thenBranch (cond=tt) or elseBranch (cond=ff).
        ((StepStmtStar P (EvalCmd P) extendEval
            (.stmts thenBranch ρ₀) (.exiting label ρ') ∧
          ρ₀.eval ρ₀.store e = .some HasBool.tt) ∨
         (StepStmtStar P (EvalCmd P) extendEval
            (.stmts elseBranch ρ₀) (.exiting label ρ') ∧
          ρ₀.eval ρ₀.store e = .some HasBool.ff)) ∨
        -- caseB: branch terminates at ρ_mid, rest exits with `label`.
        (∃ ρ_mid,
          ((StepStmtStar P (EvalCmd P) extendEval
              (.stmts thenBranch ρ₀) (.terminal ρ_mid) ∧
            ρ₀.eval ρ₀.store e = .some HasBool.tt) ∨
           (StepStmtStar P (EvalCmd P) extendEval
              (.stmts elseBranch ρ₀) (.terminal ρ_mid) ∧
            ρ₀.eval ρ₀.store e = .some HasBool.ff)) ∧
          StepStmtStar P (EvalCmd P) extendEval (.stmts rest ρ_mid) (.exiting label ρ')) := by
      cases h_exit with
      | step _ _ _ hstep1 hrest1 =>
        cases hstep1 with
        | step_stmts_cons =>
          have h_seq_inv := seq_reaches_exiting P (EvalCmd P) extendEval hrest1
          rcases h_seq_inv with h_inner_exit | h_term_exit
          · -- inner = .stmt (.ite ..) ρ₀ → .exiting label ρ'
            cases h_inner_exit with
            | step _ _ _ hstep2 hrest2 =>
              cases hstep2 with
              | step_ite_true h_eval_tt _ =>
                exact Or.inl (Or.inl ⟨hrest2, h_eval_tt⟩)
              | step_ite_false h_eval_ff _ =>
                exact Or.inl (Or.inr ⟨hrest2, h_eval_ff⟩)
          · obtain ⟨ρ_mid_outer, h_inner_term, h_rest_exit⟩ := h_term_exit
            -- inner = .stmt (.ite ..) ρ₀ → .terminal ρ_mid_outer
            cases h_inner_term with
            | step _ _ _ hstep2 hrest2 =>
              cases hstep2 with
              | step_ite_true h_eval_tt _ =>
                exact Or.inr ⟨ρ_mid_outer, Or.inl ⟨hrest2, h_eval_tt⟩, h_rest_exit⟩
              | step_ite_false h_eval_ff _ =>
                exact Or.inr ⟨ρ_mid_outer, Or.inr ⟨hrest2, h_eval_ff⟩, h_rest_exit⟩
    -- Block membership: distribute h_cfg_blocks over concatenated blocks.
    subst h_blocks
    have h_cfg_accum : ∀ b ∈ accumBlocks, b ∈ cfg.blocks := fun b hb =>
      h_cfg_blocks b (List.mem_append_left _ hb)
    have h_cfg_tbs : ∀ b ∈ tbs, b ∈ cfg.blocks := fun b hb =>
      h_cfg_blocks b (List.mem_append_right _
        (List.mem_append_left _ hb))
    have h_cfg_fbs : ∀ b ∈ fbs, b ∈ cfg.blocks := fun b hb =>
      h_cfg_blocks b (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ hb)))
    have h_cfg_rest : ∀ b ∈ bsNext, b ∈ cfg.blocks := fun b hb =>
      h_cfg_blocks b (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_right _ hb)))
    -- noFuncDecl projections.
    have h_nofd_then : Block.noFuncDecl thenBranch = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.1.1
    have h_nofd_else : Block.noFuncDecl elseBranch = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.1.2
    have h_nofd_rest : Block.noFuncDecl rest = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.2
    -- simpleShape projections.
    have h_simple_head : Stmt.simpleShape (.ite (.det e) thenBranch elseBranch md) = true :=
      (Block.simpleShape_cons_iff.mp h_simple).1
    have h_simple_rest : Block.simpleShape rest = true :=
      (Block.simpleShape_cons_iff.mp h_simple).2
    -- loopBodyNoInits/loopHasNoInvariants/noMeasureLoops projections.
    have h_lbni_head : Stmt.loopBodyNoInits (.ite (.det e) thenBranch elseBranch md) = true :=
      (Block.loopBodyNoInits_cons_iff.mp h_lbni).1
    have h_lbni_rest : Block.loopBodyNoInits rest = true :=
      (Block.loopBodyNoInits_cons_iff.mp h_lbni).2
    have h_lhni_head : Stmt.loopHasNoInvariants (.ite (.det e) thenBranch elseBranch md) = true :=
      (Block.loopHasNoInvariants_cons_iff.mp h_lhni).1
    have h_lhni_rest : Block.loopHasNoInvariants rest = true :=
      (Block.loopHasNoInvariants_cons_iff.mp h_lhni).2
    have h_nml_head : Stmt.noMeasureLoops (.ite (.det e) thenBranch elseBranch md) = true :=
      (Block.noMeasureLoops_cons_iff.mp h_nml).1
    have h_nml_rest : Block.noMeasureLoops rest = true :=
      (Block.noMeasureLoops_cons_iff.mp h_nml).2
    obtain ⟨h_simple_then, h_simple_else, h_lbni_then, h_lbni_else,
            h_lhni_then, h_lhni_else, h_nml_then, h_nml_else⟩ :=
      ite_branch_shape h_simple_head h_lbni_head h_lhni_head h_nml_head
    have h_unique_then : Block.uniqueInits thenBranch :=
      Block.uniqueInits.ite_then h_unique
    have h_unique_else : Block.uniqueInits elseBranch :=
      Block.uniqueInits.ite_else h_unique
    have h_unique_rest : Block.uniqueInits rest := Block.uniqueInits.tail h_unique
    -- Lift accum to the CFG side via EvalCmds_under_agreement.
    have h_fresh_accum : ∀ x ∈ Cmds.definedVars accum.reverse, σ_base x = none := by
      intro x hx
      exact h_fresh_combined x (List.mem_append_left _ hx)
    have h_unique_accum : (Cmds.definedVars accum.reverse).Nodup :=
      (List.nodup_append.mp h_unique_combined).1
    have ⟨σ_cfg_after, h_accum_cfg, h_agree_after⟩ :=
      EvalCmds_under_agreement ρ₀.eval accum.reverse hwf_def hwf_congr
        σ_struct_base σ_base ρ₀.store hf_accum h_agree_entry h_accum h_fresh_accum
        h_unique_accum
    -- Freshness preservation through the lifted accum.
    have h_preserve_after :
        ∀ x, σ_base x = none → x ∉ Cmds.definedVars accum.reverse →
          σ_cfg_after x = none := by
      intro x h_σ h_x_not
      exact agreement_helper_unchanged_at_x_multi h_accum_cfg h_x_not h_σ
    -- Block.initVars decomposition.
    have h_initvars_eq :
        Block.initVars (Stmt.ite (ExprOrNondet.det e) thenBranch elseBranch md :: rest) =
        (Block.initVars thenBranch ++ Block.initVars elseBranch) ++ Block.initVars rest := by
      rw [Block.initVars]
      simp
    have h_unique_outer_inits :
        (Cmds.definedVars accum.reverse ++
          ((Block.initVars thenBranch ++ Block.initVars elseBranch) ++ Block.initVars rest)).Nodup := by
      rw [← h_initvars_eq]; exact h_unique_combined
    -- Freshness for sub-branch and rest recursions.
    have h_fresh_then_inits : ∀ x ∈ Block.initVars thenBranch, σ_cfg_after x = none := by
      intro x hx
      have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := fun hx_acc =>
        (List.nodup_append.mp h_unique_outer_inits).2.2 x hx_acc x
          (List.mem_append_left _ (List.mem_append_left _ hx)) rfl
      have h_σ_x : σ_base x = none :=
        h_fresh_combined x (List.mem_append_right _
          (h_initvars_eq ▸ List.mem_append_left _ (List.mem_append_left _ hx)))
      exact h_preserve_after x h_σ_x h_x_not_accum
    have h_fresh_else_inits : ∀ x ∈ Block.initVars elseBranch, σ_cfg_after x = none := by
      intro x hx
      have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := fun hx_acc =>
        (List.nodup_append.mp h_unique_outer_inits).2.2 x hx_acc x
          (List.mem_append_left _ (List.mem_append_right _ hx)) rfl
      have h_σ_x : σ_base x = none :=
        h_fresh_combined x (List.mem_append_right _
          (h_initvars_eq ▸ List.mem_append_left _ (List.mem_append_right _ hx)))
      exact h_preserve_after x h_σ_x h_x_not_accum
    have h_fresh_rest_inits_after :
        ∀ x ∈ Block.initVars rest, σ_cfg_after x = none := by
      intro x hx
      have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := fun hx_acc =>
        (List.nodup_append.mp h_unique_outer_inits).2.2 x hx_acc x
          (List.mem_append_right _ hx) rfl
      have h_σ_x : σ_base x = none :=
        h_fresh_combined x (List.mem_append_right _
          (h_initvars_eq ▸ List.mem_append_right _ hx))
      exact h_preserve_after x h_σ_x h_x_not_accum
    have h_combined_then :
        ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars thenBranch,
        σ_cfg_after x = none :=
      fun x hx => h_fresh_then_inits x (by simpa [Cmds.definedVars] using hx)
    have h_unique_combined_ite := unique_combined_ite h_unique_outer_inits
    have h_unique_combined_then :
        (Cmds.definedVars [].reverse ++ Block.initVars thenBranch).Nodup :=
      h_unique_combined_ite.1
    have h_combined_else :
        ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars elseBranch,
        σ_cfg_after x = none :=
      fun x hx => h_fresh_else_inits x (by simpa [Cmds.definedVars] using hx)
    have h_unique_combined_else :
        (Cmds.definedVars [].reverse ++ Block.initVars elseBranch).Nodup :=
      h_unique_combined_ite.2.1
    have h_lookup : ∀ lbl blk, (lbl, blk) ∈ cfg.blocks →
        cfg.blocks.lookup lbl = some blk :=
      fun lbl blk h_mem => List.lookup_of_mem_nodup cfg.blocks h_cfg_nodup lbl blk h_mem
    -- GenStep chains for WF and subset.
    have h_gen_eq_f : gen_f = gen' := (Prod.mk.inj h_gen).2
    have h_step_e_to_f : StringGenState.GenStep gen_e gen_f :=
      flushCmds_genStep _ _ _ _ _ _ _ _ h_flush_eq
    have h_step_t_to_e : StringGenState.GenStep gen_t gen_e :=
      stmtsToBlocks_genStep _ _ _ _ _ _ _ _ h_else_eq
    have h_step_ite_to_t : StringGenState.GenStep gen_ite gen_t :=
      stmtsToBlocks_genStep _ _ _ _ _ _ _ _ h_then_eq
    have h_step_r_to_ite : StringGenState.GenStep gen_r gen_ite := by
      have h_eq : (StringGenState.gen "ite" gen_r).2 = gen_ite := congrArg Prod.snd h_ite_label
      exact h_eq ▸ StringGenState.GenStep.of_gen "ite" gen_r
    have h_step_gen_to_r : StringGenState.GenStep gen gen_r :=
      stmtsToBlocks_genStep _ _ _ _ _ _ _ _ h_rest_eq
    have h_step_gen_to_ite : StringGenState.GenStep gen gen_ite :=
      h_step_gen_to_r.trans h_step_r_to_ite
    have h_step_gen_to_t : StringGenState.GenStep gen gen_t :=
      h_step_gen_to_ite.trans h_step_ite_to_t
    have h_step_gen_to_e : StringGenState.GenStep gen gen_e :=
      h_step_gen_to_t.trans h_step_t_to_e
    have h_wf_t : StringGenState.WF gen_t := h_step_gen_to_t.wf_mono h_wf_gen
    have h_wf_e : StringGenState.WF gen_e := h_step_gen_to_e.wf_mono h_wf_gen
    have h_wf_r : StringGenState.WF gen_r := h_step_gen_to_r.wf_mono h_wf_gen
    have h_wf_ite : StringGenState.WF gen_ite := h_step_gen_to_ite.wf_mono h_wf_gen
    -- Lift store-no-gens to σ_cfg_after at the lemma's local `gen` precondition.
    have h_store_no_gens_upper_after :
        ∀ x : String, Q x →
          x ∉ StringGenState.stringGens genUpperBound →
          σ_cfg_after (HasIdent.ident (P := P) x) = none :=
      store_no_gens_lift_after_accum h_accum_cfg genUpperBound h_store_no_gens_upper
        (fun x hx => h_combined_no_gen_suffix x (List.mem_append_left _ hx))
    -- Subset chains lifting outer upper-bound to inner gen' subsets.
    have h_outer_upper_e : StringGenState.stringGens gen_e ⊆ StringGenState.stringGens genUpperBound :=
      h_step_e_to_f.subset.trans (h_gen_eq_f ▸ h_outer_upper)
    have h_outer_upper_t : StringGenState.stringGens gen_t ⊆ StringGenState.stringGens genUpperBound :=
      h_step_t_to_e.subset.trans h_outer_upper_e
    have h_outer_upper_r : StringGenState.stringGens gen_r ⊆ StringGenState.stringGens genUpperBound :=
      h_step_r_to_ite.subset.trans (h_step_ite_to_t.subset.trans h_outer_upper_t)
    -- Sub-branch and rest combined-no-gen-suffix discharges.
    have h_then_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars [].reverse ++ Block.initVars thenBranch) := fun x hx s heq =>
      h_combined_no_gen_suffix x (List.mem_append_right _ (h_initvars_eq ▸
        List.mem_append_left _ (List.mem_append_left _ (by simpa [Cmds.definedVars] using hx)))) s heq
    have h_else_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars [].reverse ++ Block.initVars elseBranch) := fun x hx s heq =>
      h_combined_no_gen_suffix x (List.mem_append_right _ (h_initvars_eq ▸
        List.mem_append_left _ (List.mem_append_right _ (by simpa [Cmds.definedVars] using hx)))) s heq
    have h_rest_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars [].reverse ++ Block.initVars rest) := fun x hx s heq =>
      h_combined_no_gen_suffix x (List.mem_append_right _ (h_initvars_eq ▸
        List.mem_append_right _ (by simpa [Cmds.definedVars] using hx))) s heq
    -- Mirror of h_initvars_eq / no_gen_suffix discharges for modifiedVars.
    have h_modvars_eq :
        transformBlockModVars (Stmt.ite (ExprOrNondet.det e) thenBranch elseBranch md :: rest) =
        (transformBlockModVars thenBranch ++ transformBlockModVars elseBranch) ++ transformBlockModVars rest := by
      rw [transformBlockModVars_cons, transformStmtModVars_ite]
    have h_then_no_gen_suffix_mod :
        NoGenSuffix (P := P) Q (Cmds.modifiedVars [].reverse ++ transformBlockModVars thenBranch) := fun x hx s heq =>
      h_combined_no_gen_suffix_mod x (List.mem_append_right _ (h_modvars_eq ▸
        List.mem_append_left _ (List.mem_append_left _ (by simpa [Cmds.modifiedVars] using hx)))) s heq
    have h_else_no_gen_suffix_mod :
        NoGenSuffix (P := P) Q (Cmds.modifiedVars [].reverse ++ transformBlockModVars elseBranch) := fun x hx s heq =>
      h_combined_no_gen_suffix_mod x (List.mem_append_right _ (h_modvars_eq ▸
        List.mem_append_left _ (List.mem_append_right _ (by simpa [Cmds.modifiedVars] using hx)))) s heq
    have h_rest_no_gen_suffix_mod :
        NoGenSuffix (P := P) Q (Cmds.modifiedVars [].reverse ++ transformBlockModVars rest) := fun x hx s heq =>
      h_combined_no_gen_suffix_mod x (List.mem_append_right _ (h_modvars_eq ▸
        List.mem_append_right _ (by simpa [Cmds.modifiedVars] using hx))) s heq
    rcases h_decomp with h_caseA | h_caseB
    · -- Branch itself exits with `label`; rest does not run.
      rcases h_caseA with h_true | h_false
      · obtain ⟨h_then_exit, h_cond_tt⟩ := h_true
        have h_flush_sim : StepDetCFGStar extendEval cfg
            (.atBlock accumEntry σ_base hf_base)
            (.atBlock tl σ_cfg_after ρ₀.hasFailure) :=
          flushCmds_condGoto_agree extendEval true accum e tl fl md l_ite gen_e gen_f
            accumEntry accumBlocks h_flush_eq σ_base σ_cfg_after hf_base hf_accum ρ₀
            hwfb hwf_def hwf_congr h_accum_cfg h_agree_after h_hf h_cond_tt cfg
            h_cfg_accum h_lookup
        -- Recurse on thenBranch with _to_cont (target = bk_target).
        have h_accum_nil_t : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have ⟨σ_cfg_branch, h_then_step, h_agree_branch, h_preserve_branch⟩ :=
          stmtsToBlocks_simulation_to_cont extendEval kNext thenBranch exitConts []
            gen_ite gen_t tl tbs h_then_eq h_nofd_then h_simple_then h_unique_then
            h_lbni_then h_lhni_then h_nml_then
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ' label bk_target h_label hwfb hwfv hwf_def hwf_congr hwf_var
            h_then_exit h_accum_nil_t h_agree_after
            h_combined_then h_unique_combined_then (by simp)
            h_wf_ite h_then_no_gen_suffix h_then_no_gen_suffix_mod
            genUpperBound h_outer_upper_t h_store_no_gens_upper_after h_foreign
            cfg h_cfg_tbs h_cfg_nodup
        refine ⟨σ_cfg_branch, ?_, h_agree_branch, ?_⟩
        · exact StepDetCFGStar_trans h_flush_sim h_then_step
        · intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
          have h_x_not_then : x ∉ Block.initVars thenBranch := fun hx =>
            h_x_not_inits (h_initvars_eq ▸ List.mem_append_left _ (List.mem_append_left _ hx))
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_after x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          -- Build inner guard at (gen_ite, gen_t) from outer guard at (gen, gen').
          have h_inner_guard_t : ∀ s : String, x = HasIdent.ident (P := P) s →
              s ∈ StringGenState.stringGens gen_ite ∨
              s ∉ StringGenState.stringGens gen_t :=
            fun s heq => match h_outer_guard s heq with
            | Or.inl h_in => Or.inl (h_step_gen_to_ite.subset h_in)
            | Or.inr h_not_in => Or.inr (fun h_in_t => h_not_in
                (h_gen_eq_f ▸ h_step_e_to_f.subset (h_step_t_to_e.subset h_in_t)))
          exact h_preserve_branch x h_σ_after_x h_nil_not h_x_not_then h_inner_guard_t
      · obtain ⟨h_else_exit, h_cond_ff⟩ := h_false
        have h_flush_sim : StepDetCFGStar extendEval cfg
            (.atBlock accumEntry σ_base hf_base)
            (.atBlock fl σ_cfg_after ρ₀.hasFailure) :=
          flushCmds_condGoto_agree extendEval false accum e tl fl md l_ite gen_e gen_f
            accumEntry accumBlocks h_flush_eq σ_base σ_cfg_after hf_base hf_accum ρ₀
            hwfb hwf_def hwf_congr h_accum_cfg h_agree_after h_hf h_cond_ff cfg
            h_cfg_accum h_lookup
        have h_accum_nil_f : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have ⟨σ_cfg_branch, h_else_step, h_agree_branch, h_preserve_branch⟩ :=
          stmtsToBlocks_simulation_to_cont extendEval kNext elseBranch exitConts []
            gen_t gen_e fl fbs h_else_eq h_nofd_else h_simple_else h_unique_else
            h_lbni_else h_lhni_else h_nml_else
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ' label bk_target h_label hwfb hwfv hwf_def hwf_congr hwf_var
            h_else_exit h_accum_nil_f h_agree_after
            h_combined_else h_unique_combined_else (by simp)
            h_wf_t h_else_no_gen_suffix h_else_no_gen_suffix_mod
            genUpperBound h_outer_upper_e h_store_no_gens_upper_after h_foreign
            cfg h_cfg_fbs h_cfg_nodup
        refine ⟨σ_cfg_branch, ?_, h_agree_branch, ?_⟩
        · exact StepDetCFGStar_trans h_flush_sim h_else_step
        · intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
          have h_x_not_else : x ∉ Block.initVars elseBranch := fun hx =>
            h_x_not_inits (h_initvars_eq ▸ List.mem_append_left _ (List.mem_append_right _ hx))
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_after x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          -- Build inner guard at (gen_t, gen_e) from outer guard at (gen, gen').
          have h_inner_guard_e : ∀ s : String, x = HasIdent.ident (P := P) s →
              s ∈ StringGenState.stringGens gen_t ∨
              s ∉ StringGenState.stringGens gen_e :=
            fun s heq => match h_outer_guard s heq with
            | Or.inl h_in => Or.inl (h_step_gen_to_t.subset h_in)
            | Or.inr h_not_in => Or.inr (fun h_in_e => h_not_in
                (h_gen_eq_f ▸ h_step_e_to_f.subset h_in_e))
          exact h_preserve_branch x h_σ_after_x h_nil_not h_x_not_else h_inner_guard_e
    · -- Branch terminates at ρ_mid, then rest exits with `label`.
      obtain ⟨ρ_mid, h_branch_term_or, h_rest_exit⟩ := h_caseB
      -- Eval well-formedness preservation through the branch (terminal).
      have hwfb₁ : WellFormedSemanticEvalBool ρ_mid.eval := by
        exact h_branch_term_or.elim
          (fun h => StepStmtStar_wfb_preserved extendEval thenBranch ρ₀ ρ_mid h.1 h_nofd_then hwfb)
          (fun h => StepStmtStar_wfb_preserved extendEval elseBranch ρ₀ ρ_mid h.1 h_nofd_else hwfb)
      have hwfv₁ : WellFormedSemanticEvalVal ρ_mid.eval := by
        exact h_branch_term_or.elim
          (fun h => StepStmtStar_wfv_preserved extendEval thenBranch ρ₀ ρ_mid h.1 h_nofd_then hwfv)
          (fun h => StepStmtStar_wfv_preserved extendEval elseBranch ρ₀ ρ_mid h.1 h_nofd_else hwfv)
      have h_eval_eq : ρ_mid.eval = ρ₀.eval := by
        rcases h_branch_term_or with h | h
        · exact smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
            thenBranch ρ₀ ρ_mid h_nofd_then h.1
        · exact smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
            elseBranch ρ₀ ρ_mid h_nofd_else h.1
      have hwf_def₁ : WellFormedSemanticEvalDef ρ_mid.eval := by
        rw [h_eval_eq]; exact hwf_def
      have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_mid.eval := by
        rw [h_eval_eq]; exact hwf_congr
      have hwf_var₁ : WellFormedSemanticEvalVar ρ_mid.eval := by
        rw [h_eval_eq]; exact hwf_var
      rcases h_branch_term_or with h_true | h_false
      · obtain ⟨h_then_term, h_cond_tt⟩ := h_true
        have h_flush_sim : StepDetCFGStar extendEval cfg
            (.atBlock accumEntry σ_base hf_base)
            (.atBlock tl σ_cfg_after ρ₀.hasFailure) :=
          flushCmds_condGoto_agree extendEval true accum e tl fl md l_ite gen_e gen_f
            accumEntry accumBlocks h_flush_eq σ_base σ_cfg_after hf_base hf_accum ρ₀
            hwfb hwf_def hwf_congr h_accum_cfg h_agree_after h_hf h_cond_tt cfg
            h_cfg_accum h_lookup
        have h_accum_nil_t : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have ⟨σ_branch, h_then_step, h_agree_then, h_preserve_then⟩ :=
          stmtsToBlocks_simulation extendEval kNext thenBranch exitConts []
            gen_ite gen_t tl tbs h_then_eq h_nofd_then h_simple_then h_unique_then
            h_lbni_then h_lhni_then h_nml_then
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ_mid hwfb hwfv hwf_def hwf_congr hwf_var
            h_then_term h_accum_nil_t h_agree_after
            h_combined_then h_unique_combined_then (by simp)
            h_wf_ite h_then_no_gen_suffix h_then_no_gen_suffix_mod
            genUpperBound h_outer_upper_t h_store_no_gens_upper_after h_foreign
            cfg h_cfg_tbs h_cfg_nodup
        -- Freshness of rest's inits at σ_branch.
        have h_fresh_rest_inits_branch :
            ∀ x ∈ Block.initVars rest, σ_branch x = none := by
          intro x hx
          have h_x_not_then : x ∉ Block.initVars thenBranch := by
            intro h_in_then
            have h1 : ((Block.initVars thenBranch ++ Block.initVars elseBranch) ++
                        Block.initVars rest).Nodup :=
              (List.nodup_append.mp h_unique_outer_inits).2.1
            have h_disj_lr := (List.nodup_append.mp h1).2.2
            have h_in_then_else : x ∈ Block.initVars thenBranch ++ Block.initVars elseBranch :=
              List.mem_append_left _ h_in_then
            exact h_disj_lr x h_in_then_else x hx rfl
          have h_σ_after_x : σ_cfg_after x = none := h_fresh_rest_inits_after x hx
          have : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          exact h_preserve_then x h_σ_after_x this h_x_not_then
            (fun s heq => Or.inr
              (fun h_in => h_foreign s
                (h_rest_no_gen_suffix x (by simp [Cmds.definedVars]; exact hx) s heq)
                (h_outer_upper_t h_in)))
        have h_combined_rest :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
            σ_branch x = none := fun x hx =>
          h_fresh_rest_inits_branch x (by simpa [Cmds.definedVars] using hx)
        have h_unique_combined_rest :
            (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup :=
          (unique_combined_ite h_unique_outer_inits).2.2
        have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_mid.eval ρ_mid.store
            [].reverse ρ_mid.store false := EvalCmds.eval_cmds_none
        -- Lift `h_store_no_gens_upper` through the thenBranch sub-simulation
        -- using the strengthened (4-premise) `h_preserve_then` directly.
        have h_store_no_gens_upper_branch_t :
            ∀ x : String, Q x →
              x ∉ StringGenState.stringGens genUpperBound →
              σ_branch (HasIdent.ident (P := P) x) = none :=
          store_no_gens_upper_lift_through_subsim gen_ite gen_t genUpperBound
            h_outer_upper_t h_preserve_then h_store_no_gens_upper_after
            (fun x hx s heq => h_then_no_gen_suffix x (List.mem_append_right _ hx) s heq)
        have ⟨σ_cfg, h_rest_sim, h_agree_rest, h_preserve_rest⟩ :=
          stmtsToBlocks_simulation_to_cont extendEval k rest exitConts [] gen gen_r kNext bsNext
            h_rest_eq h_nofd_rest h_simple_rest h_unique_rest
            h_lbni_rest h_lhni_rest h_nml_rest ρ_mid.store σ_branch ρ_mid.hasFailure false
            ρ_mid ρ' label bk_target h_label
            hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁ hwf_var₁
            h_rest_exit h_accum_nil_r h_agree_then
            h_combined_rest h_unique_combined_rest (by simp)
            h_wf_gen h_rest_no_gen_suffix h_rest_no_gen_suffix_mod
            genUpperBound h_outer_upper_r h_store_no_gens_upper_branch_t h_foreign
            cfg h_cfg_rest h_cfg_nodup
        refine ⟨σ_cfg, ?_, h_agree_rest, ?_⟩
        · exact StepDetCFGStar_trans
            (StepDetCFGStar_trans h_flush_sim h_then_step) h_rest_sim
        · intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
          have h_x_not_then : x ∉ Block.initVars thenBranch := fun hx =>
            h_x_not_inits (h_initvars_eq ▸ List.mem_append_left _ (List.mem_append_left _ hx))
          have h_x_not_rest : x ∉ Block.initVars rest := fun hx =>
            h_x_not_inits (h_initvars_eq ▸ List.mem_append_right _ hx)
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_after x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          -- Build inner guards from outer guard via GenStep monotonicity.
          have h_inner_guard_t : ∀ s : String, x = HasIdent.ident (P := P) s →
              s ∈ StringGenState.stringGens gen_ite ∨
              s ∉ StringGenState.stringGens gen_t :=
            fun s heq => match h_outer_guard s heq with
            | Or.inl h_in => Or.inl (h_step_gen_to_ite.subset h_in)
            | Or.inr h_not_in => Or.inr (fun h_in_t => h_not_in
                (h_gen_eq_f ▸ h_step_e_to_f.subset (h_step_t_to_e.subset h_in_t)))
          have h_inner_guard_r : ∀ s : String, x = HasIdent.ident (P := P) s →
              s ∈ StringGenState.stringGens gen ∨
              s ∉ StringGenState.stringGens gen_r :=
            fun s heq => match h_outer_guard s heq with
            | Or.inl h_in => Or.inl h_in
            | Or.inr h_not_in => Or.inr (fun h_in_r => h_not_in
                (h_gen_eq_f ▸ h_step_e_to_f.subset (h_step_t_to_e.subset
                  (h_step_ite_to_t.subset (h_step_r_to_ite.subset h_in_r)))))
          have h_σ_branch_x : σ_branch x = none :=
            h_preserve_then x h_σ_after_x h_nil_not h_x_not_then h_inner_guard_t
          exact h_preserve_rest x h_σ_branch_x h_nil_not h_x_not_rest h_inner_guard_r
      · obtain ⟨h_else_term, h_cond_ff⟩ := h_false
        have h_flush_sim : StepDetCFGStar extendEval cfg
            (.atBlock accumEntry σ_base hf_base)
            (.atBlock fl σ_cfg_after ρ₀.hasFailure) :=
          flushCmds_condGoto_agree extendEval false accum e tl fl md l_ite gen_e gen_f
            accumEntry accumBlocks h_flush_eq σ_base σ_cfg_after hf_base hf_accum ρ₀
            hwfb hwf_def hwf_congr h_accum_cfg h_agree_after h_hf h_cond_ff cfg
            h_cfg_accum h_lookup
        have h_accum_nil_f : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have ⟨σ_branch, h_else_step, h_agree_else, h_preserve_else⟩ :=
          stmtsToBlocks_simulation extendEval kNext elseBranch exitConts []
            gen_t gen_e fl fbs h_else_eq h_nofd_else h_simple_else h_unique_else
            h_lbni_else h_lhni_else h_nml_else
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ_mid hwfb hwfv hwf_def hwf_congr hwf_var
            h_else_term h_accum_nil_f h_agree_after
            h_combined_else h_unique_combined_else (by simp)
            h_wf_t h_else_no_gen_suffix h_else_no_gen_suffix_mod
            genUpperBound h_outer_upper_e h_store_no_gens_upper_after h_foreign
            cfg h_cfg_fbs h_cfg_nodup
        have h_fresh_rest_inits_branch :
            ∀ x ∈ Block.initVars rest, σ_branch x = none := by
          intro x hx
          have h_x_not_else : x ∉ Block.initVars elseBranch := by
            intro h_in_else
            have h1 : ((Block.initVars thenBranch ++ Block.initVars elseBranch) ++
                        Block.initVars rest).Nodup :=
              (List.nodup_append.mp h_unique_outer_inits).2.1
            have h_disj_lr := (List.nodup_append.mp h1).2.2
            have h_in_then_else : x ∈ Block.initVars thenBranch ++ Block.initVars elseBranch :=
              List.mem_append_right _ h_in_else
            exact h_disj_lr x h_in_then_else x hx rfl
          have h_σ_after_x : σ_cfg_after x = none := h_fresh_rest_inits_after x hx
          have : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          exact h_preserve_else x h_σ_after_x this h_x_not_else
            (fun s heq => Or.inr
              (fun h_in => h_foreign s
                (h_rest_no_gen_suffix x (by simp [Cmds.definedVars]; exact hx) s heq)
                (h_outer_upper_e h_in)))
        have h_combined_rest :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
            σ_branch x = none := fun x hx =>
          h_fresh_rest_inits_branch x (by simpa [Cmds.definedVars] using hx)
        have h_unique_combined_rest :
            (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup :=
          (unique_combined_ite h_unique_outer_inits).2.2
        have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_mid.eval ρ_mid.store
            [].reverse ρ_mid.store false := EvalCmds.eval_cmds_none
        -- Lift `h_store_no_gens_upper` through the elseBranch sub-simulation
        -- using the strengthened (4-premise) `h_preserve_else` directly.
        have h_store_no_gens_upper_branch_e :
            ∀ x : String, Q x →
              x ∉ StringGenState.stringGens genUpperBound →
              σ_branch (HasIdent.ident (P := P) x) = none :=
          store_no_gens_upper_lift_through_subsim gen_t gen_e genUpperBound
            h_outer_upper_e h_preserve_else h_store_no_gens_upper_after
            (fun x hx s heq => h_else_no_gen_suffix x (List.mem_append_right _ hx) s heq)
        have ⟨σ_cfg, h_rest_sim, h_agree_rest, h_preserve_rest⟩ :=
          stmtsToBlocks_simulation_to_cont extendEval k rest exitConts [] gen gen_r kNext bsNext
            h_rest_eq h_nofd_rest h_simple_rest h_unique_rest
            h_lbni_rest h_lhni_rest h_nml_rest ρ_mid.store σ_branch ρ_mid.hasFailure false
            ρ_mid ρ' label bk_target h_label
            hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁ hwf_var₁
            h_rest_exit h_accum_nil_r h_agree_else
            h_combined_rest h_unique_combined_rest (by simp)
            h_wf_gen h_rest_no_gen_suffix h_rest_no_gen_suffix_mod
            genUpperBound h_outer_upper_r h_store_no_gens_upper_branch_e h_foreign
            cfg h_cfg_rest h_cfg_nodup
        refine ⟨σ_cfg, ?_, h_agree_rest, ?_⟩
        · exact StepDetCFGStar_trans
            (StepDetCFGStar_trans h_flush_sim h_else_step) h_rest_sim
        · intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
          have h_x_not_else : x ∉ Block.initVars elseBranch := fun hx =>
            h_x_not_inits (h_initvars_eq ▸ List.mem_append_left _ (List.mem_append_right _ hx))
          have h_x_not_rest : x ∉ Block.initVars rest := fun hx =>
            h_x_not_inits (h_initvars_eq ▸ List.mem_append_right _ hx)
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_after x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          -- Build inner guards from outer guard via GenStep monotonicity.
          have h_inner_guard_e : ∀ s : String, x = HasIdent.ident (P := P) s →
              s ∈ StringGenState.stringGens gen_t ∨
              s ∉ StringGenState.stringGens gen_e :=
            fun s heq => match h_outer_guard s heq with
            | Or.inl h_in => Or.inl (h_step_gen_to_t.subset h_in)
            | Or.inr h_not_in => Or.inr (fun h_in_e => h_not_in
                (h_gen_eq_f ▸ h_step_e_to_f.subset h_in_e))
          have h_inner_guard_r : ∀ s : String, x = HasIdent.ident (P := P) s →
              s ∈ StringGenState.stringGens gen ∨
              s ∉ StringGenState.stringGens gen_r :=
            fun s heq => match h_outer_guard s heq with
            | Or.inl h_in => Or.inl h_in
            | Or.inr h_not_in => Or.inr (fun h_in_r => h_not_in
                (h_gen_eq_f ▸ h_step_e_to_f.subset (h_step_t_to_e.subset
                  (h_step_ite_to_t.subset (h_step_r_to_ite.subset h_in_r)))))
          have h_σ_branch_x : σ_branch x = none :=
            h_preserve_else x h_σ_after_x h_nil_not h_x_not_else h_inner_guard_e
          exact h_preserve_rest x h_σ_branch_x h_nil_not h_x_not_rest h_inner_guard_r
  | .ite .nondet _ _ _ :: _ =>
    exact absurd (Block.simpleShape_cons_iff.mp h_simple).1 (by simp [Stmt.simpleShape])
  | .loop guard measure invariants body md :: rest =>
    -- Subdispatch on guard: .nondet is excluded by strengthened simpleShape.
    have h_simple_head : Stmt.simpleShape (.loop guard measure invariants body md) = true :=
      (Block.simpleShape_cons_iff.mp h_simple).1
    have ⟨guardExpr, hg_eq⟩ : ∃ ge, guard = .det ge :=
      Stmt.simpleShape_loop_guard_det h_simple_head
    subst hg_eq
    -- Subdispatch on measure: only `.none` is admitted by noMeasureLoops.
    have h_nml_head : Stmt.noMeasureLoops (.loop (.det guardExpr) measure invariants body md) = true :=
      (Block.noMeasureLoops_cons_iff.mp h_nml).1
    have h_measure_none : measure = .none := by
      simp only [Stmt.noMeasureLoops, Bool.and_eq_true, Option.isNone_iff_eq_none] at h_nml_head
      exact h_nml_head.1
    subst h_measure_none
    -- Subdispatch on invariants: only `[]` is admitted by loopHasNoInvariants.
    have h_lhni_head : Stmt.loopHasNoInvariants
        (.loop (.det guardExpr) (none : Option P.Expr) invariants body md) = true :=
      (Block.loopHasNoInvariants_cons_iff.mp h_lhni).1
    have h_invs_nil : invariants = [] :=
      Stmt.loopHasNoInvariants_loop_invs h_lhni_head
    subst h_invs_nil
    -- === STEP 1: Decompose h_gen. ===
    obtain ⟨kNext, lentry, bl, bbs, bsRest, accumEntry, accumBlocks,
           gen_r, gen_le, gen_b, gen_f,
           h_rest_eq, h_le_eq, h_body_eq, h_flush_eq, h_gen_eq, h_entry_eq, h_blocks_eq⟩ :=
      InlineLoopHelpers.loop_det_decompose_h_gen k gen gen' entry blocks accum
        guardExpr body md exitConts rest h_gen
    -- === STEP 2: Project sub-block preconditions (same as terminal arm). ===
    have h_body_no_inits : Block.initVars body = [] :=
      Stmt.loopBodyNoInits_loop_body ((Block.loopBodyNoInits_cons_iff.mp h_lbni).1)
    have h_nofd_body : Block.noFuncDecl body = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.1
    have h_nofd_rest : Block.noFuncDecl rest = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.2
    have h_simple_body : Block.simpleShape body = true :=
      Stmt.simpleShape_loop_body h_simple_head
    have h_simple_rest : Block.simpleShape rest = true :=
      (Block.simpleShape_cons_iff.mp h_simple).2
    have h_unique_body : Block.uniqueInits body := by
      have h := Block.uniqueInits.head_stmt h_unique
      simp only [Stmt.initVars] at h; exact h
    have h_unique_rest : Block.uniqueInits rest := Block.uniqueInits.tail h_unique
    have h_lbni_body : Block.loopBodyNoInits body = true :=
      Stmt.loopBodyNoInits_loop_body_rec ((Block.loopBodyNoInits_cons_iff.mp h_lbni).1)
    have h_lbni_rest : Block.loopBodyNoInits rest = true :=
      (Block.loopBodyNoInits_cons_iff.mp h_lbni).2
    have h_lhni_body : Block.loopHasNoInvariants body = true :=
      Stmt.loopHasNoInvariants_loop_body_rec h_lhni_head
    have h_lhni_rest : Block.loopHasNoInvariants rest = true :=
      (Block.loopHasNoInvariants_cons_iff.mp h_lhni).2
    have h_nml_body : Block.noMeasureLoops body = true :=
      Stmt.noMeasureLoops_loop_body_rec h_nml_head
    have h_nml_rest : Block.noMeasureLoops rest = true :=
      (Block.noMeasureLoops_cons_iff.mp h_nml).2
    have h_initvars_eq :
        Block.initVars (Stmt.loop (.det guardExpr) none [] body md :: rest) =
        Block.initVars rest := by
      rw [Block.initVars]; simp only [Stmt.initVars, h_body_no_inits, List.nil_append]
    -- === STEP 3: Split h_exit (loop :: rest exits with label). ===
    -- Two cases: (a) the loop body exits with label (loop produces .exiting), or
    -- (b) the loop terminates, then rest exits with label.
    have h_exit_dispatch :
        (∃ ρ_loop_post, StepStmtStar P (EvalCmd P) extendEval
            (.stmt (Stmt.loop (.det guardExpr) none [] body md) ρ₀) (.exiting label ρ_loop_post) ∧
          ρ' = ρ_loop_post) ∨
        (∃ ρ_loop_post, StepStmtStar P (EvalCmd P) extendEval
            (.stmt (Stmt.loop (.det guardExpr) none [] body md) ρ₀) (.terminal ρ_loop_post) ∧
          StepStmtStar P (EvalCmd P) extendEval
            (.stmts rest ρ_loop_post) (.exiting label ρ')) := by
      cases h_exit with
      | step _ _ _ hstep1 hrest1 =>
        cases hstep1 with
        | step_stmts_cons =>
          rcases seq_reaches_exiting P (EvalCmd P) extendEval hrest1 with h_inner | h_term
          · exact Or.inl ⟨ρ', h_inner, rfl⟩
          · obtain ⟨ρ_loop_post, h_loop_term, h_rest_exit⟩ := h_term
            exact Or.inr ⟨ρ_loop_post, h_loop_term, h_rest_exit⟩
    -- === STEP 3b: GenStep chain. ===
    subst h_entry_eq
    subst h_gen_eq
    have h_step_gen_to_r : StringGenState.GenStep gen gen_r :=
      stmtsToBlocks_genStep _ _ _ _ _ _ _ _ h_rest_eq
    have h_step_r_to_le : StringGenState.GenStep gen_r gen_le := by
      rw [show gen_le = (StringGenState.gen "loop_entry$" gen_r).2 from (by rw [h_le_eq])]
      exact StringGenState.GenStep.of_gen "loop_entry$" gen_r
    have h_step_le_to_b : StringGenState.GenStep gen_le gen_b :=
      stmtsToBlocks_genStep _ _ _ _ _ _ _ _ h_body_eq
    have h_step_b_to_f : StringGenState.GenStep gen_b gen_f :=
      flushCmds_genStep _ _ _ _ _ _ _ _ h_flush_eq
    have h_step_gen_to_le : StringGenState.GenStep gen gen_le := h_step_gen_to_r.trans h_step_r_to_le
    have h_step_gen_to_b : StringGenState.GenStep gen gen_b := h_step_gen_to_le.trans h_step_le_to_b
    have h_wf_r : StringGenState.WF gen_r := h_step_gen_to_r.wf_mono h_wf_gen
    have h_wf_le : StringGenState.WF gen_le := h_step_gen_to_le.wf_mono h_wf_gen
    have h_wf_b : StringGenState.WF gen_b := h_step_gen_to_b.wf_mono h_wf_gen
    have h_outer_upper_b : StringGenState.stringGens gen_b ⊆ StringGenState.stringGens genUpperBound :=
      h_step_b_to_f.subset.trans h_outer_upper
    have h_outer_upper_le : StringGenState.stringGens gen_le ⊆ StringGenState.stringGens genUpperBound :=
      h_step_le_to_b.subset.trans h_outer_upper_b
    have h_outer_upper_r : StringGenState.stringGens gen_r ⊆ StringGenState.stringGens genUpperBound :=
      h_step_r_to_le.subset.trans h_outer_upper_le
    -- === STEP 3c: Block-list membership. ===
    let lentryBlk : DetBlock String (Cmd P) P :=
      { cmds := ([] : List (Cmd P)), transfer := DetTransferCmd.condGoto guardExpr bl kNext md }
    have h_blocks_full :
        accumBlocks ++ [(lentry, lentryBlk)] ++ bbs ++ bsRest = blocks := h_blocks_eq
    subst h_blocks_full
    have h_cfg_accum : ∀ b ∈ accumBlocks, b ∈ cfg.blocks := fun b hb =>
      h_cfg_blocks b (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hb)))
    have h_cfg_lentry : (lentry, lentryBlk) ∈ cfg.blocks :=
      h_cfg_blocks _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.Mem.head _))))
    have h_cfg_bbs : ∀ b ∈ bbs, b ∈ cfg.blocks := fun b hb =>
      h_cfg_blocks b (List.mem_append_left _ (List.mem_append_right _ hb))
    have h_cfg_bsRest : ∀ b ∈ bsRest, b ∈ cfg.blocks := fun b hb =>
      h_cfg_blocks b (List.mem_append_right _ hb)
    have h_lentry_lkp : cfg.blocks.lookup lentry = some lentryBlk :=
      List.lookup_of_mem_nodup cfg.blocks h_cfg_nodup _ _ h_cfg_lentry
    -- === STEP 4: Lift accum to CFG (accumEntry → lentry). ===
    have h_fresh_accum : ∀ x ∈ Cmds.definedVars accum.reverse, σ_base x = none := fun x hx =>
      h_fresh_combined x (List.mem_append_left _ hx)
    have h_unique_accum : (Cmds.definedVars accum.reverse).Nodup :=
      (List.nodup_append.mp h_unique_combined).1
    have ⟨σ_cfg_after, h_step_flush, h_agree_after, h_preserve_flush⟩ :=
      flushCmds_simulation_agree extendEval "before_loop$" lentry accum gen_b gen_f
        accumEntry accumBlocks h_flush_eq σ_struct_base σ_base hf_base hf_accum ρ₀
        hwfb hwfv hwf_def hwf_congr h_accum h_agree_entry h_fresh_accum h_unique_accum
        h_hf cfg h_cfg_accum h_cfg_nodup
    -- === STEP 5: no-gen-suffix discharges and the store invariant. ===
    have h_body_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars [].reverse ++ Block.initVars body) := by
      rw [h_body_no_inits]; intro x hx; simp [Cmds.definedVars] at hx
    have h_rest_no_gen_suffix :
        NoGenSuffix (P := P) Q (Cmds.definedVars [].reverse ++ Block.initVars rest) := fun x hx s heq =>
      h_combined_no_gen_suffix x (List.mem_append_right _ (h_initvars_eq ▸
        (by simpa [Cmds.definedVars] using hx))) s heq
    have h_body_no_gen_suffix_mod :
        NoGenSuffix (P := P) Q (Cmds.modifiedVars [].reverse ++ transformBlockModVars body) :=
      fun x hx s heq => h_combined_no_gen_suffix_mod x
        (List.mem_append_right _ (by
          rw [transformBlockModVars_cons, transformStmtModVars_loop]
          exact List.mem_append_left _ (by simpa [Cmds.modifiedVars] using hx))) s heq
    let P_keep : P.Ident → Prop := fun x =>
      ∀ s : String, x = HasIdent.ident (P := P) s →
        s ∈ StringGenState.stringGens gen_le ∨ s ∉ StringGenState.stringGens gen_b
    let storeInv : SemanticStore P → Prop := fun σ =>
      ∀ x, P_keep x → σ_cfg_after x = none → σ x = none
    have h_inv_after : storeInv σ_cfg_after := fun x _ h => h
    have h_store_no_gens_upper_after :
        ∀ x : String, Q x →
          x ∉ StringGenState.stringGens genUpperBound →
          σ_cfg_after (HasIdent.ident (P := P) x) = none :=
      store_no_gens_lift_after_flush h_preserve_flush genUpperBound h_store_no_gens_upper
        (fun y hy => h_combined_no_gen_suffix y (List.mem_append_left _ hy))
    have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none := by
      intro x hx
      have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := fun h_in_accum =>
        (List.nodup_append.mp (h_initvars_eq ▸ h_unique_combined)).2.2 x h_in_accum x hx rfl
      have h_σ_base_x : σ_base x = none :=
        h_fresh_combined x (h_initvars_eq ▸ List.mem_append_right _ hx)
      exact h_preserve_flush x h_σ_base_x h_x_not_accum
    -- The store-no-gens-iter derivation shared between the two body-sim oracles.
    have h_sng_of_inv : ∀ σ, storeInv σ →
        ∀ x : String, Q x →
          x ∉ StringGenState.stringGens genUpperBound →
          σ (HasIdent.ident (P := P) x) = none := by
      intro σ h_inv x hx_sfx hx_notin
      have h_keep : P_keep (HasIdent.ident (P := P) x) := by
        intro s heq
        have hs_eq : x = s := LawfulHasIdent.ident_inj heq
        subst hs_eq
        exact Or.inr (fun h_in_b => hx_notin (h_outer_upper_b h_in_b))
      exact h_inv _ h_keep (h_store_no_gens_upper_after x hx_sfx hx_notin)
    -- === STEP 6: Body-sim oracle for terminating iterations. ===
    have h_body_sim_at :
        ∀ (ρ_iter : Env P) (σ_cfg_iter : SemanticStore P),
          ρ_iter.eval = ρ₀.eval →
          StoreAgreement ρ_iter.store σ_cfg_iter →
          storeInv σ_cfg_iter →
          ∀ (ρ_body : Env P), StepStmtStar P (EvalCmd P) extendEval
              (.stmts body ρ_iter) (.terminal ρ_body) →
            ∃ σ_cfg_after_body,
              StepDetCFGStar extendEval cfg
                (.atBlock bl σ_cfg_iter ρ_iter.hasFailure)
                (.atBlock lentry σ_cfg_after_body ρ_body.hasFailure) ∧
              StoreAgreement ρ_body.store σ_cfg_after_body ∧
              storeInv σ_cfg_after_body := by
      intro ρ_iter σ_cfg_iter h_eval_iter h_agree_iter h_inv_iter ρ_body h_body_run
      have hwfb_iter : WellFormedSemanticEvalBool ρ_iter.eval := h_eval_iter ▸ hwfb
      have hwfv_iter : WellFormedSemanticEvalVal ρ_iter.eval := h_eval_iter ▸ hwfv
      have hwf_def_iter : WellFormedSemanticEvalDef ρ_iter.eval := h_eval_iter ▸ hwf_def
      have hwf_congr_iter : WellFormedSemanticEvalExprCongr ρ_iter.eval := h_eval_iter ▸ hwf_congr
      have hwf_var_iter : WellFormedSemanticEvalVar ρ_iter.eval := h_eval_iter ▸ hwf_var
      have h_combined_body : ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
          σ_cfg_iter x = none := by
        intro x hx; rw [h_body_no_inits] at hx; simp [Cmds.definedVars] at hx
      have h_unique_combined_body : (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
        rw [h_body_no_inits]; simp [Cmds.definedVars]
      have h_accum_nil : EvalCmds P (EvalCmd P) ρ_iter.eval ρ_iter.store
          [].reverse ρ_iter.store false := EvalCmds.eval_cmds_none
      have h_hf_iter : ρ_iter.hasFailure = (ρ_iter.hasFailure || false) := by simp
      have ⟨σ_cfg_after_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
        stmtsToBlocks_simulation extendEval lentry body ((.none, kNext) :: exitConts) []
          gen_le gen_b bl bbs h_body_eq h_nofd_body h_simple_body h_unique_body
          h_lbni_body h_lhni_body h_nml_body
          ρ_iter.store σ_cfg_iter ρ_iter.hasFailure false
          ρ_iter ρ_body hwfb_iter hwfv_iter hwf_def_iter hwf_congr_iter hwf_var_iter
          h_body_run h_accum_nil h_agree_iter
          h_combined_body h_unique_combined_body h_hf_iter
          h_wf_le h_body_no_gen_suffix h_body_no_gen_suffix_mod
          genUpperBound h_outer_upper_b (h_sng_of_inv σ_cfg_iter h_inv_iter) h_foreign
          cfg h_cfg_bbs h_cfg_nodup
      refine ⟨σ_cfg_after_body, h_step_body, h_agree_body, ?_⟩
      intro x h_keep h_after_x
      have h_iter_x : σ_cfg_iter x = none := h_inv_iter x h_keep h_after_x
      have h_nil_not : x ∉ Cmds.definedVars ([] : List (Cmd P)).reverse := by simp [Cmds.definedVars]
      have h_not_body : x ∉ Block.initVars body := by rw [h_body_no_inits]; simp
      exact h_preserve_body x h_iter_x h_nil_not h_not_body h_keep
    -- === STEP 6b: Body-sim oracle for the exiting iteration. ===
    -- The label resolution: ((.none, kNext) :: exitConts).lookup (.some label) = bk_target.
    have h_label_lookup :
        ((.none, kNext) :: exitConts).lookup (.some label) = some bk_target := by
      simp [List.lookup, h_label]
    have h_body_sim_exit_at :
        ∀ (ρ_iter : Env P) (σ_cfg_iter : SemanticStore P),
          ρ_iter.eval = ρ₀.eval →
          StoreAgreement ρ_iter.store σ_cfg_iter →
          storeInv σ_cfg_iter →
          ∀ (ρ_body : Env P), StepStmtStar P (EvalCmd P) extendEval
              (.stmts body ρ_iter) (.exiting label ρ_body) →
            ∃ σ_cfg_after_body,
              StepDetCFGStar extendEval cfg
                (.atBlock bl σ_cfg_iter ρ_iter.hasFailure)
                (.atBlock bk_target σ_cfg_after_body ρ_body.hasFailure) ∧
              StoreAgreement ρ_body.store σ_cfg_after_body ∧
              storeInv σ_cfg_after_body := by
      intro ρ_iter σ_cfg_iter h_eval_iter h_agree_iter h_inv_iter ρ_body h_body_exit
      have hwfb_iter : WellFormedSemanticEvalBool ρ_iter.eval := h_eval_iter ▸ hwfb
      have hwfv_iter : WellFormedSemanticEvalVal ρ_iter.eval := h_eval_iter ▸ hwfv
      have hwf_def_iter : WellFormedSemanticEvalDef ρ_iter.eval := h_eval_iter ▸ hwf_def
      have hwf_congr_iter : WellFormedSemanticEvalExprCongr ρ_iter.eval := h_eval_iter ▸ hwf_congr
      have hwf_var_iter : WellFormedSemanticEvalVar ρ_iter.eval := h_eval_iter ▸ hwf_var
      have h_combined_body : ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
          σ_cfg_iter x = none := by
        intro x hx; rw [h_body_no_inits] at hx; simp [Cmds.definedVars] at hx
      have h_unique_combined_body : (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
        rw [h_body_no_inits]; simp [Cmds.definedVars]
      have h_accum_nil : EvalCmds P (EvalCmd P) ρ_iter.eval ρ_iter.store
          [].reverse ρ_iter.store false := EvalCmds.eval_cmds_none
      have h_hf_iter : ρ_iter.hasFailure = (ρ_iter.hasFailure || false) := by simp
      have ⟨σ_cfg_after_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
        stmtsToBlocks_simulation_to_cont extendEval lentry body ((.none, kNext) :: exitConts) []
          gen_le gen_b bl bbs h_body_eq h_nofd_body h_simple_body h_unique_body
          h_lbni_body h_lhni_body h_nml_body
          ρ_iter.store σ_cfg_iter ρ_iter.hasFailure false
          ρ_iter ρ_body label bk_target h_label_lookup
          hwfb_iter hwfv_iter hwf_def_iter hwf_congr_iter hwf_var_iter
          h_body_exit h_accum_nil h_agree_iter
          h_combined_body h_unique_combined_body h_hf_iter
          h_wf_le h_body_no_gen_suffix h_body_no_gen_suffix_mod
          genUpperBound h_outer_upper_b (h_sng_of_inv σ_cfg_iter h_inv_iter) h_foreign
          cfg h_cfg_bbs h_cfg_nodup
      refine ⟨σ_cfg_after_body, h_step_body, h_agree_body, ?_⟩
      intro x h_keep h_after_x
      have h_iter_x : σ_cfg_iter x = none := h_inv_iter x h_keep h_after_x
      have h_nil_not : x ∉ Cmds.definedVars ([] : List (Cmd P)).reverse := by simp [Cmds.definedVars]
      have h_not_body : x ∉ Block.initVars body := by rw [h_body_no_inits]; simp
      exact h_preserve_body x h_iter_x h_nil_not h_not_body h_keep
    -- === STEP 7: Dispatch on the exit. ===
    rcases h_exit_dispatch with ⟨ρ_loop_post, h_loop_exit, hρ'_eq⟩ | h_caseB
    · -- CASE A: loop body exits with label → bk_target directly.
      subst hρ'_eq
      have ⟨σ_cfg_bk, h_loop_run, h_agree_bk, h_inv_bk⟩ :=
        InlineLoopHelpers.loop_iterations_to_cont_det extendEval guardExpr body md
          ρ₀ ρ' label cfg lentry kNext bl bk_target σ_cfg_after storeInv
          h_lentry_lkp h_agree_after h_inv_after h_loop_exit h_nofd_body
          h_body_sim_at h_body_sim_exit_at hwfb hwf_def hwf_congr
      refine ⟨σ_cfg_bk, ?_, h_agree_bk, ?_⟩
      · exact StepDetCFGStar_trans h_step_flush h_loop_run
      · intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
        have h_x_not_rest : x ∉ Block.initVars rest := fun hx =>
          h_x_not_inits (h_initvars_eq ▸ hx)
        have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
        have h_keep : P_keep x := by
          intro s heq
          rcases h_outer_guard s heq with h_in_gen | h_notin_gen'
          · exact Or.inl (h_step_gen_to_le.subset h_in_gen)
          · exact Or.inr (fun h_in_b => h_notin_gen' (h_step_b_to_f.subset h_in_b))
        exact h_inv_bk x h_keep h_σ_after_x
    · -- CASE B: loop terminates, then rest exits with label.
      obtain ⟨ρ_loop_post, h_loop_term, h_rest_exit⟩ := h_caseB
      have h_loop_stmt := h_loop_term
      have ⟨σ_cfg_kNext, h_loop_run, h_agree_loop, h_inv_loop⟩ :=
        InlineLoopHelpers.loop_iterations_det extendEval guardExpr body md ρ₀ ρ_loop_post
          cfg lentry kNext bl σ_cfg_after storeInv h_lentry_lkp h_agree_after h_inv_after
          h_loop_stmt h_nofd_body h_body_sim_at
          hwfb hwf_def hwf_congr
      have h_sng_loop : ∀ x : String, Q x →
          x ∉ StringGenState.stringGens genUpperBound →
          σ_cfg_kNext (HasIdent.ident (P := P) x) = none :=
        h_sng_of_inv σ_cfg_kNext h_inv_loop
      have h_fresh_rest_loop : ∀ x ∈ Block.initVars rest, σ_cfg_kNext x = none := by
        intro x hx
        have h_keep : P_keep x := by
          intro s heq
          exact Or.inr (fun h_in_b =>
            h_foreign s
              (h_rest_no_gen_suffix x (by simpa [Cmds.definedVars] using hx) s heq)
              (h_outer_upper_b h_in_b))
        exact h_inv_loop x h_keep (h_fresh_rest_inits_after x hx)
      have h_loop_stmts : StepStmtStar P (EvalCmd P) extendEval
          (.stmts [.loop (.det guardExpr) none [] body md] ρ₀) (.terminal ρ_loop_post) :=
        ReflTrans_Transitive _ _ _ _
          (stmts_cons_step P (EvalCmd P) extendEval _ [] ρ₀ ρ_loop_post h_loop_term)
          (.step _ _ _ .step_stmts_nil (.refl _))
      have h_eval_loop : ρ_loop_post.eval = ρ₀.eval :=
        smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
          [.loop (.det guardExpr) none [] body md] ρ₀ ρ_loop_post
          (by simp [Block.noFuncDecl, Stmt.noFuncDecl, h_nofd_body])
          h_loop_stmts
      have hwfb_loop : WellFormedSemanticEvalBool ρ_loop_post.eval := h_eval_loop ▸ hwfb
      have hwfv_loop : WellFormedSemanticEvalVal ρ_loop_post.eval := h_eval_loop ▸ hwfv
      have hwf_def_loop : WellFormedSemanticEvalDef ρ_loop_post.eval := h_eval_loop ▸ hwf_def
      have hwf_congr_loop : WellFormedSemanticEvalExprCongr ρ_loop_post.eval := h_eval_loop ▸ hwf_congr
      have hwf_var_loop : WellFormedSemanticEvalVar ρ_loop_post.eval := h_eval_loop ▸ hwf_var
      have h_combined_rest : ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
          σ_cfg_kNext x = none := fun x hx =>
        h_fresh_rest_loop x (by simpa [Cmds.definedVars] using hx)
      have h_unique_combined_rest : (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
        simpa [Cmds.definedVars, Block.uniqueInits] using h_unique_rest
      have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_loop_post.eval ρ_loop_post.store
          [].reverse ρ_loop_post.store false := EvalCmds.eval_cmds_none
      have h_hf_loop : ρ_loop_post.hasFailure = (ρ_loop_post.hasFailure || false) := by simp
      have h_rest_no_gen_suffix_mod :
          NoGenSuffix (P := P) Q (Cmds.modifiedVars [].reverse ++ transformBlockModVars rest) :=
        fun x hx s heq => h_combined_no_gen_suffix_mod x
          (List.mem_append_right _ (by
            rw [transformBlockModVars_cons, transformStmtModVars_loop]
            exact List.mem_append_right _ (by simpa [Cmds.modifiedVars] using hx))) s heq
      have ⟨σ_cfg, h_rest_sim, h_agree_rest, h_preserve_rest⟩ :=
        stmtsToBlocks_simulation_to_cont extendEval k rest exitConts [] gen gen_r kNext bsRest
          h_rest_eq h_nofd_rest h_simple_rest h_unique_rest
          h_lbni_rest h_lhni_rest h_nml_rest
          ρ_loop_post.store σ_cfg_kNext ρ_loop_post.hasFailure false
          ρ_loop_post ρ' label bk_target h_label
          hwfb_loop hwfv_loop hwf_def_loop hwf_congr_loop hwf_var_loop
          h_rest_exit h_accum_nil_r h_agree_loop
          h_combined_rest h_unique_combined_rest h_hf_loop
          h_wf_gen h_rest_no_gen_suffix h_rest_no_gen_suffix_mod
          genUpperBound h_outer_upper_r h_sng_loop h_foreign
          cfg h_cfg_bsRest h_cfg_nodup
      refine ⟨σ_cfg, ?_, h_agree_rest, ?_⟩
      · exact StepDetCFGStar_trans (StepDetCFGStar_trans h_step_flush h_loop_run) h_rest_sim
      · intro x h_σ_x h_x_not_accum h_x_not_inits h_outer_guard
        have h_x_not_rest : x ∉ Block.initVars rest := fun hx =>
          h_x_not_inits (h_initvars_eq ▸ hx)
        have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
        have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
        have h_keep : P_keep x := by
          intro s heq
          rcases h_outer_guard s heq with h_in_gen | h_notin_gen'
          · exact Or.inl (h_step_gen_to_le.subset h_in_gen)
          · exact Or.inr (fun h_in_b => h_notin_gen' (h_step_b_to_f.subset h_in_b))
        have h_x_fresh_loop : σ_cfg_kNext x = none := h_inv_loop x h_keep h_σ_after_x
        have h_guard_rest : ∀ s : String, x = HasIdent.ident (P := P) s →
            s ∈ StringGenState.stringGens gen ∨ s ∉ StringGenState.stringGens gen_r :=
          fun s heq => match h_outer_guard s heq with
            | Or.inl h_in => Or.inl h_in
            | Or.inr h_notin => Or.inr (fun h_in_r => h_notin
                (h_step_b_to_f.subset (h_step_le_to_b.subset (h_step_r_to_le.subset h_in_r))))
        exact h_preserve_rest x h_x_fresh_loop h_nil_not h_x_not_rest h_guard_rest
termination_by sizeOf ss
decreasing_by
  all_goals (subst h_match; simp_wf; omega)
end


/-! ## Top-level theorems -/

/-- Specification lemma: `stmtsToCFG` produces a CFG whose blocks come from
`stmtsToBlocks` plus a terminal block, and whose entry matches.
Specialized to `CmdT = Cmd P` so we can use `stmtsToBlocks_invariant`
(which depends on the `[HasNot P]` instance present on `Cmd P`). -/
theorem stmtsToCFG_stmtsToBlocks_spec {P : PureExpr}
    [HasBool P] [HasIdent P] [HasFvar P] [HasIntOrder P] [HasNot P]
    (ss : List (Stmt P (Cmd P)))
    (h_disj : ∀ gen', StringGenState.WF gen' → Block.userLabelsDisjoint ss gen') :
    ∃ (lend : String) (gen gen' : StringGenState)
      (entry : String) (blocks : DetBlocks String (Cmd P) P),
      stmtsToBlocks lend ss [] [] gen = ((entry, blocks), gen') ∧
      (stmtsToCFG ss).entry = entry ∧
      (∀ b ∈ blocks, b ∈ (stmtsToCFG ss).blocks) ∧
      (stmtsToCFG ss).blocks.lookup lend =
        some ({ cmds := [], transfer := .finish synthesizedMd } : BasicBlock (DetTransferCmd String P) (Cmd P)) ∧
      StringGenState.WF gen ∧
      -- `gen` is the generator state after the single `"end$"` mint that
      -- `stmtsToCFGM` performs before invoking `stmtsToBlocks`.  Exposing this
      -- lets the caller track `AllMem` from `StringGenState.emp` through to the
      -- output `gen'`, which underpins the foreign-label self-discharge.
      gen = (StringGenState.gen "end$" StringGenState.emp).2 := by
  let p_end := StringGenState.gen "end$" StringGenState.emp
  let lend := p_end.1
  let gen0 := p_end.2
  let r := stmtsToBlocks lend ss ([] : List (Option String × String)) ([] : List (Cmd P)) gen0
  have h_cfg : stmtsToCFG ss =
      { entry := r.1.1, blocks := r.1.2 ++ [(lend, { cmds := [], transfer := .finish synthesizedMd })] } := by
    simp [stmtsToCFG, stmtsToCFGM]
    rfl
  -- WF of gen0 (after one gen call from emp)
  have hwf0 : StringGenState.WF gen0 :=
    StringGenState.WFMono StringGenState.wf_emp rfl
  refine ⟨lend, gen0, r.2, r.1.1, r.1.2, rfl, ?_, ?_, ?_, hwf0, rfl⟩
  · simp [h_cfg]
  · intro b hb; simp [h_cfg]; exact Or.inl hb
  · -- Show lookup of lend in (r.1.2 ++ [(lend, finish)]) is the finish block.
    -- Strategy: use stmtsToBlocks_invariant to show lend ∉ r.1.2.map Prod.fst,
    -- then List.lookup skips past r.1.2 to find lend at the end.
    rw [h_cfg]
    show List.lookup lend (r.1.2 ++ [(lend, _)]) = _
    -- WF of gen0 (after one gen call from emp)
    have hwf0 : StringGenState.WF gen0 :=
      StringGenState.WFMono StringGenState.wf_emp rfl
    -- lend ∈ stringGens gen0
    have h_lend_in_gen0 : lend ∈ StringGenState.stringGens gen0 := by
      show lend ∈ StringGenState.stringGens p_end.2
      rw [StringGenState.stringGens_gen]; exact List.mem_cons.mpr (Or.inl rfl)
    -- All labels in r.1.2 are NOT in stringGens gen0 (by invariant fresh field)
    have h_eq : stmtsToBlocks lend ss [] [] gen0 = ((r.1.1, r.1.2), r.2) := rfl
    have hwf_r2 : StringGenState.WF r.2 :=
      (stmtsToBlocks_genStep lend ss [] [] gen0 r.2 r.1.1 r.1.2 h_eq).wf_mono hwf0
    have h_inv : @GenInv P gen0 r.2 (Block.userBlockLabels ss) r.1.2 :=
      stmtsToBlocks_invariant lend ss [] [] gen0 r.2 _ _ h_eq hwf0 (h_disj _ hwf_r2)
    have h_lend_not_in_blocks : lend ∉ r.1.2.map Prod.fst := by
      intro h_in
      cases h_inv.fresh _ h_in with
      | inl h_gen => exact h_gen.2 h_lend_in_gen0
      | inr h_user =>
        have h_lend_in_r2 : lend ∈ StringGenState.stringGens r.2 :=
          h_inv.toGenStep.subset h_lend_in_gen0
        exact h_inv.user_disj _ h_user h_lend_in_r2
    -- Now lookup lend in r.1.2 ++ [(lend, _)] = lookup lend [(lend, _)]
    rw [List.lookup_append]
    -- Helper lemma: lookup = some v implies (key, v) ∈ list
    have lookup_to_mem : ∀ {α β : Type} [BEq α] [LawfulBEq α]
        (l : List (α × β)) (k : α) (v : β), l.lookup k = some v → (k, v) ∈ l := by
      intro α β _ _ l k v hlk
      induction l with
      | nil => simp [List.lookup] at hlk
      | cons hd tl ih =>
        obtain ⟨k', v'⟩ := hd
        by_cases h_eq : k = k'
        · subst h_eq
          simp [List.lookup] at hlk
          subst hlk
          exact List.Mem.head _
        · have h_neq : ¬(k == k') = true := by simp [h_eq]
          simp [List.lookup, h_neq] at hlk
          exact List.mem_cons_of_mem _ (ih hlk)
    have h_lookup_none : List.lookup lend r.1.2 = none := by
      rcases h : List.lookup lend r.1.2 with _ | v
      · rfl
      · exfalso
        apply h_lend_not_in_blocks
        exact List.mem_map.mpr ⟨(lend, v), lookup_to_mem _ _ _ h, rfl⟩
    rw [h_lookup_none]
    simp [List.lookup, Option.or]
    rfl

private theorem end_block_terminal {P : PureExpr} [HasFvar P] [HasNot P] [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P)
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (lend : String) (σ : SemanticStore P) (δ : SemanticEval P) (failed : Bool)
    (h_lookup : cfg.blocks.lookup lend =
      some ({ cmds := [], transfer := .finish synthesizedMd } : DetBlock String (Cmd P) P)) :
    StepDetCFGStar extendEval cfg
      (.atBlock lend σ failed)
      (.terminal σ failed) := by
  have h_cmds : EvalCmds P (EvalCmd P) δ σ [] σ false :=
    EvalCmds.eval_cmds_none
  have h_run := run_block_finish (extendEval := extendEval) (cfg := cfg)
                  (f_base := failed) h_lookup h_cmds
  rw [Bool.or_false] at h_run
  exact h_run

/-- If the structured program reaches a terminal state, the CFG also reaches
    a corresponding terminal state.

    The CFG end-store agrees with the structured end-store on every defined
    variable (`StoreAgreement`); they may differ only on variables introduced
    by inner scopes (e.g. `.block`'s local frames).

    The label-kind predicate `Q` is constrained only by `hQmint`: the
    thirteen-conjunct witness that `Q` holds of every `gen`-output under the
    prefixes `stmtsToCFG` mints under.  From it the proof *derives* the
    foreign-label obligation — any label that is not `Q` is absent from the
    output generator — by tracking `AllMem Q` from the empty generator state
    (through the single `"end$"` mint and `stmtsToBlocks`) and discharging by
    contraposition, so no universal-over-all-WF-states freshness assumption is
    needed. -/
theorem stmtsToCFG_terminal {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasBool P] [LawfulHasIdent P]
    [LawfulHasIntOrder P] [LawfulHasNot P]
    {Q : String → Prop}
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P)))
    (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwf_def : WellFormedSemanticEvalDef ρ₀.eval)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (hwf_var : WellFormedSemanticEvalVar ρ₀.eval)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_simple : Block.simpleShape ss = true)
    (h_unique : Block.uniqueInits ss)
    (h_lbni : Block.loopBodyNoInits ss = true)
    (h_lhni : Block.loopHasNoInvariants ss = true)
    (h_nml : Block.noMeasureLoops ss = true)
    (h_fresh_inits : ∀ x ∈ Block.initVars ss, ρ₀.store x = none)
    (h_disj : Block.userLabelsShapeNodup ss)
    (h_store_gens : ∀ x : String, Q x → ρ₀.store (HasIdent.ident (P := P) x) = none)
    (h_input_no_gen_suffix : NoGenSuffix (P := P) Q (Block.initVars ss))
    (h_input_no_gen_suffix_mod : NoGenSuffix (P := P) Q (transformBlockModVars ss))
    (hQmint : S2UMintWitness Q)
    (h_term : StepStmtStar P (EvalCmd P) extendEval
      (.stmts ss ρ₀) (.terminal ρ')) :
    let cfg := stmtsToCFG ss
    ∃ σ_cfg, StepDetCFGStar extendEval cfg
      (.atBlock cfg.entry ρ₀.store ρ₀.hasFailure)
      (.terminal σ_cfg ρ'.hasFailure)
      ∧ StoreAgreement ρ'.store σ_cfg := by
  intro cfg
  -- Bridge the gen-free `userLabelsShapeNodup` precondition to the
  -- `∀ WF gen', userLabelsDisjoint ss gen'` form the spec/nodup helpers consume:
  -- the disjointness conjunct is recovered from shape-freedom at any WF state.
  have h_disj_wf : ∀ gen', StringGenState.WF gen' → Block.userLabelsDisjoint ss gen' :=
    Block.userLabelsDisjoint_of_shapeNodup ss h_disj
  have ⟨lend, gen, gen', entry, blocks, h_gen, h_entry, h_blocks, h_lend, h_wf_gen, h_gen0⟩ :=
    stmtsToCFG_stmtsToBlocks_spec ss h_disj_wf
  rw [h_entry]
  have h_accum : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store [].reverse ρ₀.store false :=
    EvalCmds.eval_cmds_none
  have h_hf : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
  have h_nodup := stmtsToCFG_nodup_keys ss h_disj_wf
  -- Combined freshness/Nodup: empty accum, so reduces to just inits.
  have h_fresh_combined : ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars ss,
      ρ₀.store x = none := by
    intro x hx
    simp [Cmds.definedVars] at hx
    exact h_fresh_inits x hx
  have h_unique_combined : (Cmds.definedVars [].reverse ++ Block.initVars ss).Nodup := by
    simp [Cmds.definedVars]
    exact h_unique
  have h_combined_no_gen_suffix :
      NoGenSuffix (P := P) Q (Cmds.definedVars [].reverse ++ Block.initVars ss) := by
    intro x hx s heq
    simp [Cmds.definedVars] at hx
    exact h_input_no_gen_suffix x hx s heq
  have h_combined_no_gen_suffix_mod :
      NoGenSuffix (P := P) Q (Cmds.modifiedVars [].reverse ++ transformBlockModVars ss) := by
    intro x hx s heq
    simp [Cmds.modifiedVars] at hx
    exact h_input_no_gen_suffix_mod x hx s heq
  have h_store_no_gens_upper :
      ∀ x : String, Q x →
        x ∉ StringGenState.stringGens gen' →
        ρ₀.store (HasIdent.ident (P := P) x) = none := fun x hx _ => h_store_gens x hx
  -- Self-discharge of the foreign-label obligation.  `gen` is the empty
  -- generator state advanced by the single `"end$"` mint; every label `gen`
  -- holds therefore satisfies `Q` (by `hQmint`'s `"end$"` witness).
  -- `stmtsToBlocks_allMem` carries this to `gen'`: every label `gen'` holds
  -- satisfies `Q`.  Hence any label that is *not* `Q` is absent — plain
  -- contraposition, no universal-WF assumption needed.
  have h_allmem_gen : StringGenState.AllMem Q gen := by
    rw [h_gen0]
    exact StringGenState.allMem_gen Q "end$" StringGenState.emp
      (StringGenState.allMem_emp Q) (hQmint.2.2.2.2.2.2.2.2.1 StringGenState.emp)
  have h_allmem_gen' : StringGenState.AllMem Q gen' :=
    stmtsToBlocks_allMem hQmint lend ss [] [] gen gen' entry blocks h_gen h_allmem_gen
  have h_foreign : ∀ s : String, ¬ Q s → s ∉ StringGenState.stringGens gen' :=
    fun s hns => StringGenState.not_mem_stringGens_of_not_allMem h_allmem_gen' hns
  have ⟨σ_cfg, h_sim, h_agree, _h_preserve⟩ :=
    stmtsToBlocks_simulation extendEval lend ss [] [] gen gen' entry blocks
      h_gen h_nofd h_simple h_unique h_lbni h_lhni h_nml
      ρ₀.store ρ₀.store ρ₀.hasFailure false ρ₀ ρ' hwfb hwfv hwf_def hwf_congr hwf_var
      h_term h_accum (StoreAgreement.refl _) h_fresh_combined h_unique_combined h_hf
      h_wf_gen h_combined_no_gen_suffix h_combined_no_gen_suffix_mod
      gen' (fun _ h => h) h_store_no_gens_upper h_foreign
      cfg h_blocks h_nodup
  have h_end := end_block_terminal extendEval cfg lend σ_cfg ρ'.eval ρ'.hasFailure h_lend
  exact ⟨σ_cfg, StepDetCFGStar_trans h_sim h_end, h_agree⟩

/-! ## Main theorems -/

/-! ### The structured-to-unstructured label *kind*

`stmtsToCFG` mints block labels under thirteen distinct prefixes.  Eight come
from the direct `gen` calls — one per syntactic construct it compiles:
`"ite"`, `"$__nondet_ite$"`, `"loop_entry$"`, `"loop_measure$"`,
`"measure_decrease$"`, `"inv$"`, `"$__nondet_loop$"`, and `"end$"`.  Four more
come from the auxiliary `flushCmds` helper that emits accumulated command
blocks: `"l$"` (the statement-list tail), `"blk$"` (the `.block` arm), `"ite$"`
(the `.ite` arm), and `"before_loop$"` (the `.loop` arm).  The thirteenth is
parametric: the `.exit` arm flushes under `"block$⟨l⟩$"` where `l` is the user
block label being exited.  `s2uKind s` is the precise predicate "`s` is a label
this pass could have minted under one of those prefixes": it carries the
matching generator prefix and equals some `gen`-output.  This is the per-kind
`Q` to instantiate the kind-generalized soundness at, replacing the blanket
`HasUnderscoreDigitSuffix` (which would overcommit a composition partner to
keeping *every* gen-shaped name fresh). -/

/-- A label that `stmtsToCFG` could have minted: it carries one of the thirteen
construct prefixes and equals a corresponding `gen` output.  Twelve prefixes are
fixed; the last is parameterised by the user block label being exited. -/
@[expose] def s2uKind (s : String) : Prop :=
  (∃ sg, String.HasGenPrefix "ite" s
      ∧ s = (StringGenState.gen "ite" sg).1)
  ∨ (∃ sg, String.HasGenPrefix "$__nondet_ite$" s
      ∧ s = (StringGenState.gen "$__nondet_ite$" sg).1)
  ∨ (∃ sg, String.HasGenPrefix "ite$" s
      ∧ s = (StringGenState.gen "ite$" sg).1)
  ∨ (∃ sg, String.HasGenPrefix "loop_entry$" s
      ∧ s = (StringGenState.gen "loop_entry$" sg).1)
  ∨ (∃ sg, String.HasGenPrefix "loop_measure$" s
      ∧ s = (StringGenState.gen "loop_measure$" sg).1)
  ∨ (∃ sg, String.HasGenPrefix "measure_decrease$" s
      ∧ s = (StringGenState.gen "measure_decrease$" sg).1)
  ∨ (∃ sg, String.HasGenPrefix "inv$" s
      ∧ s = (StringGenState.gen "inv$" sg).1)
  ∨ (∃ sg, String.HasGenPrefix "$__nondet_loop$" s
      ∧ s = (StringGenState.gen "$__nondet_loop$" sg).1)
  ∨ (∃ sg, String.HasGenPrefix "end$" s
      ∧ s = (StringGenState.gen "end$" sg).1)
  ∨ (∃ sg, String.HasGenPrefix "l$" s
      ∧ s = (StringGenState.gen "l$" sg).1)
  ∨ (∃ sg, String.HasGenPrefix "blk$" s
      ∧ s = (StringGenState.gen "blk$" sg).1)
  ∨ (∃ sg, String.HasGenPrefix "before_loop$" s
      ∧ s = (StringGenState.gen "before_loop$" sg).1)
  ∨ (∃ l : String, ∃ sg, String.HasGenPrefix (s!"block${l}$") s
      ∧ s = (StringGenState.gen (s!"block${l}$") sg).1)

/-- Each of the thirteen prefixes `stmtsToCFG` mints under lands inside
`s2uKind`: this is exactly the thirteen-conjunct mint witness at
`Q := s2uKind`, the analogue of `ndelimKind_gen` for the S2U construct prefixes.
The final conjunct is parametric in the user block label `l`. -/
theorem s2uKind_gen : S2UMintWitness s2uKind := by
  refine ⟨fun sg => ?_, fun sg => ?_, fun sg => ?_, fun sg => ?_, fun sg => ?_,
          fun sg => ?_, fun sg => ?_, fun sg => ?_, fun sg => ?_, fun sg => ?_,
          fun sg => ?_, fun sg => ?_, fun l sg => ?_⟩
  · exact Or.inl ⟨sg, StringGenState.gen_hasGenPrefix "ite" sg, rfl⟩
  · exact Or.inr (Or.inl ⟨sg, StringGenState.gen_hasGenPrefix "$__nondet_ite$" sg, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨sg, StringGenState.gen_hasGenPrefix "ite$" sg, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨sg, StringGenState.gen_hasGenPrefix "loop_entry$" sg, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨sg, StringGenState.gen_hasGenPrefix "loop_measure$" sg, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨sg, StringGenState.gen_hasGenPrefix "measure_decrease$" sg, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨sg, StringGenState.gen_hasGenPrefix "inv$" sg, rfl⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨sg, StringGenState.gen_hasGenPrefix "$__nondet_loop$" sg, rfl⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨sg, StringGenState.gen_hasGenPrefix "end$" sg, rfl⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨sg, StringGenState.gen_hasGenPrefix "l$" sg, rfl⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨sg, StringGenState.gen_hasGenPrefix "blk$" sg, rfl⟩))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨sg, StringGenState.gen_hasGenPrefix "before_loop$" sg, rfl⟩)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨l, sg, StringGenState.gen_hasGenPrefix (s!"block${l}$") sg, rfl⟩)))))))))))

/-- Kind-generalized soundness of `stmtsToCFG`.  Like a blanket-freshness
formulation but with the threaded input-freshness invariant (`NoGenSuffix`)
constraining only the labels *this* pass mints (`s2uKind`) rather than every
gen-shaped name, which is what lets a composition partner — one that mints under
disjoint prefixes — satisfy it.

Unlike the structured-to-structured passes (`nondetElim`, the loop-init hoist),
`stmtsToCFG` produces a CFG and so its soundness must dispatch a *foreign-label*
obligation: any label not minted by this pass is absent from the output
generator's `stringGens`.  This obligation is *not* derivable from
well-formedness alone at the finer `Q := s2uKind` — `stmtsToCFG` also mints under
auxiliary `flushCmds` prefixes (`"l$"`, `"blk$"`, `"before_loop$"`, and a
user-label-parameterised `"block$⟨l⟩$"`), so a generic WF state may legitimately
contain non-`s2uKind` labels.  It is instead discharged *internally* by
`stmtsToCFG_terminal`: from the thirteen-conjunct mint witness `hQmint` it tracks
`AllMem Q` from the empty generator state through the pass, so every label the
pass produces satisfies `Q`, and any label that is not `Q` is absent by
contraposition.  Phase 4 therefore supplies only `hQmint` (via `s2uKind_gen` at
`Q := s2uKind`) — there is no separate foreign hypothesis to discharge. -/
theorem structuredToUnstructured_sound_kind {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    [LawfulHasFvar P] [LawfulHasBool P] [LawfulHasIdent P]
    [LawfulHasIntOrder P] [LawfulHasNot P]
    {Q : String → Prop}
    (hQmint : S2UMintWitness Q)
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P)))
    (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwf_def : WellFormedSemanticEvalDef ρ₀.eval)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (hwf_var : WellFormedSemanticEvalVar ρ₀.eval)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_simple : Block.simpleShape ss = true)
    (h_unique : Block.uniqueInits ss)
    (h_lbni : Block.loopBodyNoInits ss = true)
    (h_lhni : Block.loopHasNoInvariants ss = true)
    (h_nml : Block.noMeasureLoops ss = true)
    (h_fresh_inits : ∀ x ∈ Block.initVars ss, ρ₀.store x = none)
    (h_disj : Block.userLabelsShapeNodup ss)
    (h_store_gens : ∀ x : String, Q x → ρ₀.store (HasIdent.ident (P := P) x) = none)
    (h_input_no_gen_suffix : NoGenSuffix (P := P) Q (Block.initVars ss))
    (h_input_no_gen_suffix_mod : NoGenSuffix (P := P) Q (transformBlockModVars ss))
    (h_term : StepStmtStar P (EvalCmd P) extendEval
      (.stmts ss ρ₀) (.terminal ρ')) :
    let cfg := stmtsToCFG ss
    ∃ σ_cfg, StepDetCFGStar extendEval cfg
      (.atBlock cfg.entry ρ₀.store ρ₀.hasFailure)
      (.terminal σ_cfg ρ'.hasFailure)
      ∧ StoreAgreement ρ'.store σ_cfg :=
  -- `hQmint` is the thirteen-conjunct mint witness for the construct prefixes —
  -- definitionally `S2UMintWitness Q`.  `stmtsToCFG_terminal` consumes it to
  -- *derive* the foreign-label obligation internally (via `AllMem Q`), so this
  -- handle needs no separate foreign hypothesis.  A composition partner supplies
  -- `hQmint` via `s2uKind_gen` at `Q := s2uKind`.
  stmtsToCFG_terminal (Q := Q)
    extendEval ss ρ₀ ρ' hwfb hwfv hwf_def hwf_congr hwf_var
    h_nofd h_simple h_unique h_lbni h_lhni h_nml
    h_fresh_inits h_disj h_store_gens h_input_no_gen_suffix
    h_input_no_gen_suffix_mod hQmint h_term

---------------------------------------------------------------------
-- Loop-init-hoisting additive helpers (ported; used by LoopInitHoist*).
---------------------------------------------------------------------

/-- Extend a `SemanticStore` with a single `(ident, value)` binding.
Returns a function that maps `ident` to `some value` and delegates other
keys to the original store. -/
@[expose] def extendStoreOne {P : PureExpr} [DecidableEq P.Ident]
    (σ : SemanticStore P) (ident : P.Ident) (val : P.Expr) :
    SemanticStore P :=
  fun y => if y = ident then some val else σ y

/-- `extendStoreOne` evaluated at the bound ident returns `some val`. -/
theorem extendStoreOne_self {P : PureExpr} [DecidableEq P.Ident]
    (σ : SemanticStore P) (ident : P.Ident) (val : P.Expr) :
    extendStoreOne σ ident val ident = some val := by
  simp [extendStoreOne]

/-- `extendStoreOne` evaluated at any other ident equals the original
store. -/
theorem extendStoreOne_other {P : PureExpr} [DecidableEq P.Ident]
    (σ : SemanticStore P) (ident : P.Ident) (val : P.Expr)
    (y : P.Ident) (h : y ≠ ident) :
    extendStoreOne σ ident val y = σ y := by
  simp [extendStoreOne, h]

end StructuredToUnstructuredCorrect

end -- public section
