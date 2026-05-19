/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.KleeneSemanticsProps
public import Strata.Transform.StructuredToUnstructured
public import Strata.Transform.Specification
public import Strata.DL.Util.StringGen
public import Strata.Languages.Core.StatementSemantics
import all Strata.DL.Imperative.BasicBlock
import all Strata.DL.Imperative.Cmd

/-! # Structured-to-Unstructured Transformation Correctness

This file proves that `stmtsToCFG` is semantics-preserving: the generated CFG
overapproximates the original structured statements. Specifically, any terminal
store reachable by executing the structured program is also reachable by
executing the CFG.

The top-level theorem is `structuredToUnstructured_sound`.

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

/-! ## Lang instances -/

/-- The structured `Lang` for `Cmd P`. -/
abbrev Lang.structured {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVal P]
    [HasIdent P] [HasIntOrder P]
    (extendEval : ExtendEval P) : Lang P :=
  Lang.imperative P (Cmd P) (EvalCmd P) extendEval (isAtAssert P)

/-- Configuration for the CFG `Lang`: wraps `CFGConfig` with the eval function
    so that `getEnv` can reconstruct a full `Env P`. -/
structure CFGLangConfig (P : PureExpr) where
  cfgConfig : CFGConfig String P
  eval : SemanticEval P

/-- Extract an `Env P` from a `CFGLangConfig`. -/
def CFGLangConfig.toEnv {P : PureExpr} (c : CFGLangConfig P) : Env P :=
  match c.cfgConfig with
  | .cont _ σ f => ⟨σ, c.eval, f⟩
  | .terminal σ f => ⟨σ, c.eval, f⟩

/-- Assert detection in a CFG configuration: an assert is active if the
    current block's command list head is an assert matching the given id. -/
def cfgIsAtAssert {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (cfg : CFG String (DetBlock String (Cmd P) P))
    : CFGLangConfig P → AssertId P → Prop
  | ⟨.cont lbl _ _, _⟩, aid =>
    match cfg.blocks.lookup lbl with
    | some blk => match blk.cmds with
      | .assert label expr _ :: _ => aid.label = label ∧ aid.expr = expr
      | _ => False
    | none => False
  | ⟨.terminal _ _, _⟩, _ => False

/-- The CFG `Lang` for `Cmd P`. -/
abbrev Lang.cfg {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVal P]
    [HasIdent P] [HasIntOrder P]
    (extendEval : ExtendEval P)
    (cfg : CFG String (DetBlock String (Cmd P) P)) : Lang P where
  StmtT := CFG String (DetBlock String (Cmd P) P)
  CfgT := CFGLangConfig P
  star := fun c₁ c₂ =>
    @StepCFGStar _ _ (Cmd P) _ P (EvalDetBlock P (EvalCmd P) extendEval) cfg c₁.cfgConfig c₂.cfgConfig
  stmtCfg := fun _ ρ => ⟨.cont cfg.entry ρ.store false, ρ.eval⟩
  terminalCfg := fun ρ => ⟨.terminal ρ.store ρ.hasFailure, ρ.eval⟩
  exitingCfg := fun _ ρ => ⟨.terminal ρ.store ρ.hasFailure, ρ.eval⟩
  isAtAssert := cfgIsAtAssert cfg
  getEnv := CFGLangConfig.toEnv

/-! ## Abbreviations -/
@[simp]
abbrev StepDetCFGStar {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (extendEval : ExtendEval P)
    (cfg : CFG String (DetBlock String (Cmd P) P)) :=
  @StepCFGStar _ _ (Cmd P) _ P (EvalDetBlock P (EvalCmd P) extendEval) cfg

theorem StepDetCFGStar_trans {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    {extendEval : ExtendEval P}
    {cfg : CFG String (DetBlock String (Cmd P) P)}
    {a b c : CFGConfig String P}
    (h₁ : StepDetCFGStar extendEval cfg a b)
    (h₂ : StepDetCFGStar extendEval cfg b c) :
    StepDetCFGStar extendEval cfg a c :=
  ReflTrans_Transitive _ _ _ _ h₁ h₂

/-! ## Bridge: EvalCmds and connectors to EvalDetBlock

`EvalDetBlock` (in `CFGSemantics.lean`) folds command evaluation directly into
its `cmd` constructor.  These proofs were originally written against an older
shape that delegated to a separate `EvalCmds` inductive, so we re-introduce
that inductive here as a proof helper and provide bridge lemmas that build the
corresponding `EvalDetBlock` derivations from an `EvalCmds` proof of the
block's command list. -/

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

namespace EvalDetBlock

variable {l : Type} {P : PureExpr} {CmdT : Type}
    {EvalCmdR : EvalCmdParam P CmdT}
    {extendEval : ExtendEval P}
    [HasNot P]

/-- Build an `EvalDetBlock` derivation that runs the entire command list `cs`
sequentially via `EvalCmds`, then takes the true branch of a `condGoto`. -/
theorem step_goto_true
    {δ : SemanticEval P} {σ σ' : SemanticStore P}
    {cs : List CmdT} {c : P.Expr} {t e : l} {md : MetaData P}
    {failed : Bool}
    (h_cmds : EvalCmds P EvalCmdR δ σ cs σ' failed)
    (h_cond : δ σ' c = .some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool δ) :
    EvalDetBlock P EvalCmdR extendEval
      σ ⟨ cs, .condGoto c t e md ⟩ (.cont t σ' failed) := by
  induction h_cmds with
  | eval_cmds_none =>
    exact EvalDetBlock.goto_true h_cond hwfb
  | eval_cmds_some hcmd hcmds ih =>
    rename_i σ_in c_h σ_mid f_h cs_t σ_out f_t
    have h_inner :
        EvalDetBlock (l := l) P EvalCmdR extendEval
          σ_mid ⟨cs_t, .condGoto c t e md⟩ (.cont t σ_out f_t) :=
      ih h_cond
    have h_step := EvalDetBlock.cmd (extendEval := extendEval)
        (transfer := DetTransferCmd.condGoto c t e md) hcmd h_inner
    have h_eq : updateFailure (.cont t σ_out f_t) f_h
              = (CFGConfig.cont t σ_out (f_h || f_t) : CFGConfig l P) := by
      simp [updateFailure, Bool.or_comm]
    rw [h_eq] at h_step
    exact h_step

/-- Build an `EvalDetBlock` derivation that runs the entire command list `cs`
sequentially via `EvalCmds`, then takes the false branch of a `condGoto`. -/
theorem step_goto_false
    {δ : SemanticEval P} {σ σ' : SemanticStore P}
    {cs : List CmdT} {c : P.Expr} {t e : l} {md : MetaData P}
    {failed : Bool}
    (h_cmds : EvalCmds P EvalCmdR δ σ cs σ' failed)
    (h_cond : δ σ' c = .some HasBool.ff)
    (hwfb : WellFormedSemanticEvalBool δ) :
    EvalDetBlock P EvalCmdR extendEval
      σ ⟨ cs, .condGoto c t e md ⟩ (.cont e σ' failed) := by
  induction h_cmds with
  | eval_cmds_none =>
    exact EvalDetBlock.goto_false h_cond hwfb
  | eval_cmds_some hcmd hcmds ih =>
    rename_i σ_in c_h σ_mid f_h cs_t σ_out f_t
    have h_inner :
        EvalDetBlock (l := l) P EvalCmdR extendEval
          σ_mid ⟨cs_t, .condGoto c t e md⟩ (.cont e σ_out f_t) :=
      ih h_cond
    have h_step := EvalDetBlock.cmd (extendEval := extendEval)
        (transfer := DetTransferCmd.condGoto c t e md) hcmd h_inner
    have h_eq : updateFailure (.cont e σ_out f_t) f_h
              = (CFGConfig.cont e σ_out (f_h || f_t) : CFGConfig l P) := by
      simp [updateFailure, Bool.or_comm]
    rw [h_eq] at h_step
    exact h_step

/-- Build an `EvalDetBlock` derivation that runs the entire command list `cs`
sequentially via `EvalCmds`, then finishes. -/
theorem step_terminal
    {δ : SemanticEval P} {σ σ' : SemanticStore P}
    {cs : List CmdT} {md : MetaData P}
    {failed : Bool}
    (h_cmds : EvalCmds P EvalCmdR δ σ cs σ' failed) :
    EvalDetBlock (l := l) P EvalCmdR extendEval
      σ ⟨ cs, .finish md ⟩ (.terminal σ' failed) := by
  induction h_cmds with
  | eval_cmds_none =>
    exact EvalDetBlock.terminal
  | eval_cmds_some hcmd hcmds ih =>
    rename_i σ_in c_h σ_mid f_h cs_t σ_out f_t
    have h_inner :
        EvalDetBlock (l := l) P EvalCmdR extendEval
          σ_mid ⟨cs_t, .finish md⟩ (.terminal σ_out f_t) := ih
    have h_step := EvalDetBlock.cmd (extendEval := extendEval)
        (transfer := DetTransferCmd.finish md) hcmd h_inner
    have h_uf : updateFailure (.terminal σ_out f_t) f_h
              = (CFGConfig.terminal σ_out (f_t || f_h) : CFGConfig l P) := rfl
    have h_eq : updateFailure (.terminal σ_out f_t) f_h
              = (CFGConfig.terminal σ_out (f_h || f_t) : CFGConfig l P) := by
      rw [h_uf, Bool.or_comm]
    rw [h_eq] at h_step
    exact h_step

end EvalDetBlock

/-! ## Temporary -/

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

theorem EvalCmds_snoc {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (δ : SemanticEval P) (σ σ' σ'' : SemanticStore P)
    (cs : List (Cmd P)) (c : Cmd P) (f₁ f₂ : Bool)
    (h₁ : EvalCmds P (@EvalCmd P _ _ _) δ σ cs σ' f₁)
    (h₂ : @EvalCmd P _ _ _ δ σ' c σ'' f₂) :
    EvalCmds P (@EvalCmd P _ _ _) δ σ (cs ++ [c]) σ'' (f₁ || f₂) := by
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

theorem EvalCmds_inv {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (δ : SemanticEval P) (σ σ' : SemanticStore P) (f : Bool)
    (h : EvalCmds P (@EvalCmd P _ _ _) δ σ [] σ' f) :
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

/-- Unfolding lemmas for Cmd.getVars on each constructor.  Used because
the underlying `Cmd.getVars` is not exposed. -/
private theorem Cmd.getVars_init {P : PureExpr} [HasVarsPure P P.Expr]
    (x : P.Ident) (ty : P.Ty) (e : P.Expr) (md : MetaData P) :
    (HasVarsPure.getVars (Cmd.init x ty (ExprOrNondet.det e) md) : List P.Ident)
      = (HasVarsPure.getVars e : List P.Ident) := by
  with_unfolding_all rfl

private theorem Cmd.getVars_init_nondet {P : PureExpr} [HasVarsPure P P.Expr]
    (x : P.Ident) (ty : P.Ty) (md : MetaData P) :
    (HasVarsPure.getVars (Cmd.init x ty ExprOrNondet.nondet md) : List P.Ident)
      = ([] : List P.Ident) := by
  with_unfolding_all rfl

private theorem Cmd.getVars_set {P : PureExpr} [HasVarsPure P P.Expr]
    (x : P.Ident) (e : P.Expr) (md : MetaData P) :
    (HasVarsPure.getVars (Cmd.set x (ExprOrNondet.det e) md) : List P.Ident)
      = (HasVarsPure.getVars e : List P.Ident) := by
  with_unfolding_all rfl

private theorem Cmd.getVars_assert {P : PureExpr} [HasVarsPure P P.Expr]
    (l : String) (e : P.Expr) (md : MetaData P) :
    (HasVarsPure.getVars (Cmd.assert l e md) : List P.Ident)
      = (HasVarsPure.getVars e : List P.Ident) := by
  with_unfolding_all rfl

private theorem Cmd.getVars_assume {P : PureExpr} [HasVarsPure P P.Expr]
    (l : String) (e : P.Expr) (md : MetaData P) :
    (HasVarsPure.getVars (Cmd.assume l e md) : List P.Ident)
      = (HasVarsPure.getVars e : List P.Ident) := by
  with_unfolding_all rfl

private theorem Cmd.getVars_cover {P : PureExpr} [HasVarsPure P P.Expr]
    (l : String) (e : P.Expr) (md : MetaData P) :
    (HasVarsPure.getVars (Cmd.cover l e md) : List P.Ident)
      = (HasVarsPure.getVars e : List P.Ident) := by
  with_unfolding_all rfl

private theorem Cmds.getVars_cons {P : PureExpr} [HasVarsPure P P.Expr]
    (c : Cmd P) (cs : List (Cmd P)) :
    (HasVarsPure.getVars (c :: cs) : List P.Ident)
      = (HasVarsPure.getVars c : List P.Ident) ++
        (HasVarsPure.getVars cs : List P.Ident) := by
  show Cmds.getVars (c :: cs) = _
  unfold Cmds.getVars
  rfl

private theorem Cmds.definedVars_cons
    {P : PureExpr} (c : Cmd P) (cs : List (Cmd P)) :
    Cmds.definedVars (c :: cs) = Cmd.definedVars c ++ Cmds.definedVars cs := by
  rw [Cmds.definedVars.eq_def]

/-- Single-command agreement-preservation. -/
private theorem EvalCmd_under_agreement {P : PureExpr}
    [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    (δ : SemanticEval P) (σ_struct₀ σ_cfg₀ : SemanticStore P)
    (c : Cmd P) (σ_struct₁ : SemanticStore P) (failed : Bool)
    (h_agree : StoreAgreement σ_struct₀ σ_cfg₀)
    (h_eval : @EvalCmd P _ _ _ δ σ_struct₀ c σ_struct₁ failed)
    (h_wf_def : WellFormedSemanticEvalDef δ)
    (h_congr : WellFormedSemanticEvalExprCongr δ)
    (h_fresh : ∀ x ∈ Cmd.definedVars c, σ_cfg₀ x = none) :
    ∃ σ_cfg₁, @EvalCmd P _ _ _ δ σ_cfg₀ c σ_cfg₁ failed
            ∧ StoreAgreement σ_struct₁ σ_cfg₁ := by
  cases h_eval with
  | eval_init heval hinit hwfvar =>
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
    refine ⟨σ_cfg₁, EvalCmd.eval_init h_eval_cfg h_init_cfg hwfvar, ?_⟩
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
          rw [h_struct_y] at h_y_def_in_σ'
          exact h_y_def_in_σ'
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
          rw [h_struct_y] at h_y_def_in_σ'
          exact h_y_def_in_σ'
        exact h_agree y h_def_y'
  | eval_set heval hupdate hwfvar =>
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
      refine ⟨σ_cfg₁, EvalCmd.eval_set h_eval_cfg h_upd hwfvar, ?_⟩
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
          rw [h_struct_y] at h_y_def_in_σ'
          exact h_y_def_in_σ'
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
          rw [h_struct_y] at h_y_def_in_σ'
          exact h_y_def_in_σ'
        exact h_agree y h_def_y'
  | eval_assert_pass hcond hwfb =>
    rename_i l md e
    have h_def_e : isDefined σ_struct₀ (HasVarsPure.getVars e) :=
      h_wf_def e HasBool.tt σ_struct₀ hcond
    have h_pointwise :
        ∀ y ∈ HasVarsPure.getVars e, σ_struct₀ y = σ_cfg₀ y :=
      store_agreement_pointwise_on_expr_vars σ_struct₀ σ_cfg₀ e h_agree h_def_e
    have h_eval_cfg : δ σ_cfg₀ e = .some HasBool.tt := by
      rw [← hcond]; exact (h_congr e σ_struct₀ σ_cfg₀ h_pointwise).symm
    exact ⟨σ_cfg₀, EvalCmd.eval_assert_pass h_eval_cfg hwfb, h_agree⟩
  | eval_assert_fail hcond hwfb =>
    rename_i l md e
    have h_def_e : isDefined σ_struct₀ (HasVarsPure.getVars e) :=
      h_wf_def e HasBool.ff σ_struct₀ hcond
    have h_pointwise :
        ∀ y ∈ HasVarsPure.getVars e, σ_struct₀ y = σ_cfg₀ y :=
      store_agreement_pointwise_on_expr_vars σ_struct₀ σ_cfg₀ e h_agree h_def_e
    have h_eval_cfg : δ σ_cfg₀ e = .some HasBool.ff := by
      rw [← hcond]; exact (h_congr e σ_struct₀ σ_cfg₀ h_pointwise).symm
    exact ⟨σ_cfg₀, EvalCmd.eval_assert_fail h_eval_cfg hwfb, h_agree⟩
  | eval_assume hcond hwfb =>
    rename_i l md e
    have h_def_e : isDefined σ_struct₀ (HasVarsPure.getVars e) :=
      h_wf_def e HasBool.tt σ_struct₀ hcond
    have h_pointwise :
        ∀ y ∈ HasVarsPure.getVars e, σ_struct₀ y = σ_cfg₀ y :=
      store_agreement_pointwise_on_expr_vars σ_struct₀ σ_cfg₀ e h_agree h_def_e
    have h_eval_cfg : δ σ_cfg₀ e = .some HasBool.tt := by
      rw [← hcond]; exact (h_congr e σ_struct₀ σ_cfg₀ h_pointwise).symm
    exact ⟨σ_cfg₀, EvalCmd.eval_assume h_eval_cfg hwfb, h_agree⟩
  | eval_cover hwfb =>
    exact ⟨σ_cfg₀, EvalCmd.eval_cover hwfb, h_agree⟩

/-- A single `EvalCmd` step preserves the `isDefined` predicate over an
arbitrary list of variables: commands only ever introduce or modify variables. -/
private theorem isDefined_of_EvalCmd {P : PureExpr}
    [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
    {δ : SemanticEval P} {σ σ' : SemanticStore P} {c : Cmd P} {failed : Bool}
    {vs : List P.Ident}
    (h_eval : @EvalCmd P _ _ _ δ σ c σ' failed)
    (h_def : isDefined σ vs) :
    isDefined σ' vs := by
  intro x hx
  have h_def_x : (σ x).isSome = true := h_def x hx
  cases h_eval with
  | eval_init heval hinit hwfvar =>
    rename_i ty md x_init v e
    cases hinit with
    | init h_xn h_xv h_other =>
      by_cases hxx' : x = x_init
      · subst hxx'; rw [h_xv]; rfl
      · have h_eq : σ' x = σ x := h_other x (fun h => hxx' h.symm)
        rw [h_eq]; exact h_def_x
  | eval_init_unconstrained hinit hwfvar =>
    rename_i ty md x_init v
    cases hinit with
    | init h_xn h_xv h_other =>
      by_cases hxx' : x = x_init
      · subst hxx'; rw [h_xv]; rfl
      · have h_eq : σ' x = σ x := h_other x (fun h => hxx' h.symm)
        rw [h_eq]; exact h_def_x
  | eval_set heval hupdate hwfvar =>
    rename_i md x_set v e
    cases hupdate with
    | update h_xv' h_xv h_other =>
      by_cases hxx' : x = x_set
      · subst hxx'; rw [h_xv]; rfl
      · have h_eq : σ' x = σ x := h_other x (fun h => hxx' h.symm)
        rw [h_eq]; exact h_def_x
  | eval_set_nondet hupdate hwfvar =>
    rename_i md x_set v
    cases hupdate with
    | update h_xv' h_xv h_other =>
      by_cases hxx' : x = x_set
      · subst hxx'; rw [h_xv]; rfl
      · have h_eq : σ' x = σ x := h_other x (fun h => hxx' h.symm)
        rw [h_eq]; exact h_def_x
  | eval_assert_pass _ _ => exact h_def_x
  | eval_assert_fail _ _ => exact h_def_x
  | eval_assume _ _ => exact h_def_x
  | eval_cover _ => exact h_def_x

/-- A helper: if `EvalCmd c σ σ' f` succeeds and `x` is not in `c`'s definedVars
(so `c` does not init x), and `σ x = none`, then `σ' x = none`.  This holds because
`c` either doesn't touch x, or modifies x via `set` (which requires `σ x = some _`,
contradicting `σ x = none`). -/
private theorem agreement_helper_unchanged_at_x {P : PureExpr}
    [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
    {δ : SemanticEval P} {σ σ' : SemanticStore P} {c : Cmd P} {failed : Bool}
    {x : P.Ident}
    (h_eval : @EvalCmd P _ _ _ δ σ c σ' failed)
    (h_x_not_def : x ∉ Cmd.definedVars c)
    (h_σ_x : σ x = none) :
    σ' x = none := by
  cases h_eval with
  | eval_init heval hinit hwfvar =>
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
  | eval_set heval hupdate hwfvar =>
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
  | eval_assert_pass _ _ => exact h_σ_x
  | eval_assert_fail _ _ => exact h_σ_x
  | eval_assume _ _ => exact h_σ_x
  | eval_cover _ => exact h_σ_x

/-- Multi-command extension of `agreement_helper_unchanged_at_x`: if `EvalCmds`
takes σ to σ' over a list `cmds`, and `x` is not in `cmds.definedVars`, and
`σ x = none`, then `σ' x = none`. By induction on `EvalCmds`. -/
private theorem agreement_helper_unchanged_at_x_multi {P : PureExpr}
    [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
    {δ : SemanticEval P} {σ σ' : SemanticStore P} {cmds : List (Cmd P)} {failed : Bool}
    {x : P.Ident}
    (h_eval : EvalCmds P (@EvalCmd P _ _ _) δ σ cmds σ' failed)
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
      EvalCmds P (@EvalCmd P _ _ _) δ σ_struct₀ cs σ_struct₁ failed →
      (∀ x ∈ Cmds.definedVars cs, σ_cfg₀ x = none) →
      (Cmds.definedVars cs).Nodup →
      ∃ σ_cfg₁, EvalCmds P (@EvalCmd P _ _ _) δ σ_cfg₀ cs σ_cfg₁ failed
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

theorem single_cmd_eval {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (extendEval : ExtendEval P)
    (c : Cmd P) (ρ₀ ρ₁ : Env P)
    (h : StepStmtStar P (@EvalCmd P _ _ _) extendEval
      (.stmts [.cmd c] ρ₀) (.terminal ρ₁)) :
    ∃ σ' failed, @EvalCmd P _ _ _ ρ₀.eval ρ₀.store c σ' failed ∧
      ρ₁.store = σ' ∧ ρ₁.eval = ρ₀.eval ∧
      ρ₁.hasFailure = (ρ₀.hasFailure || failed) := by
  cases h with
  | step _ _ _ hstep1 hrest1 =>
    cases hstep1 with
    | step_stmts_cons =>
      have ⟨ρ_mid, h_inner, h_tail⟩ := seq_reaches_terminal P (@EvalCmd P _ _ _) extendEval hrest1
      have h_eq := stmts_nil_terminal (@EvalCmd P _ _ _) extendEval _ _ h_tail
      subst h_eq
      cases h_inner with
      | step _ _ _ hstep2 hrest2 =>
        cases hstep2 with
        | step_cmd heval =>
          cases hrest2 with
          | refl => exact ⟨_, _, heval, rfl, rfl, rfl⟩
          | step _ _ _ hstep3 _ => exact absurd hstep3 (by intro h; cases h)

/-! ## Helper: flushCmds simulation

If we have accumulated commands `accum` (stored in reverse) that form the
content of a single block, executing that block via `EvalCmds` produces
the same store transitions as executing each command sequentially in the
structured semantics. -/

private theorem evalCmds_of_stmtStar_cmds_gen {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (extendEval : ExtendEval P)
    (cmds : List (Cmd P)) (δ : SemanticEval P) (σ σ' : SemanticStore P)
    (failed : Bool) (hf : Bool)
    (h : EvalCmds P (@EvalCmd P _ _ _) δ σ cmds σ' failed) :
    StepStmtStar P (@EvalCmd P _ _ _) extendEval
      (.stmts (cmds.map Stmt.cmd) ⟨σ, δ, hf⟩)
      (.terminal ⟨σ', δ, hf || failed⟩) := by
  induction h generalizing hf with
  | eval_cmds_none =>
    simp [List.map, Bool.or_false]
    exact ReflTrans.step _ _ _ StepStmt.step_stmts_nil (ReflTrans.refl _)
  | eval_cmds_some hcmd hcmds ih =>
    simp only [List.map]
    -- Three steps: stmts_cons, seq_inner (step_cmd), seq_done, then IH
    apply ReflTrans.step _ _ _ StepStmt.step_stmts_cons
    apply ReflTrans.step _ _ _ (StepStmt.step_seq_inner (StepStmt.step_cmd hcmd))
    apply ReflTrans.step _ _ _ StepStmt.step_seq_done
    rw [← Bool.or_assoc]
    exact ih (hf || _)

private theorem evalCmds_of_stmtStar_cmds {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (extendEval : ExtendEval P)
    (cmds : List (Cmd P)) (δ : SemanticEval P) (σ σ' : SemanticStore P)
    (failed : Bool)
    (h : EvalCmds P (@EvalCmd P _ _ _) δ σ cmds σ' failed) :
    StepStmtStar P (@EvalCmd P _ _ _) extendEval
      (.stmts (cmds.map Stmt.cmd) ⟨σ, δ, false⟩)
      (.terminal ⟨σ', δ, failed⟩) := by
  have := evalCmds_of_stmtStar_cmds_gen extendEval cmds δ σ σ' failed false h
  simp [Bool.false_or] at this
  exact this

/-- Generalized version of `stmtStar_cmds_to_evalCmds` that separates the
env's `hasFailure` from the `EvalCmds` failure accumulation. -/
private theorem stmtStar_cmds_to_evalCmds {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (extendEval : ExtendEval P)
    (cmds : List (Cmd P)) (ρ₀ ρ' : Env P)
    (h : StepStmtStar P (@EvalCmd P _ _ _) extendEval
      (.stmts (cmds.map Stmt.cmd) ρ₀) (.terminal ρ')) :
    ∃ failed, EvalCmds P (@EvalCmd P _ _ _) ρ₀.eval ρ₀.store cmds ρ'.store failed ∧
      ρ'.hasFailure = (ρ₀.hasFailure || failed) := by
  induction cmds generalizing ρ₀ with
  | nil =>
    simp [List.map] at h
    have hnil : ρ' = ρ₀ := by
      cases h with
      | step _ _ _ hstep hrest => cases hstep with
        | step_stmts_nil => cases hrest with
          | refl => rfl
          | step _ _ _ h _ => exact absurd h (by intro h; cases h)
    subst hnil
    exact ⟨false, EvalCmds.eval_cmds_none, by simp⟩
  | cons c cs ih =>
    simp [List.map] at h
    have ⟨ρ₁, hcmd_star, hrest⟩ := stmts_append_terminates P (@EvalCmd P _ _ _) extendEval
      [.cmd c] (List.map Stmt.cmd cs) ρ₀ ρ' h
    cases hcmd_star with
    | step _ _ _ hstep1 hrest1 => cases hstep1 with
      | step_stmts_cons =>
        have ⟨ρ_s, h_s_term, h_nil⟩ := seq_reaches_terminal P (@EvalCmd P _ _ _) extendEval hrest1
        have hrest' : StepStmtStar P (@EvalCmd P _ _ _) extendEval
            (.stmts (List.map Stmt.cmd cs) ρ_s) (.terminal ρ') := by
          cases h_nil with
          | step _ _ _ hstep3 hrest3 => cases hstep3 with
            | step_stmts_nil => cases hrest3 with
              | refl => exact hrest
              | step _ _ _ h _ => exact absurd h (by intro h; cases h)
        cases h_s_term with
        | step _ _ _ hstep2 hrest2 => cases hstep2 with
          | step_cmd heval =>
            cases hrest2 with
            | refl =>
              have ⟨failed', heval_rest, hfail'⟩ := ih _ hrest'
              refine ⟨_ || failed', EvalCmds.eval_cmds_some heval heval_rest, ?_⟩
              rw [hfail', Bool.or_assoc]
            | step _ _ _ h _ => exact absurd h (by intro h; cases h)

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
    cases hl with
    | inl h => exact h₁.user_shape l h
    | inr h => exact h₂.user_shape l h
  · -- user_disj: user labels are absent from stringGens gen'.
    -- Shape-free + WF gen' ⇒ not in stringGens gen'.
    intro l hl
    rw [List.mem_append] at hl
    have h_shape : ¬ String.HasUnderscoreDigitSuffix l := by
      cases hl with
      | inl h => exact h₁.user_shape l h
      | inr h => exact h₂.user_shape l h
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
    cases hl with
    | inl h =>
      cases h₁.fresh l h with
      | inl h_gen =>
        left
        exact ⟨h₂.subset h_gen.1, h_gen.2⟩
      | inr h_user =>
        right
        exact List.mem_append.mpr (Or.inl h_user)
    | inr h =>
      cases h₂.fresh l h with
      | inl h_gen =>
        left
        refine ⟨h_gen.1, ?_⟩
        intro h_in_gen
        exact h_gen.2 (h₁.subset h_in_gen)
      | inr h_user =>
        right
        exact List.mem_append.mpr (Or.inr h_user)
  · -- nodup
    rw [List.map_append, List.nodup_append]
    refine ⟨h₁.nodup, h₂.nodup, ?_⟩
    intro x hx y hy h_eq
    subst h_eq
    cases h₁.fresh x hx with
    | inl h_x_gen₁ =>
      cases h₂.fresh x hy with
      | inl h_x_gen₂ =>
        exact h_x_gen₂.2 h_x_gen₁.1
      | inr h_x_user₂ =>
        -- x ∈ stringGens gen_mid (from h_x_gen₁.1) but x ∈ userLabels₂ (shape-free).
        -- WF gen_mid + shape-free ⇒ x ∉ stringGens gen_mid. Contradiction.
        exact (userLabel_not_in_stringGens_of_shape_free hwf_mid
                (h₂.user_shape x h_x_user₂)) h_x_gen₁.1 |>.elim
    | inr h_x_user₁ =>
      cases h₂.fresh x hy with
      | inl h_x_gen₂ =>
        -- x ∈ userLabels₁ (shape-free), but x ∈ stringGens gen'.
        -- WF gen' + shape-free ⇒ x ∉ stringGens gen'. Contradiction.
        exact (userLabel_not_in_stringGens_of_shape_free hwf_out
                (h₁.user_shape x h_x_user₁)) h_x_gen₂.1 |>.elim
      | inr h_x_user₂ =>
        exact h_user_disj x h_x_user₁ h_x_user₂

/-- Trivial GenInv: same state, no blocks, no user labels. -/
private theorem GenInv.refl {P : PureExpr}
    (gen : StringGenState) (hwf : StringGenState.WF gen) :
    @GenInv P gen gen [] [] := by
  refine ⟨StringGenState.GenStep.refl _, hwf, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl; simp at hl
  · intro l hl; simp at hl
  · simp
  · intro l hl; simp at hl
  · simp

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
    cases hx with
    | inl h_eq =>
      subst h_eq
      exact .inl ⟨h_l_in, h_l_notin_gen⟩
    | inr h_in =>
      cases h_blocks.fresh _ h_in with
      | inl h_gen =>
        refine .inl ⟨h_gen.1, ?_⟩
        intro hgen
        exact h_gen.2 (h_step.subset hgen)
      | inr h_user =>
        exact .inr h_user
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
    rw [← h_gen']
    exact StringGenState.GenStep.refl gen
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
    rw [← h_gen']
    exact h1.trans h2

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
    cases hx with
    | inl h_eq =>
      subst h_eq
      exact userLabel_not_in_stringGens_of_shape_free hwf_out h_l_shape
    | inr h_in => exact h_blocks.user_disj x h_in
  · rw [List.nodup_cons]
    exact ⟨h_l_notin_user, h_blocks.user_nodup⟩
  · intro x hx
    rw [List.map_cons, List.mem_cons] at hx
    cases hx with
    | inl h_eq =>
      subst h_eq
      exact .inr (List.mem_cons.mpr (Or.inl rfl))
    | inr h_in =>
      cases h_blocks.fresh _ h_in with
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

/-! ### User init-variables (specialized to `Core.Expression`)

NOTE on specialization: the helper below (and the simulation lemmas it
supports) is specialized to `Core.Expression` because we use that
instantiation's `Identifier Unit` constructor `⟨s, ()⟩`'s definitional
injectivity to bridge between `String`-valued gen state and
`P.Ident`-valued defined-vars lists.

To generalize over `P : PureExpr`, would need a typeclass:
```
class HasIdentInj (P : PureExpr) extends HasIdent P where
  ident_injective : Function.Injective (HasIdent.ident (P := P))
```
plus instances for each concrete `P` (Core.Expression, etc.), and threading
`[HasIdentInj P]` through all simulation-lemma signatures and recursive
calls. The cost is ~30 sites × typeclass-propagation lines. Specialization
is preferred while no external consumer needs the generic form. -/

/-- Per-stmt user init-variable names, recursing into block/ite/loop children.

Specialized to `Core.Expression` so that `.cmd (.init x ty e md)`'s `x`
field has type `Identifier Unit`, from which we can extract the underlying
`String` via `.name`. -/
@[expose] def Block.userInitVars :
    List (Stmt Core.Expression (Cmd Core.Expression)) → List String
  | [] => []
  | s :: rest => stmtUserInitVars s ++ Block.userInitVars rest
where
  stmtUserInitVars : Stmt Core.Expression (Cmd Core.Expression) → List String
    | .cmd (.init x _ _ _) => [x.name]
    | .block _ ss _ => Block.userInitVars ss
    | .ite _ tss ess _ => Block.userInitVars tss ++ Block.userInitVars ess
    | .loop _ _ _ ss _ => Block.userInitVars ss
    | _ => []

/-! Equational lemmas for `userInitVars` (proved via `unfold`). -/

theorem Block.userInitVars_block_cons
    (l : String) (bss : List (Stmt Core.Expression (Cmd Core.Expression)))
    (md : MetaData Core.Expression)
    (rest : List (Stmt Core.Expression (Cmd Core.Expression))) :
    Block.userInitVars (.block l bss md :: rest) =
      Block.userInitVars bss ++ Block.userInitVars rest := by
  show Block.userInitVars.stmtUserInitVars _ ++ _ = _
  rfl

theorem Block.userInitVars_ite_cons
    (c : Imperative.ExprOrNondet Core.Expression)
    (tss ess : List (Stmt Core.Expression (Cmd Core.Expression)))
    (md : MetaData Core.Expression)
    (rest : List (Stmt Core.Expression (Cmd Core.Expression))) :
    Block.userInitVars (.ite c tss ess md :: rest) =
      (Block.userInitVars tss ++ Block.userInitVars ess)
        ++ Block.userInitVars rest := by
  show Block.userInitVars.stmtUserInitVars _ ++ _ = _
  rfl

theorem Block.userInitVars_loop_cons
    (c : Imperative.ExprOrNondet Core.Expression)
    (m : Option Core.Expression.Expr)
    (is : List (String × Core.Expression.Expr))
    (bss : List (Stmt Core.Expression (Cmd Core.Expression)))
    (md : MetaData Core.Expression)
    (rest : List (Stmt Core.Expression (Cmd Core.Expression))) :
    Block.userInitVars (.loop c m is bss md :: rest) =
      Block.userInitVars bss ++ Block.userInitVars rest := by
  show Block.userInitVars.stmtUserInitVars _ ++ _ = _
  rfl

theorem Block.userInitVars_init_cmd_cons
    (x : Core.Expression.Ident) (ty : Core.Expression.Ty)
    (e : Imperative.ExprOrNondet Core.Expression)
    (md : MetaData Core.Expression)
    (rest : List (Stmt Core.Expression (Cmd Core.Expression))) :
    Block.userInitVars (.cmd (.init x ty e md) :: rest) =
      x.name :: Block.userInitVars rest := by
  show Block.userInitVars.stmtUserInitVars _ ++ _ = _
  rfl

theorem Block.userInitVars_funcDecl_cons
    (decl : Imperative.PureFunc Core.Expression)
    (md : MetaData Core.Expression)
    (rest : List (Stmt Core.Expression (Cmd Core.Expression))) :
    Block.userInitVars (.funcDecl decl md :: rest) =
      Block.userInitVars rest := by
  show Block.userInitVars.stmtUserInitVars _ ++ _ = _
  rfl

theorem Block.userInitVars_typeDecl_cons
    (tc : TypeConstructor) (md : MetaData Core.Expression)
    (rest : List (Stmt Core.Expression (Cmd Core.Expression))) :
    Block.userInitVars (.typeDecl tc md :: rest) =
      Block.userInitVars rest := by
  show Block.userInitVars.stmtUserInitVars _ ++ _ = _
  rfl

theorem Block.userInitVars_exit_cons
    (l : String) (md : MetaData Core.Expression)
    (rest : List (Stmt Core.Expression (Cmd Core.Expression))) :
    Block.userInitVars (.exit l md :: rest) =
      Block.userInitVars rest := by
  show Block.userInitVars.stmtUserInitVars _ ++ _ = _
  rfl

/-- A predicate stating that user-provided init-variable names are shape-free
(do not have the `_<digits>` generator suffix), so they cannot collide with
fresh identifiers produced by the translator's `StringGenState.gen`. This is
the variable-side analog of `userLabelsDisjoint`'s shape-free clause; see
that definition for the labels analog. -/
@[expose] def Block.userVarsDisjoint
    (ss : List (Stmt Core.Expression (Cmd Core.Expression))) : Prop :=
  ∀ v ∈ Block.userInitVars ss, ¬ String.HasUnderscoreDigitSuffix v

/-- `userVarsDisjoint` distributes over `cons`: if a longer list is disjoint,
so is the tail. -/
private theorem Block.userVarsDisjoint_tail
    (s : Stmt Core.Expression (Cmd Core.Expression))
    (rest : List (Stmt Core.Expression (Cmd Core.Expression)))
    (h : Block.userVarsDisjoint (s :: rest)) :
    Block.userVarsDisjoint rest := by
  intro v hv
  apply h
  unfold Block.userInitVars
  exact List.mem_append.mpr (Or.inr hv)

/-- `userVarsDisjoint` for the body of a `Stmt.block`: if the outer
`Stmt.block l bss md :: rest` is disjoint, so are `bss`'s user init vars. -/
private theorem Block.userVarsDisjoint_block_body
    (l : String) (bss : List (Stmt Core.Expression (Cmd Core.Expression)))
    (md : MetaData Core.Expression)
    (rest : List (Stmt Core.Expression (Cmd Core.Expression)))
    (h : Block.userVarsDisjoint (Stmt.block l bss md :: rest)) :
    Block.userVarsDisjoint bss := by
  intro v hv
  apply h
  rw [Block.userInitVars_block_cons]
  exact List.mem_append.mpr (Or.inl hv)

/-- `userVarsDisjoint` for the then-branch of a `Stmt.ite`. -/
private theorem Block.userVarsDisjoint_ite_then
    (c : Imperative.ExprOrNondet Core.Expression)
    (tss ess : List (Stmt Core.Expression (Cmd Core.Expression)))
    (md : MetaData Core.Expression)
    (rest : List (Stmt Core.Expression (Cmd Core.Expression)))
    (h : Block.userVarsDisjoint (Stmt.ite c tss ess md :: rest)) :
    Block.userVarsDisjoint tss := by
  intro v hv
  apply h
  rw [Block.userInitVars_ite_cons]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hv)))

/-- `userVarsDisjoint` for the else-branch of a `Stmt.ite`. -/
private theorem Block.userVarsDisjoint_ite_else
    (c : Imperative.ExprOrNondet Core.Expression)
    (tss ess : List (Stmt Core.Expression (Cmd Core.Expression)))
    (md : MetaData Core.Expression)
    (rest : List (Stmt Core.Expression (Cmd Core.Expression)))
    (h : Block.userVarsDisjoint (Stmt.ite c tss ess md :: rest)) :
    Block.userVarsDisjoint ess := by
  intro v hv
  apply h
  rw [Block.userInitVars_ite_cons]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hv)))

/-- `userVarsDisjoint` for the body of a `Stmt.loop`. -/
private theorem Block.userVarsDisjoint_loop_body
    (c : Imperative.ExprOrNondet Core.Expression)
    (m : Option Core.Expression.Expr)
    (is : List (String × Core.Expression.Expr))
    (bss : List (Stmt Core.Expression (Cmd Core.Expression)))
    (md : MetaData Core.Expression)
    (rest : List (Stmt Core.Expression (Cmd Core.Expression)))
    (h : Block.userVarsDisjoint (Stmt.loop c m is bss md :: rest)) :
    Block.userVarsDisjoint bss := by
  intro v hv
  apply h
  rw [Block.userInitVars_loop_cons]
  exact List.mem_append.mpr (Or.inl hv)


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

/-- `userLabelsDisjoint` for the head statement: if `s :: rest` is disjoint,
so are the user labels in `s` itself. -/
private theorem Block.userLabelsDisjoint_head {P : PureExpr}
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (s :: rest) gen') :
    ∀ l ∈ Block.userBlockLabels.stmtUserBlockLabels s,
      l ∉ StringGenState.stringGens gen' := by
  intro l hl
  apply h.2.2
  unfold Block.userBlockLabels
  exact List.mem_append.mpr (Or.inl hl)

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

/-! ### User labels vs generated labels

A label produced by `StringGenState.gen pf σ` is always `pf ++ "_" ++ toString n`.
User-provided block labels carry no such guarantee.  We expose the shape lemmas
from `StringGen.lean` here in the form most directly useful for the
`stmtsToBlocks_invariant` proof: a user label that does not have the
`_<digits>` suffix is automatically disjoint from any future `gen` output. -/

/-- A user label that lacks the `_<digits>` suffix shape is never produced by
`gen`. This is the structural guarantee the user supplies for free by choosing
labels that are "human-readable" rather than counter-shaped. -/
theorem userLabel_ne_gen
    (pf : String) (σ : StringGenState) (s : String)
    (h : ¬ String.HasUnderscoreDigitSuffix s) :
    s ≠ (StringGenState.gen pf σ).1 :=
  StringGenState.gen_ne_of_not_hasUnderscoreDigitSuffix pf σ s h

/-- A label inside a WF generator state has the generator suffix shape. So a
shape-free user label is automatically not in `stringGens`. -/
theorem userLabel_not_in_stringGens
    {σ : StringGenState} (hwf : StringGenState.WF σ)
    {s : String} (h : ¬ String.HasUnderscoreDigitSuffix s) :
    s ∉ σ.stringGens :=
  StringGenState.not_mem_stringGens_of_not_hasUnderscoreDigitSuffix hwf h

/-- Generated labels from inside a WF state always have the suffix shape, so a
shape-free string is disjoint from the generated set even when reasoning
positionally. -/
theorem hasUnderscoreDigitSuffix_of_mem
    {σ : StringGenState} (hwf : StringGenState.WF σ)
    {s : String} (h : s ∈ σ.stringGens) :
    String.HasUnderscoreDigitSuffix s :=
  StringGenState.hasUnderscoreDigitSuffix_of_mem_generated hwf h

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
    unfold stmtsToBlocks at h_gen
    simp only [bind, StateT.bind, pure] at h_gen
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
    rw [← h_gen_eq]
    exact (h_step_rest.trans h_step_body).trans h_step_flush
  | .ite c tss fss md :: rest =>
    unfold stmtsToBlocks at h_gen
    simp only [bind, StateT.bind, pure] at h_gen
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
      rw [← h_gen_eq]
      exact (((h_step_rest.trans h_step_ite).trans h_step_then).trans h_step_else).trans
              h_step_flush
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
      rw [← h_gen_eq]
      exact ((((h_step_rest.trans h_step_ite).trans h_step_then).trans h_step_else).trans
              h_step_nondet).trans h_step_flush
  | .loop c m is bss md :: rest =>
    unfold stmtsToBlocks at h_gen
    simp only [bind, StateT.bind] at h_gen
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
      have h_step_inv : StringGenState.GenStep gen_b gen_i := by
        apply mapM_genStep _ _ is gen_b gen_i invCmds h_inv_def
        intro a g g' b h_step
        obtain ⟨srcLabel, i⟩ := a
        by_cases h_empty : srcLabel.isEmpty
        · simp only [h_empty, if_true, bind, StateT.bind, pure, StateT.pure] at h_step
          have h_g_eq : g' = (StringGenState.gen "inv$" g).2 := (Prod.mk.inj h_step).2.symm
          rw [h_g_eq]
          exact StringGenState.GenStep.of_gen "inv$" g
        · simp only [h_empty, bind, pure] at h_step
          have h_g_eq : g' = g := (Prod.mk.inj h_step).2.symm
          rw [h_g_eq]
          exact StringGenState.GenStep.refl g
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
        rw [← h_gen_eq]
        exact h_step_prefix.trans h_step_flush
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
        rw [← h_gen_eq]
        exact (h_step_prefix.trans h_step_nondet).trans h_step_flush
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
      have h_step_inv : StringGenState.GenStep gen_b gen_i := by
        apply mapM_genStep _ _ is gen_b gen_i invCmds h_inv_def
        intro a g g' b h_step
        obtain ⟨srcLabel, i⟩ := a
        by_cases h_empty : srcLabel.isEmpty
        · simp only [h_empty, if_true, bind, StateT.bind, pure, StateT.pure] at h_step
          have h_g_eq : g' = (StringGenState.gen "inv$" g).2 := (Prod.mk.inj h_step).2.symm
          rw [h_g_eq]
          exact StringGenState.GenStep.of_gen "inv$" g
        · simp only [h_empty, bind, pure] at h_step
          have h_g_eq : g' = g := (Prod.mk.inj h_step).2.symm
          rw [h_g_eq]
          exact StringGenState.GenStep.refl g
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
        rw [← h_gen_eq]
        exact h_step_prefix.trans h_step_flush
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
        rw [← h_gen_eq]
        exact (h_step_prefix.trans h_step_nondet).trans h_step_flush
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
    unfold stmtsToBlocks at h_gen
    simp only [bind, StateT.bind, pure] at h_gen
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
      rw [← h_gen_eq]
      exact (h_step_body.trans h_step_flush).subset
    have h_subset_b_gen' : StringGenState.stringGens gen_b ⊆ StringGenState.stringGens gen' := by
      rw [← h_gen_eq]
      exact h_step_flush.subset
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
      cases hx with
      | inl h => exact List.mem_append.mpr (Or.inr h)
      | inr h => exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inr h)))
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
        cases h_in with
        | inl h => exact h_l_props.2.2.2 h
        | inr h => exact h_l_props.2.2.1 h
      -- l ∉ map fst of (accumBlocks ++ bbs ++ bsNext): from h_inv_out.fresh, none of those
      -- labels equal l (l is a user label, and the existing blocks' labels are either
      -- generated or in rest++bss user labels — both disjoint from l).
      have h_l_notin_blks : l ∉ List.map Prod.fst (accumBlocks ++ bbs ++ bsNext) := by
        intro h_in
        cases h_inv_out.fresh l h_in with
        | inl h_gen =>
          -- l shape-free vs l ∈ stringGens gen_f (= gen'): contradiction via shape.
          have hwf_out : StringGenState.WF gen_f := h_inv_out.wf_out
          exact userLabel_not_in_stringGens_of_shape_free hwf_out h_l_props.1 h_gen.1
        | inr h_user => exact h_l_notin_user_combined h_user
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
          cases h with
          | inl h => exact List.mem_append.mpr (Or.inr h)
          | inr h => exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inr h)))
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
    unfold stmtsToBlocks at h_gen
    simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
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
      simp only [pure, StateT.pure] at h_gen
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
        rw [← h_gen_eq]
        exact ((((h_step_ite.trans h_step_then).trans h_step_else)).trans h_step_flush).subset
      have h_subset_ite_gen' : StringGenState.stringGens gen_ite ⊆ StringGenState.stringGens gen' := by
        rw [← h_gen_eq]
        exact (((h_step_then.trans h_step_else)).trans h_step_flush).subset
      have h_subset_t_gen' : StringGenState.stringGens gen_t ⊆ StringGenState.stringGens gen' := by
        rw [← h_gen_eq]
        exact (h_step_else.trans h_step_flush).subset
      have h_subset_e_gen' : StringGenState.stringGens gen_e ⊆ StringGenState.stringGens gen' := by
        rw [← h_gen_eq]
        exact h_step_flush.subset
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
        cases h_x_in with
        | inl h_x_r => exact h_er x h_x_f h_x_r
        | inr h_x_t => exact h_te x h_x_t h_x_f
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
      simp only [pure, StateT.pure] at h_gen
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
        rw [← h_gen_eq]
        exact h_step_r_to_f.subset
      have h_subset_ite_gen' : StringGenState.stringGens gen_ite ⊆ StringGenState.stringGens gen' := by
        rw [← h_gen_eq]
        exact (((h_step_then.trans h_step_else).trans h_step_nondet).trans h_step_flush).subset
      have h_subset_t_gen' : StringGenState.stringGens gen_t ⊆ StringGenState.stringGens gen' := by
        rw [← h_gen_eq]
        exact ((h_step_else.trans h_step_nondet).trans h_step_flush).subset
      have h_subset_e_gen' : StringGenState.stringGens gen_e ⊆ StringGenState.stringGens gen' := by
        rw [← h_gen_eq]
        exact (h_step_nondet.trans h_step_flush).subset
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
        cases h_x_in with
        | inl h_x_r => exact h_er x h_x_f h_x_r
        | inr h_x_t => exact h_te x h_x_t h_x_f
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
    unfold stmtsToBlocks at h_gen
    simp only [bind, StateT.bind] at h_gen
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
      have h_step_inv : StringGenState.GenStep gen_b gen_i := by
        apply mapM_genStep _ _ is gen_b gen_i invCmds h_inv_def
        intro a g g' b' h_step
        obtain ⟨srcLabel, i⟩ := a
        by_cases h_empty : srcLabel.isEmpty
        · simp only [h_empty, if_true, bind, StateT.bind, pure, StateT.pure] at h_step
          have h_g_eq : g' = (StringGenState.gen "inv$" g).2 := (Prod.mk.inj h_step).2.symm
          rw [h_g_eq]; exact StringGenState.GenStep.of_gen "inv$" g
        · simp only [h_empty, bind, pure] at h_step
          have h_g_eq : g' = g := (Prod.mk.inj h_step).2.symm
          rw [h_g_eq]; exact StringGenState.GenStep.refl g
      cases h_c : c with
      | det e =>
        rw [h_c] at h_gen
        simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
        generalize h_flush_eq : @flushCmds P (Cmd P) _ "before_loop$" accum
          Option.none lentry gen_i = r_flush at h_gen
        obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
        simp only [pure, StateT.pure] at h_gen
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
          cases h_inv_chron.fresh lentry h_in with
          | inl h_g =>
            -- lentry ∈ gen_f \ gen — but lentry was generated from gen_r, so
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
              cases h_inv_rest.fresh lentry h_bs with
              | inl h_gr => exact h_lentry_notin_gen_r h_gr.1
              | inr h_user =>
                have h_shape := h_inv_rest.user_shape lentry h_user
                have h_shape_lentry :
                    String.HasUnderscoreDigitSuffix lentry := by
                  have := StringGenState.hasUnderscoreDigitSuffix_of_mem_generated
                            (h_inv_le_step.wf_out) h_lentry_in_gen_le
                  exact this
                exact h_shape h_shape_lentry
            · -- bbs: from h_inv_body.fresh
              cases h_inv_body.fresh lentry h_bb with
              | inl h_gb =>
                -- lentry ∉ stringGens gen_le (= h_gb.2): but h_lentry_in_gen_le says lentry ∈ gen_le.
                exact h_gb.2 h_lentry_in_gen_le
              | inr h_user =>
                -- lentry would be a user label of bss
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
          | inr h_user =>
            -- lentry would be in (rest ++ bss) user labels: shape contradiction.
            have h_shape : ¬ String.HasUnderscoreDigitSuffix lentry := by
              rw [List.mem_append] at h_user
              cases h_user with
              | inl h_r => exact h_inv_rest.user_shape lentry h_r
              | inr h_b => exact h_inv_body.user_shape lentry h_b
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
            simp [List.append_assoc, List.singleton_append]
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
          cases hx with
          | inl h_r => exact Or.inr h_r
          | inr h_b => exact Or.inl h_b
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
        simp only [pure, StateT.pure] at h_gen
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
          rw [← h_gen_eq]
          exact ((h_step_inv.trans h_step_nondet).trans h_step_flush).subset
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
          · cases h_inv_rest.fresh lentry h_bs with
            | inl h_gr => exact h_lentry_notin_gen_r h_gr.1
            | inr h_user =>
              have h_shape := h_inv_rest.user_shape lentry h_user
              exact h_shape (StringGenState.hasUnderscoreDigitSuffix_of_mem_generated
                                (h_inv_le_step.wf_out) h_lentry_in_gen_le)
          · cases h_inv_body.fresh lentry h_bb with
            | inl h_gb => exact h_gb.2 h_lentry_in_gen_le
            | inr h_user =>
              have h_shape := h_inv_body.user_shape lentry h_user
              exact h_shape (StringGenState.hasUnderscoreDigitSuffix_of_mem_generated
                                (h_inv_le_step.wf_out) h_lentry_in_gen_le)
          · cases h_inv_flush.fresh lentry h_ac with
            | inl h_gf =>
              -- lentry ∈ gen_le ⊆ gen_n: contradicts h_gf.2 (lentry ∉ gen_n).
              exact h_gf.2 (((h_step_body.trans h_step_inv).trans h_step_nondet).subset
                              h_lentry_in_gen_le)
            | inr h_user => simp at h_user
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
            simp [List.append_assoc, List.singleton_append]
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
        rw [Block.userBlockLabels_loop_cons]
        apply GenInv.weaken_userLabels gen gen_f _ _ _ h_inv_perm
        · intro x hx
          rw [List.mem_append] at hx
          rw [List.mem_append]
          cases hx with
          | inl h_r => exact Or.inr h_r
          | inr h_b => exact Or.inl h_b
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
      have h_step_inv : StringGenState.GenStep gen_b gen_i := by
        apply mapM_genStep _ _ is gen_b gen_i invCmds h_inv_def
        intro a g g' b' h_step
        obtain ⟨srcLabel, i⟩ := a
        by_cases h_empty : srcLabel.isEmpty
        · simp only [h_empty, if_true, bind, StateT.bind, pure, StateT.pure] at h_step
          have h_g_eq : g' = (StringGenState.gen "inv$" g).2 := (Prod.mk.inj h_step).2.symm
          rw [h_g_eq]; exact StringGenState.GenStep.of_gen "inv$" g
        · simp only [h_empty, bind, pure] at h_step
          have h_g_eq : g' = g := (Prod.mk.inj h_step).2.symm
          rw [h_g_eq]; exact StringGenState.GenStep.refl g
      cases h_c : c with
      | det e =>
        rw [h_c] at h_gen
        simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
        generalize h_flush_eq : @flushCmds P (Cmd P) _ "before_loop$" accum
          Option.none lentry gen_i = r_flush at h_gen
        obtain ⟨⟨accumEntry, accumBlocks⟩, gen_f⟩ := r_flush
        simp only [pure, StateT.pure] at h_gen
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
          (ldec, { cmds := [decCmd], transfer := DetTransferCmd.goto lentry })
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
          · cases h_inv_rest.fresh lentry h_bs with
            | inl h_gr => exact h_lentry_notin_gen_r h_gr.1
            | inr h_user =>
              have h_shape := h_inv_rest.user_shape lentry h_user
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
          · cases h_inv_body.fresh lentry h_bb with
            | inl h_gb =>
              -- lentry ∈ gen_le ⊆ gen_ldec, but h_gb.2 says lentry ∉ gen_ldec.
              exact h_gb.2 ((h_step_ml.trans h_step_ldec).subset h_lentry_in_gen_le)
            | inr h_user =>
              have h_shape := h_inv_body.user_shape lentry h_user
              exact h_shape (StringGenState.hasUnderscoreDigitSuffix_of_mem_generated
                                (h_inv_le_step.wf_out) h_lentry_in_gen_le)
          · cases h_inv_flush.fresh lentry h_ac with
            | inl h_gf =>
              exact h_gf.2 ((h_step_le_to_b.trans h_step_inv).subset h_lentry_in_gen_le)
            | inr h_user => simp at h_user
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
            simp [List.append_assoc, List.singleton_append]
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
        rw [← h_blocks_eq, ← h_gen_eq]
        rw [Block.userBlockLabels_loop_cons]
        apply GenInv.weaken_userLabels gen gen_f _ _ _ h_inv_perm
        · intro x hx
          rw [List.mem_append] at hx
          rw [List.mem_append]
          cases hx with
          | inl h_r => exact Or.inr h_r
          | inr h_b => exact Or.inl h_b
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
        simp only [pure, StateT.pure] at h_gen
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
          (ldec, { cmds := [decCmd], transfer := DetTransferCmd.goto lentry })
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
          rw [← h_gen_eq]
          exact ((h_step_inv.trans h_step_nondet).trans h_step_flush).subset
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
          · cases h_inv_rest.fresh lentry h_bs with
            | inl h_gr => exact h_lentry_notin_gen_r h_gr.1
            | inr h_user =>
              have h_shape := h_inv_rest.user_shape lentry h_user
              exact h_shape (StringGenState.hasUnderscoreDigitSuffix_of_mem_generated
                                (h_inv_le_step.wf_out) h_lentry_in_gen_le)
          · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h_dec
            rw [h_dec] at h_lentry_in_gen_le
            exact h_ldec_notin_gen_ml (h_step_ml.subset h_lentry_in_gen_le)
          · cases h_inv_body.fresh lentry h_bb with
            | inl h_gb =>
              exact h_gb.2 ((h_step_ml.trans h_step_ldec).subset h_lentry_in_gen_le)
            | inr h_user =>
              have h_shape := h_inv_body.user_shape lentry h_user
              exact h_shape (StringGenState.hasUnderscoreDigitSuffix_of_mem_generated
                                (h_inv_le_step.wf_out) h_lentry_in_gen_le)
          · cases h_inv_flush.fresh lentry h_ac with
            | inl h_gf =>
              exact h_gf.2 (((h_step_le_to_b.trans h_step_inv).trans h_step_nondet).subset
                              h_lentry_in_gen_le)
            | inr h_user => simp at h_user
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
            simp [List.append_assoc, List.singleton_append]
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
        rw [← h_blocks_eq, ← h_gen_eq]
        rw [Block.userBlockLabels_loop_cons]
        apply GenInv.weaken_userLabels gen gen_f _ _ _ h_inv_perm
        · intro x hx
          rw [List.mem_append] at hx
          rw [List.mem_append]
          cases hx with
          | inl h_r => exact Or.inr h_r
          | inr h_b => exact Or.inl h_b
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
    (h_disj : ∀ gen', Block.userLabelsDisjoint ss gen') :
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
  have h_inv : @GenInv P gen0 r.2 (Block.userBlockLabels ss) r.1.2 :=
    stmtsToBlocks_invariant lend ss [] [] gen0 r.2 _ _ h_eq hwf0 (h_disj _)
  -- Build Nodup of r.1.2.map Prod.fst ++ [lend]
  rw [List.nodup_append]
  refine ⟨h_inv.nodup, ?_, ?_⟩
  · simp
  · -- disjointness: lend not in r.1.2.map Prod.fst
    intro x hx y hy h_eq
    rw [List.mem_singleton] at hy
    subst hy
    subst h_eq
    cases h_inv.fresh _ hx with
    | inl h_gen =>
      -- lend ∈ stringGens r.2 \ stringGens gen0; but lend ∈ stringGens gen0. Contradiction.
      exact h_gen.2 h_lend_in_gen0
    | inr h_user =>
      -- lend is a user label of ss; but lend = (gen "end$" emp).1 has shape, so it's not user.
      -- We instead use that user labels are disjoint from stringGens (h_inv.user_disj)
      have h_lend_in_r2 : lend ∈ StringGenState.stringGens r.2 := by
        have h_step := h_inv.toGenStep
        exact h_step.subset h_lend_in_gen0
      exact h_inv.user_disj _ h_user h_lend_in_r2



/-- Evaluator well-formedness (Bool) is preserved by structured execution when
no `funcDecl` statements are executed (i.e., the evaluator doesn't change).
This holds because only `step_funcDecl` modifies `eval`. -/
private theorem StepStmtStar_wfb_preserved {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
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
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
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

/-- When `flushCmds` emits a block with a `condGoto` transfer and the condition
evaluates to true at the post-command store `ρ₀.store`, the CFG steps from the
entry to the true-branch label. -/
private theorem flushCmds_condGoto_true {P : PureExpr} [HasFvar P] [HasNot P]
    (extendEval : ExtendEval P)
    (accum : List (Cmd P))
    (e : P.Expr) (tl fl : String) (md : MetaData P)
    (l_ite : String) (gen_e gen_f : StringGenState)
    (accumEntry : String) (accumBlocks : DetBlocks String (Cmd P) P)
    (h_flush_eq : flushCmds "ite$" accum
      (some (DetTransferCmd.condGoto e tl fl md)) l_ite gen_e = ((accumEntry, accumBlocks), gen_f))
    (σ_base : SemanticStore P) (hf_base hf_accum : Bool)
    (ρ₀ : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (h_accum : EvalCmds P (EvalCmd P) ρ₀.eval σ_base accum.reverse ρ₀.store hf_accum)
    (h_hf : ρ₀.hasFailure = (hf_base || hf_accum))
    (h_cond : ρ₀.eval ρ₀.store e = .some HasBool.tt)
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (h_cfg_accum : ∀ b ∈ accumBlocks, b ∈ cfg.blocks)
    (h_lookup : ∀ lbl blk, (lbl, blk) ∈ cfg.blocks →
      cfg.blocks.lookup lbl = some blk) :
    StepDetCFGStar extendEval cfg
      (.cont accumEntry σ_base hf_base)
      (.cont tl ρ₀.store ρ₀.hasFailure) := by
  -- With the fixed flushCmds, `tr? = some _` always emits a single block
  -- (regardless of whether accum is empty), so there's no isTrue/isFalse split.
  unfold flushCmds at h_flush_eq
  simp only [bind, StateT.bind, pure, StateT.pure, Id] at h_flush_eq
  injection h_flush_eq with h_pair h_gen_eq
  injection h_pair with h_entry_eq h_blks_eq
  subst h_entry_eq; subst h_blks_eq
  have h_mem := h_cfg_accum _ (List.Mem.head _)
  have h_lkp := h_lookup _ _ h_mem
  have h_eval_block : EvalDetBlock P (EvalCmd P) extendEval
      σ_base ⟨accum.reverse, .condGoto e tl fl md⟩
      (.cont tl ρ₀.store hf_accum) :=
    EvalDetBlock.step_goto_true (δ := ρ₀.eval) h_accum h_cond hwfb
  have h_step : @StepCFG _ _ (Cmd P) _ P
      (EvalDetBlock P (EvalCmd P) extendEval) cfg
      (.cont (StringGenState.gen "ite$" gen_e).fst σ_base hf_base)
      (updateFailure (.cont tl ρ₀.store hf_accum) hf_base) :=
    StepCFG.eval_next (failed := hf_base) h_lkp h_eval_block
  have h_uf : @updateFailure String P (.cont tl ρ₀.store hf_accum) hf_base =
      CFGConfig.cont tl ρ₀.store ρ₀.hasFailure := by
    simp [updateFailure, h_hf, Bool.or_comm]
  rw [h_uf] at h_step
  exact ReflTrans.step _ _ _ h_step (ReflTrans.refl _)

/-- When `flushCmds` emits a block with a `condGoto` transfer and the condition
evaluates to false at the post-command store `ρ₀.store`, the CFG steps from the
entry to the false-branch label. -/
private theorem flushCmds_condGoto_false {P : PureExpr} [HasFvar P] [HasNot P]
    (extendEval : ExtendEval P)
    (accum : List (Cmd P))
    (e : P.Expr) (tl fl : String) (md : MetaData P)
    (l_ite : String) (gen_e gen_f : StringGenState)
    (accumEntry : String) (accumBlocks : DetBlocks String (Cmd P) P)
    (h_flush_eq : flushCmds "ite$" accum
      (some (DetTransferCmd.condGoto e tl fl md)) l_ite gen_e = ((accumEntry, accumBlocks), gen_f))
    (σ_base : SemanticStore P) (hf_base hf_accum : Bool)
    (ρ₀ : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (h_accum : EvalCmds P (EvalCmd P) ρ₀.eval σ_base accum.reverse ρ₀.store hf_accum)
    (h_hf : ρ₀.hasFailure = (hf_base || hf_accum))
    (h_cond : ρ₀.eval ρ₀.store e = .some HasBool.ff)
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (h_cfg_accum : ∀ b ∈ accumBlocks, b ∈ cfg.blocks)
    (h_lookup : ∀ lbl blk, (lbl, blk) ∈ cfg.blocks →
      cfg.blocks.lookup lbl = some blk) :
    StepDetCFGStar extendEval cfg
      (.cont accumEntry σ_base hf_base)
      (.cont fl ρ₀.store ρ₀.hasFailure) := by
  -- With the fixed flushCmds, `tr? = some _` always emits a single block.
  unfold flushCmds at h_flush_eq
  simp only [bind, StateT.bind, pure, StateT.pure, Id] at h_flush_eq
  injection h_flush_eq with h_pair h_gen_eq
  injection h_pair with h_entry_eq h_blks_eq
  subst h_entry_eq; subst h_blks_eq
  have h_mem := h_cfg_accum _ (List.Mem.head _)
  have h_lkp := h_lookup _ _ h_mem
  have h_eval_block : EvalDetBlock P (EvalCmd P) extendEval
      σ_base ⟨accum.reverse, .condGoto e tl fl md⟩
      (.cont fl ρ₀.store hf_accum) :=
    EvalDetBlock.step_goto_false (δ := ρ₀.eval) h_accum h_cond hwfb
  have h_step : @StepCFG _ _ (Cmd P) _ P
      (EvalDetBlock P (EvalCmd P) extendEval) cfg
      (.cont (StringGenState.gen "ite$" gen_e).fst σ_base hf_base)
      (updateFailure (.cont fl ρ₀.store hf_accum) hf_base) :=
    StepCFG.eval_next (failed := hf_base) h_lkp h_eval_block
  have h_uf : @updateFailure String P (.cont fl ρ₀.store hf_accum) hf_base =
      CFGConfig.cont fl ρ₀.store ρ₀.hasFailure := by
    simp [updateFailure, h_hf, Bool.or_comm]
  rw [h_uf] at h_step
  exact ReflTrans.step _ _ _ h_step (ReflTrans.refl _)

/-! ## Agreement-based variants of flushCmds_condGoto_*

These variants take the CFG-side accumulated trace pre-lifted via
`EvalCmds_under_agreement`, allowing the agreement gap (between structured and
CFG entry stores) to be threaded through the simulation. -/

/-- Variant of `flushCmds_condGoto_true` that operates under StoreAgreement:
the input accum trace is on the CFG side (lifted via `EvalCmds_under_agreement`)
and reaches `σ_cfg_after`, which agrees with `ρ₀.store`. -/
private theorem flushCmds_condGoto_true_agree {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P)
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
    (h_cond : ρ₀.eval ρ₀.store e = .some HasBool.tt)
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (h_cfg_accum : ∀ b ∈ accumBlocks, b ∈ cfg.blocks)
    (h_lookup : ∀ lbl blk, (lbl, blk) ∈ cfg.blocks →
      cfg.blocks.lookup lbl = some blk) :
    StepDetCFGStar extendEval cfg
      (.cont accumEntry σ_base hf_base)
      (.cont tl σ_cfg_after ρ₀.hasFailure) := by
  unfold flushCmds at h_flush_eq
  simp only [bind, StateT.bind, pure, StateT.pure, Id] at h_flush_eq
  injection h_flush_eq with h_pair h_gen_eq
  injection h_pair with h_entry_eq h_blks_eq
  subst h_entry_eq; subst h_blks_eq
  have h_def_e : isDefined ρ₀.store (HasVarsPure.getVars e) :=
    h_wf_def e HasBool.tt ρ₀.store h_cond
  have h_pointwise :
      ∀ y ∈ HasVarsPure.getVars e, ρ₀.store y = σ_cfg_after y :=
    store_agreement_pointwise_on_expr_vars ρ₀.store σ_cfg_after e h_agree_after h_def_e
  have h_cond_cfg : ρ₀.eval σ_cfg_after e = .some HasBool.tt := by
    rw [← h_cond]
    exact (h_congr e ρ₀.store σ_cfg_after h_pointwise).symm
  have h_mem := h_cfg_accum _ (List.Mem.head _)
  have h_lkp := h_lookup _ _ h_mem
  have h_eval_block : EvalDetBlock P (EvalCmd P) extendEval
      σ_base ⟨accum.reverse, .condGoto e tl fl md⟩
      (.cont tl σ_cfg_after hf_accum) :=
    EvalDetBlock.step_goto_true (δ := ρ₀.eval) h_accum_cfg h_cond_cfg hwfb
  have h_step : @StepCFG _ _ (Cmd P) _ P
      (EvalDetBlock P (EvalCmd P) extendEval) cfg
      (.cont (StringGenState.gen "ite$" gen_e).fst σ_base hf_base)
      (updateFailure (.cont tl σ_cfg_after hf_accum) hf_base) :=
    StepCFG.eval_next (failed := hf_base) h_lkp h_eval_block
  have h_uf : @updateFailure String P (.cont tl σ_cfg_after hf_accum) hf_base =
      CFGConfig.cont tl σ_cfg_after ρ₀.hasFailure := by
    simp [updateFailure, h_hf, Bool.or_comm]
  rw [h_uf] at h_step
  exact ReflTrans.step _ _ _ h_step (ReflTrans.refl _)

/-- Variant of `flushCmds_condGoto_false` that operates under StoreAgreement. -/
private theorem flushCmds_condGoto_false_agree {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVarsPure P P.Expr]
    (extendEval : ExtendEval P)
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
    (h_cond : ρ₀.eval ρ₀.store e = .some HasBool.ff)
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (h_cfg_accum : ∀ b ∈ accumBlocks, b ∈ cfg.blocks)
    (h_lookup : ∀ lbl blk, (lbl, blk) ∈ cfg.blocks →
      cfg.blocks.lookup lbl = some blk) :
    StepDetCFGStar extendEval cfg
      (.cont accumEntry σ_base hf_base)
      (.cont fl σ_cfg_after ρ₀.hasFailure) := by
  unfold flushCmds at h_flush_eq
  simp only [bind, StateT.bind, pure, StateT.pure, Id] at h_flush_eq
  injection h_flush_eq with h_pair h_gen_eq
  injection h_pair with h_entry_eq h_blks_eq
  subst h_entry_eq; subst h_blks_eq
  have h_def_e : isDefined ρ₀.store (HasVarsPure.getVars e) :=
    h_wf_def e HasBool.ff ρ₀.store h_cond
  have h_pointwise :
      ∀ y ∈ HasVarsPure.getVars e, ρ₀.store y = σ_cfg_after y :=
    store_agreement_pointwise_on_expr_vars ρ₀.store σ_cfg_after e h_agree_after h_def_e
  have h_cond_cfg : ρ₀.eval σ_cfg_after e = .some HasBool.ff := by
    rw [← h_cond]
    exact (h_congr e ρ₀.store σ_cfg_after h_pointwise).symm
  have h_mem := h_cfg_accum _ (List.Mem.head _)
  have h_lkp := h_lookup _ _ h_mem
  have h_eval_block : EvalDetBlock P (EvalCmd P) extendEval
      σ_base ⟨accum.reverse, .condGoto e tl fl md⟩
      (.cont fl σ_cfg_after hf_accum) :=
    EvalDetBlock.step_goto_false (δ := ρ₀.eval) h_accum_cfg h_cond_cfg hwfb
  have h_step : @StepCFG _ _ (Cmd P) _ P
      (EvalDetBlock P (EvalCmd P) extendEval) cfg
      (.cont (StringGenState.gen "ite$" gen_e).fst σ_base hf_base)
      (updateFailure (.cont fl σ_cfg_after hf_accum) hf_base) :=
    StepCFG.eval_next (failed := hf_base) h_lkp h_eval_block
  have h_uf : @updateFailure String P (.cont fl σ_cfg_after hf_accum) hf_base =
      CFGConfig.cont fl σ_cfg_after ρ₀.hasFailure := by
    simp [updateFailure, h_hf, Bool.or_comm]
  rw [h_uf] at h_step
  exact ReflTrans.step _ _ _ h_step (ReflTrans.refl _)

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

private theorem Block.uniqueInits.loop_body {P : PureExpr}
    {guard : ExprOrNondet P} {measure : Option P.Expr}
    {invariants : List (String × P.Expr)}
    {bss : List (Stmt P (Cmd P))} {md : MetaData P}
    {rest : List (Stmt P (Cmd P))}
    (h : Block.uniqueInits (.loop guard measure invariants bss md :: rest)) :
    Block.uniqueInits bss := by
  have h_head := Block.uniqueInits.head_stmt h
  unfold Stmt.initVars at h_head
  exact h_head

/-! ## Block.noBlocks projection helpers

`Block.noBlocks ss` is a boolean predicate identifying statement lists
containing no `.block` constructor. These helpers project it down to
sub-lists used by the recursive simulation calls. -/

private theorem Block.noBlocks.tail {P : PureExpr} {C : Type}
    {s : Stmt P C} {ss : List (Stmt P C)}
    (h : Block.noBlocks (s :: ss) = true) : Block.noBlocks ss = true := by
  rw [Block.noBlocks] at h
  exact (Bool.and_eq_true _ _).mp h |>.2

private theorem Block.noBlocks.head_stmt {P : PureExpr} {C : Type}
    {s : Stmt P C} {ss : List (Stmt P C)}
    (h : Block.noBlocks (s :: ss) = true) : Stmt.noBlocks s = true := by
  rw [Block.noBlocks] at h
  exact (Bool.and_eq_true _ _).mp h |>.1

private theorem Block.noBlocks.ite_then {P : PureExpr} {C : Type}
    {g : ExprOrNondet P} {tss ess : List (Stmt P C)} {md : MetaData P}
    {rest : List (Stmt P C)}
    (h : Block.noBlocks (.ite g tss ess md :: rest) = true) :
    Block.noBlocks tss = true := by
  have h_head := Block.noBlocks.head_stmt h
  rw [Stmt.noBlocks] at h_head
  exact (Bool.and_eq_true _ _).mp h_head |>.1

private theorem Block.noBlocks.ite_else {P : PureExpr} {C : Type}
    {g : ExprOrNondet P} {tss ess : List (Stmt P C)} {md : MetaData P}
    {rest : List (Stmt P C)}
    (h : Block.noBlocks (.ite g tss ess md :: rest) = true) :
    Block.noBlocks ess = true := by
  have h_head := Block.noBlocks.head_stmt h
  rw [Stmt.noBlocks] at h_head
  exact (Bool.and_eq_true _ _).mp h_head |>.2

private theorem Block.noBlocks.loop_body {P : PureExpr} {C : Type}
    {guard : ExprOrNondet P} {measure : Option P.Expr}
    {invariants : List (String × P.Expr)}
    {bss : List (Stmt P C)} {md : MetaData P}
    {rest : List (Stmt P C)}
    (h : Block.noBlocks (.loop guard measure invariants bss md :: rest) = true) :
    Block.noBlocks bss = true := by
  have h_head := Block.noBlocks.head_stmt h
  rw [Stmt.noBlocks] at h_head
  exact h_head

/-! ## Generalized simulation

The central lemma: for any continuation `k`, exit-continuation stack, and
accumulated commands, if the structured execution of `ss` from `ρ₀` terminates
(or exits), then the CFG blocks produced by `stmtsToBlocks` can step from the
entry label to the continuation `k` (or the resolved exit target). -/

private theorem flushCmds_simulation {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P]
    (extendEval : ExtendEval P)
    (pfx : String)
    (k : String)
    (accum : List (Cmd P))
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : (flushCmds pfx accum .none k gen) = ((entry, blocks), gen'))
    (σ_base : SemanticStore P)
    (hf_base : Bool)
    (hf_accum : Bool)
    (ρ₀ : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (h_accum : EvalCmds P (EvalCmd P) ρ₀.eval σ_base accum.reverse ρ₀.store hf_accum)
    (h_hf : ρ₀.hasFailure = (hf_base || hf_accum))
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (h_cfg_blocks : ∀ b ∈ blocks, b ∈ cfg.blocks)
    (h_cfg_nodup : (cfg.blocks.map Prod.fst).Nodup) :
    StepDetCFGStar extendEval cfg
      (.cont entry σ_base hf_base)
      (.cont k ρ₀.store ρ₀.hasFailure) := by
  unfold flushCmds at h_gen
  simp only at h_gen  -- reduce the `match tr? with | none => ...` to just the none branch
  split at h_gen
  case isTrue h_empty =>
    have ⟨h_entry, h_blocks⟩ := Prod.mk.inj (Prod.mk.inj h_gen).1
    subst h_entry; subst h_blocks
    have h_nil : accum.reverse = [] := by
      simp [List.isEmpty_iff] at h_empty; simp [h_empty]
    have ⟨h_store, h_fail⟩ := EvalCmds_inv ρ₀.eval σ_base ρ₀.store hf_accum
      (h_nil ▸ h_accum)
    subst h_store; subst h_fail
    simp [Bool.or_false] at h_hf
    rw [h_hf]
    exact ReflTrans.refl _
  case isFalse h_nonempty =>
    -- accum is non-empty: flushCmds generates a fresh label `entry` and a single block
    -- (entry, { cmds := accum.reverse, transfer := .goto k })
    simp only [bind, StateT.bind, pure, StateT.pure, Id] at h_gen
    injection h_gen with h_pair h_gen_eq
    injection h_pair with h_entry_eq h_blks_eq
    subst h_entry_eq; subst h_blks_eq
    -- entry = (gen pfx gen).fst, blocks = [(entry, { cmds := accum.reverse, transfer := .goto k })]
    have h_mem :
        ((StringGenState.gen pfx gen).fst,
          ({ cmds := accum.reverse, transfer := DetTransferCmd.goto k }
            : DetBlock String (Cmd P) P)) ∈ cfg.blocks :=
      h_cfg_blocks _ (List.Mem.head _)
    -- Build EvalDetBlock via the goto bridge: .goto k = .condGoto HasBool.tt k k _.
    have h_cond_tt : ρ₀.eval ρ₀.store HasBool.tt = .some HasBool.tt :=
      eval_tt_is_tt ρ₀.eval ρ₀.store hwfv
    have h_goto_eq :
        (DetTransferCmd.goto k : DetTransferCmd String P) =
          DetTransferCmd.condGoto HasBool.tt k k .empty := rfl
    have h_eval_block : EvalDetBlock P (EvalCmd P) extendEval
        σ_base ⟨accum.reverse, DetTransferCmd.goto k⟩
        (.cont k ρ₀.store hf_accum) := by
      rw [h_goto_eq]
      exact EvalDetBlock.step_goto_true (δ := ρ₀.eval) h_accum h_cond_tt hwfb
    have h_lkp : cfg.blocks.lookup (StringGenState.gen pfx gen).fst =
        some { cmds := accum.reverse, transfer := DetTransferCmd.goto k } :=
      List.lookup_of_mem_nodup cfg.blocks h_cfg_nodup _ _ h_mem
    have h_step : @StepCFG _ _ (Cmd P) _ P
        (EvalDetBlock P (EvalCmd P) extendEval) cfg
        (.cont (StringGenState.gen pfx gen).fst σ_base hf_base)
        (updateFailure (.cont k ρ₀.store hf_accum) hf_base) :=
      StepCFG.eval_next (failed := hf_base) h_lkp h_eval_block
    have h_uf : @updateFailure String P (.cont k ρ₀.store hf_accum) hf_base =
        CFGConfig.cont k ρ₀.store ρ₀.hasFailure := by
      simp [updateFailure, h_hf, Bool.or_comm]
    rw [h_uf] at h_step
    exact ReflTrans.step _ _ _ h_step (ReflTrans.refl _)

/-- Variant of `flushCmds_simulation` that operates under StoreAgreement: the
input accum trace runs from `σ_struct_base` (struct side) to `ρ₀.store`
(struct side), and `StoreAgreement σ_struct_base σ_base` holds at the entry. -/
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
      (.cont entry σ_base hf_base)
      (.cont k σ_cfg ρ₀.hasFailure)
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
          ({ cmds := accum.reverse, transfer := DetTransferCmd.goto k }
            : DetBlock String (Cmd P) P)) ∈ cfg.blocks :=
      h_cfg_blocks _ (List.Mem.head _)
    have h_cond_tt : ρ₀.eval σ_cfg_after HasBool.tt = .some HasBool.tt :=
      eval_tt_is_tt ρ₀.eval σ_cfg_after hwfv
    have h_goto_eq :
        (DetTransferCmd.goto k : DetTransferCmd String P) =
          DetTransferCmd.condGoto HasBool.tt k k .empty := rfl
    have h_eval_block : EvalDetBlock P (EvalCmd P) extendEval
        σ_base ⟨accum.reverse, DetTransferCmd.goto k⟩
        (.cont k σ_cfg_after hf_accum) := by
      rw [h_goto_eq]
      exact EvalDetBlock.step_goto_true (δ := ρ₀.eval) h_accum_cfg h_cond_tt hwfb
    have h_lkp : cfg.blocks.lookup (StringGenState.gen pfx gen).fst =
        some { cmds := accum.reverse, transfer := DetTransferCmd.goto k } :=
      List.lookup_of_mem_nodup cfg.blocks h_cfg_nodup _ _ h_mem
    have h_step : @StepCFG _ _ (Cmd P) _ P
        (EvalDetBlock P (EvalCmd P) extendEval) cfg
        (.cont (StringGenState.gen pfx gen).fst σ_base hf_base)
        (updateFailure (.cont k σ_cfg_after hf_accum) hf_base) :=
      StepCFG.eval_next (failed := hf_base) h_lkp h_eval_block
    have h_uf : @updateFailure String P (.cont k σ_cfg_after hf_accum) hf_base =
        CFGConfig.cont k σ_cfg_after ρ₀.hasFailure := by
      simp [updateFailure, h_hf, Bool.or_comm]
    rw [h_uf] at h_step
    refine ⟨σ_cfg_after, ReflTrans.step _ _ _ h_step (ReflTrans.refl _), h_agree_after, ?_⟩
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
      (.cont entry σ_base hf_base)
      (.cont bk σ_cfg ρ₀.hasFailure)
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
  have h_goto_eq :
      (DetTransferCmd.goto bk md : DetTransferCmd String P) =
        DetTransferCmd.condGoto HasBool.tt bk bk md := rfl
  have h_eval_block : EvalDetBlock P (EvalCmd P) extendEval
      σ_base ⟨accum.reverse, DetTransferCmd.goto bk md⟩
      (.cont bk σ_cfg_after hf_accum) := by
    rw [h_goto_eq]
    exact EvalDetBlock.step_goto_true (δ := ρ₀.eval) h_accum_cfg h_cond_tt hwfb
  have h_lkp : cfg.blocks.lookup (StringGenState.gen pfx gen).fst =
      some { cmds := accum.reverse, transfer := DetTransferCmd.goto bk md } :=
    List.lookup_of_mem_nodup cfg.blocks h_cfg_nodup _ _ h_mem
  have h_step : @StepCFG _ _ (Cmd P) _ P
      (EvalDetBlock P (EvalCmd P) extendEval) cfg
      (.cont (StringGenState.gen pfx gen).fst σ_base hf_base)
      (updateFailure (.cont bk σ_cfg_after hf_accum) hf_base) :=
    StepCFG.eval_next (failed := hf_base) h_lkp h_eval_block
  have h_uf : @updateFailure String P (.cont bk σ_cfg_after hf_accum) hf_base =
      CFGConfig.cont bk σ_cfg_after ρ₀.hasFailure := by
    simp [updateFailure, h_hf, Bool.or_comm]
  rw [h_uf] at h_step
  refine ⟨σ_cfg_after, ReflTrans.step _ _ _ h_step (ReflTrans.refl _), h_agree_after, ?_⟩
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

set_option maxHeartbeats 1600000 in
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
    (extendEval : ExtendEval P)
    (k : String) (ss : List (Stmt P (Cmd P)))
    (exitConts : List (Option String × String))
    (accum : List (Cmd P))
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : (stmtsToBlocks k ss exitConts accum gen) = ((entry, blocks), gen'))
    (h_nofd : Block.noFuncDecl ss = true)
    (h_unique : Block.uniqueInits ss)
    (σ_struct_base σ_base : SemanticStore P)
    (hf_base : Bool)
    (hf_accum : Bool)
    (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwf_def : WellFormedSemanticEvalDef ρ₀.eval)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (h_term : StepStmtStar P (EvalCmd P) extendEval
      (.stmts ss ρ₀) (.terminal ρ'))
    (h_accum : EvalCmds P (EvalCmd P) ρ₀.eval σ_struct_base accum.reverse ρ₀.store hf_accum)
    (h_agree_entry : StoreAgreement σ_struct_base σ_base)
    (h_fresh_combined :
      ∀ x ∈ Cmds.definedVars accum.reverse ++ Block.initVars ss, σ_base x = none)
    (h_unique_combined :
      (Cmds.definedVars accum.reverse ++ Block.initVars ss).Nodup)
    (h_hf : ρ₀.hasFailure = (hf_base || hf_accum))
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (h_cfg_blocks : ∀ b ∈ blocks, b ∈ cfg.blocks)
    (h_cfg_nodup : (cfg.blocks.map Prod.fst).Nodup) :
    ∃ σ_cfg, StepDetCFGStar extendEval cfg
      (.cont entry σ_base hf_base)
      (.cont k σ_cfg ρ'.hasFailure)
      ∧ StoreAgreement ρ'.store σ_cfg
      ∧ (∀ x, σ_base x = none →
          x ∉ Cmds.definedVars accum.reverse → x ∉ Block.initVars ss →
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
    intro x h_σ_x h_x_not_accum _
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
    have hwfb' : WellFormedSemanticEvalBool ρ₁.eval := by rw [heval_eq_c]; exact hwfb
    have hwfv' : WellFormedSemanticEvalVal ρ₁.eval := by rw [heval_eq_c]; exact hwfv
    have hwf_def' : WellFormedSemanticEvalDef ρ₁.eval := by rw [heval_eq_c]; exact hwf_def
    have hwf_congr' : WellFormedSemanticEvalExprCongr ρ₁.eval := by
      rw [heval_eq_c]; exact hwf_congr
    have h_nofd_rest : Block.noFuncDecl rest = true := by
      simp [Block.noFuncDecl] at h_nofd; exact h_nofd.2
    have h_unique_rest : Block.uniqueInits rest := Block.uniqueInits.tail h_unique
    -- Show that the combined defined-vars list is identical for the two sides
    -- of the recursion (just rebracketed).
    have h_definedVars_snoc :
        Cmds.definedVars (accum.reverse ++ [c]) =
        Cmds.definedVars accum.reverse ++ Cmd.definedVars c := by
      induction accum.reverse with
      | nil => simp [Cmds.definedVars]
      | cons hd tl ih =>
        rw [List.cons_append, Cmds.definedVars_cons, Cmds.definedVars_cons,
            ih, List.append_assoc]
    have h_eq_combined :
        Cmds.definedVars (c :: accum).reverse ++ Block.initVars rest =
        Cmds.definedVars accum.reverse ++ Block.initVars (.cmd c :: rest) := by
      rw [List.reverse_cons, h_definedVars_snoc]
      rw [Block.initVars]
      cases c <;> simp [Stmt.initVars, Cmd.definedVars, List.append_assoc]
    have h_fresh_combined' :
        ∀ x ∈ Cmds.definedVars (c :: accum).reverse ++ Block.initVars rest,
        σ_base x = none := by
      intro x hx
      rw [h_eq_combined] at hx
      exact h_fresh_combined x hx
    have h_unique_combined' :
        (Cmds.definedVars (c :: accum).reverse ++ Block.initVars rest).Nodup := by
      rw [h_eq_combined]
      exact h_unique_combined
    have ⟨σ_cfg, h_step, h_agree, h_preserve⟩ :=
      stmtsToBlocks_simulation extendEval k rest exitConts (c :: accum) gen gen'
        entry blocks h_gen h_nofd_rest h_unique_rest
        σ_struct_base σ_base hf_base (hf_accum || failed_c)
        ρ₁ ρ' hwfb' hwfv' hwf_def' hwf_congr' h_rest_star h_accum'
        h_agree_entry h_fresh_combined' h_unique_combined' h_hf'
        cfg h_cfg_blocks h_cfg_nodup
    refine ⟨σ_cfg, h_step, h_agree, ?_⟩
    intro x h_σ_x h_x_not_accum h_x_not_inits
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
          simp [Block.initVars, Stmt.initVars]
        | _ => simp [Cmd.definedVars] at h
    have h_x_not_rest_inits : x ∉ Block.initVars rest := by
      intro h
      apply h_x_not_inits
      rw [Block.initVars]
      -- Stmt.initVars (.cmd _) is either [x'] or [], in either case x ∈ rhs ∪ Block.initVars rest
      cases c <;> simp [Stmt.initVars] <;> first | right; exact h | exact h
    exact h_preserve x h_σ_x h_x_not_new_accum h_x_not_rest_inits
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
    -- Eval well-formedness preservation through ite branch
    have hwfb₁ : WellFormedSemanticEvalBool ρ₁.eval := by
      cases h_ite_inv with
      | inl h => exact StepStmtStar_wfb_preserved extendEval thenBranch ρ₀ ρ₁ h.1 h_nofd_then hwfb
      | inr h => exact StepStmtStar_wfb_preserved extendEval elseBranch ρ₀ ρ₁ h.1 h_nofd_else hwfb
    have hwfv₁ : WellFormedSemanticEvalVal ρ₁.eval := by
      cases h_ite_inv with
      | inl h => exact StepStmtStar_wfv_preserved extendEval thenBranch ρ₀ ρ₁ h.1 h_nofd_then hwfv
      | inr h => exact StepStmtStar_wfv_preserved extendEval elseBranch ρ₀ ρ₁ h.1 h_nofd_else hwfv
    have h_eval_eq : ρ₁.eval = ρ₀.eval := by
      cases h_ite_inv with
      | inl h =>
        exact smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
          thenBranch ρ₀ ρ₁ h_nofd_then h.1
      | inr h =>
        exact smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
          elseBranch ρ₀ ρ₁ h_nofd_else h.1
    have hwf_def₁ : WellFormedSemanticEvalDef ρ₁.eval := by
      rw [h_eval_eq]; exact hwf_def
    have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ₁.eval := by
      rw [h_eval_eq]; exact hwf_congr
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
      simp [Stmt.initVars]
    have h_unique_outer_inits :
        (Cmds.definedVars accum.reverse ++
          ((Block.initVars thenBranch ++ Block.initVars elseBranch) ++ Block.initVars rest)).Nodup := by
      rw [← h_initvars_eq]; exact h_unique_combined
    -- Freshness for sub-branch and rest recursions.
    have h_fresh_then_inits : ∀ x ∈ Block.initVars thenBranch, σ_cfg_after x = none := by
      intro x hx
      have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
        intro hx_acc
        have h_disj := List.nodup_append.mp h_unique_outer_inits
        have h_disj_lr := h_disj.2.2
        exact h_disj_lr x hx_acc x
          (List.mem_append_left _ (List.mem_append_left _ hx)) rfl
      have h_σ_x : σ_base x = none :=
        h_fresh_combined x (List.mem_append_right _
          (h_initvars_eq ▸ List.mem_append_left _ (List.mem_append_left _ hx)))
      exact h_preserve_after x h_σ_x h_x_not_accum
    have h_fresh_else_inits : ∀ x ∈ Block.initVars elseBranch, σ_cfg_after x = none := by
      intro x hx
      have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
        intro hx_acc
        have h_disj := List.nodup_append.mp h_unique_outer_inits
        have h_disj_lr := h_disj.2.2
        exact h_disj_lr x hx_acc x
          (List.mem_append_left _ (List.mem_append_right _ hx)) rfl
      have h_σ_x : σ_base x = none :=
        h_fresh_combined x (List.mem_append_right _
          (h_initvars_eq ▸ List.mem_append_left _ (List.mem_append_right _ hx)))
      exact h_preserve_after x h_σ_x h_x_not_accum
    have h_fresh_rest_inits_after :
        ∀ x ∈ Block.initVars rest, σ_cfg_after x = none := by
      intro x hx
      have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
        intro hx_acc
        have h_disj := List.nodup_append.mp h_unique_outer_inits
        have h_disj_lr := h_disj.2.2
        exact h_disj_lr x hx_acc x
          (List.mem_append_right _ hx) rfl
      have h_σ_x : σ_base x = none :=
        h_fresh_combined x (List.mem_append_right _
          (h_initvars_eq ▸ List.mem_append_right _ hx))
      exact h_preserve_after x h_σ_x h_x_not_accum
    -- Combined freshness for branch recursion (empty accum + branch's inits).
    have h_combined_then :
        ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars thenBranch,
        σ_cfg_after x = none := by
      intro x hx
      simp [Cmds.definedVars] at hx
      exact h_fresh_then_inits x hx
    have h_unique_combined_then :
        (Cmds.definedVars [].reverse ++ Block.initVars thenBranch).Nodup := by
      simp [Cmds.definedVars]
      have h1 : ((Block.initVars thenBranch ++ Block.initVars elseBranch) ++
                  Block.initVars rest).Nodup :=
        (List.nodup_append.mp h_unique_outer_inits).2.1
      have h2 : (Block.initVars thenBranch ++ Block.initVars elseBranch).Nodup :=
        (List.nodup_append.mp h1).1
      exact (List.nodup_append.mp h2).1
    have h_combined_else :
        ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars elseBranch,
        σ_cfg_after x = none := by
      intro x hx
      simp [Cmds.definedVars] at hx
      exact h_fresh_else_inits x hx
    have h_unique_combined_else :
        (Cmds.definedVars [].reverse ++ Block.initVars elseBranch).Nodup := by
      simp [Cmds.definedVars]
      have h1 : ((Block.initVars thenBranch ++ Block.initVars elseBranch) ++
                  Block.initVars rest).Nodup :=
        (List.nodup_append.mp h_unique_outer_inits).2.1
      have h2 : (Block.initVars thenBranch ++ Block.initVars elseBranch).Nodup :=
        (List.nodup_append.mp h1).1
      exact (List.nodup_append.mp h2).2.1
    -- Lookup helper for the condGoto helpers
    have h_lookup : ∀ lbl blk, (lbl, blk) ∈ cfg.blocks →
        cfg.blocks.lookup lbl = some blk :=
      fun lbl blk h_mem => List.lookup_of_mem_nodup cfg.blocks h_cfg_nodup lbl blk h_mem
    cases h_ite_inv with
    | inl h_true =>
      obtain ⟨h_then_term, h_cond_tt⟩ := h_true
      -- Step from accumEntry to tl via the lifted accum + condGoto.
      have h_flush_sim : StepDetCFGStar extendEval cfg
          (.cont accumEntry σ_base hf_base)
          (.cont tl σ_cfg_after ρ₀.hasFailure) :=
        flushCmds_condGoto_true_agree extendEval accum e tl fl md l_ite gen_e gen_f
          accumEntry accumBlocks h_flush_eq σ_base σ_cfg_after hf_base hf_accum ρ₀
          hwfb hwf_def hwf_congr h_accum_cfg h_agree_after h_hf h_cond_tt cfg
          h_cfg_accum h_lookup
      -- Recurse on thenBranch.
      have h_accum_nil_t : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
          [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
      have h_hf_t : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
      have ⟨σ_branch, h_then_step, h_agree_then, h_preserve_then⟩ :=
        stmtsToBlocks_simulation extendEval kNext thenBranch exitConts []
          gen_ite gen_t tl tbs h_then_eq h_nofd_then h_unique_then
          ρ₀.store σ_cfg_after ρ₀.hasFailure false
          ρ₀ ρ₁ hwfb hwfv hwf_def hwf_congr h_then_term h_accum_nil_t h_agree_after
          h_combined_then h_unique_combined_then h_hf_t cfg h_cfg_tbs h_cfg_nodup
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
      -- Combined freshness for rest recursion.
      have h_combined_rest :
          ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
          σ_branch x = none := by
        intro x hx
        simp [Cmds.definedVars] at hx
        exact h_fresh_rest_inits_branch x hx
      have h_unique_combined_rest :
          (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
        simp [Cmds.definedVars]
        have h1 : ((Block.initVars thenBranch ++ Block.initVars elseBranch) ++
                    Block.initVars rest).Nodup :=
          (List.nodup_append.mp h_unique_outer_inits).2.1
        exact (List.nodup_append.mp h1).2.1
      -- Recurse on rest.
      have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ₁.eval ρ₁.store
          [].reverse ρ₁.store false := EvalCmds.eval_cmds_none
      have h_hf_r : ρ₁.hasFailure = (ρ₁.hasFailure || false) := by simp
      have ⟨σ_cfg, h_rest_sim, h_agree_rest, h_preserve_rest⟩ :=
        stmtsToBlocks_simulation extendEval k rest exitConts [] gen gen_r kNext bsNext
          h_rest_eq h_nofd_rest h_unique_rest ρ₁.store σ_branch ρ₁.hasFailure false
          ρ₁ ρ' hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁ h_rest_star h_accum_nil_r h_agree_then
          h_combined_rest h_unique_combined_rest h_hf_r cfg h_cfg_rest h_cfg_nodup
      refine ⟨σ_cfg, ?_, h_agree_rest, ?_⟩
      · exact StepDetCFGStar_trans
          (StepDetCFGStar_trans h_flush_sim h_then_step) h_rest_sim
      · -- Freshness preservation for the outer call.
        intro x h_σ_x h_x_not_accum h_x_not_inits
        -- Decompose h_x_not_inits: x ∉ Block.initVars (.ite ... :: rest)
        --   = x ∉ Block.initVars tss ∧ x ∉ Block.initVars ess ∧ x ∉ Block.initVars rest
        have h_x_not_then : x ∉ Block.initVars thenBranch := by
          intro hx
          apply h_x_not_inits
          rw [h_initvars_eq]; exact List.mem_append_left _ (List.mem_append_left _ hx)
        have h_x_not_else : x ∉ Block.initVars elseBranch := by
          intro hx
          apply h_x_not_inits
          rw [h_initvars_eq]; exact List.mem_append_left _ (List.mem_append_right _ hx)
        have h_x_not_rest : x ∉ Block.initVars rest := by
          intro hx
          apply h_x_not_inits
          rw [h_initvars_eq]; exact List.mem_append_right _ hx
        have h_σ_after_x : σ_cfg_after x = none := h_preserve_after x h_σ_x h_x_not_accum
        have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
        have h_σ_branch_x : σ_branch x = none :=
          h_preserve_then x h_σ_after_x h_nil_not h_x_not_then
        exact h_preserve_rest x h_σ_branch_x h_nil_not h_x_not_rest
    | inr h_false =>
      obtain ⟨h_else_term, h_cond_ff⟩ := h_false
      -- Step from accumEntry to fl via the lifted accum + condGoto.
      have h_flush_sim : StepDetCFGStar extendEval cfg
          (.cont accumEntry σ_base hf_base)
          (.cont fl σ_cfg_after ρ₀.hasFailure) :=
        flushCmds_condGoto_false_agree extendEval accum e tl fl md l_ite gen_e gen_f
          accumEntry accumBlocks h_flush_eq σ_base σ_cfg_after hf_base hf_accum ρ₀
          hwfb hwf_def hwf_congr h_accum_cfg h_agree_after h_hf h_cond_ff cfg
          h_cfg_accum h_lookup
      -- Recurse on elseBranch.
      have h_accum_nil_f : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
          [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
      have h_hf_f : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
      have ⟨σ_branch, h_else_step, h_agree_else, h_preserve_else⟩ :=
        stmtsToBlocks_simulation extendEval kNext elseBranch exitConts []
          gen_t gen_e fl fbs h_else_eq h_nofd_else h_unique_else
          ρ₀.store σ_cfg_after ρ₀.hasFailure false
          ρ₀ ρ₁ hwfb hwfv hwf_def hwf_congr h_else_term h_accum_nil_f h_agree_after
          h_combined_else h_unique_combined_else h_hf_f cfg h_cfg_fbs h_cfg_nodup
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
      -- Combined freshness for rest recursion.
      have h_combined_rest :
          ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
          σ_branch x = none := by
        intro x hx
        simp [Cmds.definedVars] at hx
        exact h_fresh_rest_inits_branch x hx
      have h_unique_combined_rest :
          (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
        simp [Cmds.definedVars]
        have h1 : ((Block.initVars thenBranch ++ Block.initVars elseBranch) ++
                    Block.initVars rest).Nodup :=
          (List.nodup_append.mp h_unique_outer_inits).2.1
        exact (List.nodup_append.mp h1).2.1
      -- Recurse on rest.
      have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ₁.eval ρ₁.store
          [].reverse ρ₁.store false := EvalCmds.eval_cmds_none
      have h_hf_r : ρ₁.hasFailure = (ρ₁.hasFailure || false) := by simp
      have ⟨σ_cfg, h_rest_sim, h_agree_rest, h_preserve_rest⟩ :=
        stmtsToBlocks_simulation extendEval k rest exitConts [] gen gen_r kNext bsNext
          h_rest_eq h_nofd_rest h_unique_rest ρ₁.store σ_branch ρ₁.hasFailure false
          ρ₁ ρ' hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁ h_rest_star h_accum_nil_r h_agree_else
          h_combined_rest h_unique_combined_rest h_hf_r cfg h_cfg_rest h_cfg_nodup
      refine ⟨σ_cfg, ?_, h_agree_rest, ?_⟩
      · exact StepDetCFGStar_trans
          (StepDetCFGStar_trans h_flush_sim h_else_step) h_rest_sim
      · intro x h_σ_x h_x_not_accum h_x_not_inits
        have h_x_not_then : x ∉ Block.initVars thenBranch := by
          intro hx
          apply h_x_not_inits
          rw [h_initvars_eq]; exact List.mem_append_left _ (List.mem_append_left _ hx)
        have h_x_not_else : x ∉ Block.initVars elseBranch := by
          intro hx
          apply h_x_not_inits
          rw [h_initvars_eq]; exact List.mem_append_left _ (List.mem_append_right _ hx)
        have h_x_not_rest : x ∉ Block.initVars rest := by
          intro hx
          apply h_x_not_inits
          rw [h_initvars_eq]; exact List.mem_append_right _ hx
        have h_σ_after_x : σ_cfg_after x = none := h_preserve_after x h_σ_x h_x_not_accum
        have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
        have h_σ_branch_x : σ_branch x = none :=
          h_preserve_else x h_σ_after_x h_nil_not h_x_not_else
        exact h_preserve_rest x h_σ_branch_x h_nil_not h_x_not_rest
  | .ite .nondet thenBranch elseBranch md :: rest =>
    sorry
  | .loop guard measure invariants body md :: rest =>
    sorry
  | .block label body md :: rest =>
    unfold stmtsToBlocks at h_gen
    simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
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
      cases h_block_inv with
      | inl h =>
        obtain ⟨ρ_i, hterm, heq⟩ := h
        exact ⟨ρ_i, Or.inl hterm, heq⟩
      | inr h =>
        obtain ⟨ρ_i, hexit, heq⟩ := h
        exact ⟨ρ_i, Or.inr hexit, heq⟩
    -- noFuncDecl projections.
    have h_nofd_body : Block.noFuncDecl body = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.1
    have h_nofd_rest : Block.noFuncDecl rest = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.2
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
      simp [Stmt.initVars]
    -- Block membership distribution. We split based on l = bl vs l ≠ bl.
    -- Convert h_gen via the if: extract entry and the blocks shape.
    by_cases h_l_eq_bl : label = bl
    · -- Case l = bl: blocks = accumBlocks ++ bbs ++ bsNext, entry = accumEntry.
      simp [h_l_eq_bl] at h_gen
      have h_entry_eq : accumEntry = entry :=
        (Prod.mk.inj (Prod.mk.inj h_gen).1).1
      have h_blocks_eq : accumBlocks ++ (bbs ++ bsNext) = blocks :=
        (Prod.mk.inj (Prod.mk.inj h_gen).1).2
      subst h_entry_eq
      subst h_blocks_eq
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
      -- Now we have: (.cont accumEntry σ_base hf_base) → (.cont bl σ_cfg_after ρ₀.hasFailure)
      -- Body recursion: from (.cont bl σ_cfg_after ρ₀.hasFailure) to (.cont kNext σ_cfg_body _).
      -- Body's structured run is from ρ₀ to ρ_inner.
      -- Need to handle both terminal and exit-match cases for body.
      cases h_body_term_or_exit with
      | inl h_body_term =>
        -- Body terminates with ρ_inner; use that for the sim.
        -- Freshness for body recursion (initVars body must be fresh in σ_cfg_after).
        have h_fresh_body_inits_after : ∀ x ∈ Block.initVars body, σ_cfg_after x = none := by
          intro x hx
          have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
            intro h_in_accum
            -- x in body's initVars and accum's defs both, contradicting Nodup.
            have h_disj_lr := List.nodup_append.mp h_unique_combined
            rw [h_initvars_eq] at h_disj_lr
            have h_disj := h_disj_lr.2.2
            exact h_disj x h_in_accum x (List.mem_append_left _ hx) rfl
          have h_σ_base_x : σ_base x = none := by
            apply h_fresh_combined
            apply List.mem_append_right
            rw [h_initvars_eq]
            exact List.mem_append_left _ hx
          exact h_preserve_flush x h_σ_base_x h_x_not_accum
        have h_combined_body :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
            σ_cfg_after x = none := by
          intro x hx
          simp [Cmds.definedVars] at hx
          exact h_fresh_body_inits_after x hx
        have h_unique_combined_body :
            (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
          simp [Cmds.definedVars]
          unfold Block.uniqueInits at h_unique_body
          exact h_unique_body
        have h_accum_nil : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have h_hf_body : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
        -- Recurse on body.
        have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
          stmtsToBlocks_simulation extendEval kNext body
            ((some label, kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
            h_nofd_body h_unique_body
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ_inner hwfb hwfv hwf_def hwf_congr h_body_term h_accum_nil h_agree_after
            h_combined_body h_unique_combined_body h_hf_body cfg h_cfg_bbs h_cfg_nodup
        -- h_agree_body : StoreAgreement ρ_inner.store σ_cfg_body
        -- Bridge structured-side projection to CFG.
        have h_agree_proj : StoreAgreement (projectStore ρ₀.store ρ_inner.store) ρ_inner.store :=
          StoreAgreement.of_projectStore _ _
        have h_agree_block_body : StoreAgreement ρ_blk.store σ_cfg_body := by
          rw [h_ρ_blk_eq]
          exact StoreAgreement.trans h_agree_proj h_agree_body
        -- Eval well-formedness preservation through body.
        have h_eval_eq : ρ_inner.eval = ρ₀.eval :=
          smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
            body ρ₀ ρ_inner h_nofd_body h_body_term
        have hwfb₁ : WellFormedSemanticEvalBool ρ_blk.eval := by
          rw [h_ρ_blk_eq]; show WellFormedSemanticEvalBool ρ_inner.eval
          rw [h_eval_eq]; exact hwfb
        have hwfv₁ : WellFormedSemanticEvalVal ρ_blk.eval := by
          rw [h_ρ_blk_eq]; show WellFormedSemanticEvalVal ρ_inner.eval
          rw [h_eval_eq]; exact hwfv
        have hwf_def₁ : WellFormedSemanticEvalDef ρ_blk.eval := by
          rw [h_ρ_blk_eq]; show WellFormedSemanticEvalDef ρ_inner.eval
          rw [h_eval_eq]; exact hwf_def
        have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_blk.eval := by
          rw [h_ρ_blk_eq]; show WellFormedSemanticEvalExprCongr ρ_inner.eval
          rw [h_eval_eq]; exact hwf_congr
        -- Freshness for rest's inits at σ_cfg_body.
        have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none := by
          intro x hx
          have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
            intro h_in_accum
            have h_disj_lr := List.nodup_append.mp h_unique_combined
            rw [h_initvars_eq] at h_disj_lr
            have h_disj := h_disj_lr.2.2
            exact h_disj x h_in_accum x
              (List.mem_append_right _ hx) rfl
          have h_σ_base_x : σ_base x = none := by
            apply h_fresh_combined
            apply List.mem_append_right
            rw [h_initvars_eq]
            exact List.mem_append_right _ hx
          exact h_preserve_flush x h_σ_base_x h_x_not_accum
        have h_fresh_rest_inits_body : ∀ x ∈ Block.initVars rest, σ_cfg_body x = none := by
          intro x hx
          have h_x_not_body : x ∉ Block.initVars body := by
            intro h_in_body
            unfold Block.uniqueInits at h_unique
            rw [h_initvars_eq] at h_unique
            have h_disj_lr := (List.nodup_append.mp h_unique).2.2
            exact h_disj_lr x h_in_body x hx rfl
          have h_σ_after_x : σ_cfg_after x = none := h_fresh_rest_inits_after x hx
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          exact h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
        have h_combined_rest :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
            σ_cfg_body x = none := by
          intro x hx
          simp [Cmds.definedVars] at hx
          exact h_fresh_rest_inits_body x hx
        have h_unique_combined_rest :
            (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
          simp [Cmds.definedVars]
          unfold Block.uniqueInits at h_unique_rest
          exact h_unique_rest
        have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_blk.eval ρ_blk.store
            [].reverse ρ_blk.store false := EvalCmds.eval_cmds_none
        have h_hf_r : ρ_blk.hasFailure = (ρ_blk.hasFailure || false) := by simp
        -- ρ_blk.hasFailure = ρ_inner.hasFailure (since projection only changes store)
        have h_hasFail_blk : ρ_blk.hasFailure = ρ_inner.hasFailure := by
          rw [h_ρ_blk_eq]
        -- Recurse on rest.
        have ⟨σ_cfg_rest, h_step_rest, h_agree_rest, h_preserve_rest⟩ :=
          stmtsToBlocks_simulation extendEval k rest exitConts [] gen gen_r kNext bsNext
            h_rest_eq h_nofd_rest h_unique_rest ρ_blk.store σ_cfg_body
            ρ_blk.hasFailure false ρ_blk ρ' hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁
            h_rest_star h_accum_nil_r h_agree_block_body
            h_combined_rest h_unique_combined_rest h_hf_r cfg h_cfg_rest h_cfg_nodup
        refine ⟨σ_cfg_rest, ?_, h_agree_rest, ?_⟩
        · -- Compose the CFG steps.
          -- Need to align the type annotation: h_step_body returns at ρ_inner.hasFailure.
          -- ρ_inner.hasFailure = ρ_blk.hasFailure.
          have h_step_body' : StepDetCFGStar extendEval cfg
              (.cont bl σ_cfg_after ρ₀.hasFailure)
              (.cont kNext σ_cfg_body ρ_blk.hasFailure) := by
            rw [h_hasFail_blk]; exact h_step_body
          exact StepDetCFGStar_trans
            (StepDetCFGStar_trans h_step_flush h_step_body') h_step_rest
        · -- Freshness preservation for the outer call.
          intro x h_σ_x h_x_not_accum h_x_not_inits
          have h_x_not_body : x ∉ Block.initVars body := by
            intro hx
            apply h_x_not_inits
            rw [h_initvars_eq]
            exact List.mem_append_left _ hx
          have h_x_not_rest : x ∉ Block.initVars rest := by
            intro hx
            apply h_x_not_inits
            rw [h_initvars_eq]
            exact List.mem_append_right _ hx
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          have h_σ_body_x : σ_cfg_body x = none :=
            h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
          exact h_preserve_rest x h_σ_body_x h_nil_not h_x_not_rest
      | inr h_body_exit_star =>
        -- Body exits with matching label.  Same final-store shape as inl:
        -- ρ_blk = { ρ_inner with store := projectStore ρ₀.store ρ_inner.store }.
        -- CFG-side: body's exitCont (some label, kNext) resolves `.exit label`
        -- inside body to a goto-kNext, so body's CFG reaches kNext.  Use
        -- `stmtsToBlocks_simulation_to_cont` for the body recursion.
        -- exitConts for body = (some label, kNext) :: exitConts.
        have h_label_lookup :
            ((some label, kNext) :: exitConts).lookup (some label) = some kNext := by
          simp [List.lookup]
        -- Freshness for body recursion.
        have h_fresh_body_inits_after : ∀ x ∈ Block.initVars body, σ_cfg_after x = none := by
          intro x hx
          have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
            intro h_in_accum
            have h_disj_lr := List.nodup_append.mp h_unique_combined
            rw [h_initvars_eq] at h_disj_lr
            have h_disj := h_disj_lr.2.2
            exact h_disj x h_in_accum x (List.mem_append_left _ hx) rfl
          have h_σ_base_x : σ_base x = none := by
            apply h_fresh_combined
            apply List.mem_append_right
            rw [h_initvars_eq]
            exact List.mem_append_left _ hx
          exact h_preserve_flush x h_σ_base_x h_x_not_accum
        have h_combined_body :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
            σ_cfg_after x = none := by
          intro x hx
          simp [Cmds.definedVars] at hx
          exact h_fresh_body_inits_after x hx
        have h_unique_combined_body :
            (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
          simp [Cmds.definedVars]
          unfold Block.uniqueInits at h_unique_body
          exact h_unique_body
        have h_accum_nil : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have h_hf_body : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
        -- Recurse on body with _to_cont.
        have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
          stmtsToBlocks_simulation_to_cont extendEval kNext body
            ((some label, kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
            h_nofd_body h_unique_body
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ_inner label kNext h_label_lookup hwfb hwfv hwf_def hwf_congr
            h_body_exit_star h_accum_nil h_agree_after
            h_combined_body h_unique_combined_body h_hf_body cfg h_cfg_bbs h_cfg_nodup
        -- Bridge structured-side projection to CFG.
        have h_agree_proj : StoreAgreement (projectStore ρ₀.store ρ_inner.store) ρ_inner.store :=
          StoreAgreement.of_projectStore _ _
        have h_agree_block_body : StoreAgreement ρ_blk.store σ_cfg_body := by
          rw [h_ρ_blk_eq]
          exact StoreAgreement.trans h_agree_proj h_agree_body
        -- Eval well-formedness preservation through body (to .exiting).
        have h_eval_eq : ρ_inner.eval = ρ₀.eval :=
          smallStep_noFuncDecl_preserves_eval_block_exiting P (EvalCmd P) extendEval
            body ρ₀ ρ_inner label h_nofd_body h_body_exit_star
        have hwfb₁ : WellFormedSemanticEvalBool ρ_blk.eval := by
          rw [h_ρ_blk_eq]; show WellFormedSemanticEvalBool ρ_inner.eval
          rw [h_eval_eq]; exact hwfb
        have hwfv₁ : WellFormedSemanticEvalVal ρ_blk.eval := by
          rw [h_ρ_blk_eq]; show WellFormedSemanticEvalVal ρ_inner.eval
          rw [h_eval_eq]; exact hwfv
        have hwf_def₁ : WellFormedSemanticEvalDef ρ_blk.eval := by
          rw [h_ρ_blk_eq]; show WellFormedSemanticEvalDef ρ_inner.eval
          rw [h_eval_eq]; exact hwf_def
        have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_blk.eval := by
          rw [h_ρ_blk_eq]; show WellFormedSemanticEvalExprCongr ρ_inner.eval
          rw [h_eval_eq]; exact hwf_congr
        -- Freshness for rest's inits at σ_cfg_body.
        have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none := by
          intro x hx
          have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
            intro h_in_accum
            have h_disj_lr := List.nodup_append.mp h_unique_combined
            rw [h_initvars_eq] at h_disj_lr
            have h_disj := h_disj_lr.2.2
            exact h_disj x h_in_accum x
              (List.mem_append_right _ hx) rfl
          have h_σ_base_x : σ_base x = none := by
            apply h_fresh_combined
            apply List.mem_append_right
            rw [h_initvars_eq]
            exact List.mem_append_right _ hx
          exact h_preserve_flush x h_σ_base_x h_x_not_accum
        have h_fresh_rest_inits_body : ∀ x ∈ Block.initVars rest, σ_cfg_body x = none := by
          intro x hx
          have h_x_not_body : x ∉ Block.initVars body := by
            intro h_in_body
            unfold Block.uniqueInits at h_unique
            rw [h_initvars_eq] at h_unique
            have h_disj_lr := (List.nodup_append.mp h_unique).2.2
            exact h_disj_lr x h_in_body x hx rfl
          have h_σ_after_x : σ_cfg_after x = none := h_fresh_rest_inits_after x hx
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          exact h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
        have h_combined_rest :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
            σ_cfg_body x = none := by
          intro x hx
          simp [Cmds.definedVars] at hx
          exact h_fresh_rest_inits_body x hx
        have h_unique_combined_rest :
            (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
          simp [Cmds.definedVars]
          unfold Block.uniqueInits at h_unique_rest
          exact h_unique_rest
        have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_blk.eval ρ_blk.store
            [].reverse ρ_blk.store false := EvalCmds.eval_cmds_none
        have h_hf_r : ρ_blk.hasFailure = (ρ_blk.hasFailure || false) := by simp
        have h_hasFail_blk : ρ_blk.hasFailure = ρ_inner.hasFailure := by
          rw [h_ρ_blk_eq]
        -- Recurse on rest with _simulation.
        have ⟨σ_cfg_rest, h_step_rest, h_agree_rest, h_preserve_rest⟩ :=
          stmtsToBlocks_simulation extendEval k rest exitConts [] gen gen_r kNext bsNext
            h_rest_eq h_nofd_rest h_unique_rest ρ_blk.store σ_cfg_body
            ρ_blk.hasFailure false ρ_blk ρ' hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁
            h_rest_star h_accum_nil_r h_agree_block_body
            h_combined_rest h_unique_combined_rest h_hf_r cfg h_cfg_rest h_cfg_nodup
        refine ⟨σ_cfg_rest, ?_, h_agree_rest, ?_⟩
        · have h_step_body' : StepDetCFGStar extendEval cfg
              (.cont bl σ_cfg_after ρ₀.hasFailure)
              (.cont kNext σ_cfg_body ρ_blk.hasFailure) := by
            rw [h_hasFail_blk]; exact h_step_body
          exact StepDetCFGStar_trans
            (StepDetCFGStar_trans h_step_flush h_step_body') h_step_rest
        · intro x h_σ_x h_x_not_accum h_x_not_inits
          have h_x_not_body : x ∉ Block.initVars body := by
            intro hx
            apply h_x_not_inits
            rw [h_initvars_eq]
            exact List.mem_append_left _ hx
          have h_x_not_rest : x ∉ Block.initVars rest := by
            intro hx
            apply h_x_not_inits
            rw [h_initvars_eq]
            exact List.mem_append_right _ hx
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          have h_σ_body_x : σ_cfg_body x = none :=
            h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
          exact h_preserve_rest x h_σ_body_x h_nil_not h_x_not_rest
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
      subst h_entry_eq
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
      cases h_body_term_or_exit with
      | inl h_body_term =>
        -- Body terminates with ρ_inner.
        have h_fresh_body_inits_after : ∀ x ∈ Block.initVars body, σ_cfg_after x = none := by
          intro x hx
          have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
            intro h_in_accum
            have h_disj_lr := List.nodup_append.mp h_unique_combined
            rw [h_initvars_eq] at h_disj_lr
            have h_disj := h_disj_lr.2.2
            exact h_disj x h_in_accum x (List.mem_append_left _ hx) rfl
          have h_σ_base_x : σ_base x = none := by
            apply h_fresh_combined
            apply List.mem_append_right
            rw [h_initvars_eq]
            exact List.mem_append_left _ hx
          exact h_preserve_flush x h_σ_base_x h_x_not_accum
        have h_combined_body :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
            σ_cfg_after x = none := by
          intro x hx
          simp [Cmds.definedVars] at hx
          exact h_fresh_body_inits_after x hx
        have h_unique_combined_body :
            (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
          simp [Cmds.definedVars]
          unfold Block.uniqueInits at h_unique_body
          exact h_unique_body
        have h_accum_nil : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have h_hf_body : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
        have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
          stmtsToBlocks_simulation extendEval kNext body
            ((some label, kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
            h_nofd_body h_unique_body
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ_inner hwfb hwfv hwf_def hwf_congr h_body_term h_accum_nil h_agree_after
            h_combined_body h_unique_combined_body h_hf_body cfg h_cfg_bbs h_cfg_nodup
        have h_agree_proj : StoreAgreement (projectStore ρ₀.store ρ_inner.store) ρ_inner.store :=
          StoreAgreement.of_projectStore _ _
        have h_agree_block_body : StoreAgreement ρ_blk.store σ_cfg_body := by
          rw [h_ρ_blk_eq]
          exact StoreAgreement.trans h_agree_proj h_agree_body
        have h_eval_eq : ρ_inner.eval = ρ₀.eval :=
          smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
            body ρ₀ ρ_inner h_nofd_body h_body_term
        have hwfb₁ : WellFormedSemanticEvalBool ρ_blk.eval := by
          rw [h_ρ_blk_eq]; show WellFormedSemanticEvalBool ρ_inner.eval
          rw [h_eval_eq]; exact hwfb
        have hwfv₁ : WellFormedSemanticEvalVal ρ_blk.eval := by
          rw [h_ρ_blk_eq]; show WellFormedSemanticEvalVal ρ_inner.eval
          rw [h_eval_eq]; exact hwfv
        have hwf_def₁ : WellFormedSemanticEvalDef ρ_blk.eval := by
          rw [h_ρ_blk_eq]; show WellFormedSemanticEvalDef ρ_inner.eval
          rw [h_eval_eq]; exact hwf_def
        have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_blk.eval := by
          rw [h_ρ_blk_eq]; show WellFormedSemanticEvalExprCongr ρ_inner.eval
          rw [h_eval_eq]; exact hwf_congr
        have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none := by
          intro x hx
          have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
            intro h_in_accum
            have h_disj_lr := List.nodup_append.mp h_unique_combined
            rw [h_initvars_eq] at h_disj_lr
            have h_disj := h_disj_lr.2.2
            exact h_disj x h_in_accum x
              (List.mem_append_right _ hx) rfl
          have h_σ_base_x : σ_base x = none := by
            apply h_fresh_combined
            apply List.mem_append_right
            rw [h_initvars_eq]
            exact List.mem_append_right _ hx
          exact h_preserve_flush x h_σ_base_x h_x_not_accum
        have h_fresh_rest_inits_body : ∀ x ∈ Block.initVars rest, σ_cfg_body x = none := by
          intro x hx
          have h_x_not_body : x ∉ Block.initVars body := by
            intro h_in_body
            unfold Block.uniqueInits at h_unique
            rw [h_initvars_eq] at h_unique
            have h_disj_lr := (List.nodup_append.mp h_unique).2.2
            exact h_disj_lr x h_in_body x hx rfl
          have h_σ_after_x : σ_cfg_after x = none := h_fresh_rest_inits_after x hx
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          exact h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
        have h_combined_rest :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
            σ_cfg_body x = none := by
          intro x hx
          simp [Cmds.definedVars] at hx
          exact h_fresh_rest_inits_body x hx
        have h_unique_combined_rest :
            (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
          simp [Cmds.definedVars]
          unfold Block.uniqueInits at h_unique_rest
          exact h_unique_rest
        have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_blk.eval ρ_blk.store
            [].reverse ρ_blk.store false := EvalCmds.eval_cmds_none
        have h_hf_r : ρ_blk.hasFailure = (ρ_blk.hasFailure || false) := by simp
        have h_hasFail_blk : ρ_blk.hasFailure = ρ_inner.hasFailure := by
          rw [h_ρ_blk_eq]
        have ⟨σ_cfg_rest, h_step_rest, h_agree_rest, h_preserve_rest⟩ :=
          stmtsToBlocks_simulation extendEval k rest exitConts [] gen gen_r kNext bsNext
            h_rest_eq h_nofd_rest h_unique_rest ρ_blk.store σ_cfg_body
            ρ_blk.hasFailure false ρ_blk ρ' hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁
            h_rest_star h_accum_nil_r h_agree_block_body
            h_combined_rest h_unique_combined_rest h_hf_r cfg h_cfg_rest h_cfg_nodup
        refine ⟨σ_cfg_rest, ?_, h_agree_rest, ?_⟩
        · have h_step_body' : StepDetCFGStar extendEval cfg
              (.cont bl σ_cfg_after ρ₀.hasFailure)
              (.cont kNext σ_cfg_body ρ_blk.hasFailure) := by
            rw [h_hasFail_blk]; exact h_step_body
          exact StepDetCFGStar_trans
            (StepDetCFGStar_trans h_step_flush h_step_body') h_step_rest
        · intro x h_σ_x h_x_not_accum h_x_not_inits
          have h_x_not_body : x ∉ Block.initVars body := by
            intro hx
            apply h_x_not_inits
            rw [h_initvars_eq]
            exact List.mem_append_left _ hx
          have h_x_not_rest : x ∉ Block.initVars rest := by
            intro hx
            apply h_x_not_inits
            rw [h_initvars_eq]
            exact List.mem_append_right _ hx
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          have h_σ_body_x : σ_cfg_body x = none :=
            h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
          exact h_preserve_rest x h_σ_body_x h_nil_not h_x_not_rest
      | inr h_body_exit_star =>
        -- Body exits with matching label; same as l = bl body-exit case.
        have h_label_lookup :
            ((some label, kNext) :: exitConts).lookup (some label) = some kNext := by
          simp [List.lookup]
        have h_fresh_body_inits_after : ∀ x ∈ Block.initVars body, σ_cfg_after x = none := by
          intro x hx
          have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
            intro h_in_accum
            have h_disj_lr := List.nodup_append.mp h_unique_combined
            rw [h_initvars_eq] at h_disj_lr
            have h_disj := h_disj_lr.2.2
            exact h_disj x h_in_accum x (List.mem_append_left _ hx) rfl
          have h_σ_base_x : σ_base x = none := by
            apply h_fresh_combined
            apply List.mem_append_right
            rw [h_initvars_eq]
            exact List.mem_append_left _ hx
          exact h_preserve_flush x h_σ_base_x h_x_not_accum
        have h_combined_body :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
            σ_cfg_after x = none := by
          intro x hx
          simp [Cmds.definedVars] at hx
          exact h_fresh_body_inits_after x hx
        have h_unique_combined_body :
            (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
          simp [Cmds.definedVars]
          unfold Block.uniqueInits at h_unique_body
          exact h_unique_body
        have h_accum_nil : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have h_hf_body : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
        have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
          stmtsToBlocks_simulation_to_cont extendEval kNext body
            ((some label, kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
            h_nofd_body h_unique_body
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ_inner label kNext h_label_lookup hwfb hwfv hwf_def hwf_congr
            h_body_exit_star h_accum_nil h_agree_after
            h_combined_body h_unique_combined_body h_hf_body cfg h_cfg_bbs h_cfg_nodup
        have h_agree_proj : StoreAgreement (projectStore ρ₀.store ρ_inner.store) ρ_inner.store :=
          StoreAgreement.of_projectStore _ _
        have h_agree_block_body : StoreAgreement ρ_blk.store σ_cfg_body := by
          rw [h_ρ_blk_eq]
          exact StoreAgreement.trans h_agree_proj h_agree_body
        have h_eval_eq : ρ_inner.eval = ρ₀.eval :=
          smallStep_noFuncDecl_preserves_eval_block_exiting P (EvalCmd P) extendEval
            body ρ₀ ρ_inner label h_nofd_body h_body_exit_star
        have hwfb₁ : WellFormedSemanticEvalBool ρ_blk.eval := by
          rw [h_ρ_blk_eq]; show WellFormedSemanticEvalBool ρ_inner.eval
          rw [h_eval_eq]; exact hwfb
        have hwfv₁ : WellFormedSemanticEvalVal ρ_blk.eval := by
          rw [h_ρ_blk_eq]; show WellFormedSemanticEvalVal ρ_inner.eval
          rw [h_eval_eq]; exact hwfv
        have hwf_def₁ : WellFormedSemanticEvalDef ρ_blk.eval := by
          rw [h_ρ_blk_eq]; show WellFormedSemanticEvalDef ρ_inner.eval
          rw [h_eval_eq]; exact hwf_def
        have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_blk.eval := by
          rw [h_ρ_blk_eq]; show WellFormedSemanticEvalExprCongr ρ_inner.eval
          rw [h_eval_eq]; exact hwf_congr
        have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none := by
          intro x hx
          have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
            intro h_in_accum
            have h_disj_lr := List.nodup_append.mp h_unique_combined
            rw [h_initvars_eq] at h_disj_lr
            have h_disj := h_disj_lr.2.2
            exact h_disj x h_in_accum x
              (List.mem_append_right _ hx) rfl
          have h_σ_base_x : σ_base x = none := by
            apply h_fresh_combined
            apply List.mem_append_right
            rw [h_initvars_eq]
            exact List.mem_append_right _ hx
          exact h_preserve_flush x h_σ_base_x h_x_not_accum
        have h_fresh_rest_inits_body : ∀ x ∈ Block.initVars rest, σ_cfg_body x = none := by
          intro x hx
          have h_x_not_body : x ∉ Block.initVars body := by
            intro h_in_body
            unfold Block.uniqueInits at h_unique
            rw [h_initvars_eq] at h_unique
            have h_disj_lr := (List.nodup_append.mp h_unique).2.2
            exact h_disj_lr x h_in_body x hx rfl
          have h_σ_after_x : σ_cfg_after x = none := h_fresh_rest_inits_after x hx
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          exact h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
        have h_combined_rest :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
            σ_cfg_body x = none := by
          intro x hx
          simp [Cmds.definedVars] at hx
          exact h_fresh_rest_inits_body x hx
        have h_unique_combined_rest :
            (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
          simp [Cmds.definedVars]
          unfold Block.uniqueInits at h_unique_rest
          exact h_unique_rest
        have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_blk.eval ρ_blk.store
            [].reverse ρ_blk.store false := EvalCmds.eval_cmds_none
        have h_hf_r : ρ_blk.hasFailure = (ρ_blk.hasFailure || false) := by simp
        have h_hasFail_blk : ρ_blk.hasFailure = ρ_inner.hasFailure := by
          rw [h_ρ_blk_eq]
        have ⟨σ_cfg_rest, h_step_rest, h_agree_rest, h_preserve_rest⟩ :=
          stmtsToBlocks_simulation extendEval k rest exitConts [] gen gen_r kNext bsNext
            h_rest_eq h_nofd_rest h_unique_rest ρ_blk.store σ_cfg_body
            ρ_blk.hasFailure false ρ_blk ρ' hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁
            h_rest_star h_accum_nil_r h_agree_block_body
            h_combined_rest h_unique_combined_rest h_hf_r cfg h_cfg_rest h_cfg_nodup
        refine ⟨σ_cfg_rest, ?_, h_agree_rest, ?_⟩
        · have h_step_body' : StepDetCFGStar extendEval cfg
              (.cont bl σ_cfg_after ρ₀.hasFailure)
              (.cont kNext σ_cfg_body ρ_blk.hasFailure) := by
            rw [h_hasFail_blk]; exact h_step_body
          exact StepDetCFGStar_trans
            (StepDetCFGStar_trans h_step_flush h_step_body') h_step_rest
        · intro x h_σ_x h_x_not_accum h_x_not_inits
          have h_x_not_body : x ∉ Block.initVars body := by
            intro hx
            apply h_x_not_inits
            rw [h_initvars_eq]
            exact List.mem_append_left _ hx
          have h_x_not_rest : x ∉ Block.initVars rest := by
            intro hx
            apply h_x_not_inits
            rw [h_initvars_eq]
            exact List.mem_append_right _ hx
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          have h_σ_body_x : σ_cfg_body x = none :=
            h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
          exact h_preserve_rest x h_σ_body_x h_nil_not h_x_not_rest
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
    have h_unique_rest : Block.uniqueInits rest := Block.uniqueInits.tail h_unique
    -- The combined-defs list is the same for `.typeDecl :: rest` and `rest`
    -- (since Stmt.initVars (.typeDecl ..) = []).
    have h_eq_combined :
        Cmds.definedVars accum.reverse ++ Block.initVars rest =
        Cmds.definedVars accum.reverse ++ Block.initVars (.typeDecl tc md :: rest) := by
      simp [Block.initVars, Stmt.initVars]
    have h_fresh_combined' :
        ∀ x ∈ Cmds.definedVars accum.reverse ++ Block.initVars rest,
        σ_base x = none := by
      intro x hx
      rw [h_eq_combined] at hx
      exact h_fresh_combined x hx
    have h_unique_combined' :
        (Cmds.definedVars accum.reverse ++ Block.initVars rest).Nodup := by
      rw [h_eq_combined]
      exact h_unique_combined
    have ⟨σ_cfg, h_step, h_agree, h_preserve⟩ :=
      stmtsToBlocks_simulation extendEval k rest exitConts accum gen gen'
        entry blocks h_gen h_nofd_rest h_unique_rest σ_struct_base σ_base hf_base hf_accum
        ρ₀ ρ' hwfb hwfv hwf_def hwf_congr h_rest_star h_accum h_agree_entry
        h_fresh_combined' h_unique_combined' h_hf cfg h_cfg_blocks h_cfg_nodup
    refine ⟨σ_cfg, h_step, h_agree, ?_⟩
    intro x h_σ_x h_x_not_accum h_x_not_inits
    have h_x_not_rest : x ∉ Block.initVars rest := by
      intro hx
      apply h_x_not_inits
      simp [Block.initVars, Stmt.initVars]; exact hx
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
    (extendEval : ExtendEval P)
    (k : String) (ss : List (Stmt P (Cmd P)))
    (exitConts : List (Option String × String))
    (accum : List (Cmd P))
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : (stmtsToBlocks k ss exitConts accum gen) = ((entry, blocks), gen'))
    (h_nofd : Block.noFuncDecl ss = true)
    (h_unique : Block.uniqueInits ss)
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
    (h_exit : StepStmtStar P (EvalCmd P) extendEval
      (.stmts ss ρ₀) (.exiting label ρ'))
    (h_accum : EvalCmds P (EvalCmd P) ρ₀.eval σ_struct_base accum.reverse ρ₀.store hf_accum)
    (h_agree_entry : StoreAgreement σ_struct_base σ_base)
    (h_fresh_combined :
      ∀ x ∈ Cmds.definedVars accum.reverse ++ Block.initVars ss, σ_base x = none)
    (h_unique_combined :
      (Cmds.definedVars accum.reverse ++ Block.initVars ss).Nodup)
    (h_hf : ρ₀.hasFailure = (hf_base || hf_accum))
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (h_cfg_blocks : ∀ b ∈ blocks, b ∈ cfg.blocks)
    (h_cfg_nodup : (cfg.blocks.map Prod.fst).Nodup) :
    ∃ σ_cfg, StepDetCFGStar extendEval cfg
      (.cont entry σ_base hf_base)
      (.cont bk_target σ_cfg ρ'.hasFailure)
      ∧ StoreAgreement ρ'.store σ_cfg
      ∧ (∀ x, σ_base x = none →
          x ∉ Cmds.definedVars accum.reverse → x ∉ Block.initVars ss →
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
          cases h_seq_inv with
          | inl h_inner_exit =>
            -- Inner is `.stmt (.cmd c) ρ₀` which can only terminate; cannot exit.
            exfalso
            cases h_inner_exit with
            | step _ _ _ hstep2 hrest2 =>
              cases hstep2 with
              | step_cmd _ =>
                cases hrest2 with
                | step _ _ _ h _ => cases h
          | inr h_term_exit =>
            obtain ⟨ρ_mid, h_inner_term, h_rest_exit⟩ := h_term_exit
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
    have hwfb' : WellFormedSemanticEvalBool ρ₁.eval := by rw [heval_eq_c]; exact hwfb
    have hwfv' : WellFormedSemanticEvalVal ρ₁.eval := by rw [heval_eq_c]; exact hwfv
    have hwf_def' : WellFormedSemanticEvalDef ρ₁.eval := by rw [heval_eq_c]; exact hwf_def
    have hwf_congr' : WellFormedSemanticEvalExprCongr ρ₁.eval := by
      rw [heval_eq_c]; exact hwf_congr
    have h_nofd_rest : Block.noFuncDecl rest = true := by
      simp [Block.noFuncDecl] at h_nofd; exact h_nofd.2
    have h_unique_rest : Block.uniqueInits rest := Block.uniqueInits.tail h_unique
    have h_definedVars_snoc :
        Cmds.definedVars (accum.reverse ++ [c]) =
        Cmds.definedVars accum.reverse ++ Cmd.definedVars c := by
      induction accum.reverse with
      | nil => simp [Cmds.definedVars]
      | cons hd tl ih =>
        rw [List.cons_append, Cmds.definedVars_cons, Cmds.definedVars_cons,
            ih, List.append_assoc]
    have h_eq_combined :
        Cmds.definedVars (c :: accum).reverse ++ Block.initVars rest =
        Cmds.definedVars accum.reverse ++ Block.initVars (.cmd c :: rest) := by
      rw [List.reverse_cons, h_definedVars_snoc]
      rw [Block.initVars]
      cases c <;> simp [Stmt.initVars, Cmd.definedVars, List.append_assoc]
    have h_fresh_combined' :
        ∀ x ∈ Cmds.definedVars (c :: accum).reverse ++ Block.initVars rest,
        σ_base x = none := by
      intro x hx
      rw [h_eq_combined] at hx
      exact h_fresh_combined x hx
    have h_unique_combined' :
        (Cmds.definedVars (c :: accum).reverse ++ Block.initVars rest).Nodup := by
      rw [h_eq_combined]
      exact h_unique_combined
    have ⟨σ_cfg, h_step, h_agree, h_preserve⟩ :=
      stmtsToBlocks_simulation_to_cont extendEval k rest exitConts (c :: accum) gen gen'
        entry blocks h_gen h_nofd_rest h_unique_rest
        σ_struct_base σ_base hf_base (hf_accum || failed_c)
        ρ₁ ρ' label bk_target h_label hwfb' hwfv' hwf_def' hwf_congr' h_rest_exit h_accum'
        h_agree_entry h_fresh_combined' h_unique_combined' h_hf'
        cfg h_cfg_blocks h_cfg_nodup
    refine ⟨σ_cfg, h_step, h_agree, ?_⟩
    intro x h_σ_x h_x_not_accum h_x_not_inits
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
          simp [Block.initVars, Stmt.initVars]
        | _ => simp [Cmd.definedVars] at h
    have h_x_not_rest : x ∉ Block.initVars rest := by
      intro h
      apply h_x_not_inits
      rw [Block.initVars]
      cases c <;> simp [Stmt.initVars] <;> first | right; exact h | exact h
    exact h_preserve x h_σ_x h_x_not_new_accum h_x_not_rest
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
          cases h_seq_inv with
          | inl h_inner_exit =>
            -- inner is .stmt (.typeDecl ..) ρ₀; cannot exit.
            exfalso
            cases h_inner_exit with
            | step _ _ _ hstep2 hrest2 =>
              cases hstep2 with
              | step_typeDecl =>
                cases hrest2 with
                | step _ _ _ h _ => cases h
          | inr h_term_exit =>
            obtain ⟨ρ_mid, h_inner_term, h_rest_exit⟩ := h_term_exit
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
    have h_unique_rest : Block.uniqueInits rest := Block.uniqueInits.tail h_unique
    have h_eq_combined :
        Cmds.definedVars accum.reverse ++ Block.initVars rest =
        Cmds.definedVars accum.reverse ++ Block.initVars (.typeDecl tc md :: rest) := by
      simp [Block.initVars, Stmt.initVars]
    have h_fresh_combined' :
        ∀ x ∈ Cmds.definedVars accum.reverse ++ Block.initVars rest,
        σ_base x = none := by
      intro x hx
      rw [h_eq_combined] at hx
      exact h_fresh_combined x hx
    have h_unique_combined' :
        (Cmds.definedVars accum.reverse ++ Block.initVars rest).Nodup := by
      rw [h_eq_combined]
      exact h_unique_combined
    have ⟨σ_cfg, h_step, h_agree, h_preserve⟩ :=
      stmtsToBlocks_simulation_to_cont extendEval k rest exitConts accum gen gen'
        entry blocks h_gen h_nofd_rest h_unique_rest σ_struct_base σ_base hf_base hf_accum
        ρ₀ ρ' label bk_target h_label hwfb hwfv hwf_def hwf_congr h_rest_exit h_accum h_agree_entry
        h_fresh_combined' h_unique_combined' h_hf cfg h_cfg_blocks h_cfg_nodup
    refine ⟨σ_cfg, h_step, h_agree, ?_⟩
    intro x h_σ_x h_x_not_accum h_x_not_inits
    have h_x_not_rest : x ∉ Block.initVars rest := by
      intro hx
      apply h_x_not_inits
      simp [Block.initVars, Stmt.initVars]; exact hx
    exact h_preserve x h_σ_x h_x_not_accum h_x_not_rest
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
          cases h_seq_inv with
          | inl h_inner_exit =>
            cases h_inner_exit with
            | step _ _ _ hstep2 hrest2 =>
              cases hstep2 with
              | step_exit =>
                cases hrest2 with
                | refl => exact ⟨rfl, rfl⟩
                | step _ _ _ h _ => cases h
          | inr h_term =>
            obtain ⟨ρ_mid, h_inner_term, _⟩ := h_term
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
    intro x h_σ_x h_x_not_accum _
    exact h_preserve x h_σ_x h_x_not_accum
  | .block label' body md :: rest =>
    unfold stmtsToBlocks at h_gen
    simp only [bind, StateT.bind, pure, StateT.pure] at h_gen
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
          cases h_seq_inv with
          | inl h_inner_exit =>
            -- inner = .stmt (.block ..) ρ₀ → .exiting label ρ'
            cases h_inner_exit with
            | step _ _ _ hstep2 hrest2 =>
              cases hstep2 with
              | step_block =>
                -- hrest2 : .block (.some label') ρ₀.store (.stmts body ρ₀) → .exiting label ρ'
                have ⟨h_ne, ρ_inner, h_body_exit, h_eq⟩ :=
                  block_some_reaches_exiting hrest2
                exact Or.inl ⟨h_ne, ρ_inner, h_body_exit, h_eq⟩
          | inr h_term_exit =>
            obtain ⟨ρ_blk, h_inner_term, h_rest_exit⟩ := h_term_exit
            cases h_inner_term with
            | step _ _ _ hstep2 hrest2 =>
              cases hstep2 with
              | step_block =>
                -- hrest2 : .block (.some label') ρ₀.store (.stmts body ρ₀) → .terminal ρ_blk
                have h_blk_inv := block_some_reaches_terminal P (EvalCmd P) extendEval hrest2
                cases h_blk_inv with
                | inl h_term =>
                  obtain ⟨ρ_i, h_body_term, heq⟩ := h_term
                  exact Or.inr ⟨ρ_blk, Or.inl ⟨ρ_i, h_body_term, heq⟩, h_rest_exit⟩
                | inr h_match =>
                  obtain ⟨ρ_i, h_body_match, heq⟩ := h_match
                  exact Or.inr ⟨ρ_blk, Or.inr ⟨ρ_i, h_body_match, heq⟩, h_rest_exit⟩
    -- noFuncDecl projections.
    have h_nofd_body : Block.noFuncDecl body = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.1
    have h_nofd_rest : Block.noFuncDecl rest = true := by
      simp [Block.noFuncDecl, Stmt.noFuncDecl] at h_nofd; exact h_nofd.2
    have h_unique_body : Block.uniqueInits body :=
      Block.uniqueInits.block_body h_unique
    have h_unique_rest : Block.uniqueInits rest := Block.uniqueInits.tail h_unique
    have h_initvars_eq :
        Block.initVars (Stmt.block label' body md :: rest) =
        Block.initVars body ++ Block.initVars rest := by
      rw [Block.initVars]
      simp [Stmt.initVars]
    -- Block membership distribution. Split on l = bl vs l ≠ bl.
    by_cases h_l_eq_bl : label' = bl
    · -- Case label' = bl: blocks = accumBlocks ++ bbs ++ bsNext, entry = accumEntry.
      simp [h_l_eq_bl] at h_gen
      have h_entry_eq : accumEntry = entry :=
        (Prod.mk.inj (Prod.mk.inj h_gen).1).1
      have h_blocks_eq : accumBlocks ++ (bbs ++ bsNext) = blocks :=
        (Prod.mk.inj (Prod.mk.inj h_gen).1).2
      subst h_entry_eq
      subst h_blocks_eq
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
      cases h_decomp with
      | inl h_caseA =>
        -- (A) Body exits with `label`, label' ≠ label.  Use _to_cont on body.
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
        have h_fresh_body_inits_after : ∀ x ∈ Block.initVars body, σ_cfg_after x = none := by
          intro x hx
          have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
            intro h_in_accum
            have h_disj_lr := List.nodup_append.mp h_unique_combined
            rw [h_initvars_eq] at h_disj_lr
            have h_disj := h_disj_lr.2.2
            exact h_disj x h_in_accum x (List.mem_append_left _ hx) rfl
          have h_σ_base_x : σ_base x = none := by
            apply h_fresh_combined
            apply List.mem_append_right
            rw [h_initvars_eq]
            exact List.mem_append_left _ hx
          exact h_preserve_flush x h_σ_base_x h_x_not_accum
        have h_combined_body :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
            σ_cfg_after x = none := by
          intro x hx
          simp [Cmds.definedVars] at hx
          exact h_fresh_body_inits_after x hx
        have h_unique_combined_body :
            (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
          simp [Cmds.definedVars]
          unfold Block.uniqueInits at h_unique_body
          exact h_unique_body
        have h_accum_nil : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have h_hf_body : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
        -- Recurse on body with _to_cont (target = bk_target).
        have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
          stmtsToBlocks_simulation_to_cont extendEval kNext body
            ((some label', kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
            h_nofd_body h_unique_body
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ_inner label bk_target h_label_lookup hwfb hwfv hwf_def hwf_congr
            h_body_exit h_accum_nil h_agree_after
            h_combined_body h_unique_combined_body h_hf_body cfg h_cfg_bbs h_cfg_nodup
        -- Bridge structured-side projection to CFG.
        have h_agree_proj : StoreAgreement (projectStore ρ₀.store ρ_inner.store) ρ_inner.store :=
          StoreAgreement.of_projectStore _ _
        have h_agree_ρ' : StoreAgreement ρ'.store σ_cfg_body := by
          rw [h_ρ'_eq]
          exact StoreAgreement.trans h_agree_proj h_agree_body
        refine ⟨σ_cfg_body, ?_, h_agree_ρ', ?_⟩
        · -- Compose: entry → bl (flush) → bk_target (body via _to_cont).
          -- Need to align ρ'.hasFailure with ρ_inner.hasFailure (both = ρ₀.hasFailure since
          -- block step preserves hasFailure via projectStore which only affects store).
          have h_hasFail_ρ' : ρ'.hasFailure = ρ_inner.hasFailure := by
            rw [h_ρ'_eq]
          have h_step_body' : StepDetCFGStar extendEval cfg
              (.cont bl σ_cfg_after ρ₀.hasFailure)
              (.cont bk_target σ_cfg_body ρ'.hasFailure) := by
            rw [h_hasFail_ρ']; exact h_step_body
          exact StepDetCFGStar_trans h_step_flush h_step_body'
        · intro x h_σ_x h_x_not_accum h_x_not_inits
          have h_x_not_body : x ∉ Block.initVars body := by
            intro hx
            apply h_x_not_inits
            rw [h_initvars_eq]
            exact List.mem_append_left _ hx
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          exact h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
      | inr h_caseB =>
        -- (B) Block terminates with ρ_blk, then rest exits.
        obtain ⟨ρ_blk, h_body_or_match, h_rest_exit⟩ := h_caseB
        -- Freshness for body recursion at σ_cfg_after.
        have h_fresh_body_inits_after : ∀ x ∈ Block.initVars body, σ_cfg_after x = none := by
          intro x hx
          have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
            intro h_in_accum
            have h_disj_lr := List.nodup_append.mp h_unique_combined
            rw [h_initvars_eq] at h_disj_lr
            have h_disj := h_disj_lr.2.2
            exact h_disj x h_in_accum x (List.mem_append_left _ hx) rfl
          have h_σ_base_x : σ_base x = none := by
            apply h_fresh_combined
            apply List.mem_append_right
            rw [h_initvars_eq]
            exact List.mem_append_left _ hx
          exact h_preserve_flush x h_σ_base_x h_x_not_accum
        have h_combined_body :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
            σ_cfg_after x = none := by
          intro x hx
          simp [Cmds.definedVars] at hx
          exact h_fresh_body_inits_after x hx
        have h_unique_combined_body :
            (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
          simp [Cmds.definedVars]
          unfold Block.uniqueInits at h_unique_body
          exact h_unique_body
        have h_accum_nil : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have h_hf_body : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
        have h_label_lookup :
            ((some label', kNext) :: exitConts).lookup (some label') = some kNext := by
          simp [List.lookup]
        -- Run body to σ_cfg_body via either _simulation (terminate) or _to_cont (match exit).
        -- Use a manual case-split to avoid binding ρ_inner with elaboration ambiguity.
        cases h_body_or_match with
        | inl h_term =>
          obtain ⟨ρ_inner, h_body_term, h_ρ_blk_eq⟩ := h_term
          have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
            stmtsToBlocks_simulation extendEval kNext body
              ((some label', kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
              h_nofd_body h_unique_body
              ρ₀.store σ_cfg_after ρ₀.hasFailure false
              ρ₀ ρ_inner hwfb hwfv hwf_def hwf_congr h_body_term h_accum_nil h_agree_after
              h_combined_body h_unique_combined_body h_hf_body cfg h_cfg_bbs h_cfg_nodup
          have h_agree_proj : StoreAgreement (projectStore ρ₀.store ρ_inner.store) ρ_inner.store :=
            StoreAgreement.of_projectStore _ _
          have h_agree_block_body : StoreAgreement ρ_blk.store σ_cfg_body := by
            rw [h_ρ_blk_eq]
            exact StoreAgreement.trans h_agree_proj h_agree_body
          have h_eval_eq : ρ_inner.eval = ρ₀.eval :=
            smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
              body ρ₀ ρ_inner h_nofd_body h_body_term
          have hwfb₁ : WellFormedSemanticEvalBool ρ_blk.eval := by
            rw [h_ρ_blk_eq]; show WellFormedSemanticEvalBool ρ_inner.eval
            rw [h_eval_eq]; exact hwfb
          have hwfv₁ : WellFormedSemanticEvalVal ρ_blk.eval := by
            rw [h_ρ_blk_eq]; show WellFormedSemanticEvalVal ρ_inner.eval
            rw [h_eval_eq]; exact hwfv
          have hwf_def₁ : WellFormedSemanticEvalDef ρ_blk.eval := by
            rw [h_ρ_blk_eq]; show WellFormedSemanticEvalDef ρ_inner.eval
            rw [h_eval_eq]; exact hwf_def
          have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_blk.eval := by
            rw [h_ρ_blk_eq]; show WellFormedSemanticEvalExprCongr ρ_inner.eval
            rw [h_eval_eq]; exact hwf_congr
          have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none := by
            intro x hx
            have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
              intro h_in_accum
              have h_disj_lr := List.nodup_append.mp h_unique_combined
              rw [h_initvars_eq] at h_disj_lr
              have h_disj := h_disj_lr.2.2
              exact h_disj x h_in_accum x
                (List.mem_append_right _ hx) rfl
            have h_σ_base_x : σ_base x = none := by
              apply h_fresh_combined
              apply List.mem_append_right
              rw [h_initvars_eq]
              exact List.mem_append_right _ hx
            exact h_preserve_flush x h_σ_base_x h_x_not_accum
          have h_fresh_rest_inits_body : ∀ x ∈ Block.initVars rest, σ_cfg_body x = none := by
            intro x hx
            have h_x_not_body : x ∉ Block.initVars body := by
              intro h_in_body
              unfold Block.uniqueInits at h_unique
              rw [h_initvars_eq] at h_unique
              have h_disj_lr := (List.nodup_append.mp h_unique).2.2
              exact h_disj_lr x h_in_body x hx rfl
            have h_σ_after_x : σ_cfg_after x = none := h_fresh_rest_inits_after x hx
            have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
            exact h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
          have h_combined_rest :
              ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
              σ_cfg_body x = none := by
            intro x hx
            simp [Cmds.definedVars] at hx
            exact h_fresh_rest_inits_body x hx
          have h_unique_combined_rest :
              (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
            simp [Cmds.definedVars]
            unfold Block.uniqueInits at h_unique_rest
            exact h_unique_rest
          have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_blk.eval ρ_blk.store
              [].reverse ρ_blk.store false := EvalCmds.eval_cmds_none
          have h_hf_r : ρ_blk.hasFailure = (ρ_blk.hasFailure || false) := by simp
          have h_hasFail_blk : ρ_blk.hasFailure = ρ_inner.hasFailure := by
            rw [h_ρ_blk_eq]
          have ⟨σ_cfg_rest, h_step_rest, h_agree_rest, h_preserve_rest⟩ :=
            stmtsToBlocks_simulation_to_cont extendEval k rest exitConts [] gen gen_r kNext bsNext
              h_rest_eq h_nofd_rest h_unique_rest ρ_blk.store σ_cfg_body
              ρ_blk.hasFailure false ρ_blk ρ' label bk_target h_label
              hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁
              h_rest_exit h_accum_nil_r h_agree_block_body
              h_combined_rest h_unique_combined_rest h_hf_r cfg h_cfg_rest h_cfg_nodup
          refine ⟨σ_cfg_rest, ?_, h_agree_rest, ?_⟩
          · have h_step_body' : StepDetCFGStar extendEval cfg
                (.cont bl σ_cfg_after ρ₀.hasFailure)
                (.cont kNext σ_cfg_body ρ_blk.hasFailure) := by
              rw [h_hasFail_blk]; exact h_step_body
            exact StepDetCFGStar_trans
              (StepDetCFGStar_trans h_step_flush h_step_body') h_step_rest
          · intro x h_σ_x h_x_not_accum h_x_not_inits
            have h_x_not_body : x ∉ Block.initVars body := by
              intro hx
              apply h_x_not_inits
              rw [h_initvars_eq]
              exact List.mem_append_left _ hx
            have h_x_not_rest : x ∉ Block.initVars rest := by
              intro hx
              apply h_x_not_inits
              rw [h_initvars_eq]
              exact List.mem_append_right _ hx
            have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
            have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
            have h_σ_body_x : σ_cfg_body x = none :=
              h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
            exact h_preserve_rest x h_σ_body_x h_nil_not h_x_not_rest
        | inr h_match_branch =>
          obtain ⟨ρ_inner, h_body_match, h_ρ_blk_eq⟩ := h_match_branch
          have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
            stmtsToBlocks_simulation_to_cont extendEval kNext body
              ((some label', kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
              h_nofd_body h_unique_body
              ρ₀.store σ_cfg_after ρ₀.hasFailure false
              ρ₀ ρ_inner label' kNext h_label_lookup hwfb hwfv hwf_def hwf_congr
              h_body_match h_accum_nil h_agree_after
              h_combined_body h_unique_combined_body h_hf_body cfg h_cfg_bbs h_cfg_nodup
          have h_agree_proj : StoreAgreement (projectStore ρ₀.store ρ_inner.store) ρ_inner.store :=
            StoreAgreement.of_projectStore _ _
          have h_agree_block_body : StoreAgreement ρ_blk.store σ_cfg_body := by
            rw [h_ρ_blk_eq]
            exact StoreAgreement.trans h_agree_proj h_agree_body
          have h_eval_eq : ρ_inner.eval = ρ₀.eval :=
            smallStep_noFuncDecl_preserves_eval_block_exiting P (EvalCmd P) extendEval
              body ρ₀ ρ_inner label' h_nofd_body h_body_match
          have hwfb₁ : WellFormedSemanticEvalBool ρ_blk.eval := by
            rw [h_ρ_blk_eq]; show WellFormedSemanticEvalBool ρ_inner.eval
            rw [h_eval_eq]; exact hwfb
          have hwfv₁ : WellFormedSemanticEvalVal ρ_blk.eval := by
            rw [h_ρ_blk_eq]; show WellFormedSemanticEvalVal ρ_inner.eval
            rw [h_eval_eq]; exact hwfv
          have hwf_def₁ : WellFormedSemanticEvalDef ρ_blk.eval := by
            rw [h_ρ_blk_eq]; show WellFormedSemanticEvalDef ρ_inner.eval
            rw [h_eval_eq]; exact hwf_def
          have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_blk.eval := by
            rw [h_ρ_blk_eq]; show WellFormedSemanticEvalExprCongr ρ_inner.eval
            rw [h_eval_eq]; exact hwf_congr
          have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none := by
            intro x hx
            have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
              intro h_in_accum
              have h_disj_lr := List.nodup_append.mp h_unique_combined
              rw [h_initvars_eq] at h_disj_lr
              have h_disj := h_disj_lr.2.2
              exact h_disj x h_in_accum x
                (List.mem_append_right _ hx) rfl
            have h_σ_base_x : σ_base x = none := by
              apply h_fresh_combined
              apply List.mem_append_right
              rw [h_initvars_eq]
              exact List.mem_append_right _ hx
            exact h_preserve_flush x h_σ_base_x h_x_not_accum
          have h_fresh_rest_inits_body : ∀ x ∈ Block.initVars rest, σ_cfg_body x = none := by
            intro x hx
            have h_x_not_body : x ∉ Block.initVars body := by
              intro h_in_body
              unfold Block.uniqueInits at h_unique
              rw [h_initvars_eq] at h_unique
              have h_disj_lr := (List.nodup_append.mp h_unique).2.2
              exact h_disj_lr x h_in_body x hx rfl
            have h_σ_after_x : σ_cfg_after x = none := h_fresh_rest_inits_after x hx
            have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
            exact h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
          have h_combined_rest :
              ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
              σ_cfg_body x = none := by
            intro x hx
            simp [Cmds.definedVars] at hx
            exact h_fresh_rest_inits_body x hx
          have h_unique_combined_rest :
              (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
            simp [Cmds.definedVars]
            unfold Block.uniqueInits at h_unique_rest
            exact h_unique_rest
          have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_blk.eval ρ_blk.store
              [].reverse ρ_blk.store false := EvalCmds.eval_cmds_none
          have h_hf_r : ρ_blk.hasFailure = (ρ_blk.hasFailure || false) := by simp
          have h_hasFail_blk : ρ_blk.hasFailure = ρ_inner.hasFailure := by
            rw [h_ρ_blk_eq]
          have ⟨σ_cfg_rest, h_step_rest, h_agree_rest, h_preserve_rest⟩ :=
            stmtsToBlocks_simulation_to_cont extendEval k rest exitConts [] gen gen_r kNext bsNext
              h_rest_eq h_nofd_rest h_unique_rest ρ_blk.store σ_cfg_body
              ρ_blk.hasFailure false ρ_blk ρ' label bk_target h_label
              hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁
              h_rest_exit h_accum_nil_r h_agree_block_body
              h_combined_rest h_unique_combined_rest h_hf_r cfg h_cfg_rest h_cfg_nodup
          refine ⟨σ_cfg_rest, ?_, h_agree_rest, ?_⟩
          · have h_step_body' : StepDetCFGStar extendEval cfg
                (.cont bl σ_cfg_after ρ₀.hasFailure)
                (.cont kNext σ_cfg_body ρ_blk.hasFailure) := by
              rw [h_hasFail_blk]; exact h_step_body
            exact StepDetCFGStar_trans
              (StepDetCFGStar_trans h_step_flush h_step_body') h_step_rest
          · intro x h_σ_x h_x_not_accum h_x_not_inits
            have h_x_not_body : x ∉ Block.initVars body := by
              intro hx
              apply h_x_not_inits
              rw [h_initvars_eq]
              exact List.mem_append_left _ hx
            have h_x_not_rest : x ∉ Block.initVars rest := by
              intro hx
              apply h_x_not_inits
              rw [h_initvars_eq]
              exact List.mem_append_right _ hx
            have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
            have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
            have h_σ_body_x : σ_cfg_body x = none :=
              h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
            exact h_preserve_rest x h_σ_body_x h_nil_not h_x_not_rest
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
      subst h_entry_eq
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
      cases h_decomp with
      | inl h_caseA =>
        obtain ⟨h_label_ne, ρ_inner, h_body_exit, h_ρ'_eq⟩ := h_caseA
        have h_label_lookup :
            ((some label', kNext) :: exitConts).lookup (some label) = some bk_target := by
          show (match label == label' with
                | true => some kNext
                | false => List.lookup (some label) exitConts) = some bk_target
          have h_beq : (label == label') = false := by
            rw [beq_eq_false_iff_ne]; intro h; exact h_label_ne h.symm
          rw [h_beq]; exact h_label
        have h_fresh_body_inits_after : ∀ x ∈ Block.initVars body, σ_cfg_after x = none := by
          intro x hx
          have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
            intro h_in_accum
            have h_disj_lr := List.nodup_append.mp h_unique_combined
            rw [h_initvars_eq] at h_disj_lr
            have h_disj := h_disj_lr.2.2
            exact h_disj x h_in_accum x (List.mem_append_left _ hx) rfl
          have h_σ_base_x : σ_base x = none := by
            apply h_fresh_combined
            apply List.mem_append_right
            rw [h_initvars_eq]
            exact List.mem_append_left _ hx
          exact h_preserve_flush x h_σ_base_x h_x_not_accum
        have h_combined_body :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
            σ_cfg_after x = none := by
          intro x hx
          simp [Cmds.definedVars] at hx
          exact h_fresh_body_inits_after x hx
        have h_unique_combined_body :
            (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
          simp [Cmds.definedVars]
          unfold Block.uniqueInits at h_unique_body
          exact h_unique_body
        have h_accum_nil : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have h_hf_body : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
        have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
          stmtsToBlocks_simulation_to_cont extendEval kNext body
            ((some label', kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
            h_nofd_body h_unique_body
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ_inner label bk_target h_label_lookup hwfb hwfv hwf_def hwf_congr
            h_body_exit h_accum_nil h_agree_after
            h_combined_body h_unique_combined_body h_hf_body cfg h_cfg_bbs h_cfg_nodup
        have h_agree_proj : StoreAgreement (projectStore ρ₀.store ρ_inner.store) ρ_inner.store :=
          StoreAgreement.of_projectStore _ _
        have h_agree_ρ' : StoreAgreement ρ'.store σ_cfg_body := by
          rw [h_ρ'_eq]
          exact StoreAgreement.trans h_agree_proj h_agree_body
        refine ⟨σ_cfg_body, ?_, h_agree_ρ', ?_⟩
        · have h_hasFail_ρ' : ρ'.hasFailure = ρ_inner.hasFailure := by
            rw [h_ρ'_eq]
          have h_step_body' : StepDetCFGStar extendEval cfg
              (.cont bl σ_cfg_after ρ₀.hasFailure)
              (.cont bk_target σ_cfg_body ρ'.hasFailure) := by
            rw [h_hasFail_ρ']; exact h_step_body
          exact StepDetCFGStar_trans h_step_flush h_step_body'
        · intro x h_σ_x h_x_not_accum h_x_not_inits
          have h_x_not_body : x ∉ Block.initVars body := by
            intro hx
            apply h_x_not_inits
            rw [h_initvars_eq]
            exact List.mem_append_left _ hx
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          exact h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
      | inr h_caseB =>
        obtain ⟨ρ_blk, h_body_or_match, h_rest_exit⟩ := h_caseB
        have h_fresh_body_inits_after : ∀ x ∈ Block.initVars body, σ_cfg_after x = none := by
          intro x hx
          have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
            intro h_in_accum
            have h_disj_lr := List.nodup_append.mp h_unique_combined
            rw [h_initvars_eq] at h_disj_lr
            have h_disj := h_disj_lr.2.2
            exact h_disj x h_in_accum x (List.mem_append_left _ hx) rfl
          have h_σ_base_x : σ_base x = none := by
            apply h_fresh_combined
            apply List.mem_append_right
            rw [h_initvars_eq]
            exact List.mem_append_left _ hx
          exact h_preserve_flush x h_σ_base_x h_x_not_accum
        have h_combined_body :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars body,
            σ_cfg_after x = none := by
          intro x hx
          simp [Cmds.definedVars] at hx
          exact h_fresh_body_inits_after x hx
        have h_unique_combined_body :
            (Cmds.definedVars [].reverse ++ Block.initVars body).Nodup := by
          simp [Cmds.definedVars]
          unfold Block.uniqueInits at h_unique_body
          exact h_unique_body
        have h_accum_nil : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have h_hf_body : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
        have h_label_lookup :
            ((some label', kNext) :: exitConts).lookup (some label') = some kNext := by
          simp [List.lookup]
        cases h_body_or_match with
        | inl h_term =>
          obtain ⟨ρ_inner, h_body_term, h_ρ_blk_eq⟩ := h_term
          have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
            stmtsToBlocks_simulation extendEval kNext body
              ((some label', kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
              h_nofd_body h_unique_body
              ρ₀.store σ_cfg_after ρ₀.hasFailure false
              ρ₀ ρ_inner hwfb hwfv hwf_def hwf_congr h_body_term h_accum_nil h_agree_after
              h_combined_body h_unique_combined_body h_hf_body cfg h_cfg_bbs h_cfg_nodup
          have h_agree_proj : StoreAgreement (projectStore ρ₀.store ρ_inner.store) ρ_inner.store :=
            StoreAgreement.of_projectStore _ _
          have h_agree_block_body : StoreAgreement ρ_blk.store σ_cfg_body := by
            rw [h_ρ_blk_eq]
            exact StoreAgreement.trans h_agree_proj h_agree_body
          have h_eval_eq : ρ_inner.eval = ρ₀.eval :=
            smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
              body ρ₀ ρ_inner h_nofd_body h_body_term
          have hwfb₁ : WellFormedSemanticEvalBool ρ_blk.eval := by
            rw [h_ρ_blk_eq]; show WellFormedSemanticEvalBool ρ_inner.eval
            rw [h_eval_eq]; exact hwfb
          have hwfv₁ : WellFormedSemanticEvalVal ρ_blk.eval := by
            rw [h_ρ_blk_eq]; show WellFormedSemanticEvalVal ρ_inner.eval
            rw [h_eval_eq]; exact hwfv
          have hwf_def₁ : WellFormedSemanticEvalDef ρ_blk.eval := by
            rw [h_ρ_blk_eq]; show WellFormedSemanticEvalDef ρ_inner.eval
            rw [h_eval_eq]; exact hwf_def
          have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_blk.eval := by
            rw [h_ρ_blk_eq]; show WellFormedSemanticEvalExprCongr ρ_inner.eval
            rw [h_eval_eq]; exact hwf_congr
          have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none := by
            intro x hx
            have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
              intro h_in_accum
              have h_disj_lr := List.nodup_append.mp h_unique_combined
              rw [h_initvars_eq] at h_disj_lr
              have h_disj := h_disj_lr.2.2
              exact h_disj x h_in_accum x
                (List.mem_append_right _ hx) rfl
            have h_σ_base_x : σ_base x = none := by
              apply h_fresh_combined
              apply List.mem_append_right
              rw [h_initvars_eq]
              exact List.mem_append_right _ hx
            exact h_preserve_flush x h_σ_base_x h_x_not_accum
          have h_fresh_rest_inits_body : ∀ x ∈ Block.initVars rest, σ_cfg_body x = none := by
            intro x hx
            have h_x_not_body : x ∉ Block.initVars body := by
              intro h_in_body
              unfold Block.uniqueInits at h_unique
              rw [h_initvars_eq] at h_unique
              have h_disj_lr := (List.nodup_append.mp h_unique).2.2
              exact h_disj_lr x h_in_body x hx rfl
            have h_σ_after_x : σ_cfg_after x = none := h_fresh_rest_inits_after x hx
            have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
            exact h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
          have h_combined_rest :
              ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
              σ_cfg_body x = none := by
            intro x hx
            simp [Cmds.definedVars] at hx
            exact h_fresh_rest_inits_body x hx
          have h_unique_combined_rest :
              (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
            simp [Cmds.definedVars]
            unfold Block.uniqueInits at h_unique_rest
            exact h_unique_rest
          have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_blk.eval ρ_blk.store
              [].reverse ρ_blk.store false := EvalCmds.eval_cmds_none
          have h_hf_r : ρ_blk.hasFailure = (ρ_blk.hasFailure || false) := by simp
          have h_hasFail_blk : ρ_blk.hasFailure = ρ_inner.hasFailure := by
            rw [h_ρ_blk_eq]
          have ⟨σ_cfg_rest, h_step_rest, h_agree_rest, h_preserve_rest⟩ :=
            stmtsToBlocks_simulation_to_cont extendEval k rest exitConts [] gen gen_r kNext bsNext
              h_rest_eq h_nofd_rest h_unique_rest ρ_blk.store σ_cfg_body
              ρ_blk.hasFailure false ρ_blk ρ' label bk_target h_label
              hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁
              h_rest_exit h_accum_nil_r h_agree_block_body
              h_combined_rest h_unique_combined_rest h_hf_r cfg h_cfg_rest h_cfg_nodup
          refine ⟨σ_cfg_rest, ?_, h_agree_rest, ?_⟩
          · have h_step_body' : StepDetCFGStar extendEval cfg
                (.cont bl σ_cfg_after ρ₀.hasFailure)
                (.cont kNext σ_cfg_body ρ_blk.hasFailure) := by
              rw [h_hasFail_blk]; exact h_step_body
            exact StepDetCFGStar_trans
              (StepDetCFGStar_trans h_step_flush h_step_body') h_step_rest
          · intro x h_σ_x h_x_not_accum h_x_not_inits
            have h_x_not_body : x ∉ Block.initVars body := by
              intro hx
              apply h_x_not_inits
              rw [h_initvars_eq]
              exact List.mem_append_left _ hx
            have h_x_not_rest : x ∉ Block.initVars rest := by
              intro hx
              apply h_x_not_inits
              rw [h_initvars_eq]
              exact List.mem_append_right _ hx
            have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
            have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
            have h_σ_body_x : σ_cfg_body x = none :=
              h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
            exact h_preserve_rest x h_σ_body_x h_nil_not h_x_not_rest
        | inr h_match_branch =>
          obtain ⟨ρ_inner, h_body_match, h_ρ_blk_eq⟩ := h_match_branch
          have ⟨σ_cfg_body, h_step_body, h_agree_body, h_preserve_body⟩ :=
            stmtsToBlocks_simulation_to_cont extendEval kNext body
              ((some label', kNext) :: exitConts) [] gen_r gen_b bl bbs h_body_eq
              h_nofd_body h_unique_body
              ρ₀.store σ_cfg_after ρ₀.hasFailure false
              ρ₀ ρ_inner label' kNext h_label_lookup hwfb hwfv hwf_def hwf_congr
              h_body_match h_accum_nil h_agree_after
              h_combined_body h_unique_combined_body h_hf_body cfg h_cfg_bbs h_cfg_nodup
          have h_agree_proj : StoreAgreement (projectStore ρ₀.store ρ_inner.store) ρ_inner.store :=
            StoreAgreement.of_projectStore _ _
          have h_agree_block_body : StoreAgreement ρ_blk.store σ_cfg_body := by
            rw [h_ρ_blk_eq]
            exact StoreAgreement.trans h_agree_proj h_agree_body
          have h_eval_eq : ρ_inner.eval = ρ₀.eval :=
            smallStep_noFuncDecl_preserves_eval_block_exiting P (EvalCmd P) extendEval
              body ρ₀ ρ_inner label' h_nofd_body h_body_match
          have hwfb₁ : WellFormedSemanticEvalBool ρ_blk.eval := by
            rw [h_ρ_blk_eq]; show WellFormedSemanticEvalBool ρ_inner.eval
            rw [h_eval_eq]; exact hwfb
          have hwfv₁ : WellFormedSemanticEvalVal ρ_blk.eval := by
            rw [h_ρ_blk_eq]; show WellFormedSemanticEvalVal ρ_inner.eval
            rw [h_eval_eq]; exact hwfv
          have hwf_def₁ : WellFormedSemanticEvalDef ρ_blk.eval := by
            rw [h_ρ_blk_eq]; show WellFormedSemanticEvalDef ρ_inner.eval
            rw [h_eval_eq]; exact hwf_def
          have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_blk.eval := by
            rw [h_ρ_blk_eq]; show WellFormedSemanticEvalExprCongr ρ_inner.eval
            rw [h_eval_eq]; exact hwf_congr
          have h_fresh_rest_inits_after : ∀ x ∈ Block.initVars rest, σ_cfg_after x = none := by
            intro x hx
            have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
              intro h_in_accum
              have h_disj_lr := List.nodup_append.mp h_unique_combined
              rw [h_initvars_eq] at h_disj_lr
              have h_disj := h_disj_lr.2.2
              exact h_disj x h_in_accum x
                (List.mem_append_right _ hx) rfl
            have h_σ_base_x : σ_base x = none := by
              apply h_fresh_combined
              apply List.mem_append_right
              rw [h_initvars_eq]
              exact List.mem_append_right _ hx
            exact h_preserve_flush x h_σ_base_x h_x_not_accum
          have h_fresh_rest_inits_body : ∀ x ∈ Block.initVars rest, σ_cfg_body x = none := by
            intro x hx
            have h_x_not_body : x ∉ Block.initVars body := by
              intro h_in_body
              unfold Block.uniqueInits at h_unique
              rw [h_initvars_eq] at h_unique
              have h_disj_lr := (List.nodup_append.mp h_unique).2.2
              exact h_disj_lr x h_in_body x hx rfl
            have h_σ_after_x : σ_cfg_after x = none := h_fresh_rest_inits_after x hx
            have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
            exact h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
          have h_combined_rest :
              ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
              σ_cfg_body x = none := by
            intro x hx
            simp [Cmds.definedVars] at hx
            exact h_fresh_rest_inits_body x hx
          have h_unique_combined_rest :
              (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
            simp [Cmds.definedVars]
            unfold Block.uniqueInits at h_unique_rest
            exact h_unique_rest
          have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_blk.eval ρ_blk.store
              [].reverse ρ_blk.store false := EvalCmds.eval_cmds_none
          have h_hf_r : ρ_blk.hasFailure = (ρ_blk.hasFailure || false) := by simp
          have h_hasFail_blk : ρ_blk.hasFailure = ρ_inner.hasFailure := by
            rw [h_ρ_blk_eq]
          have ⟨σ_cfg_rest, h_step_rest, h_agree_rest, h_preserve_rest⟩ :=
            stmtsToBlocks_simulation_to_cont extendEval k rest exitConts [] gen gen_r kNext bsNext
              h_rest_eq h_nofd_rest h_unique_rest ρ_blk.store σ_cfg_body
              ρ_blk.hasFailure false ρ_blk ρ' label bk_target h_label
              hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁
              h_rest_exit h_accum_nil_r h_agree_block_body
              h_combined_rest h_unique_combined_rest h_hf_r cfg h_cfg_rest h_cfg_nodup
          refine ⟨σ_cfg_rest, ?_, h_agree_rest, ?_⟩
          · have h_step_body' : StepDetCFGStar extendEval cfg
                (.cont bl σ_cfg_after ρ₀.hasFailure)
                (.cont kNext σ_cfg_body ρ_blk.hasFailure) := by
              rw [h_hasFail_blk]; exact h_step_body
            exact StepDetCFGStar_trans
              (StepDetCFGStar_trans h_step_flush h_step_body') h_step_rest
          · intro x h_σ_x h_x_not_accum h_x_not_inits
            have h_x_not_body : x ∉ Block.initVars body := by
              intro hx
              apply h_x_not_inits
              rw [h_initvars_eq]
              exact List.mem_append_left _ hx
            have h_x_not_rest : x ∉ Block.initVars rest := by
              intro hx
              apply h_x_not_inits
              rw [h_initvars_eq]
              exact List.mem_append_right _ hx
            have h_σ_after_x : σ_cfg_after x = none := h_preserve_flush x h_σ_x h_x_not_accum
            have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
            have h_σ_body_x : σ_cfg_body x = none :=
              h_preserve_body x h_σ_after_x h_nil_not h_x_not_body
            exact h_preserve_rest x h_σ_body_x h_nil_not h_x_not_rest
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
          cases h_seq_inv with
          | inl h_inner_exit =>
            -- inner = .stmt (.ite ..) ρ₀ → .exiting label ρ'
            cases h_inner_exit with
            | step _ _ _ hstep2 hrest2 =>
              cases hstep2 with
              | step_ite_true h_eval_tt _ =>
                exact Or.inl (Or.inl ⟨hrest2, h_eval_tt⟩)
              | step_ite_false h_eval_ff _ =>
                exact Or.inl (Or.inr ⟨hrest2, h_eval_ff⟩)
          | inr h_term_exit =>
            obtain ⟨ρ_mid_outer, h_inner_term, h_rest_exit⟩ := h_term_exit
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
      simp [Stmt.initVars]
    have h_unique_outer_inits :
        (Cmds.definedVars accum.reverse ++
          ((Block.initVars thenBranch ++ Block.initVars elseBranch) ++ Block.initVars rest)).Nodup := by
      rw [← h_initvars_eq]; exact h_unique_combined
    -- Freshness for sub-branch and rest recursions.
    have h_fresh_then_inits : ∀ x ∈ Block.initVars thenBranch, σ_cfg_after x = none := by
      intro x hx
      have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
        intro hx_acc
        have h_disj := List.nodup_append.mp h_unique_outer_inits
        have h_disj_lr := h_disj.2.2
        exact h_disj_lr x hx_acc x
          (List.mem_append_left _ (List.mem_append_left _ hx)) rfl
      have h_σ_x : σ_base x = none :=
        h_fresh_combined x (List.mem_append_right _
          (h_initvars_eq ▸ List.mem_append_left _ (List.mem_append_left _ hx)))
      exact h_preserve_after x h_σ_x h_x_not_accum
    have h_fresh_else_inits : ∀ x ∈ Block.initVars elseBranch, σ_cfg_after x = none := by
      intro x hx
      have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
        intro hx_acc
        have h_disj := List.nodup_append.mp h_unique_outer_inits
        have h_disj_lr := h_disj.2.2
        exact h_disj_lr x hx_acc x
          (List.mem_append_left _ (List.mem_append_right _ hx)) rfl
      have h_σ_x : σ_base x = none :=
        h_fresh_combined x (List.mem_append_right _
          (h_initvars_eq ▸ List.mem_append_left _ (List.mem_append_right _ hx)))
      exact h_preserve_after x h_σ_x h_x_not_accum
    have h_fresh_rest_inits_after :
        ∀ x ∈ Block.initVars rest, σ_cfg_after x = none := by
      intro x hx
      have h_x_not_accum : x ∉ Cmds.definedVars accum.reverse := by
        intro hx_acc
        have h_disj := List.nodup_append.mp h_unique_outer_inits
        have h_disj_lr := h_disj.2.2
        exact h_disj_lr x hx_acc x
          (List.mem_append_right _ hx) rfl
      have h_σ_x : σ_base x = none :=
        h_fresh_combined x (List.mem_append_right _
          (h_initvars_eq ▸ List.mem_append_right _ hx))
      exact h_preserve_after x h_σ_x h_x_not_accum
    have h_combined_then :
        ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars thenBranch,
        σ_cfg_after x = none := by
      intro x hx
      simp [Cmds.definedVars] at hx
      exact h_fresh_then_inits x hx
    have h_unique_combined_then :
        (Cmds.definedVars [].reverse ++ Block.initVars thenBranch).Nodup := by
      simp [Cmds.definedVars]
      have h1 : ((Block.initVars thenBranch ++ Block.initVars elseBranch) ++
                  Block.initVars rest).Nodup :=
        (List.nodup_append.mp h_unique_outer_inits).2.1
      have h2 : (Block.initVars thenBranch ++ Block.initVars elseBranch).Nodup :=
        (List.nodup_append.mp h1).1
      exact (List.nodup_append.mp h2).1
    have h_combined_else :
        ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars elseBranch,
        σ_cfg_after x = none := by
      intro x hx
      simp [Cmds.definedVars] at hx
      exact h_fresh_else_inits x hx
    have h_unique_combined_else :
        (Cmds.definedVars [].reverse ++ Block.initVars elseBranch).Nodup := by
      simp [Cmds.definedVars]
      have h1 : ((Block.initVars thenBranch ++ Block.initVars elseBranch) ++
                  Block.initVars rest).Nodup :=
        (List.nodup_append.mp h_unique_outer_inits).2.1
      have h2 : (Block.initVars thenBranch ++ Block.initVars elseBranch).Nodup :=
        (List.nodup_append.mp h1).1
      exact (List.nodup_append.mp h2).2.1
    have h_lookup : ∀ lbl blk, (lbl, blk) ∈ cfg.blocks →
        cfg.blocks.lookup lbl = some blk :=
      fun lbl blk h_mem => List.lookup_of_mem_nodup cfg.blocks h_cfg_nodup lbl blk h_mem
    cases h_decomp with
    | inl h_caseA =>
      -- Branch itself exits with `label`; rest does not run.
      cases h_caseA with
      | inl h_true =>
        obtain ⟨h_then_exit, h_cond_tt⟩ := h_true
        have h_flush_sim : StepDetCFGStar extendEval cfg
            (.cont accumEntry σ_base hf_base)
            (.cont tl σ_cfg_after ρ₀.hasFailure) :=
          flushCmds_condGoto_true_agree extendEval accum e tl fl md l_ite gen_e gen_f
            accumEntry accumBlocks h_flush_eq σ_base σ_cfg_after hf_base hf_accum ρ₀
            hwfb hwf_def hwf_congr h_accum_cfg h_agree_after h_hf h_cond_tt cfg
            h_cfg_accum h_lookup
        -- Recurse on thenBranch with _to_cont (target = bk_target).
        have h_accum_nil_t : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have h_hf_t : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
        have ⟨σ_cfg_branch, h_then_step, h_agree_branch, h_preserve_branch⟩ :=
          stmtsToBlocks_simulation_to_cont extendEval kNext thenBranch exitConts []
            gen_ite gen_t tl tbs h_then_eq h_nofd_then h_unique_then
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ' label bk_target h_label hwfb hwfv hwf_def hwf_congr
            h_then_exit h_accum_nil_t h_agree_after
            h_combined_then h_unique_combined_then h_hf_t cfg h_cfg_tbs h_cfg_nodup
        refine ⟨σ_cfg_branch, ?_, h_agree_branch, ?_⟩
        · exact StepDetCFGStar_trans h_flush_sim h_then_step
        · intro x h_σ_x h_x_not_accum h_x_not_inits
          have h_x_not_then : x ∉ Block.initVars thenBranch := by
            intro hx
            apply h_x_not_inits
            rw [h_initvars_eq]; exact List.mem_append_left _ (List.mem_append_left _ hx)
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_after x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          exact h_preserve_branch x h_σ_after_x h_nil_not h_x_not_then
      | inr h_false =>
        obtain ⟨h_else_exit, h_cond_ff⟩ := h_false
        have h_flush_sim : StepDetCFGStar extendEval cfg
            (.cont accumEntry σ_base hf_base)
            (.cont fl σ_cfg_after ρ₀.hasFailure) :=
          flushCmds_condGoto_false_agree extendEval accum e tl fl md l_ite gen_e gen_f
            accumEntry accumBlocks h_flush_eq σ_base σ_cfg_after hf_base hf_accum ρ₀
            hwfb hwf_def hwf_congr h_accum_cfg h_agree_after h_hf h_cond_ff cfg
            h_cfg_accum h_lookup
        have h_accum_nil_f : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have h_hf_f : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
        have ⟨σ_cfg_branch, h_else_step, h_agree_branch, h_preserve_branch⟩ :=
          stmtsToBlocks_simulation_to_cont extendEval kNext elseBranch exitConts []
            gen_t gen_e fl fbs h_else_eq h_nofd_else h_unique_else
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ' label bk_target h_label hwfb hwfv hwf_def hwf_congr
            h_else_exit h_accum_nil_f h_agree_after
            h_combined_else h_unique_combined_else h_hf_f cfg h_cfg_fbs h_cfg_nodup
        refine ⟨σ_cfg_branch, ?_, h_agree_branch, ?_⟩
        · exact StepDetCFGStar_trans h_flush_sim h_else_step
        · intro x h_σ_x h_x_not_accum h_x_not_inits
          have h_x_not_else : x ∉ Block.initVars elseBranch := by
            intro hx
            apply h_x_not_inits
            rw [h_initvars_eq]; exact List.mem_append_left _ (List.mem_append_right _ hx)
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_after x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          exact h_preserve_branch x h_σ_after_x h_nil_not h_x_not_else
    | inr h_caseB =>
      -- Branch terminates at ρ_mid, then rest exits with `label`.
      obtain ⟨ρ_mid, h_branch_term_or, h_rest_exit⟩ := h_caseB
      -- Eval well-formedness preservation through the branch (terminal).
      have hwfb₁ : WellFormedSemanticEvalBool ρ_mid.eval := by
        cases h_branch_term_or with
        | inl h => exact StepStmtStar_wfb_preserved extendEval thenBranch ρ₀ ρ_mid h.1 h_nofd_then hwfb
        | inr h => exact StepStmtStar_wfb_preserved extendEval elseBranch ρ₀ ρ_mid h.1 h_nofd_else hwfb
      have hwfv₁ : WellFormedSemanticEvalVal ρ_mid.eval := by
        cases h_branch_term_or with
        | inl h => exact StepStmtStar_wfv_preserved extendEval thenBranch ρ₀ ρ_mid h.1 h_nofd_then hwfv
        | inr h => exact StepStmtStar_wfv_preserved extendEval elseBranch ρ₀ ρ_mid h.1 h_nofd_else hwfv
      have h_eval_eq : ρ_mid.eval = ρ₀.eval := by
        cases h_branch_term_or with
        | inl h =>
          exact smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
            thenBranch ρ₀ ρ_mid h_nofd_then h.1
        | inr h =>
          exact smallStep_noFuncDecl_preserves_eval_block P (EvalCmd P) extendEval
            elseBranch ρ₀ ρ_mid h_nofd_else h.1
      have hwf_def₁ : WellFormedSemanticEvalDef ρ_mid.eval := by
        rw [h_eval_eq]; exact hwf_def
      have hwf_congr₁ : WellFormedSemanticEvalExprCongr ρ_mid.eval := by
        rw [h_eval_eq]; exact hwf_congr
      cases h_branch_term_or with
      | inl h_true =>
        obtain ⟨h_then_term, h_cond_tt⟩ := h_true
        have h_flush_sim : StepDetCFGStar extendEval cfg
            (.cont accumEntry σ_base hf_base)
            (.cont tl σ_cfg_after ρ₀.hasFailure) :=
          flushCmds_condGoto_true_agree extendEval accum e tl fl md l_ite gen_e gen_f
            accumEntry accumBlocks h_flush_eq σ_base σ_cfg_after hf_base hf_accum ρ₀
            hwfb hwf_def hwf_congr h_accum_cfg h_agree_after h_hf h_cond_tt cfg
            h_cfg_accum h_lookup
        have h_accum_nil_t : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have h_hf_t : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
        have ⟨σ_branch, h_then_step, h_agree_then, h_preserve_then⟩ :=
          stmtsToBlocks_simulation extendEval kNext thenBranch exitConts []
            gen_ite gen_t tl tbs h_then_eq h_nofd_then h_unique_then
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ_mid hwfb hwfv hwf_def hwf_congr h_then_term h_accum_nil_t h_agree_after
            h_combined_then h_unique_combined_then h_hf_t cfg h_cfg_tbs h_cfg_nodup
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
        have h_combined_rest :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
            σ_branch x = none := by
          intro x hx
          simp [Cmds.definedVars] at hx
          exact h_fresh_rest_inits_branch x hx
        have h_unique_combined_rest :
            (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
          simp [Cmds.definedVars]
          have h1 : ((Block.initVars thenBranch ++ Block.initVars elseBranch) ++
                      Block.initVars rest).Nodup :=
            (List.nodup_append.mp h_unique_outer_inits).2.1
          exact (List.nodup_append.mp h1).2.1
        have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_mid.eval ρ_mid.store
            [].reverse ρ_mid.store false := EvalCmds.eval_cmds_none
        have h_hf_r : ρ_mid.hasFailure = (ρ_mid.hasFailure || false) := by simp
        have ⟨σ_cfg, h_rest_sim, h_agree_rest, h_preserve_rest⟩ :=
          stmtsToBlocks_simulation_to_cont extendEval k rest exitConts [] gen gen_r kNext bsNext
            h_rest_eq h_nofd_rest h_unique_rest ρ_mid.store σ_branch ρ_mid.hasFailure false
            ρ_mid ρ' label bk_target h_label
            hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁
            h_rest_exit h_accum_nil_r h_agree_then
            h_combined_rest h_unique_combined_rest h_hf_r cfg h_cfg_rest h_cfg_nodup
        refine ⟨σ_cfg, ?_, h_agree_rest, ?_⟩
        · exact StepDetCFGStar_trans
            (StepDetCFGStar_trans h_flush_sim h_then_step) h_rest_sim
        · intro x h_σ_x h_x_not_accum h_x_not_inits
          have h_x_not_then : x ∉ Block.initVars thenBranch := by
            intro hx
            apply h_x_not_inits
            rw [h_initvars_eq]; exact List.mem_append_left _ (List.mem_append_left _ hx)
          have h_x_not_rest : x ∉ Block.initVars rest := by
            intro hx
            apply h_x_not_inits
            rw [h_initvars_eq]; exact List.mem_append_right _ hx
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_after x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          have h_σ_branch_x : σ_branch x = none :=
            h_preserve_then x h_σ_after_x h_nil_not h_x_not_then
          exact h_preserve_rest x h_σ_branch_x h_nil_not h_x_not_rest
      | inr h_false =>
        obtain ⟨h_else_term, h_cond_ff⟩ := h_false
        have h_flush_sim : StepDetCFGStar extendEval cfg
            (.cont accumEntry σ_base hf_base)
            (.cont fl σ_cfg_after ρ₀.hasFailure) :=
          flushCmds_condGoto_false_agree extendEval accum e tl fl md l_ite gen_e gen_f
            accumEntry accumBlocks h_flush_eq σ_base σ_cfg_after hf_base hf_accum ρ₀
            hwfb hwf_def hwf_congr h_accum_cfg h_agree_after h_hf h_cond_ff cfg
            h_cfg_accum h_lookup
        have h_accum_nil_f : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have h_hf_f : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
        have ⟨σ_branch, h_else_step, h_agree_else, h_preserve_else⟩ :=
          stmtsToBlocks_simulation extendEval kNext elseBranch exitConts []
            gen_t gen_e fl fbs h_else_eq h_nofd_else h_unique_else
            ρ₀.store σ_cfg_after ρ₀.hasFailure false
            ρ₀ ρ_mid hwfb hwfv hwf_def hwf_congr h_else_term h_accum_nil_f h_agree_after
            h_combined_else h_unique_combined_else h_hf_f cfg h_cfg_fbs h_cfg_nodup
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
        have h_combined_rest :
            ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars rest,
            σ_branch x = none := by
          intro x hx
          simp [Cmds.definedVars] at hx
          exact h_fresh_rest_inits_branch x hx
        have h_unique_combined_rest :
            (Cmds.definedVars [].reverse ++ Block.initVars rest).Nodup := by
          simp [Cmds.definedVars]
          have h1 : ((Block.initVars thenBranch ++ Block.initVars elseBranch) ++
                      Block.initVars rest).Nodup :=
            (List.nodup_append.mp h_unique_outer_inits).2.1
          exact (List.nodup_append.mp h1).2.1
        have h_accum_nil_r : EvalCmds P (EvalCmd P) ρ_mid.eval ρ_mid.store
            [].reverse ρ_mid.store false := EvalCmds.eval_cmds_none
        have h_hf_r : ρ_mid.hasFailure = (ρ_mid.hasFailure || false) := by simp
        have ⟨σ_cfg, h_rest_sim, h_agree_rest, h_preserve_rest⟩ :=
          stmtsToBlocks_simulation_to_cont extendEval k rest exitConts [] gen gen_r kNext bsNext
            h_rest_eq h_nofd_rest h_unique_rest ρ_mid.store σ_branch ρ_mid.hasFailure false
            ρ_mid ρ' label bk_target h_label
            hwfb₁ hwfv₁ hwf_def₁ hwf_congr₁
            h_rest_exit h_accum_nil_r h_agree_else
            h_combined_rest h_unique_combined_rest h_hf_r cfg h_cfg_rest h_cfg_nodup
        refine ⟨σ_cfg, ?_, h_agree_rest, ?_⟩
        · exact StepDetCFGStar_trans
            (StepDetCFGStar_trans h_flush_sim h_else_step) h_rest_sim
        · intro x h_σ_x h_x_not_accum h_x_not_inits
          have h_x_not_else : x ∉ Block.initVars elseBranch := by
            intro hx
            apply h_x_not_inits
            rw [h_initvars_eq]; exact List.mem_append_left _ (List.mem_append_right _ hx)
          have h_x_not_rest : x ∉ Block.initVars rest := by
            intro hx
            apply h_x_not_inits
            rw [h_initvars_eq]; exact List.mem_append_right _ hx
          have h_σ_after_x : σ_cfg_after x = none := h_preserve_after x h_σ_x h_x_not_accum
          have h_nil_not : x ∉ Cmds.definedVars [].reverse := by simp [Cmds.definedVars]
          have h_σ_branch_x : σ_branch x = none :=
            h_preserve_else x h_σ_after_x h_nil_not h_x_not_else
          exact h_preserve_rest x h_σ_branch_x h_nil_not h_x_not_rest
  | .ite .nondet thenBranch elseBranch md :: rest =>
    sorry
  | .loop guard measure invariants body md :: rest =>
    sorry
termination_by sizeOf ss
decreasing_by
  all_goals (subst h_match; simp_wf; omega)
end

/-- Variant of `stmtsToBlocks_simulation` for when the structured execution
exits rather than terminates. The CFG still reaches some terminal state. -/
private theorem stmtsToBlocks_simulation_exiting {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVal P] [HasIdent P] [HasIntOrder P]
    (extendEval : ExtendEval P)
    (k : String) (ss : List (Stmt P (Cmd P)))
    (exitConts : List (Option String × String))
    (accum : List (Cmd P))
    (allBlocks : DetBlocks String (Cmd P) P)
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : (stmtsToBlocks k ss exitConts accum gen) = ((entry, blocks), gen'))
    (σ_base : SemanticStore P)
    (hf_base : Bool)
    (hf_accum : Bool)
    (ρ₀ ρ' : Env P) (lbl : String)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (h_exit : StepStmtStar P (EvalCmd P) extendEval
      (.stmts ss ρ₀) (.exiting lbl ρ'))
    (h_accum : EvalCmds P (EvalCmd P) ρ₀.eval σ_base accum.reverse ρ₀.store hf_accum)
    (h_hf : ρ₀.hasFailure = (hf_base || hf_accum))
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (h_cfg_blocks : ∀ b ∈ blocks, b ∈ cfg.blocks) :
    ∃ σ_final failed, StepDetCFGStar extendEval cfg
      (.cont entry σ_base hf_base)
      (.terminal σ_final failed) ∧ σ_final = ρ'.store := by
  sorry

/-! ## Top-level theorems -/

/-- Specification lemma: `stmtsToCFG` produces a CFG whose blocks come from
`stmtsToBlocks` plus a terminal block, and whose entry matches.
Specialized to `CmdT = Cmd P` so we can use `stmtsToBlocks_invariant`
(which depends on the `[HasNot P]` instance present on `Cmd P`). -/
theorem stmtsToCFG_stmtsToBlocks_spec {P : PureExpr}
    [HasBool P] [HasIdent P] [HasFvar P] [HasIntOrder P] [HasNot P]
    (ss : List (Stmt P (Cmd P)))
    (h_disj : ∀ gen', Block.userLabelsDisjoint ss gen') :
    ∃ (lend : String) (gen gen' : StringGenState)
      (entry : String) (blocks : DetBlocks String (Cmd P) P),
      stmtsToBlocks lend ss [] [] gen = ((entry, blocks), gen') ∧
      (stmtsToCFG ss).entry = entry ∧
      (∀ b ∈ blocks, b ∈ (stmtsToCFG ss).blocks) ∧
      (stmtsToCFG ss).blocks.lookup lend =
        some ({ cmds := [], transfer := .finish } : BasicBlock (DetTransferCmd String P) (Cmd P)) := by
  let p_end := StringGenState.gen "end$" StringGenState.emp
  let lend := p_end.1
  let gen0 := p_end.2
  let r := stmtsToBlocks lend ss ([] : List (Option String × String)) ([] : List (Cmd P)) gen0
  have h_cfg : stmtsToCFG ss =
      { entry := r.1.1, blocks := r.1.2 ++ [(lend, { cmds := [], transfer := .finish })] } := by
    simp [stmtsToCFG, stmtsToCFGM]
    rfl
  refine ⟨lend, gen0, r.2, r.1.1, r.1.2, rfl, ?_, ?_, ?_⟩
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
    have h_inv : @GenInv P gen0 r.2 (Block.userBlockLabels ss) r.1.2 :=
      stmtsToBlocks_invariant lend ss [] [] gen0 r.2 _ _ h_eq hwf0 (h_disj _)
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

private theorem end_block_terminal {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    (extendEval : ExtendEval P)
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (lend : String) (σ : SemanticStore P) (δ : SemanticEval P) (failed : Bool)
    (h_lookup : cfg.blocks.lookup lend =
      some ({ cmds := [], transfer := .finish } : DetBlock String (Cmd P) P)) :
    StepDetCFGStar extendEval cfg
      (.cont lend σ failed)
      (.terminal σ failed) := by
    have h_eval : EvalDetBlock P (EvalCmd P) extendEval
        σ ({ cmds := [], transfer := .finish } : DetBlock String (Cmd P) P)
        (.terminal σ false) :=
      EvalDetBlock.step_terminal (δ := δ) EvalCmds.eval_cmds_none
    have h_step : @StepCFG _ _ (Cmd P) _ P (EvalDetBlock P (EvalCmd P) extendEval) cfg
        (.cont lend σ failed) (updateFailure (.terminal σ false) failed) :=
      StepCFG.eval_next (failed := failed) h_lookup h_eval
    have h_uf : @updateFailure String P (.terminal σ false) failed =
        CFGConfig.terminal σ failed := rfl
    rw [h_uf] at h_step
    exact ReflTrans.step _ _ _ h_step (ReflTrans.refl _)

/-- If the structured program reaches a terminal state, the CFG also reaches
    a corresponding terminal state. Requires that the initial failure flag is
    false, since the CFG always starts with failure = false.

    The CFG end-store agrees with the structured end-store on every defined
    variable (`StoreAgreement`); they may differ only on variables introduced
    by inner scopes (e.g. `.block`'s local frames). -/
theorem stmtsToCFG_terminal {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P)))
    (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwf_def : WellFormedSemanticEvalDef ρ₀.eval)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (hf₀ : ρ₀.hasFailure = false)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_unique : Block.uniqueInits ss)
    (h_fresh_inits : ∀ x ∈ Block.initVars ss, ρ₀.store x = none)
    (h_disj : ∀ gen', Block.userLabelsDisjoint ss gen')
    (h_term : StepStmtStar P (EvalCmd P) extendEval
      (.stmts ss ρ₀) (.terminal ρ')) :
    let cfg := stmtsToCFG ss
    ∃ σ_cfg, StepDetCFGStar extendEval cfg
      (.cont cfg.entry ρ₀.store false)
      (.terminal σ_cfg ρ'.hasFailure)
      ∧ StoreAgreement ρ'.store σ_cfg := by
  intro cfg
  have ⟨lend, gen, gen', entry, blocks, h_gen, h_entry, h_blocks, h_lend⟩ :=
    stmtsToCFG_stmtsToBlocks_spec ss h_disj
  rw [h_entry]
  have h_accum : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store [].reverse ρ₀.store false :=
    EvalCmds.eval_cmds_none
  have h_hf : ρ₀.hasFailure = (false || false) := by simp [hf₀]
  have h_nodup := stmtsToCFG_nodup_keys ss h_disj
  -- Combined freshness/Nodup: empty accum, so reduces to just inits.
  have h_fresh_combined : ∀ x ∈ Cmds.definedVars [].reverse ++ Block.initVars ss,
      ρ₀.store x = none := by
    intro x hx
    simp [Cmds.definedVars] at hx
    exact h_fresh_inits x hx
  have h_unique_combined : (Cmds.definedVars [].reverse ++ Block.initVars ss).Nodup := by
    simp [Cmds.definedVars]
    exact h_unique
  have ⟨σ_cfg, h_sim, h_agree, _h_preserve⟩ :=
    stmtsToBlocks_simulation extendEval lend ss [] [] gen gen' entry blocks
      h_gen h_nofd h_unique ρ₀.store ρ₀.store false false ρ₀ ρ' hwfb hwfv hwf_def hwf_congr
      h_term h_accum (StoreAgreement.refl _) h_fresh_combined h_unique_combined h_hf
      cfg h_blocks h_nodup
  have h_end := end_block_terminal extendEval cfg lend σ_cfg ρ'.eval ρ'.hasFailure h_lend
  exact ⟨σ_cfg, StepDetCFGStar_trans h_sim h_end, h_agree⟩

/-- If the structured program reaches an exiting state, the CFG also reaches
    a corresponding terminal state (since `stmtsToCFG` resolves exits to jumps). -/
theorem stmtsToCFG_exiting {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVal P] [HasIdent P] [HasIntOrder P]
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P)))
    (ρ₀ ρ' : Env P) (lbl : String)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hf₀ : ρ₀.hasFailure = false)
    (h_disj : ∀ gen', Block.userLabelsDisjoint ss gen')
    (h_exit : StepStmtStar P (EvalCmd P) extendEval
      (.stmts ss ρ₀) (.exiting lbl ρ')) :
    let cfg := stmtsToCFG ss
    ∃ σ_final failed,
      StepDetCFGStar extendEval cfg
        (.cont cfg.entry ρ₀.store false)
        (.terminal σ_final failed) ∧
      σ_final = ρ'.store := by
  intro cfg
  have ⟨lend, gen, gen', entry, blocks, h_gen, h_entry, h_blocks, _⟩ :=
    stmtsToCFG_stmtsToBlocks_spec ss h_disj
  rw [h_entry]
  have h_accum : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store [].reverse ρ₀.store false :=
    EvalCmds.eval_cmds_none
  have h_hf : ρ₀.hasFailure = (false || false) := by simp [hf₀]
  exact stmtsToBlocks_simulation_exiting extendEval lend ss [] [] blocks gen gen' entry blocks
    h_gen ρ₀.store false false ρ₀ ρ' lbl hwfb hwfv h_exit h_accum h_hf cfg h_blocks

/-! ## Main theorems -/

/-- `stmtsToCFG` is sound: any terminal state reachable from the structured
    execution is reachable from the CFG execution at a store that agrees with
    the structured store on every defined variable.

    Since CFGs have no "exiting" configs (exits are compiled to jumps), the
    exiting case is ruled out by the `h_exits` precondition. -/
theorem structuredToUnstructured_sound {P : PureExpr} [HasFvar P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P)))
    (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwf_def : WellFormedSemanticEvalDef ρ₀.eval)
    (hwf_congr : WellFormedSemanticEvalExprCongr ρ₀.eval)
    (hf₀ : ρ₀.hasFailure = false)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_unique : Block.uniqueInits ss)
    (h_fresh_inits : ∀ x ∈ Block.initVars ss, ρ₀.store x = none)
    (h_disj : ∀ gen', Block.userLabelsDisjoint ss gen')
    (h_term : StepStmtStar P (EvalCmd P) extendEval
      (.stmts ss ρ₀) (.terminal ρ')) :
    let cfg := stmtsToCFG ss
    ∃ σ_cfg, StepDetCFGStar extendEval cfg
      (.cont cfg.entry ρ₀.store false)
      (.terminal σ_cfg ρ'.hasFailure)
      ∧ StoreAgreement ρ'.store σ_cfg :=
  stmtsToCFG_terminal extendEval ss ρ₀ ρ' hwfb hwfv hwf_def hwf_congr hf₀
    h_nofd h_unique h_fresh_inits h_disj h_term

/-- Converse: any terminal store reachable from the CFG execution is also
    reachable from the structured execution. Together with soundness, this
    establishes bisimulation. -/
theorem structuredToUnstructured_complete {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVal P] [HasIdent P] [HasIntOrder P]
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P)))
    (ρ₀ : Env P) (σ_final : SemanticStore P) (failed : Bool)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hf₀ : ρ₀.hasFailure = false)
    (h_exits : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks [] ss)
    (h_cfg : let cfg := stmtsToCFG ss
             StepDetCFGStar extendEval cfg
               (.cont cfg.entry ρ₀.store false)
               (.terminal σ_final failed)) :
    ∃ ρ' : Env P,
      ρ'.store = σ_final ∧ ρ'.hasFailure = failed ∧
      StepStmtStar P (EvalCmd P) extendEval
        (.stmts ss ρ₀) (.terminal ρ') := by
  sorry

end StructuredToUnstructuredCorrect

end -- public section
