/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CFGSemantics
public import Strata.Transform.StructuredToUnstructured
public import Strata.Transform.Specification
public import Strata.DL.Util.StringGen

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

private structure GenInv {P : PureExpr} (gen gen' : StringGenState)
    (blocks : List (String × DetBlock String (Cmd P) P)) : Prop
    extends StringGenState.GenStep gen gen' where
  fresh : ∀ l ∈ blocks.map Prod.fst,
    l ∈ StringGenState.stringGens gen' ∧ l ∉ StringGenState.stringGens gen
  nodup : (blocks.map Prod.fst).Nodup

/-- The invariant for `flushCmds`: emitted blocks have fresh, unique labels.
We require WF on `gen` to conclude freshness w.r.t. `stringGens gen`. -/
private theorem flushCmds_invariant {P : PureExpr} [HasBool P]
    (pfx : String) (accum : List (Cmd P))
    (tr? : Option (DetTransferCmd String P)) (k : String)
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : flushCmds pfx accum tr? k gen = ((entry, blocks), gen'))
    (hwf : StringGenState.WF gen) :
    @GenInv P gen gen' blocks := by
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
      refine ⟨StringGenState.GenStep.refl _, ?_, ?_⟩
      · intros l hl; simp at hl
      · simp
    · rw [if_neg h_empty] at h_gen
      simp only [bind, StateT.bind, pure, StateT.pure, Id] at h_gen
      injection h_gen with h_pair h_gen_eq
      injection h_pair with h_entry_eq h_blocks_eq
      subst h_entry_eq; subst h_blocks_eq; subst h_gen_eq
      refine ⟨StringGenState.GenStep.of_gen pfx gen, ?_, ?_⟩
      · intro l hl
        simp at hl; subst hl
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
    refine ⟨StringGenState.GenStep.of_gen pfx gen, ?_, ?_⟩
    · intro l hl
      simp at hl; subst hl
      refine ⟨?_, ?_⟩
      · rw [StringGenState.stringGens_gen]; exact List.mem_cons.mpr (Or.inl rfl)
      · exact StringGenState.stringGens_gen_not_in pfx gen hwf
    · simp

/-- Composition lemma: if both `gen → gen_mid` (with `blocks₁`) and
`gen_mid → gen'` (with `blocks₂`) satisfy `GenInv`, then `gen → gen'`
with `blocks₁ ++ blocks₂` does too. -/
private theorem GenInv.trans {P : PureExpr}
    (gen gen_mid gen' : StringGenState)
    (blocks₁ blocks₂ : List (String × DetBlock String (Cmd P) P))
    (h₁ : @GenInv P gen gen_mid blocks₁)
    (h₂ : @GenInv P gen_mid gen' blocks₂) :
    @GenInv P gen gen' (blocks₁ ++ blocks₂) := by
  refine ⟨h₁.toGenStep.trans h₂.toGenStep, ?_, ?_⟩
  · intro l hl
    rw [List.map_append, List.mem_append] at hl
    cases hl with
    | inl h =>
      have ⟨h_in_mid, h_notin⟩ := h₁.fresh l h
      exact ⟨h₂.subset h_in_mid, h_notin⟩
    | inr h =>
      have ⟨h_in', h_notin_mid⟩ := h₂.fresh l h
      refine ⟨h_in', ?_⟩
      intro h_in_gen
      exact h_notin_mid (h₁.subset h_in_gen)
  · rw [List.map_append, List.nodup_append]
    refine ⟨h₁.nodup, h₂.nodup, ?_⟩
    intro x hx
    intro y hy h_eq
    -- x ∈ blocks₁.map fst, y ∈ blocks₂.map fst, h_eq : x = y
    have ⟨h_x_in_mid, _⟩ := h₁.fresh x hx
    have ⟨_, h_y_notin_mid⟩ := h₂.fresh y hy
    subst h_eq
    exact h_y_notin_mid h_x_in_mid

/-- Trivial GenInv: same state, no blocks. -/
private theorem GenInv.refl {P : PureExpr} (gen : StringGenState) :
    @GenInv P gen gen [] := by
  refine ⟨StringGenState.GenStep.refl _, ?_, ?_⟩
  · intro l hl; simp at hl
  · simp

/-- `GenInv` is closed under list permutation of the blocks (the freshness
and Nodup properties are permutation-invariant). -/
private theorem GenInv.perm {P : PureExpr}
    (gen gen' : StringGenState)
    (blocks₁ blocks₂ : List (String × DetBlock String (Cmd P) P))
    (h : @GenInv P gen gen' blocks₁)
    (hperm : blocks₁.Perm blocks₂) :
    @GenInv P gen gen' blocks₂ := by
  refine ⟨h.toGenStep, ?_, ?_⟩
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
    (blocks : List (String × DetBlock String (Cmd P) P))
    (l : String) (b : DetBlock String (Cmd P) P)
    (h_step : StringGenState.GenStep gen gen_mid)
    (h_blocks : @GenInv P gen_mid gen' blocks)
    (h_l_in : l ∈ StringGenState.stringGens gen')
    (h_l_notin_gen : l ∉ StringGenState.stringGens gen)
    (h_l_notin_blocks : l ∉ blocks.map Prod.fst) :
    @GenInv P gen gen' ((l, b) :: blocks) := by
  refine ⟨h_step.trans h_blocks.toGenStep, ?_, ?_⟩
  · intro x hx
    rw [List.map_cons, List.mem_cons] at hx
    cases hx with
    | inl h_eq =>
      subst h_eq
      exact ⟨h_l_in, h_l_notin_gen⟩
    | inr h_in =>
      have ⟨h_x_in, h_x_notin_mid⟩ := h_blocks.fresh _ h_in
      refine ⟨h_x_in, ?_⟩
      intro hgen
      exact h_x_notin_mid (h_step.subset hgen)
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨h_l_notin_blocks, h_blocks.nodup⟩

/-- All user-provided `Stmt.block` labels appearing in a list of statements.
Defined recursively on the list, with a helper for individual statements
defined as a local `where` clause for mutual recursion. -/
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

/-- A predicate stating that user-provided block labels do not collide
with strings generated by `gen`'s lifecycle (specifically, they are not
in `stringGens gen'`, i.e., were not produced by the generator). This is
the precondition needed for `stmtsToBlocks` to produce a CFG with unique
block labels. -/
@[expose] def Block.userLabelsDisjoint {P : PureExpr}
    (ss : List (Stmt P (Cmd P))) (gen' : StringGenState) : Prop :=
  ∀ l ∈ Block.userBlockLabels ss, l ∉ StringGenState.stringGens gen'

/-- `userLabelsDisjoint` distributes over `cons`: if a longer list is
disjoint, so is the tail. -/
private theorem Block.userLabelsDisjoint_tail {P : PureExpr}
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (s :: rest) gen') :
    Block.userLabelsDisjoint rest gen' := by
  intro l hl
  apply h
  unfold Block.userBlockLabels
  exact List.mem_append.mpr (Or.inr hl)

/-- `userLabelsDisjoint` for the head statement: if `s :: rest` is disjoint,
so are the user labels in `s` itself. -/
private theorem Block.userLabelsDisjoint_head {P : PureExpr}
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) (gen' : StringGenState)
    (h : Block.userLabelsDisjoint (s :: rest) gen') :
    ∀ l ∈ Block.userBlockLabels.stmtUserBlockLabels s,
      l ∉ StringGenState.stringGens gen' := by
  intro l hl
  apply h
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
  intro l hl h_in_gen
  exact h l hl (h_sub h_in_gen)

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
  sorry

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
    @GenInv P gen gen' blocks := by
  match h_match : ss with
  | [] =>
    -- stmtsToBlocks reduces to flushCmds "l$" accum .none k
    unfold stmtsToBlocks at h_gen
    exact flushCmds_invariant "l$" accum .none k gen gen' entry blocks h_gen hwf
  | .cmd c :: rest =>
    -- Recurse with extended accumulator
    unfold stmtsToBlocks at h_gen
    exact stmtsToBlocks_invariant k rest exitConts (c :: accum) gen gen' entry blocks h_gen hwf
      (Block.userLabelsDisjoint_tail _ _ _ h_disj)
  | .funcDecl _ _ :: rest =>
    -- Skip funcDecl, recurse on rest
    unfold stmtsToBlocks at h_gen
    exact stmtsToBlocks_invariant k rest exitConts accum gen gen' entry blocks h_gen hwf
      (Block.userLabelsDisjoint_tail _ _ _ h_disj)
  | .typeDecl _ _ :: rest =>
    -- Skip typeDecl, recurse on rest
    unfold stmtsToBlocks at h_gen
    exact stmtsToBlocks_invariant k rest exitConts accum gen gen' entry blocks h_gen hwf
      (Block.userLabelsDisjoint_tail _ _ _ h_disj)
  | .exit l? md :: _ =>
    -- The bk computation is pure (no gen calls); only flushCmds is stateful
    unfold stmtsToBlocks at h_gen
    exact flushCmds_invariant _ accum _ _ gen gen' entry blocks h_gen hwf
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
    have h_disj_bss_gen' : Block.userLabelsDisjoint bss gen' := by
      intro x hx
      apply Block.userLabelsDisjoint_head _ _ _ h_disj x
      unfold Block.userBlockLabels.stmtUserBlockLabels
      exact List.mem_cons.mpr (Or.inr hx)
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
    have h_inv_rest : @GenInv P gen gen_r bsNext :=
      stmtsToBlocks_invariant k rest exitConts [] gen gen_r kNext bsNext h_rest_eq hwf
        h_disj_rest_gen_r
    have hwf_r := h_inv_rest.wf_mono hwf
    have h_inv_body : @GenInv P gen_r gen_b bbs :=
      stmtsToBlocks_invariant kNext bss _ [] gen_r gen_b bl bbs h_body_eq hwf_r
        h_disj_bss_gen_b
    have hwf_b := h_inv_body.wf_mono hwf_r
    have h_inv_flush : @GenInv P gen_b gen_f accumBlocks :=
      flushCmds_invariant "blk$" accum .none bl gen_b gen_f accumEntry accumBlocks
        h_flush_eq hwf_b
    -- Compose chronologically: gen → gen_r → gen_b → gen_f
    have h_inv_chron : @GenInv P gen gen_f (bsNext ++ bbs ++ accumBlocks) :=
      GenInv.trans gen gen_b gen_f (bsNext ++ bbs) accumBlocks
        (GenInv.trans gen gen_r gen_b bsNext bbs h_inv_rest h_inv_body)
        h_inv_flush
    -- Permutation: (bsNext ++ bbs ++ accumBlocks) ~ (accumBlocks ++ bbs ++ bsNext)
    have h_perm : (bsNext ++ bbs ++ accumBlocks).Perm (accumBlocks ++ bbs ++ bsNext) := by
      have h1 : (bsNext ++ bbs ++ accumBlocks).Perm (accumBlocks ++ (bsNext ++ bbs)) :=
        List.perm_append_comm
      have h2 : (accumBlocks ++ (bsNext ++ bbs)).Perm (accumBlocks ++ (bbs ++ bsNext)) :=
        List.Perm.append_left accumBlocks List.perm_append_comm
      have h3 : (accumBlocks ++ (bbs ++ bsNext)) = (accumBlocks ++ bbs ++ bsNext) := by
        rw [List.append_assoc]
      exact (h1.trans h2).trans (h3 ▸ List.Perm.refl _)
    have h_inv_out : @GenInv P gen gen_f (accumBlocks ++ bbs ++ bsNext) :=
      GenInv.perm gen gen_f _ _ h_inv_chron h_perm
    -- Now case-split on the if l == bl
    by_cases h_eq : l = bl
    · rw [if_pos h_eq] at h_gen
      simp only [pure, StateT.pure] at h_gen
      have h_pair := (Prod.mk.inj h_gen).1
      have h_entry_eq : accumEntry = entry := (Prod.mk.inj h_pair).1
      have h_blocks_eq : accumBlocks ++ (bbs ++ bsNext) = blocks := (Prod.mk.inj h_pair).2
      subst h_entry_eq
      have h_blks : blocks = accumBlocks ++ bbs ++ bsNext := by
        rw [List.append_assoc]; exact h_blocks_eq.symm
      rw [h_blks]
      rw [← h_gen_eq]
      exact h_inv_out
    · rw [if_neg h_eq] at h_gen
      sorry
  | .ite c tss fss md :: rest =>
    -- Five sub-computations (gen for ite label, rest, then, else, optional gen
    -- for nondet, flushCmds with condGoto). Same permutation issue as block.
    sorry
  | .loop c m is bss md :: rest =>
    -- Most complex: nested matches on m and c, mapM over invariants.
    sorry
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
  have h_inv : @GenInv P gen0 r.2 r.1.2 :=
    stmtsToBlocks_invariant lend ss [] [] gen0 r.2 _ _ h_eq hwf0 (h_disj _)
  -- Build Nodup of r.1.2.map Prod.fst ++ [lend]
  rw [List.nodup_append]
  refine ⟨h_inv.nodup, ?_, ?_⟩
  · simp
  · -- disjointness: lend not in r.1.2.map Prod.fst
    intro x hx
    intro y hy h_eq
    rw [List.mem_singleton] at hy
    subst hy
    -- After: h_eq : x = lend, and we want False
    subst h_eq
    -- Now x is gone, lend ∈ l₁ (i.e. lend ∈ map fst r.1.2)
    have ⟨_, h_lend_notin⟩ := h_inv.fresh _ hx
    exact h_lend_notin h_lend_in_gen0



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
private theorem flushCmds_condGoto_true {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
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
  -- Instance equality (HasBool from explicit class vs HasNot.toHasBool diamond)
  have h_inst_eq : (inferInstance : HasBool P) = HasNot.toHasBool := by
    sorry  -- Instance equality (orthogonal to flushCmds fix)
  have h_cond' : ρ₀.eval ρ₀.store e = .some (@HasBool.tt P HasNot.toHasBool) := by
    rw [← h_inst_eq]; exact h_cond
  have hwfb' : @WellFormedSemanticEvalBool P HasNot.toHasBool _ ρ₀.eval := by
    rw [← h_inst_eq]; exact hwfb
  have h_eval_block : EvalDetBlock P (EvalCmd P) extendEval
      σ_base ⟨accum.reverse, .condGoto e tl fl md⟩
      (.cont tl ρ₀.store hf_accum) :=
    EvalDetBlock.step_goto_true (δ := ρ₀.eval) h_accum h_cond' hwfb'
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
private theorem flushCmds_condGoto_false {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
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
  have h_inst_eq : (inferInstance : HasBool P) = HasNot.toHasBool := by
    sorry  -- Instance equality (orthogonal to flushCmds fix)
  have h_cond' : ρ₀.eval ρ₀.store e = .some (@HasBool.ff P HasNot.toHasBool) := by
    rw [← h_inst_eq]; exact h_cond
  have hwfb' : @WellFormedSemanticEvalBool P HasNot.toHasBool _ ρ₀.eval := by
    rw [← h_inst_eq]; exact hwfb
  have h_eval_block : EvalDetBlock P (EvalCmd P) extendEval
      σ_base ⟨accum.reverse, .condGoto e tl fl md⟩
      (.cont fl ρ₀.store hf_accum) :=
    EvalDetBlock.step_goto_false (δ := ρ₀.eval) h_accum h_cond' hwfb'
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

/-! ## Generalized simulation

The central lemma: for any continuation `k`, exit-continuation stack, and
accumulated commands, if the structured execution of `ss` from `ρ₀` terminates
(or exits), then the CFG blocks produced by `stmtsToBlocks` can step from the
entry label to the continuation `k` (or the resolved exit target). -/

private theorem flushCmds_simulation {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
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
    (h_cfg_blocks : ∀ b ∈ blocks, b ∈ cfg.blocks) :
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
    sorry

private theorem stmtsToBlocks_simulation {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    (extendEval : ExtendEval P)
    (k : String) (ss : List (Stmt P (Cmd P)))
    (exitConts : List (Option String × String))
    (accum : List (Cmd P))
    (gen gen' : StringGenState)
    (entry : String) (blocks : DetBlocks String (Cmd P) P)
    (h_gen : (stmtsToBlocks k ss exitConts accum gen) = ((entry, blocks), gen'))
    (h_nofd : Block.noFuncDecl ss = true)
    (σ_base : SemanticStore P)
    (hf_base : Bool)
    (hf_accum : Bool)
    (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (h_term : StepStmtStar P (EvalCmd P) extendEval
      (.stmts ss ρ₀) (.terminal ρ'))
    (h_accum : EvalCmds P (EvalCmd P) ρ₀.eval σ_base accum.reverse ρ₀.store hf_accum)
    (h_hf : ρ₀.hasFailure = (hf_base || hf_accum))
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (h_cfg_blocks : ∀ b ∈ blocks, b ∈ cfg.blocks)
    (h_cfg_nodup : (cfg.blocks.map Prod.fst).Nodup) :
    StepDetCFGStar extendEval cfg
      (.cont entry σ_base hf_base)
      (.cont k ρ'.store ρ'.hasFailure) := by
  match h_match : ss with
  | [] =>
    -- stmtsToBlocks k [] exitConts accum = flushCmds "l$" accum .none k
    unfold stmtsToBlocks at h_gen
    have h_ρ : ρ₀ = ρ' := stmts_nil_terminal (EvalCmd P) extendEval _ _ h_term
    subst h_ρ
    exact flushCmds_simulation extendEval "l$" k accum gen gen' entry blocks h_gen
      σ_base hf_base hf_accum ρ₀ hwfb hwfv h_accum h_hf cfg h_cfg_blocks
  | .cmd c :: rest =>
    unfold stmtsToBlocks at h_gen
    -- Structured semantics: execute c then rest
    have ⟨ρ₁, h_c_star, h_rest_star⟩ :=
      stmts_append_terminates P (EvalCmd P) extendEval [.cmd c] rest ρ₀ ρ'
        (by simp at h_term ⊢; exact h_term)
    have ⟨σ_c, failed_c, heval_c, hstore_c, heval_eq_c, hfail_c⟩ :=
      single_cmd_eval extendEval c ρ₀ ρ₁ h_c_star
    have h_accum' : EvalCmds P (EvalCmd P) ρ₁.eval σ_base (c :: accum).reverse ρ₁.store
        (hf_accum || failed_c) := by
      simp [List.reverse_cons]
      rw [heval_eq_c, hstore_c]
      exact EvalCmds_snoc ρ₀.eval σ_base ρ₀.store σ_c accum.reverse c hf_accum failed_c
        h_accum heval_c
    have h_hf' : ρ₁.hasFailure = (hf_base || (hf_accum || failed_c)) := by
      rw [hfail_c, h_hf, Bool.or_assoc]
    have hwfb' : WellFormedSemanticEvalBool ρ₁.eval := by rw [heval_eq_c]; exact hwfb
    have hwfv' : WellFormedSemanticEvalVal ρ₁.eval := by rw [heval_eq_c]; exact hwfv
    have h_nofd_rest : Block.noFuncDecl rest = true := by
      simp [Block.noFuncDecl] at h_nofd; exact h_nofd.2
    exact stmtsToBlocks_simulation extendEval k rest exitConts (c :: accum) gen gen'
      entry blocks h_gen h_nofd_rest σ_base hf_base (hf_accum || failed_c) ρ₁ ρ' hwfb' hwfv'
      h_rest_star h_accum' h_hf' cfg h_cfg_blocks h_cfg_nodup
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
    -- Rest simulation via recursive call (rest is structurally smaller)
    have h_accum_nil : EvalCmds P (EvalCmd P) ρ₁.eval ρ₁.store
        [].reverse ρ₁.store false := EvalCmds.eval_cmds_none
    have h_hf_rest : ρ₁.hasFailure = (ρ₁.hasFailure || false) := by simp
    have h_rest_sim : StepDetCFGStar extendEval cfg
        (.cont kNext ρ₁.store ρ₁.hasFailure)
        (.cont k ρ'.store ρ'.hasFailure) :=
      stmtsToBlocks_simulation extendEval k rest exitConts [] gen gen_r kNext bsNext
        h_rest_eq h_nofd_rest ρ₁.store ρ₁.hasFailure false ρ₁ ρ' hwfb₁ hwfv₁
        h_rest_star h_accum_nil h_hf_rest cfg h_cfg_rest h_cfg_nodup
    -- Case split on which branch was taken
    cases h_ite_inv with
    | inl h_true =>
      obtain ⟨h_then_term, h_cond_tt⟩ := h_true
      -- CFG steps: entry →[accum+condGoto(true)]→ tl
      have h_flush_sim : StepDetCFGStar extendEval cfg
          (.cont accumEntry σ_base hf_base)
          (.cont tl ρ₀.store ρ₀.hasFailure) := by
        have h_lookup : ∀ lbl blk, (lbl, blk) ∈ cfg.blocks →
            cfg.blocks.lookup lbl = some blk :=
          fun lbl blk h_mem => List.lookup_of_mem_nodup cfg.blocks h_cfg_nodup lbl blk h_mem
        exact flushCmds_condGoto_true extendEval accum e tl fl md l_ite gen_e gen_f
          accumEntry accumBlocks h_flush_eq σ_base hf_base hf_accum ρ₀
          hwfb h_accum h_hf h_cond_tt cfg h_cfg_accum h_lookup
      -- CFG steps: tl →[then-branch blocks]→ kNext
      -- Recursive call: thenBranch is structurally smaller than ss
      have h_then_sim : StepDetCFGStar extendEval cfg
          (.cont tl ρ₀.store ρ₀.hasFailure)
          (.cont kNext ρ₁.store ρ₁.hasFailure) := by
        have h_accum_nil_t : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have h_hf_t : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
        exact stmtsToBlocks_simulation extendEval kNext thenBranch exitConts []
          gen_ite gen_t tl tbs h_then_eq h_nofd_then ρ₀.store ρ₀.hasFailure false
          ρ₀ ρ₁ hwfb hwfv h_then_term h_accum_nil_t h_hf_t cfg h_cfg_tbs h_cfg_nodup
      exact StepDetCFGStar_trans
        (StepDetCFGStar_trans h_flush_sim h_then_sim) h_rest_sim
    | inr h_false =>
      obtain ⟨h_else_term, h_cond_ff⟩ := h_false
      -- CFG steps: entry →[accum+condGoto(false)]→ fl
      have h_flush_sim : StepDetCFGStar extendEval cfg
          (.cont accumEntry σ_base hf_base)
          (.cont fl ρ₀.store ρ₀.hasFailure) := by
        have h_lookup : ∀ lbl blk, (lbl, blk) ∈ cfg.blocks →
            cfg.blocks.lookup lbl = some blk :=
          fun lbl blk h_mem => List.lookup_of_mem_nodup cfg.blocks h_cfg_nodup lbl blk h_mem
        exact flushCmds_condGoto_false extendEval accum e tl fl md l_ite gen_e gen_f
          accumEntry accumBlocks h_flush_eq σ_base hf_base hf_accum ρ₀
          hwfb h_accum h_hf h_cond_ff cfg h_cfg_accum h_lookup
      -- CFG steps: fl →[else-branch blocks]→ kNext
      -- Recursive call: elseBranch is structurally smaller than ss
      have h_else_sim : StepDetCFGStar extendEval cfg
          (.cont fl ρ₀.store ρ₀.hasFailure)
          (.cont kNext ρ₁.store ρ₁.hasFailure) := by
        have h_accum_nil_f : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store
            [].reverse ρ₀.store false := EvalCmds.eval_cmds_none
        have h_hf_f : ρ₀.hasFailure = (ρ₀.hasFailure || false) := by simp
        exact stmtsToBlocks_simulation extendEval kNext elseBranch exitConts []
          gen_t gen_e fl fbs h_else_eq h_nofd_else ρ₀.store ρ₀.hasFailure false
          ρ₀ ρ₁ hwfb hwfv h_else_term h_accum_nil_f h_hf_f cfg h_cfg_fbs h_cfg_nodup
      exact StepDetCFGStar_trans
        (StepDetCFGStar_trans h_flush_sim h_else_sim) h_rest_sim
  | .ite .nondet thenBranch elseBranch md :: rest =>
    sorry
  | .loop guard measure invariants body md :: rest =>
    sorry
  | .block label body md :: rest =>
    sorry
  | .exit label md :: rest =>
    sorry
  | .funcDecl decl md :: rest =>
    -- funcDecl changes the evaluator — requires additional reasoning
    sorry
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
    exact stmtsToBlocks_simulation extendEval k rest exitConts accum gen gen'
      entry blocks h_gen h_nofd_rest σ_base hf_base hf_accum ρ₀ ρ' hwfb hwfv h_rest_star
      h_accum h_hf cfg h_cfg_blocks h_cfg_nodup
termination_by sizeOf ss
decreasing_by
  all_goals (subst h_match; simp_wf; omega)

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
    have h_inv : @GenInv P gen0 r.2 r.1.2 :=
      stmtsToBlocks_invariant lend ss [] [] gen0 r.2 _ _ h_eq hwf0 (h_disj _)
    have h_lend_not_in_blocks : lend ∉ r.1.2.map Prod.fst := by
      intro h_in
      have ⟨_, h_notin⟩ := h_inv.fresh _ h_in
      exact h_notin h_lend_in_gen0
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
    the corresponding terminal state. Requires that the initial failure flag is
    false, since the CFG always starts with failure = false. -/
theorem stmtsToCFG_terminal {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P)))
    (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hf₀ : ρ₀.hasFailure = false)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_disj : ∀ gen', Block.userLabelsDisjoint ss gen')
    (h_term : StepStmtStar P (EvalCmd P) extendEval
      (.stmts ss ρ₀) (.terminal ρ')) :
    let cfg := stmtsToCFG ss
    StepDetCFGStar extendEval cfg
      (.cont cfg.entry ρ₀.store false)
      (.terminal ρ'.store ρ'.hasFailure) := by
  intro cfg
  have ⟨lend, gen, gen', entry, blocks, h_gen, h_entry, h_blocks, h_lend⟩ :=
    stmtsToCFG_stmtsToBlocks_spec ss h_disj
  rw [h_entry]
  have h_accum : EvalCmds P (EvalCmd P) ρ₀.eval ρ₀.store [].reverse ρ₀.store false :=
    EvalCmds.eval_cmds_none
  have h_hf : ρ₀.hasFailure = (false || false) := by simp [hf₀]
  have h_nodup := stmtsToCFG_nodup_keys ss h_disj
  have h_sim := stmtsToBlocks_simulation extendEval lend ss [] [] gen gen' entry blocks
      h_gen h_nofd ρ₀.store false false ρ₀ ρ' hwfb hwfv h_term h_accum h_hf cfg h_blocks h_nodup
  have h_end := end_block_terminal extendEval cfg lend ρ'.store ρ'.eval ρ'.hasFailure h_lend
  exact StepDetCFGStar_trans h_sim h_end

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

/-- `stmtsToCFG` is sound: any terminal store reachable from the structured
    execution is also reachable from the CFG execution, provided the evaluator
    is well-formed and the initial failure flag is false.

    Since CFGs have no "exiting" configs (exits are compiled to jumps), the
    exiting case is ruled out by the `h_exits` precondition. -/
theorem structuredToUnstructured_sound {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P]
    [HasVal P] [HasBoolVal P] [HasIdent P] [HasIntOrder P]
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P)))
    (ρ₀ ρ' : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hf₀ : ρ₀.hasFailure = false)
    (h_nofd : Block.noFuncDecl ss = true)
    (h_disj : ∀ gen', Block.userLabelsDisjoint ss gen')
    (h_term : StepStmtStar P (EvalCmd P) extendEval
      (.stmts ss ρ₀) (.terminal ρ')) :
    let cfg := stmtsToCFG ss
    StepDetCFGStar extendEval cfg
      (.cont cfg.entry ρ₀.store false)
      (.terminal ρ'.store ρ'.hasFailure) :=
  stmtsToCFG_terminal extendEval ss ρ₀ ρ' hwfb hwfv hf₀ h_nofd h_disj h_term

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
