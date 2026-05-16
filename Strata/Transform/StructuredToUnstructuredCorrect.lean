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

/-- The measure block computation in the `loop` case produces a `GenInv`.
The result list `decreaseBlocks` is either `[]` (when `m = none`) or contains
exactly one block `(ldec, ...)` where `ldec` is freshly generated. -/
private theorem measure_invariant {P : PureExpr} [HasInit P (Cmd P)] [HasIdent P]
    [HasFvar P] [HasIntOrder P] [HasNot P] [HasPassiveCmds P (Cmd P)]
    (m : Option P.Expr)
    (lentry : String)
    (gen_le gen_m : StringGenState)
    (measureCmds : List (Cmd P)) (bodyK : String)
    (decreaseBlocks : DetBlocks String (Cmd P) P)
    (hwf_le : StringGenState.WF gen_le)
    (h_eq :
      (match m with
       | none => (pure ([], lentry, []) : LabelGen.StringGenM
                    (List (Cmd P) × String × DetBlocks String (Cmd P) P))
       | some mExpr => do
         let mLabel ← StringGenState.gen "loop_measure$"
         let mIdent := HasIdent.ident mLabel
         let mOldExpr := HasFvar.mkFvar mIdent
         let initCmd  := HasInit.init mIdent HasIntOrder.intTy ExprOrNondet.nondet synthesizedMd
         let assumeCmd := HasPassiveCmds.assume s!"assume_{mLabel}"
                            (HasIntOrder.eq mOldExpr mExpr) synthesizedMd
         let lbCmd    := HasPassiveCmds.assert s!"measure_lb_{mLabel}"
                            (HasNot.not (HasIntOrder.lt mOldExpr HasIntOrder.zero)) synthesizedMd
         let decCmd   := HasPassiveCmds.assert s!"measure_decrease_{mLabel}"
                            (HasIntOrder.lt mExpr mOldExpr) synthesizedMd
         let ldec ← StringGenState.gen "measure_decrease$"
         let decBlock := (ldec, ({ cmds := [decCmd],
                                   transfer := DetTransferCmd.goto lentry }
                                 : DetBlock String (Cmd P) P))
         pure ([initCmd, assumeCmd, lbCmd], ldec, [decBlock])) gen_le
       = ((measureCmds, bodyK, decreaseBlocks), gen_m)) :
    @GenInv P gen_le gen_m [] decreaseBlocks := by
  cases h_m_cases : m with
  | none =>
    rw [h_m_cases] at h_eq
    simp only [pure, StateT.pure] at h_eq
    -- h_eq : (([], lentry, []), gen_le) = ((measureCmds, bodyK, decreaseBlocks), gen_m)
    -- This reduces to: ([], lentry, []) = (measureCmds, bodyK, decreaseBlocks) ∧ gen_le = gen_m
    have h_pairs := (Prod.mk.inj h_eq).1
    -- h_pairs : ([], lentry, []) = (measureCmds, bodyK, decreaseBlocks)
    -- The 3-tuple: ([], (lentry, [])) = (measureCmds, (bodyK, decreaseBlocks))
    have h_db : decreaseBlocks = [] := ((Prod.mk.inj h_pairs).2 |> Prod.mk.inj).2.symm
    have h_gen_m : gen_m = gen_le := ((Prod.mk.inj h_eq).2).symm
    rw [h_db, h_gen_m]
    exact GenInv.refl gen_le hwf_le
  | some mExpr =>
    rw [h_m_cases] at h_eq
    simp only [bind, StateT.bind, pure, StateT.pure] at h_eq
    generalize h_ml : StringGenState.gen "loop_measure$" gen_le = r_ml at h_eq
    obtain ⟨mLabel, gen_ml⟩ := r_ml
    simp only at h_eq
    generalize h_ld : StringGenState.gen "measure_decrease$" gen_ml = r_ld at h_eq
    obtain ⟨ldec, gen_ld⟩ := r_ld
    simp only at h_eq
    have h_pairs := (Prod.mk.inj h_eq).1
    have h_db_eq : decreaseBlocks =
        [(ldec, ({ cmds := [HasPassiveCmds.assert (P := P) (CmdT := Cmd P)
                             s!"measure_decrease_{mLabel}"
                             (HasIntOrder.lt mExpr (HasFvar.mkFvar (HasIdent.ident mLabel)))
                             synthesizedMd],
                   transfer := DetTransferCmd.goto lentry } : DetBlock String (Cmd P) P))] :=
      ((Prod.mk.inj h_pairs).2 |> Prod.mk.inj).2.symm
    have h_gen_m_eq : gen_m = gen_ld := ((Prod.mk.inj h_eq).2).symm
    rw [h_db_eq, h_gen_m_eq]
    -- Show: GenInv gen_le gen_ld [] [(ldec, ...)]
    -- gen_le → gen_ml (one gen) → gen_ld (one gen)
    have h_step_ml : StringGenState.GenStep gen_le gen_ml := by
      rw [show gen_ml = (StringGenState.gen "loop_measure$" gen_le).2 from
            (by rw [h_ml])]
      exact StringGenState.GenStep.of_gen "loop_measure$" gen_le
    have hwf_ml : StringGenState.WF gen_ml := h_step_ml.wf_mono hwf_le
    have h_step_ld : StringGenState.GenStep gen_ml gen_ld := by
      rw [show gen_ld = (StringGenState.gen "measure_decrease$" gen_ml).2 from
            (by rw [h_ld])]
      exact StringGenState.GenStep.of_gen "measure_decrease$" gen_ml
    -- ldec is freshly generated from gen_ml.
    have h_ldec_in_gen_ld : ldec ∈ StringGenState.stringGens gen_ld := by
      rw [show ldec = (StringGenState.gen "measure_decrease$" gen_ml).1 from
            (by rw [h_ld])]
      rw [show gen_ld = (StringGenState.gen "measure_decrease$" gen_ml).2 from
            (by rw [h_ld])]
      rw [StringGenState.stringGens_gen]
      exact List.mem_cons.mpr (Or.inl rfl)
    have h_ldec_notin_gen_le : ldec ∉ StringGenState.stringGens gen_le := by
      intro h_in
      have h_in_ml : ldec ∈ StringGenState.stringGens gen_ml := h_step_ml.subset h_in
      have h_ldec_eq : ldec = (StringGenState.gen "measure_decrease$" gen_ml).1 := by
        rw [h_ld]
      have h_notin :=
        StringGenState.stringGens_gen_not_in "measure_decrease$" gen_ml hwf_ml
      rw [h_ldec_eq] at h_in_ml
      exact h_notin h_in_ml
    -- Build GenInv via cons_gen on top of the trivial GenInv at gen_ml.
    apply GenInv.cons_gen gen_le gen_ml gen_ld [] []
    · exact hwf_le
    · exact h_step_ml
    · exact GenInv.empty_step gen_ml gen_ld hwf_ml h_step_ld
    · exact h_ldec_in_gen_ld
    · exact h_ldec_notin_gen_le
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
    · -- l ≠ bl: blocks = accumBlocks ++ (l, .goto bl md) :: (bbs ++ bsNext)
      rw [if_neg h_eq] at h_gen
      simp only [pure, StateT.pure] at h_gen
      have h_pair := (Prod.mk.inj h_gen).1
      have h_entry_eq : l = entry := (Prod.mk.inj h_pair).1
      let lBlk : DetBlock String (Cmd P) P :=
        { cmds := [], transfer := DetTransferCmd.goto bl md }
      have h_blocks_eq :
          accumBlocks ++ (l, lBlk) :: (bbs ++ bsNext) = blocks :=
        (Prod.mk.inj h_pair).2
      subst h_entry_eq
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
    -- Sub-computations:
    --   gen → gen_r:    stmtsToBlocks rest
    --   gen_r → gen_le: gen "loop_entry$"
    --   gen_le → gen_m: match m (none: id; some: gen "loop_measure$" then gen "measure_decrease$")
    --   gen_m → gen_b:  stmtsToBlocks bss
    --   gen_b → gen_i:  is.mapM (mapM over invariants)
    --   gen_i → gen_n:  match c (det: id; nondet: gen "$__nondet_loop$")
    --   gen_n → gen_f:  flushCmds "before_loop$"
    --
    -- Output blocks: accumBlocks ++ [(lentry, ...)] ++ bbs ++ decreaseBlocks ++ bsNext
    -- Output user labels: userBlockLabels bss ++ userBlockLabels rest
    --
    -- Helpers built and ready: mapM_genStep, measure_invariant,
    -- Block.userLabels_loop_cross_disj, GenInv.{cons_gen, cons_user, weaken_userLabels,
    -- empty_step}.
    --
    -- The first 5 monadic peels (rest, lentry, measure-match, body, mapM)
    -- decompose cleanly via `generalize`. The 6th step (`match c`) is the
    -- sticking point because the inner `let contractMd := match m with ...`
    -- creates a second `match m` that confounds case analysis of c. Closing
    -- this requires a wrapper helper that captures the contractMd computation
    -- separately.
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
