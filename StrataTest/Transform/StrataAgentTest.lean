import Strata.Transform.Specification

open Imperative Specification Transform

/-! # The Language We're Working In

We work GENERICALLY over any expression system `P` satisfying these constraints:
- HasFvar P    : expressions can contain free variables
- HasBool P    : there exist expressions `tt` and `ff` (true/false)
- HasNot P     : there's a `not` operation on expressions
- HasIntOrder P: there's integer comparison (eq, lt, zero)
- HasVal P     : there's a notion of "value" (fully evaluated expression)

The STATEMENTS are `Stmt P (Cmd P)` — the Imperative dialect's statement type:
  .cmd c              -- atomic command (init, set, assert, assume, havoc, cover)
  .block l [s1,...] md -- labeled block
  .ite cond [t1,...] [e1,...] md -- if-then-else
  .loop guard meas inv [body...] md -- loop
  .exit l md          -- structured exit
  .funcDecl f md      -- local function declaration
  .typeDecl tc md     -- local type declaration

The SEMANTICS are given by `EvalCmd P` (command evaluation) and `StepStmt`
(small-step transitions). Multi-step is `StepStmtStar` (reflexive-transitive closure).

The CONFIGURATIONS are `Config P (Cmd P)`:
  .stmt s ρ           -- about to execute statement s in environment ρ
  .stmts [s1,...] ρ   -- about to execute statement list
  .terminal ρ         -- execution finished
  .exiting lbl ρ      -- exiting with label
  .block lbl inner    -- inside a block (wraps inner config)
  .seq inner [rest..] -- sequencing (inner executes, then rest)
-/

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasIntOrder P] [HasVal P]

/-! ## Abbreviations to make things readable -/

-- The language we're proving things about:
-- "Standard imperative language with expression system P"
abbrev MyLang (extendEval : ExtendEval P) : Lang P :=
  Lang.imperative P (Cmd P) (EvalCmd P) extendEval (isAtAssert P)

-- The multi-step execution relation
-- "st ρ₀ →* terminal ρ'"  means  StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) (.terminal ρ')
-- which is exactly what (MyLang extendEval).star (stmtCfg st ρ₀) (terminalCfg ρ') unfolds to.

-- KEY INSIGHT: When you see the goal:
--   (MyLang extendEval).star ((MyLang extendEval).stmtCfg st ρ₀) ((MyLang extendEval).terminalCfg ρ')
-- This is definitionally equal to:
--   StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) (.terminal ρ')
-- Lean knows this — you can use StepStmt constructors directly!

/-! ## Exercise 0: Identity overapproximates -/

theorem my_overapproximates_id (L : Lang P) :
    Overapproximates L L some := by
  unfold Overapproximates
  simp

/-! ## Exercise 1: Sound identity -/

theorem my_sound_id (L : Lang P) :
  Sound L L some := by
  unfold Sound
  simp
  intro s s' a h_s_s' h_assert
  simp [h_s_s']
  assumption

/-! ## Exercise 2: wrapInBlock overapproximates

The transform: given any statement `st`, produce `block "wrapper" [st]`.

Example (informally):
  Source: `assert [foo] (x == 1)`
  Target: `block "wrapper" { assert [foo] (x == 1) }`

Why it overapproximates: the block adds no behavior — it just wraps.
Any terminal state reachable from `st` is also reachable from `block [st]`.

The execution trace for the target looks like:
  .stmt (.block "wrapper" [st] .empty) ρ₀
    →  step_block
  .block (some "wrapper") (.stmts [st] ρ₀)
    →  step_block_body step_stmts_cons
  .block (some "wrapper") (.seq (.stmt st ρ₀) [])
    →* step_block_body (seq_inner_star ... <source execution>)
  .block (some "wrapper") (.seq (.terminal ρ') [])
    →  step_block_body step_seq_done
  .block (some "wrapper") (.stmts [] ρ')
    →  step_block_body step_stmts_nil
  .block (some "wrapper") (.terminal ρ')
    →  step_block_done
  .terminal ρ'
-/

/-! ## No-defs-no-new-vars lemma

If a command `c` has `Cmd.definedVars c = []` (i.e., it is not an `init` command),
then executing `.stmt (.cmd c) ρ₀ →* .terminal ρ'` does not grow the store:
every variable defined in `ρ'.store` was already defined in `ρ₀.store`.
-/

/-- Helper: `UpdateState` preserves the store domain. -/
private theorem updateState_no_new_vars
    {σ σ' : SemanticStore P} {name : P.Ident} {v : P.Expr}
    (hupd : UpdateState P σ name v σ') :
    ∀ x, (σ' x).isSome → (σ x).isSome := by
  intro x hx
  cases hupd with
  | update hold hset hall =>
    by_cases heq : name = x
    · subst heq; simp_all [Option.isSome]
    · rw [hall x heq] at hx; exact hx

/-- Helper: if `EvalCmd` evaluates a non-init command, the store domain doesn't grow. -/
private theorem evalCmd_no_init_no_new_vars
    {c : Cmd P} {δ : SemanticEval P} {σ σ' : SemanticStore P} {f : Bool}
    (heval : EvalCmd P δ σ c σ' f)
    (h_no_defs : Cmd.definedVars c = []) :
    ∀ x, (σ' x).isSome → (σ x).isSome := by
  cases heval with
  | eval_init _ _ _ => simp [Cmd.definedVars] at h_no_defs
  | eval_init_unconstrained _ _ => simp [Cmd.definedVars] at h_no_defs
  | eval_set _ hupd _ => exact updateState_no_new_vars hupd
  | eval_set_nondet hupd _ => exact updateState_no_new_vars hupd
  | eval_assert_pass _ _ => intro x hx; exact hx
  | eval_assert_fail _ _ => intro x hx; exact hx
  | eval_assume _ _ => intro x hx; exact hx
  | eval_cover _ => intro x hx; exact hx

/-- If a command has no defined vars (not an init), executing it doesn't grow the store. -/
theorem cmd_no_defs_no_new_vars
    {extendEval : ExtendEval P}
    {c : Cmd P} {ρ₀ ρ' : Env P}
    (h_step : StepStmtStar P (EvalCmd P) extendEval (Config.stmt (Stmt.cmd c) ρ₀) (Config.terminal ρ'))
    (h_no_defs : Cmd.definedVars c = []) :
    ∀ x, (ρ'.store x).isSome → (ρ₀.store x).isSome := by
  -- The execution from .stmt (.cmd c) ρ₀ to .terminal ρ' must be exactly one step_cmd
  cases h_step with
  | step _ _ _ hstep hrest =>
    cases hstep with
    | step_cmd hcmd =>
      -- After step_cmd, we're at .terminal {...}, so hrest must be refl
      cases hrest with
      | refl =>
        intro x hx
        simp at *
        exact evalCmd_no_init_no_new_vars hcmd h_no_defs x hx
      | step _ _ _ h _ => exact nomatch h

-- Generalized transform: wrap any COMMAND with definedVars = [] in a block.
-- This accepts all commands except .init (which creates new variables).
def wrapCmdInBlock (s : Stmt P (Cmd P)) : Option (Stmt P (Cmd P)) :=
  match s with
  | .cmd c =>
    if Cmd.definedVars c = [] then
      some (.block "wrapper" [.cmd c] .empty)
    else
      none
  | _ => none

/-! ### Helper lemma: wrapping any command in a block overapproximates,
    given `Cmd.definedVars c = []`. Uses `evalCmd_no_init_no_new_vars`. -/

private theorem wrapCmd_overapprox_helper
    (extendEval : ExtendEval P)
    (c : Cmd P)
    (ρ₀ : Env P)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hswf : (MyLang extendEval).initEnvWF (Stmt.cmd c) ρ₀)
    (h_no_defs : Cmd.definedVars c = []) :
    (∀ ρ',
      (StepStmtStar P (EvalCmd P) extendEval (Config.stmt (Stmt.cmd c) ρ₀) (Config.terminal ρ') →
        StepStmtStar P (EvalCmd P) extendEval
          (Config.stmt (Stmt.block "wrapper" [Stmt.cmd c] .empty) ρ₀) (Config.terminal ρ'))
      ∧
      (∀ lbl, StepStmtStar P (EvalCmd P) extendEval (Config.stmt (Stmt.cmd c) ρ₀) (Config.exiting lbl ρ') →
        StepStmtStar P (EvalCmd P) extendEval
          (Config.stmt (Stmt.block "wrapper" [Stmt.cmd c] .empty) ρ₀) (Config.exiting lbl ρ')))
    ∧
    (CanFail (MyLang extendEval) (Stmt.cmd c) ρ₀ →
      CanFail (MyLang extendEval) (Stmt.block "wrapper" [Stmt.cmd c] .empty) ρ₀)
    ∧
    (MyLang extendEval).initEnvWF (Stmt.block "wrapper" [Stmt.cmd c] .empty) ρ₀ := by
  refine ⟨fun ρ' => ⟨?_, ?_⟩, ?_, ?_⟩
  · -- Terminal case
    intro h_step_st
    have h_store_sub : ∀ x, (ρ'.store x).isSome → (ρ₀.store x).isSome :=
      cmd_no_defs_no_new_vars h_step_st h_no_defs
    have h_proj : projectStore ρ₀.store ρ'.store = ρ'.store := by
      funext x; simp [projectStore]
      cases heq : ρ₀.store x with
      | none =>
        cases heq' : ρ'.store x with
        | none => simp
        | some v =>
          exfalso
          have := h_store_sub x (by rw [heq']; rfl)
          simp [Option.isSome, heq] at this
      | some _ => simp_all
    have h_enter : StepStmtStar P (EvalCmd P) extendEval
        (Config.stmt (Stmt.block "wrapper" [Stmt.cmd c] .empty) ρ₀)
        (Config.block (some "wrapper") ρ₀.store (Config.seq (Config.stmt (Stmt.cmd c) ρ₀) [])) :=
      .step _ _ _ StepStmt.step_block
        (.step _ _ _ (StepStmt.step_block_body StepStmt.step_stmts_cons) (.refl _))
    have h_mid := block_inner_star P (EvalCmd P) extendEval _ _
      (some "wrapper") ρ₀.store (seq_inner_star P (EvalCmd P) extendEval _ _ [] h_step_st)
    have h_tail : StepStmtStar P (EvalCmd P) extendEval
        (Config.block (some "wrapper") ρ₀.store (Config.seq (Config.terminal ρ') []))
        (Config.terminal { ρ' with store := projectStore ρ₀.store ρ'.store }) :=
      .step _ _ _ (StepStmt.step_block_body StepStmt.step_seq_done)
        (.step _ _ _ (StepStmt.step_block_body StepStmt.step_stmts_nil)
          (.step _ _ _ StepStmt.step_block_done (.refl _)))
    have h23 := ReflTrans_Transitive (StepStmt P (EvalCmd P) extendEval) _ _ _ h_mid h_tail
    have h_full := ReflTrans_Transitive (StepStmt P (EvalCmd P) extendEval) _ _ _ h_enter h23
    simp [h_proj] at h_full
    exact h_full
  · -- Exiting case: .cmd c can never produce exiting (commands are atomic)
    intro lbl h_step_st
    cases h_step_st with
    | step _ _ _ hstep hrest =>
      cases hstep with
      | step_cmd hcmd =>
        cases hrest with
        | step _ _ _ h _ => exact nomatch h
  · -- CanFail: lift failing execution into the block context
    intro ⟨cfg, hfail, hreach⟩
    have h_enter : StepStmtStar P (EvalCmd P) extendEval
        (Config.stmt (Stmt.block "wrapper" [Stmt.cmd c] .empty) ρ₀)
        (Config.block (some "wrapper") ρ₀.store (Config.seq (Config.stmt (Stmt.cmd c) ρ₀) [])) :=
      .step _ _ _ StepStmt.step_block
        (.step _ _ _ (StepStmt.step_block_body StepStmt.step_stmts_cons) (.refl _))
    have h_lifted := block_inner_star P (EvalCmd P) extendEval _ _
      (some "wrapper") ρ₀.store (seq_inner_star P (EvalCmd P) extendEval _ _ [] hreach)
    have h_full := ReflTrans_Transitive (StepStmt P (EvalCmd P) extendEval) _ _ _ h_enter h_lifted
    exact ⟨Config.block (some "wrapper") ρ₀.store (Config.seq cfg []), hfail, h_full⟩
  · -- initEnvWF
    exact hswf

/-! ### Main theorem: uses the helper with cmd_no_defs_no_new_vars -/

theorem wrapCmdInBlock_overapproximates
    (extendEval : ExtendEval P) :
    Overapproximates (MyLang extendEval) (MyLang extendEval) wrapCmdInBlock := by
  intro st s' ht ρ₀ hwfb hwfv hswf
  match st with
  | .cmd c =>
    simp [wrapCmdInBlock] at ht
    obtain ⟨h_no_defs, ht⟩ := ht
    subst ht
    exact wrapCmd_overapprox_helper extendEval c ρ₀ hwfb hwfv hswf h_no_defs
  | .block .. | .ite .. | .loop .. | .exit .. | .funcDecl .. | .typeDecl .. =>
    simp [wrapCmdInBlock] at ht
