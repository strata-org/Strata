/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.StmtProps
public import Strata.DL.Imperative.CmdSemanticsProps
public import Strata.DL.Imperative.CmdTraceWF
import all Strata.DL.Imperative.CmdSemanticsProps
import all Strata.DL.Imperative.Cmd
import all Strata.Util.Relations
import all Strata.Util.RelationsProps

namespace Imperative

public section

/-! # Metatheory of statement-list small-step evaluation

## Statement-level store and environment extension laws

`StoreAgreement.of_projectStore` and `StoreAgreement.of_projectStore_parents`
(block-scope `projectStore` survival for store agreement),
`StoreExtendsWith.projectStore` (scope-projection of a classified store
extension), and `Env.ExtendsWith.refl` / `Env.ExtendsWith.trans_union`
(environment-extension reflexivity and composition).  These are the
statement-level (`projectStore`- and `Env`-keyed) companions of the
command-level store relations in `StoreRelationsProps`.

## Failure-flag semantics

Key results for `StepStmt` / `StepStmtStar`:

- Store and expression plumbing: `projectStore_id`, the `StoreAgreement`
  helpers, and the `eval_fvarExpr_*`, `eval_mkFvar_*`, and `mkTypedFvar_*`
  families.
- Block scope: `projectStore_eq_dropVars` shows that leaving a block drops
  exactly the names scoped by its body.
- Configuration invariants: `Config.varsDefined_star_of`,
  `Config.varsUndefinedThroughout_star_of`, and
  `Config.varsUndefinedScoped_star_of` preserve store-domain properties;
  `block_run_terminal_preserves_eq_of_not_written` preserves the exact value of
  variables a block does not write.
- Run inversion and lifting results for `.seq`, `.block`, and `.stmts`.

## Event-trace semantics

Key results for `StepStmtE` / `StepStmtStarE`:

- `StepStmt.toStepStmtE` embeds failure-flag steps into event semantics while
  preserving their deterministic event trace.
- `stepE_preserves_factory` and `starE_preserves_factory` establish factory
  invariance for single-step and multi-step event runs.
- `seq_run_decomposeE`, `seq_reaches_terminalE`, and
  `seq_reaches_exitingE` split traced sequence runs chronologically;
  `stmtRun_to_singletonE` lifts a completed statement run to its singleton-list run.
- `stepStmtStarE_from_terminal` / `stepStmtStarE_from_exiting`,
  `block_reaches_doneE`, and `stmt_block_reaches_doneE` characterize completed
  traced runs.
- `projectStore_eq_dropVarsE` provides event-trace block-scope preservation.
- `seqT_reaches_terminalE` and `stmtsT_cons_terminalE` provide step-counted
  completion inversions used by the event loop rule.
- `Config.varsDefined_star_ofE` and `Config.storeWellDefined_star_ofE`
  preserve store-domain properties across traced runs;
  `Config.storeWellDefined_step_evalCmdE` and
  `Config.storeWellDefined_star_evalCmdE` specialize this preservation to the
  evaluator value law at the run's unchanged factory.
- `StepStmtE.imp` and `StepStmtStarE.imp`: `StepStmtE` and `StepStmtStarE` are
  monotone in their command relation.
- `stmts_prefix_terminal_appendE`, `stmts_prefix_exiting_appendE`, and
  `stmts_prefix_appendE` extend a traced run of a statement-list prefix to the
  whole list.

## Event snapshots

- `Event.readsDefined` / `Trace.readsDefined` state that every captured free
  variable is defined at its event snapshot; `Cmd.emittedEvents_readsDefined`
  establishes it for a single command.
- `Trace.semanticWF_of_stepE` / `Trace.semanticWF_of_starE` show that traced
  runs from well-formed stores emit semantically well-formed snapshots.
- `Config.defUseReady` lifts `Block.defUseWellFormed` to configurations;
  `Config.defUseReady_stepE` / `Config.defUseReady_starE` preserve it, and
  `Block.run_readsDefined` concludes that every run of a def-use well-formed
  block emits read-defined events. `block_run_terminal_store_isSome_eqE`
  supports this by tracking which names a terminating block run defines.
-/

variable {P : PureExpr} {CmdT : Type}

/-- If every var that's defined in `σ'` is also defined in `σ`, then projection
    through `σ` is the identity on `σ'`. -/
theorem projectStore_id {P : PureExpr} {σ σ' : SemanticStore P}
    (h : ∀ x, σ' x ≠ none → σ x ≠ none) :
    projectStore σ σ' = σ' := by
  funext x
  simp only [projectStore, ite_eq_left_iff, Bool.not_eq_true, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none]
  intro hx
  cases heq : σ' x
  · rfl
  · exact absurd hx (h x (by simp [heq]))

/-- Projecting a store through itself is the identity. -/
theorem projectStore_self {P : PureExpr} (σ : SemanticStore P) :
    projectStore σ σ = σ := projectStore_id (fun _ h => h)

/-- `projectStore` preserves `isSome` for any variable that is `isSome`
    in both the parent and the inner store. -/
theorem projectStore_isSome {P : PureExpr} {σ_parent σ_inner : SemanticStore P}
    {n : P.Ident}
    (hp : (σ_parent n).isSome) (hi : (σ_inner n).isSome) :
    (projectStore σ_parent σ_inner n).isSome := by
  simp [projectStore, hp, hi]

/-! ## `Env.varsUndefined` properties -/

/-- `Env.varsUndefined` unfolds to its original per-string shape.  The
`SemanticStore.varsUndefined` delegation is over `∃ s, Q s ∧ y = ident s`; this
recovers the equivalent `∀ s, Q s → ρ.store (ident s) = none` used at call sites. -/
theorem Env.varsUndefined_iff {P : PureExpr} [HasIdent P]
    {Q : String → Prop} {ρ : Env P} :
    Env.varsUndefined Q ρ ↔ ∀ s : String, Q s → ρ.store (HasIdent.ident (P := P) s) = none := by
  constructor
  · intro h s hs; exact h (HasIdent.ident (P := P) s) ⟨s, hs, rfl⟩
  · rintro h y ⟨s, hs, rfl⟩; exact h s hs

/-- Apply `Env.varsUndefined` directly at a string key. -/
theorem Env.varsUndefined_apply {P : PureExpr} [HasIdent P]
    {Q : String → Prop} {ρ : Env P} (h : Env.varsUndefined Q ρ)
    (s : String) (hs : Q s) : ρ.store (HasIdent.ident (P := P) s) = none :=
  h (HasIdent.ident (P := P) s) ⟨s, hs, rfl⟩

/-- Monotonicity of `Env.varsUndefined` in its name predicate: if `Q ⊆ R` and every
`R`-named var is undefined, then every `Q`-named var is. -/
theorem Env.varsUndefined_of_imp {P : PureExpr} [HasIdent P] {Q R : String → Prop}
    {ρ : Env P} (himp : ∀ s, Q s → R s) (h : Env.varsUndefined R ρ) :
    Env.varsUndefined Q ρ :=
  Env.varsUndefined_iff.mpr (fun s hs => Env.varsUndefined_apply h s (himp s hs))

/-- An empty statement list reaching `.terminal` leaves the environment
unchanged: the only run of `.stmts [] ρ₀` to `.terminal ρ'` has `ρ₀ = ρ'`. -/
theorem stmts_nil_terminal {P : PureExpr} [HasBoolOps P]
    {CmdT : Type}
    (EvalCmdR : EvalCmdParam P CmdT)

    (ρ₀ ρ' : Env P)
    (h : StepStmtStar P EvalCmdR (.stmts [] ρ₀) (.terminal ρ')) :
    ρ₀ = ρ' := by
  rcases h
  rename_i h₁ h₂ h₃
  cases h₂
  cases h₃
  · rfl
  · rename_i h₁ _
    cases h₁

/-! ## Multi-step execution: properties -/

section

variable
  {CmdT : Type}
  (P : PureExpr)
  [HasFvars P] [HasBool P] [HasInt P] [HasIntOps P] [HasOps P]
  (EvalCmd : EvalCmdParam P CmdT)


omit [HasOps P] [HasFvars P] [HasInt P] [HasIntOps P] in
/-- Empty statement list evaluation. -/
theorem evalStmtsSmallNil
    (ρ : Env P) :
    EvalStmtsSmall P EvalCmd ρ [] ρ := by
  unfold EvalStmtsSmall
  exact .step _ _ _ StepStmt.step_stmts_nil (.refl _)

omit [HasOps P] [HasFvars P] [HasInt P] [HasIntOps P] in
/-- A single step preserves the environment's factory. -/
theorem step_preserves_factory
    (c₁ c₂ : Config P CmdT)
    (hstep : StepStmt P EvalCmd c₁ c₂) :
    c₁.getEnv.factory = c₂.getEnv.factory := by
  induction hstep with
  | step_seq_inner _ ih => simpa [Config.getEnv] using ih
  | step_block_body _ ih => simpa [Config.getEnv] using ih
  | _ => simp [Config.getEnv]

omit [HasOps P] [HasFvars P] [HasInt P] [HasIntOps P] in
/-- Terminal configurations are indeed terminal. -/
theorem terminalIsTerminal
    (ρ : Env P) :
    IsTerminal P EvalCmd (.terminal ρ) := by
  unfold IsTerminal
  intro c' h
  cases h

omit [HasOps P] [HasFvars P] [HasInt P] [HasIntOps P] in
/-- Helper: if the inner config of a `.seq` takes multiple steps, the
    enclosing `.seq` takes the same number of steps.
    Proved by induction on the multi-step derivation. -/
theorem seq_inner_star
    (inner inner' : Config P CmdT)
    (ss : List (Stmt P CmdT))
    (h : StepStmtStar P EvalCmd inner inner') :
    StepStmtStar P EvalCmd
      (.seq inner ss)
      (.seq inner' ss) := by
  induction h with
  | refl => exact .refl _
  | step _ mid _ hstep _ ih =>
    exact .step _ _ _ (.step_seq_inner hstep) ih

omit [HasOps P] [HasFvars P] [HasInt P] [HasIntOps P] in
/-- Helper: if the inner config of a `.block` takes multiple steps, the
    enclosing `.block` takes the same number of steps. -/
theorem block_inner_star
    (inner inner' : Config P CmdT)
    (label : Option String)
    (σ_parent : SemanticStore P)
    (h : StepStmtStar P EvalCmd inner inner') :
    StepStmtStar P EvalCmd
      (.block label σ_parent inner) (.block label σ_parent inner') := by
  induction h with
  | refl => exact .refl _
  | step _ mid _ hstep _ ih => exact .step _ _ _ (.step_block_body hstep) ih

omit [HasOps P] [HasFvars P] [HasInt P] [HasIntOps P] in
/-- When executing `.stmts (s :: ss) ρ`, if the head statement `s`
    multi-steps to `.terminal ρ'`, then the whole list multi-steps to
    `.stmts ss ρ'`.

    This captures the fundamental sequencing behaviour of statement lists
    in the small-step semantics. -/
theorem stmts_cons_step
    (s : Stmt P CmdT) (ss : List (Stmt P CmdT))
    (ρ ρ' : Env P)
    (hstmt : StepStmtStar P EvalCmd
      (.stmt s ρ) (.terminal ρ')) :
    StepStmtStar P EvalCmd
      (.stmts (s :: ss) ρ)
      (.stmts ss ρ') := by
  -- Step 1: .stmts (s :: ss) ρ  →  .seq (.stmt s ρ) ss
  --         via step_stmts_cons
  apply ReflTrans.step _ (.seq (.stmt s ρ) ss)
  · exact .step_stmts_cons
  -- Step 2: .seq (.stmt s ρ) ss  →*  .seq (.terminal ρ') ss
  --         by lifting hstmt through the seq context
  have h2 := seq_inner_star P EvalCmd _ _ ss hstmt
  -- Step 3: .seq (.terminal ρ') ss  →  .stmts ss ρ'
  --         via step_seq_done, then chain with h2 by induction
  suffices h3 : StepStmtStar P EvalCmd
      (.seq (.terminal ρ') ss) (.stmts ss ρ') from
    ReflTrans_Transitive _ _ _ _ h2 h3
  exact .step _ _ _ .step_seq_done (.refl _)

/-! ## Inversion lemmas for seq and block execution -/

omit [HasOps P] [HasFvars P] [HasInt P] [HasIntOps P] in
/-- Invert a seq execution reaching terminal: the inner terminates,
    then the tail stmts run to terminal. -/
theorem seq_reaches_terminal
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)} {ρ' : Env P}
    (hstar : StepStmtStar P EvalCmd (.seq inner ss) (.terminal ρ')) :
    ∃ ρ₁, StepStmtStar P EvalCmd inner (.terminal ρ₁) ∧
      StepStmtStar P EvalCmd (.stmts ss ρ₁) (.terminal ρ') := by
  suffices h_gen : ∀ src tgt, StepStmtStar P EvalCmd src tgt →
      ∀ inner ss ρ', src = .seq inner ss → tgt = .terminal ρ' →
      ∃ ρ₁, StepStmtStar P EvalCmd inner (.terminal ρ₁) ∧
        StepStmtStar P EvalCmd (.stmts ss ρ₁) (.terminal ρ') from
    h_gen _ _ hstar _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner ss ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_seq_inner h =>
      have ⟨ρ₁, hterm, htail⟩ := ih _ _ _ rfl htgt
      exact ⟨ρ₁, .step _ _ _ h hterm, htail⟩
    | step_seq_done => subst htgt; exact ⟨_, .refl _, hrest⟩
    | step_seq_exit => subst htgt; cases hrest with | step _ _ _ h _ => cases h

omit [HasOps P] [HasFvars P] [HasInt P] [HasIntOps P] in
/-- Invert a seq execution reaching exiting: either the inner exited
    (propagated), or the inner terminated and the tail exited. -/
theorem seq_reaches_exiting
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)} {lbl : String} {ρ' : Env P}
    (hstar : StepStmtStar P EvalCmd (.seq inner ss) (.exiting lbl ρ')) :
    (StepStmtStar P EvalCmd inner (.exiting lbl ρ')) ∨
    (∃ ρ₁, StepStmtStar P EvalCmd inner (.terminal ρ₁) ∧
      StepStmtStar P EvalCmd (.stmts ss ρ₁) (.exiting lbl ρ')) := by
  suffices h_gen : ∀ src tgt, StepStmtStar P EvalCmd src tgt →
      ∀ inner ss lbl ρ', src = .seq inner ss → tgt = .exiting lbl ρ' →
      (StepStmtStar P EvalCmd inner (.exiting lbl ρ')) ∨
      (∃ ρ₁, StepStmtStar P EvalCmd inner (.terminal ρ₁) ∧
        StepStmtStar P EvalCmd (.stmts ss ρ₁) (.exiting lbl ρ')) from
    h_gen _ _ hstar _ _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner ss lbl ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_seq_inner h =>
      match ih _ _ _ _ rfl htgt with
      | .inl hexit => exact .inl (.step _ _ _ h hexit)
      | .inr ⟨ρ₁, hterm, htail⟩ => exact .inr ⟨ρ₁, .step _ _ _ h hterm, htail⟩
    | step_seq_done => subst htgt; exact .inr ⟨_, .refl _, hrest⟩
    | step_seq_exit => exact .inl (htgt ▸ hrest)

/-! ## Trace construction helpers -/

omit [HasOps P] [HasFvars P] [HasInt P] [HasIntOps P] in
/-- Decompose a terminating execution of `ss₁ ++ ss₂` into a terminating
    execution of `ss₁` followed by a terminating execution of `ss₂`. -/
theorem stmts_append_terminates
    (ss₁ ss₂ : List (Stmt P CmdT)) (ρ ρ' : Env P)
    (h : StepStmtStar P EvalCmd (.stmts (ss₁ ++ ss₂) ρ) (.terminal ρ')) :
    ∃ ρ₁, StepStmtStar P EvalCmd (.stmts ss₁ ρ) (.terminal ρ₁) ∧
           StepStmtStar P EvalCmd (.stmts ss₂ ρ₁) (.terminal ρ') := by
  induction ss₁ generalizing ρ with
  | nil =>
    exact ⟨ρ, .step _ _ _ .step_stmts_nil (.refl _), h⟩
  | cons s rest ih =>
    cases h with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        have ⟨ρ_mid, h_s, h_rest_ss₂⟩ :=
          seq_reaches_terminal P EvalCmd hrest
        have ⟨ρ₁, h_rest, h_ss₂⟩ := ih ρ_mid h_rest_ss₂
        exact ⟨ρ₁, ReflTrans_Transitive _ _ _ _
          (stmts_cons_step P EvalCmd
            s rest ρ ρ_mid h_s) h_rest, h_ss₂⟩

omit [HasOps P] [HasFvars P] [HasInt P] [HasIntOps P] in
/-- An exiting head statement makes the whole list exit with the same label: the
    tail never runs. -/
private theorem stmts_cons_exiting
    (s : Stmt P CmdT) (ss : List (Stmt P CmdT)) (ρ ρ' : Env P) (lbl : String)
    (h : StepStmtStar P EvalCmd (.stmt s ρ) (.exiting lbl ρ')) :
    StepStmtStar P EvalCmd (.stmts (s :: ss) ρ) (.exiting lbl ρ') := by
  refine .step _ _ _ .step_stmts_cons ?_
  exact ReflTrans_Transitive _ _ _ _
    (seq_inner_star P EvalCmd _ _ ss h)
    (.step _ _ _ .step_seq_exit (.refl _))

omit [HasOps P] [HasFvars P] [HasInt P] [HasIntOps P] in
/-- Decompose a *finished* execution of `ss₁ ++ ss₂` — terminal or exiting — by what
    `ss₁` did: either `ss₁` exited on its own, and `ss₂` never ran, or `ss₁`
    terminated at some `ρ₁` from which `ss₂` finished the same way.
    `stmts_append_terminates` is the terminal-only special case. -/
theorem stmts_append_done
    (ss₁ ss₂ : List (Stmt P CmdT)) (ρ ρ' : Env P)
    (h : StepStmtStar P EvalCmd (.stmts (ss₁ ++ ss₂) ρ) (.terminal ρ') ∨
      ∃ lbl, StepStmtStar P EvalCmd (.stmts (ss₁ ++ ss₂) ρ) (.exiting lbl ρ')) :
    (∃ lbl, StepStmtStar P EvalCmd (.stmts ss₁ ρ) (.exiting lbl ρ')) ∨
    (∃ ρ₁, StepStmtStar P EvalCmd (.stmts ss₁ ρ) (.terminal ρ₁) ∧
      (StepStmtStar P EvalCmd (.stmts ss₂ ρ₁) (.terminal ρ') ∨
       ∃ lbl, StepStmtStar P EvalCmd (.stmts ss₂ ρ₁) (.exiting lbl ρ'))) := by
  induction ss₁ generalizing ρ with
  | nil => exact .inr ⟨ρ, .step _ _ _ .step_stmts_nil (.refl _), h⟩
  | cons s rest ih =>
    -- Peel the head off, then recurse on `rest ++ ss₂`.
    have hhead : (∃ lbl, StepStmtStar P EvalCmd (.stmt s ρ) (.exiting lbl ρ')) ∨
        ∃ ρ_mid, StepStmtStar P EvalCmd (.stmt s ρ) (.terminal ρ_mid) ∧
          (StepStmtStar P EvalCmd (.stmts (rest ++ ss₂) ρ_mid) (.terminal ρ') ∨
           ∃ lbl, StepStmtStar P EvalCmd
             (.stmts (rest ++ ss₂) ρ_mid) (.exiting lbl ρ')) := by
      match h with
      | .inl hterm =>
        cases hterm with
        | step _ _ _ hstep hrest => cases hstep with
          | step_stmts_cons =>
            have ⟨ρ_mid, h_s, h_tail⟩ := seq_reaches_terminal P EvalCmd hrest
            exact .inr ⟨ρ_mid, h_s, .inl h_tail⟩
      | .inr ⟨lbl, hexit⟩ =>
        cases hexit with
        | step _ _ _ hstep hrest => cases hstep with
          | step_stmts_cons =>
            match seq_reaches_exiting P EvalCmd hrest with
            | .inl h_s => exact .inl ⟨lbl, h_s⟩
            | .inr ⟨ρ_mid, h_s, h_tail⟩ => exact .inr ⟨ρ_mid, h_s, .inr ⟨lbl, h_tail⟩⟩
    match hhead with
    | .inl ⟨lbl, h_s⟩ =>
      exact .inl ⟨lbl, stmts_cons_exiting P EvalCmd s rest ρ ρ' lbl h_s⟩
    | .inr ⟨ρ_mid, h_s, h_tail⟩ =>
      have hcons := stmts_cons_step P EvalCmd s rest ρ ρ_mid h_s
      match ih ρ_mid h_tail with
      | .inl ⟨lbl, hexit_rest⟩ =>
        exact .inl ⟨lbl, ReflTrans_Transitive _ _ _ _ hcons hexit_rest⟩
      | .inr ⟨ρ₁, hterm_rest, hfin⟩ =>
        exact .inr ⟨ρ₁, ReflTrans_Transitive _ _ _ _ hcons hterm_rest, hfin⟩

/-- Try every non-recursive `StepStmt` constructor, using `‹_›` (term-level
    assumption) to fill arguments so that no hypothesis names are needed. -/
local macro "apply_step" : tactic => `(tactic| first
  | exact .step_cmd ‹_›        | exact .step_ite_true ‹_›
  | exact .step_ite_false ‹_›
  | exact .step_loop_enter ‹_›
  | exact .step_loop_exit ‹_›
  | exact .step_block
  | exact .step_exit
  | exact .step_typeDecl        | exact .step_stmts_nil
  | exact .step_stmts_cons)

/-! ## Well-paired exits: preservation and no-escape -/

omit [HasBool P] [HasOps P] [HasFvars P] in
/-- Helper: when the inner of a block reaches `.exiting l` and the
    block's label (if some) doesn't match `l`, then `l` must be in the outer
    labels list.  The conclusion is `l ∈ labels`, which is exactly the
    `Config.exitsCoveredByBlocks` of `.exiting l ρ''` for any ρ''. -/
private theorem block_exit_mismatch_unfold {labels : List String}
    {label : Option String} {σ_parent : SemanticStore P}
    {l : String} {ρ' ρ'' : Env P}
    (h : Config.exitsCoveredByBlocks labels
          (.block label σ_parent (.exiting l ρ' : Config P CmdT)))
    (hne : label ≠ .some l) :
    Config.exitsCoveredByBlocks labels (.exiting l ρ'' : Config P CmdT) := by
  show l ∈ labels
  cases label with
  | none => exact h
  | some lb =>
    have h' : l ∈ lb :: labels := h
    rw [List.mem_cons] at h'
    rcases h' with hh | hh
    · exact absurd (by rw [hh]) hne
    · exact hh

omit [HasOps P] [HasInt P] [HasIntOps P] [HasFvars P] in
/-- A single step preserves `Config.exitsCoveredByBlocks`. -/
theorem step_preserves_exitsCoveredByBlocks
    (labels : List String)
    (c₁ c₂ : Config P CmdT)
    (hstep : StepStmt P EvalCmd c₁ c₂)
    (hwp : c₁.exitsCoveredByBlocks labels) :
    c₂.exitsCoveredByBlocks labels := by
  -- Prove a generalized version where labels is universally quantified,
  -- so the IH works at any nesting depth (needed for step_block_body).
  suffices h_gen : ∀ c₁ c₂, StepStmt P EvalCmd c₁ c₂ →
      ∀ labels, c₁.exitsCoveredByBlocks labels → c₂.exitsCoveredByBlocks labels by
    exact h_gen c₁ c₂ hstep labels hwp
  intro c₁ c₂ hstep
  induction hstep with
  | step_cmd => intro _ _; trivial
  | step_block => intro _ hwp; exact hwp
  | step_ite_true => intro _ hwp; exact hwp.1
  | step_ite_false => intro _ hwp; exact hwp.2
  | step_ite_nondet_true => intro _ hwp; exact hwp.1
  | step_ite_nondet_false => intro _ hwp; exact hwp.2
  | step_loop_enter _ =>
    intro labels hwp
    -- Goal: .seq (.block .none ρ.store (.stmts body ρ')) [.loop ...] covers labels.
    -- The .block .none label doesn't extend the labels list (Config.exitsCoveredByBlocks's
    -- .block none case just descends).
    simp only [Config.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks] at hwp ⊢
    exact ⟨hwp, hwp, True.intro⟩
  | step_loop_exit => intro _ _; trivial
  | step_loop_nondet_enter =>
    intro labels hwp
    simp only [Config.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks] at hwp ⊢
    exact ⟨hwp, hwp, True.intro⟩
  | step_loop_nondet_exit => intro _ _; trivial
  | step_exit =>
    intro labels hwp
    -- hwp : l ∈ labels (from .stmt (.exit l)), goal: .exiting (.some l) covers labels = l ∈ labels
    exact hwp
  | step_typeDecl => intro _ _; trivial
  | step_stmts_nil => intro _ _; trivial
  | step_stmts_cons => intro _ hwp; exact ⟨hwp.1, hwp.2⟩
  | step_seq_inner _ ih => intro labels hwp; exact ⟨ih labels hwp.1, hwp.2⟩
  | step_seq_done => intro _ hwp; exact hwp.2
  | step_seq_exit => intro _ hwp; exact hwp.1
  | step_block_body _ ih =>
    intro labels hwp
    rename_i inner inner' label σ_parent _
    cases label with
    | none => exact ih labels hwp
    | some l => exact ih (l :: labels) hwp
  | step_block_done => intro _ _; trivial
  | step_block_exit_match => intro _ _; trivial
  | step_block_exit_mismatch hne =>
    intro labels hwp
    exact block_exit_mismatch_unfold (P := P) (CmdT := CmdT) hwp hne

omit [HasOps P] [HasFvars P] [HasInt P] [HasIntOps P] in
/-- If `.block l inner →* cfg`, the inner config never reaches `.exiting`,
    and `cfg` is neither terminal nor exiting, then `cfg = .block l inner'`
    for some `inner'` with `inner →* inner'`. -/
theorem block_star_extract_inner
    {l : Option String} {σ_parent : SemanticStore P}
    {inner cfg : Config P CmdT}
    (h_star : StepStmtStar P EvalCmd (.block l σ_parent inner) cfg)
    (h_no_exit : ∀ lbl ρ', ¬ StepStmtStar P EvalCmd
        inner (.exiting lbl ρ'))
    (h_not_terminal : ∀ ρ', cfg ≠ .terminal ρ')
    (h_not_exiting : ∀ lbl ρ', cfg ≠ .exiting lbl ρ') :
    ∃ inner', cfg = .block l σ_parent inner' ∧
      StepStmtStar P EvalCmd inner inner' := by
  suffices h_gen : ∀ c₁ c₂,
      StepStmtStar P EvalCmd c₁ c₂ →
      ∀ inner₀, c₁ = .block l σ_parent inner₀ →
      (∀ lbl ρ', ¬ StepStmtStar P EvalCmd inner₀ (.exiting lbl ρ')) →
      (∀ ρ', c₂ ≠ .terminal ρ') → (∀ lbl ρ', c₂ ≠ .exiting lbl ρ') →
      ∃ inner', c₂ = .block l σ_parent inner' ∧
        StepStmtStar P EvalCmd inner₀ inner' from
    h_gen _ _ h_star _ rfl h_no_exit h_not_terminal h_not_exiting
  intro c₁ c₂ h_star
  induction h_star with
  | refl => intro inner₀ heq _ _ _; subst heq; exact ⟨inner₀, rfl, .refl _⟩
  | step _ mid _ hstep hrest ih =>
    intro inner₀ heq h_ne h_nt h_nx; subst heq
    cases hstep with
    | step_block_body h_inner_step =>
      have h_ne' : ∀ lbl ρ', ¬ StepStmtStar P EvalCmd _ (.exiting lbl ρ') :=
        fun lbl ρ' h => h_ne lbl ρ' (.step _ _ _ h_inner_step h)
      obtain ⟨inner', rfl, h_inner_star⟩ := ih _ rfl h_ne' h_nt h_nx
      exact ⟨inner', rfl, .step _ _ _ h_inner_step h_inner_star⟩
    | step_block_done =>
      cases hrest with
      | refl => exact absurd rfl (h_nt _)
      | step _ _ _ h _ => exact nomatch h
    | step_block_exit_match => exact absurd (.refl _) (h_ne _ _)
    | step_block_exit_mismatch => exact absurd (.refl _) (h_ne _ _)

/-! ## WF preservation along a run -/

variable [HasFvar P] [HasSubstFvar P] [HasBoolOps P]

omit [HasOps P] in
/-- Single step preserves `Config.wfEval` via the step's factory equality. -/
private theorem step_preserves_wfEval_wfExtend
    (c₁ c₂ : Config P CmdT)
    (hstep : StepStmt P EvalCmd c₁ c₂)
    (hwf : c₁.wfEval) :
    c₂.wfEval := by
  show WellFormedSemanticEval (P := P) c₂.getEnv.factory
  rw [← step_preserves_factory P EvalCmd _ _ hstep]
  exact hwf

omit [HasOps P] in
/-- `Config.wfEval` is preserved under `StepStmtStar`. -/
theorem star_preserves_cfg_wfEval
    {c₁ c₂ : Config P CmdT}
    (hstar : StepStmtStar P EvalCmd c₁ c₂)
    (hwf : c₁.wfEval) :
    c₂.wfEval := by
  induction hstar with
  | refl => exact hwf
  | step _ _ _ hstep _ ih =>
    exact ih (step_preserves_wfEval_wfExtend P EvalCmd _ _ hstep hwf)

omit [HasOps P] in
/-- `WellFormedSemanticEval` of the factory is preserved under `StepStmtStar`
    from a top-level `.stmt` start, using factory preservation. -/
theorem star_preserves_wfEval
    {s : Stmt P CmdT} {ρ : Env P} {c₂ : Config P CmdT}
    (hstar : StepStmtStar P EvalCmd (.stmt s ρ) c₂)
    (hwf : WellFormedSemanticEval (P := P) ρ.factory) :
    WellFormedSemanticEval (P := P) c₂.getEnv.factory := by
  have h := star_preserves_cfg_wfEval P EvalCmd hstar
    (show Config.wfEval (P := P) (CmdT := CmdT) (Config.stmt s ρ) from hwf)
  exact h

omit [HasOps P] in
/-- Block-list variant of `star_preserves_wfEval`: starting at `.stmts ss ρ`. -/
theorem star_preserves_wfEval_block
    {ss : List (Stmt P CmdT)} {ρ : Env P} {c₂ : Config P CmdT}
    (hstar : StepStmtStar P EvalCmd (.stmts ss ρ) c₂)
    (hwf : WellFormedSemanticEval (P := P) ρ.factory) :
    WellFormedSemanticEval (P := P) c₂.getEnv.factory := by
  have h := star_preserves_cfg_wfEval P EvalCmd hstar
    (show Config.wfEval (P := P) (CmdT := CmdT) (Config.stmts ss ρ) from hwf)
  exact h

end -- section

section AssertSetProps

variable {P : PureExpr} [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P]
  [HasInt P] [HasIntOps P] [HasOps P]

/-! ### Assert command properties (statement-level) -/

omit [HasFvars P] [HasInt P] [HasIntOps P] in
theorem eval_stmt_assert_store_cst :
  EvalStmtSmall P (EvalCmd P) ρ (.cmd (Cmd.assert l e md)) ρ' → ρ.store = ρ'.store := by
  intro Heval
  unfold EvalStmtSmall at Heval
  match Heval with
  | .step _ _ _ (.step_cmd hcmd) hrest =>
    cases hrest with
    | refl => exact eval_assert_store_cst hcmd
    | step _ _ _ hstep _ => exact absurd hstep (by intro h; cases h)


omit [HasFvars P] [HasInt P] [HasIntOps P] in
theorem eval_stmts_assert_store_cst :
  EvalStmtsSmall P (EvalCmd P) ρ [(.cmd (Cmd.assert l e md))] ρ' → ρ.store = ρ'.store := by
  intro Heval
  have hstmt : EvalStmtSmall P (EvalCmd P) ρ (.cmd (Cmd.assert l e md)) ρ' := by
    unfold EvalStmtsSmall at Heval
    unfold EvalStmtSmall
    match Heval with
    | .step _ _ _ .step_stmts_cons hrest =>
      have ⟨ρ₁, hterm, htail⟩ := seq_reaches_terminal P (EvalCmd P) hrest
      match htail with
      | .step _ _ _ .step_stmts_nil hrest' =>
        cases hrest' with
        | refl => exact hterm
        | step _ _ _ h _ => exact absurd h (by intro h; cases h)
  exact eval_stmt_assert_store_cst hstmt

omit [HasOps P] [HasFvars P] [HasInt P] [HasIntOps P] in
theorem eval_stmt_assert_eq_of_pure_expr_eq :
  WellFormedSemanticEvalBool (P := P) ρ.factory →
  (EvalStmtSmall P (EvalCmd P) ρ (.cmd (Cmd.assert l1 e md1)) ρ' ↔
  EvalStmtSmall P (EvalCmd P) ρ (.cmd (Cmd.assert l2 e md2)) ρ') := by
  intro Hwf
  constructor <;>
  (
    intro Heval
    unfold EvalStmtSmall at Heval ⊢
    match Heval with
    | .step _ _ _ (.step_cmd hcmd) hrest =>
      cases hrest with
      | refl =>
        cases hcmd with
        | eval_assert_pass htt _ =>
          exact .step _ _ _ (.step_cmd (EvalCmd.eval_assert_pass htt Hwf)) (.refl _)
        | eval_assert_fail hne _ =>
          exact .step _ _ _ (.step_cmd (EvalCmd.eval_assert_fail hne Hwf)) (.refl _)
      | step _ _ _ hstep _ => exact absurd hstep (by intro h; cases h)
  )

/-! ### Assert elimination -/

omit [HasOps P] [HasFvars P] [HasInt P] [HasIntOps P] in
theorem assert_elim :
  WellFormedSemanticEvalBool (P := P) ρ.factory →
  EvalStmtsSmall P (EvalCmd P) ρ (.cmd (.assert l1 e md1) :: [.cmd (.assert l2 e md2)]) ρ' →
  EvalStmtsSmall P (EvalCmd P) ρ [.cmd (.assert l3 e md3)] ρ' := by
  intro Hwf Heval
  unfold EvalStmtsSmall at Heval ⊢
  -- Invert: first assert
  match Heval with
  | .step _ _ _ .step_stmts_cons hrest =>
    have ⟨ρ₁, hterm1, htail1⟩ := seq_reaches_terminal P (EvalCmd P) hrest
    match hterm1 with
    | .step _ _ _ (.step_cmd hcmd1) (.refl _) =>
      -- Invert: second assert (from htail1 which is .stmts [assert2] ρ₁ →* .terminal ρ')
      match htail1 with
      | .step _ _ _ .step_stmts_cons hrest2 =>
        have ⟨ρ₂, hterm2, htail2⟩ := seq_reaches_terminal P (EvalCmd P) hrest2
        match hterm2 with
        | .step _ _ _ (.step_cmd hcmd2) (.refl _) =>
          match htail2 with
          | .step _ _ _ .step_stmts_nil (.refl _) =>
            cases hcmd1 with
            | eval_assert_pass h1 _ =>
              cases hcmd2 with
              | eval_assert_pass _ _ =>
                apply ReflTrans.step _ _ _ .step_stmts_cons
                apply ReflTrans.step _ _ _ (.step_seq_inner (.step_cmd (EvalCmd.eval_assert_pass h1 Hwf)))
                apply ReflTrans.step _ _ _ .step_seq_done
                apply ReflTrans.step _ _ _ .step_stmts_nil
                simp_all only [Bool.or_false]; exact .refl _
              | eval_assert_fail h2 _ =>
                exact absurd (h1.symm.trans h2)
                  (by exact fun h => HasBool.tt_is_not_ff (Option.some.inj h))
            | eval_assert_fail h1 _ =>
              cases hcmd2 with
              | eval_assert_pass h2 _ =>
                simp at h2
                exact absurd (h2.symm.trans h1)
                  (by exact fun h => HasBool.tt_is_not_ff (Option.some.inj h))
              | eval_assert_fail _ _ =>
                apply ReflTrans.step _ _ _ .step_stmts_cons
                apply ReflTrans.step _ _ _ (.step_seq_inner (.step_cmd (EvalCmd.eval_assert_fail h1 Hwf)))
                apply ReflTrans.step _ _ _ .step_seq_done
                apply ReflTrans.step _ _ _ .step_stmts_nil
                simp_all only [Bool.or_true, Bool.or_self]; exact .refl _

/-! ### Set command commutation -/

omit [HasFvars P] [HasInt P] [HasIntOps P] in
theorem eval_stmt_set_comm
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasFvars P]
  [DecidableEq P.Ident]:
  WellFormedSemanticEvalExprCongr (P := P) ρ.factory →
  WellFormedStore ρ.store ρ.factory →
  WellFormedStore ρ1.store ρ.factory →
  WellFormedStore ρ2.store ρ.factory →
  ¬ x1 = x2 →
  ¬ x1 ∈ HasFvars.getFvars v2 →
  ¬ x2 ∈ HasFvars.getFvars v1 →
  EvalStmtSmall P (EvalCmd P) ρ (.cmd (Cmd.set x1 (.det v1) md1)) ρ1 →
  EvalStmtSmall P (EvalCmd P) ρ1 (.cmd (Cmd.set x2 (.det v2) md2)) ρ' →
  EvalStmtSmall P (EvalCmd P) ρ (.cmd (Cmd.set x2 (.det v2) md2')) ρ2 →
  EvalStmtSmall P (EvalCmd P) ρ2 (.cmd (Cmd.set x1 (.det v1) md1')) ρ'' →
  ρ'.store = ρ''.store := by
  intro Hwf Hwfs Hwfs1 Hwfs2 Hneq Hnin1 Hnin2 Hs1 Hs2 Hs3 Hs4
  unfold EvalStmtSmall at Hs1 Hs2 Hs3 Hs4
  match Hs1, Hs2, Hs3, Hs4 with
  | .step _ _ _ (.step_cmd Hc1) (.refl _),
    .step _ _ _ (.step_cmd Hc2) (.refl _),
    .step _ _ _ (.step_cmd Hc3) (.refl _),
    .step _ _ _ (.step_cmd Hc4) (.refl _) =>
    exact eval_cmd_set_comm Hwf Hwfs Hwfs1 Hwfs2 Hneq Hnin1 Hnin2 Hc1 Hc2 Hc3 Hc4

omit [HasInt P] [HasIntOps P] in
theorem eval_stmts_set_comm
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
  [DecidableEq P.Ident] :
  WellFormedSemanticEvalExprCongr (P := P) ρ.factory →
  WellFormedStore ρ.store ρ.factory →
  (∀ ρ_mid, EvalStmtSmall P (EvalCmd P) ρ (.cmd (Cmd.set x1 (.det v1) md1)) ρ_mid →
    WellFormedStore ρ_mid.store ρ.factory) →
  (∀ ρ_mid, EvalStmtSmall P (EvalCmd P) ρ (.cmd (Cmd.set x2 (.det v2) md2')) ρ_mid →
    WellFormedStore ρ_mid.store ρ.factory) →
  ¬ x1 = x2 →
  ¬ x1 ∈ HasFvars.getFvars v2 →
  ¬ x2 ∈ HasFvars.getFvars v1 →
  EvalStmtsSmall P (EvalCmd P) ρ [(.cmd (Cmd.set x1 (.det v1) md1)), (.cmd (Cmd.set x2 (.det v2) md2))] ρ' →
  EvalStmtsSmall P (EvalCmd P) ρ [(.cmd (Cmd.set x2 (.det v2) md2')), (.cmd (Cmd.set x1 (.det v1) md1'))] ρ'' →
  ρ'.store = ρ''.store := by
  intro Hwf Hwfs Hwfs1 Hwfs2 Hneq Hnin1 Hnin2 Heval1 Heval2
  have extract := fun (s1 s2 : Stmt P (Cmd P)) (ρ₀ ρ_final : Env P)
      (h : EvalStmtsSmall P (EvalCmd P) ρ₀ [s1, s2] ρ_final) =>
    show ∃ ρ_mid, EvalStmtSmall P (EvalCmd P) ρ₀ s1 ρ_mid ∧
        EvalStmtSmall P (EvalCmd P) ρ_mid s2 ρ_final from by
      unfold EvalStmtsSmall EvalStmtSmall at *
      match h with
      | .step _ _ _ .step_stmts_cons hrest =>
        have ⟨ρ₁, hterm1, htail1⟩ := seq_reaches_terminal P (EvalCmd P) hrest
        match htail1 with
        | .step _ _ _ .step_stmts_cons hrest2 =>
          have ⟨ρ₂, hterm2, htail2⟩ := seq_reaches_terminal P (EvalCmd P) hrest2
          match htail2 with
          | .step _ _ _ .step_stmts_nil (.refl _) =>
            exact ⟨ρ₁, hterm1, hterm2⟩
  have ⟨ρ_m1, Hs1, Hs2⟩ := extract _ _ _ _ Heval1
  have ⟨ρ_m2, Hs3, Hs4⟩ := extract _ _ _ _ Heval2
  exact eval_stmt_set_comm Hwf Hwfs (Hwfs1 _ Hs1) (Hwfs2 _ Hs3) Hneq Hnin1 Hnin2 Hs1 Hs2 Hs3 Hs4

end AssertSetProps

/-! ## `ReflTransT` decomposition helpers

Structural inversion lemmas for multi-step derivations indexed in `Type`
(so step counts can be used by `termination_by`).  Generic over `CmdT`
and the command-evaluation parameter. -/

section ReflTransTHelpers

variable {P : PureExpr} {CmdT : Type}
  [HasFvars P] [HasBool P] [HasInt P] [HasIntOps P] [HasOps P]
  {EvalCmd : EvalCmdParam P CmdT}


omit [HasOps P] [HasFvars P] [HasInt P] [HasIntOps P] in
/-- Invert a `.seq` execution reaching terminal in `ReflTransT`: the inner
    terminates first, then the tail stmts run to terminal.  Length bound
    is strict so callers can recurse on `hstar.len`. -/
theorem seqT_reaches_terminal
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)} {ρ' : Env P}
    (hstar : ReflTransT (StepStmt P EvalCmd) (.seq inner ss) (.terminal ρ')) :
    ∃ (ρ₁ : Env P), ∃ (h1 : ReflTransT (StepStmt P EvalCmd) inner (.terminal ρ₁)),
      ∃ (h2 : ReflTransT (StepStmt P EvalCmd) (.stmts ss ρ₁) (.terminal ρ')),
      h1.len + h2.len < hstar.len := by
  match hstar with
  | .step _ _ _ (.step_seq_inner h) hrest =>
    have ⟨ρ₁, hterm, htail, hlen⟩ := seqT_reaches_terminal hrest
    exact ⟨ρ₁, .step _ _ _ h hterm, htail, by simp [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_seq_done hrest =>
    exact ⟨_, .refl _, hrest, by show 0 + hrest.len < 1 + hrest.len; omega⟩
  | .step _ _ _ .step_seq_exit hrest =>
    match hrest with
    | .step _ _ _ h _ => exact nomatch h

omit [HasOps P] [HasFvars P] [HasInt P] [HasIntOps P] in
/-- Invert a `.stmts (s :: rest)` execution reaching terminal in `ReflTransT`. -/
theorem stmtsT_cons_terminal
    {s : Stmt P CmdT} {rest : List (Stmt P CmdT)} {ρ₀ ρ' : Env P}
    (hstar : ReflTransT (StepStmt P EvalCmd) (.stmts (s :: rest) ρ₀) (.terminal ρ')) :
    ∃ (ρ₁ : Env P), ∃ (h1 : ReflTransT (StepStmt P EvalCmd) (.stmt s ρ₀) (.terminal ρ₁)),
      ∃ (h2 : ReflTransT (StepStmt P EvalCmd) (.stmts rest ρ₁) (.terminal ρ')),
      h1.len + h2.len + 2 ≤ hstar.len := by
  match hstar with
  | .step _ _ _ .step_stmts_cons hrest =>
    have ⟨ρ₁, h1, h2, hlen⟩ := seqT_reaches_terminal hrest
    exact ⟨ρ₁, h1, h2, by simp [ReflTransT.len]; omega⟩

omit [HasOps P] [HasFvars P] [HasInt P] [HasIntOps P] in
/-- Decompose `.stmts (ss₁ ++ [s])` reaching terminal into: a full `.stmts ss₁`
    run to some intermediate `ρ₁` followed by a strictly shorter `s`-run.
    The escape-free hypothesis `hcov` rules out the exiting case. -/
theorem stmtsT_append_terminal
    (ss₁ : List (Stmt P CmdT)) (s : Stmt P CmdT) (ρ₀ ρ' : Env P)
    (hstar : ReflTransT (StepStmt P EvalCmd) (.stmts (ss₁ ++ [s]) ρ₀) (.terminal ρ'))
    (hcov : Block.exitsCoveredByBlocks (P := P) (CmdT := CmdT) [] ss₁) :
    ∃ (ρ₁ : Env P), ∃ (_ : StepStmtStar P EvalCmd (.stmts ss₁ ρ₀) (.terminal ρ₁)),
      ∃ (hs : ReflTransT (StepStmt P EvalCmd) (.stmt s ρ₁) (.terminal ρ')),
      hs.len < hstar.len := by
  induction ss₁ generalizing ρ₀ with
  | nil =>
    have ⟨ρ₁, h1, h2, hlen⟩ := stmtsT_cons_terminal hstar
    have hρ : ρ₁ = ρ' := by
      match h2 with
      | .step _ _ _ .step_stmts_nil (.refl _) => rfl
    subst hρ
    exact ⟨ρ₀, .step _ _ _ .step_stmts_nil (.refl _), h1, by grind⟩
  | cons s' rest' ih =>
    have ⟨ρ₁, h_s', h_rest, hlen₁⟩ := stmtsT_cons_terminal hstar
    have ⟨ρ₂, h_rest', h_s, hlen₂⟩ := ih ρ₁ h_rest hcov.2
    have hle : h_rest.len ≤ hstar.len := by
      have hb : h_rest.len ≤ h_s'.len + h_rest.len + 2 := by omega
      exact Nat.le_trans hb hlen₁
    exact ⟨ρ₂,
      ReflTrans_Transitive _ _ _ _
        (stmts_cons_step P EvalCmd s' rest' ρ₀ ρ₁ (reflTransT_to_prop h_s'))
        h_rest',
      h_s, Nat.lt_of_lt_of_le hlen₂ hle⟩

end ReflTransTHelpers

/-! ## Factory preservation -/

/-! ### Store-projection and environment-extension helpers

The `StoreAgreement` projection helpers and the classified-extension lemmas
for `projectStore` and `Env.ExtendsWith` are consumed by the loop-init-hoist
and structured-to-unstructured correctness proofs.  They live here so the
several downstream transform proofs share one copy. -/

/-- The projected inner store agrees with the unprojected inner store on
`σ_parent`'s domain. Variables present in the parent are unchanged by
projection; variables absent from the parent become `none` in the projection,
but those don't satisfy `isDefined (projectStore _ _) [x]`, so
`StoreAgreement` doesn't constrain them. -/
theorem StoreAgreement.of_projectStore {P : PureExpr}
    (σ_parent σ_inner : SemanticStore P) :
    StoreAgreement (projectStore σ_parent σ_inner) σ_inner := by
  intro x h_def
  have h := h_def x (List.mem_singleton.mpr rfl)
  unfold projectStore at h ⊢
  by_cases hp : (σ_parent x).isSome
  · simp [hp]
  · simp [hp] at h

namespace StoreExtendsWith

/-- Projecting related inner stores through related parent stores preserves
classified extension. -/
theorem projectStore {P : PureExpr} {Extra : P.Ident → Prop}
    {sourceParent targetParent sourceInner targetInner : SemanticStore P}
    (hparent : StoreExtendsWith Extra sourceParent targetParent)
    (hinner : StoreExtendsWith Extra sourceInner targetInner) :
    StoreExtendsWith Extra
      (Imperative.projectStore sourceParent sourceInner)
      (Imperative.projectStore targetParent targetInner) := by
  refine ⟨?_, ?_⟩
  · intro ident hdefined
    have hsourceSome :
        (Imperative.projectStore sourceParent sourceInner ident).isSome = true :=
      hdefined ident (List.mem_singleton.mpr rfl)
    simp only [Imperative.projectStore] at hsourceSome ⊢
    by_cases hsp : (sourceParent ident).isSome
    · rw [ite_eq_left hsp] at hsourceSome ⊢
      have hparentEq : sourceParent ident = targetParent ident :=
        hparent.1 ident (fun x hx => by
          simpa [List.mem_singleton.mp hx] using hsp)
      have htp : (targetParent ident).isSome := by
        rw [← hparentEq]
        exact hsp
      rw [ite_eq_left htp]
      exact hinner.1 ident (fun x hx => by
        simpa [List.mem_singleton.mp hx] using hsourceSome)
    · rw [ite_eq_right hsp] at hsourceSome
      simp at hsourceSome
  · intro ident htargetSome
    simp only [Imperative.projectStore] at htargetSome ⊢
    by_cases htp : (targetParent ident).isSome
    · rw [ite_eq_left htp] at htargetSome
      rcases hparent.2 ident htp with hsp | hextra
      · rcases hinner.2 ident htargetSome with hsi | hextra
        · rw [ite_eq_left hsp]
          exact Or.inl hsi
        · exact Or.inr hextra
      · exact Or.inr hextra
    · rw [ite_eq_right htp] at htargetSome
      simp at htargetSome

end StoreExtendsWith

namespace Env.ExtendsWith

/-- Every environment extends itself. -/
theorem refl {P : PureExpr} (Extra : P.Ident → Prop) (env : Env P) :
    env.ExtendsWith Extra env :=
  ⟨rfl, rfl, StoreExtendsWith.refl Extra _⟩

/-- Environment extension composes while unioning extra-register classes. -/
theorem trans_union {P : PureExpr} {Extra₁ Extra₂ : P.Ident → Prop}
    {source middle target : Env P}
    (h₁ : source.ExtendsWith Extra₁ middle)
    (h₂ : middle.ExtendsWith Extra₂ target) :
    source.ExtendsWith (fun ident => Extra₁ ident ∨ Extra₂ ident) target :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1,
   StoreExtendsWith.trans_union h₁.2.2 h₂.2.2⟩

end Env.ExtendsWith

/-- **Two-parent `projectStore` survival for `StoreAgreement`.**  Agreeing parents
+ agreeing inner stores ⟹ the block-projected stores agree (a projected key is
either parent-defined, where the inner stores agree, or parent-undefined, where
both projections are `none`).  Re-establishes agreement across each loop
iteration's `projectStore` boundary. -/
theorem StoreAgreement.of_projectStore_parents {P : PureExpr}
    {σp_src σp_tgt σi_src σi_tgt : SemanticStore P}
    (h_par : StoreAgreement σp_src σp_tgt)
    (h_inn : StoreAgreement σi_src σi_tgt) :
    StoreAgreement (projectStore σp_src σi_src) (projectStore σp_tgt σi_tgt) := by
  intro x h_def
  have h := h_def x (List.mem_singleton.mpr rfl)
  simp only [projectStore] at h ⊢
  by_cases hp : (σp_src x).isSome
  · rw [ite_eq_left hp] at h ⊢
    have h_inn_x : σi_src x = σi_tgt x :=
      h_inn x (fun z hz => by simpa [List.mem_singleton.mp hz] using h)
    have h_par_x : σp_src x = σp_tgt x :=
      h_par x (fun z hz => by simpa [List.mem_singleton.mp hz] using hp)
    have hpt : (σp_tgt x).isSome := by rw [← h_par_x]; exact hp
    rw [ite_eq_left hpt, h_inn_x]
  · rw [ite_eq_right hp] at h; simp at h

/-- When every read-var of `e` is defined in the source store, `StoreAgreement`
pins the two stores to equal values on those vars.  No freshness side-condition
is needed — a source-defined var is exactly where `StoreAgreement` constrains the
target. -/
theorem storeAgreement_pointwise_on_expr_vars {P : PureExpr}
    [HasFvars P]
    (σ_src σ_tgt : SemanticStore P) (e : P.Expr)
    (h_agree : StoreAgreement σ_src σ_tgt)
    (h_def : isDefined σ_src (HasFvars.getFvars e)) :
    ∀ x ∈ HasFvars.getFvars e, σ_src x = σ_tgt x :=
  fun x hx => h_agree x (fun z hz => by
    simpa [List.mem_singleton.mp hz] using h_def x hx)

/-! ## Structured small-step run inversions and singleton/seq/block helpers

Generic `StepStmtStar`/`ReflTrans` decomposition and lifting lemmas over the statement small-step semantics, consumed by multiple pass-correctness proofs. -/

/-- A terminating empty statement list leaves the environment unchanged. -/
theorem stmts_nil_terminal_eq {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    (ρ ρ' : Env P)
    (h : StepStmtStar P (EvalCmd P) (.stmts [] ρ) (.terminal ρ')) :
    ρ = ρ' := by
  cases h with
  | step _ _ _ hstep hrest =>
    cases hstep with
    | step_stmts_nil =>
      cases hrest with
      | refl => rfl
      | step _ _ _ h _ => cases h

/-- A single statement that runs to terminal also runs to terminal when wrapped
as a singleton statement list.  This is the bridge from the `.stmt s` shape of
the source-side step rules to the `.stmts [s]` shape that the pass emits for the
pass-through `.cmd` arm. -/
theorem stmt_to_singleton_stmts {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    (s : Stmt P (Cmd P)) (ρ ρ' : Env P)
    (h : StepStmtStar P (EvalCmd P) (.stmt s ρ) (.terminal ρ')) :
    StepStmtStar P (EvalCmd P) (.stmts [s] ρ) (.terminal ρ') :=
  ReflTrans_Transitive _ _ _ _
    (stmts_cons_step P (EvalCmd P) s [] ρ ρ' h)
    (evalStmtsSmallNil P (EvalCmd P) ρ')

/-- Exiting variant of `stmt_to_singleton_stmts`: a single statement exiting
yields the singleton list exiting. -/
theorem stmt_to_singleton_stmts_exiting {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    (s : Stmt P (Cmd P)) (ρ ρ' : Env P) (lbl : String)
    (h : StepStmtStar P (EvalCmd P) (.stmt s ρ) (.exiting lbl ρ')) :
    StepStmtStar P (EvalCmd P) (.stmts [s] ρ) (.exiting lbl ρ') := by
  refine .step _ _ _ .step_stmts_cons ?_
  refine ReflTrans_Transitive _ _ _ _ (seq_inner_star P (EvalCmd P) _ _ [] h) ?_
  exact .step _ _ _ .step_seq_exit (.refl _)

/-- Outcome-generic variant of `stmt_to_singleton_stmts`: a single statement
reaching `Env.outcomeConfig oc ρ'` yields the singleton list reaching the same
outcome. -/
theorem stmt_to_singleton_stmts_outcome {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    (s : Stmt P (Cmd P)) (ρ ρ' : Env P) (oc : Option String)
    (h : StepStmtStar P (EvalCmd P) (.stmt s ρ) (Env.outcomeConfig oc ρ')) :
    StepStmtStar P (EvalCmd P) (.stmts [s] ρ) (Env.outcomeConfig oc ρ') := by
  cases oc with
  | none => exact stmt_to_singleton_stmts s ρ ρ' h
  | some lbl => exact stmt_to_singleton_stmts_exiting s ρ ρ' lbl h

/-- Outcome-generic decomposition of `.stmts (s :: rest)`: a run reaching
`Env.outcomeConfig oc ρ'` either (a) had the head `s` exit (so `oc = some lbl` and
the whole list exits with that label, skipping `rest`), or (b) had `s` terminate
to some `ρ_mid` after which `rest` reached the same outcome. -/
theorem stmts_cons_outcome {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    (s : Stmt P (Cmd P)) (rest : List (Stmt P (Cmd P))) (ρ ρ' : Env P) (oc : Option String)
    (h : StepStmtStar P (EvalCmd P) (.stmts (s :: rest) ρ) (Env.outcomeConfig oc ρ')) :
    (∃ lbl, oc = some lbl ∧
        StepStmtStar P (EvalCmd P) (.stmt s ρ) (.exiting lbl ρ')) ∨
    (∃ ρ_mid, StepStmtStar P (EvalCmd P) (.stmt s ρ) (.terminal ρ_mid) ∧
        StepStmtStar P (EvalCmd P) (.stmts rest ρ_mid) (Env.outcomeConfig oc ρ')) := by
  -- Reduce `Env.outcomeConfig` to a concrete constructor before inverting the run,
  -- so dependent elimination on the `.stmts (s :: rest)` head step succeeds.
  cases oc with
  | none =>
    simp only [Env.outcomeConfig] at h ⊢
    cases h with
    | step _ _ _ hstep hrest =>
      cases hstep with
      | step_stmts_cons =>
        have ⟨ρ_mid, h_s, h_tail⟩ := seq_reaches_terminal P (EvalCmd P) hrest
        exact .inr ⟨ρ_mid, h_s, h_tail⟩
  | some lbl =>
    simp only [Env.outcomeConfig] at h ⊢
    cases h with
    | step _ _ _ hstep hrest =>
      cases hstep with
      | step_stmts_cons =>
        rcases seq_reaches_exiting P (EvalCmd P) hrest with
          h_s | ⟨ρ_mid, h_s, h_tail⟩
        · exact .inl ⟨lbl, rfl, h_s⟩
        · exact .inr ⟨ρ_mid, h_s, h_tail⟩

/-- Forward: if a prefix list `pfx` exits with `lbl`, then `pfx ++ sfx` exits
with `lbl` (the suffix is skipped). -/
theorem stmts_cons_head_exiting_append {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    (pfx sfx : List (Stmt P (Cmd P))) (ρ ρ' : Env P) (lbl : String)
    (h : StepStmtStar P (EvalCmd P) (.stmts pfx ρ) (.exiting lbl ρ')) :
    StepStmtStar P (EvalCmd P) (.stmts (pfx ++ sfx) ρ) (.exiting lbl ρ') := by
  induction pfx generalizing ρ with
  | nil =>
    -- `.stmts [] ρ` cannot exit.
    exfalso
    cases h with
    | step _ _ _ hstep hrest =>
      cases hstep with
      | step_stmts_nil => cases hrest with | step _ _ _ h _ => cases h
  | cons s rest ih =>
    cases h with
    | step _ _ _ hstep hrest =>
      cases hstep with
      | step_stmts_cons =>
        rcases seq_reaches_exiting P (EvalCmd P) hrest with
          h_s | ⟨ρ₁, h_term, h_tail⟩
        · -- head `s` exits: lift through `step_stmts_cons`/`step_seq_exit`.
          refine .step _ _ _ .step_stmts_cons ?_
          refine ReflTrans_Transitive _ _ _ _
            (seq_inner_star P (EvalCmd P) _ _ (rest ++ sfx) h_s) ?_
          exact .step _ _ _ .step_seq_exit (.refl _)
        · -- head terminates to ρ₁, recurse on `rest`.
          exact ReflTrans_Transitive _ _ _ _
            (stmts_cons_step P (EvalCmd P) s (rest ++ sfx) ρ ρ₁ h_term)
            (ih ρ₁ h_tail)

/-- Reading a free-variable expression out of any store where its variable maps
to a *value* `b` yields exactly `b`.  The proof evaluates in a minimal
well-formed store and extends to an arbitrary one via `WellFormedSemanticEvalVar`
and `WellFormedSemanticEvalMono`.  Stated over any `e` that `getFvar` reads as
`ident`, so it serves an annotated variable as well as a bare one. -/
theorem eval_fvarExpr_of_value {P : PureExpr} [HasVal P] [HasFvar P] [DecidableEq P.Ident] [HasOps P] [LawfulHasFvar P]
    (δ : P.Factory) (σ : SemanticStore P) (ident : P.Ident) (e b : P.Expr)
    (hfv : HasFvar.getFvar e = some ident)
    (hval : HasVal.value δ b)
    (h_def : σ ident = some b)
    (hwf_var : WellFormedSemanticEvalVar δ)
    (hwf_mono : WellFormedSemanticEvalMono δ) :
    P.eval δ σ e = some b := by
  let σ₀ : SemanticStore P := fun y => if y = ident then some b else none
  have hwf₀ : WellFormedStore σ₀ δ := by
    intro x v hx
    simp only [σ₀] at hx
    by_cases hxi : x = ident
    · rw [ite_eq_left hxi] at hx
      have : b = v := Option.some.inj hx
      subst this; exact hval
    · rw [ite_eq_right hxi] at hx; exact absurd hx (by simp)
  have h₀ : P.eval δ σ₀ e = some b := by
    have h := hwf_var e ident σ₀ hwf₀ hfv
    rw [h]; simp only [σ₀, ite_eq_left rfl]
  refine hwf_mono _ _ σ₀ σ ?_ h₀
  intro x w hx
  simp only [σ₀] at hx
  by_cases hxi : x = ident
  · rw [ite_eq_left hxi] at hx
    have : b = w := Option.some.inj hx
    subst this; rw [hxi]; exact h_def
  · rw [ite_eq_right hxi] at hx; exact absurd hx (by simp)

/-- Reading a bare free-variable expression `mkFvar ident` from a store that maps
`ident` to a value yields that value. -/
theorem eval_mkFvar_of_value {P : PureExpr} [HasVal P] [HasFvar P] [DecidableEq P.Ident] [HasOps P] [LawfulHasFvar P]
    (δ : P.Factory) (σ : SemanticStore P) (ident : P.Ident) (b : P.Expr)
    (hval : HasVal.value δ b)
    (h_def : σ ident = some b)
    (hwf_var : WellFormedSemanticEvalVar δ)
    (hwf_mono : WellFormedSemanticEvalMono δ) :
    P.eval δ σ (HasFvar.mkFvar ident) = some b :=
  eval_fvarExpr_of_value δ σ ident _ b (LawfulHasFvar.getFvar_mkFvar ident)
    hval h_def hwf_var hwf_mono

/-- Evaluating a type-annotated free variable in a store that holds a value for it
yields that value: the annotation does not affect the lookup. -/
theorem eval_mkTypedFvar_of_value {P : PureExpr} [HasVal P] [HasFvar P] [DecidableEq P.Ident] [HasOps P] [LawfulHasFvar P]
    {ty : P.Ty} (δ : P.Factory) (σ : SemanticStore P) (ident : P.Ident) (b : P.Expr)
    (hval : HasVal.value δ b)
    (h_def : σ ident = some b)
    (hwf_var : WellFormedSemanticEvalVar δ)
    (hwf_mono : WellFormedSemanticEvalMono δ) :
    P.eval δ σ (HasFvar.mkTypedFvar ident ty) = some b :=
  eval_fvarExpr_of_value δ σ ident _ b (LawfulHasFvar.getFvar_mkTypedFvar ident ty)
    hval h_def hwf_var hwf_mono

/-- Evaluating a free-variable expression in a store just updated at the variable
that expression denotes yields the value written there, given a well-formed
evaluator. -/
theorem eval_fvarExpr_storeWith {P : PureExpr} [HasVal P] [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasOps P] [LawfulHasFvar P]
    (δ : P.Factory) (σ : SemanticStore P) (ident : P.Ident) (e b : P.Expr)
    (hfv : HasFvar.getFvar e = some ident)
    (hval : HasVal.value δ b)
    (hwf_var : WellFormedSemanticEvalVar δ)
    (hwf_mono : WellFormedSemanticEvalMono δ) :
    P.eval δ (SemanticStore.update σ ident b) e = some b :=
  eval_fvarExpr_of_value δ (SemanticStore.update σ ident b) ident e b hfv hval
    (by simp [SemanticStore.update]) hwf_var hwf_mono

/-- Evaluating a bare free variable in a store just updated at that variable
yields the value written there. -/
theorem eval_mkFvar_storeWith {P : PureExpr} [HasVal P] [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasOps P] [LawfulHasFvar P]
    (δ : P.Factory) (σ : SemanticStore P) (ident : P.Ident) (b : P.Expr)
    (hval : HasVal.value δ b)
    (hwf_var : WellFormedSemanticEvalVar δ)
    (hwf_mono : WellFormedSemanticEvalMono δ) :
    P.eval δ (SemanticStore.update σ ident b) (HasFvar.mkFvar ident) = some b :=
  eval_fvarExpr_storeWith δ σ ident _ b (LawfulHasFvar.getFvar_mkFvar ident)
    hval hwf_var hwf_mono

/-- Evaluating a type-annotated free variable in a store just updated at that
variable yields the value written there: the annotation does not affect the
lookup. -/
theorem eval_mkTypedFvar_storeWith {P : PureExpr} [HasVal P] [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasOps P] [LawfulHasFvar P]
    {ty : P.Ty} (δ : P.Factory) (σ : SemanticStore P) (ident : P.Ident) (b : P.Expr)
    (hval : HasVal.value δ b)
    (hwf_var : WellFormedSemanticEvalVar δ)
    (hwf_mono : WellFormedSemanticEvalMono δ) :
    P.eval δ (SemanticStore.update σ ident b) (HasFvar.mkTypedFvar ident ty) = some b :=
  eval_fvarExpr_storeWith δ σ ident _ b
    (LawfulHasFvar.getFvar_mkTypedFvar ident ty) hval hwf_var hwf_mono

/-! ### Agreement-preserving replay of a single source command

A source-side `EvalCmd c σ_src₀ σ_src₁ failed` can be replayed on a target store
`σ_tgt₀` that agrees with `σ_src₀` (in the `StoreAgreement` sense), producing a
`σ_tgt₁` that agrees with `σ_src₁`.  This is the workhorse of the pass-through
`.cmd` arm: the rewrite is the identity on `.cmd`, so the target replays the
exact same command, and we only need that the command's evaluation depends on
the store solely through the source-visible part. -/

/-- Invert a single `.stmt s` execution to terminal: the first step is
`step_stmts_cons`-free; `s` itself steps to some `c`, then `c →* terminal`. -/
theorem stmt_step_first_inv {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] (s : Stmt P (Cmd P)) (ρ ρ' : Env P)
    (h : StepStmtStar P (EvalCmd P) (.stmt s ρ) (.terminal ρ')) :
    ∃ c, StepStmt P (EvalCmd P) (.stmt s ρ) c ∧
      StepStmtStar P (EvalCmd P) c (.terminal ρ') := by
  cases h with
  | step _ mid _ hstep hrest => exact ⟨mid, hstep, hrest⟩

/-! ## Single-outcome reachability classifiers

Three-way terminal/exiting/stuck inversions of a small-step run started from a
`.cmd`, `.exit`, or `.typeDecl` config. -/

/-- Inversion of a small-step run started from a `.cmd c` config: it is either still
at the start config, or has taken the single command step to a terminal config. -/
theorem cmd_run_outcome {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [DecidableEq P.Ident]
    {c : Cmd P} {ρ : Env P} {d : Config P (Cmd P)}
    (h_run : StepStmtStar P (EvalCmd P) (.stmt (.cmd c) ρ) d) :
    (∃ ρ', d = .terminal ρ') ∨ (∃ l ρ', d = .exiting l ρ') ∨ d = .stmt (.cmd c) ρ := by
  cases h_run with
  | refl => exact Or.inr (Or.inr rfl)
  | step _ _ _ h1 hr1 =>
    cases h1 with
    | step_cmd hev =>
      cases hr1 with
      | refl => exact Or.inl ⟨_, rfl⟩
      | step _ _ _ hd _ => exact nomatch hd

/-- Inversion of a small-step run started from an `.exit lbl` config: it is either still
at the start config, or has taken the single exit step to an `.exiting lbl` config
(a terminal config is also admitted by the disjunction). -/
theorem exit_run_outcome {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [DecidableEq P.Ident]
    {lbl : String} {md : MetaData P} {ρ : Env P} {d : Config P (Cmd P)}
    (h_run : StepStmtStar P (EvalCmd P) (.stmt (.exit lbl md) ρ) d) :
    (∃ ρ', d = .terminal ρ') ∨ (∃ l ρ', d = .exiting l ρ') ∨ d = .stmt (.exit lbl md) ρ := by
  cases h_run with
  | refl => exact Or.inr (Or.inr rfl)
  | step _ _ _ h1 hr1 =>
    cases h1
    cases hr1 with
    | refl => exact Or.inr (Or.inl ⟨_, _, rfl⟩)
    | step _ _ _ hd _ => exact nomatch hd

/-- Inversion of a small-step run started from a `.typeDecl` config: it is either still
at the start config or has stepped to a terminal config (`.typeDecl` performs no exit). -/
theorem typeDecl_run_outcome {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [DecidableEq P.Ident]
    {tc : TypeConstructor} {md : MetaData P} {ρ : Env P} {d : Config P (Cmd P)}
    (h_run : StepStmtStar P (EvalCmd P) (.stmt (.typeDecl tc md) ρ) d) :
    (∃ ρ', d = .terminal ρ') ∨ (∃ l ρ', d = .exiting l ρ') ∨ d = .stmt (.typeDecl tc md) ρ := by
  cases h_run with
  | refl => exact Or.inr (Or.inr rfl)
  | step _ _ _ h1 hr1 =>
    cases h1
    cases hr1 with
    | refl => exact Or.inl ⟨_, rfl⟩
    | step _ _ _ hd _ => exact nomatch hd

/-- A `.seq` whose inner config runs to terminal and whose continuation list is
empty itself runs to that same terminal.  (The trailing `step_seq_done` lands on
`.stmts [] ρ'`, which is one `step_stmts_nil` from `.terminal ρ'`.) -/
theorem seq_nil_terminal {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    (inner : Config P (Cmd P)) (ρ' : Env P)
    (h : StepStmtStar P (EvalCmd P) inner (.terminal ρ')) :
    StepStmtStar P (EvalCmd P) (.seq inner []) (.terminal ρ') := by
  have h1 : StepStmtStar P (EvalCmd P) (.seq inner []) (.seq (.terminal ρ') []) :=
    seq_inner_star P (EvalCmd P) _ _ [] h
  refine ReflTrans_Transitive _ _ _ _ h1 ?_
  refine .step _ _ _ .step_seq_done ?_
  exact evalStmtsSmallNil P (EvalCmd P) ρ'

/-- Outcome-generic `.seq inner []`: if `inner` reaches `Env.outcomeConfig oc ρ'`,
the seq with empty continuation reaches the same outcome (terminal flows through
`step_seq_done`; exiting flows through `step_seq_exit`). -/
theorem seq_nil_outcome {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    (inner : Config P (Cmd P)) (ρ' : Env P) (oc : Option String)
    (h : StepStmtStar P (EvalCmd P) inner (Env.outcomeConfig oc ρ')) :
    StepStmtStar P (EvalCmd P) (.seq inner []) (Env.outcomeConfig oc ρ') := by
  cases oc with
  | none => exact seq_nil_terminal inner ρ' h
  | some lbl =>
    have h1 : StepStmtStar P (EvalCmd P) (.seq inner []) (.seq (.exiting lbl ρ') []) :=
      seq_inner_star P (EvalCmd P) _ _ [] h
    refine ReflTrans_Transitive _ _ _ _ h1 ?_
    exact .step _ _ _ .step_seq_exit (.refl _)

/-! ### Anonymous-block / seq / ite structural inversions (outcome-generic)

Generic `StepStmt`/`ReflTransT` inversions for `.block .none` / `.seq` / nondet-`ite`
reaching a terminal or exiting outcome, consumed by multiple pass-correctness proofs. -/

/-- Type-valued inversion of a `.seq inner ss` run reaching `.exiting lbl`:
either the inner config exits (skipping `ss`), or the inner config terminates
and `ss` reaches the exiting outcome.  Both pieces carry a strict len-decrease. -/
theorem seqT_reaches_exiting {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    {inner : Config P (Cmd P)} {ss : List (Stmt P (Cmd P))} {lbl : String} {ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P)) (.seq inner ss) (.exiting lbl ρ')) :
    (∃ (h : ReflTransT (StepStmt P (EvalCmd P)) inner (.exiting lbl ρ')),
        h.len < hstar.len) ∨
    (∃ (ρ₁ : Env P)
        (h1 : ReflTransT (StepStmt P (EvalCmd P)) inner (.terminal ρ₁))
        (h2 : ReflTransT (StepStmt P (EvalCmd P)) (.stmts ss ρ₁) (.exiting lbl ρ')),
        h1.len + h2.len < hstar.len) := by
  match hstar with
  | .step _ _ _ (.step_seq_inner h) hrest =>
    rcases seqT_reaches_exiting hrest with ⟨hexit, hlen⟩ | ⟨ρ₁, h1, h2, hlen⟩
    · exact .inl ⟨.step _ _ _ h hexit, by simp only [ReflTransT.len]; omega⟩
    · exact .inr ⟨ρ₁, .step _ _ _ h h1, h2, by simp only [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_seq_done hrest =>
    exact .inr ⟨_, .refl _, hrest, by simp only [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_seq_exit hrest =>
    exact .inl ⟨hrest, by simp only [ReflTransT.len]; omega⟩

/-- Type-valued inversion of a singleton statement-list `[s]` reaching
`.exiting lbl`: the head statement reaches the exiting outcome, with a strict
len-decrease (the `step_stmts_cons` administrative step). -/
theorem stmtsT_singleton_exiting {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    {s : Stmt P (Cmd P)} {lbl : String} {ρ₀ ρ' : Env P}
    (hstar : ReflTransT (StepStmt P (EvalCmd P)) (.stmts [s] ρ₀) (.exiting lbl ρ')) :
    ∃ (h : ReflTransT (StepStmt P (EvalCmd P)) (.stmt s ρ₀) (.exiting lbl ρ')),
      h.len < hstar.len := by
  match hstar with
  | .step _ _ _ .step_stmts_cons hrest =>
    rcases seqT_reaches_exiting hrest with ⟨hexit, hlen⟩ | ⟨ρ₁, _, h2, hlen⟩
    · exact ⟨hexit, by simp only [ReflTransT.len]; omega⟩
    · -- The tail `[]` cannot reach `.exiting`: it steps to `.terminal` only.
      match h2 with
      | .step _ _ _ .step_stmts_nil hr =>
        match hr with
        | .step _ _ _ h _ => exact nomatch h

/-! ## Per-variable definedness through a run

The `Config.varsDefined` / `Config.varDefined` predicates are defined in
`StmtSemantics`; here we prove they are preserved across steps and runs. -/

/-- A single step preserves `Config.varsDefined`: every tracked variable stays
    defined, given a command evaluator that never undefines a store slot
    (`h_cmd`). -/
theorem Config.varsDefined_step_of {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [DecidableEq P.Ident]
    {CmdT : Type} {evalCmd : EvalCmdParam P CmdT}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {hf : Bool} {y : P.Ident},
      evalCmd f σ c σ' hf → (σ y).isSome = true → (σ' y).isSome = true)
    {Q : P.Ident → Prop} {c c' : Config P CmdT}
    (hstep : StepStmt P evalCmd c c')
    (h : Config.varsDefined Q c) :
    Config.varsDefined Q c' := by
  induction hstep with
  | step_cmd hcmd =>
    exact fun y hQ => h_cmd hcmd (h y hQ)
  | step_block => exact ⟨h, h⟩
  | step_ite_true _ => exact ⟨h, h⟩
  | step_ite_false _ => exact ⟨h, h⟩
  | step_ite_nondet_true => exact ⟨h, h⟩
  | step_ite_nondet_false => exact ⟨h, h⟩
  | step_loop_enter _ => exact ⟨h, h⟩
  | step_loop_exit _ => exact h
  | step_loop_nondet_enter => exact ⟨h, h⟩
  | step_loop_nondet_exit => exact h
  | step_exit => exact h
  | step_typeDecl => exact h
  | step_stmts_nil => exact h
  | step_stmts_cons => exact h
  | step_seq_inner _ ih => exact ih h
  | step_seq_done => exact h
  | step_seq_exit => exact h
  | step_block_body _ ih =>
    exact ⟨h.1, ih h.2⟩
  | step_block_done =>
    intro y hQ
    simp only [projectStore]; rw [ite_eq_left (h.1 y hQ)]; exact h.2 y hQ
  | step_block_exit_match heq =>
    intro y hQ
    simp only [projectStore]; rw [ite_eq_left (h.1 y hQ)]; exact h.2 y hQ
  | step_block_exit_mismatch hne =>
    intro y hQ
    simp only [projectStore]; rw [ite_eq_left (h.1 y hQ)]; exact h.2 y hQ

/-! ### `Config.storeWellDefined` preservation

Store value-hood is relative to the factory `fac`, so a run preserves
it given that the command evaluator preserves it. -/

/-- A single step preserves `Config.storeWellDefined`, given that the command
    evaluator does (`h_cmd`). -/
private theorem Config.storeWellDefined_step_of {P : PureExpr} [HasBool P] [HasBoolOps P]
    {CmdT : Type} {evalCmd : EvalCmdParam P CmdT}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {fl : Bool},
      evalCmd f σ c σ' fl → WellFormedStore σ f → WellFormedStore σ' f)
    {c c' : Config P CmdT}
    (hstep : StepStmt P evalCmd c c')
    (h : Config.storeWellDefined c) :
    Config.storeWellDefined c' := by
  induction hstep with
  | step_cmd hcmd => exact h_cmd hcmd h
  | step_seq_inner _ ih =>
    exact ih h
  | step_block_body hinner ih =>
    exact ⟨step_preserves_factory P evalCmd _ _ hinner ▸ h.1, ih h.2⟩
  -- The three exit rules project the store; projection keeps only slots that are
  -- defined in `ρ'`, where `h.2` already witnesses value-hood against the factory.
  | step_block_done | step_block_exit_match _ | step_block_exit_mismatch _ =>
    intro x w hx
    simp only [projectStore] at hx
    split at hx
    · exact h.2 x w hx
    · exact absurd hx (by simp)
  -- Everything else either leaves the operative store alone or pushes it into a
  -- block frame, which repeats it as the saved parent store.
  | _ => first | exact h | exact ⟨h, h⟩

/-- Multi-step preservation of `Config.varsDefined`, over any command evaluator
that never undefines a store slot. -/
theorem Config.varsDefined_star_of {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [DecidableEq P.Ident]
    {CmdT : Type} {evalCmd : EvalCmdParam P CmdT}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {hf : Bool} {y : P.Ident},
      evalCmd f σ c σ' hf → (σ y).isSome = true → (σ' y).isSome = true)
    {Q : P.Ident → Prop} {c c' : Config P CmdT}
    (hstar : StepStmtStar P evalCmd c c')
    (h : Config.varsDefined Q c) :
    Config.varsDefined Q c' := by
  induction hstar with
  | refl => exact h
  | step _ _ _ hstep _ ih =>
    exact ih (Config.varsDefined_step_of h_cmd hstep h)

/-- Single-step preservation of `Config.varsDefined` at `EvalCmd`. -/
theorem Config.varsDefined_step {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [DecidableEq P.Ident]
    {Q : P.Ident → Prop} {c c' : Config P (Cmd P)}
    (hstep : StepStmt P (EvalCmd P) c c')
    (h : Config.varsDefined Q c) :
    Config.varsDefined Q c' :=
  Config.varsDefined_step_of
    (fun hc hs => EvalCmd_preserves_isSome hc hs) hstep h

/-- Multi-step preservation of `Config.varsDefined` at `EvalCmd`. -/
theorem Config.varsDefined_star {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [DecidableEq P.Ident]
    {Q : P.Ident → Prop} {c c' : Config P (Cmd P)}
    (hstar : StepStmtStar P (EvalCmd P) c c')
    (h : Config.varsDefined Q c) :
    Config.varsDefined Q c' :=
  Config.varsDefined_star_of
    (fun hc hs => EvalCmd_preserves_isSome hc hs) hstar h

/-- The gen guard `y`, defined in the start store, stays defined after running a
statement list to terminal.  A corollary of `Config.varsDefined_star` (at the
singleton `Config.varDefined y`) that packages the `(.stmts ss ρ)` coercion; kept
as a named cross-module convenience (used from the transform-correctness proofs)
so those call sites need not spell out the coercion, and hence cannot be `private`. -/
theorem stmts_preserves_isSome {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [DecidableEq P.Ident]
    {y : P.Ident} {ss : List (Stmt P (Cmd P))} {ρ ρ' : Env P}
    (hstar : StepStmtStar P (EvalCmd P) (.stmts ss ρ) (.terminal ρ'))
    (h_some : (ρ.store y).isSome = true) :
    (ρ'.store y).isSome = true :=
  Config.varsDefined_star hstar
    (show Config.varDefined y (.stmts ss ρ) from fun _ hz => hz ▸ h_some) y rfl


/-! ## Per-variable undefinedness through a run, scope-aware

The `excludeScoped := true` variant, which allows a block-local `init` of a tracked
variable because leaving the block projects that binding away again. -/

/-- Single-step preservation of `Config.varsUndefined true`, over any command
    evaluator that only defines the slots the command itself declares.

    Every case is immediate: entering a scope saves the parent store (which
    carries the invariant), leaving one projects through it, and no case needs
    to know anything about what happened inside. -/
private theorem Config.varsUndefinedScoped_step_of {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P] [HasIdent P] [DecidableEq P.Ident]
    {CmdT : Type} [HasVarsImp P CmdT] {evalCmd : EvalCmdParam P CmdT}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {hf : Bool} {y : P.Ident},
      evalCmd f σ c σ' hf → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    {Q : P.Ident → Prop} {cfg cfg' : Config P CmdT}
    (h_step : StepStmt P evalCmd cfg cfg')
    (h_inv : Config.varsUndefined true (P := P) Q cfg) :
    Config.varsUndefined true (P := P) Q cfg' := by
  induction h_step with
  | step_cmd h_eval =>
    intro y hQ
    obtain ⟨h_none, h_ndef⟩ := h_inv y hQ
    exact h_cmd h_eval h_none (by simpa [Stmt.definedVars] using h_ndef)
  | step_loop_enter _ | step_loop_nondet_enter =>
    refine ⟨fun y hQ => (h_inv y hQ).1, fun y hQ s hs => ?_⟩
    rcases List.mem_cons.mp hs with h_eq | h_in
    · subst h_eq; simp [Stmt.definedVars]
    · exact absurd h_in (List.not_mem_nil)
  | step_stmts_cons =>
    refine ⟨fun y hQ => ⟨(h_inv y hQ).1, (h_inv y hQ).2 _ List.mem_cons_self⟩,
            fun y hQ s' hs' => (h_inv y hQ).2 s' (List.mem_cons_of_mem _ hs')⟩
  | step_seq_inner _ ih => exact ⟨ih h_inv.1, h_inv.2⟩
  | step_seq_done => exact fun y hQ => ⟨h_inv.1 y hQ, h_inv.2 y hQ⟩
  | step_seq_exit => exact h_inv.1
  | step_block_body _ _ => exact h_inv
  | step_block_done | step_block_exit_match _ | step_block_exit_mismatch _ =>
    intro y hQ
    show projectStore _ _ y = none
    unfold projectStore; rw [ite_eq_right]; rw [h_inv y hQ]; simp
  | _ => exact fun y hQ => (h_inv y hQ).1

/-- Trace lift of `Config.varsUndefinedScoped_step_of` (the `excludeScoped = true`
    form of `Config.varsUndefined`). -/
theorem Config.varsUndefinedScoped_star_of {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P] [HasIdent P] [DecidableEq P.Ident]
    {CmdT : Type} [HasVarsImp P CmdT] {evalCmd : EvalCmdParam P CmdT}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {hf : Bool} {y : P.Ident},
      evalCmd f σ c σ' hf → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    {Q : P.Ident → Prop} {cfg cfg' : Config P CmdT}
    (h_run : StepStmtStar P evalCmd cfg cfg')
    (h_inv : Config.varsUndefined true (P := P) Q cfg) :
    Config.varsUndefined true (P := P) Q cfg' := by
  induction h_run with
  | refl => exact h_inv
  | step _ _ _ h_step _ ih => exact ih (Config.varsUndefinedScoped_step_of h_cmd h_step h_inv)

/-- **Leaving a block drops exactly the names its body scopes**, so the store handed back
    is determined by the body alone. -/
theorem projectStore_eq_dropVars {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P] [HasIdent P] [DecidableEq P.Ident]
    {CmdT : Type} [HasVarsImp P CmdT] {evalCmd : EvalCmdParam P CmdT}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {hf : Bool} {y : P.Ident},
      evalCmd f σ c σ' hf → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    {ss : List (Stmt P CmdT)} {ρ₀ ρ : Env P}
    (hdefs : ∀ x ∈ Block.definedVars (P := P) (C := CmdT) ss true, ρ₀.store x = none)
    (hrun : StepStmtStar P evalCmd (.stmts ss ρ₀) (.terminal ρ) ∨
      ∃ lbl, StepStmtStar P evalCmd (.stmts ss ρ₀) (.exiting lbl ρ)) :
    projectStore ρ₀.store ρ.store
      = dropVars (Block.definedVars (P := P) (C := CmdT) ss true) ρ.store := by
  funext n
  by_cases hmem : n ∈ Block.definedVars (P := P) (C := CmdT) ss true
  · simp [projectStore, dropVars, hmem, hdefs n hmem]
  · cases hq : ρ₀.store n with
    | some v => simp [projectStore, dropVars, hmem, hq]
    | none =>
      -- Undefined in the parent and not scoped by the body, so still undefined at `ρ`.
      have hstart : Config.varsUndefined true (P := P) (· = n) (.stmts ss ρ₀) := by
        rintro y rfl
        exact ⟨hq, all_not_mem_definedVars_of_block hmem⟩
      have hnone : ρ.store n = none := by
        match hrun with
        | .inl hterm => exact Config.varsUndefinedScoped_star_of h_cmd hterm hstart n rfl
        | .inr ⟨_, hexit⟩ => exact Config.varsUndefinedScoped_star_of h_cmd hexit hstart n rfl
      simp [projectStore, dropVars, hmem, hq, hnone]

/-! ## Per-variable undefinedness through a run (dual of `Config.varsDefined`) -/

/-- Single-step preservation of `Config.varsUndefined false`, over any command
    evaluator that only ever defines the slots the command itself declares.

    Every case but `step_cmd` is structural — a matter of how `Stmt.definedVars`
    and `projectStore` decompose — so the evaluator enters only through `h_cmd`.
    `Config.varsUndefinedThroughout_step` instantiates this at `EvalCmd`;
    `Core.core_varsUndefinedThroughout_star` does so at `EvalCommand`. -/
theorem Config.varsUndefinedThroughout_step_of {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [DecidableEq P.Ident]
    {CmdT : Type} [HasVarsImp P CmdT] {evalCmd : EvalCmdParam P CmdT}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {hf : Bool} {y : P.Ident},
      evalCmd f σ c σ' hf → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c false → σ' y = none)
    {Q : P.Ident → Prop} {cfg cfg' : Config P CmdT}
    (h_step : StepStmt P evalCmd cfg cfg')
    (h_inv : Config.varsUndefined false (P := P) Q cfg) :
    Config.varsUndefined false (P := P) Q cfg' := by
  induction h_step with
  | step_cmd h_eval =>
    intro y hQ
    obtain ⟨h_none, h_ndef⟩ := h_inv y hQ
    refine h_cmd h_eval h_none ?_
    simpa [Stmt.definedVars] using h_ndef
  | step_block =>
    refine ⟨fun y hQ => (h_inv y hQ).1, fun y hQ => ?_⟩
    obtain ⟨h_none, h_ndef⟩ := h_inv y hQ
    exact ⟨h_none, all_not_mem_definedVars_of_block (by simpa [Stmt.definedVars] using h_ndef)⟩
  | step_ite_true _ | step_ite_nondet_true =>
    refine ⟨fun y hQ => (h_inv y hQ).1, fun y hQ => ?_⟩
    obtain ⟨h_none, h_ndef⟩ := h_inv y hQ
    rw [Stmt.definedVars] at h_ndef
    simp only [Bool.false_eq_true, ite_false] at h_ndef
    exact ⟨h_none, all_not_mem_definedVars_of_block (fun hc => h_ndef (List.mem_append.mpr (Or.inl hc)))⟩
  | step_ite_false _ | step_ite_nondet_false =>
    refine ⟨fun y hQ => (h_inv y hQ).1, fun y hQ => ?_⟩
    obtain ⟨h_none, h_ndef⟩ := h_inv y hQ
    rw [Stmt.definedVars] at h_ndef
    simp only [Bool.false_eq_true, ite_false] at h_ndef
    exact ⟨h_none, all_not_mem_definedVars_of_block (fun hc => h_ndef (List.mem_append.mpr (Or.inr hc)))⟩
  | step_loop_enter _ | step_loop_nondet_enter =>
    refine ⟨⟨fun y hQ => (h_inv y hQ).1, fun y hQ => ?_⟩, fun y hQ s hs => ?_⟩
    · obtain ⟨h_none, h_ndef⟩ := h_inv y hQ
      rw [Stmt.definedVars] at h_ndef
      simp only [Bool.false_eq_true, ite_false] at h_ndef
      exact ⟨h_none, all_not_mem_definedVars_of_block h_ndef⟩
    · obtain ⟨_, h_ndef⟩ := h_inv y hQ
      rw [Stmt.definedVars] at h_ndef
      simp only [Bool.false_eq_true, ite_false] at h_ndef
      rcases List.mem_cons.mp hs with h_eq | h_in
      · subst h_eq; rw [Stmt.definedVars]; simp only [Bool.false_eq_true, ite_false]; exact h_ndef
      · exact absurd h_in (List.not_mem_nil)
  | step_stmts_cons =>
    refine ⟨fun y hQ => ?_, fun y hQ s' hs' => ?_⟩
    · obtain ⟨h_none, h_ndef⟩ := h_inv y hQ
      exact ⟨h_none, h_ndef _ (List.mem_cons_self)⟩
    · exact (h_inv y hQ).2 s' (List.mem_cons_of_mem _ hs')
  | step_seq_inner _ ih =>
    obtain ⟨h_inner_inv, h_ndef⟩ := h_inv
    exact ⟨ih h_inner_inv, h_ndef⟩
  | step_seq_done =>
    obtain ⟨h_inner, h_ndef⟩ := h_inv
    intro y hQ
    exact ⟨h_inner y hQ, h_ndef y hQ⟩
  | step_seq_exit =>
    exact h_inv.1
  | step_block_body _ ih =>
    obtain ⟨h_parent, h_inner_inv⟩ := h_inv
    exact ⟨h_parent, ih h_inner_inv⟩
  | step_block_done | step_block_exit_match _ | step_block_exit_mismatch _ =>
    obtain ⟨h_parent, _⟩ := h_inv
    intro y hQ
    show projectStore _ _ y = none
    unfold projectStore; rw [ite_eq_right]; rw [h_parent y hQ]; simp
  | _ => intro y hQ; exact (h_inv y hQ).1

/-- Trace lift of `Config.varsUndefinedThroughout_step_of` (the
    `excludeScoped = false` form of `Config.varsUndefined`). -/
theorem Config.varsUndefinedThroughout_star_of {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P] [DecidableEq P.Ident]
    {CmdT : Type} [HasVarsImp P CmdT] {evalCmd : EvalCmdParam P CmdT}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {hf : Bool} {y : P.Ident},
      evalCmd f σ c σ' hf → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c false → σ' y = none)
    {Q : P.Ident → Prop} {cfg cfg' : Config P CmdT}
    (h_run : StepStmtStar P evalCmd cfg cfg')
    (h_inv : Config.varsUndefined false (P := P) Q cfg) :
    Config.varsUndefined false (P := P) Q cfg' := by
  induction h_run with
  | refl => exact h_inv
  | step _ _ _ h_step _ ih =>
    exact ih (Config.varsUndefinedThroughout_step_of h_cmd h_step h_inv)

/-- Single-step preservation of `Config.varsUndefined false` at `EvalCmd`. -/
theorem Config.varsUndefinedThroughout_step {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [DecidableEq P.Ident]
    {Q : P.Ident → Prop} {cfg cfg' : Config P (Cmd P)}
    (h_step : StepStmt P (EvalCmd P) cfg cfg')
    (h_inv : Config.varsUndefined false (P := P) Q cfg) :
    Config.varsUndefined false (P := P) Q cfg' :=
  Config.varsUndefinedThroughout_step_of
    (fun he hn hnd => evalCmd_preserves_none_of_not_def he hn hnd) h_step h_inv

/-- Trace lift: `Config.varsUndefined false` is preserved along a multi-step run. -/
theorem Config.varsUndefinedThroughout_star {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P] [DecidableEq P.Ident]
    {Q : P.Ident → Prop} {cfg cfg' : Config P (Cmd P)}
    (h_run : StepStmtStar P (EvalCmd P) cfg cfg')
    (h_inv : Config.varsUndefined false (P := P) Q cfg) :
    Config.varsUndefined false (P := P) Q cfg' :=
  Config.varsUndefinedThroughout_star_of
    (fun he hn hnd => evalCmd_preserves_none_of_not_def he hn hnd) h_run h_inv

/-- A terminating `.stmts bss` run preserves `store y = none` for any
`y ∉ Block.definedVars bss`.  Thin single-key corollary of the `Q`-keyed
`Config.varsUndefinedThroughout_star` engine (specialize `Q` to the singleton `· = y`). -/
theorem block_run_terminal_preserves_none_of_not_definedVars {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasIdent P] [HasInt P] [HasIntOps P] [DecidableEq P.Ident]
    {y : P.Ident} {bss : List (Stmt P (Cmd P))} {ρ ρ' : Env P}
    (h_y_not_def : y ∉ Block.definedVars (P := P) (C := Cmd P) bss false)
    (h_none : ρ.store y = none)
    (h_run : StepStmtStar P (EvalCmd P) (.stmts bss ρ) (.terminal ρ')) :
    ρ'.store y = none :=
  Config.varsUndefinedThroughout_star (Q := (· = y)) h_run
    (by rintro z rfl; exact ⟨h_none, all_not_mem_definedVars_of_block h_y_not_def⟩) y rfl

/-! ## Per-variable *value* preservation through a run (frame lemma)

Dual of `Config.varsUndefined`: rather than tracking that a variable stays
`none`, we track that a variable holds a *fixed value option* `w` — both in the
operative store and in every enclosing block's saved parent store — as long as no
statement still to run writes it (neither `init`s it at any scope depth, nor
`set`/`havoc`s it).  This lifts the command-level exact-value frame
(`evalCmd_preserves_eq_of_not_written`) to a whole terminating/escaping run: a
variable a block never writes exits the block with exactly its entry value. -/

/-- A statement list writes `y` at neither scope: `y` is defined by no member (at
any nesting depth) and modified by no member.  Companion of
`all_not_mem_definedVars_of_block` for the modified-variable set. -/
private theorem all_not_mem_modifiedVars_of_block {P : PureExpr} [HasFvars P]
    {y : P.Ident} {ss : List (Stmt P (Cmd P))}
    (h : y ∉ Block.modifiedVars (P := P) (C := Cmd P) ss) :
    ∀ s ∈ ss, y ∉ Stmt.modifiedVars (P := P) (C := Cmd P) s := by
  induction ss with
  | nil => intro s hs; exact absurd hs (List.not_mem_nil)
  | cons s rest ih =>
    rw [Block.modifiedVars] at h
    intro s' hs'
    rcases List.mem_cons.mp hs' with h_eq | h_in
    · exact h_eq ▸ (fun hc => h (List.mem_append.mpr (Or.inl hc)))
    · exact ih (fun hc => h (List.mem_append.mpr (Or.inr hc))) s' h_in

/-- Scope-aware value-preservation invariant: the variable `y` is bound to the
fixed value option `w` in the operative store and in every enclosing block's
saved parent store, and no statement still to run writes `y` (defines it at any
depth or modifies it). -/
@[expose] def Config.varEqUnwritten {P : PureExpr} [HasFvars P]
    (y : P.Ident) (w : Option P.Expr) : Config P (Cmd P) → Prop
  | .stmt s ρ => ρ.store y = w
      ∧ y ∉ Stmt.definedVars (P := P) (C := Cmd P) s false
      ∧ y ∉ Stmt.modifiedVars (P := P) (C := Cmd P) s
  | .stmts ss ρ => ρ.store y = w
      ∧ (∀ s ∈ ss, y ∉ Stmt.definedVars (P := P) (C := Cmd P) s false)
      ∧ (∀ s ∈ ss, y ∉ Stmt.modifiedVars (P := P) (C := Cmd P) s)
  | .terminal ρ => ρ.store y = w
  | .exiting _ ρ => ρ.store y = w
  | .block _ σ_parent inner => σ_parent y = w ∧ Config.varEqUnwritten y w inner
  | .seq inner ss => Config.varEqUnwritten y w inner
      ∧ (∀ s ∈ ss, y ∉ Stmt.definedVars (P := P) (C := Cmd P) s false)
      ∧ (∀ s ∈ ss, y ∉ Stmt.modifiedVars (P := P) (C := Cmd P) s)

/-- A single `EvalCmd` statement step preserves `Config.varEqUnwritten`. -/
theorem Config.varEqUnwritten_step {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [DecidableEq P.Ident]
    {y : P.Ident} {w : Option P.Expr} {cfg cfg' : Config P (Cmd P)}
    (h_step : StepStmt P (EvalCmd P) cfg cfg')
    (h_inv : Config.varEqUnwritten (P := P) y w cfg) :
    Config.varEqUnwritten (P := P) y w cfg' := by
  induction h_step with
  | step_cmd h_eval =>
    obtain ⟨hw, hnd, hnm⟩ := h_inv
    have heq := evalCmd_preserves_eq_of_not_written (y := y) h_eval
      (by simpa [Stmt.definedVars, HasVarsImp.definedVars] using hnd)
      (by simpa [Stmt.modifiedVars, HasVarsImp.modifiedVars] using hnm)
    exact heq.trans hw
  | step_block =>
    obtain ⟨hw, hnd, hnm⟩ := h_inv
    rw [Stmt.definedVars] at hnd; simp only [Bool.false_eq_true, ite_false] at hnd
    rw [Stmt.modifiedVars] at hnm
    exact ⟨hw, hw, all_not_mem_definedVars_of_block hnd, all_not_mem_modifiedVars_of_block hnm⟩
  | step_ite_true _ | step_ite_nondet_true =>
    obtain ⟨hw, hnd, hnm⟩ := h_inv
    rw [Stmt.definedVars] at hnd; simp only [Bool.false_eq_true, ite_false] at hnd
    rw [Stmt.modifiedVars] at hnm
    exact ⟨hw, hw,
      all_not_mem_definedVars_of_block (fun hc => hnd (List.mem_append.mpr (Or.inl hc))),
      all_not_mem_modifiedVars_of_block (fun hc => hnm (List.mem_append.mpr (Or.inl hc)))⟩
  | step_ite_false _ | step_ite_nondet_false =>
    obtain ⟨hw, hnd, hnm⟩ := h_inv
    rw [Stmt.definedVars] at hnd; simp only [Bool.false_eq_true, ite_false] at hnd
    rw [Stmt.modifiedVars] at hnm
    exact ⟨hw, hw,
      all_not_mem_definedVars_of_block (fun hc => hnd (List.mem_append.mpr (Or.inr hc))),
      all_not_mem_modifiedVars_of_block (fun hc => hnm (List.mem_append.mpr (Or.inr hc)))⟩
  | step_loop_enter _ | step_loop_nondet_enter =>
    obtain ⟨hw, hnd, hnm⟩ := h_inv
    have hnd' := hnd; have hnm' := hnm
    rw [Stmt.definedVars] at hnd; simp only [Bool.false_eq_true, ite_false] at hnd
    rw [Stmt.modifiedVars] at hnm
    refine ⟨⟨hw, hw, all_not_mem_definedVars_of_block hnd, all_not_mem_modifiedVars_of_block hnm⟩,
      ?_, ?_⟩
    · intro s hs; rw [List.mem_singleton] at hs; subst hs; exact hnd'
    · intro s hs; rw [List.mem_singleton] at hs; subst hs; exact hnm'
  | step_loop_exit _ | step_loop_nondet_exit | step_exit | step_typeDecl =>
    exact h_inv.1
  | step_stmts_nil =>
    exact h_inv.1
  | step_stmts_cons =>
    obtain ⟨hw, hnd, hnm⟩ := h_inv
    exact ⟨⟨hw, hnd _ List.mem_cons_self, hnm _ List.mem_cons_self⟩,
      fun s hs => hnd _ (List.mem_cons_of_mem _ hs),
      fun s hs => hnm _ (List.mem_cons_of_mem _ hs)⟩
  | step_seq_inner _ ih =>
    obtain ⟨h_inner, h_nd, h_nm⟩ := h_inv
    exact ⟨ih h_inner, h_nd, h_nm⟩
  | step_seq_done =>
    obtain ⟨h_inner, h_nd, h_nm⟩ := h_inv
    exact ⟨h_inner, h_nd, h_nm⟩
  | step_seq_exit =>
    exact h_inv.1
  | step_block_body _ ih =>
    obtain ⟨h_parent, h_inner⟩ := h_inv
    exact ⟨h_parent, ih h_inner⟩
  | step_block_done | step_block_exit_match _ | step_block_exit_mismatch _ =>
    obtain ⟨h_parent, h_inner⟩ := h_inv
    have hi : _ = w := h_inner
    show projectStore _ _ y = w
    simp only [projectStore]
    rw [h_parent, hi]
    cases w with
    | none => simp
    | some v => simp

/-- Trace lift: `Config.varEqUnwritten` is preserved along a multi-step run. -/
theorem Config.varEqUnwritten_star {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [DecidableEq P.Ident]
    {y : P.Ident} {w : Option P.Expr} {cfg cfg' : Config P (Cmd P)}
    (h_run : StepStmtStar P (EvalCmd P) cfg cfg')
    (h_inv : Config.varEqUnwritten (P := P) y w cfg) :
    Config.varEqUnwritten (P := P) y w cfg' := by
  induction h_run with
  | refl => exact h_inv
  | step _ _ _ h_step _ ih => exact ih (Config.varEqUnwritten_step h_step h_inv)

/-- **Value frame lemma.**  A terminating `.stmts bss` run preserves the exact
value at any `y` the block never writes: if `y ∉ Block.definedVars bss false`
and `y ∉ Block.modifiedVars bss`, then `ρ'.store y = ρ.store y`.  The exact-value
analogue of `block_run_terminal_preserves_none_of_not_definedVars`; instantiates
the `Config.varEqUnwritten` engine at `w := ρ.store y`. -/
theorem block_run_terminal_preserves_eq_of_not_written {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] [DecidableEq P.Ident]
    {y : P.Ident} {bss : List (Stmt P (Cmd P))} {ρ ρ' : Env P}
    (h_y_not_def : y ∉ Block.definedVars (P := P) (C := Cmd P) bss false)
    (h_y_not_mod : y ∉ Block.modifiedVars (P := P) (C := Cmd P) bss)
    (h_run : StepStmtStar P (EvalCmd P) (.stmts bss ρ) (.terminal ρ')) :
    ρ'.store y = ρ.store y :=
  Config.varEqUnwritten_star (w := ρ.store y) h_run
    ⟨rfl, all_not_mem_definedVars_of_block h_y_not_def,
     all_not_mem_modifiedVars_of_block h_y_not_mod⟩

/-- A command-free administrative step is already an event step after normalizing
its silent trace and unchanged cumulative failure flag. -/
private theorem StepStmt.adminToStepStmtE
    {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P]
    {c c' : Config P (Cmd P)}
    (h : StepStmt P (noCommandEvalE P (Cmd P)) c c') :
    StepStmtE P (EvalCmdE P) c (c.emittedEvents)
      (c'.withFailure c.getEnv.hasFailure) := by
  induction h <;>
    simp_all only [noCommandEvalE, Config.emittedEvents, Config.withFailure, Config.getEnv, ne_eq] <;>
    first
    | exact StepStmtE.step_seq_inner (by assumption)
    | exact StepStmtE.step_block_body (by assumption)
    | apply StepStmtE.step_admin
      constructor <;> simp_all

/-- A legacy statement step is reproduced by the event semantics with the
source configuration's deterministic active-command trace. The event target is
the legacy target with its cumulative failure flag normalized back to the
source flag, because event semantics records assertion observations in the
trace instead of mutating `hasFailure`. -/
theorem StepStmt.toStepStmtE
    {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P]
    {c c' : Config P (Cmd P)}
    (h : StepStmt P (EvalCmd P) c c') :
    StepStmtE P (EvalCmdE P) c (c.emittedEvents)
      (c'.withFailure c.getEnv.hasFailure) := by
  induction h with
  | step_cmd hcmd =>
      simpa [Config.emittedEvents, Config.withFailure, Config.getEnv] using
        (StepStmtE.step_cmd hcmd.toEvalCmdE)
  | step_block => exact StepStmt.adminToStepStmtE .step_block
  | step_ite_true heval =>
      exact StepStmt.adminToStepStmtE (.step_ite_true heval)
  | step_ite_false heval =>
      exact StepStmt.adminToStepStmtE (.step_ite_false heval)
  | step_ite_nondet_true =>
      exact StepStmt.adminToStepStmtE .step_ite_nondet_true
  | step_ite_nondet_false =>
      exact StepStmt.adminToStepStmtE .step_ite_nondet_false
  | step_loop_enter heval =>
      exact StepStmt.adminToStepStmtE (.step_loop_enter heval)
  | step_loop_exit heval =>
      exact StepStmt.adminToStepStmtE (.step_loop_exit heval)
  | step_loop_nondet_enter =>
      exact StepStmt.adminToStepStmtE .step_loop_nondet_enter
  | step_loop_nondet_exit =>
      exact StepStmt.adminToStepStmtE .step_loop_nondet_exit
  | step_exit => exact StepStmt.adminToStepStmtE .step_exit
  | step_typeDecl => exact StepStmt.adminToStepStmtE .step_typeDecl
  | step_stmts_nil => exact StepStmt.adminToStepStmtE .step_stmts_nil
  | step_stmts_cons => exact StepStmt.adminToStepStmtE .step_stmts_cons
  | step_seq_inner _ ih =>
      simpa [Config.emittedEvents, Config.withFailure, Config.getEnv] using
        (StepStmtE.step_seq_inner (ss := _) ih)
  | step_seq_done => exact StepStmt.adminToStepStmtE .step_seq_done
  | step_seq_exit => exact StepStmt.adminToStepStmtE .step_seq_exit
  | step_block_body _ ih =>
      simpa [Config.emittedEvents, Config.withFailure, Config.getEnv] using
        (StepStmtE.step_block_body (label := _) (σ_parent := _) ih)
  | step_block_done => exact StepStmt.adminToStepStmtE .step_block_done
  | step_block_exit_match hlabel =>
      exact StepStmt.adminToStepStmtE (.step_block_exit_match hlabel)
  | step_block_exit_mismatch hlabel =>
      exact StepStmt.adminToStepStmtE (.step_block_exit_mismatch hlabel)

/-! ## Traced (`StepStmtStarE`) structural helpers

Trace-carrying analogues of the failure-flag `seq`/`stmts` helpers, used to lift
per-statement event-trace overapproximation to statement lists. Administrative
steps arise two ways from a `.seq`: natively via `step_seq_inner` (carrying the
inner event list) or through `step_admin` (empty trace); both are handled and
produce the same chronological trace. -/

section EventTraceStructural

variable {P : PureExpr} {CmdT : Type} {EventT : Type} [HasBool P]
  (EvalCmd : EvalCmdParamE P CmdT EventT)


/-- Lift a traced inner run through a `.seq` frame, preserving its trace. -/
theorem seq_inner_starE
    {inner inner' : Config P CmdT} {ss : List (Stmt P CmdT)} {tr : List EventT}
    (h : StepStmtStarE P EvalCmd inner tr inner') :
    StepStmtStarE P EvalCmd (.seq inner ss) tr (.seq inner' ss) := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ _ _ hstep _ ih => exact .step _ _ _ _ _ (.step_seq_inner hstep) ih

/-- A traced run of an empty statement list emits no events and stays put or
terminates. -/
theorem stmts_nil_runE
    {ρ₀ : Env P} {cfg : Config P CmdT} {tr : List EventT}
    (h : StepStmtStarE P EvalCmd (.stmts [] ρ₀) tr cfg) :
    tr = [] ∧ (cfg = .stmts [] ρ₀ ∨ cfg = .terminal ρ₀) := by
  cases h with
  | refl => exact ⟨rfl, .inl rfl⟩
  | step _ _ _ _ _ hstep hrest =>
    cases hstep with
    | step_admin hadmin =>
      cases hadmin with
      | step_stmts_nil =>
        cases hrest with
        | refl => exact ⟨by simp, .inr rfl⟩
        | step _ _ _ _ _ h' _ => cases h' with | step_admin h'' => cases h''

/-- Strip the leading `step_stmts_cons` from a traced cons-list run: either the
run is empty, or it continues from the head-in-`.seq` configuration with the
same trace. -/
theorem stmts_cons_headE
    {s : Stmt P CmdT} {ss : List (Stmt P CmdT)} {ρ₀ : Env P}
    {cfg : Config P CmdT} {tr : List EventT}
    (h : StepStmtStarE P EvalCmd (.stmts (s :: ss) ρ₀) tr cfg) :
    (cfg = .stmts (s :: ss) ρ₀ ∧ tr = []) ∨
    StepStmtStarE P EvalCmd (.seq (.stmt s ρ₀) ss) tr cfg := by
  cases h with
  | refl => exact .inl ⟨rfl, rfl⟩
  | step _ _ _ _ _ hstep hrest =>
    cases hstep with
    | step_admin hadmin =>
      cases hadmin with
      | step_stmts_cons => exact .inr (by simpa using hrest)

/-- Terminate a head statement, then step the enclosing list to its tail with
the head's trace. -/
theorem stmts_cons_stepE
    (s : Stmt P CmdT) (ss : List (Stmt P CmdT)) (ρ ρ' : Env P) {tr : List EventT}
    (hstmt : StepStmtStarE P EvalCmd (.stmt s ρ) tr (.terminal ρ')) :
    StepStmtStarE P EvalCmd (.stmts (s :: ss) ρ) tr (.stmts ss ρ') := by
  have h2 := seq_inner_starE EvalCmd (ss := ss) hstmt
  have hchain := ReflTransTrace.trans _
    (ReflTransTrace.step _ _ _ _ _ (.step_admin .step_stmts_cons) h2)
    (ReflTransTrace.step (r := StepStmtE P EvalCmd)
      _ _ _ _ _ (.step_admin .step_seq_done) (.refl _))
  simpa using hchain

/-- A single statement whose event run terminates gives a terminating event run of the
one-element statement list wrapping it, with the same trace. -/
theorem stmtRun_to_singletonE
    {s : Stmt P CmdT} {ρ ρ' : Env P} {tr : List EventT}
    (h : StepStmtStarE P EvalCmd (.stmt s ρ) tr (.terminal ρ')) :
    StepStmtStarE P EvalCmd (.stmts [s] ρ) tr (.terminal ρ') := by
  have hcons := stmts_cons_stepE EvalCmd s [] ρ ρ' h
  have hnil : StepStmtStarE P EvalCmd
      (.stmts [] ρ') [] (.terminal ρ') :=
    .step _ [] _ [] _ (.step_admin .step_stmts_nil) (.refl _)
  simpa using ReflTransTrace.trans _ hcons hnil

/-- Decompose a traced `.seq inner ss` run to an arbitrary target: still inside
the head, the head terminated and the tail continues, or the head exited. The
trace splits chronologically as head ++ tail. -/
theorem seq_run_decomposeE
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)}
    {cfg : Config P CmdT} {tr : List EventT}
    (hstar : StepStmtStarE P EvalCmd (.seq inner ss) tr cfg) :
    (∃ inner', cfg = .seq inner' ss ∧
        StepStmtStarE P EvalCmd inner tr inner')
    ∨ (∃ ρ₁ tr₁ tr₂, tr = tr₁ ++ tr₂ ∧
        StepStmtStarE P EvalCmd inner tr₁ (.terminal ρ₁) ∧
        StepStmtStarE P EvalCmd (.stmts ss ρ₁) tr₂ cfg)
    ∨ (∃ lbl ρ₁, cfg = .exiting lbl ρ₁ ∧
        StepStmtStarE P EvalCmd inner tr (.exiting lbl ρ₁)) := by
  suffices h_gen : ∀ src tr' tgt,
      StepStmtStarE P EvalCmd src tr' tgt →
      ∀ inner ss, src = .seq inner ss →
      (∃ inner', tgt = .seq inner' ss ∧
          StepStmtStarE P EvalCmd inner tr' inner')
      ∨ (∃ ρ₁ tr₁ tr₂, tr' = tr₁ ++ tr₂ ∧
          StepStmtStarE P EvalCmd inner tr₁ (.terminal ρ₁) ∧
          StepStmtStarE P EvalCmd (.stmts ss ρ₁) tr₂ tgt)
      ∨ (∃ lbl ρ₁, tgt = .exiting lbl ρ₁ ∧
          StepStmtStarE P EvalCmd inner tr' (.exiting lbl ρ₁)) by
    exact h_gen _ _ _ hstar _ _ rfl
  intro src tr' tgt hstar_g
  induction hstar_g with
  | refl x => intro inner ss hsrc; subst hsrc; exact .inl ⟨inner, rfl, .refl _⟩
  | step x emitted y restTr z hstep hrest ih =>
    intro inner ss hsrc; subst hsrc
    cases hstep with
    | step_seq_inner hinner =>
      rcases ih _ _ rfl with
        ⟨inner'', hcfg, hrun⟩ | ⟨ρ₁, tr₁, tr₂, htr, hterm, htail⟩ | ⟨lbl, ρ₁, hcfg, hexit⟩
      · exact .inl ⟨inner'', hcfg, .step _ _ _ _ _ hinner hrun⟩
      · exact .inr (.inl ⟨ρ₁, emitted ++ tr₁, tr₂, by rw [htr]; simp [List.append_assoc],
          .step _ _ _ _ _ hinner hterm, htail⟩)
      · exact .inr (.inr ⟨lbl, ρ₁, hcfg, .step _ _ _ _ _ hinner hexit⟩)
    | step_admin hadmin =>
      cases hadmin with
      | step_seq_inner hinner' =>
        rcases ih _ _ rfl with
          ⟨inner'', hcfg, hrun⟩ | ⟨ρ₁, tr₁, tr₂, htr, hterm, htail⟩ | ⟨lbl, ρ₁, hcfg, hexit⟩
        · exact .inl ⟨inner'', hcfg, .step _ _ _ _ _ (.step_admin hinner') hrun⟩
        · exact .inr (.inl ⟨ρ₁, tr₁, tr₂, by rw [htr]; simp,
            .step _ _ _ _ _ (.step_admin hinner') hterm, htail⟩)
        · exact .inr (.inr ⟨lbl, ρ₁, hcfg, .step _ _ _ _ _ (.step_admin hinner') hexit⟩)
      | step_seq_done =>
        exact .inr (.inl ⟨_, [], restTr, by simp, .refl _, hrest⟩)
      | step_seq_exit =>
        cases hrest with
        | refl => exact .inr (.inr ⟨_, _, rfl, .refl _⟩)
        | step _ _ _ _ _ h' _ => cases h' with | step_admin h'' => cases h''

/-- A traced `.seq inner ss` run reaching terminal splits into the inner
terminating and the tail running to terminal. -/
theorem seq_reaches_terminalE
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)} {ρ' : Env P} {tr : List EventT}
    (hstar : StepStmtStarE P EvalCmd (.seq inner ss) tr (.terminal ρ')) :
    ∃ ρ₁ tr₁ tr₂, tr = tr₁ ++ tr₂ ∧
      StepStmtStarE P EvalCmd inner tr₁ (.terminal ρ₁) ∧
      StepStmtStarE P EvalCmd (.stmts ss ρ₁) tr₂ (.terminal ρ') := by
  rcases seq_run_decomposeE EvalCmd hstar with
    ⟨inner', hcfg, _⟩ | ⟨ρ₁, tr₁, tr₂, htr, hterm, htail⟩ | ⟨lbl, ρ₁, hcfg, _⟩
  · simp at hcfg
  · exact ⟨ρ₁, tr₁, tr₂, htr, hterm, htail⟩
  · simp at hcfg

/-- A traced `.seq inner ss` run reaching exiting: the inner exited, or the
inner terminated and the tail exited. -/
theorem seq_reaches_exitingE
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)} {lbl : String}
    {ρ' : Env P} {tr : List EventT}
    (hstar : StepStmtStarE P EvalCmd (.seq inner ss) tr (.exiting lbl ρ')) :
    StepStmtStarE P EvalCmd inner tr (.exiting lbl ρ') ∨
    ∃ ρ₁ tr₁ tr₂, tr = tr₁ ++ tr₂ ∧
      StepStmtStarE P EvalCmd inner tr₁ (.terminal ρ₁) ∧
      StepStmtStarE P EvalCmd (.stmts ss ρ₁) tr₂ (.exiting lbl ρ') := by
  rcases seq_run_decomposeE EvalCmd hstar with
    ⟨inner', hcfg, _⟩ | ⟨ρ₁, tr₁, tr₂, htr, hterm, htail⟩ | ⟨lbl', ρ₁, hcfg, hexit⟩
  · simp at hcfg
  · exact .inr ⟨ρ₁, tr₁, tr₂, htr, hterm, htail⟩
  · injection hcfg with hl hρ; subst hρ; subst hl; exact .inl hexit

/-- A single traced step preserves `Config.exitsCoveredByBlocks`. -/
private theorem stepStmtE_preserves_exitsCoveredByBlocks
    {c₁ c₂ : Config P CmdT} {tr : List EventT}
    (hstep : StepStmtE P EvalCmd c₁ tr c₂) :
    ∀ labels, c₁.exitsCoveredByBlocks labels → c₂.exitsCoveredByBlocks labels := by
  induction hstep with
  | step_cmd _ => intro _ _; trivial
  | step_admin hadmin =>
      intro labels hcov
      exact step_preserves_exitsCoveredByBlocks P (noCommandEvalE P CmdT)
        labels _ _ hadmin hcov
  | step_seq_inner _ ih =>
      intro labels hcov
      exact ⟨ih labels hcov.1, hcov.2⟩
  | step_block_body _ ih =>
      intro labels hcov
      rename_i inner emitted inner' label σ_parent _
      cases label with
      | none => exact ih labels hcov
      | some l => exact ih (l :: labels) hcov

/-- Well-paired statement lists cannot escape via `.exiting` under the traced
semantics. -/
theorem stmts_exitsCoveredByBlocks_noEscapeE
    (bss : List (Stmt P CmdT))
    (hwp : Block.exitsCoveredByBlocks [] bss) :
    ∀ (ρ : Env P) (lbl : String) (ρ' : Env P) {tr : List EventT},
      ¬ StepStmtStarE P EvalCmd (.stmts bss ρ) tr (.exiting lbl ρ') := by
  intro ρ lbl ρ' tr hstar
  suffices h_pres : ∀ (c₁ : Config P CmdT) (tr' : List EventT) (c₂ : Config P CmdT),
      StepStmtStarE P EvalCmd c₁ tr' c₂ →
      c₁.exitsCoveredByBlocks ([] : List String) →
      c₂.exitsCoveredByBlocks ([] : List String) by
    have hwp' := h_pres _ _ _ hstar
      (show Config.exitsCoveredByBlocks [] (.stmts bss ρ) from hwp)
    exact absurd hwp' (by simp [Config.exitsCoveredByBlocks])
  intro c₁ tr' c₂ hstar_c
  induction hstar_c with
  | refl => exact id
  | step _ _ _ _ _ hstep _ ih =>
      intro hcov
      exact ih (stepStmtE_preserves_exitsCoveredByBlocks EvalCmd hstep _ hcov)

/-- A statement whose exits are all caught by enclosing blocks cannot escape via
`.exiting` under the traced semantics: the `.stmt` analogue of
`stmts_exitsCoveredByBlocks_noEscapeE`. -/
theorem exitsCoveredByBlocks_noEscapeE
    (s : Stmt P CmdT)
    (hwp : s.exitsCoveredByBlocks []) :
    ∀ (ρ : Env P) (lbl : String) (ρ' : Env P) {tr : List EventT},
      ¬ StepStmtStarE P EvalCmd (.stmt s ρ) tr (.exiting lbl ρ') := by
  intro ρ lbl ρ' tr hstar
  suffices h_pres : ∀ (c₁ : Config P CmdT) (tr' : List EventT) (c₂ : Config P CmdT),
      StepStmtStarE P EvalCmd c₁ tr' c₂ →
      c₁.exitsCoveredByBlocks ([] : List String) →
      c₂.exitsCoveredByBlocks ([] : List String) by
    have hwp' := h_pres _ _ _ hstar
      (show Config.exitsCoveredByBlocks [] (.stmt s ρ) from hwp)
    exact absurd hwp' (by simp [Config.exitsCoveredByBlocks])
  intro c₁ tr' c₂ hstar_c
  induction hstar_c with
  | refl => exact id
  | step _ _ _ _ _ hstep _ ih =>
      intro hcov
      exact ih (stepStmtE_preserves_exitsCoveredByBlocks EvalCmd hstep _ hcov)

/-- An exiting head statement makes the whole traced list exit with the same
label and trace: the event analogue of `stmts_cons_exiting`. -/
private theorem stmts_cons_exitE
    (s : Stmt P CmdT) (ss : List (Stmt P CmdT)) (ρ ρ' : Env P) (lbl : String)
    {tr : List EventT}
    (h : StepStmtStarE P EvalCmd (.stmt s ρ) tr (.exiting lbl ρ')) :
    StepStmtStarE P EvalCmd (.stmts (s :: ss) ρ) tr (.exiting lbl ρ') := by
  have hchain := ReflTransTrace.trans _
    (ReflTransTrace.step _ _ _ _ _ (.step_admin .step_stmts_cons)
      (seq_inner_starE EvalCmd (ss := ss) h))
    (ReflTransTrace.step _ _ _ _ _ (.step_admin .step_seq_exit) (.refl _))
  simpa using hchain

/-- Decompose a *finished* traced run of `.stmts (ss₁ ++ ss₂)` — terminal or
exiting — by what `ss₁` did: either `ss₁` escaped on its own (consuming the
whole trace, `ss₂` never running), or `ss₁` terminated at some `ρ₁` with a
prefix trace `tr₁` from which `ss₂` finished the same way with the remaining
`tr₂`, splitting the trace chronologically as `tr₁ ++ tr₂`. The event analogue
of `stmts_append_done`. -/
theorem stmts_append_doneE
    (ss₁ ss₂ : List (Stmt P CmdT)) (ρ ρ' : Env P) {tr : List EventT}
    (h : StepStmtStarE P EvalCmd (.stmts (ss₁ ++ ss₂) ρ) tr (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE P EvalCmd
        (.stmts (ss₁ ++ ss₂) ρ) tr (.exiting lbl ρ')) :
    (∃ lbl, StepStmtStarE P EvalCmd (.stmts ss₁ ρ) tr (.exiting lbl ρ')) ∨
    (∃ ρ₁ tr₁ tr₂, tr = tr₁ ++ tr₂ ∧
      StepStmtStarE P EvalCmd (.stmts ss₁ ρ) tr₁ (.terminal ρ₁) ∧
      (StepStmtStarE P EvalCmd (.stmts ss₂ ρ₁) tr₂ (.terminal ρ') ∨
       ∃ lbl, StepStmtStarE P EvalCmd
         (.stmts ss₂ ρ₁) tr₂ (.exiting lbl ρ'))) := by
  induction ss₁ generalizing ρ tr with
  | nil =>
      -- empty prefix: it terminates in place emitting nothing; ss₂ ran the whole trace
      refine .inr ⟨ρ, [], tr, by simp, ?_, ?_⟩
      · exact ReflTransTrace.step (r := StepStmtE P EvalCmd)
          _ _ _ _ _ (StepStmtE.step_admin StepStmt.step_stmts_nil) (.refl _)
      · simpa using h
  | cons s rest ih =>
      simp only [List.cons_append] at h
      -- classify the head, splitting the trace at the head/tail boundary
      have hhead :
          (∃ lbl, StepStmtStarE P EvalCmd (.stmt s ρ) tr (.exiting lbl ρ')) ∨
          (∃ ρ_mid trh trt, tr = trh ++ trt ∧
            StepStmtStarE P EvalCmd (.stmt s ρ) trh (.terminal ρ_mid) ∧
            (StepStmtStarE P EvalCmd
                (.stmts (rest ++ ss₂) ρ_mid) trt (.terminal ρ') ∨
             ∃ lbl, StepStmtStarE P EvalCmd
                (.stmts (rest ++ ss₂) ρ_mid) trt (.exiting lbl ρ'))) := by
        rcases h with hterm | ⟨lbl, hexit⟩
        · rcases stmts_cons_headE EvalCmd hterm with ⟨hcfg, _⟩ | hseq
          · simp at hcfg
          · obtain ⟨ρ_mid, trh, trt, htr, hh, ht⟩ :=
              seq_reaches_terminalE EvalCmd hseq
            exact .inr ⟨ρ_mid, trh, trt, htr, hh, .inl ht⟩
        · rcases stmts_cons_headE EvalCmd hexit with ⟨hcfg, _⟩ | hseq
          · simp at hcfg
          · rcases seq_reaches_exitingE EvalCmd hseq with hh | ⟨ρ_mid, trh, trt, htr, hh, ht⟩
            · exact .inl ⟨lbl, hh⟩
            · exact .inr ⟨ρ_mid, trh, trt, htr, hh, .inr ⟨lbl, ht⟩⟩
      rcases hhead with ⟨lbl, hexit_s⟩ | ⟨ρ_mid, trh, trt, htr, hterm_s, htail⟩
      · exact .inl ⟨lbl, stmts_cons_exitE EvalCmd s rest ρ ρ' lbl hexit_s⟩
      · have hcons : StepStmtStarE P EvalCmd
            (.stmts (s :: rest) ρ) trh (.stmts rest ρ_mid) :=
          stmts_cons_stepE EvalCmd s rest ρ ρ_mid hterm_s
        rcases ih ρ_mid htail with
          ⟨lbl, hexit_rest⟩ | ⟨ρ₁, tr₁', tr₂', htr', hterm_rest, hfin⟩
        · refine .inl ⟨lbl, ?_⟩
          rw [htr]
          exact ReflTransTrace.trans _ hcons hexit_rest
        · refine .inr ⟨ρ₁, trh ++ tr₁', tr₂', ?_, ?_, hfin⟩
          · rw [htr, htr']; simp [List.append_assoc]
          · exact ReflTransTrace.trans _ hcons hterm_rest

end EventTraceStructural

/-! ## Traced block-frame lifting, completion inversion, and scope plumbing

Event-trace (`StepStmtStarE`) analogues of the failure-flag block metatheory:
lifting a run through a `.block` frame, inverting a finished block run (terminal
or exiting) with the emitted trace preserved, factory preservation,
and the scope-aware `varsUndefined`/`projectStore_eq_dropVars` plumbing.  Command
none-preservation enters only through an abstract `h_cmd` premise so the results
apply to any `EvalCmdParamE`. -/

section EventBlockScope

variable {P : PureExpr} {CmdT : Type} {EventT : Type} [HasBool P]
  {EvalCmd : EvalCmdParamE P CmdT EventT}

/-- A single event step is a one-step run carrying the same trace. -/
theorem StepStmtStarE.single
    {c c' : Config P CmdT} {e : List EventT}
    (h : StepStmtE P EvalCmd c e c') : StepStmtStarE P EvalCmd c e c' := by
  simpa using ReflTransTrace.step c e c' [] c' h (.refl _)

/-- A command configuration steps by running the command's event semantics,
reaching a terminal configuration carrying the updated store. -/
theorem StepStmtE.cmd_cases
    {c : CmdT} {ρ : Env P} {e : List EventT} {c' : Config P CmdT}
    (h : StepStmtE P EvalCmd (.stmt (.cmd c) ρ) e c') :
    ∃ σ', EvalCmd ρ.factory ρ.store c σ' e ∧ c' = .terminal { ρ with store := σ' } := by
  cases h with
  | step_cmd h => exact ⟨_, h, rfl⟩
  | step_admin h =>
    cases h with
    | step_cmd h => exact h.elim

/-- Case analysis on one event step of a `.block` configuration: either the inner
configuration steps, or it was terminal/exiting, in which case the scope is left
by projecting the inner store and the result finishes, matches the block's label,
or propagates a mismatched exit. -/
theorem StepStmtE.block_cases
    {l : Option String} {σp : SemanticStore P} {inner : Config P CmdT} {e : List EventT}
    {c' : Config P CmdT}
    (h : StepStmtE P EvalCmd (.block l σp inner) e c') :
    (∃ inner', StepStmtE P EvalCmd inner e inner' ∧ c' = .block l σp inner') ∨
    (∃ ρ, inner = .terminal ρ ∧ e = [] ∧
      c' = .terminal { ρ with store := projectStore σp ρ.store }) ∨
    (∃ l' ρ, inner = .exiting l' ρ ∧ e = [] ∧ l = some l' ∧
      c' = .terminal { ρ with store := projectStore σp ρ.store }) ∨
    (∃ l' ρ, inner = .exiting l' ρ ∧ e = [] ∧ l ≠ some l' ∧
      c' = .exiting l' { ρ with store := projectStore σp ρ.store }) := by
  cases h with
  | step_block_body h => exact .inl ⟨_, h, rfl⟩
  | step_admin h =>
    cases h with
    | step_block_body h => exact .inl ⟨_, .step_admin h, rfl⟩
    | step_block_done => exact .inr (.inl ⟨_, rfl, rfl, rfl⟩)
    | step_block_exit_match hl => exact .inr (.inr (.inl ⟨_, _, rfl, rfl, hl, rfl⟩))
    | step_block_exit_mismatch hl => exact .inr (.inr (.inr ⟨_, _, rfl, rfl, hl, rfl⟩))

/-- An exiting configuration takes no event step. -/
theorem StepStmtE.exiting_false
    {l : String} {ρ : Env P} {e : List EventT} {c' : Config P CmdT}
    (h : StepStmtE P EvalCmd (.exiting l ρ) e c') : False := by
  cases h with
  | step_admin h => cases h


/-- No traced event step leaves a terminal configuration. -/
private theorem stepStmtE_from_terminal_none
    {ρ : Env P} {emitted : List EventT} {cfg : Config P CmdT}
    (h : StepStmtE P EvalCmd (.terminal ρ) emitted cfg) : False := by
  cases h with
  | step_admin hadmin => cases hadmin

/-- A traced run from a stuck terminal config is reflexive and emits nothing. -/
theorem stepStmtStarE_from_terminal
    {ρ : Env P} {tr : List EventT} {cfg : Config P CmdT}
    (h : StepStmtStarE P EvalCmd (.terminal ρ) tr cfg) :
    cfg = .terminal ρ ∧ tr = [] := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step _ _ _ _ _ hstep _ => exact (stepStmtE_from_terminal_none hstep).elim

/-- No traced event step leaves an exiting configuration. -/
private theorem stepStmtE_from_exiting_none
    {lbl : String} {ρ : Env P} {emitted : List EventT} {cfg : Config P CmdT}
    (h : StepStmtE P EvalCmd (.exiting lbl ρ) emitted cfg) : False := by
  cases h with
  | step_admin hadmin => cases hadmin

/-- A traced run from a stuck exiting config is reflexive and emits nothing. -/
theorem stepStmtStarE_from_exiting
    {lbl : String} {ρ : Env P} {tr : List EventT} {cfg : Config P CmdT}
    (h : StepStmtStarE P EvalCmd (.exiting lbl ρ) tr cfg) :
    cfg = .exiting lbl ρ ∧ tr = [] := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step _ _ _ _ _ hstep _ => exact (stepStmtE_from_exiting_none hstep).elim

/-- Lift a traced inner run through a `.block` frame, preserving its trace. -/
theorem block_inner_starE
    {inner inner' : Config P CmdT} {label : Option String}
    {σ_parent : SemanticStore P} {tr : List EventT}
    (h : StepStmtStarE P EvalCmd inner tr inner') :
    StepStmtStarE P EvalCmd
      (.block label σ_parent inner) tr (.block label σ_parent inner') := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ _ _ hstep _ ih => exact .step _ _ _ _ _ (.step_block_body hstep) ih

/-- General inversion of a finished traced `.block` run: either the block is
still open, or its body reached a terminal/exiting outcome (with the *same*
trace, since block enter/exit steps emit nothing) and the block projected the
result store through the parent, restoring the parent factory. -/
theorem block_run_to_finalE
    {inner : Config P CmdT} {label : Option String}
    {σ_parent : SemanticStore P}
    {cfg : Config P CmdT} {tr : List EventT}
    (hstar : StepStmtStarE P EvalCmd
      (.block label σ_parent inner) tr cfg) :
    (∃ inner', cfg = .block label σ_parent inner' ∧
        StepStmtStarE P EvalCmd inner tr inner')
    ∨ (∃ ρ_i, StepStmtStarE P EvalCmd inner tr (.terminal ρ_i) ∧
        cfg = .terminal { ρ_i with store := projectStore σ_parent ρ_i.store})
    ∨ (∃ l ρ_i, label = .some l ∧
        StepStmtStarE P EvalCmd inner tr (.exiting l ρ_i) ∧
        cfg = .terminal { ρ_i with store := projectStore σ_parent ρ_i.store})
    ∨ (∃ lbl ρ_i, label ≠ .some lbl ∧
        StepStmtStarE P EvalCmd inner tr (.exiting lbl ρ_i) ∧
        cfg = .exiting lbl { ρ_i with store := projectStore σ_parent ρ_i.store}) := by
  suffices h_gen : ∀ src tr cfg, StepStmtStarE P EvalCmd src tr cfg →
      ∀ inner, src = .block label σ_parent inner →
      (∃ inner', cfg = .block label σ_parent inner' ∧
          StepStmtStarE P EvalCmd inner tr inner')
      ∨ (∃ ρ_i, StepStmtStarE P EvalCmd inner tr (.terminal ρ_i) ∧
          cfg = .terminal { ρ_i with store := projectStore σ_parent ρ_i.store})
      ∨ (∃ l ρ_i, label = .some l ∧
          StepStmtStarE P EvalCmd inner tr (.exiting l ρ_i) ∧
          cfg = .terminal { ρ_i with store := projectStore σ_parent ρ_i.store})
      ∨ (∃ lbl ρ_i, label ≠ .some lbl ∧
          StepStmtStarE P EvalCmd inner tr (.exiting lbl ρ_i) ∧
          cfg = .exiting lbl { ρ_i with store := projectStore σ_parent ρ_i.store}) from
    h_gen _ _ _ hstar _ rfl
  intro src tr cfg hstar_g
  induction hstar_g with
  | refl x => intro inner hsrc; subst hsrc; exact .inl ⟨inner, rfl, .refl _⟩
  | step x emitted y restTr z hstep hrest ih =>
    intro inner hsrc; subst hsrc
    cases hstep with
    | step_block_body hE =>
      rcases ih _ rfl with
        ⟨inner'', hcfg, hrun⟩ | ⟨ρ_i, hrun, hcfg⟩ | ⟨l, ρ_i, hl, hrun, hcfg⟩ | ⟨lbl, ρ_i, hne, hrun, hcfg⟩
      · exact .inl ⟨inner'', hcfg, .step _ _ _ _ _ hE hrun⟩
      · exact .inr (.inl ⟨ρ_i, .step _ _ _ _ _ hE hrun, hcfg⟩)
      · exact .inr (.inr (.inl ⟨l, ρ_i, hl, .step _ _ _ _ _ hE hrun, hcfg⟩))
      · exact .inr (.inr (.inr ⟨lbl, ρ_i, hne, .step _ _ _ _ _ hE hrun, hcfg⟩))
    | step_admin hadmin =>
      cases hadmin with
      | step_block_body hinner =>
        rcases ih _ rfl with
          ⟨inner'', hcfg, hrun⟩ | ⟨ρ_i, hrun, hcfg⟩ | ⟨l, ρ_i, hl, hrun, hcfg⟩ | ⟨lbl, ρ_i, hne, hrun, hcfg⟩
        · exact .inl ⟨inner'', hcfg, .step _ _ _ _ _ (.step_admin hinner) hrun⟩
        · exact .inr (.inl ⟨ρ_i, .step _ _ _ _ _ (.step_admin hinner) hrun, hcfg⟩)
        · exact .inr (.inr (.inl ⟨l, ρ_i, hl, .step _ _ _ _ _ (.step_admin hinner) hrun, hcfg⟩))
        · exact .inr (.inr (.inr ⟨lbl, ρ_i, hne, .step _ _ _ _ _ (.step_admin hinner) hrun, hcfg⟩))
      | step_block_done =>
        obtain ⟨hz, hrestnil⟩ := stepStmtStarE_from_terminal hrest
        subst hrestnil
        exact .inr (.inl ⟨_, .refl _, hz⟩)
      | step_block_exit_match hlabel =>
        obtain ⟨hz, hrestnil⟩ := stepStmtStarE_from_terminal hrest
        subst hrestnil
        exact .inr (.inr (.inl ⟨_, _, hlabel, .refl _, hz⟩))
      | step_block_exit_mismatch hne =>
        obtain ⟨hz, hrestnil⟩ := stepStmtStarE_from_exiting hrest
        subst hrestnil
        exact .inr (.inr (.inr ⟨_, _, hne, .refl _, hz⟩))

/-- Invert a *finished* traced `.block` run — terminal or exiting — into the
inner run (carrying the same trace) plus the parent-store projection. -/
theorem block_reaches_doneE
    {inner : Config P CmdT} {label : Option String}
    {σ_parent : SemanticStore P} {ρ' : Env P} {tr : List EventT}
    (hdone :
      StepStmtStarE P EvalCmd
        (.block label σ_parent inner) tr (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE P EvalCmd
        (.block label σ_parent inner) tr (.exiting lbl ρ')) :
    ∃ ρ_inner,
      (StepStmtStarE P EvalCmd inner tr (.terminal ρ_inner) ∨
       ∃ lbl, StepStmtStarE P EvalCmd inner tr (.exiting lbl ρ_inner)) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store} := by
  rcases hdone with hterm | ⟨lbl0, hexit⟩
  · rcases block_run_to_finalE hterm with
      ⟨_, hcfg, _⟩ | ⟨ρ_i, hrun, hcfg⟩ | ⟨l, ρ_i, _, hrun, hcfg⟩ | ⟨lbl, ρ_i, _, hrun, hcfg⟩
    · simp at hcfg
    · injection hcfg with hρ; exact ⟨ρ_i, .inl hrun, hρ⟩
    · injection hcfg with hρ; exact ⟨ρ_i, .inr ⟨l, hrun⟩, hρ⟩
    · simp at hcfg
  · rcases block_run_to_finalE hexit with
      ⟨_, hcfg, _⟩ | ⟨ρ_i, hrun, hcfg⟩ | ⟨l, ρ_i, _, hrun, hcfg⟩ | ⟨lbl, ρ_i, _, hrun, hcfg⟩
    · simp at hcfg
    · simp at hcfg
    · simp at hcfg
    · injection hcfg with _ hρ; exact ⟨ρ_i, .inr ⟨lbl, hrun⟩, hρ⟩

/-- Invert a finished traced run of `.stmt (.block l ss md)`: step through the
block-enter, then invert the block completion, yielding the body run at the same
trace and the parent-store projection of the result. -/
theorem stmt_block_reaches_doneE
    {ss : List (Stmt P CmdT)} {l : String} {md : MetaData P} {ρ₀ ρ' : Env P} {tr : List EventT}
    (hdone :
      StepStmtStarE P EvalCmd (.stmt (.block l ss md) ρ₀) tr (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE P EvalCmd (.stmt (.block l ss md) ρ₀) tr (.exiting lbl ρ')) :
    ∃ ρ_inner,
      (StepStmtStarE P EvalCmd (.stmts ss ρ₀) tr (.terminal ρ_inner) ∨
       ∃ lbl, StepStmtStarE P EvalCmd (.stmts ss ρ₀) tr (.exiting lbl ρ_inner)) ∧
      ρ' = { ρ_inner with store := projectStore ρ₀.store ρ_inner.store} := by
  rcases hdone with hterm | ⟨lbl, hexit⟩
  · cases hterm with
    | step _ _ _ _ _ hstep hrest =>
      cases hstep with
      | step_admin hadmin => cases hadmin with
        | step_block =>
          obtain ⟨ρ_inner, hinner, heq⟩ := block_reaches_doneE (.inl hrest)
          exact ⟨ρ_inner, by simpa using hinner, heq⟩
  · cases hexit with
    | step _ _ _ _ _ hstep hrest =>
      cases hstep with
      | step_admin hadmin => cases hadmin with
        | step_block =>
          obtain ⟨ρ_inner, hinner, heq⟩ := block_reaches_doneE (.inr ⟨lbl, hrest⟩)
          exact ⟨ρ_inner, by simpa using hinner, heq⟩

/-- Single-step preservation of scope-aware `Config.varsUndefined true` under a
traced event step, given the command evaluator only defines what the command
declares (`h_cmd`). -/
private theorem Config.varsUndefinedScoped_stepE_of [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasIdent P] [DecidableEq P.Ident] [HasVarsImp P CmdT]
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : List EventT} {y : P.Ident},
      EvalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    {Q : P.Ident → Prop} {cfg cfg' : Config P CmdT} {tr : List EventT}
    (h_step : StepStmtE P EvalCmd cfg tr cfg')
    (h_inv : Config.varsUndefined true (P := P) Q cfg) :
    Config.varsUndefined true (P := P) Q cfg' := by
  induction h_step with
  | step_cmd h_eval =>
    intro y hQ
    obtain ⟨h_none, h_ndef⟩ := h_inv y hQ
    exact h_cmd h_eval h_none (by simpa [Stmt.definedVars] using h_ndef)
  | step_admin hadmin =>
    exact Config.varsUndefinedScoped_step_of (evalCmd := noCommandEvalE P CmdT)
      (fun he _ _ => by simp [noCommandEvalE] at he) hadmin h_inv
  | step_seq_inner _ ih => exact ⟨ih h_inv.1, h_inv.2⟩
  | step_block_body _ _ => exact h_inv

/-- A scope-aware `Config.varsUndefined true` invariant is preserved across a
traced run when each command defines only the variables it declares. -/
theorem Config.varsUndefinedScoped_star_ofE [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasIdent P] [DecidableEq P.Ident] [HasVarsImp P CmdT]
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : List EventT} {y : P.Ident},
      EvalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    {Q : P.Ident → Prop} {cfg cfg' : Config P CmdT} {tr : List EventT}
    (h_run : StepStmtStarE P EvalCmd cfg tr cfg')
    (h_inv : Config.varsUndefined true (P := P) Q cfg) :
    Config.varsUndefined true (P := P) Q cfg' := by
  induction h_run with
  | refl => exact h_inv
  | step _ _ _ _ _ h_step _ ih =>
    exact ih (Config.varsUndefinedScoped_stepE_of h_cmd h_step h_inv)

/-- **Leaving a block drops exactly the names its body scopes**, event-trace
version: the store handed back after a finished traced body run is determined by
the body alone. -/
theorem projectStore_eq_dropVarsE [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasIdent P] [DecidableEq P.Ident] [HasVarsImp P CmdT]
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : List EventT} {y : P.Ident},
      EvalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    {ss : List (Stmt P CmdT)} {ρ₀ ρ : Env P} {tr : List EventT}
    (hdefs : ∀ x ∈ Block.definedVars (P := P) (C := CmdT) ss true, ρ₀.store x = none)
    (hrun :
      StepStmtStarE P EvalCmd (.stmts ss ρ₀) tr (.terminal ρ) ∨
      ∃ lbl, StepStmtStarE P EvalCmd (.stmts ss ρ₀) tr (.exiting lbl ρ)) :
    projectStore ρ₀.store ρ.store
      = dropVars (Block.definedVars (P := P) (C := CmdT) ss true) ρ.store := by
  funext n
  by_cases hmem : n ∈ Block.definedVars (P := P) (C := CmdT) ss true
  · simp [projectStore, dropVars, hmem, hdefs n hmem]
  · cases hq : ρ₀.store n with
    | some v => simp [projectStore, dropVars, hmem, hq]
    | none =>
      have hstart : Config.varsUndefined true (P := P) (· = n) (.stmts ss ρ₀) := by
        rintro y rfl
        exact ⟨hq, all_not_mem_definedVars_of_block hmem⟩
      have hnone : ρ.store n = none := by
        rcases hrun with hterm | ⟨_, hexit⟩
        · exact Config.varsUndefinedScoped_star_ofE h_cmd hterm hstart n rfl
        · exact Config.varsUndefinedScoped_star_ofE h_cmd hexit hstart n rfl
      simp [projectStore, dropVars, hmem, hq, hnone]

end EventBlockScope

/-! ## Type-valued traced completion inversion for the loop rule

`Type`-valued (`ReflTransTraceT`) analogues of `seqT_reaches_terminal` and
`stmtsT_cons_terminal`, carrying the
emitted trace *and* a strict step-count bound.  The event `while_rule` recurses
on the strictly shrinking length of the remaining loop derivation while
composing each iteration's trace chronologically. -/

section EventTraceReflTransTHelpers

variable {P : PureExpr} {CmdT : Type} {EventT : Type} [HasBool P]
  {EvalCmd : EvalCmdParamE P CmdT EventT}


/-- Invert a traced `.seq inner ss` run reaching terminal: the inner terminates
emitting a prefix, then the tail runs to terminal emitting the suffix, splitting
the trace chronologically with a strict length bound. -/
theorem seqT_reaches_terminalE
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)} {ρ' : Env P} {tr : List EventT}
    (hstar : ReflTransTraceT (StepStmtE P EvalCmd)
      (.seq inner ss) tr (.terminal ρ')) :
    ∃ (ρ₁ : Env P) (tr₁ tr₂ : List EventT), tr = tr₁ ++ tr₂ ∧
      ∃ (h1 : ReflTransTraceT (StepStmtE P EvalCmd) inner tr₁ (.terminal ρ₁)),
      ∃ (h2 : ReflTransTraceT (StepStmtE P EvalCmd) (.stmts ss ρ₁) tr₂ (.terminal ρ')),
      h1.len + h2.len < hstar.len := by
  match hstar with
  | .step _ emitted _ restTr _ (.step_seq_inner hE) hrest =>
    obtain ⟨ρ₁, tr₁, tr₂, htr, h1, h2, hlen⟩ := seqT_reaches_terminalE hrest
    exact ⟨ρ₁, emitted ++ tr₁, tr₂, by rw [htr]; simp [List.append_assoc],
      .step _ _ _ _ _ hE h1, h2, by simp only [ReflTransTraceT.len]; omega⟩
  | .step _ _ _ restTr _ (.step_admin (.step_seq_inner hE')) hrest =>
    obtain ⟨ρ₁, tr₁, tr₂, htr, h1, h2, hlen⟩ := seqT_reaches_terminalE hrest
    exact ⟨ρ₁, tr₁, tr₂, by simp [htr],
      .step _ _ _ _ _ (.step_admin hE') h1, h2, by simp only [ReflTransTraceT.len]; omega⟩
  | .step _ _ _ restTr _ (.step_admin .step_seq_done) hrest =>
    exact ⟨_, [], restTr, by simp, .refl _, hrest, by simp only [ReflTransTraceT.len]; omega⟩
  | .step _ _ _ _ _ (.step_admin .step_seq_exit) hrest =>
    obtain ⟨hc, _⟩ := stepStmtStarE_from_exiting (reflTransTraceT_to_prop hrest)
    exact absurd hc (by simp)
termination_by hstar.len
decreasing_by all_goals (simp only [ReflTransTraceT.len]; omega)

/-- Invert a traced `.stmts (s :: rest)` run reaching terminal: the head
terminates emitting a prefix, then the tail list runs to terminal emitting the
suffix, with a strict length bound (the leading `step_stmts_cons` is consumed). -/
theorem stmtsT_cons_terminalE
    {s : Stmt P CmdT} {rest : List (Stmt P CmdT)} {ρ₀ ρ' : Env P} {tr : List EventT}
    (hstar : ReflTransTraceT (StepStmtE P EvalCmd)
      (.stmts (s :: rest) ρ₀) tr (.terminal ρ')) :
    ∃ (ρ₁ : Env P) (tr₁ tr₂ : List EventT), tr = tr₁ ++ tr₂ ∧
      ∃ (h1 : ReflTransTraceT (StepStmtE P EvalCmd) (.stmt s ρ₀) tr₁ (.terminal ρ₁)),
      ∃ (h2 : ReflTransTraceT (StepStmtE P EvalCmd) (.stmts rest ρ₁) tr₂ (.terminal ρ')),
      h1.len + h2.len + 2 ≤ hstar.len := by
  match hstar with
  | .step _ _ _ restTr _ (.step_admin .step_stmts_cons) hrest =>
    obtain ⟨ρ₁, tr₁, tr₂, htr, h1, h2, hlen⟩ := seqT_reaches_terminalE hrest
    exact ⟨ρ₁, tr₁, tr₂, by simpa using htr, h1, h2, by simp only [ReflTransTraceT.len]; omega⟩

/-- Extend a terminating statement-list run with an unexecuted suffix. -/
theorem stmts_prefix_terminal_appendE
    (pfx sfx : List (Stmt P CmdT)) (ρ ρ' : Env P)
    {trace : List EventT}
    (h : StepStmtStarE P EvalCmd (.stmts pfx ρ) trace (.terminal ρ')) :
    StepStmtStarE P EvalCmd (.stmts (pfx ++ sfx) ρ) trace (.stmts sfx ρ') := by
  induction pfx generalizing ρ trace with
  | nil =>
      obtain ⟨htrace, hcfg⟩ := stmts_nil_runE EvalCmd h
      subst htrace
      rcases hcfg with hcfg | hcfg
      · simp at hcfg
      · injection hcfg with hρ
        subst hρ
        exact .refl _
  | cons s rest ih =>
      rcases stmts_cons_headE EvalCmd h with hcfg | hseq
      · simp at hcfg
      · obtain ⟨ρ₁, tr₁, tr₂, htrace, hs, hr⟩ :=
          seq_reaches_terminalE EvalCmd hseq
        subst trace
        exact ReflTransTrace.trans _
          (stmts_cons_stepE EvalCmd s (rest ++ sfx) ρ ρ₁ hs)
          (ih ρ₁ hr)

/-- Extend an exiting statement-list run with an unexecuted suffix. -/
theorem stmts_prefix_exiting_appendE
    (pfx sfx : List (Stmt P CmdT)) (ρ ρ' : Env P) (label : String)
    {trace : List EventT}
    (h : StepStmtStarE P EvalCmd (.stmts pfx ρ) trace (.exiting label ρ')) :
    StepStmtStarE P EvalCmd (.stmts (pfx ++ sfx) ρ) trace
      (.exiting label ρ') := by
  induction pfx generalizing ρ trace with
  | nil =>
      obtain ⟨_, hcfg⟩ := stmts_nil_runE EvalCmd h
      rcases hcfg with hcfg | hcfg <;> simp at hcfg
  | cons s rest ih =>
      rcases stmts_cons_headE EvalCmd h with hcfg | hseq
      · simp at hcfg
      · rcases seq_reaches_exitingE EvalCmd hseq with hs | htail
        · have hrun := ReflTransTrace.trans _
            (ReflTransTrace.step _ _ _ _ _ (.step_admin .step_stmts_cons)
              (seq_inner_starE EvalCmd (ss := rest ++ sfx) hs))
            (StepStmtStarE.single
              (c := .seq (.exiting label ρ') (rest ++ sfx))
              (.step_admin .step_seq_exit))
          simpa using hrun
        · obtain ⟨ρ₁, tr₁, tr₂, htrace, hs, hr⟩ := htail
          subst trace
          exact ReflTransTrace.trans _
            (stmts_cons_stepE EvalCmd s (rest ++ sfx) ρ ρ₁ hs)
            (ih ρ₁ hr)

/-- Extend a finite statement-list prefix run with an unexecuted suffix. -/
theorem stmts_prefix_appendE
    (pfx sfx : List (Stmt P CmdT)) (ρ : Env P)
    {cfg : Config P CmdT} {trace : List EventT}
    (h : StepStmtStarE P EvalCmd (.stmts pfx ρ) trace cfg) :
    ∃ cfg', StepStmtStarE P EvalCmd (.stmts (pfx ++ sfx) ρ) trace cfg' := by
  induction pfx generalizing ρ trace cfg with
  | nil =>
      obtain ⟨htrace, _⟩ := stmts_nil_runE EvalCmd h
      subst htrace
      exact ⟨_, .refl _⟩
  | cons s rest ih =>
      rcases stmts_cons_headE EvalCmd h with ⟨hcfg, htrace⟩ | hseq
      · subst hcfg
        subst htrace
        exact ⟨_, .refl _⟩
      · rcases seq_run_decomposeE EvalCmd hseq with
          ⟨inner', hcfg, hs⟩ | ⟨ρ₁, tr₁, tr₂, htrace, hs, hr⟩ |
            ⟨label, ρ₁, hcfg, hs⟩
        · subst hcfg
          refine ⟨.seq inner' (rest ++ sfx), ?_⟩
          exact ReflTransTrace.step _ _ _ _ _ (.step_admin .step_stmts_cons)
            (seq_inner_starE EvalCmd hs)
        · obtain ⟨cfg', hr'⟩ := ih ρ₁ hr
          subst trace
          exact ⟨cfg', ReflTransTrace.trans _
            (stmts_cons_stepE EvalCmd s (rest ++ sfx) ρ ρ₁ hs) hr'⟩
        · subst hcfg
          refine ⟨.exiting label ρ₁, ?_⟩
          have hrun := ReflTransTrace.trans _
            (ReflTransTrace.step _ _ _ _ _ (.step_admin .step_stmts_cons)
              (seq_inner_starE EvalCmd (ss := rest ++ sfx) hs))
            (StepStmtStarE.single
              (c := .seq (.exiting label ρ₁) (rest ++ sfx))
              (.step_admin .step_seq_exit))
          simpa using hrun

end EventTraceReflTransTHelpers


/-! ## Event-trace `varsDefined` / `storeWellDefined` preservation engines

These reuse the failure-flag `_step_of` lemmas for administrative steps, so they
are stated with `[HasBoolOps P]` only (never a *separate* `[HasBool P]`): that
keeps `HasBool`/`HasVal` resolved uniformly through the `HasBoolOps → HasBool →
HasVal` hierarchy, matching the instances the failure-flag lemmas use. -/

section EventInvariantEngines

variable {P : PureExpr} {CmdT : Type} {EventT : Type} [HasBoolOps P]
  {EvalCmd : EvalCmdParamE P CmdT EventT}


/-- Single traced event step preserves `Config.varsDefined`, given a command
evaluator that never undefines a slot (`h_cmd`). -/
private theorem Config.varsDefined_stepE_of
    [HasFvar P] [HasFvars P] [DecidableEq P.Ident]
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : List EventT} {y : P.Ident},
      EvalCmd f σ c σ' emitted → (σ y).isSome = true → (σ' y).isSome = true)
    {Q : P.Ident → Prop} {cfg cfg' : Config P CmdT} {tr : List EventT}
    (h_step : StepStmtE P EvalCmd cfg tr cfg')
    (h_inv : Config.varsDefined Q cfg) :
    Config.varsDefined Q cfg' := by
  induction h_step with
  | step_cmd h_eval => exact fun y hQ => h_cmd h_eval (h_inv y hQ)
  | step_admin hadmin =>
    exact Config.varsDefined_step_of (evalCmd := noCommandEvalE P CmdT)
      (fun he _ => by simp [noCommandEvalE] at he) hadmin h_inv
  | step_seq_inner _ ih => exact ih h_inv
  | step_block_body _ ih => exact ⟨h_inv.1, ih h_inv.2⟩

/-- `Config.varsDefined` is preserved across a traced run when command
evaluation never undefines an existing store slot. -/
theorem Config.varsDefined_star_ofE
    [HasFvar P] [HasFvars P] [DecidableEq P.Ident]
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : List EventT} {y : P.Ident},
      EvalCmd f σ c σ' emitted → (σ y).isSome = true → (σ' y).isSome = true)
    {Q : P.Ident → Prop} {cfg cfg' : Config P CmdT} {tr : List EventT}
    (h_run : StepStmtStarE P EvalCmd cfg tr cfg')
    (h_inv : Config.varsDefined Q cfg) :
    Config.varsDefined Q cfg' := by
  induction h_run with
  | refl => exact h_inv
  | step _ _ _ _ _ h_step _ ih =>
    exact ih (Config.varsDefined_stepE_of h_cmd h_step h_inv)

/-- A single traced event step preserves the environment's factory. -/
theorem stepE_preserves_factory
    {cfg cfg' : Config P CmdT} {tr : List EventT}
    (h_step : StepStmtE P EvalCmd cfg tr cfg') :
    cfg.getEnv.factory = cfg'.getEnv.factory := by
  induction h_step with
  | step_cmd _ => simp [Config.getEnv]
  | step_admin hadmin => exact step_preserves_factory P (noCommandEvalE P CmdT) _ _ hadmin
  | step_seq_inner _ ih => simpa [Config.getEnv] using ih
  | step_block_body _ ih => simpa [Config.getEnv] using ih

/-- A traced event run preserves the environment's factory. -/
theorem starE_preserves_factory
    {cfg cfg' : Config P CmdT} {tr : List EventT}
    (h_run : StepStmtStarE P EvalCmd cfg tr cfg') :
    cfg.getEnv.factory = cfg'.getEnv.factory := by
  induction h_run with
  | refl => rfl
  | step _ _ _ _ _ h_step _ ih =>
    exact (stepE_preserves_factory h_step).trans ih

/-- Single traced event step preserves `Config.storeWellDefined`, given the
command evaluator does (`h_cmd`). -/
private theorem Config.storeWellDefined_stepE_of
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : List EventT},
      EvalCmd f σ c σ' emitted → WellFormedStore σ f → WellFormedStore σ' f)
    {cfg cfg' : Config P CmdT} {tr : List EventT}
    (h_step : StepStmtE P EvalCmd cfg tr cfg')
    (h_inv : Config.storeWellDefined cfg) :
    Config.storeWellDefined cfg' := by
  induction h_step with
  | step_cmd h_eval => exact h_cmd h_eval h_inv
  | step_admin hadmin =>
    exact Config.storeWellDefined_step_of (evalCmd := noCommandEvalE P CmdT)
      (fun he _ => by simp [noCommandEvalE] at he) hadmin h_inv
  | step_seq_inner _ ih =>
    exact ih h_inv
  | step_block_body hinner ih =>
    exact ⟨stepE_preserves_factory hinner ▸ h_inv.1, ih h_inv.2⟩

/-- A configuration whose store holds only values remains store-well-defined
across a traced run when commands preserve store well-formedness. -/
theorem Config.storeWellDefined_star_ofE
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : List EventT},
      EvalCmd f σ c σ' emitted → WellFormedStore σ f → WellFormedStore σ' f)
    {cfg cfg' : Config P CmdT} {tr : List EventT}
    (h_run : StepStmtStarE P EvalCmd cfg tr cfg')
    (h_inv : Config.storeWellDefined cfg) :
    Config.storeWellDefined cfg' := by
  induction h_run with
  | refl => exact h_inv
  | step _ _ _ _ _ h_step _ ih =>
    exact ih (Config.storeWellDefined_stepE_of h_cmd h_step h_inv)

/-- A base-command event step preserves store well-formedness using the
value law at the step's unchanged factory. -/
theorem Config.storeWellDefined_step_evalCmdE
    {P : PureExpr} [HasFvar P] [HasBoolOps P] [HasFvars P] [LawfulHasVal P]
    {cfg cfg' : Config P (Cmd P)} {tr : Trace P}
    (hval : WellFormedSemanticEvalVal (P := P) cfg.getEnv.factory)
    (h_step : StepStmtE P (EvalCmdE P) cfg tr cfg')
    (h_inv : Config.storeWellDefined cfg) :
    Config.storeWellDefined cfg' := by
  induction h_step with
  | step_cmd h_eval => exact evalCmdE_storeWellDefined hval h_eval h_inv
  | step_admin hadmin =>
    exact Config.storeWellDefined_step_of (evalCmd := noCommandEvalE P (Cmd P))
      (fun he _ => by simp [noCommandEvalE] at he) hadmin h_inv
  | step_seq_inner _ ih => exact ih hval h_inv
  | step_block_body hinner ih =>
      exact ⟨stepE_preserves_factory hinner ▸ h_inv.1, ih hval h_inv.2⟩

/-- A base-command event run preserves store well-formedness using the value law
at its factory. -/
theorem Config.storeWellDefined_star_evalCmdE
    {P : PureExpr} [HasFvar P] [HasBoolOps P] [HasFvars P] [LawfulHasVal P]
    {cfg cfg' : Config P (Cmd P)} {tr : Trace P}
    (hval : WellFormedSemanticEvalVal (P := P) cfg.getEnv.factory)
    (h_run : StepStmtStarE P (EvalCmdE P) cfg tr cfg')
    (h_inv : Config.storeWellDefined cfg) :
    Config.storeWellDefined cfg' := by
  induction h_run with
  | refl => exact h_inv
  | step c _ c₁ _ _ h_step _ ih =>
    have h_inv₁ := Config.storeWellDefined_step_evalCmdE hval h_step h_inv
    have hfac : c.getEnv.factory = c₁.getEnv.factory := stepE_preserves_factory h_step
    exact ih (hfac ▸ hval) h_inv₁

/-- A slot defined at the start of a terminating base-command statement run
remains defined at the end. -/
private theorem stmt_preserves_isSomeE
    {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident]
    {y : P.Ident} {s : Stmt P (Cmd P)} {ρ ρ' : Env P} {tr : Trace P}
    (h_run : StepStmtStarE P (EvalCmdE P)
      (.stmt s ρ) tr (.terminal ρ'))
    (h_some : (ρ.store y).isSome = true) :
    (ρ'.store y).isSome = true :=
  Config.varsDefined_star_ofE
    (fun he hs => evalCmdE_preserves_isSome he hs)
    h_run
    (show Config.varDefined y (.stmt s ρ) from fun _ hz => hz ▸ h_some)
    y rfl

/-- A slot that starts undefined and is not defined at statement scope remains
undefined after a terminating base-command statement run. -/
theorem stmt_run_terminal_preserves_none_of_not_definedVars_trueE
    {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident]
    {y : P.Ident} {s : Stmt P (Cmd P)} {ρ ρ' : Env P} {tr : Trace P}
    (h_y_not_def : y ∉ Stmt.definedVars s true)
    (h_none : ρ.store y = none)
    (h_run : StepStmtStarE P (EvalCmdE P)
      (.stmt s ρ) tr (.terminal ρ')) :
    ρ'.store y = none :=
  Config.varsUndefinedScoped_star_ofE
    (fun he hn hnd =>
      evalCmdE_preserves_none_of_not_def he hn (fun hmem => hnd (by
        with_unfolding_all exact hmem)))
    h_run (by rintro z rfl; exact ⟨h_none, h_y_not_def⟩) y rfl

/-- A terminating base-command statement run changes the store domain exactly
by adding the statement's scope-level definitions. -/
theorem stmt_run_terminal_store_isSome_eqE
    {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident]
    {s : Stmt P (Cmd P)} {ρ ρ' : Env P} {tr : Trace P}
    (h_run : StepStmtStarE P (EvalCmdE P)
      (.stmt s ρ) tr (.terminal ρ')) (n : P.Ident) :
    (ρ'.store n).isSome =
      ((ρ.store n).isSome || decide (n ∈ Stmt.definedVars s true)) := by
  by_cases hd : n ∈ Stmt.definedVars s true
  · simp only [hd, decide_true, Bool.or_true]
    match s with
    | .cmd c =>
      cases h_run with
      | step _ _ _ _ _ hstep hrest =>
        cases hstep with
        | step_cmd h_eval =>
          obtain ⟨hcfg, _⟩ := stepStmtStarE_from_terminal hrest
          injection hcfg with hρ
          subst hρ
          simp only [Stmt.definedVars] at hd
          exact evalCmdE_definedVars_isSome h_eval hd
        | step_admin hadmin =>
          cases hadmin with
          | step_cmd hfalse => exact hfalse.elim
    | .block .. | .ite .. | .loop .. | .exit .. | .typeDecl .. =>
      simp [Stmt.definedVars] at hd
  · simp only [hd, decide_false, Bool.or_false]
    by_cases hs : (ρ.store n).isSome = true
    · rw [hs, stmt_preserves_isSomeE h_run hs]
    · have hnone : ρ.store n = none := by
        cases h : ρ.store n with
        | none => rfl
        | some v => rw [h] at hs; simp at hs
      rw [hnone] at hs
      rw [stmt_run_terminal_preserves_none_of_not_definedVars_trueE
        hd hnone h_run, hnone]

/-- Every free variable captured by an event has a slot in its snapshot. -/
@[expose] def Event.readsDefined {P : PureExpr} [HasFvars P] : Event P → Prop
  | .assert arg | .assume arg | .cover arg =>
      ∀ ident ∈ HasFvars.getFvars arg.expr, (arg.store ident).isSome = true

/-- Every event in a trace captures only defined free variables. -/
@[expose] def Trace.readsDefined {P : PureExpr} [HasFvars P] (trace : Trace P) : Prop :=
  ∀ event ∈ trace, Event.readsDefined event

/-- Defined-read evidence composes across trace concatenation. -/
theorem Trace.readsDefined_append {P : PureExpr} [HasFvars P]
    {first second : Trace P} (hfirst : first.readsDefined)
    (hsecond : second.readsDefined) : (first ++ second).readsDefined := by
  intro event hevent
  exact (List.mem_append.mp hevent).elim (hfirst event) (hsecond event)

/-- A command whose reads are defined emits only defined-read snapshots. -/
theorem Cmd.emittedEvents_readsDefined {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBool P]
    (command : Cmd P) (factory : P.Factory) (store : SemanticStore P)
    (hreads : (Cmd.getVars command).all (fun ident => (store ident).isSome) = true) :
    (Cmd.emittedEvents P command factory store).readsDefined := by
  rw [List.all_eq_true] at hreads
  cases command with
  | init | set => simp [Cmd.emittedEvents, Trace.readsDefined]
  | assert label expr metadata | assume label expr metadata | cover label expr metadata =>
      intro event hevent
      simp only [Cmd.emittedEvents, List.mem_singleton] at hevent
      subst event
      intro ident hident
      exact hreads ident (by simpa [Cmd.getVars] using hident)

/-- A terminating statement-list run changes the store domain exactly by adding
the list's scope-level definitions: a slot is defined afterwards iff it was
defined on entry or the list defines it at scope level. -/
theorem block_run_terminal_store_isSome_eqE
    {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident]
    {ss : List (Stmt P (Cmd P))} {ρ ρ' : Env P} {tr : Trace P}
    (h_run : StepStmtStarE P (EvalCmdE P)
      (.stmts ss ρ) tr (.terminal ρ')) (n : P.Ident) :
    (ρ'.store n).isSome =
      ((ρ.store n).isSome || decide (n ∈ Block.definedVars ss true)) := by
  induction ss generalizing ρ ρ' tr with
  | nil =>
      obtain ⟨htrace, hfinal⟩ := stmts_nil_runE (EvalCmdE P) h_run
      subst htrace
      rcases hfinal with hbad | hfinal
      · simp at hbad
      · injection hfinal with henv
        subst henv
        simp [Block.definedVars]
  | cons head tail ih =>
      rcases stmts_cons_headE (EvalCmdE P) h_run with hbad | hseq
      · simp at hbad
      · obtain ⟨middle, headTrace, tailTrace, htrace, hhead, htail⟩ :=
          seq_reaches_terminalE (EvalCmdE P) hseq
        rw [ih htail, stmt_run_terminal_store_isSome_eqE hhead n]
        simp only [Block.definedVars, List.mem_append]
        by_cases hheadDef : n ∈ Stmt.definedVars head true <;>
          by_cases htailDef : n ∈ Block.definedVars tail true <;>
          simp [hheadDef, htailDef]

end EventInvariantEngines

/-! ## Event snapshots are read-defined and semantically well formed

`Config.defUseReady` is the configuration-level form of
`Block.defUseWellFormed`. Pending statement lists are checked against a
definedness predicate whose names are already in the store. For a sequence,
the pending tail's predicate is justified semantically: every terminating run of
the active head defines it. A traced run from a ready configuration emits only
events whose captured free variables are defined at the event snapshot. -/

section EventSnapshots

/-- A command evaluated from a well-formed store emits well-formed snapshots. -/
theorem Cmd.emittedEvents_semanticWF {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBool P]
    (command : Cmd P) (factory : P.Factory) (store : SemanticStore P)
    (hstore : WellFormedStore store factory)
    (hcongr : WellFormedSemanticEvalExprCongr factory) :
    Trace.semanticWF (Cmd.emittedEvents P command factory store) := by
  cases command with
  | init | set => simp [Cmd.emittedEvents, Trace.semanticWF]
  | assert label expr metadata | assume label expr metadata | cover label expr metadata =>
      intro event hevent
      simp only [Cmd.emittedEvents, List.mem_singleton] at hevent
      subst event
      exact ⟨hstore, hcongr⟩

/-- Events emitted by one structured step capture the step's well-formed input
store and evaluator congruence law. -/
theorem Trace.semanticWF_of_stepE {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P]
    {cfg cfg' : Config P (Cmd P)} {trace : Trace P}
    (hstep : StepStmtE P (EvalCmdE P) cfg trace cfg')
    (hstore : Config.storeWellDefined cfg)
    (hcongr : WellFormedSemanticEvalExprCongr cfg.getEnv.factory) :
    Trace.semanticWF trace := by
  induction hstep with
  | step_cmd heval =>
      rw [heval.emitted_eq]
      exact Cmd.emittedEvents_semanticWF _ _ _ hstore hcongr
  | step_admin _ => simp [Trace.semanticWF]
  | step_seq_inner _ ih => exact ih hstore hcongr
  | step_block_body _ ih => exact ih hstore.2 hcongr

/-- A structured run from a well-formed configuration emits only well-formed
event snapshots. -/
theorem Trace.semanticWF_of_starE {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    {cfg cfg' : Config P (Cmd P)} {trace : Trace P}
    (hrun : StepStmtStarE P (EvalCmdE P) cfg trace cfg')
    (hval : WellFormedSemanticEvalVal cfg.getEnv.factory)
    (hcongr : WellFormedSemanticEvalExprCongr cfg.getEnv.factory)
    (hstore : Config.storeWellDefined cfg) :
    Trace.semanticWF trace := by
  induction hrun with
  | refl => simp [Trace.semanticWF]
  | step _ _ _ _ _ hstep _ ih =>
      have hfactory := stepE_preserves_factory hstep
      exact Trace.semanticWF_append (Trace.semanticWF_of_stepE hstep hstore hcongr)
        (ih (hfactory ▸ hval) (hfactory ▸ hcongr)
          (Config.storeWellDefined_step_evalCmdE hval hstep hstore))

variable {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
  [HasOps P] [DecidableEq P.Ident]

/-- Def-use readiness of a base-command configuration. -/
@[expose] def Config.defUseReady (declared : P.Ident → Bool) :
    Config P (Cmd P) → Prop
  | .stmt s ρ => ∃ defined : P.Ident → Bool,
      Stmt.defUseWellFormed defined declared s = true ∧
      ∀ x, defined x = true → (ρ.store x).isSome = true
  | .stmts ss ρ => ∃ defined : P.Ident → Bool,
      Block.defUseWellFormed defined declared ss = true ∧
      ∀ x, defined x = true → (ρ.store x).isSome = true
  | .terminal _ => True
  | .exiting _ _ => True
  | .block _ _ inner => Config.defUseReady declared inner
  | .seq inner rest => Config.defUseReady declared inner ∧
      ∃ defined : P.Ident → Bool,
        Block.defUseWellFormed defined declared rest = true ∧
        ∀ ρ' tr, StepStmtStarE P (EvalCmdE P) inner tr (.terminal ρ') →
          ∀ x, defined x = true → (ρ'.store x).isSome = true

omit [HasIdent P] [HasOps P] in
/-- A terminating run preserves a slot defined in every store of its start. -/
private theorem run_terminal_isSome_of_varDefined
    {cfg : Config P (Cmd P)} {ρ' : Env P} {trace : Trace P} {x : P.Ident}
    (hrun : StepStmtStarE P (EvalCmdE P) cfg trace (.terminal ρ'))
    (hdefined : Config.varDefined x cfg) : (ρ'.store x).isSome = true :=
  Config.varsDefined_star_ofE (fun he hs => evalCmdE_preserves_isSome he hs)
    hrun hdefined x rfl

omit [HasFvars P] [HasIdent P] [HasOps P] [DecidableEq P.Ident] in
/-- A definedness promise about every terminating run is preserved by a step. -/
private theorem terminalDefined_of_stepE
    {inner inner' : Config P (Cmd P)} {emitted : Trace P}
    (hstep : StepStmtE P (EvalCmdE P) inner emitted inner')
    {defined : P.Ident → Bool}
    (h : ∀ ρ' tr, StepStmtStarE P (EvalCmdE P) inner tr (.terminal ρ') →
      ∀ x, defined x = true → (ρ'.store x).isSome = true) :
    ∀ ρ' tr, StepStmtStarE P (EvalCmdE P) inner' tr (.terminal ρ') →
      ∀ x, defined x = true → (ρ'.store x).isSome = true :=
  fun ρ' tr hrun => h ρ' (emitted ++ tr) (.step _ _ _ _ _ hstep hrun)

/-- Command-free structured steps preserve def-use readiness. -/
private theorem Config.defUseReady_admin {declared : P.Ident → Bool}
    {cfg cfg' : Config P (Cmd P)}
    (hstep : StepStmt P (noCommandEvalE P (Cmd P)) cfg cfg')
    (hready : Config.defUseReady declared cfg) :
    Config.defUseReady declared cfg' := by
  induction hstep with
  | step_cmd heval => simp [noCommandEvalE] at heval
  | step_block =>
      obtain ⟨defined, hdu, hdefined⟩ := hready
      exact ⟨defined, by simpa [Stmt.defUseWellFormed] using hdu, hdefined⟩
  | step_ite_true _ | step_ite_nondet_true =>
      obtain ⟨defined, hdu, hdefined⟩ := hready
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      exact ⟨defined, hdu.1.2, hdefined⟩
  | step_ite_false _ | step_ite_nondet_false =>
      obtain ⟨defined, hdu, hdefined⟩ := hready
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      exact ⟨defined, hdu.2, hdefined⟩
  | step_loop_enter _ | step_loop_nondet_enter =>
      obtain ⟨defined, hdu, hdefined⟩ := hready
      have hloop := hdu
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      refine ⟨⟨defined, hdu.2, hdefined⟩, defined, ?_, ?_⟩
      · simp [Block.defUseWellFormed, hloop]
      · intro ρ' tr hrun x hx
        exact run_terminal_isSome_of_varDefined hrun
          ⟨fun _ hz => hz ▸ hdefined x hx, fun _ hz => hz ▸ hdefined x hx⟩
  | step_loop_exit _ | step_loop_nondet_exit | step_exit | step_typeDecl
  | step_stmts_nil | step_seq_exit | step_block_done
  | step_block_exit_match _ | step_block_exit_mismatch _ =>
      simp [Config.defUseReady]
  | step_stmts_cons =>
      obtain ⟨defined, hdu, hdefined⟩ := hready
      simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
      refine ⟨⟨defined, hdu.1, hdefined⟩, _, hdu.2, ?_⟩
      intro ρ' tr hrun x hx
      rw [stmt_run_terminal_store_isSome_eqE hrun x]
      rcases Bool.or_eq_true_iff.mp hx with hold | hnew
      · simp [hdefined x hold]
      · simp only [decide_eq_true_eq] at hnew
        simp [hnew]
  | step_seq_inner hinner ih =>
      obtain ⟨hinnerReady, defined, hdu, hsem⟩ := hready
      exact ⟨ih hinnerReady, defined, hdu,
        terminalDefined_of_stepE (.step_admin hinner) hsem⟩
  | step_seq_done =>
      obtain ⟨_, defined, hdu, hsem⟩ := hready
      exact ⟨defined, hdu, hsem _ [] (.refl _)⟩
  | step_block_body _ ih => exact ih hready

/-- A structured event step from a def-use-ready configuration emits only
read-defined snapshots and preserves readiness. -/
theorem Config.defUseReady_stepE {declared : P.Ident → Bool}
    {cfg cfg' : Config P (Cmd P)} {trace : Trace P}
    (hstep : StepStmtE P (EvalCmdE P) cfg trace cfg')
    (hready : Config.defUseReady declared cfg) :
    Trace.readsDefined trace ∧ Config.defUseReady declared cfg' := by
  induction hstep with
  | step_cmd heval =>
      obtain ⟨defined, hdu, hdefined⟩ := hready
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      have hreads := hdu.1.1.1
      refine ⟨?_, by simp [Config.defUseReady]⟩
      rw [heval.emitted_eq]
      apply Cmd.emittedEvents_readsDefined
      rw [List.all_eq_true] at hreads ⊢
      intro x hx
      exact hdefined x (hreads x hx)
  | step_admin hadmin =>
      exact ⟨by simp [Trace.readsDefined], Config.defUseReady_admin hadmin hready⟩
  | step_seq_inner hinner ih =>
      obtain ⟨hinnerReady, defined, hdu, hsem⟩ := hready
      obtain ⟨hreads, hready'⟩ := ih hinnerReady
      exact ⟨hreads, hready', defined, hdu, terminalDefined_of_stepE hinner hsem⟩
  | step_block_body _ ih => exact ih hready

/-- A structured run from a def-use-ready configuration emits only read-defined
snapshots. -/
theorem Config.defUseReady_starE {declared : P.Ident → Bool}
    {cfg cfg' : Config P (Cmd P)} {trace : Trace P}
    (hrun : StepStmtStarE P (EvalCmdE P) cfg trace cfg')
    (hready : Config.defUseReady declared cfg) :
    Trace.readsDefined trace ∧ Config.defUseReady declared cfg' := by
  induction hrun with
  | refl => exact ⟨by simp [Trace.readsDefined], hready⟩
  | step _ _ _ _ _ hstep _ ih =>
      obtain ⟨hhead, hmiddle⟩ := Config.defUseReady_stepE hstep hready
      obtain ⟨htail, hfinal⟩ := ih hmiddle
      exact ⟨Trace.readsDefined_append hhead htail, hfinal⟩

/-- A def-use-well-formed statement list emits only read-defined snapshots. -/
theorem Block.run_readsDefined {declared : P.Ident → Bool}
    {ss : List (Stmt P (Cmd P))} {ρ : Env P}
    {cfg : Config P (Cmd P)} {trace : Trace P}
    (hdu : Block.defUseWellFormed (fun x => (ρ.store x).isSome) declared ss = true)
    (hrun : StepStmtStarE P (EvalCmdE P) (.stmts ss ρ) trace cfg) :
    Trace.readsDefined trace :=
  (Config.defUseReady_starE hrun ⟨_, hdu, fun _ h => h⟩).1

end EventSnapshots

/-! ## Monotonicity in the command relation -/

section EventCmdMonotonicity

variable {P : PureExpr} {CmdT EventT : Type} [HasBool P]

/-- `StepStmtE` is monotone in its command relation. -/
theorem StepStmtE.imp {E E' : EvalCmdParamE P CmdT EventT}
    (h : ∀ f σ c σ' evs, E f σ c σ' evs → E' f σ c σ' evs) :
    ∀ {c evs c'}, StepStmtE P E c evs c' → StepStmtE P E' c evs c' :=
  (by induction · <;> solve_by_elim)

/-- `StepStmtStarE` is monotone in its command relation. -/
theorem StepStmtStarE.imp {E E' : EvalCmdParamE P CmdT EventT}
    (h : ∀ f σ c σ' evs, E f σ c σ' evs → E' f σ c σ' evs) :
    ∀ {c evs c'}, StepStmtStarE P E c evs c' → StepStmtStarE P E' c evs c' :=
  ReflTransTrace.imp fun _ _ _ => (·.imp h)

end EventCmdMonotonicity

end -- public section
end Imperative
