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

## Store and expression plumbing

`projectStore_id`, the `StoreAgreement` helpers, and the `eval_fvarExpr_*`,
`eval_mkFvar_*`, and `mkTypedFvar_*` families.

## Event-trace semantics

Key results for `StepStmtE` / `StepStmtStarE`:

- `stepE_preserves_factory` and `starE_preserves_factory` establish factory
  invariance for single-step and multi-step event runs.
- `seq_run_decomposeE`, `seq_reaches_terminalE`, and
  `seq_reaches_exitingE` split traced sequence runs chronologically;
  `stmtRun_to_singletonE` lifts a completed statement run to its singleton-list run.
- `stepStmtStarE_from_terminal` / `stepStmtStarE_from_exiting`,
  `block_reaches_doneE`, and `stmt_block_reaches_doneE` characterize completed
  traced runs.
- `projectStore_eq_dropVarsE`: leaving a block drops exactly the names scoped
  by its body.
- `stepStmtE_preserves_exitsCoveredByBlocks`,
  `stmts_exitsCoveredByBlocks_noEscapeE`, and `exitsCoveredByBlocks_noEscapeE`:
  well-paired exits cannot escape.
- `seqT_reaches_terminalE` and `stmtsT_cons_terminalE` provide step-counted
  completion inversions used by the event loop rule.
- `Config.varsDefined_star_ofE`, `Config.varsUndefinedScoped_star_ofE`,
  `Config.varsUndefinedThroughout_star_ofE`, and
  `Config.storeWellDefined_star_ofE` preserve store-domain properties across
  traced runs;
  `Config.storeWellDefined_step_evalCmdE` and
  `Config.storeWellDefined_star_evalCmdE` specialize this preservation to the
  evaluator value law at the run's unchanged factory.
- `Config.typedAt_star_ofE`: a traced run keeps a slot defined in every store of the
  starting configuration at its type, when commands do.
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

/-! ## Store-projection and environment-extension helpers

The `StoreAgreement` projection helpers and the classified-extension lemmas
for `projectStore` and `Env.ExtendsWith` are consumed by the loop-init-hoist
and structured-to-unstructured correctness proofs.  They live here so the
several downstream transform proofs share one copy. -/

/-- The projected inner store agrees with the unprojected inner store on
`σ_parent`'s domain. Variables present in the parent are unchanged by
projection; variables absent from the parent become `none` in the projection,
but those don't satisfy `SemanticStore.varsDefined (· ∈ [x]) (projectStore _ _)`, so
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
  ⟨rfl, StoreExtendsWith.refl Extra _⟩

/-- Environment extension composes while unioning extra-register classes. -/
theorem trans_union {P : PureExpr} {Extra₁ Extra₂ : P.Ident → Prop}
    {source middle target : Env P}
    (h₁ : source.ExtendsWith Extra₁ middle)
    (h₂ : middle.ExtendsWith Extra₂ target) :
    source.ExtendsWith (fun ident => Extra₁ ident ∨ Extra₂ ident) target :=
  ⟨h₁.1.trans h₂.1, StoreExtendsWith.trans_union h₁.2 h₂.2⟩

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
    (h_def : SemanticStore.varsDefined (· ∈ (HasFvars.getFvars e)) σ_src) :
    ∀ x ∈ HasFvars.getFvars e, σ_src x = σ_tgt x :=
  fun x hx => h_agree x (fun z hz => by
    simpa [List.mem_singleton.mp hz] using h_def x hx)

/-- Reading a free-variable expression out of any store where its variable maps
to a *value* `b` yields exactly `b`.  The proof evaluates in a minimal
well-formed store and extends to an arbitrary one via `WellFormedSemanticEvalVar`
and `WellFormedSemanticEvalMono`.  Stated over any `e` that `getFvar` reads as
`ident`, so it serves an annotated variable as well as a bare one. -/
theorem eval_fvarExpr_of_value {P : PureExpr} [HasVal P] [HasFvar P] [DecidableEq P.Ident] [HasOps P] [LawfulHasFvar P]
    (δ : P.Factory) (σ : SemanticStore P) (ident : P.Ident) (e : P.Expr) (b : P.Val)
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
    (δ : P.Factory) (σ : SemanticStore P) (ident : P.Ident) (b : P.Val)
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
    {ty : P.Ty} (δ : P.Factory) (σ : SemanticStore P) (ident : P.Ident) (b : P.Val)
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
    (δ : P.Factory) (σ : SemanticStore P) (ident : P.Ident) (e : P.Expr) (b : P.Val)
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
    (δ : P.Factory) (σ : SemanticStore P) (ident : P.Ident) (b : P.Val)
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
    {ty : P.Ty} (δ : P.Factory) (σ : SemanticStore P) (ident : P.Ident) (b : P.Val)
    (hval : HasVal.value δ b)
    (hwf_var : WellFormedSemanticEvalVar δ)
    (hwf_mono : WellFormedSemanticEvalMono δ) :
    P.eval δ (SemanticStore.update σ ident b) (HasFvar.mkTypedFvar ident ty) = some b :=
  eval_fvarExpr_storeWith δ σ ident _ b
    (LawfulHasFvar.getFvar_mkTypedFvar ident ty) hval hwf_var hwf_mono

/-! ## Traced (`StepStmtStarE`) structural helpers

Trace-carrying `seq`/`stmts` decomposition and lifting helpers, used to lift
per-statement event-trace overapproximation to statement lists. -/

section EventTraceStructural

variable {P : PureExpr} {CmdT : Type} {EventT : Type _} [HasBool P]
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
    | step_stmts_nil =>
      cases hrest with
      | refl => exact ⟨by simp, .inr rfl⟩
      | step _ _ _ _ _ h' _ => cases h'

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
    | step_stmts_cons => exact .inr (by simpa using hrest)

/-- Terminate a head statement, then step the enclosing list to its tail with
the head's trace. -/
theorem stmts_cons_stepE
    (s : Stmt P CmdT) (ss : List (Stmt P CmdT)) (ρ ρ' : Env P) {tr : List EventT}
    (hstmt : StepStmtStarE P EvalCmd (.stmt s ρ) tr (.terminal ρ')) :
    StepStmtStarE P EvalCmd (.stmts (s :: ss) ρ) tr (.stmts ss ρ') := by
  have h2 := seq_inner_starE EvalCmd (ss := ss) hstmt
  have hchain := ReflTransTrace.trans _
    (ReflTransTrace.step _ _ _ _ _ .step_stmts_cons h2)
    (ReflTransTrace.step (r := StepStmtE P EvalCmd)
      _ _ _ _ _ .step_seq_done (.refl _))
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
    .step _ [] _ [] _ .step_stmts_nil (.refl _)
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
    | step_seq_done =>
      exact .inr (.inl ⟨_, [], restTr, by simp, .refl _, hrest⟩)
    | step_seq_exit =>
      cases hrest with
      | refl => exact .inr (.inr ⟨_, _, rfl, .refl _⟩)
      | step _ _ _ _ _ h' _ => cases h'

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

omit [HasBool P] in
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

/-- A single traced step preserves `Config.exitsCoveredByBlocks`. -/
theorem stepStmtE_preserves_exitsCoveredByBlocks
    {c₁ c₂ : Config P CmdT} {tr : List EventT}
    (hstep : StepStmtE P EvalCmd c₁ tr c₂) :
    ∀ labels, c₁.exitsCoveredByBlocks labels → c₂.exitsCoveredByBlocks labels := by
  induction hstep with
  | step_cmd _ => intro _ _; trivial
  | step_block => intro _ hwp; exact hwp
  | step_ite_true => intro _ hwp; exact hwp.1
  | step_ite_false => intro _ hwp; exact hwp.2
  | step_ite_nondet_true => intro _ hwp; exact hwp.1
  | step_ite_nondet_false => intro _ hwp; exact hwp.2
  | step_loop_enter _ | step_loop_nondet_enter =>
    intro labels hwp
    -- The anonymous body block does not extend the label list.
    simp only [Config.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks] at hwp ⊢
    exact ⟨hwp, hwp, True.intro⟩
  | step_loop_exit | step_loop_nondet_exit | step_typeDecl | step_stmts_nil
  | step_block_done | step_block_exit_match =>
    intro _ _; trivial
  | step_exit => intro _ hwp; exact hwp
  | step_stmts_cons => intro _ hwp; exact ⟨hwp.1, hwp.2⟩
  | step_seq_inner _ ih =>
      intro labels hcov
      exact ⟨ih labels hcov.1, hcov.2⟩
  | step_seq_done => intro _ hwp; exact hwp.2
  | step_seq_exit => intro _ hwp; exact hwp.1
  | step_block_body _ ih =>
      intro labels hcov
      rename_i inner emitted inner' label σ_parent _
      cases label with
      | none => exact ih labels hcov
      | some l => exact ih (l :: labels) hcov
  | step_block_exit_mismatch hne =>
    intro labels hwp
    exact block_exit_mismatch_unfold (P := P) (CmdT := CmdT) hwp hne

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
label and trace: the tail never runs. -/
private theorem stmts_cons_exitE
    (s : Stmt P CmdT) (ss : List (Stmt P CmdT)) (ρ ρ' : Env P) (lbl : String)
    {tr : List EventT}
    (h : StepStmtStarE P EvalCmd (.stmt s ρ) tr (.exiting lbl ρ')) :
    StepStmtStarE P EvalCmd (.stmts (s :: ss) ρ) tr (.exiting lbl ρ') := by
  have hchain := ReflTransTrace.trans _
    (ReflTransTrace.step _ _ _ _ _ .step_stmts_cons
      (seq_inner_starE EvalCmd (ss := ss) h))
    (ReflTransTrace.step _ _ _ _ _ .step_seq_exit (.refl _))
  simpa using hchain

/-- Decompose a *finished* traced run of `.stmts (ss₁ ++ ss₂)` — terminal or
exiting — by what `ss₁` did: either `ss₁` escaped on its own (consuming the
whole trace, `ss₂` never running), or `ss₁` terminated at some `ρ₁` with a
prefix trace `tr₁` from which `ss₂` finished the same way with the remaining
`tr₂`, splitting the trace chronologically as `tr₁ ++ tr₂`. -/
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
          _ _ _ _ _ StepStmtE.step_stmts_nil (.refl _)
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

Block metatheory for the event-trace semantics (`StepStmtStarE`):
lifting a run through a `.block` frame, inverting a finished block run (terminal
or exiting) with the emitted trace preserved, factory preservation,
and the scope-aware `varsUndefined`/`projectStore_eq_dropVarsE` plumbing.  Command
none-preservation enters only through an abstract `h_cmd` premise so the results
apply to any `EvalCmdParamE`. -/

section EventBlockScope

variable {P : PureExpr} {CmdT : Type} {EventT : Type _} [HasBool P]
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
  | step_block_done => exact .inr (.inl ⟨_, rfl, rfl, rfl⟩)
  | step_block_exit_match hl => exact .inr (.inr (.inl ⟨_, _, rfl, rfl, hl, rfl⟩))
  | step_block_exit_mismatch hl => exact .inr (.inr (.inr ⟨_, _, rfl, rfl, hl, rfl⟩))

/-- An exiting configuration takes no event step. -/
theorem StepStmtE.exiting_false
    {l : String} {ρ : Env P} {e : List EventT} {c' : Config P CmdT}
    (h : StepStmtE P EvalCmd (.exiting l ρ) e c') : False := by
  cases h


/-- No traced event step leaves a terminal configuration. -/
private theorem stepStmtE_from_terminal_none
    {ρ : Env P} {emitted : List EventT} {cfg : Config P CmdT}
    (h : StepStmtE P EvalCmd (.terminal ρ) emitted cfg) : False := by
  cases h

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
  cases h

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
      | step_block =>
        obtain ⟨ρ_inner, hinner, heq⟩ := block_reaches_doneE (.inl hrest)
        exact ⟨ρ_inner, by simpa using hinner, heq⟩
  · cases hexit with
    | step _ _ _ _ _ hstep hrest =>
      cases hstep with
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

/-- Single-step preservation of `Config.varsUndefined false` under a traced
event step, given the command evaluator only defines what the command declares
(`h_cmd`).  Every case but `step_cmd` is structural: a matter of how
`Stmt.definedVars` and `projectStore` decompose. -/
private theorem Config.varsUndefinedThroughout_stepE_of [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasIdent P] [DecidableEq P.Ident] [HasVarsImp P CmdT]
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : List EventT} {y : P.Ident},
      EvalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c false → σ' y = none)
    {Q : P.Ident → Prop} {cfg cfg' : Config P CmdT} {tr : List EventT}
    (h_step : StepStmtE P EvalCmd cfg tr cfg')
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
    exact ⟨h_none, all_not_mem_definedVars_of_block
      (fun hc => h_ndef (List.mem_append.mpr (Or.inl hc)))⟩
  | step_ite_false _ | step_ite_nondet_false =>
    refine ⟨fun y hQ => (h_inv y hQ).1, fun y hQ => ?_⟩
    obtain ⟨h_none, h_ndef⟩ := h_inv y hQ
    rw [Stmt.definedVars] at h_ndef
    simp only [Bool.false_eq_true, ite_false] at h_ndef
    exact ⟨h_none, all_not_mem_definedVars_of_block
      (fun hc => h_ndef (List.mem_append.mpr (Or.inr hc)))⟩
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

/-- A `Config.varsUndefined false` invariant — every tracked slot is undefined in
the operative store and in every enclosing parent store, and no pending statement
defines one — is preserved along a whole traced run, given a command evaluator
that only defines the slots its command declares (`h_cmd`). -/
theorem Config.varsUndefinedThroughout_star_ofE [HasBoolOps P]
    [HasFvar P] [HasFvars P] [HasIdent P] [DecidableEq P.Ident] [HasVarsImp P CmdT]
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : List EventT} {y : P.Ident},
      EvalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c false → σ' y = none)
    {Q : P.Ident → Prop} {cfg cfg' : Config P CmdT} {tr : List EventT}
    (h_run : StepStmtStarE P EvalCmd cfg tr cfg')
    (h_inv : Config.varsUndefined false (P := P) Q cfg) :
    Config.varsUndefined false (P := P) Q cfg' := by
  induction h_run with
  | refl => exact h_inv
  | step _ _ _ _ _ h_step _ ih =>
    exact ih (Config.varsUndefinedThroughout_stepE_of h_cmd h_step h_inv)

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

`Type`-valued (`ReflTransTraceT`) completion inversions for `.seq` and
`.stmts` runs, carrying the
emitted trace *and* a strict step-count bound.  The event `while_rule` recurses
on the strictly shrinking length of the remaining loop derivation while
composing each iteration's trace chronologically. -/

section EventTraceReflTransTHelpers

variable {P : PureExpr} {CmdT : Type} {EventT : Type _} [HasBool P]
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
  | .step _ _ _ restTr _ .step_seq_done hrest =>
    exact ⟨_, [], restTr, by simp, .refl _, hrest, by simp only [ReflTransTraceT.len]; omega⟩
  | .step _ _ _ _ _ .step_seq_exit hrest =>
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
  | .step _ _ _ restTr _ .step_stmts_cons hrest =>
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
            (ReflTransTrace.step _ _ _ _ _ .step_stmts_cons
              (seq_inner_starE EvalCmd (ss := rest ++ sfx) hs))
            (StepStmtStarE.single
              (c := .seq (.exiting label ρ') (rest ++ sfx))
              .step_seq_exit)
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
          exact ReflTransTrace.step _ _ _ _ _ .step_stmts_cons
            (seq_inner_starE EvalCmd hs)
        · obtain ⟨cfg', hr'⟩ := ih ρ₁ hr
          subst trace
          exact ⟨cfg', ReflTransTrace.trans _
            (stmts_cons_stepE EvalCmd s (rest ++ sfx) ρ ρ₁ hs) hr'⟩
        · subst hcfg
          refine ⟨.exiting label ρ₁, ?_⟩
          have hrun := ReflTransTrace.trans _
            (ReflTransTrace.step _ _ _ _ _ .step_stmts_cons
              (seq_inner_starE EvalCmd (ss := rest ++ sfx) hs))
            (StepStmtStarE.single
              (c := .seq (.exiting label ρ₁) (rest ++ sfx))
              .step_seq_exit)
          simpa using hrun

end EventTraceReflTransTHelpers


/-! ## Event-trace `varsDefined` / `storeWellDefined` preservation engines

These are stated with `[HasBoolOps P]` only (never a *separate* `[HasBool P]`):
that keeps `HasBool`/`HasVal` resolved uniformly through the `HasBoolOps →
HasBool → HasVal` hierarchy, matching the instances their callers use. -/

section EventInvariantEngines

variable {P : PureExpr} {CmdT : Type} {EventT : Type _} [HasBoolOps P]
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
  | step_block | step_ite_true _ | step_ite_false _ | step_ite_nondet_true
  | step_ite_nondet_false | step_loop_enter _ | step_loop_nondet_enter =>
    exact ⟨h_inv, h_inv⟩
  | step_seq_inner _ ih => exact ih h_inv
  | step_block_body _ ih => exact ⟨h_inv.1, ih h_inv.2⟩
  | step_block_done | step_block_exit_match _ | step_block_exit_mismatch _ =>
    intro y hQ
    simp only [projectStore]; rw [ite_eq_left (h_inv.1 y hQ)]; exact h_inv.2 y hQ
  | _ => exact h_inv

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
  | step_seq_inner _ ih => simpa [Config.getEnv] using ih
  | step_block_body _ ih => simpa [Config.getEnv] using ih
  | _ => simp [Config.getEnv]

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
  | step_seq_inner _ ih =>
    exact ih h_inv
  | step_block_body hinner ih =>
    exact ⟨stepE_preserves_factory hinner ▸ h_inv.1, ih h_inv.2⟩
  -- The three exit rules project the store; projection keeps only slots that are
  -- defined in `ρ'`, where `h_inv.2` already witnesses value-hood against the factory.
  | step_block_done | step_block_exit_match _ | step_block_exit_mismatch _ =>
    intro x w hx
    simp only [projectStore] at hx
    split at hx
    · exact h_inv.2 x w hx
    · exact absurd hx (by simp)
  -- Everything else either leaves the operative store alone or pushes it into a
  -- block frame, which repeats it as the saved parent store.
  | _ => first | exact h_inv | exact ⟨h_inv, h_inv⟩

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

/-- A single traced event step keeps the operative store's slot at `y` holding a value of
type `ty`, given that every store of the configuration defines `y` and that commands keep
a typed slot at its type (`h_cmd`). -/
private theorem Config.typedAt_stepE_of
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : List EventT}
        {y : P.Ident} {ty : P.Ty},
      EvalCmd f σ c σ' emitted →
      (∃ v, σ y = some v ∧ HasVal.valueOfTy f v ty) →
      ∃ v, σ' y = some v ∧ HasVal.valueOfTy f v ty)
    {cfg cfg' : Config P CmdT} {tr : List EventT} {y : P.Ident} {ty : P.Ty}
    (h_step : StepStmtE P EvalCmd cfg tr cfg')
    (h_def : Config.varDefined y cfg)
    (h_ty : ∃ v, cfg.getEnv.store y = some v ∧ HasVal.valueOfTy cfg.getEnv.factory v ty) :
    ∃ v, cfg'.getEnv.store y = some v ∧ HasVal.valueOfTy cfg'.getEnv.factory v ty := by
  induction h_step with
  | step_cmd h_eval => exact h_cmd h_eval h_ty
  | step_seq_inner _ ih => exact ih h_def h_ty
  | step_block_body _ ih => exact ih h_def.2 h_ty
  | step_block_done | step_block_exit_match _ | step_block_exit_mismatch _ =>
    simpa only [Config.getEnv, projectStore, h_def.1 y rfl, ite_true] using h_ty
  | _ => exact h_ty

/-- A traced run keeps the operative store's slot at `y` holding a value of type `ty`, given
that every store of the starting configuration defines `y`, that commands never undefine a
slot (`h_def`), and that commands keep a typed slot at its type (`h_cmd`). -/
theorem Config.typedAt_star_ofE
    [HasFvar P] [HasFvars P] [DecidableEq P.Ident]
    (h_def : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : List EventT}
        {y : P.Ident},
      EvalCmd f σ c σ' emitted → (σ y).isSome = true → (σ' y).isSome = true)
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : List EventT}
        {y : P.Ident} {ty : P.Ty},
      EvalCmd f σ c σ' emitted →
      (∃ v, σ y = some v ∧ HasVal.valueOfTy f v ty) →
      ∃ v, σ' y = some v ∧ HasVal.valueOfTy f v ty)
    {cfg cfg' : Config P CmdT} {tr : List EventT} {y : P.Ident} {ty : P.Ty}
    (h_run : StepStmtStarE P EvalCmd cfg tr cfg')
    (h_defd : Config.varDefined y cfg)
    (h_ty : ∃ v, cfg.getEnv.store y = some v ∧ HasVal.valueOfTy cfg.getEnv.factory v ty) :
    ∃ v, cfg'.getEnv.store y = some v ∧ HasVal.valueOfTy cfg'.getEnv.factory v ty := by
  induction h_run with
  | refl => exact h_ty
  | step _ _ _ _ _ h_step _ ih =>
    exact ih (Config.varsDefined_stepE_of h_def h_step h_defd)
      (Config.typedAt_stepE_of h_cmd h_step h_defd h_ty)

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
  | step_seq_inner _ ih => exact ih hval h_inv
  | step_block_body hinner ih =>
      exact ⟨stepE_preserves_factory hinner ▸ h_inv.1, ih hval h_inv.2⟩
  -- The three exit rules project the store; projection keeps only slots that are
  -- defined in `ρ'`, where `h_inv.2` already witnesses value-hood against the factory.
  | step_block_done | step_block_exit_match _ | step_block_exit_mismatch _ =>
    intro x w hx
    simp only [projectStore] at hx
    split at hx
    · exact h_inv.2 x w hx
    · exact absurd hx (by simp)
  -- Everything else either leaves the operative store alone or pushes it into a
  -- block frame, which repeats it as the saved parent store.
  | _ => first | exact h_inv | exact ⟨h_inv, h_inv⟩

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
  | step_seq_inner _ ih => exact ih hstore hcongr
  | step_block_body _ ih => exact ih hstore.2 hcongr
  | _ => simp [Trace.semanticWF]

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
  | step_block =>
      obtain ⟨defined, hdu, hdefined⟩ := hready
      exact ⟨by simp [Trace.readsDefined],
        defined, by simpa [Stmt.defUseWellFormed] using hdu, hdefined⟩
  | step_ite_true _ | step_ite_nondet_true =>
      obtain ⟨defined, hdu, hdefined⟩ := hready
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      exact ⟨by simp [Trace.readsDefined], defined, hdu.1.2, hdefined⟩
  | step_ite_false _ | step_ite_nondet_false =>
      obtain ⟨defined, hdu, hdefined⟩ := hready
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      exact ⟨by simp [Trace.readsDefined], defined, hdu.2, hdefined⟩
  | step_loop_enter _ | step_loop_nondet_enter =>
      obtain ⟨defined, hdu, hdefined⟩ := hready
      have hloop := hdu
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
      refine ⟨by simp [Trace.readsDefined], ⟨defined, hdu.2, hdefined⟩, defined, ?_, ?_⟩
      · simp [Block.defUseWellFormed, hloop]
      · intro ρ' tr hrun x hx
        exact run_terminal_isSome_of_varDefined hrun
          ⟨fun _ hz => hz ▸ hdefined x hx, fun _ hz => hz ▸ hdefined x hx⟩
  | step_loop_exit _ | step_loop_nondet_exit | step_exit | step_typeDecl
  | step_stmts_nil | step_seq_exit | step_block_done
  | step_block_exit_match _ | step_block_exit_mismatch _ =>
      simp [Trace.readsDefined, Config.defUseReady]
  | step_stmts_cons =>
      obtain ⟨defined, hdu, hdefined⟩ := hready
      simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
      refine ⟨by simp [Trace.readsDefined], ⟨defined, hdu.1, hdefined⟩, _, hdu.2, ?_⟩
      intro ρ' tr hrun x hx
      rw [stmt_run_terminal_store_isSome_eqE hrun x]
      rcases Bool.or_eq_true_iff.mp hx with hold | hnew
      · simp [hdefined x hold]
      · simp only [decide_eq_true_eq] at hnew
        simp [hnew]
  | step_seq_inner hinner ih =>
      obtain ⟨hinnerReady, defined, hdu, hsem⟩ := hready
      obtain ⟨hreads, hready'⟩ := ih hinnerReady
      exact ⟨hreads, hready', defined, hdu, terminalDefined_of_stepE hinner hsem⟩
  | step_seq_done =>
      obtain ⟨_, defined, hdu, hsem⟩ := hready
      exact ⟨by simp [Trace.readsDefined], defined, hdu, hsem _ [] (.refl _)⟩
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

variable {P : PureExpr} {CmdT : Type} {EventT : Type _} [HasBool P]

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
