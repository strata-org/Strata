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
public import Strata.DL.Imperative.Logic.TraceRelations
import all Strata.Transform.SpecificationProps
import all Strata.Transform.DetToKleene
import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.StmtSemanticsProps
import Strata.DL.Imperative.Logic.TraceRelationsProps
import all Strata.DL.Imperative.CmdSemantics
import all Strata.Util.Relations
import all Strata.Util.RelationsProps
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
import Strata.DL.Imperative.KleeneSemanticsProps

/-! # Deterministic-to-Kleene Transformation Correctness.

The top-level theorem is `detToKleene_overapproximates`.  It is a canonical
real-event trace simulation: every finite deterministic event trace is matched,
up to `Imperative.TraceStuttersEnv`, by a Kleene event trace reaching a
structurally related configuration.
-/

public section

open Imperative Specification Strata.Logic Imperative.Logic

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P] [HasFvars P] [HasOps P]
  [HasInt P] [HasIntOps P] [HasSubstFvar P]

/-! ## Transform-success helpers: extract sub-transform results -/

omit [HasFvar P] [HasFvars P] [HasOps P] [HasSubstFvar P] in
private theorem ite_transform_some_det
    (cond : P.Expr) (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (ns : KleeneStmt P (Cmd P))
    (ht : StmtToKleeneStmt (.ite (.det cond) tss ess md) = some ns) :
    ∃ t e, BlockToKleeneStmt tss = some t ∧ BlockToKleeneStmt ess = some e ∧
      ns = .choice
        (.block (.seq (.cmd (.assume "true_cond" cond md)) t))
        (.block (.seq (.cmd (.assume "false_cond" (HasBoolOps.not cond) md)) e)) := by
  simp [StmtToKleeneStmt] at ht
  match h1 : BlockToKleeneStmt tss, h2 : BlockToKleeneStmt ess with
  | some t, some e =>
    simp [h1, h2, Option.bind] at ht
    exact ⟨t, e, rfl, rfl, ht.symm⟩
  | some _, none => simp [h1, h2, Option.bind] at ht
  | none, _ => simp [h1, Option.bind] at ht

omit [HasFvar P] [HasFvars P] [HasOps P] [HasSubstFvar P] in
private theorem ite_transform_some_nondet
    (tss ess : List (Stmt P (Cmd P))) (md : MetaData P)
    (ns : KleeneStmt P (Cmd P))
    (ht : StmtToKleeneStmt (.ite .nondet tss ess md) = some ns) :
    ∃ t e, BlockToKleeneStmt tss = some t ∧ BlockToKleeneStmt ess = some e ∧
      ns = .choice (.block t) (.block e) := by
  simp [StmtToKleeneStmt] at ht
  match h1 : BlockToKleeneStmt tss, h2 : BlockToKleeneStmt ess with
  | some t, some e =>
    simp [h1, h2, Option.bind] at ht
    exact ⟨t, e, rfl, rfl, ht.symm⟩
  | some _, none => simp [h1, h2, Option.bind] at ht
  | none, _ => simp [h1, Option.bind] at ht

omit [HasFvar P] [HasFvars P] [HasOps P] [HasSubstFvar P] in
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

omit [HasFvar P] [HasFvars P] [HasOps P] [HasSubstFvar P] in
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

omit [HasFvar P] [HasFvars P] [HasOps P] [HasSubstFvar P] in
/-- A successful `StmtToKleeneStmt` of a `.block` extracts a successful
`BlockToKleeneStmt` of its body: the translated statement is the `.block` wrapper
of that body translation. -/
private theorem block_stmt_transform_some
    (label : String) (bss : List (Stmt P (Cmd P))) (md : MetaData P)
    (ns : KleeneStmt P (Cmd P))
    (ht : StmtToKleeneStmt (.block label bss md) = some ns) :
    ∃ b, BlockToKleeneStmt bss = some b ∧ ns = .block b := by
  simp [StmtToKleeneStmt] at ht
  match hb : BlockToKleeneStmt bss with
  | some b => simp [hb, Option.bind] at ht; exact ⟨b, rfl, ht.symm⟩
  | none => simp [hb, Option.bind] at ht

omit [HasFvar P] [HasFvars P] [HasOps P] [HasSubstFvar P] in
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

/-! ## Canonical trace simulation -/

/-- A source statement-list continuation may correspond either to its full
block translation or, for the recursive continuation installed by a Kleene
loop, to the translation of its single statement. -/
private inductive DetToKleeneContSim :
    List (Stmt P (Cmd P)) → KleeneStmt P (Cmd P) → Prop where
  | block {ss target} : BlockToKleeneStmt ss = some target →
      DetToKleeneContSim ss target
  | singleton {source target} : StmtToKleeneStmt source = some target →
      DetToKleeneContSim [source] target

/-- Structural invariant relating an in-flight deterministic configuration to
an in-flight Kleene configuration.  The singleton/empty-list cases account for
the recursive continuation installed by the Kleene loop rule, which omits the
block translation's trailing skip assertion. `Config.block` carries no factory
field, so the block case needs no factory premise. -/
private inductive DetToKleeneConfigSim :
    Config P (Cmd P) → KleeneConfig P (Cmd P) → Prop where
  | stmt {source target ρ} : StmtToKleeneStmt source = some target →
      DetToKleeneConfigSim (.stmt source ρ) (.stmt target ρ)
  | stmts {source target ρ} : BlockToKleeneStmt source = some target →
      DetToKleeneConfigSim (.stmts source ρ) (.stmt target ρ)
  | stmtsSingleton {source target ρ} : StmtToKleeneStmt source = some target →
      DetToKleeneConfigSim (.stmts [source] ρ) (.stmt target ρ)
  | stmtsNil {ρ} : DetToKleeneConfigSim (.stmts [] ρ) (.terminal ρ)
  | terminal {ρ} : DetToKleeneConfigSim (.terminal ρ) (.terminal ρ)
  | seq {sourceInner targetInner sourceRest targetRest} :
      DetToKleeneConfigSim sourceInner targetInner →
      DetToKleeneContSim sourceRest targetRest →
      DetToKleeneConfigSim (.seq sourceInner sourceRest) (.seq targetInner targetRest)
  | seqNil {sourceInner targetInner} :
      DetToKleeneConfigSim sourceInner targetInner →
      DetToKleeneConfigSim (.seq sourceInner []) targetInner
  | block {label parent sourceInner targetInner} :
      DetToKleeneConfigSim sourceInner targetInner →
      DetToKleeneConfigSim
        (.block label parent sourceInner) (.block parent targetInner)

omit [HasFvar P] [HasFvars P] [HasOps P] [HasInt P] [HasIntOps P] [HasSubstFvar P] in
/-- Related in-flight configurations expose exactly the same environment. -/
private theorem DetToKleeneConfigSim.getEnv_eq
    {source : Config P (Cmd P)} {target : KleeneConfig P (Cmd P)}
    (h : DetToKleeneConfigSim source target) : source.getEnv = target.getEnv := by
  induction h <;> simp_all [Config.getEnv, KleeneConfig.getEnv]

omit [HasFvar P] [HasBoolOps P] [HasFvars P] [HasOps P] [HasInt P] [HasIntOps P]
  [HasSubstFvar P] in
/-- A selected guard assumption whose condition is true is stutter-eligible. -/
private theorem guard_assume_event_true
    {ρ : Env P} {label : String} {expr : P.Expr} {md : MetaData P}
    (h : P.eval ρ.factory ρ.store expr = some HasBool.tt) :
    Event.isTrueAssumeOrAssert
      (Event.assume (EventArg.mk ρ.factory ρ.store label expr md)) := h

omit [HasFvar P] [HasBoolOps P] [HasFvars P] [HasOps P] [HasInt P] [HasIntOps P]
  [HasSubstFvar P] in
/-- The trailing skip assertion inserted by the block translation is
semantically true, hence stutter-eligible. -/
private theorem skip_assert_event_true [LawfulHasVal P]
    {ρ : Env P}
    (hwfv : WellFormedSemanticEvalVal (P := P) ρ.factory) :
    Event.isTrueAssumeOrAssert
      (Event.assert (EventArg.mk ρ.factory ρ.store "$__skip" HasBool.tt .empty)) :=
  eval_tt_is_tt ρ.store ρ.factory hwfv

omit [HasFvars P] [HasOps P] [HasInt P] [HasIntOps P] [HasSubstFvar P] in
/-- One deterministic statement step is simulated by a finite Kleene prefix
with the same resulting structural configuration. -/
private theorem detToKleene_stmt_step
    {source : Stmt P (Cmd P)} {target : KleeneStmt P (Cmd P)} {ρ : Env P}
    {emitted : Trace P} {source' : Config P (Cmd P)}
    (hwfb : WellFormedSemanticEvalBool (P := P) ρ.factory)
    (ht : StmtToKleeneStmt source = some target)
    (hstep : StepStmtE P (EvalCmdE P)
      (.stmt source ρ) emitted source') :
    ∃ target' targetTrace,
      StepKleeneStarE P (EvalCmdE P) (.stmt target ρ) targetTrace target' ∧
      DetToKleeneConfigSim source' target' ∧
      TraceStuttersEnv (P := P) (fun _ : P.Ident => False) (fun _ => True) emitted targetTrace := by
  cases hstep with
  | step_cmd hcmd =>
      simp only [StmtToKleeneStmt.eq_1, Option.some.injEq] at ht
      subst ht
      exact ⟨.terminal { ρ with store := _ }, _,
        .step _ _ _ _ _ (StepKleeneE.step_cmd hcmd) (.refl _),
        .terminal, by simpa using
          TraceStuttersEnv.refl (P := P) (fun _ : P.Ident => False) (fun _ => True) emitted⟩
  | step_admin hadmin =>
    cases hadmin with
    | step_block =>
        obtain ⟨bodyTarget, hbody, rfl⟩ := block_stmt_transform_some _ _ _ _ ht
        exact ⟨.block ρ.store (.stmt bodyTarget ρ), [],
          .step _ _ _ _ _ StepKleeneE.step_block (.refl _),
          .block (.stmts hbody), .nil⟩
    | step_ite_true hcond =>
        obtain ⟨thenTarget, elseTarget, hthen, _helse, rfl⟩ :=
          ite_transform_some_det _ _ _ _ _ ht
        exact ⟨_, _,
          kleene_choice_left_traceE
            (.step _ _ _ _ _ StepKleeneE.step_block
              (stepKleeneStarE_block_inner
                (kleene_seq_traceE (kleene_assume_traceE ρ "true_cond" _ _) (.refl _)))),
          .block (.stmts hthen),
          .stutter_right trivial (guard_assume_event_true hcond) .nil⟩
    | step_ite_false hcond =>
        obtain ⟨_thenTarget, elseTarget, _hthen, helse, rfl⟩ :=
          ite_transform_some_det _ _ _ _ _ ht
        exact ⟨_, _,
          kleene_choice_right_traceE
            (.step _ _ _ _ _ StepKleeneE.step_block
              (stepKleeneStarE_block_inner
                (kleene_seq_traceE (kleene_assume_traceE ρ "false_cond" _ _) (.refl _)))),
          .block (.stmts helse),
          .stutter_right trivial (guard_assume_event_true ((hwfb ρ.store _).2.mp hcond)) .nil⟩
    | step_ite_nondet_true =>
        obtain ⟨thenTarget, elseTarget, hthen, _helse, rfl⟩ :=
          ite_transform_some_nondet _ _ _ _ ht
        exact ⟨.block ρ.store (.stmt thenTarget ρ), [],
          kleene_choice_left_traceE
            (.step _ _ _ _ _ StepKleeneE.step_block (.refl _)),
          .block (.stmts hthen), .nil⟩
    | step_ite_nondet_false =>
        obtain ⟨_thenTarget, elseTarget, _hthen, helse, rfl⟩ :=
          ite_transform_some_nondet _ _ _ _ ht
        exact ⟨.block ρ.store (.stmt elseTarget ρ), [],
          kleene_choice_right_traceE
            (.step _ _ _ _ _ StepKleeneE.step_block (.refl _)),
          .block (.stmts helse), .nil⟩
    | step_loop_enter hcond =>
        obtain ⟨rfl, bodyTarget, hbody, rfl⟩ := loop_transform_some_det _ _ _ _ _ _ ht
        exact ⟨_, _,
          .step _ _ _ _ _ StepKleeneE.step_loop_step
            (stepKleeneStarE_seq_inner
              (stepKleeneStarE_block_inner
                (kleene_seq_traceE (kleene_assume_traceE ρ "guard" _ _) (.refl _)))),
          .seq (.block (.stmts hbody)) (.singleton ht),
          .stutter_right trivial (guard_assume_event_true hcond) .nil⟩
    | step_loop_exit _ =>
        obtain ⟨rfl, _, _, rfl⟩ := loop_transform_some_det _ _ _ _ _ _ ht
        exact ⟨.terminal ρ, [], kleene_loop_zero_traceE _ _, .terminal, .nil⟩
    | step_loop_nondet_enter =>
        obtain ⟨rfl, bodyTarget, hbody, rfl⟩ := loop_transform_some_nondet _ _ _ _ _ ht
        exact ⟨_, [],
          .step _ _ _ _ _ StepKleeneE.step_loop_step (.refl _),
          .seq (.block (.stmts hbody)) (.singleton ht), .nil⟩
    | step_loop_nondet_exit =>
        obtain ⟨rfl, _, _, rfl⟩ := loop_transform_some_nondet _ _ _ _ _ ht
        exact ⟨.terminal ρ, [], kleene_loop_zero_traceE _ _, .terminal, .nil⟩
    | step_cmd hfalse => simp [noCommandEvalE] at hfalse
    | step_exit => simp [StmtToKleeneStmt.eq_6] at ht
    | step_typeDecl => simp [StmtToKleeneStmt.eq_5] at ht

omit [HasFvars P] [HasOps P] [HasInt P] [HasIntOps P] [HasSubstFvar P] in
/-- The structural configuration invariant is a forward simulation: one source
step is matched by a finite Kleene run that preserves the invariant and matches
the emitted trace up to stuttering. -/
private theorem detToKleene_config_step [LawfulHasVal P]
    {source : Config P (Cmd P)} {target : KleeneConfig P (Cmd P)}
    (hsim : DetToKleeneConfigSim source target) :
    ∀ {emitted : Trace P} {source' : Config P (Cmd P)},
      WellFormedSemanticEvalBool (P := P) source.getEnv.factory →
      WellFormedSemanticEvalVal (P := P) source.getEnv.factory →
      StepStmtE P (EvalCmdE P) source emitted source' →
      ∃ target' targetTrace,
        StepKleeneStarE P (EvalCmdE P) target targetTrace target' ∧
        DetToKleeneConfigSim source' target' ∧
        TraceStuttersEnv (P := P) (fun _ : P.Ident => False) (fun _ => True) emitted targetTrace := by
  induction hsim with
  | stmt ht =>
      intro emitted source' hwfb _hwfv hstep
      exact detToKleene_stmt_step hwfb ht hstep

  | stmts ht =>
      rename_i sourceStmts targetStmt ρ
      intro emitted source' _hwfb hwfv hstep
      cases hstep with
      | step_admin hadmin => cases hadmin with
        | step_stmts_nil =>
          simp only [BlockToKleeneStmt.eq_1, Option.some.injEq] at ht
          subst targetStmt
          exact ⟨.terminal _,
            [Event.assert (EventArg.mk ρ.factory ρ.store "$__skip" HasBool.tt .empty)],
            .step _ _ _ _ _ (StepKleeneE.step_cmd EvalCmdE.eval_assert) (.refl _),
            .terminal, .stutter_right trivial (skip_assert_event_true hwfv) .nil⟩
        | step_stmts_cons =>
          obtain ⟨headTarget, restTarget, hhead, hrest, rfl⟩ :=
            block_transform_some _ _ _ ht
          exact ⟨_, [],
            .step _ _ _ _ _ StepKleeneE.step_seq (.refl _),
            .seq (.stmt hhead) (.block hrest), .nil⟩

  | stmtsSingleton ht =>
      intro emitted source' _hwfb _hwfv hstep
      cases hstep with
      | step_admin hadmin => cases hadmin with
        | step_stmts_cons => exact ⟨_, [], .refl _, .seqNil (.stmt ht), .nil⟩

  | stmtsNil =>
      intro emitted source' _hwfb _hwfv hstep
      cases hstep with
      | step_admin hadmin => cases hadmin with
        | step_stmts_nil => exact ⟨_, [], .refl _, .terminal, .nil⟩

  | terminal =>
      intro emitted source' _hwfb _hwfv hstep
      cases hstep with
      | step_admin hadmin => cases hadmin

  | seq hinner hcont ih =>
      intro emitted source' hwfb hwfv hstep
      cases hstep with
      | step_seq_inner hinnerStep =>
        obtain ⟨targetInner', targetTrace, htarget, hsim', hrel⟩ := ih hwfb hwfv hinnerStep
        exact ⟨_, targetTrace, stepKleeneStarE_seq_inner htarget,
          .seq hsim' hcont, hrel⟩
      | step_admin hadmin => cases hadmin with
        | step_seq_inner hinnerStep =>
          obtain ⟨targetInner', targetTrace, htarget, hsim', hrel⟩ :=
            ih hwfb hwfv (StepStmtE.step_admin hinnerStep)
          exact ⟨_, targetTrace, stepKleeneStarE_seq_inner htarget,
            .seq hsim' hcont, hrel⟩
        | step_seq_done =>
          cases hinner
          cases hcont with
          | block hrest =>
              exact ⟨_, [], .step _ _ _ _ _ StepKleeneE.step_seq_done (.refl _),
                .stmts hrest, .nil⟩
          | singleton hrest =>
              exact ⟨_, [], .step _ _ _ _ _ StepKleeneE.step_seq_done (.refl _),
                .stmtsSingleton hrest, .nil⟩
        | step_seq_exit => cases hinner

  | seqNil hinner ih =>
      intro emitted source' hwfb hwfv hstep
      cases hstep with
      | step_seq_inner hinnerStep =>
        obtain ⟨target', targetTrace, htarget, hsim', hrel⟩ := ih hwfb hwfv hinnerStep
        exact ⟨target', targetTrace, htarget, .seqNil hsim', hrel⟩
      | step_admin hadmin => cases hadmin with
        | step_seq_inner hinnerStep =>
          obtain ⟨target', targetTrace, htarget, hsim', hrel⟩ :=
            ih hwfb hwfv (StepStmtE.step_admin hinnerStep)
          exact ⟨target', targetTrace, htarget, .seqNil hsim', hrel⟩
        | step_seq_done =>
          cases hinner
          exact ⟨_, [], .refl _, .stmtsNil, .nil⟩
        | step_seq_exit => cases hinner

  | block hinner ih =>
      intro emitted source' hwfb hwfv hstep
      cases hstep with
      | step_block_body hinnerStep =>
        obtain ⟨targetInner', targetTrace, htarget, hsim', hrel⟩ := ih hwfb hwfv hinnerStep
        exact ⟨_, targetTrace, stepKleeneStarE_block_inner htarget,
          .block hsim', hrel⟩
      | step_admin hadmin => cases hadmin with
        | step_block_body hinnerStep =>
          obtain ⟨targetInner', targetTrace, htarget, hsim', hrel⟩ :=
            ih hwfb hwfv (StepStmtE.step_admin hinnerStep)
          exact ⟨_, targetTrace, stepKleeneStarE_block_inner htarget,
            .block hsim', hrel⟩
        | step_block_done =>
          cases hinner
          exact ⟨_, [],
            .step _ _ _ _ _ StepKleeneE.step_block_done (.refl _),
            .terminal, .nil⟩
        | step_block_exit_match _ => cases hinner
        | step_block_exit_mismatch _ => cases hinner

omit [HasFvars P] [HasOps P] [HasInt P] [HasIntOps P] [HasSubstFvar P] in
/-- Every finite source trace prefix has a related target trace prefix. -/
private theorem detToKleene_config_trace [LawfulHasVal P]
    {source source' : Config P (Cmd P)}
    {target : KleeneConfig P (Cmd P)} {sourceTrace : Trace P}
    (hsim : DetToKleeneConfigSim source target)
    (hwfb : WellFormedSemanticEvalBool (P := P) source.getEnv.factory)
    (hwfv : WellFormedSemanticEvalVal (P := P) source.getEnv.factory)
    (htrace : StepStmtStarE P (EvalCmdE P) source sourceTrace source') :
    ∃ target' targetTrace,
      StepKleeneStarE P (EvalCmdE P) target targetTrace target' ∧
      DetToKleeneConfigSim source' target' ∧
      TraceStuttersEnv (P := P) (fun _ : P.Ident => False) (fun _ => True) sourceTrace targetTrace := by
  induction htrace generalizing target with
  | refl =>
      exact ⟨target, [], .refl _, hsim,
        TraceStuttersEnv.refl (P := P) (fun _ : P.Ident => False) (fun _ => True) []⟩
  | step source emitted mid rest source' hstep _hrest ih =>
      obtain ⟨targetMid, targetHead, htargetHead, hsimMid, hrelHead⟩ :=
        detToKleene_config_step hsim hwfb hwfv hstep
      have hwfbMid : WellFormedSemanticEvalBool (P := P) mid.getEnv.factory := by
        rw [hsimMid.getEnv_eq, stepKleeneStarE_preserves_factory htargetHead,
          ← hsim.getEnv_eq]
        exact hwfb
      have hwfvMid : WellFormedSemanticEvalVal (P := P) mid.getEnv.factory := by
        rw [hsimMid.getEnv_eq, stepKleeneStarE_preserves_factory htargetHead,
          ← hsim.getEnv_eq]
        exact hwfv
      obtain ⟨target', targetRest, htargetRest, hsim', hrelRest⟩ :=
        ih hsimMid hwfbMid hwfvMid
      exact ⟨target', targetHead ++ targetRest,
        ReflTransTrace.trans _ htargetHead htargetRest,
        hsim', hrelHead.append hrelRest⟩

/-! ## Main theorem -/

omit [HasOps P] in
/-- `StmtToKleeneStmt` matches every canonical deterministic trace prefix by a
Kleene trace prefix, and every terminating deterministic run by a Kleene run
reaching the same environment. Events correspond under `TraceStuttersEnv`:
translated commands match item-by-item, while the selected guard assumptions
and trailing skip assertion are semantically true target-only instrumentation.
The exiting case is ruled out because the transform returns `none` for `.exit`
sub-statements. The unrestricted factory predicate keeps this top-level theorem
a generic illustration of `OverapproximatesTraces` and the `EventLang` packages. -/
theorem detToKleene_overapproximates [LawfulHasVal P] :
    Transform.OverapproximatesTraces
      (TraceStuttersEnv (P := P) (fun _ : P.Ident => False) (fun _ => True))
      (EventLang.imperativeE P (Cmd P) (EvalCmdE P) Unit
        (fun _ _ ρ => WellFormedSemanticEval (P := P) ρ.factory))
      (EventLang.kleeneE P Unit
        (fun _ _ ρ => WellFormedSemanticEval (P := P) ρ.factory))
      (StmtToKleeneStmt (P := P)) () () := by
  intro st ns ht _ ρ₀ ρ₀' heq hwf
  subst heq
  refine ⟨?_, ?_, ?_, hwf⟩
  · intro cfg sourceTrace htrace
    obtain ⟨targetCfg, targetTrace, htarget, _hsim, hrel⟩ :=
      detToKleene_config_trace (.stmt ht) hwf.bool hwf.val htrace
    exact ⟨targetCfg, targetTrace, htarget, hrel⟩
  · intro ρ' sourceTrace htrace
    obtain ⟨targetCfg, targetTrace, htarget, hsim, hrel⟩ :=
      detToKleene_config_trace (.stmt ht) hwf.bool hwf.val htrace
    cases hsim
    exact ⟨ρ', targetTrace, htarget, rfl, hrel⟩
  · intro label ρ' sourceTrace htrace
    obtain ⟨targetCfg, targetTrace, htarget, hsim, hrel⟩ :=
      detToKleene_config_trace (.stmt ht) hwf.bool hwf.val htrace
    cases hsim

end
