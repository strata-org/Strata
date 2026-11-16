/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterReach
public import Strata.Languages.Core.Logic.LangDef
public import Strata.DL.Imperative.Logic.Termination
import all Strata.Languages.Core.InterpreterReach
import Strata.Languages.Core.InterpreterEvalSound
import Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.DL.Lambda.LExprDenoteEval
import Strata.Util.ListUtilsProps
import Strata.DL.Lambda.Denote.LExprDenoteConsts
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.DL.Imperative.StmtCFGCallSemanticsProps
import Strata.DL.Imperative.CmdSemanticsProps

/-! # Running straight-line code over literals: soundness and termination

Theorems about the runner of `InterpreterReach` (`evalLit`, `runLits`, `runLitsProgresses`).
Their results are the values of every model of `Core.Factory` (`eval_of_evalLit`) and the stores
every run reaches (`runLits_run`), so a computation of `runLits` (by `native_decide`, say) tells
what a straight-line body does in every model. A result obtained by `native_decide` trusts the
compiled code (`Lean.ofReduceBool`), so it belongs in tests, not in a theorem the library relies
on. When moreover every write is at the type of its target (`runLitsProgresses`), every run of
the body finishes (`runLits_terminates`).

Key results: `eval_of_evalLit`, `LitBinds.Holds.set`, `runLits_run`, `runLits_terminates`.
-/

namespace Core
open Lambda Imperative
public section

/-- The runtime store of `bs` denotes the semantic store of `bs` when its literals are well
    typed. -/
private theorem storeDenotes_litBinds (F : Expression.Factory) {bs : LitBinds}
    (hwt : ∀ b ∈ bs, b.2.wt = true) :
    StoreDenotes F bs.rstore (bs.store F.model.tcInterp) := by
  refine ⟨fun x => by simp [LitBinds.rstore, LitBinds.store], fun x r v hr hv => ?_⟩
  simp only [LitBinds.rstore, Option.map_eq_some_iff] at hr
  simp only [LitBinds.store, Option.map_eq_some_iff] at hv
  obtain ⟨c, hc, rfl⟩ := hr
  obtain ⟨c', hc', rfl⟩ := hv
  obtain rfl : c = c' := Option.some.inj (hc.symm.trans hc')
  exact (denotes_const_iff (hwt _ (List.mem_of_lookup_eq_some hc))).2 rfl

/-- **Evaluation by the concrete evaluator.**  If `evalLit` computes the literal `c` for `e`, then
    in every store holding the literals of `bs`, of every runtime factory over `Core.Factory`,
    `e` evaluates to the value of `c`. -/
theorem eval_of_evalLit {F : Expression.Factory} (hF : F.factory = Core.Factory)
    {σ : CoreStore} {bs : LitBinds} {e : Expression.Expr} {c : LConst} {fuel : Nat}
    (hσ : LitBinds.Holds F.model.tcInterp σ bs) (h : evalLit fuel bs e = some c) :
    Expression.eval F σ e = some (SemValue.ofConst F.model.tcInterp c) := by
  unfold evalLit at h
  split at h
  · rename_i hchk
    simp only [Bool.and_eq_true, List.all_eq_true] at hchk
    obtain ⟨hwt, hfv⟩ := hchk
    split at h
    · rename_i m c' hev
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨v, hv, hd⟩ := boundedEvalSoundAt_coreFactory F hF fuel bs.rstore
          (bs.store F.model.tcInterp) e (.const m c') (storeDenotes_litBinds F hwt)
          (show evalBounded fuel F.factory bs.rstore e = _ by rw [hF]; exact hev)
        rw [(denotes_const_iff hc).1 hd] at hv
        have hcongr : Expression.eval F σ e = Expression.eval F (bs.store F.model.tcInterp) e :=
          LExpr.denoteEval_congr e fun x ty hx => by
            obtain ⟨c'', hc''⟩ := Option.isSome_iff_exists.mp (hfv (x, ty) hx)
            rw [hσ _ (List.mem_of_lookup_eq_some hc'')]
            simp [LitBinds.store, hc'']
        rw [hcongr]
        exact hv
      · cases h
    · cases h
  · cases h

/-- A store that holds `bs` and binds `x` to the value of `c`, leaving every other name alone,
    holds `bs.set x c`. -/
theorem LitBinds.Holds.set {tc : TyConstrInterp} {σ σ' : CoreStore} {bs : LitBinds}
    {x : Expression.Ident} {c : LConst} (hσ : LitBinds.Holds tc σ bs)
    (hx : σ' x = some (SemValue.ofConst tc c)) (hoth : ∀ w, x ≠ w → σ' w = σ w) :
    LitBinds.Holds tc σ' (bs.set x c) := by
  intro b hb
  simp only [LitBinds.set, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq] at hb
  rcases hb with rfl | ⟨hb, hne⟩
  · exact hx
  · exact (hoth b.1 (Ne.symm hne)).trans (hσ b hb)

/-- **Soundness of `stepLit`.**  A command step `stepLit` takes from `bs` to `bs'`, from a store
    holding `bs` of a runtime factory over `Core.Factory`, ends in a store holding `bs'` and emits
    no event. -/
private theorem stepLit_step {π : String → Option Procedure} {fuel : Nat} {bs bs' : LitBinds}
    {s : Statement} (h : stepLit fuel bs s = some bs') :
    ∃ c, s = .cmd c ∧ ∀ {F : Expression.Factory} {σ σ' : CoreStore} {tr : Trace Expression},
      F.factory = Core.Factory → LitBinds.Holds F.model.tcInterp σ bs →
      EvalCommandE π F σ c σ' tr → tr = [] ∧ LitBinds.Holds F.model.tcInterp σ' bs' := by
  unfold stepLit at h
  split at h
  · rename_i x e md
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨_, rfl, fun hF hσ hev => ?_⟩
    obtain ⟨v, he, -, hx, hoth, rfl⟩ := EvalCmdE.set_det_inv (evalCmdExtE_cmd_iff.mp hev)
    rw [eval_of_evalLit hF hσ hc, Option.some.injEq] at he
    subst he
    exact ⟨rfl, hσ.set hx hoth⟩
  · rename_i x ty e md
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨_, rfl, fun hF hσ hev => ?_⟩
    obtain ⟨v, he, -, hx, hoth, rfl, -⟩ := EvalCmdE.init_det_inv (evalCmdExtE_cmd_iff.mp hev)
    rw [eval_of_evalLit hF hσ hc, Option.some.injEq] at he
    subst he
    exact ⟨rfl, hσ.set hx hoth⟩
  · cases h

/-- **Soundness of `runLits`.**  A run of a straight-line body that `runLits` takes from `bs` to
    `bs'`, from an environment over `Core.Factory` whose store holds `bs`, terminates only in an
    environment with the same factory whose store holds `bs'`, and emits no event. -/
theorem runLits_run {π : String → Option Procedure} {fuel : Nat} :
    ∀ {ss : Statements} {bs bs' : LitBinds}, runLits fuel bs ss = some bs' →
      ∀ {ρ ρ' : Imperative.Env Expression} {tr : Trace Expression},
      ρ.factory.factory = Core.Factory → LitBinds.Holds ρ.factory.model.tcInterp ρ.store bs →
      StepStmtStarE Expression (EvalCommandE π) (.stmts ss ρ) tr (.terminal ρ') →
      tr = [] ∧ ρ'.factory = ρ.factory ∧
        LitBinds.Holds ρ'.factory.model.tcInterp ρ'.store bs'
  | [], bs, bs', h, ρ, ρ', tr, _, hσ, hrun => by
    simp only [runLits, Option.some.injEq] at h
    subst h
    obtain ⟨rfl, hcfg | hcfg⟩ := stmts_nil_runE (EvalCommandE π) hrun
    · cases hcfg
    · cases hcfg
      exact ⟨rfl, rfl, hσ⟩
  | s :: ss, bs, bs', h, ρ, ρ', tr, hF, hσ, hrun => by
    obtain ⟨bs₁, h₁, hrest⟩ := Option.bind_eq_some_iff.mp h
    rcases stmts_cons_headE (EvalCommandE π) hrun with ⟨hcfg, -⟩ | hseq
    · cases hcfg
    obtain ⟨ρ₁, tr₁, tr₂, rfl, hs, hss⟩ := seq_reaches_terminalE (EvalCommandE π) hseq
    obtain ⟨c, rfl, hstep⟩ := stepLit_step (π := π) h₁
    obtain ⟨hcmd, hρ₁⟩ := cmdRun_invE (EvalCmd := EvalCommandE π) (.inl hs)
    obtain ⟨rfl, hσ₁⟩ := hstep hF hσ hcmd
    rw [hρ₁] at hss
    obtain ⟨rfl, hfac, hσ'⟩ := runLits_run (ρ := { ρ with store := ρ₁.store }) hrest hF hσ₁ hss
    exact ⟨rfl, hfac, hσ'⟩

/-- The value of a literal is a value of every type whose monomorphic form is the literal's
    type. -/
private theorem valueOfTy_ofConst {F : Expression.Factory} {c : LConst} {ty : Expression.Ty}
    (h : ty.toMonoType? = some c.ty) :
    HasVal.valueOfTy F (SemValue.ofConst F.model.tcInterp c) ty :=
  ⟨rfl, h.trans (congrArg some (LConst.ty_isGround c).symm)⟩

/-- A statement list headed by a command must terminate when the command can execute, and the
    rest must terminate from every store the command can produce. -/
private theorem mustTerminate_cmd_cons {π : String → Option Procedure} {c : Cmd Expression}
    {ss : Statements} {ρ : Imperative.Env Expression}
    (hprog : ∃ σ' tr, EvalCmdE Expression ρ.factory ρ.store c σ' tr)
    (hall : ∀ σ' tr, EvalCmdE Expression ρ.factory ρ.store c σ' tr →
      (Logic.EventLang.coreBlock π).MustTerminate (.stmts ss { ρ with store := σ' })) :
    (Logic.EventLang.coreBlock π).MustTerminate (.stmts (.cmd (.cmd c) :: ss) ρ) := by
  obtain ⟨σ', tr, hc⟩ := hprog
  refine .step ⟨[], _, (.step_stmts_cons : CoreStepE π _ _ _)⟩
    fun _ _ (hs : CoreStepE π _ _ _) => ?_
  cases hs
  refine .step ⟨tr, _,
      (.step_seq_inner (.step_cmd (evalCmdExtE_cmd_iff.mpr hc)) : CoreStepE π _ _ _)⟩
    fun _ _ (hs : CoreStepE π _ _ _) => ?_
  cases hs with
  | step_seq_inner hs =>
    cases hs with
    | step_cmd hc' =>
      have hk := hall _ _ (evalCmdExtE_cmd_iff.mp hc')
      refine .step ⟨[], _, (.step_seq_done : CoreStepE π _ _ _)⟩
        fun _ _ (hs : CoreStepE π _ _ _) => ?_
      cases hs with
      | step_seq_done => exact hk
      | step_seq_inner hs =>
        exact absurd hs ((Logic.EventLang.coreBlock π).terminal_no_step _ _ _)

/-- A straight-line body `ss` whose writes are all at the type of their target
    (`runLitsProgresses` from `bs` and `Γ`) must terminate from every environment over
    `Core.Factory` whose store holds the literals of `bs`, binds every name of `Γ` to a value of
    its type, and leaves undeclared every name that `ss` declares and `Γ` does not. -/
private theorem runLits_mustTerminate {π : String → Option Procedure} {fuel : Nat} :
    ∀ (ss : Statements) (bs : LitBinds) (Γ : LitDecls) (ρ : Imperative.Env Expression),
      runLitsProgresses fuel bs Γ ss = true → ρ.factory.factory = Core.Factory →
      LitBinds.Holds ρ.factory.model.tcInterp ρ.store bs → LitDecls.Holds ρ.factory ρ.store Γ →
      (∀ x ∈ Block.definedVars ss true, Γ.lookup x = none → ρ.store x = none) →
      (Logic.EventLang.coreBlock π).MustTerminate (.stmts ss ρ)
  | [], _, _, _, _, _, _, _, _ =>
    .step ⟨[], _, (.step_stmts_nil : CoreStepE π _ _ _)⟩ fun _ _ (hs : CoreStepE π _ _ _) => by
      cases hs
      exact .terminal _
  | Stmt.cmd (CmdExt.cmd (Cmd.set x (.det e) md)) :: ss, bs, Γ, ρ, h, hF, hbs, hΓ, hfr => by
    simp only [runLitsProgresses] at h
    split at h
    · rename_i c hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hlk, hrest⟩ := h
      obtain ⟨prev, hprev, hprevTy⟩ := hΓ _ (List.mem_of_lookup_eq_some hlk)
      have hev := eval_of_evalLit hF hbs hc
      have hvTy := valueOfTy_ofConst (F := ρ.factory) (ty := .forAll [] c.ty) rfl
      refine mustTerminate_cmd_cons
        ⟨fun y => if y = x then some (SemValue.ofConst ρ.factory.model.tcInterp c) else ρ.store y,
          [], .eval_set hev (.update hprev (ite_eq_left rfl) fun y hy => ite_eq_right (Ne.symm hy))
            ⟨prev, _, hprev, hprevTy, hvTy⟩ (coreEvaluator_WellFormedSemanticEvalVar _)⟩
        fun σ' tr hc' => ?_
      obtain ⟨v, hv, -, hx, hoth, -⟩ := EvalCmdE.set_det_inv hc'
      rw [hev, Option.some.injEq] at hv
      subst hv
      have hxΓ : ∀ y, Γ.lookup y = none → x ≠ y := fun y hy hxy => by
        subst hxy; rw [hlk] at hy; cases hy
      refine runLits_mustTerminate ss _ Γ _ hrest hF (hbs.set hx hoth) (fun p hp => ?_)
        (fun y hy hny => (hoth y (hxΓ y hny)).trans (hfr y (by simp [Block.definedVars,
          Stmt.definedVars, HasVarsImp.definedVars, hy]) hny))
      obtain ⟨w, hw, hwTy⟩ := hΓ p hp
      by_cases hpx : x = p.1
      · rw [← hpx] at hw ⊢
        rw [hprev, Option.some.injEq] at hw
        subst hw
        exact ⟨_, hx, LawfulHasVal.valueOfTy_congr _ _ _ _ _ hwTy hprevTy hvTy⟩
      · exact ⟨w, (hoth _ hpx).trans hw, hwTy⟩
    · cases h
  | Stmt.cmd (CmdExt.cmd (Cmd.init x ty (.det e) md)) :: ss, bs, Γ, ρ, h, hF, hbs, hΓ, hfr => by
    simp only [runLitsProgresses] at h
    split at h
    · rename_i c hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
      obtain ⟨⟨hlk, hmono⟩, hrest⟩ := h
      have hnone : ρ.store x = none := hfr x (by
        simp [Block.definedVars, Stmt.definedVars, HasVarsImp.definedVars, CmdExt.definedVars,
          Cmd.definedVars]) hlk
      have hev := eval_of_evalLit hF hbs hc
      have hvTy := valueOfTy_ofConst (F := ρ.factory) hmono
      refine mustTerminate_cmd_cons
        ⟨fun y => if y = x then some (SemValue.ofConst ρ.factory.model.tcInterp c) else ρ.store y,
          [], .eval_init hev (.init hnone (ite_eq_left rfl) fun y hy => ite_eq_right (Ne.symm hy))
            hvTy (coreEvaluator_WellFormedSemanticEvalVar _)⟩
        fun σ' tr hc' => ?_
      obtain ⟨v, hv, -, hx, hoth, -, -⟩ := EvalCmdE.init_det_inv hc'
      rw [hev, Option.some.injEq] at hv
      subst hv
      refine runLits_mustTerminate ss _ _ _ hrest hF (hbs.set hx hoth) (fun p hp => ?_)
        (fun y hy hny => ?_)
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨_, hx, valueOfTy_ofConst rfl⟩
        · obtain ⟨w, hw, hwTy⟩ := hΓ p hp
          have hpx : x ≠ p.1 := fun hxp => by
            rw [← hxp, hnone] at hw; cases hw
          exact ⟨w, (hoth _ hpx).trans hw, hwTy⟩
      · have hxy : x ≠ y := fun hxy => by subst hxy; simp at hny
        have hyx : (y == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm hxy)
        have hny' : Γ.lookup y = none := by
          simpa only [List.lookup, hyx] using hny
        exact (hoth y hxy).trans (hfr y (by simp [Block.definedVars, Stmt.definedVars,
          HasVarsImp.definedVars, hy]) hny')
    · cases h
  | Stmt.cmd (CmdExt.cmd (Cmd.set _ .nondet _)) :: _, _, _, _, h, _, _, _, _ => by
    simp [runLitsProgresses] at h
  | Stmt.cmd (CmdExt.cmd (Cmd.init _ _ .nondet _)) :: _, _, _, _, h, _, _, _, _ => by
    simp [runLitsProgresses] at h
  | Stmt.cmd (CmdExt.cmd (Cmd.assert _ _ _)) :: _, _, _, _, h, _, _, _, _ => by
    simp [runLitsProgresses] at h
  | Stmt.cmd (CmdExt.cmd (Cmd.assume _ _ _)) :: _, _, _, _, h, _, _, _, _ => by
    simp [runLitsProgresses] at h
  | Stmt.cmd (CmdExt.cmd (Cmd.cover _ _ _)) :: _, _, _, _, h, _, _, _, _ => by
    simp [runLitsProgresses] at h
  | Stmt.cmd (CmdExt.call _ _ _) :: _, _, _, _, h, _, _, _, _ => by
    simp [runLitsProgresses] at h
  | Stmt.block _ _ _ :: _, _, _, _, h, _, _, _, _ => by simp [runLitsProgresses] at h
  | Stmt.ite _ _ _ _ :: _, _, _, _, h, _, _, _, _ => by simp [runLitsProgresses] at h
  | Stmt.loop _ _ _ _ _ :: _, _, _, _, h, _, _, _, _ => by simp [runLitsProgresses] at h
  | Stmt.exit _ _ :: _, _, _, _, h, _, _, _, _ => by simp [runLitsProgresses] at h
  | Stmt.typeDecl _ _ :: _, _, _, _, h, _, _, _, _ => by simp [runLitsProgresses] at h

/-- **Straight-line code over literals terminates.**  A body that `runLits` runs from no
    bindings with every write at the type of its target (`runLitsProgresses`), from an
    environment over `Core.Factory` whose store declares the names of `Γ` at their types and none
    of the names the body declares, terminates: every execution finishes, none gets stuck
    (`EventLang.MustTerminate.not_mayGetStuck`) and none diverges. -/
theorem runLits_terminates (π : String → Option Procedure) {fuel : Nat} {ss : Statements}
    {Γ : LitDecls} {ρ : Imperative.Env Expression} (h : runLitsProgresses fuel [] Γ ss = true)
    (hF : ρ.factory.factory = Core.Factory) (hΓ : LitDecls.Holds ρ.factory ρ.store Γ)
    (hfresh : ∀ x ∈ Block.definedVars ss true, ρ.store x = none) :
    (Logic.EventLang.coreBlock π).Terminates ss ρ :=
  runLits_mustTerminate ss [] Γ ρ h hF (fun _ hb => nomatch hb) hΓ fun x hx _ => hfresh x hx

end
end Core
