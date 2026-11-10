/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterReach
public import Strata.Languages.Core.InterpreterCallComplete
import all Strata.DL.Imperative.InterpreterCallCompleteProps
import all Strata.DL.Imperative.InterpreterCallComplete
import all Strata.DL.Imperative.InterpreterSemanticsSpec
import all Strata.DL.Imperative.CmdSemantics
import all Strata.Languages.Core.Interpreter
import Strata.DL.Imperative.CmdSemanticsProps
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.DL.Imperative.StmtCFGCallSemanticsProps
import Strata.DL.Imperative.CFGSemanticsProps
import Strata.DL.Lambda.LExprEvalFuelProps
import Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.Denote.LExprDenote

/-! # Reference runs on computable evaluations are replayed by the engine

The bridges from Core's reference semantics to the engine (reference ⇒ engine) without the
global premise `BoundedEvalComplete Expression`, which Core's bounded evaluator does not meet.
A reference run is engine-realizable when every expression it evaluates is computable
(`ComputableEval`), stated on the run as `EvalsComputable`: at every configuration the reference
semantics visits from the start (`Visits`: by reference steps, or by entering the structured body
of a call), every guard, deterministic right-hand side and call argument the statement in active
position (`ActiveStmt`) evaluates (`stmtEvalExprs`) is computable at its environment, and at every
CFG configuration it visits in a CFG callee body (`VisitsCFG`: by entering the CFG body of a call,
or by reference CFG steps), every right-hand side and call argument of the command heading the
residual commands and every guard of a conditional transfer (`cfgEvalExprs`) is computable.
The engine reads guards and failing conditions as the literals `HasBool.tt` and `HasBool.ff` up to
metadata, and a computable evaluation commits such a literal with some metadata.

Key definitions: `stmtEvalExprs`, `ActiveStmt`, `Visits`, `VisitsCFG`, `cfgEvalExprs`,
`EvalsComputable`,
`ComputableFailure`. Key theorems: `evalCmdEngE_of_computable`,
`writeBackTypedComplete_core`, `runChoices_of_evalsComputable` (the bridge to choice sequences,
`Calls.RunChoices`), and its corollaries `core_replayComplete_of_evalsComputable`,
`core_replayComplete_of_deterministic_computable`,
`core_runCoreInterp_complete_eval_of_computable`. -/

namespace Core

open Imperative Lambda

public section

/-! ## The expressions a reference run evaluates -/

/-- The expressions a statement evaluates when it steps: the guard of a deterministic `ite` or
    `loop`, the right-hand side of a deterministic `init` or `set`, the input arguments of a
    call. Assertions, assumptions and covers only record their condition. -/
@[expose] def stmtEvalExprs : Statement → List Expression.Expr
  | .ite (.det c) _ _ _ => [c]
  | .loop (.det g) _ _ _ _ => [g]
  | .cmd (.cmd (.init _ _ (.det e) _)) => [e]
  | .cmd (.cmd (.set _ (.det e) _)) => [e]
  | .cmd (.call _ args _) => Calls.getInputExprs args
  | _ => []

/-- `ActiveStmt c ρ s`: the statement `s` is in active position of the configuration `c`, under
    the environment `ρ`: `c` is `.stmt s ρ` inside enclosing sequence and block frames. -/
inductive ActiveStmt : CoreConfig → Imperative.Env Expression → Statement → Prop where
  /-- The active statement itself. -/
  | here {s : Statement} {ρ : Imperative.Env Expression} : ActiveStmt (.stmt s ρ) ρ s
  /-- Descend into the head of a sequence. -/
  | seq {inner : CoreConfig} {ss : Statements} {ρ : Imperative.Env Expression} {s : Statement} :
      ActiveStmt inner ρ s → ActiveStmt (.seq inner ss) ρ s
  /-- Descend into the body of a block. -/
  | block {label : Option String} {σp : CoreStore} {inner : CoreConfig}
      {ρ : Imperative.Env Expression} {s : Statement} :
      ActiveStmt inner ρ s → ActiveStmt (.block label σp inner) ρ s

mutual
/-- `Visits π c d`: the reference semantics visits the configuration `d` from `c`: by reference
    steps, or by entering the structured body of a call, from a callee frame the reference call
    rule builds (`CallEntry`), where the call is in active position of a visited configuration or
    heads the residual commands of a visited CFG configuration (`VisitsCFG`). -/
inductive Visits (π : String → Option Procedure) (c : CoreConfig) : CoreConfig → Prop where
  /-- The start configuration. -/
  | refl : Visits π c c
  /-- A reference step from a visited configuration. -/
  | step {x y : CoreConfig} {evs : List (Event Expression)} :
      Visits π c x → CoreStepE π x evs y → Visits π c y
  /-- The entry of the structured body of a call in active position of a visited configuration. -/
  | call {x : CoreConfig} {ρ : Imperative.Env Expression} {n : String}
      {args : List (CallArg Expression)} {md : MetaData Expression} {p : Procedure}
      {ss : Statements} {σAO : CoreStore} :
      Visits π c x → ActiveStmt x ρ (.cmd (.call n args md)) → π n = some p →
      p.body = .structured ss → CallEntry ρ.factory ρ.store p args σAO →
      Visits π c (.stmt (Stmt.block "" ss #[]) ⟨σAO, ρ.factory⟩)
  /-- The entry of the structured body of a call heading the residual commands of a visited CFG
      configuration. -/
  | cfgCall {g : Imperative.DetCFG Expression Command} {t : String} {cs : List Command}
      {tr : DetTransferCmd String Expression} {ρ : Imperative.Env Expression} {n : String}
      {args : List (CallArg Expression)} {md : MetaData Expression} {p : Procedure}
      {ss : Statements} {σAO : CoreStore} :
      VisitsCFG π c (.inBlock g t (.call n args md :: cs) tr ρ) → π n = some p →
      p.body = .structured ss → CallEntry ρ.factory ρ.store p args σAO →
      Visits π c (.stmt (Stmt.block "" ss #[]) ⟨σAO, ρ.factory⟩)

/-- `VisitsCFG π c d`: the reference semantics visits the CFG configuration `d` from `c`: by
    entering the CFG body of a call at its entry block, from a callee frame the reference call
    rule builds (`CallEntry`), where the call is in active position of a visited configuration
    (`Visits`) or heads the residual commands of a visited CFG configuration, or by reference CFG
    steps from a visited CFG configuration. -/
inductive VisitsCFG (π : String → Option Procedure) (c : CoreConfig) :
    CFGConfig String Command Expression → Prop where
  /-- The entry of the CFG body of a call in active position of a visited configuration. -/
  | call {x : CoreConfig} {ρ : Imperative.Env Expression} {n : String}
      {args : List (CallArg Expression)} {md : MetaData Expression} {p : Procedure}
      {g : Imperative.DetCFG Expression Command} {σAO : CoreStore} :
      Visits π c x → ActiveStmt x ρ (.cmd (.call n args md)) → π n = some p →
      p.body = .cfg g → CallEntry ρ.factory ρ.store p args σAO →
      VisitsCFG π c (.atBlock g g.entry ⟨σAO, ρ.factory⟩)
  /-- The entry of the CFG body of a call heading the residual commands of a visited CFG
      configuration. -/
  | cfgCall {g' : Imperative.DetCFG Expression Command} {t : String} {cs : List Command}
      {tr : DetTransferCmd String Expression} {ρ : Imperative.Env Expression} {n : String}
      {args : List (CallArg Expression)} {md : MetaData Expression} {p : Procedure}
      {g : Imperative.DetCFG Expression Command} {σAO : CoreStore} :
      VisitsCFG π c (.inBlock g' t (.call n args md :: cs) tr ρ) → π n = some p →
      p.body = .cfg g → CallEntry ρ.factory ρ.store p args σAO →
      VisitsCFG π c (.atBlock g g.entry ⟨σAO, ρ.factory⟩)
  /-- A reference CFG step from a visited CFG configuration. -/
  | step {x y : CFGConfig String Command Expression} {evs : List (Event Expression)} :
      VisitsCFG π c x → StepCFGE Expression (EvalCommandE π) x evs y → VisitsCFG π c y
end

/-- The expressions a CFG configuration evaluates when it steps: those the command heading the
    residual commands of its block evaluates (`stmtEvalExprs`), or, once the residual commands are
    exhausted, the guard of the block's conditional transfer. -/
@[expose] def cfgEvalExprs : CFGConfig String Command Expression → List Expression.Expr
  | .inBlock _ _ (c :: _) _ _ => stmtEvalExprs (.cmd c)
  | .inBlock _ _ [] (.condGoto e _ _ _) _ => [e]
  | _ => []

/-- **Every expression a reference run from `c` evaluates is computable**: at every configuration
    the reference semantics visits from `c` (`Visits`), every expression the statement in active
    position evaluates (`stmtEvalExprs`) is computable (`ComputableEval`) at the environment it
    is evaluated in, and at every CFG configuration it visits in a CFG callee body (`VisitsCFG`),
    every expression the configuration evaluates (`cfgEvalExprs`) is computable at the
    configuration's environment. -/
@[expose] def EvalsComputable (π : String → Option Procedure) (c : CoreConfig) : Prop :=
  (∀ d, Visits π c d → ∀ ρ s, ActiveStmt d ρ s → ∀ e ∈ stmtEvalExprs s,
    ComputableEval ρ.factory ρ.store e) ∧
  ∀ d, VisitsCFG π c d → ∀ e ∈ cfgEvalExprs d, ComputableEval d.getEnv.factory d.getEnv.store e

/-! ## Core's executable checks on computable evaluations -/

/-- A runtime value that denotes `v` type checks against the factory to the type of `v`'s
    sort. -/
theorem typeCheckWith_of_denotes {F : Expression.Factory} {r : Expression.Expr}
    {v : Expression.Val} (h : InterpLang.Denotes F r v) :
    r.typeCheckWith F.factory [] = some v.sort.toMonoTy := by
  have ht := denotes_typeCheck h
  have hs := (denotes_iff.1 h).2.1
  unfold LExpr.typeCheckWith at hs ⊢
  split at hs
  · rename_i ho
    simp only [ho, ↓reduceIte]
    exact ht
  · cases hs

/-- **Core's write-back check is complete**: a runtime value denoting a value of the type of the
    value a variable's runtime value denotes passes the engine's write-back check. -/
theorem writeBackTypedComplete_core : WriteBackTypedComplete Expression := by
  rintro F old r vo v ty hold hr ⟨-, hvo⟩ ⟨-, hv⟩
  refine ⟨(denotes_iff.1 hr).1, ?_⟩
  have hs : vo.sort.toMonoTy = v.sort.toMonoTy := Option.some.inj (hvo.symm.trans hv)
  simp only [InterpLang.ops, replayValueOps, beq_iff_eq]
  show LExpr.typeCheckWith F.factory [] old = LExpr.typeCheckWith F.factory [] r
  rw [typeCheckWith_of_denotes hold, typeCheckWith_of_denotes hr, hs]

/-- Every runtime value the engine commits for a computable expression whose reference value is
    `v` is a literal whose value is `v`. -/
theorem computable_committed {F : Expression.Factory} {σ : SemanticStore Expression}
    {e : Expression.Expr} {v : Expression.Val} {σr : RStore Expression} {n : Nat}
    {r : Expression.Expr} (h : ComputableEval F σ e) (hv : Expression.eval F σ e = some v)
    (hS : StoreDenotes F σr σ) (hb : evalBounded n F.factory σr e = some r) :
    ∃ m c, r = .const m c ∧ v = SemValue.ofConst F.model.tcInterp c := by
  obtain ⟨hd, τ, hτ, -, -⟩ := (LExpr.denoteEval_eq_some_iff (T := CoreLParams)).1 hv
  obtain ⟨c, -, hc, n0, m, hb0⟩ := h σr τ hS hd hτ
  obtain ⟨-, he, -⟩ := evalBounded_eq_some_iff.1 hb
  obtain ⟨-, he0, -⟩ := evalBounded_eq_some_iff.1 hb0
  exact ⟨m, c, eval_value_true_deterministic _ _ _ _ _ _ _ he he0,
    Option.some.inj (hv.symm.trans hc)⟩

/-- The value of a literal is the Boolean value `b` only for the literal `b`. -/
private theorem ofConst_eq_ofBool {tc : TyConstrInterp} {c : LConst} {b : Bool}
    (h : SemValue.ofConst tc c = SemValue.ofBool tc b) : c = .boolConst b := by
  have hs := congrArg SemValue.sort h
  cases c with
  | boolConst b' =>
    obtain ⟨-, -, hv⟩ := SemValue.mk.inj h
    exact congrArg LConst.boolConst (eq_of_heq (by exact hv : b' ≍ b))
  | _ => simp [SemValue.ofConst, SemValue.ofBool, LConst.ty, LMonoTy.substTyVars, LMonoTy.int,
      LMonoTy.real, LMonoTy.string, LSort.bool] at hs

/-- On a computable expression whose reference value is the Boolean `b`, every runtime value
    the engine commits is the Boolean literal of `b` with some metadata. -/
private theorem engEvalOK_bool {F : Expression.Factory} {σ : SemanticStore Expression}
    {e : Expression.Expr} {b : Bool} (h : ComputableEval F σ e)
    (hv : Expression.eval F σ e = some (SemValue.ofBool F.model.tcInterp b)) :
    EngEvalOK Expression F σ e (fun _ r => ∃ m, r = LExpr.boolConst m b) := by
  intro σr n r hS hb
  obtain ⟨m, c, rfl, hc⟩ := computable_committed h hv hS hb
  obtain rfl := ofConst_eq_ofBool hc.symm
  exact ⟨m, rfl⟩

/-- The evaluation of a computable guard whose reference value is `ttVal` is one the engine
    performs, every committed value read as `true` (`InterpLang.boolLit?`) (`EngEval`). -/
theorem engEval_tt_of_computable {F : Expression.Factory} {σ : SemanticStore Expression}
    {e : Expression.Expr} (h : ComputableEval F σ e)
    (hv : Expression.eval F σ e = some (HasBool.ttVal F)) :
    EngEval Expression F σ e (fun _ r => InterpLang.boolLit? r = some true) :=
  ⟨engEvalReach_of_computableEval h, fun σr n r hS hb =>
    (engEvalOK_bool (b := true) h hv σr n r hS hb).elim fun m hm => hm ▸ boolLit?_boolConst m _⟩

/-- The evaluation of a computable guard whose reference value is `ffVal` is one the engine
    performs, every committed value read as `false` (`InterpLang.boolLit?`) (`EngEval`). -/
theorem engEval_ff_of_computable {F : Expression.Factory} {σ : SemanticStore Expression}
    {e : Expression.Expr} (h : ComputableEval F σ e)
    (hv : Expression.eval F σ e = some (HasBool.ffVal F)) :
    EngEval Expression F σ e (fun _ r => InterpLang.boolLit? r = some false) :=
  ⟨engEvalReach_of_computableEval h, fun σr n r hS hb =>
    (engEvalOK_bool (b := false) h hv σr n r hS hb).elim fun m hm => hm ▸ boolLit?_boolConst m _⟩

/-- The value of a literal has the literal's type as the monomorphic type of its sort. -/
private theorem ofConst_sort (tc : TyConstrInterp) (c : LConst) :
    (SemValue.ofConst tc c).sort.toMonoTy = c.ty :=
  LConst.ty_isGround c

/-- **Reference base commands on computable right-hand sides are engine-realizable**: a reference
    evaluation of a base command whose deterministic right-hand side is computable is one the
    engine performs, every check of the engine passing, its nondeterministic values typed. -/
theorem evalCmdEngE_of_computable {f : Expression.Factory} {σ σ' : CoreStore}
    {c : Imperative.Cmd Expression} {evs : Trace Expression}
    (h : EvalCmdE (P := Expression) f σ c σ' evs)
    (hc : ∀ e ∈ stmtEvalExprs (.cmd (.cmd c)), ComputableEval f σ e) :
    EvalCmdEngE Expression (ChoiceRecord.typed Expression) f σ c σ' evs := by
  cases h with
  | eval_init he i hty hwf =>
    obtain ⟨hx, rfl⟩ := i.eq_update
    have hce := hc _ (List.mem_singleton_self _)
    refine .eval_init hx he ⟨engEvalReach_of_computableEval hce, fun σr n r hS hb => ?_⟩ hty hwf
    obtain ⟨m, c, rfl, rfl⟩ := computable_committed hce he hS hb
    obtain ⟨-, hτ⟩ := hty
    rw [ofConst_sort] at hτ
    refine ⟨isValue_const_true _ m c, ?_⟩
    simp only [InterpLang.ops, replayValueOps, valueHasType, hτ, valueHasMonoType,
      Bool.and_eq_true, beq_iff_eq, isGroundTy_iff]
    exact ⟨rfl, LConst.ty_isGround c⟩
  | eval_init_unconstrained i hty hwf =>
    obtain ⟨hx, rfl⟩ := i.eq_update
    exact .eval_init_nondet hx hty hty hwf
  | eval_set he u hty hwf =>
    obtain ⟨⟨old, ho⟩, rfl⟩ := u.eq_update
    have hce := hc _ (List.mem_singleton_self _)
    refine .eval_set ho he ⟨engEvalReach_of_computableEval hce,
      fun σr n r hS hb ro hro => ?_⟩ hty hwf
    obtain ⟨m, c, rfl, rfl⟩ := computable_committed hce he hS hb
    obtain ⟨prev, ty, hp, hpt, hvt⟩ := hty
    exact writeBackTypedComplete_core f ro _ prev _ ty (hS.2 _ ro prev hro hp)
      (denotes_const_iff.2 rfl) hpt hvt
  | eval_set_nondet u hty hwf =>
    obtain ⟨⟨old, ho⟩, rfl⟩ := u.eq_update
    obtain ⟨prev, ty, hp, ⟨hpc, hpt⟩, ⟨hvc, hvt⟩⟩ := id hty
    obtain rfl := Option.some.inj (hp.symm.trans ho)
    refine .eval_set_nondet (ty := LTy.forAll [] prev.sort.toMonoTy) ho
      (fun σr ro hS hro => ?_) ⟨hvc, ?_⟩ hty (fun σr ro r hS hro hr => ?_) hwf
    · show (ro.typeCheckWith f.factory []).map (LTy.forAll []) = _
      rw [typeCheckWith_of_denotes (hS.2 _ ro prev hro hp)]
      rfl
    · exact congrArg some (Option.some.inj (hpt.symm.trans hvt))
    · exact writeBackTypedComplete_core f ro r prev _ ty (hS.2 _ ro prev hro hp) hr
        ⟨hpc, hpt⟩ ⟨hvc, hvt⟩
  | eval_assert => exact .eval_assert
  | eval_assume => exact .eval_assume
  | eval_cover => exact .eval_cover

/-! ## Reference runs on computable evaluations have choice sequences -/

/-- The context a statement `s` is evaluated in under `ρ`, relative to a set `Q` of
    configurations and a set `QC` of CFG configurations: every expression `s` evaluates is
    computable, and when `s` is a call, the body of the callee starts, from every callee frame
    the call rule builds, at a configuration `Q` admits (a structured body) or at a CFG
    configuration `QC` admits (a CFG body). -/
private def StmtCtx (π : String → Option Procedure) (Q : CoreConfig → Prop)
    (QC : CFGConfig String Command Expression → Prop) (ρ : Imperative.Env Expression)
    (s : Statement) : Prop :=
  (∀ e ∈ stmtEvalExprs s, ComputableEval ρ.factory ρ.store e) ∧
    ∀ n args md p σAO, s = .cmd (.call n args md) → π n = some p →
      CallEntry ρ.factory ρ.store p args σAO →
      (∀ ss, p.body = .structured ss → Q (.stmt (Stmt.block "" ss #[]) ⟨σAO, ρ.factory⟩)) ∧
        ∀ g, p.body = .cfg g → QC (.atBlock g g.entry ⟨σAO, ρ.factory⟩)

/-- The context a reference step at `x` is taken in: every statement in active position of `x`
    is evaluated in the context `StmtCtx` relative to `Q` and `QC`. -/
private def StepCtx (π : String → Option Procedure) (Q : CoreConfig → Prop)
    (QC : CFGConfig String Command Expression → Prop) (x : CoreConfig) : Prop :=
  ∀ ρ s, ActiveStmt x ρ s → StmtCtx π Q QC ρ s

/-- The context a reference CFG step at `x` is taken in: the command heading the residual
    commands of its block is evaluated in the context `StmtCtx` relative to `Q` and `QC`, and,
    once the residual commands are exhausted, the guard of a conditional transfer is
    computable. -/
private def CFGCtx (π : String → Option Procedure) (Q : CoreConfig → Prop)
    (QC : CFGConfig String Command Expression → Prop) :
    CFGConfig String Command Expression → Prop
  | .inBlock _ _ (c :: _) _ ρ => StmtCtx π Q QC ρ (.cmd c)
  | .inBlock _ _ [] (.condGoto e _ _ _) ρ => ComputableEval ρ.factory ρ.store e
  | _ => True

/-- A reference run from a configuration of a set `Q` closed under its steps reads its choices
    off an oracle, given that each of its steps from a configuration of `Q` does, through an
    oracle-reading step relation `R` over the oracle-reading command relation at some
    call-nesting height, `R` being monotone in its command relation. -/
private theorem oracle_star {π : String → Option Procedure} {α : Type 1}
    {S : α → List (Event Expression) → α → Prop}
    {R : Calls.OracleCmdRel Expression → α × List Expression.Val → List (Event Expression) →
      α × List Expression.Val → Prop}
    (hR : ∀ {E E' : Calls.OracleCmdRel Expression},
      (∀ f σ c σ' evs o o', E f σ c σ' evs o o' → E' f σ c σ' evs o o') →
        ∀ {x e y}, R E x e y → R E' x e y)
    {x y : α} {evs : List (Event Expression)} (h : ReflTransTrace S x evs y) {Q : α → Prop}
    (hQ : ∀ x e y, Q x → S x e y → Q y)
    (hS : ∀ x e y, Q x → S x e y →
      ∃ cs n, ∀ rest, R (Calls.OracleCmdAt π n) (x, cs ++ rest) e (y, rest)) (hx : Q x) :
    ∃ cs n, ∀ rest, ReflTransTrace (R (Calls.OracleCmdAt π n)) (x, cs ++ rest) evs (y, rest) := by
  induction h with
  | refl => exact ⟨[], 0, fun _ => .refl _⟩
  | step x e y _ _ hs _ ih =>
    obtain ⟨a, n, ha⟩ := hS x e y hx hs
    obtain ⟨b, m, hb⟩ := ih (hQ x e y hx hs)
    refine ⟨a ++ b, n + m, fun r => ?_⟩
    rw [List.append_assoc]
    exact .step _ _ _ _ _ (hR (fun _ _ _ _ _ _ _ => Calls.oracleCmdAt_mono π (by omega)) (ha _))
      ((hb r).imp fun _ _ _ => hR fun _ _ _ _ _ _ _ => Calls.oracleCmdAt_mono π (by omega))

/-- A reference step in a context where its evaluations are computable reads its choices off an
    oracle, given that every command step in its context does. -/
private theorem oracleStep {π : String → Option Procedure} {Q : CoreConfig → Prop}
    {QC : CFGConfig String Command Expression → Prop} {E : CoreCmdRel}
    (hE : ∀ f σ cmd σ' evs, E f σ cmd σ' evs → StmtCtx π Q QC ⟨σ, f⟩ (.cmd cmd) →
      ∃ cs n, ∀ rest, Calls.OracleCmdAt π n f σ cmd σ' evs (cs ++ rest) rest)
    {x y : CoreConfig} {evs : List (Event Expression)} (hs : StepStmtE Expression E x evs y)
    (hx : StepCtx π Q QC x) :
    ∃ cs n, ∀ rest, Calls.OracleStepE (Calls.OracleCmdAt π n) (x, cs ++ rest) evs (y, rest) := by
  induction hs with
  | step_cmd h =>
    obtain ⟨cs, n, H⟩ := hE _ _ _ _ _ h (hx _ _ .here)
    exact ⟨cs, n, fun r => .step_cmd (H r)⟩
  | step_ite_true he =>
    exact ⟨[], 0, fun _ => .step_det (.step_ite_true he
      (engEval_tt_of_computable ((hx _ _ .here).1 _ (List.mem_singleton_self _)) he))⟩
  | step_ite_false he =>
    exact ⟨[], 0, fun _ => .step_det (.step_ite_false he
      (engEval_ff_of_computable ((hx _ _ .here).1 _ (List.mem_singleton_self _)) he))⟩
  | step_loop_enter he =>
    exact ⟨[], 0, fun _ => .step_det (.step_loop_enter he
      (engEval_tt_of_computable ((hx _ _ .here).1 _ (List.mem_singleton_self _)) he))⟩
  | step_loop_exit he =>
    exact ⟨[], 0, fun _ => .step_det (.step_loop_exit he
      (engEval_ff_of_computable ((hx _ _ .here).1 _ (List.mem_singleton_self _)) he))⟩
  | step_ite_nondet_true => exact ⟨[_], 0, fun _ => .step_ite_then⟩
  | step_ite_nondet_false => exact ⟨[_], 0, fun _ => .step_ite_else⟩
  | step_loop_nondet_enter => exact ⟨[_], 0, fun _ => .step_loop_enter⟩
  | step_loop_nondet_exit => exact ⟨[_], 0, fun _ => .step_loop_exit⟩
  | step_seq_inner _ ih =>
    obtain ⟨cs, n, H⟩ := ih fun ρ s ha => hx ρ s (.seq ha)
    exact ⟨cs, n, fun r => .step_seq_inner (H r)⟩
  | step_block_body _ ih =>
    obtain ⟨cs, n, H⟩ := ih fun ρ s ha => hx ρ s (.block ha)
    exact ⟨cs, n, fun r => .step_block_body (H r)⟩
  | _ => exact ⟨[], 0, fun _ => .step_det (by constructor <;> assumption)⟩

/-- A reference CFG step in a context where its evaluations are computable reads its choices off
    an oracle, given that every command step in its context does. -/
private theorem oracleCFGStep {π : String → Option Procedure} {Q : CoreConfig → Prop}
    {QC : CFGConfig String Command Expression → Prop} {E : CoreCmdRel}
    (hE : ∀ f σ cmd σ' evs, E f σ cmd σ' evs → StmtCtx π Q QC ⟨σ, f⟩ (.cmd cmd) →
      ∃ cs n, ∀ rest, Calls.OracleCmdAt π n f σ cmd σ' evs (cs ++ rest) rest)
    {x y : CFGConfig String Command Expression} {evs : List (Event Expression)}
    (hs : StepCFGE Expression E x evs y) (hx : CFGCtx π Q QC x) :
    ∃ cs n, ∀ rest, OracleCFGStepE (Calls.OracleCmdAt π n) (x, cs ++ rest) evs (y, rest) := by
  cases hs with
  | step_cmd h =>
    obtain ⟨cs, n, H⟩ := hE _ _ _ _ _ h hx
    exact ⟨cs, n, fun r => .step_cmd (H r)⟩
  | fetch h => exact ⟨[], 0, fun _ => .step_admin (.fetch h)⟩
  | goto_true he =>
    exact ⟨[], 0, fun _ => .step_admin (.goto_true he (engEval_tt_of_computable hx he))⟩
  | goto_false he =>
    exact ⟨[], 0, fun _ => .step_admin (.goto_false he (engEval_ff_of_computable hx he))⟩
  | finish => exact ⟨[], 0, fun _ => .step_admin .finish⟩

/-- A reference command evaluation in a context where its evaluations are computable reads its
    choices off an oracle, when callee bodies start in a set `Q` of configurations closed under
    reference steps, every configuration of which is such a context, or in a set `QC` of CFG
    configurations closed under reference CFG steps, every CFG configuration of which is such a
    context. -/
private theorem oracleCmd {π : String → Option Procedure}
    {Q : CoreConfig → Prop} {QC : CFGConfig String Command Expression → Prop}
    (hQ : ∀ x evs y, Q x → CoreStepE π x evs y → Q y)
    (hQC : ∀ x evs y, QC x → StepCFGE Expression (EvalCommandE π) x evs y → QC y)
    (hctx : ∀ x, Q x → StepCtx π Q QC x) (hctxC : ∀ x, QC x → CFGCtx π Q QC x)
    {f : Expression.Factory} {σ σ' : CoreStore} {cmd : Command} {evs : Trace Expression}
    (h : EvalCommandE π f σ cmd σ' evs) :
    StmtCtx π Q QC ⟨σ, f⟩ (.cmd cmd) →
      ∃ cs n, ∀ rest, Calls.OracleCmdAt π n f σ cmd σ' evs (cs ++ rest) rest := by
  induction h using EvalCmdExtE.induct with
  | cmd_sem h =>
    intro hc
    have heng := evalCmdEngE_of_computable h hc.1
    cases h with
    | eval_init_unconstrained hi =>
      obtain ⟨_, hx, _⟩ := hi
      exact ⟨[_], 0, fun _ => ⟨_, rfl, heng, .inr ⟨_, _, rfl, hx, .inl ⟨_, _, rfl⟩⟩⟩⟩
    | eval_set_nondet hu =>
      obtain ⟨_, hx, _⟩ := hu
      exact ⟨[_], 0, fun _ => ⟨_, rfl, heng, .inr ⟨_, _, rfl, hx, .inr ⟨_, rfl⟩⟩⟩⟩
    | _ => exact ⟨[], 0, fun _ => ⟨_, rfl, heng, .inl ⟨rfl, rfl⟩⟩⟩
  | call_sem hπ he _ hx ih =>
    rintro ⟨hargs, hbody⟩
    obtain ⟨hs, hg⟩ := hbody _ _ _ _ _ rfl hπ he
    have hreach := fun e he' => engEvalReach_of_computableEval (hargs e he')
    have hwb := Calls.writeBackOK_of_complete writeBackTypedComplete_core hx
    rcases ih with ⟨ss, ρ', hss, rfl, hr⟩ | ⟨g, ρ', hcfg, rfl, hr⟩
    · obtain ⟨cs, n, hn⟩ := oracle_star Calls.OracleStepE.imp hr
        (fun x e y hq hs => hQ x e y hq (hs.imp fun _ _ _ _ _ ⟨h, _⟩ => h))
        (fun x _ _ hq hs => oracleStep (fun _ _ _ _ _ ⟨_, hm⟩ => hm) hs (hctx x hq))
        (hs ss hss)
      exact ⟨cs, n + 1, fun r =>
        .inr (.inl ⟨_, _, _, _, _, _, _, _, rfl, hπ, hss, he, hn r, hx, rfl, hreach, hwb⟩)⟩
    · obtain ⟨cs, n, hn⟩ := oracle_star Calls.OracleCFGStepE.imp hr
        (fun x e y hq hs => hQC x e y hq (hs.imp fun _ _ _ _ _ ⟨h, _⟩ => h))
        (fun x _ _ hq hs => oracleCFGStep (fun _ _ _ _ _ ⟨_, hm⟩ => hm) hs (hctxC x hq))
        (hg g hcfg)
      exact ⟨cs, n + 1, fun r =>
        .inr (.inr ⟨_, _, _, _, _, _, _, _, rfl, hπ, hcfg, he, hn r, hx, rfl, hreach, hwb⟩)⟩

/-- **Reference runs on computable evaluations have choice sequences** (reference ⇒ engine).  A
    reference run of `π` from `c` along which every evaluated expression is computable
    (`EvalsComputable`), in structured and CFG callee bodies alike, has a choice sequence
    (`Calls.RunChoices`): it is a run the engine reproduces. -/
theorem runChoices_of_evalsComputable (π : String → Option Procedure) {c c' : CoreConfig}
    {evs : List (Event Expression)} (hcomp : EvalsComputable π c) (h : CoreStepStarE π c evs c') :
    ∃ cs, Calls.RunChoices π c evs c' cs := by
  have hctx : ∀ x, Visits π c x → StepCtx π (Visits π c) (VisitsCFG π c) x := fun x hx ρ s ha =>
    ⟨hcomp.1 x hx ρ s ha, fun _ _ _ _ _ hs hp he =>
      ⟨fun _ hb => .call hx (hs ▸ ha) hp hb he, fun _ hb => .call hx (hs ▸ ha) hp hb he⟩⟩
  have hctxC : ∀ x, VisitsCFG π c x → CFGCtx π (Visits π c) (VisitsCFG π c) x := by
    rintro (_ | ⟨_, _, _ | ⟨_, _⟩, _ | _, _⟩ | _) hx
    all_goals first
      | trivial
      | exact hcomp.2 _ hx _ (List.mem_singleton_self _)
      | exact ⟨hcomp.2 _ hx, fun _ _ _ _ _ hs hp he =>
          ⟨fun _ hb => .cfgCall (Stmt.cmd.inj hs ▸ hx) hp hb he,
            fun _ hb => .cfgCall (Stmt.cmd.inj hs ▸ hx) hp hb he⟩⟩
  obtain ⟨cs, n, hn⟩ := oracle_star Calls.OracleStepE.imp h (fun _ _ _ hq hs => .step hq hs)
    (fun x _ _ hq hs => oracleStep (fun _ _ _ _ _ hc hx => oracleCmd
      (fun _ _ _ hq hs => .step hq hs) (fun _ _ _ hq hs => .step hq hs) hctx hctxC hc hx) hs
      (hctx x hq)) .refl
  exact ⟨cs, n, hn⟩

/-! ## Completeness of Core replay on computable evaluations -/

/-- The event `ev` is a failure of the target obligation whose condition is computable: an
    assertion of the target whose condition the reference evaluator evaluates to `ffVal`, or a
    cover of the target whose condition it evaluates to `ttVal`, the condition being computable
    (`ComputableEval`) at the event's snapshot. -/
@[expose] def ComputableFailure (target : AssertId Expression) : Event Expression → Prop
  | .assert a => target.label = a.label ∧ target.md = a.metadata ∧
      Expression.eval a.factory a.store a.expr = some (HasBool.ffVal a.factory) ∧
      ComputableEval a.factory a.store a.expr
  | .cover a => target.label = a.label ∧ target.md = a.metadata ∧
      Expression.eval a.factory a.store a.expr = some (HasBool.ttVal a.factory) ∧
      ComputableEval a.factory a.store a.expr
  | .assume _ => False

/-- On a computable expression whose reference value is the Boolean `b`, every runtime value the
    engine commits equals the Boolean literal of `b` up to metadata. -/
private theorem engEval_eqModuloMeta {F : Expression.Factory} {σ : SemanticStore Expression}
    {e : Expression.Expr} {b : Bool} (h : ComputableEval F σ e)
    (hv : Expression.eval F σ e = some (SemValue.ofBool F.model.tcInterp b)) :
    EngEval Expression F σ e (fun _ r => InterpLang.eqModuloMeta r (LExpr.boolConst () b)) :=
  ⟨engEvalReach_of_computableEval h, fun σr n r hS hb =>
    (engEvalOK_bool h hv σr n r hS hb).elim fun m hm => by subst hm; cases b <;> rfl⟩

/-- A failure with a computable condition is one the engine evaluates
    (`Calls.assertFailureE`). -/
theorem assertFailureE_of_computable
    {target : AssertId Expression} : ∀ {ev : Event Expression}, ComputableFailure target ev →
      Calls.assertFailureE target ev
  | .assert _, ⟨hl, hm, he, hc⟩ =>
    ⟨hl, hm, he, engEval_eqModuloMeta (b := false) hc he⟩
  | .cover _, ⟨hl, hm, he, hc⟩ =>
    ⟨hl, hm, he, engEval_eqModuloMeta (b := true) hc he⟩

/-- **Completeness of Core replay on computable evaluations** (reference ⇒ engine).  If a
    reference run of `π` from the configuration `cex.cfg` stands for, along which every evaluated
    expression is computable (`EvalsComputable`), emits a failure of the target with a computable
    condition (`ComputableFailure`), then the run has a choice sequence `cs` (`Calls.RunChoices`)
    such that, whenever `cex.oracle` begins with a runtime segment witnessing `cs`
    (`OracleWitness`) that passes `choose`'s type check (`OracleTyped`), `cex` replayed with its
    own oracle reaches that failure (`genuine`) at every sufficiently large fuel and call-depth
    limit. -/
theorem core_replayComplete_of_evalsComputable {F : Expression.Factory}
    (π : String → Option Procedure) (target : AssertId Expression)
    (cex : CexA Expression Command) {evs : List (Event Expression)}
    {final : Config Expression Command} (hd : cex.cfg.Denoting F) (ht : cex.cfg.Tracked)
    (hcomp : EvalsComputable π (cex.cfg.abs F)) (hrun : CoreStepStarE π (cex.cfg.abs F) evs final)
    (hfail : ∃ ev ∈ evs, ComputableFailure target ev) :
    ∃ cs, Calls.RunChoices π (cex.cfg.abs F) evs final cs ∧
      ∀ rs : List Expression.Expr, rs <+: cex.oracle → OracleWitness F rs cs →
        OracleTyped F (ChoiceRecord.typed Expression) rs cs →
          ∃ f0, ∀ fuel d, f0 ≤ fuel → f0 ≤ d → genuine π target fuel cex d := by
  obtain ⟨cs, hcs⟩ := runChoices_of_evalsComputable π hcomp hrun
  obtain ⟨ev, hev, hf⟩ := hfail
  exact ⟨cs, hcs, fun rs hpre hrs hty => core_replayComplete π target cex hd ht hcs rs hpre hrs hty
    ⟨ev, hev, assertFailureE_of_computable hf⟩⟩

/-- **Completeness of Core replay on deterministic programs with computable evaluations**
    (reference ⇒ engine).  If the program is deterministic (`Calls.ProgDeterministic`), and a
    reference run of `π` from `cex.cfg`, along which every evaluated expression is computable,
    emits a failure of the target with a computable condition, then `cex`, replayed with its own
    oracle, reaches that failure (`genuine`) at every sufficiently large fuel and call-depth
    limit. -/
theorem core_replayComplete_of_deterministic_computable {F : Expression.Factory}
    (π : String → Option Procedure) (target : AssertId Expression)
    (cex : CexA Expression Command) {evs : List (Event Expression)}
    {final : Config Expression Command} (hd : cex.cfg.Denoting F) (ht : cex.cfg.Tracked)
    (hdet : Calls.ProgDeterministic π (cex.cfg.abs F))
    (hcomp : EvalsComputable π (cex.cfg.abs F)) (hrun : CoreStepStarE π (cex.cfg.abs F) evs final)
    (hfail : ∃ ev ∈ evs, ComputableFailure target ev) :
    ∃ f0, ∀ fuel d, f0 ≤ fuel → f0 ≤ d → genuine π target fuel cex d := by
  obtain ⟨cs, hcs, h⟩ := core_replayComplete_of_evalsComputable π target cex hd ht hcomp hrun hfail
  obtain rfl := Calls.runChoices_nil_of_deterministic hdet hcs
  exact h [] (List.nil_prefix) ⟨rfl, nofun⟩ nofun

/-- **Whole-run Core `EvalM` completeness on deterministic programs with computable evaluations**
    (reference ⇒ engine).  If the program is deterministic, and a reference run of `π` from
    `start`, along which every evaluated expression is computable, ends in a done configuration
    `final` and its events go through at `opts` for every list of well-formed runtime events
    standing for them, then `runCoreInterp π` at `EvalM` from every interpreter configuration
    denoting `start` reaches one denoting `final`, from every state at every large enough fuel
    and call-depth limit, prepending runtime events denoting exactly the run's events to the
    trace. -/
theorem core_runCoreInterp_complete_eval_of_computable {F : Expression.Factory}
    (π : String → Option Procedure) (opts : EvalOpts)
    {start final : Config Expression Command} {evs : List (Event Expression)}
    (istart : IConfig Expression Command) (hstart : istart.Denotes F start)
    (hdet : Calls.ProgDeterministic π start) (hcomp : EvalsComputable π start)
    (hrun : CoreStepStarE π start evs final) (hdone : Config.Done final)
    (hemit : ∀ revs : List (IEvent Expression), (∀ ev ∈ revs, Calls.EvGood F ev) →
      revs.map (REvent.abs F) = evs → EvalEmitsOk opts revs) (st : EvalState) :
    ∃ (f0 : Nat) (final' : IConfig Expression Command) (st' : EvalState), final'.Denotes F final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        evalRun (runCoreInterp π fuel istart d) opts st = (.ok final', st'))
      ∧ obsEval.TraceExt F st st' evs := by
  obtain ⟨cs, hcs⟩ := runChoices_of_evalsComputable π hcomp hrun
  exact core_runCoreInterp_complete_eval_of_deterministic π opts istart hstart hdet hcs hdone
    hemit st

end

end Core
