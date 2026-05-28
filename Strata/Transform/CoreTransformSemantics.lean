/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementSemanticsProps
public import Strata.Transform.CoreTransform
import all Strata.Languages.Core.StatementSemantics
import all Strata.Languages.Core.StatementSemanticsProps

/-! # Block-evaluator helpers for `CoreTransform`-generated statements

  These helpers connect `Core.Transform.create{Havocs,Inits,InitVars}` (defined
  in `Strata.Transform.CoreTransform`) to the small-step
  `EvalStatementsContract` semantics from
  `Strata.Languages.Core.StatementSemantics`.

  They were previously private to `Strata.Transform.CallElimCorrect`; moving them
  here lets multiple downstream proofs reuse them, and avoids the import cycle
  that would arise from extending `StatementSemanticsProps` directly (which
  cannot depend on `CoreTransform`).
-/

public section

namespace Core

open Imperative

/-- A single contract-evaluating command produces a single-statement
    `EvalStatementsContract` derivation.  Reusable scaffold for the
    block helpers below. -/
theorem singleCmdToStmts
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval} {σ σ' : CoreStore} {c : Core.Command}
    (Hcmd : Core.EvalCommandContract π δ σ c σ' false) :
    EvalStatementsContract π φ ⟨σ, δ, false⟩
      [Imperative.Stmt.cmd c]
      ⟨σ', δ, false⟩ := by
  unfold EvalStatementsContract Imperative.EvalStmtsSmall
  apply ReflTrans.step _ _ _ Imperative.StepStmt.step_stmts_cons
  apply ReflTrans.step _ _ _
          (Imperative.StepStmt.step_seq_inner (Imperative.StepStmt.step_cmd Hcmd))
  apply ReflTrans.step _ _ _ Imperative.StepStmt.step_seq_done
  exact ReflTrans.step _ _ _ Imperative.StepStmt.step_stmts_nil (.refl _)

/-- Evaluating `createHavocs vs md` under contract semantics steps from σ
    through `HavocVars vs` to σ'. -/
theorem H_havocs
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval} {σ σ' : CoreStore}
    {vs : List Expression.Ident}
    {md : Imperative.MetaData Expression}
    (Hwfv : Imperative.WellFormedSemanticEvalVar δ)
    (Hdef : Imperative.isDefined σ vs)
    (Hhav : HavocVars σ vs σ') :
    EvalStatementsContract π φ ⟨σ, δ, false⟩
      (Core.Transform.createHavocs vs md)
      ⟨σ', δ, false⟩ := by
  induction vs generalizing σ with
  | nil =>
    have heq : σ' = σ := by cases Hhav; rfl
    subst heq
    exact ReflTrans.step _ _ _ Imperative.StepStmt.step_stmts_nil (.refl _)
  | cons h t ih =>
    cases Hhav with
    | update_some hUp hTail =>
      rename_i v σmid
      have Hcmd : Core.EvalCommandContract π δ σ
                    (Core.CmdExt.cmd (Imperative.Cmd.set h .nondet md))
                    σmid false :=
        Core.EvalCommandContract.cmd_sem (Imperative.EvalCmd.eval_set_nondet hUp Hwfv)
      have Hdef_tail : Imperative.isDefined σ t :=
        fun v hv => Hdef v (List.mem_cons_of_mem h hv)
      have HdefTail : Imperative.isDefined σmid t :=
        Imperative.UpdateStateDefMonotone Hdef_tail hUp
      have HrecTail := ih HdefTail hTail
      simp only [Core.Transform.createHavocs, List.map_cons,
                 Core.Transform.createHavoc]
      exact EvalStatementsContractApp (singleCmdToStmts Hcmd) HrecTail

/-- Evaluating a single `Statement.init x ty (.det e) md` under contract
    semantics steps from σ to `updatedState σ x v`, given `δ σ e = some v`
    and that `x` is currently undefined in σ. -/
theorem H_init
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval} {σ : CoreStore}
    {x : Expression.Ident} {ty : Expression.Ty}
    {e : Expression.Expr} {v : Expression.Expr}
    {md : Imperative.MetaData Expression}
    (Heval : δ σ e = some v)
    (Hnone : σ x = none)
    (Hwfv : Imperative.WellFormedSemanticEvalVar δ) :
    EvalStatementsContract π φ ⟨σ, δ, false⟩
      [Statement.init x ty (.det e) md]
      ⟨updatedState σ x v, δ, false⟩ := by
  have Hinit : Imperative.InitState Expression σ x v (updatedState σ x v) := by
    apply Imperative.InitState.init Hnone
    · simp [updatedState]
    · intro y Hne
      simp [updatedState]
      intro Heq
      exact absurd Heq.symm Hne
  have Hcmd : Core.EvalCommandContract π δ σ
                (Core.CmdExt.cmd (Imperative.Cmd.init x ty (.det e) md))
                (updatedState σ x v) false :=
    Core.EvalCommandContract.cmd_sem (Imperative.EvalCmd.eval_init Heval Hinit Hwfv)
  exact singleCmdToStmts Hcmd

/-- If `k ∉ ks`, then `ReadValues σ ks vs` is preserved when extending σ
    with an unrelated key.  Re-derived from the legacy `ReadValuesUpdatedState`. -/
theorem readValues_updatedState
    {σ : CoreStore} {k : Expression.Ident} {v : Expression.Expr}
    {ks : List Expression.Ident} {vs : List Expression.Expr}
    (Hnin : ¬ k ∈ ks)
    (Hrd : ReadValues σ ks vs) :
    ReadValues (updatedState σ k v) ks vs := by
  induction ks generalizing vs with
  | nil =>
    cases Hrd
    exact ReadValues.read_none
  | cons x xs ih =>
    cases vs with
    | nil => cases Hrd
    | cons v' vs' =>
      cases Hrd with
      | read_some Hsome Hrest =>
      have Hxk : x ≠ k :=
        fun heq => Hnin (heq ▸ List.mem_cons_self)
      have Hnin_t : ¬ k ∈ xs :=
        fun hin => Hnin (List.mem_cons_of_mem _ hin)
      have Hsome' : updatedState σ k v x = some v' := by
        simp [updatedState, Hxk]
        exact Hsome
      exact ReadValues.read_some Hsome' (ih Hnin_t Hrest)

/-- Evaluating `createInitVars trips md` under contract semantics steps σ
    through one `Statement.init` per trip, given:
    - generated names disjoint from referenced source names (Nodup gen ++ src),
    - `ReadValues σ source-names readVals`,
    - generated names not currently defined in σ. -/
theorem H_initVars
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval} {σ : CoreStore}
    {trips : List ((Expression.Ident × Expression.Ty) × Expression.Ident)}
    {readVals : List Expression.Expr}
    {md : Imperative.MetaData Expression}
    (Hwfv : Imperative.WellFormedSemanticEvalVar δ)
    (Hndup : List.Nodup (trips.unzip.fst.unzip.fst ++ trips.unzip.snd))
    (Hrd : ReadValues σ trips.unzip.snd readVals)
    (Hndef : Imperative.isNotDefined σ trips.unzip.fst.unzip.fst) :
    EvalStatementsContract π φ ⟨σ, δ, false⟩
      (Core.Transform.createInitVars trips md)
      ⟨updatedStates σ trips.unzip.fst.unzip.fst readVals, δ, false⟩ := by
  induction trips generalizing σ readVals with
  | nil =>
    cases Hrd
    simp only [Core.Transform.createInitVars, List.map_nil,
               List.unzip_nil, updatedStates, updatedStates', List.zip_nil_left]
    exact ReflTrans.step _ _ _ Imperative.StepStmt.step_stmts_nil (.refl _)
  | cons h t ih =>
    obtain ⟨⟨x', ty⟩, src⟩ := h
    -- Unfold the head Read, and the indices in goal/Hndup/Hndup
    simp only [List.unzip_cons] at Hrd Hndup Hndef ⊢
    -- Hrd : ReadValues σ (src :: t.unzip.snd) readVals
    -- Use a separate term-mode lemma to invert Hrd cleanly.
    rcases Hrd with _ | ⟨_, Hrest_rd⟩
    rename_i tail_vals vv Hsrc
    -- After simp, Hndup : List.Nodup (x' :: t.unzip.fst.unzip.fst ++
    --                                  src :: t.unzip.snd)
    -- Tail Nodup: drop x' from heads, drop src from tails
    have Hndup_tail :
        List.Nodup (t.unzip.fst.unzip.fst ++ t.unzip.snd) := by
      rw [List.cons_append] at Hndup
      have Hndup1 : List.Nodup (t.unzip.fst.unzip.fst ++ src :: t.unzip.snd) :=
        (List.nodup_cons.mp Hndup).2
      apply List.Sublist.nodup ?_ Hndup1
      apply List.Sublist.append_left
      exact List.sublist_cons_self src t.unzip.snd
    -- isNotDefined for the tail keys after updating x'
    have Hndef_t : Imperative.isNotDefined σ t.unzip.fst.unzip.fst := by
      unfold Imperative.isNotDefined
      intro y hy
      exact Hndef y (List.mem_cons_of_mem _ hy)
    -- Read-values preserved on updated state for the tail's source list.
    -- We need `¬ x' ∈ t.unzip.snd` from Hndup.
    have Hxsrc_tail : ¬ x' ∈ t.unzip.snd := by
      rw [List.cons_append] at Hndup
      -- Hndup : List.Nodup (x' :: (t.unzip.fst.unzip.fst ++ src :: t.unzip.snd))
      have Hnotin : x' ∉ (t.unzip.fst.unzip.fst ++ src :: t.unzip.snd) :=
        (List.nodup_cons.mp Hndup).1
      intro Hin
      apply Hnotin
      apply List.mem_append_right
      exact List.mem_cons_of_mem _ Hin
    have Hrest_rd' : ReadValues (updatedState σ x' vv) t.unzip.snd tail_vals :=
      readValues_updatedState Hxsrc_tail Hrest_rd
    -- isNotDefined preserved on the updated state for the rest of heads.
    have Hndef_t' :
        Imperative.isNotDefined (updatedState σ x' vv) t.unzip.fst.unzip.fst := by
      unfold Imperative.isNotDefined
      intro y hy
      have Hyne : y ≠ x' := by
        intro heq
        rw [List.cons_append] at Hndup
        have Hnotin : x' ∉ (t.unzip.fst.unzip.fst ++ src :: t.unzip.snd) :=
          (List.nodup_cons.mp Hndup).1
        apply Hnotin
        apply List.mem_append_left
        exact heq.symm ▸ hy
      simp [updatedState, Hyne]
      exact Hndef_t y hy
    -- Recursive call.
    have Hrec := ih Hndup_tail Hrest_rd' Hndef_t'
    -- Build the head step: Statement.init x' ty (.det (fvar src)) md
    have Hsrc_eval : δ σ (Lambda.LExpr.fvar () src none) = some vv := by
      have := Hwfv (Lambda.LExpr.fvar () src none) src σ
      simp [Imperative.HasFvar.getFvar] at this
      rw [this]
      exact Hsrc
    have Hxnone : σ x' = none := Hndef x' (by simp)
    have Hhead :
        EvalStatementsContract π φ ⟨σ, δ, false⟩
          [Statement.init x' ty
            (.det (Lambda.LExpr.fvar () src none)) md]
          ⟨updatedState σ x' vv, δ, false⟩ :=
      H_init Hsrc_eval Hxnone Hwfv
    -- Glue: createInitVars unfolds to head :: rest, and the updated states
    -- compose.
    have Hshape :
        updatedStates σ (x' :: t.unzip.fst.unzip.fst) (vv :: tail_vals) =
        updatedStates (updatedState σ x' vv) t.unzip.fst.unzip.fst tail_vals := by
      simp [updatedStates, updatedStates']
    rw [Hshape]
    have Hcombined :
        EvalStatementsContract π φ ⟨σ, δ, false⟩
          ([Statement.init x' ty
              (.det (Lambda.LExpr.fvar () src none)) md] ++
           Core.Transform.createInitVars t md)
          ⟨updatedStates (updatedState σ x' vv) t.unzip.fst.unzip.fst tail_vals,
            δ, false⟩ := EvalStatementsContractApp Hhead Hrec
    have Hunfold :
        Core.Transform.createInitVars (((x', ty), src) :: t) md =
        [Statement.init x' ty (.det (Lambda.LExpr.fvar () src none)) md] ++
          Core.Transform.createInitVars t md := by
      simp [Core.Transform.createInitVars, Core.Transform.createInitVar]
    rw [Hunfold]
    exact Hcombined

/-- If `k` is not in the free variables of `e`, evaluating `e` is unchanged
    when σ is extended with `k ↦ v`.  Re-derived from the legacy
    `EvalExpressionUpdatedState` for the small-step proof. -/
theorem evalExpression_updatedState
    {δ : CoreEval} {σ : CoreStore}
    {k : Expression.Ident} {v : Expression.Expr}
    {e v' : Expression.Expr}
    (Hwfv : Imperative.WellFormedSemanticEvalVar δ)
    (Hwfc : Core.WellFormedCoreEvalCong δ)
    (Hwfvl : Imperative.WellFormedSemanticEvalVal δ)
    (Hnin : ¬ k ∈ Imperative.HasVarsPure.getVars e)
    (Heval : δ σ e = some v') :
    δ (updatedState σ k v) e = some v' := by
  simp [Imperative.WellFormedSemanticEvalVar, Imperative.HasFvar.getFvar] at Hwfv
  simp [Imperative.WellFormedSemanticEvalVal] at Hwfvl
  have Hval := Hwfvl.2
  simp [← Heval] at *
  induction e <;>
    simp [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
  case const c | op o ty | bvar b =>
    rw [Hval]; rw [Hval]; constructor; constructor
  case fvar m n ty =>
    simp [Hwfv]
    simp [updatedState]
    grind
  case abs m ty e ih =>
    apply ((Hwfc.1 (updatedState σ k v) σ))
    grind
  case quant m kk ty tr e trih eih =>
    apply Hwfc.quantcongr <;> grind
  case app m fn e fnih eih =>
    apply Hwfc.appcongr <;> grind
  case ite m c t e cih tih eih =>
    apply Hwfc.itecongr <;> grind
  case eq m e1 e2 e1ih e2ih =>
    apply Hwfc.eqcongr <;> grind

/-- List version: if `k` is not in the union of free variables of any `e ∈ es`,
    `EvalExpressions δ σ es vs` survives the extension `σ[k ↦ v]`. -/
theorem evalExpressions_updatedState
    {δ : CoreEval} {σ : CoreStore}
    {k : Expression.Ident} {v : Expression.Expr}
    {es : List Expression.Expr} {vs : List Expression.Expr}
    (Hwfv : Imperative.WellFormedSemanticEvalVar δ)
    (Hwfc : Core.WellFormedCoreEvalCong δ)
    (Hwfvl : Imperative.WellFormedSemanticEvalVal δ)
    (Hnin : ¬ k ∈ es.flatMap (Imperative.HasVarsPure.getVars (P:=Expression)))
    (Heval : EvalExpressions (P:=Core.Expression) δ σ es vs) :
    EvalExpressions (P:=Core.Expression) δ (updatedState σ k v) es vs := by
  induction es generalizing vs with
  | nil =>
    cases Heval
    exact EvalExpressions.eval_none
  | cons e' es_t ih =>
    cases vs with
    | nil => cases Heval
    | cons v_h vs_t =>
      cases Heval with
      | eval_some Hdef He Hes =>
      have Hnin_h : ¬ k ∈ Imperative.HasVarsPure.getVars (P:=Expression) e' := by
        intro Hin
        apply Hnin
        simp [List.mem_flatMap]
        exact Or.inl Hin
      have Hnin_t : ¬ k ∈
          es_t.flatMap (Imperative.HasVarsPure.getVars (P:=Expression)) := by
        intro Hin
        apply Hnin
        simp [List.mem_flatMap]
        right
        simp [List.mem_flatMap] at Hin
        obtain ⟨e2, He2_in, He2_var⟩ := Hin
        exact ⟨e2, He2_in, He2_var⟩
      have Hdef' : Imperative.isDefined (updatedState σ k v)
                    (Imperative.HasVarsPure.getVars e') := by
        unfold Imperative.isDefined
        intro x Hx
        have Hsome := Hdef x Hx
        simp [updatedState]
        split <;> simp_all
      have He' : δ (updatedState σ k v) e' = some v_h :=
        evalExpression_updatedState Hwfv Hwfc Hwfvl Hnin_h He
      exact EvalExpressions.eval_some Hdef' He' (ih Hnin_t Hes)

/-- Evaluating `createInits trips md` under contract semantics steps σ
    through one `Statement.init` per trip with the trip's expression
    evaluating to the corresponding value. -/
theorem H_inits
    {π : String → Option Procedure}
    {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
    {δ : CoreEval} {σ : CoreStore}
    {trips : List ((Expression.Ident × Expression.Ty) × Expression.Expr)}
    {evalVals : List Expression.Expr}
    {md : Imperative.MetaData Expression}
    (Hwfv : Imperative.WellFormedSemanticEvalVar δ)
    (Hwfvl : Imperative.WellFormedSemanticEvalVal δ)
    (Hwfc : Core.WellFormedCoreEvalCong δ)
    (Hdisj : trips.unzip.fst.unzip.fst.Disjoint
              (List.flatMap (Imperative.HasVarsPure.getVars (P:=Expression))
                  trips.unzip.snd))
    (Hndup : List.Nodup trips.unzip.fst.unzip.fst)
    (Heval : EvalExpressions (P:=Core.Expression) δ σ trips.unzip.snd evalVals)
    (Hndef : Imperative.isNotDefined σ trips.unzip.fst.unzip.fst) :
    EvalStatementsContract π φ ⟨σ, δ, false⟩
      (Core.Transform.createInits trips md)
      ⟨updatedStates σ trips.unzip.fst.unzip.fst evalVals, δ, false⟩ := by
  induction trips generalizing σ evalVals with
  | nil =>
    cases Heval
    simp only [Core.Transform.createInits, List.map_nil,
               List.unzip_nil, updatedStates, updatedStates', List.zip_nil_left]
    exact ReflTrans.step _ _ _ Imperative.StepStmt.step_stmts_nil (.refl _)
  | cons h t ih =>
    obtain ⟨⟨x', ty⟩, e⟩ := h
    simp only [List.unzip_cons] at Heval Hdisj Hndup Hndef ⊢
    cases Heval
    rename_i tail_vals vv Hdef He Hes
    have Hndup_t : List.Nodup t.unzip.fst.unzip.fst :=
      (List.nodup_cons.mp Hndup).2
    have Hxnotin_e : ¬ x' ∈ Imperative.HasVarsPure.getVars (P:=Expression) e := by
      intro Hin
      have Hxmem : x' ∈ (x' :: t.unzip.fst.unzip.fst) := by simp
      have Hflat : x' ∈ (e :: t.unzip.snd).flatMap
                  (Imperative.HasVarsPure.getVars (P:=Expression)) := by
        simp [List.mem_flatMap]
        exact Or.inl Hin
      exact Hdisj Hxmem Hflat
    have Hxnotin_es : ¬ x' ∈ t.unzip.snd.flatMap
        (Imperative.HasVarsPure.getVars (P:=Expression)) := by
      intro Hin
      have Hxmem : x' ∈ (x' :: t.unzip.fst.unzip.fst) := by simp
      have Hflat : x' ∈ (e :: t.unzip.snd).flatMap
                  (Imperative.HasVarsPure.getVars (P:=Expression)) := by
        simp [List.mem_flatMap]
        right
        simp [List.mem_flatMap] at Hin
        obtain ⟨e2, He2_in, He2_var⟩ := Hin
        exact ⟨e2, He2_in, He2_var⟩
      exact Hdisj Hxmem Hflat
    have Hes' : EvalExpressions (P:=Core.Expression) δ
                  (updatedState σ x' vv) t.unzip.snd tail_vals :=
      evalExpressions_updatedState Hwfv Hwfc Hwfvl Hxnotin_es Hes
    have Hxnone : σ x' = none := Hndef x' (by simp)
    have Hndef_t : Imperative.isNotDefined σ t.unzip.fst.unzip.fst := by
      unfold Imperative.isNotDefined
      intro y hy
      exact Hndef y (List.mem_cons_of_mem _ hy)
    have Hndef_t' : Imperative.isNotDefined (updatedState σ x' vv)
                      t.unzip.fst.unzip.fst := by
      unfold Imperative.isNotDefined
      intro y hy
      have Hyne : y ≠ x' := by
        intro heq
        have Hnotin : x' ∉ t.unzip.fst.unzip.fst :=
          (List.nodup_cons.mp Hndup).1
        apply Hnotin
        exact heq ▸ hy
      simp [updatedState, Hyne]
      exact Hndef_t y hy
    have Hdisj_t :
        t.unzip.fst.unzip.fst.Disjoint
          (List.flatMap (Imperative.HasVarsPure.getVars (P:=Expression))
            t.unzip.snd) := by
      intro y Hy_in_t Hy_in_var
      have Hy_in_h : y ∈ (x' :: t.unzip.fst.unzip.fst) :=
        List.mem_cons_of_mem _ Hy_in_t
      have Hflat : y ∈ (e :: t.unzip.snd).flatMap
                  (Imperative.HasVarsPure.getVars (P:=Expression)) := by
        simp [List.mem_flatMap]
        right
        simp [List.mem_flatMap] at Hy_in_var
        obtain ⟨e2, He2_in_t, He2_var⟩ := Hy_in_var
        exact ⟨e2, He2_in_t, He2_var⟩
      exact Hdisj Hy_in_h Hflat
    have Hrec : EvalStatementsContract π φ ⟨updatedState σ x' vv, δ, false⟩
                  (Core.Transform.createInits t md)
                  ⟨updatedStates (updatedState σ x' vv) t.unzip.fst.unzip.fst
                                   tail_vals, δ, false⟩ :=
      ih Hdisj_t Hndup_t Hes' Hndef_t'
    have Hhead :
        EvalStatementsContract π φ ⟨σ, δ, false⟩
          [Statement.init x' ty (.det e) md]
          ⟨updatedState σ x' vv, δ, false⟩ :=
      H_init He Hxnone Hwfv
    have Hshape :
        updatedStates σ (x' :: t.unzip.fst.unzip.fst) (vv :: tail_vals) =
        updatedStates (updatedState σ x' vv) t.unzip.fst.unzip.fst tail_vals := by
      simp [updatedStates, updatedStates']
    rw [Hshape]
    have Hcombined :
        EvalStatementsContract π φ ⟨σ, δ, false⟩
          ([Statement.init x' ty (.det e) md] ++ Core.Transform.createInits t md)
          ⟨updatedStates (updatedState σ x' vv) t.unzip.fst.unzip.fst tail_vals,
            δ, false⟩ := EvalStatementsContractApp Hhead Hrec
    have Hunfold :
        Core.Transform.createInits (((x', ty), e) :: t) md =
        [Statement.init x' ty (.det e) md] ++ Core.Transform.createInits t md := by
      simp [Core.Transform.createInits, Core.Transform.createInit]
    rw [Hunfold]
    exact Hcombined

/-! ### Generic `mapM`-over-`CoreGenM` helpers

The Arg/Out/Old gen-ident families share the structural shape
`List.mapM (g : α → CoreGenM Ident) l`, where the only difference is
`α` (Unit for Arg, Ident for Out/Old) and the per-element generator `g`.
The four facts below — length preservation, generated-stack accounting,
WF preservation, and `Forall`-lifting — depend only on (i) `mapM`'s
recursion shape and (ii) a pointwise hypothesis on the per-element
generator.  We prove each generically once and derive the 12
single-iterator specializations (3 each for Arg/Out/Old × length /
GeneratedWF / WFMono / Forall) as one-line corollaries. -/

/-- Length preservation for any `List.mapM` against `CoreGenM`. -/
theorem genIdentMapM_length' {α : Type}
    {g : α → CoreGenM Expression.Ident}
    {l : List α} {s : CoreGenState} :
    (List.mapM g l s).fst.length = l.length := by
  induction l generalizing s <;> simp_all
  case nil =>
    simp [pure, StateT.pure]
  case cons h t ih =>
    simp [bind, StateT.bind, Functor.map]
    split
    simp [StateT.map, Functor.map]
    apply ih

/-- Generated-stack accounting for `List.mapM` once the per-element
    generator is known to push exactly one element onto `generated`. -/
theorem genIdentMapM_GeneratedWF {α : Type}
    {g : α → CoreGenM Expression.Ident}
    (Hone : ∀ {a : α} {s s' : CoreGenState} {l : Expression.Ident},
              g a s = (l, s') → s'.generated = l :: s.generated)
    {l : List α} {s s' : CoreGenState} {ls : List Expression.Ident}
    (Hgen : List.mapM g l s = (ls, s')) :
    s'.generated = ls.reverse ++ s.generated := by
  induction l generalizing s s' ls with
  | nil =>
      simp only [List.mapM_nil, pure, StateT.pure] at Hgen
      cases Hgen
      simp
  | cons h t ih =>
      simp only [List.mapM_cons, bind, StateT.bind, pure, StateT.pure] at Hgen
      cases hg1 : g h s with
      | mk a₁ s₁ =>
        rw [hg1] at Hgen
        simp only at Hgen
        cases hg2 : List.mapM g t s₁ with
        | mk a₂ s₂ =>
          rw [hg2] at Hgen
          cases Hgen
          have HH₁ := Hone hg1
          have HH₂ := ih hg2
          rw [HH₂, HH₁]
          simp

/-- WF preservation for `List.mapM` once the per-element generator
    preserves WF. -/
theorem genIdentMapM_WFMono {α : Type}
    {g : α → CoreGenM Expression.Ident}
    (Hone : ∀ {a : α} {s s' : CoreGenState} {l : Expression.Ident},
              CoreGenState.WF s → g a s = (l, s') → CoreGenState.WF s')
    {l : List α} {s s' : CoreGenState} {ls : List Expression.Ident}
    (Hwf : CoreGenState.WF s) (Hgen : List.mapM g l s = (ls, s')) :
    CoreGenState.WF s' := by
  induction l generalizing s s' ls with
  | nil =>
      simp only [List.mapM_nil, pure, StateT.pure] at Hgen
      cases Hgen
      exact Hwf
  | cons h t ih =>
      simp only [List.mapM_cons, bind, StateT.bind, pure, StateT.pure] at Hgen
      cases hg1 : g h s with
      | mk a₁ s₁ =>
        rw [hg1] at Hgen
        simp only at Hgen
        cases hg2 : List.mapM g t s₁ with
        | mk a₂ s₂ =>
          rw [hg2] at Hgen
          cases Hgen
          exact ih (Hone Hwf hg1) hg2

/-- `Forall`-lifting for `List.mapM` once the per-element generator
    produces values satisfying the predicate. -/
theorem genIdentMapM_Forall {α : Type} {P : Expression.Ident → Prop}
    {g : α → CoreGenM Expression.Ident}
    (Hone : ∀ {a : α} {s s' : CoreGenState} {l : Expression.Ident},
              g a s = (l, s') → P l)
    {l : List α} {s s' : CoreGenState} {ls : List Expression.Ident}
    (Hgen : List.mapM g l s = (ls, s')) :
    Forall P ls := by
  induction l generalizing s s' ls with
  | nil =>
      simp only [List.mapM_nil, pure, StateT.pure] at Hgen
      cases Hgen
      simp [Forall]
  | cons h t ih =>
      simp only [List.mapM_cons, bind, StateT.bind, pure, StateT.pure] at Hgen
      cases hg1 : g h s with
      | mk a₁ s₁ =>
        rw [hg1] at Hgen
        simp only at Hgen
        cases hg2 : List.mapM g t s₁ with
        | mk a₂ s₂ =>
          rw [hg2] at Hgen
          cases Hgen
          simp [Forall]
          exact ⟨Hone hg1, ih hg2⟩

/-! ### Length lemmas for the `gen*ExprIdents{,Trip}` family

The `_snd` and `*GeneratedWF` helpers below need to know that
`genArgExprIdents n` produces a list of length exactly `n`, etc.  These
follow inductively from `genIdent`'s contract.  Proved here so that the
trip-level helpers can quote them directly. -/

/-- The fst-projection of running `genArgExprIdent` `t.length`-many times
    (with `t : List Unit`) is a list of length `t.length`.  This is the
    raw form; `genArgExprIdents_length'` specializes to `n = t.length`. -/
theorem genArgExprIdent_len'
    {t : List Unit} {s : CoreGenState} :
    (List.mapM (fun _ => Core.Transform.genArgExprIdent) t s).fst.length = t.length :=
  genIdentMapM_length'

theorem genArgExprIdents_length'
    (n : Nat) (s : CoreGenState) :
    (Core.Transform.genArgExprIdents n s).fst.length = n := by
  simp only [Core.Transform.genArgExprIdents]
  rw [genArgExprIdent_len']
  simp

theorem genArgExprIdents_length
    {n : Nat} {s s' : CoreGenState} {ls : List Expression.Ident}
    (Hgen : Core.Transform.genArgExprIdents n s = (ls, s')) :
    ls.length = n := by
  have := genArgExprIdents_length' n s
  rw [Hgen] at this
  exact this

theorem genOutExprIdent_len'
    {t : List Expression.Ident} {s : CoreGenState} :
    (List.mapM Core.Transform.genOutExprIdent t s).fst.length = t.length :=
  genIdentMapM_length'

theorem genOutExprIdents_length'
    (idents : List Expression.Ident) (s : CoreGenState) :
    (Core.Transform.genOutExprIdents idents s).fst.length = idents.length := by
  simp only [Core.Transform.genOutExprIdents]
  exact genOutExprIdent_len'

theorem genOutExprIdents_length
    {idents : List Expression.Ident} {s s' : CoreGenState}
    {ls : List Expression.Ident}
    (Hgen : Core.Transform.genOutExprIdents idents s = (ls, s')) :
    ls.length = idents.length := by
  have := genOutExprIdents_length' idents s
  rw [Hgen] at this
  exact this

theorem genOldExprIdent_len'
    {t : List Expression.Ident} {s : CoreGenState} :
    (List.mapM Core.Transform.genOldExprIdent t s).fst.length = t.length :=
  genIdentMapM_length'

theorem genOldExprIdents_length'
    (idents : List Expression.Ident) (s : CoreGenState) :
    (Core.Transform.genOldExprIdents idents s).fst.length = idents.length := by
  simp only [Core.Transform.genOldExprIdents]
  exact genOldExprIdent_len'

theorem genOldExprIdents_length
    {idents : List Expression.Ident} {s s' : CoreGenState}
    {ls : List Expression.Ident}
    (Hgen : Core.Transform.genOldExprIdents idents s = (ls, s')) :
    ls.length = idents.length := by
  have := genOldExprIdents_length' idents s
  rw [Hgen] at this
  exact this

/-! ### Trip-level success extractors

The Arg and Out trip wrappers share a uniform success-branch shape: they
length-check, run a `genXxxExprIdents` call, and `return
(gen_idents.zip ys).zip xs`.  Extracting the post-condition once removes
~80 LoC of repeated monad-layer simping. -/

theorem genArgExprIdentsTrip_extract
    {inputs : @Lambda.LTySignature Visibility} {args : List Expression.Expr}
    {s s' : Core.Transform.CoreTransformState}
    {argTrips : List ((Expression.Ident × Lambda.LTy) × Expression.Expr)}
    (Hgen : Core.Transform.genArgExprIdentsTrip inputs args s = (Except.ok argTrips, s')) :
    let gen_idents := (Core.Transform.genArgExprIdents args.length s.genState).fst
    let s_gen     := (Core.Transform.genArgExprIdents args.length s.genState).snd
    (gen_idents.zip (List.map Prod.snd inputs)).zip args = argTrips ∧
    s' = { s with genState := s_gen } ∧
    inputs.length = args.length := by
  simp only [Core.Transform.genArgExprIdentsTrip] at Hgen
  split at Hgen
  case isTrue Hne =>
    simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, StateT.pure] at Hgen
    cases Hgen
  case isFalse Hlen =>
    simp [bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.lift,
          ExceptT.pure, StateT.bind, StateT.pure, pure, monadLift,
          MonadLift.monadLift, liftM, Functor.map, StateT.map,
          Core.Transform.liftCoreGenM] at Hgen
    refine ⟨?_, ?_, ?_⟩
    · have := congrArg Prod.fst Hgen
      simp at this
      exact this
    · have := congrArg Prod.snd Hgen
      simp at this
      exact this.symm
    · simp at Hlen; exact Hlen

theorem genOutExprIdentsTrip_extract
    {outputs : @Lambda.LTySignature Visibility} {lhs : List Expression.Ident}
    {s s' : Core.Transform.CoreTransformState}
    {outTrips : List ((Expression.Ident × Expression.Ty) × Expression.Ident)}
    (Hgen : Core.Transform.genOutExprIdentsTrip outputs lhs s = (Except.ok outTrips, s')) :
    let gen_idents := (Core.Transform.genOutExprIdents lhs s.genState).fst
    let s_gen     := (Core.Transform.genOutExprIdents lhs s.genState).snd
    (gen_idents.zip (List.map Prod.snd outputs)).zip lhs = outTrips ∧
    s' = { s with genState := s_gen } ∧
    outputs.length = lhs.length := by
  simp only [Core.Transform.genOutExprIdentsTrip] at Hgen
  split at Hgen
  case isTrue Hne =>
    simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, pure, StateT.pure] at Hgen
    cases Hgen
  case isFalse Hlen =>
    simp [bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.lift,
          ExceptT.pure, StateT.bind, StateT.pure, pure, monadLift,
          MonadLift.monadLift, liftM, Functor.map, StateT.map,
          Core.Transform.liftCoreGenM] at Hgen
    refine ⟨?_, ?_, ?_⟩
    · have := congrArg Prod.fst Hgen
      simp at this
      exact this
    · have := congrArg Prod.snd Hgen
      simp at this
      exact this.symm
    · simp at Hlen; exact Hlen

/-! ### Trip-shape geometry helpers

The Arg/Out/Old trip lemmas all share a `((g.zip ys).zip xs)` outer
shape and project either the `.unzip.snd` (= `xs`, given length
agreement) or `.unzip.fst.unzip.fst` (= `g`, ditto).  These pure list
facts are extracted once so that the trip-level lemmas can short-cut
their unzip/zip ceremony. -/

theorem zip_zip_unzip_snd_of_lengths {α β γ}
    {g : List α} {ys : List β} {xs : List γ}
    (Hgx : g.length = xs.length) (Hyx : ys.length = xs.length) :
    ((g.zip ys).zip xs).unzip.snd = xs := by
  rw [List.unzip_zip_right]
  rw [List.length_zip]
  omega

theorem zip_zip_unzip_fst_unzip_fst_of_lengths {α β γ}
    {g : List α} {ys : List β} {xs : List γ}
    (Hgx : g.length = xs.length) (Hyx : ys.length = xs.length) :
    ((g.zip ys).zip xs).unzip.fst.unzip.fst = g := by
  rw [List.unzip_zip_left (l₁ := (g.zip ys)) (l₂ := xs)]
  · rw [List.unzip_zip_left (l₁ := g) (l₂ := ys)]
    omega
  · rw [List.length_zip]
    omega

/-! ### `_snd` projection lemmas for the `gen*ExprIdentsTrip` family

These say: the `Prod.snd` projection of the trip list is exactly the
input arguments/lhs/old-vars list.  The legacy proofs went through
intricate splittings; the live forms are short reductions through the
monad layers because we have the structural form
`(gen_idents.zip inputs.unzip.2).zip args` directly visible. -/

theorem genArgExprIdentsTrip_snd
    {inputs : @Lambda.LTySignature Visibility} {args : List Expression.Expr}
    {s s' : Core.Transform.CoreTransformState}
    {argTrips : List ((Expression.Ident × Lambda.LTy) × Expression.Expr)}
    (Hgen : Core.Transform.genArgExprIdentsTrip inputs args s = (Except.ok argTrips, s')) :
    argTrips.unzip.snd = args := by
  obtain ⟨Hat, _, Hilen⟩ := genArgExprIdentsTrip_extract Hgen
  rw [← Hat]
  exact zip_zip_unzip_snd_of_lengths
          (genArgExprIdents_length' args.length s.genState)
          (by simp [List.length_map]; omega)

theorem genOutExprIdentsTrip_snd
    {outputs : @Lambda.LTySignature Visibility} {lhs : List Expression.Ident}
    {s s' : Core.Transform.CoreTransformState}
    {outTrips : List ((Expression.Ident × Expression.Ty) × Expression.Ident)}
    (Hgen : Core.Transform.genOutExprIdentsTrip outputs lhs s = (Except.ok outTrips, s')) :
    outTrips.unzip.snd = lhs := by
  obtain ⟨Hot, _, Hilen⟩ := genOutExprIdentsTrip_extract Hgen
  rw [← Hot]
  exact zip_zip_unzip_snd_of_lengths
          (genOutExprIdents_length' lhs s.genState)
          (by simp [List.length_map]; omega)

/-- The "snd" projection lemma for the `oldTripsRaw` shape used in the
    live `callElimCmd`: `oldTripsRaw = (genOldIdents.zip oldTys).zip oldVars`,
    so its `snd` projection is `oldVars` provided
    `genOldIdents.length = oldVars.length` and `oldTys.length = oldVars.length`.

    Unlike the arg/out cases, the live `callElimCmd` does not call a
    dedicated `genOldExprIdentsTrip` wrapper; instead it constructs
    `oldTripsRaw` inline.  This helper provides the equivalent
    structural fact. -/
theorem genOldExprIdentsTrip_snd
    {oldVars : List Expression.Ident}
    {oldTys : List Lambda.LTy}
    {s s' : CoreGenState}
    {genOldIdents : List Expression.Ident}
    (Hgen : Core.Transform.genOldExprIdents oldVars s = (genOldIdents, s'))
    (Htylen : oldTys.length = oldVars.length) :
    ((genOldIdents.zip oldTys).zip oldVars).unzip.snd = oldVars :=
  zip_zip_unzip_snd_of_lengths (genOldExprIdents_length Hgen) Htylen

/-! ### `*GeneratedWF` lemmas: each generator pushes its results to `generated`

`CoreGenState.gen` extends `generated` by one cons; running `mapM` of a
generator over a list extends `generated` by the produced list reversed.
The trip-wrapper variants quote these and additionally lift the
`generated` accounting through `CoreTransformState`. -/

theorem genCoreIdentGeneratedWF
    {pf : Expression.Ident} {s s' : CoreGenState} {l : Expression.Ident}
    (Hgen : CoreGenState.gen pf s = (l, s')) :
    s'.generated = l :: s.generated := by
  unfold CoreGenState.gen at Hgen
  have Hl : l = ⟨(StringGenState.gen pf.name s.cs).fst, ()⟩ := by
    have := congrArg Prod.fst Hgen
    simp at this
    exact this.symm
  have Hs : s' = { cs := (StringGenState.gen pf.name s.cs).snd,
                   generated := ⟨(StringGenState.gen pf.name s.cs).fst, ()⟩ :: s.generated } := by
    have := congrArg Prod.snd Hgen
    simp at this
    exact this.symm
  rw [Hl, Hs]

theorem genIdentGeneratedWF
    {ident : Expression.Ident} {pf : String → String}
    {s s' : CoreGenState} {l : Expression.Ident}
    (Hgen : Core.Transform.genIdent ident pf s = (l, s')) :
    s'.generated = l :: s.generated :=
  genCoreIdentGeneratedWF Hgen

theorem genArgExprIdents_GeneratedWF
    {n : Nat} {s s' : CoreGenState} {ls : List Expression.Ident}
    (Hgen : Core.Transform.genArgExprIdents n s = (ls, s')) :
    s'.generated = ls.reverse ++ s.generated :=
  genIdentMapM_GeneratedWF
    (g := fun (_ : Unit) => Core.Transform.genArgExprIdent)
    (fun H => genCoreIdentGeneratedWF H) Hgen

theorem genOutExprIdents_GeneratedWF
    {idents : List Expression.Ident} {s s' : CoreGenState}
    {ls : List Expression.Ident}
    (Hgen : Core.Transform.genOutExprIdents idents s = (ls, s')) :
    s'.generated = ls.reverse ++ s.generated :=
  genIdentMapM_GeneratedWF
    (g := Core.Transform.genOutExprIdent)
    (fun H => genCoreIdentGeneratedWF H) Hgen

theorem genOldExprIdents_GeneratedWF
    {idents : List Expression.Ident} {s s' : CoreGenState}
    {ls : List Expression.Ident}
    (Hgen : Core.Transform.genOldExprIdents idents s = (ls, s')) :
    s'.generated = ls.reverse ++ s.generated :=
  genIdentMapM_GeneratedWF
    (g := Core.Transform.genOldExprIdent)
    (fun H => genCoreIdentGeneratedWF H) Hgen

/-- Trip-level GeneratedWF for arg trips: the generated list is extended
    with `argTrips.unzip.fst.unzip.fst.reverse`. -/
theorem genArgExprIdentsTripGeneratedWF
    {inputs : @Lambda.LTySignature Visibility} {args : List Expression.Expr}
    {s s' : Core.Transform.CoreTransformState}
    {argTrips : List ((Expression.Ident × Lambda.LTy) × Expression.Expr)}
    (Hgen : Core.Transform.genArgExprIdentsTrip inputs args s = (Except.ok argTrips, s')) :
    s'.genState.generated =
        argTrips.unzip.fst.unzip.fst.reverse ++ s.genState.generated := by
  obtain ⟨Hat, Hs', Hilen⟩ := genArgExprIdentsTrip_extract Hgen
  rw [Hs']; simp only
  rw [genArgExprIdents_GeneratedWF (s := s.genState)
        (s' := (Core.Transform.genArgExprIdents args.length s.genState).snd)
        (ls := (Core.Transform.genArgExprIdents args.length s.genState).fst) rfl]
  congr 1
  rw [← Hat]
  rw [zip_zip_unzip_fst_unzip_fst_of_lengths
        (genArgExprIdents_length' args.length s.genState)
        (by simp [List.length_map]; omega)]

theorem genOutExprIdentsTripGeneratedWF
    {outputs : @Lambda.LTySignature Visibility} {lhs : List Expression.Ident}
    {s s' : Core.Transform.CoreTransformState}
    {outTrips : List ((Expression.Ident × Expression.Ty) × Expression.Ident)}
    (Hgen : Core.Transform.genOutExprIdentsTrip outputs lhs s = (Except.ok outTrips, s')) :
    s'.genState.generated =
        outTrips.unzip.fst.unzip.fst.reverse ++ s.genState.generated := by
  obtain ⟨Hot, Hs', Hilen⟩ := genOutExprIdentsTrip_extract Hgen
  rw [Hs']; simp only
  rw [genOutExprIdents_GeneratedWF (s := s.genState)
        (s' := (Core.Transform.genOutExprIdents lhs s.genState).snd)
        (ls := (Core.Transform.genOutExprIdents lhs s.genState).fst) rfl]
  congr 1
  rw [← Hot]
  rw [zip_zip_unzip_fst_unzip_fst_of_lengths
        (genOutExprIdents_length' lhs s.genState)
        (by simp [List.length_map]; omega)]

/-! ### `*WFMono` lemmas: each generator preserves `CoreGenState.WF`

These lift `CoreGenState.WFMono'` through the inductive structure of
`gen*ExprIdents` and the `CoreTransformM` wrapping of `gen*ExprIdentsTrip`. -/

theorem genArgExprIdents_WFMono
    {n : Nat} {s s' : CoreGenState} {ls : List Expression.Ident}
    (Hwf : CoreGenState.WF s) (Hgen : Core.Transform.genArgExprIdents n s = (ls, s')) :
    CoreGenState.WF s' :=
  genIdentMapM_WFMono
    (g := fun (_ : Unit) => Core.Transform.genArgExprIdent)
    (fun H1 H2 => CoreGenState.WFMono' H1 H2) Hwf Hgen

theorem genOutExprIdents_WFMono
    {idents : List Expression.Ident} {s s' : CoreGenState}
    {ls : List Expression.Ident}
    (Hwf : CoreGenState.WF s) (Hgen : Core.Transform.genOutExprIdents idents s = (ls, s')) :
    CoreGenState.WF s' :=
  genIdentMapM_WFMono
    (g := Core.Transform.genOutExprIdent)
    (fun H1 H2 => CoreGenState.WFMono' H1 H2) Hwf Hgen

theorem genOldExprIdents_WFMono
    {idents : List Expression.Ident} {s s' : CoreGenState}
    {ls : List Expression.Ident}
    (Hwf : CoreGenState.WF s) (Hgen : Core.Transform.genOldExprIdents idents s = (ls, s')) :
    CoreGenState.WF s' :=
  genIdentMapM_WFMono
    (g := Core.Transform.genOldExprIdent)
    (fun H1 H2 => CoreGenState.WFMono' H1 H2) Hwf Hgen

/-- Trip-level WFMono for arg trips. -/
theorem genArgExprIdentsTripWFMono
    {inputs : @Lambda.LTySignature Visibility} {args : List Expression.Expr}
    {s s' : Core.Transform.CoreTransformState}
    {argTrips : List ((Expression.Ident × Lambda.LTy) × Expression.Expr)}
    (Hwf : CoreGenState.WF s.genState)
    (Hgen : Core.Transform.genArgExprIdentsTrip inputs args s = (Except.ok argTrips, s')) :
    CoreGenState.WF s'.genState := by
  obtain ⟨_, Hs', _⟩ := genArgExprIdentsTrip_extract Hgen
  rw [Hs']; simp only
  exact genArgExprIdents_WFMono (s := s.genState)
          (s' := (Core.Transform.genArgExprIdents args.length s.genState).snd)
          (ls := (Core.Transform.genArgExprIdents args.length s.genState).fst) Hwf rfl

/-- Trip-level WFMono for out trips. -/
theorem genOutExprIdentsTripWFMono
    {outputs : @Lambda.LTySignature Visibility} {lhs : List Expression.Ident}
    {s s' : Core.Transform.CoreTransformState}
    {outTrips : List ((Expression.Ident × Expression.Ty) × Expression.Ident)}
    (Hwf : CoreGenState.WF s.genState)
    (Hgen : Core.Transform.genOutExprIdentsTrip outputs lhs s = (Except.ok outTrips, s')) :
    CoreGenState.WF s'.genState := by
  obtain ⟨_, Hs', _⟩ := genOutExprIdentsTrip_extract Hgen
  rw [Hs']; simp only
  exact genOutExprIdents_WFMono (s := s.genState)
          (s' := (Core.Transform.genOutExprIdents lhs s.genState).snd)
          (ls := (Core.Transform.genOutExprIdents lhs s.genState).fst) Hwf rfl

/-- Bare WFMono for old vars (live `callElimCmd` builds `oldTripsRaw` inline). -/
theorem genOldExprIdentsTripWFMono
    {oldVars : List Expression.Ident}
    {s s' : CoreGenState} {genOldIdents : List Expression.Ident}
    (Hwf : CoreGenState.WF s)
    (Hgen : Core.Transform.genOldExprIdents oldVars s = (genOldIdents, s')) :
    CoreGenState.WF s' :=
  genOldExprIdents_WFMono Hwf Hgen

/-- Trip-level GeneratedWF for old trips, parameterized over the bare
    `genOldExprIdents` (since the live `callElimCmd` constructs its
    `oldTripsRaw` inline rather than through a wrapper). -/
theorem genOldExprIdentsTripGeneratedWF
    {oldVars : List Expression.Ident} {oldTys : List Lambda.LTy}
    {s s' : CoreGenState} {genOldIdents : List Expression.Ident}
    (Hgen : Core.Transform.genOldExprIdents oldVars s = (genOldIdents, s'))
    (Htylen : oldTys.length = oldVars.length) :
    s'.generated =
        ((genOldIdents.zip oldTys).zip oldVars).unzip.fst.unzip.fst.reverse ++ s.generated := by
  rw [genOldExprIdents_GeneratedWF Hgen]
  rw [zip_zip_unzip_fst_unzip_fst_of_lengths
        (genOldExprIdents_length Hgen) Htylen]

end Core

end -- public section
