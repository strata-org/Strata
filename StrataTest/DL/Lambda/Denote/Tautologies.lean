/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteProps
import all Strata.DL.Lambda.IntBoolFactory

/-!
## Tautologies in the Lambda Denotational Semantics

Basic propositional and first-order tautologies expressed as `Valid` statements
over `IntBoolFactory`. Each formula is a closed, well-typed `LExpr` of type
`bool`, and validity means it denotes `true` under every consistent
interpretation, type-variable valuation, and free-variable valuation.

Because HashMaps do not reduce well in the kernel, this file uses
`native_decide` for simplifying the `Factory` `concreteEval`.
-/

namespace Lambda

/-! ## Section 1: InterpConsistentEvalReduce

`InterpConsistentEval` (from `LExprDenote.lean`) uses `LMonoTy.subst` which has a
well-founded recursion guard that prevents definitional reduction. We restate it
using `LMonoTy.substReduce` (structural recursion, no guard) so that ground-type
instantiations reduce in the kernel. The conversion theorem bridges the two via
`subst_eq_substReduce`, `denote_cast_ty`, `denoteArgs_cast_ty`, and `applyArgs_cast_ty`.
-/

private def LFunc.InterpConsistentEvalReduce
    {T : LExprParams}
    (tcInterp : TyConstrInterp) (opInterp : OpInterp tcInterp)
    (f : LFunc T) (ceval : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono)) : Prop :=
  ∀ (vt : TyVarVal) (fvarVal : FreeVarVal T tcInterp)
    (md : T.Metadata) (tySubst : Subst)
    (argExprs : List (LExpr T.mono)) (resultExpr : LExpr T.mono),
  ceval md argExprs = some resultExpr →
  let instInputTys := (List.map Prod.snd f.inputs).map (LMonoTy.substReduce tySubst)
  let instOutputTy := LMonoTy.substReduce tySubst f.output
  let inputSorts := instInputTys.map (LMonoTy.substTyVars vt)
  let outputSort := LMonoTy.substTyVars vt instOutputTy
  let fullSort := LSort.mkArrow outputSort inputSorts
  ∀ (h_args : List.Forall₂ (LExpr.HasTypeA []) argExprs instInputTys)
    (h_result : LExpr.HasTypeA [] resultExpr instOutputTy),
  LExpr.denote tcInterp opInterp fvarVal vt .nil resultExpr instOutputTy h_result =
    SortDenote.applyArgs tcInterp (opInterp f.name.name fullSort)
      (denoteArgs tcInterp opInterp fvarVal vt .nil argExprs instInputTys h_args)

/--
Equivalence of InterpConsistentEval (for proofs) and InterpConsistentEvalReduce
(reduces in kernel). This involves messy dependent types and typecasts, but must
only be done once: now ground types will automatically reduce in proofs
-/
private theorem InterpConsistentEval_to_Simple
    {T : LExprParams} [DecidableEq T.IDMeta]
    (tcInterp : TyConstrInterp) (opInterp : OpInterp tcInterp)
    (f : LFunc T) (ceval : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono))
    (h : LFunc.InterpConsistentEval tcInterp opInterp f ceval)
    : LFunc.InterpConsistentEvalReduce tcInterp opInterp f ceval := by
  unfold Lambda.LFunc.InterpConsistentEval at h
  unfold LFunc.InterpConsistentEvalReduce
  intros vt fvarVal md tySubst argExprs resultExprs hceval instInputTys
    instOutputTy inputSorts outputSorts fullSort
  subst instOutputTy
  intros h_args
  have heq:= LMonoTy.subst_eq_substReduce tySubst f.output
  intros h_result
  have hty2 : LExpr.HasTypeA [] resultExprs (LMonoTy.subst tySubst f.output) := by rw [heq]; assumption
  rw[denote_cast_ty (h_eq:=heq.symm) (h₂:=hty2)]
  have heq2 : instInputTys = List.map (LMonoTy.subst tySubst) (List.map Prod.snd f.inputs) := by
    subst instInputTys
    induction (List.map Prod.snd f.inputs)
    . simp
    . rw[List.map_cons, List.map_cons]
      congr 1
      rw [LMonoTy.subst_eq_substReduce]
  have hty3 : List.Forall₂ (LExpr.HasTypeA []) argExprs (List.map (LMonoTy.subst tySubst) (List.map Prod.snd f.inputs)) := by
    rw[←heq2]; assumption
  rw[denoteArgs_cast_ty (h_eq:=heq2) (h₂:=hty3)]
  specialize (h vt fvarVal md tySubst argExprs resultExprs hceval hty3 hty2)
  rw[h]
  rw[applyArgs_cast_ty (h_args :=heq2.symm) (h_ret:=heq)]
  grind

private abbrev TP : LExprParams := ⟨Unit, Unit⟩
private abbrev F : @Factory TP := @IntBoolFactory TP ⟨()⟩ ⟨()⟩

private abbrev m : TP.Metadata := ()
private abbrev boolTy : LMonoTy := .bool
private abbrev intTy : LMonoTy := .int

-- Dummy trigger (required by quant constructor but unused semantically)
private abbrev trg : LExpr TP.mono := .const m (.boolConst true)

-- Operator type annotations
private abbrev boolBinTy : LMonoTy := .arrow boolTy (.arrow boolTy boolTy)
private abbrev boolUnTy : LMonoTy := .arrow boolTy boolTy

-- Operator nodes
private abbrev andOp : LExpr TP.mono := .op m ⟨"Bool.And", ()⟩ (some boolBinTy)
private abbrev orOp : LExpr TP.mono := .op m ⟨"Bool.Or", ()⟩ (some boolBinTy)
private abbrev implOp : LExpr TP.mono := .op m ⟨"Bool.Implies", ()⟩ (some boolBinTy)
private abbrev notOp : LExpr TP.mono := .op m ⟨"Bool.Not", ()⟩ (some boolUnTy)

-- Smart constructors for applying operators
private abbrev mkAnd (a b : LExpr TP.mono) : LExpr TP.mono :=
  .app m (.app m andOp a) b
private abbrev mkOr (a b : LExpr TP.mono) : LExpr TP.mono :=
  .app m (.app m orOp a) b
private abbrev mkImpl (a b : LExpr TP.mono) : LExpr TP.mono :=
  .app m (.app m implOp a) b
private abbrev mkNot (a : LExpr TP.mono) : LExpr TP.mono :=
  .app m notOp a

-- Bound variable shorthands (de Bruijn)
private abbrev bv0 : LExpr TP.mono := .bvar m 0
private abbrev bv1 : LExpr TP.mono := .bvar m 1

-- Typing helpers for operators
private abbrev andOp_ty : LExpr.HasTypeA Δ andOp boolBinTy := .op
private abbrev orOp_ty : LExpr.HasTypeA Δ orOp boolBinTy := .op
private abbrev implOp_ty : LExpr.HasTypeA Δ implOp boolBinTy := .op
private abbrev notOp_ty : LExpr.HasTypeA Δ notOp boolUnTy := .op

private abbrev mkAnd_ty (ha : LExpr.HasTypeA Δ a boolTy) (hb : LExpr.HasTypeA Δ b boolTy) :
    LExpr.HasTypeA Δ (mkAnd a b) boolTy :=
  .app (.app andOp_ty ha) hb

private abbrev mkOr_ty (ha : LExpr.HasTypeA Δ a boolTy) (hb : LExpr.HasTypeA Δ b boolTy) :
    LExpr.HasTypeA Δ (mkOr a b) boolTy :=
  .app (.app orOp_ty ha) hb

private abbrev mkImpl_ty (ha : LExpr.HasTypeA Δ a boolTy) (hb : LExpr.HasTypeA Δ b boolTy) :
    LExpr.HasTypeA Δ (mkImpl a b) boolTy :=
  .app (.app implOp_ty ha) hb

private abbrev mkNot_ty (ha : LExpr.HasTypeA Δ a boolTy) :
    LExpr.HasTypeA Δ (mkNot a) boolTy :=
  .app notOp_ty ha

/-! ### 1. True is valid -/

private def trueExpr : LExpr TP.mono := .const m (.boolConst true)
private def trueExpr_ty : LExpr.HasTypeA [] trueExpr boolTy := .const

theorem valid_true : Valid F trueExpr trueExpr_ty := by
  intro I vt fvarVal
  simp only [trueExpr]
  unfold LMonoTy.bool
  rw [denote_boolConst]

/-! ### 2. Equality is reflexive (bool): ∀ p : bool, p = p -/

private def eq_refl_bool : LExpr TP.mono :=
  .quant m .all "p" (some boolTy) trg (.eq m bv0 bv0)

private def eq_refl_bool_ty : LExpr.HasTypeA [] eq_refl_bool boolTy :=
  .quant .const (.eq (.bvar (by rfl)) (.bvar (by rfl)))

theorem valid_eq_refl_bool : Valid F eq_refl_bool eq_refl_bool_ty := by
  intro I vt fvarVal
  simp only [eq_refl_bool, boolTy]
  unfold LMonoTy.bool
  have h_body : LExpr.HasTypeA [.tcons "bool" []] (LExpr.eq m bv0 bv0) (.tcons "bool" []) :=
    .eq (.bvar (by rfl)) (.bvar (by rfl))
  apply denote_quant_all_true .nil h_body
  intro x
  apply denote_eq_true (.cons x .nil) (.bvar (by rfl)) (.bvar (by rfl))
  rfl

/-! ### 3. Equality is reflexive (polymorphic): ∀ T, ∀ x : T, x = x -/

private def eq_refl_poly : LExpr TP.mono :=
  .quant m .all "x" (some (.ftvar "T")) trg (.eq m bv0 bv0)

private def eq_refl_poly_ty : LExpr.HasTypeA [] eq_refl_poly boolTy :=
  .quant .const (.eq (.bvar (by rfl)) (.bvar (by rfl)))

theorem valid_eq_refl_poly : Valid F eq_refl_poly eq_refl_poly_ty := by
  intro I vt fvarVal
  simp only [eq_refl_poly]
  unfold LMonoTy.bool
  have h_body : LExpr.HasTypeA [.ftvar "T"] (LExpr.eq m bv0 bv0) (.tcons "bool" []) :=
    .eq (.bvar (by rfl)) (.bvar (by rfl))
  apply denote_quant_all_true .nil h_body
  intro x
  apply denote_eq_true (.cons x .nil) (.bvar (by rfl)) (.bvar (by rfl))
  rfl

/-! ## Section 2: Operator Interpretation Lemmas

Each factory operator (Bool.And, Bool.Or, Bool.Implies, Bool.Not) is shown to
interpret as its Lean counterpart in any consistent interpretation. The proof
strategy is:

1. Extract `ceval` from `concreteEval` via `native_decide` membership/isSome proofs
2. Convert `InterpConsistentEval` to `InterpConsistentEvalReduce` (Section 1)
3. Rewrite factory fields (name, inputs, output) using `native_decide` lemmas
4. Instantiate with concrete boolean constant expressions
5. Since `substReduce` reduces definitionally on ground types, typing proofs (`.const`) work directly
6. Use `change` to normalize the goal (substReduce is defeq but not syntactically reduced)
-/

private abbrev boolBinSort : LSort :=
  .tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]]

private abbrev boolUnSort : LSort :=
  .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]

private theorem bool_and_mem : "Bool.And" ∈ F := by native_decide
private theorem bool_and_has_ceval : (F["Bool.And"]'bool_and_mem).concreteEval.isSome = true := by native_decide
private theorem bool_and_name : (F["Bool.And"]'bool_and_mem).name.name = "Bool.And" := by native_decide
private theorem bool_and_output : (F["Bool.And"]'bool_and_mem).output = .bool := by native_decide
private theorem bool_and_input_tys : List.map Prod.snd (F["Bool.And"]'bool_and_mem).inputs = [.bool, .bool] := by native_decide

private theorem bool_and_interp (I : Interp F) :
    I.opInterp "Bool.And" boolBinSort
    = fun (p : Bool) (q : Bool) => Bool.and p q := by
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp bool_and_has_ceval
  have h_ic := InterpConsistentEval_to_Simple I.tcInterp I.opInterp _ ceval
    (I.interpConsistent.2 "Bool.And" bool_and_mem ceval h_ceval_eq)
  -- Unfold and simplify factory fields
  unfold LFunc.InterpConsistentEvalReduce at h_ic
  rw [bool_and_input_tys, bool_and_output, bool_and_name] at h_ic
  -- Now h_ic uses substReduce which reduces definitionally on ground types
  funext p q
  have h_eval : ceval () [.boolConst () p, .boolConst () q]
      = some (.boolConst () (p && q)) := by
    have h_concrete :
        ∀ (b1 b2 : Bool),
          (F["Bool.And"]'bool_and_mem).concreteEval.bind
            (fun f => f () [.boolConst () b1, .boolConst () b2])
          = some (.boolConst () (b1 && b2)) := by
      intro b1 b2; cases b1 <;> cases b2 <;> native_decide
    have h_inst_concrete := h_concrete p q
    rw [h_ceval_eq] at h_inst_concrete
    simpa using h_inst_concrete
  have h_vt : TyVarVal := fun _ => .tcons "bool" []
  have h_fv : FreeVarVal TP I.tcInterp := fun _ s =>
    @default _ (@SortDenote.instInhabited I.tcInterp I.allInhabited s)
  have h_inst := h_ic h_vt h_fv () Subst.empty
      [.boolConst () p, .boolConst () q]
      (.boolConst () (p && q))
      h_eval
  -- substReduce reduces definitionally on ground types. Provide typing proofs.
  have h_args : List.Forall₂ (LExpr.HasTypeA (T := TP) [])
      [.boolConst () p, .boolConst () q]
      [.tcons "bool" [], .tcons "bool" []] :=
    .cons .const (.cons .const .nil)
  have h_result : LExpr.HasTypeA (T := TP) [] (.boolConst () (p && q)) (.tcons "bool" []) := .const
  have h_eq := h_inst h_args h_result
  -- substReduce reduces definitionally but Lean displays it unreduced.
  -- Use change to normalize the type in h_eq.
  change (p && q) = I.opInterp "Bool.And" boolBinSort p q at h_eq
  exact h_eq.symm

private theorem bool_implies_mem : "Bool.Implies" ∈ F := by native_decide
private theorem bool_implies_has_ceval : (F["Bool.Implies"]'bool_implies_mem).concreteEval.isSome = true := by native_decide
private theorem bool_implies_name : (F["Bool.Implies"]'bool_implies_mem).name.name = "Bool.Implies" := by native_decide
private theorem bool_implies_output : (F["Bool.Implies"]'bool_implies_mem).output = .bool := by native_decide
private theorem bool_implies_input_tys : List.map Prod.snd (F["Bool.Implies"]'bool_implies_mem).inputs = [.bool, .bool] := by native_decide

private theorem bool_implies_interp (I : Interp F) :
    I.opInterp "Bool.Implies" boolBinSort
    = fun (p : Bool) (q : Bool) => (!p || q) := by
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp bool_implies_has_ceval
  have h_ic := InterpConsistentEval_to_Simple I.tcInterp I.opInterp _ ceval
    (I.interpConsistent.2 "Bool.Implies" bool_implies_mem ceval h_ceval_eq)
  unfold LFunc.InterpConsistentEvalReduce at h_ic
  rw [bool_implies_input_tys, bool_implies_output, bool_implies_name] at h_ic
  funext p q
  have h_eval : ceval () [.boolConst () p, .boolConst () q]
      = some (.boolConst () (!p || q)) := by
    have h_concrete :
        ∀ (b1 b2 : Bool),
          (F["Bool.Implies"]'bool_implies_mem).concreteEval.bind
            (fun f => f () [.boolConst () b1, .boolConst () b2])
          = some (.boolConst () (!b1 || b2)) := by
      intro b1 b2; cases b1 <;> cases b2 <;> native_decide
    have h_inst_concrete := h_concrete p q
    rw [h_ceval_eq] at h_inst_concrete
    simpa using h_inst_concrete
  have h_vt : TyVarVal := fun _ => .tcons "bool" []
  have h_fv : FreeVarVal TP I.tcInterp := fun _ s =>
    @default _ (@SortDenote.instInhabited I.tcInterp I.allInhabited s)
  have h_inst := h_ic h_vt h_fv () Subst.empty
      [.boolConst () p, .boolConst () q]
      (.boolConst () (!p || q))
      h_eval
  have h_args : List.Forall₂ (LExpr.HasTypeA (T := TP) [])
      [.boolConst () p, .boolConst () q]
      [.tcons "bool" [], .tcons "bool" []] :=
    .cons .const (.cons .const .nil)
  have h_result : LExpr.HasTypeA (T := TP) [] (.boolConst () (!p || q)) (.tcons "bool" []) := .const
  have h_eq := h_inst h_args h_result
  change (!p || q) = I.opInterp "Bool.Implies" boolBinSort p q at h_eq
  exact h_eq.symm

private theorem bool_or_mem : "Bool.Or" ∈ F := by native_decide
private theorem bool_or_has_ceval : (F["Bool.Or"]'bool_or_mem).concreteEval.isSome = true := by native_decide
private theorem bool_or_name : (F["Bool.Or"]'bool_or_mem).name.name = "Bool.Or" := by native_decide
private theorem bool_or_output : (F["Bool.Or"]'bool_or_mem).output = .bool := by native_decide
private theorem bool_or_input_tys : List.map Prod.snd (F["Bool.Or"]'bool_or_mem).inputs = [.bool, .bool] := by native_decide

private theorem bool_or_interp (I : Interp F) :
    I.opInterp "Bool.Or" boolBinSort
    = fun (p : Bool) (q : Bool) => Bool.or p q := by
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp bool_or_has_ceval
  have h_ic := InterpConsistentEval_to_Simple I.tcInterp I.opInterp _ ceval
    (I.interpConsistent.2 "Bool.Or" bool_or_mem ceval h_ceval_eq)
  unfold LFunc.InterpConsistentEvalReduce at h_ic
  rw [bool_or_input_tys, bool_or_output, bool_or_name] at h_ic
  funext p q
  have h_eval : ceval () [.boolConst () p, .boolConst () q]
      = some (.boolConst () (p || q)) := by
    have h_concrete :
        ∀ (b1 b2 : Bool),
          (F["Bool.Or"]'bool_or_mem).concreteEval.bind
            (fun f => f () [.boolConst () b1, .boolConst () b2])
          = some (.boolConst () (b1 || b2)) := by
      intro b1 b2; cases b1 <;> cases b2 <;> native_decide
    have h_inst_concrete := h_concrete p q
    rw [h_ceval_eq] at h_inst_concrete
    simpa using h_inst_concrete
  have h_vt : TyVarVal := fun _ => .tcons "bool" []
  have h_fv : FreeVarVal TP I.tcInterp := fun _ s =>
    @default _ (@SortDenote.instInhabited I.tcInterp I.allInhabited s)
  have h_inst := h_ic h_vt h_fv () Subst.empty
      [.boolConst () p, .boolConst () q]
      (.boolConst () (p || q))
      h_eval
  have h_args : List.Forall₂ (LExpr.HasTypeA (T := TP) [])
      [.boolConst () p, .boolConst () q]
      [.tcons "bool" [], .tcons "bool" []] :=
    .cons .const (.cons .const .nil)
  have h_result : LExpr.HasTypeA (T := TP) [] (.boolConst () (p || q)) (.tcons "bool" []) := .const
  have h_eq := h_inst h_args h_result
  change (p || q) = I.opInterp "Bool.Or" boolBinSort p q at h_eq
  exact h_eq.symm

private theorem bool_not_mem : "Bool.Not" ∈ F := by native_decide
private theorem bool_not_has_ceval : (F["Bool.Not"]'bool_not_mem).concreteEval.isSome = true := by native_decide
private theorem bool_not_name : (F["Bool.Not"]'bool_not_mem).name.name = "Bool.Not" := by native_decide
private theorem bool_not_output : (F["Bool.Not"]'bool_not_mem).output = .bool := by native_decide
private theorem bool_not_input_tys : List.map Prod.snd (F["Bool.Not"]'bool_not_mem).inputs = [.bool] := by native_decide

private theorem bool_not_interp (I : Interp F) :
    I.opInterp "Bool.Not" boolUnSort
    = fun (p : Bool) => Bool.not p := by
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp bool_not_has_ceval
  have h_ic := InterpConsistentEval_to_Simple I.tcInterp I.opInterp _ ceval
    (I.interpConsistent.2 "Bool.Not" bool_not_mem ceval h_ceval_eq)
  unfold LFunc.InterpConsistentEvalReduce at h_ic
  rw [bool_not_input_tys, bool_not_output, bool_not_name] at h_ic
  funext p
  have h_eval : ceval () [.boolConst () p]
      = some (.boolConst () (!p)) := by
    have h_concrete :
        ∀ (b : Bool),
          (F["Bool.Not"]'bool_not_mem).concreteEval.bind
            (fun f => f () [.boolConst () b])
          = some (.boolConst () (!b)) := by
      intro b; cases b <;> native_decide
    have h_inst_concrete := h_concrete p
    rw [h_ceval_eq] at h_inst_concrete
    simpa using h_inst_concrete
  have h_vt : TyVarVal := fun _ => .tcons "bool" []
  have h_fv : FreeVarVal TP I.tcInterp := fun _ s =>
    @default _ (@SortDenote.instInhabited I.tcInterp I.allInhabited s)
  have h_inst := h_ic h_vt h_fv () Subst.empty
      [.boolConst () p]
      (.boolConst () (!p))
      h_eval
  have h_args : List.Forall₂ (LExpr.HasTypeA (T := TP) [])
      [.boolConst () p]
      [.tcons "bool" []] :=
    .cons .const .nil
  have h_result : LExpr.HasTypeA (T := TP) [] (.boolConst () (!p)) (.tcons "bool" []) := .const
  have h_eq := h_inst h_args h_result
  change (!p) = I.opInterp "Bool.Not" boolUnSort p at h_eq
  exact h_eq.symm

/-! ## Section 3: Tautologies

Each tautology is proved `Valid` by: peeling quantifiers with `denote_quant_all_true`,
using `change` to fix the goal to the concrete expression, repeatedly applying
denote unfolding lemmas (`denote_app`, `denote_op`, `denote_bvar`, `denote_eq_true`),
rewriting with operator interp lemmas (Section 2), then using typing inversion
lemmas (`op_inv`, `bvar_inv`) to simplify casts and conclude.

TODO: this should be automated
-/

/-! ### 4. p ∧ q → p (and-elimination left): ∀ p q, (p ∧ q) → p -/

private def and_elim_left : LExpr TP.mono :=
  .quant m .all "p" (some boolTy) trg
    (.quant m .all "q" (some boolTy) trg
      (mkImpl (mkAnd bv1 bv0) bv1))

private def and_elim_left_ty : LExpr.HasTypeA [] and_elim_left boolTy :=
  .quant .const
    (.quant .const
      (mkImpl_ty (mkAnd_ty (.bvar (by rfl)) (.bvar (by rfl))) (.bvar (by rfl))))

theorem valid_and_elim_left : Valid F and_elim_left and_elim_left_ty := by
  intro I vt fvarVal
  simp only [and_elim_left, boolTy]
  unfold LMonoTy.bool
  have h_inner : LExpr.HasTypeA [.tcons "bool" [], .tcons "bool" []]
      (mkImpl (mkAnd bv1 bv0) bv1) (.tcons "bool" []) :=
    mkImpl_ty (mkAnd_ty (.bvar (by rfl)) (.bvar (by rfl))) (.bvar (by rfl))
  have h_q : LExpr.HasTypeA [.tcons "bool" []]
      (.quant m .all "q" (some (.tcons "bool" [])) trg (mkImpl (mkAnd bv1 bv0) bv1))
      (.tcons "bool" []) :=
    .quant .const h_inner
  apply denote_quant_all_true .nil h_q
  intro p
  apply denote_quant_all_true (.cons p .nil) h_inner
  intro q
  -- Unfold abbreviations in the goal
  change LExpr.denote I.tcInterp I.opInterp fvarVal vt (.cons q (.cons p .nil))
    (mkImpl (mkAnd bv1 bv0) bv1) (.tcons "bool" []) h_inner = true
  simp only [mkImpl, mkAnd, andOp, implOp, boolBinTy, bv0, bv1, m]
  -- Peel outer app (impl _ bv1)
  have ⟨_, h_fn1, h_arg1⟩ := HasTypeA.app_inv h_inner
  rw [denote_app (.cons q (.cons p .nil)) h_fn1 h_arg1]
  -- Peel inner app (app implOp (and p q))
  have ⟨_, h_fn2, h_arg2⟩ := HasTypeA.app_inv h_fn1
  rw [denote_app (.cons q (.cons p .nil)) h_fn2 h_arg2]
  -- Peel outer app of and (app (app andOp bv1) bv0)
  have ⟨_, h_fn3, h_arg3⟩ := HasTypeA.app_inv h_arg2
  rw [denote_app (.cons q (.cons p .nil)) h_fn3 h_arg3]
  -- Peel inner app of and (app andOp bv1)
  have ⟨_, h_fn4, h_arg4⟩ := HasTypeA.app_inv h_fn3
  rw [denote_app (.cons q (.cons p .nil)) h_fn4 h_arg4]
  -- Now rewrite ops and bvars
  rw [denote_op, denote_op, denote_bvar, denote_bvar, denote_bvar]
  -- Simplify HList.get, substTyVars, and casts
  simp only [HList.get, LMonoTy.substTyVars, LMonoTy.substTyVars.map, LMonoTy.arrow]
  -- Use interp lemmas
  rw[bool_and_interp, bool_implies_interp]
  -- Collapse ⋯ ▸ casts (all between definitionally equal Bool types)
  -- and close by case split on p
  have h_op2 := HasTypeA.op_inv h_fn2
  have h_op4 := HasTypeA.op_inv h_fn4
  have h_bv1 := HasTypeA.bvar_inv h_arg1
  have h_bv3 := HasTypeA.bvar_inv h_arg3
  have h_bv4 := HasTypeA.bvar_inv h_arg4
  simp at h_bv1 h_bv3 h_bv4; subst h_bv1 h_bv3 h_bv4
  simp [boolBinTy, boolTy, LMonoTy.arrow, LMonoTy.bool] at h_op2 h_op4
  subst_vars
  cases p <;> simp

/-! ### 5. p → p ∨ q (or-introduction left): ∀ p q, p → (p ∨ q) -/

private def or_intro_left : LExpr TP.mono :=
  .quant m .all "p" (some boolTy) trg
    (.quant m .all "q" (some boolTy) trg
      (mkImpl bv1 (mkOr bv1 bv0)))

private def or_intro_left_ty : LExpr.HasTypeA [] or_intro_left boolTy :=
  .quant .const
    (.quant .const
      (mkImpl_ty (.bvar (by rfl)) (mkOr_ty (.bvar (by rfl)) (.bvar (by rfl)))))

theorem valid_or_intro_left : Valid F or_intro_left or_intro_left_ty := by
  intro I vt fvarVal
  simp only [or_intro_left, boolTy]
  unfold LMonoTy.bool
  have h_inner : LExpr.HasTypeA [.tcons "bool" [], .tcons "bool" []]
      (mkImpl bv1 (mkOr bv1 bv0)) (.tcons "bool" []) :=
    mkImpl_ty (.bvar (by rfl)) (mkOr_ty (.bvar (by rfl)) (.bvar (by rfl)))
  have h_q : LExpr.HasTypeA [.tcons "bool" []]
      (.quant m .all "q" (some (.tcons "bool" [])) trg (mkImpl bv1 (mkOr bv1 bv0)))
      (.tcons "bool" []) :=
    .quant .const h_inner
  apply denote_quant_all_true .nil h_q
  intro p
  apply denote_quant_all_true (.cons p .nil) h_inner
  intro q
  change LExpr.denote I.tcInterp I.opInterp fvarVal vt (.cons q (.cons p .nil))
    (mkImpl bv1 (mkOr bv1 bv0)) (.tcons "bool" []) h_inner = true
  simp only [mkImpl, mkOr, orOp, implOp, boolBinTy, bv0, bv1, m]
  -- Peel apps: impl(bv1, or(bv1, bv0))
  have ⟨_, h_fn1, h_arg1⟩ := HasTypeA.app_inv h_inner
  rw [denote_app (.cons q (.cons p .nil)) h_fn1 h_arg1]
  have ⟨_, h_fn2, h_arg2⟩ := HasTypeA.app_inv h_fn1
  rw [denote_app (.cons q (.cons p .nil)) h_fn2 h_arg2]
  -- Peel or(bv1, bv0)
  have ⟨_, h_fn3, h_arg3⟩ := HasTypeA.app_inv h_arg1
  rw [denote_app (.cons q (.cons p .nil)) h_fn3 h_arg3]
  have ⟨_, h_fn4, h_arg4⟩ := HasTypeA.app_inv h_fn3
  rw [denote_app (.cons q (.cons p .nil)) h_fn4 h_arg4]
  rw [denote_op, denote_op, denote_bvar, denote_bvar, denote_bvar]
  simp only [HList.get, LMonoTy.substTyVars, LMonoTy.substTyVars.map, LMonoTy.arrow]
  rw [bool_implies_interp, bool_or_interp]
  have h_op2 := HasTypeA.op_inv h_fn2
  have h_op4 := HasTypeA.op_inv h_fn4
  have h_bv1 := HasTypeA.bvar_inv h_arg2
  have h_bv3 := HasTypeA.bvar_inv h_arg3  -- this is bv0 in or
  have h_bv4 := HasTypeA.bvar_inv h_arg4
  simp at h_bv1 h_bv3 h_bv4; subst h_bv1 h_bv3 h_bv4
  simp [boolBinTy, boolTy, LMonoTy.arrow, LMonoTy.bool] at h_op2 h_op4
  subst_vars
  cases p <;> simp

/-! ### 6. Excluded middle: ∀ p, p ∨ ¬p -/

private def excluded_middle : LExpr TP.mono :=
  .quant m .all "p" (some boolTy) trg
    (mkOr bv0 (mkNot bv0))

private def excluded_middle_ty : LExpr.HasTypeA [] excluded_middle boolTy :=
  .quant .const
    (mkOr_ty (.bvar (by rfl)) (mkNot_ty (.bvar (by rfl))))

theorem valid_excluded_middle : Valid F excluded_middle excluded_middle_ty := by
  intro I vt fvarVal
  simp only [excluded_middle, boolTy]
  unfold LMonoTy.bool
  have h_inner : LExpr.HasTypeA [.tcons "bool" []]
      (mkOr bv0 (mkNot bv0)) (.tcons "bool" []) :=
    mkOr_ty (.bvar (by rfl)) (mkNot_ty (.bvar (by rfl)))
  apply denote_quant_all_true .nil h_inner
  intro p
  change LExpr.denote I.tcInterp I.opInterp fvarVal vt (.cons p .nil)
    (mkOr bv0 (mkNot bv0)) (.tcons "bool" []) h_inner = true
  simp only [mkOr, mkNot, orOp, notOp, boolBinTy, boolUnTy, bv0, m]
  -- Peel or(bv0, not(bv0))
  have ⟨_, h_fn1, h_arg1⟩ := HasTypeA.app_inv h_inner
  rw [denote_app (.cons p .nil) h_fn1 h_arg1]
  have ⟨_, h_fn2, h_arg2⟩ := HasTypeA.app_inv h_fn1
  rw [denote_app (.cons p .nil) h_fn2 h_arg2]
  -- Peel not(bv0)
  have ⟨_, h_fn3, h_arg3⟩ := HasTypeA.app_inv h_arg1
  rw [denote_app (.cons p .nil) h_fn3 h_arg3]
  rw [denote_op, denote_op, denote_bvar, denote_bvar]
  simp only [HList.get, LMonoTy.substTyVars, LMonoTy.substTyVars.map, LMonoTy.arrow]
  rw [bool_or_interp, bool_not_interp]
  have h_op2 := HasTypeA.op_inv h_fn2
  have h_op3 := HasTypeA.op_inv h_fn3
  have h_bv2 := HasTypeA.bvar_inv h_arg2
  have h_bv3 := HasTypeA.bvar_inv h_arg3
  simp at h_bv2 h_bv3; subst h_bv2 h_bv3
  simp [boolBinTy, boolUnTy, boolTy, LMonoTy.arrow, LMonoTy.bool] at h_op2 h_op3
  subst_vars
  cases p <;> simp

/-! ### 7. Modus ponens: ∀ p q, p → (p → q) → q -/

private def modus_ponens : LExpr TP.mono :=
  .quant m .all "p" (some boolTy) trg
    (.quant m .all "q" (some boolTy) trg
      (mkImpl bv1 (mkImpl (mkImpl bv1 bv0) bv0)))

private def modus_ponens_ty : LExpr.HasTypeA [] modus_ponens boolTy :=
  .quant .const
    (.quant .const
      (mkImpl_ty (.bvar (by rfl))
        (mkImpl_ty (mkImpl_ty (.bvar (by rfl)) (.bvar (by rfl))) (.bvar (by rfl)))))

theorem valid_modus_ponens : Valid F modus_ponens modus_ponens_ty := by
  intro I vt fvarVal
  simp only [modus_ponens, boolTy]
  unfold LMonoTy.bool
  have h_inner : LExpr.HasTypeA [.tcons "bool" [], .tcons "bool" []]
      (mkImpl bv1 (mkImpl (mkImpl bv1 bv0) bv0)) (.tcons "bool" []) :=
    mkImpl_ty (.bvar (by rfl))
      (mkImpl_ty (mkImpl_ty (.bvar (by rfl)) (.bvar (by rfl))) (.bvar (by rfl)))
  have h_q : LExpr.HasTypeA [.tcons "bool" []]
      (.quant m .all "q" (some (.tcons "bool" [])) trg
        (mkImpl bv1 (mkImpl (mkImpl bv1 bv0) bv0))) (.tcons "bool" []) :=
    .quant .const h_inner
  apply denote_quant_all_true .nil h_q
  intro p
  apply denote_quant_all_true (.cons p .nil) h_inner
  intro q
  change LExpr.denote I.tcInterp I.opInterp fvarVal vt (.cons q (.cons p .nil))
    (mkImpl bv1 (mkImpl (mkImpl bv1 bv0) bv0)) (.tcons "bool" []) h_inner = true
  simp only [mkImpl, implOp, boolBinTy, bv0, bv1, m]
  -- Peel all 6 apps (3 impl applications, each is 2 apps)
  have ⟨_, h_fn1, h_arg1⟩ := HasTypeA.app_inv h_inner
  rw [denote_app (.cons q (.cons p .nil)) h_fn1 h_arg1]
  have ⟨_, h_fn2, h_arg2⟩ := HasTypeA.app_inv h_fn1
  rw [denote_app (.cons q (.cons p .nil)) h_fn2 h_arg2]
  have ⟨_, h_fn3, h_arg3⟩ := HasTypeA.app_inv h_arg1
  rw [denote_app (.cons q (.cons p .nil)) h_fn3 h_arg3]
  have ⟨_, h_fn4, h_arg4⟩ := HasTypeA.app_inv h_fn3
  rw [denote_app (.cons q (.cons p .nil)) h_fn4 h_arg4]
  have ⟨_, h_fn5, h_arg5⟩ := HasTypeA.app_inv h_arg4
  rw [denote_app (.cons q (.cons p .nil)) h_fn5 h_arg5]
  have ⟨_, h_fn6, h_arg6⟩ := HasTypeA.app_inv h_fn5
  rw [denote_app (.cons q (.cons p .nil)) h_fn6 h_arg6]
  rw [denote_op, denote_op, denote_op, denote_bvar, denote_bvar, denote_bvar, denote_bvar]
  simp only [HList.get, LMonoTy.substTyVars, LMonoTy.substTyVars.map, LMonoTy.arrow]
  rw [bool_implies_interp]
  have h_bv_arg2 := HasTypeA.bvar_inv h_arg2
  have h_bv_arg3 := HasTypeA.bvar_inv h_arg3
  have h_bv_arg5 := HasTypeA.bvar_inv h_arg5
  have h_bv_arg6 := HasTypeA.bvar_inv h_arg6
  simp at h_bv_arg2 h_bv_arg3 h_bv_arg5 h_bv_arg6
  subst h_bv_arg2 h_bv_arg3 h_bv_arg5 h_bv_arg6
  have h_op2 := HasTypeA.op_inv h_fn2
  have h_op4 := HasTypeA.op_inv h_fn4
  have h_op6 := HasTypeA.op_inv h_fn6
  simp [boolBinTy, boolTy, LMonoTy.arrow, LMonoTy.bool] at h_op2 h_op4 h_op6
  subst_vars
  cases p <;> simp

/-! ### 8. Non-contradiction: ∀ p, ¬(p ∧ ¬p) -/

private def non_contradiction : LExpr TP.mono :=
  .quant m .all "p" (some boolTy) trg
    (mkNot (mkAnd bv0 (mkNot bv0)))

private def non_contradiction_ty : LExpr.HasTypeA [] non_contradiction boolTy :=
  .quant .const
    (mkNot_ty (mkAnd_ty (.bvar (by rfl)) (mkNot_ty (.bvar (by rfl)))))

theorem valid_non_contradiction : Valid F non_contradiction non_contradiction_ty := by
  intro I vt fvarVal
  simp only [non_contradiction, boolTy]
  unfold LMonoTy.bool
  have h_inner : LExpr.HasTypeA [.tcons "bool" []]
      (mkNot (mkAnd bv0 (mkNot bv0))) (.tcons "bool" []) :=
    mkNot_ty (mkAnd_ty (.bvar (by rfl)) (mkNot_ty (.bvar (by rfl))))
  apply denote_quant_all_true .nil h_inner
  intro p
  change LExpr.denote I.tcInterp I.opInterp fvarVal vt (.cons p .nil)
    (mkNot (mkAnd bv0 (mkNot bv0))) (.tcons "bool" []) h_inner = true
  simp only [mkNot, mkAnd, notOp, andOp, boolBinTy, boolUnTy, bv0, m]
  -- Peel not(and(bv0, not(bv0)))
  -- outer not
  have ⟨_, h_fn1, h_arg1⟩ := HasTypeA.app_inv h_inner
  rw [denote_app (.cons p .nil) h_fn1 h_arg1]
  -- and(bv0, not(bv0))
  have ⟨_, h_fn2, h_arg2⟩ := HasTypeA.app_inv h_arg1
  rw [denote_app (.cons p .nil) h_fn2 h_arg2]
  have ⟨_, h_fn3, h_arg3⟩ := HasTypeA.app_inv h_fn2
  rw [denote_app (.cons p .nil) h_fn3 h_arg3]
  -- inner not(bv0)
  have ⟨_, h_fn4, h_arg4⟩ := HasTypeA.app_inv h_arg2
  rw [denote_app (.cons p .nil) h_fn4 h_arg4]
  rw [denote_op, denote_op, denote_op, denote_bvar, denote_bvar]
  simp only [HList.get, LMonoTy.substTyVars, LMonoTy.substTyVars.map, LMonoTy.arrow]
  rw [bool_not_interp, bool_and_interp]
  have h_bv3 := HasTypeA.bvar_inv h_arg3
  have h_bv4 := HasTypeA.bvar_inv h_arg4
  simp at h_bv3 h_bv4; subst h_bv3 h_bv4
  have h_op1 := HasTypeA.op_inv h_fn1
  have h_op3 := HasTypeA.op_inv h_fn3
  have h_op4 := HasTypeA.op_inv h_fn4
  simp [boolBinTy, boolUnTy, boolTy, LMonoTy.arrow, LMonoTy.bool] at h_op1 h_op3 h_op4
  subst_vars
  cases p <;> simp

/-! ### 9. Double negation: ∀ p, ¬¬p = p -/

private def double_negation : LExpr TP.mono :=
  .quant m .all "p" (some boolTy) trg
    (.eq m (mkNot (mkNot bv0)) bv0)

private def double_negation_ty : LExpr.HasTypeA [] double_negation boolTy :=
  .quant .const
    (.eq (mkNot_ty (mkNot_ty (.bvar (by rfl)))) (.bvar (by rfl)))

theorem valid_double_negation : Valid F double_negation double_negation_ty := by
  intro I vt fvarVal
  simp only [double_negation, boolTy]
  unfold LMonoTy.bool
  have h_inner : LExpr.HasTypeA [.tcons "bool" []]
      (.eq m (mkNot (mkNot bv0)) bv0) (.tcons "bool" []) :=
    .eq (mkNot_ty (mkNot_ty (.bvar (by rfl)))) (.bvar (by rfl))
  apply denote_quant_all_true .nil h_inner
  intro p
  -- Need to show eq(¬¬p, p) denotes true, i.e. both sides denote the same value
  have h_lhs_ty : LExpr.HasTypeA [.tcons "bool" []]
      (mkNot (mkNot bv0)) (.tcons "bool" []) :=
    mkNot_ty (mkNot_ty (.bvar (by rfl)))
  have h_rhs_ty : LExpr.HasTypeA [.tcons "bool" []]
      bv0 (.tcons "bool" []) := .bvar (by rfl)
  apply denote_eq_true (.cons p .nil) h_lhs_ty h_rhs_ty
  -- Goal: denote (¬¬p) = denote p
  -- RHS: denote bv0 = p
  rw [denote_bvar]
  simp only [HList.get]
  -- LHS: peel ¬¬bv0
  change LExpr.denote I.tcInterp I.opInterp fvarVal vt (.cons p .nil)
    (mkNot (mkNot bv0)) (.tcons "bool" []) h_lhs_ty = p
  simp only [mkNot, notOp, boolUnTy, bv0, m]
  have ⟨_, h_fn1, h_arg1⟩ := HasTypeA.app_inv h_lhs_ty
  rw [denote_app (.cons p .nil) h_fn1 h_arg1]
  have ⟨_, h_fn2, h_arg2⟩ := HasTypeA.app_inv h_arg1
  rw [denote_app (.cons p .nil) h_fn2 h_arg2]
  rw [denote_op, denote_op, denote_bvar]
  simp only [HList.get, LMonoTy.substTyVars, LMonoTy.substTyVars.map, LMonoTy.arrow]
  rw [bool_not_interp]
  have h_bv2 := HasTypeA.bvar_inv h_arg2
  simp at h_bv2; subst h_bv2
  have h_op1 := HasTypeA.op_inv h_fn1
  have h_op2 := HasTypeA.op_inv h_fn2
  simp [boolUnTy, boolTy, LMonoTy.arrow, LMonoTy.bool] at h_op1 h_op2
  subst_vars
  cases p <;> simp

/-! ### 10. Existential witness: ∀ x : int, ∃ y : int, y = x -/

private def exist_witness : LExpr TP.mono :=
  .quant m .all "x" (some intTy) trg
    (.quant m .exist "y" (some intTy) trg
      (.eq m bv0 bv1))

private def exist_witness_ty : LExpr.HasTypeA [] exist_witness boolTy :=
  .quant .const
    (.quant .const
      (.eq (.bvar (by rfl)) (.bvar (by rfl))))

theorem valid_exist_witness : Valid F exist_witness exist_witness_ty := by
  intro I vt fvarVal
  simp only [exist_witness, intTy]
  unfold LMonoTy.bool LMonoTy.int
  have h_exist : LExpr.HasTypeA [.tcons "int" []]
      (.quant m .exist "y" (some (.tcons "int" [])) trg (.eq m bv0 bv1)) (.tcons "bool" []) :=
    .quant .const (.eq (.bvar (by rfl)) (.bvar (by rfl)))
  apply denote_quant_all_true .nil h_exist
  intro x
  have h_body : LExpr.HasTypeA [.tcons "int" [], .tcons "int" []]
      (.eq m bv0 bv1) (.tcons "bool" []) :=
    .eq (.bvar (by rfl)) (.bvar (by rfl))
  -- Witness: y = x
  apply denote_quant_exist_true (.cons x .nil) h_body h_exist x
  apply denote_eq_true (.cons x (.cons x .nil)) (.bvar (by rfl)) (.bvar (by rfl))
  rfl

/-! ### 11. Non-tautology: ∀ p, p is not valid (over the empty factory) -/

-- We use the empty factory to avoid constructing consistent interpretations

private abbrev emptyF : @Factory TP := Factory.default

private def all_p : LExpr TP.mono :=
  .quant m .all "p" (some boolTy) trg bv0

private def all_p_ty : LExpr.HasTypeA [] all_p boolTy :=
  .quant .const (.bvar (by rfl))

private def trivialInterp : Interp emptyF where
  tcInterp := fun _ _ => Bool
  opInterp := fun _ s => @default _ (SortDenote.inhabited (fun _ _ => Bool)
    (fun _ _ => by constructor; exact true) s)
  allInhabited := ⟨fun _ _ => by constructor; exact true⟩
  interpConsistent := ⟨fun _ hf => absurd hf (Factory.default_empty _),
                       fun _ hf => absurd hf (Factory.default_empty _)⟩
  constrConsistent := ⟨fun _ _ hf => absurd hf (by simp [emptyF]),
                       fun _ hf => absurd hf (by simp [emptyF])⟩

theorem not_valid_all_p : ¬ Valid emptyF all_p all_p_ty := by
  intro h
  unfold Valid Interp.satisfies at h
  have h_fv : FreeVarVal TP trivialInterp.tcInterp := fun _ s =>
    @default _ (@SortDenote.instInhabited _ trivialInterp.allInhabited s)
  have h_eq := h trivialInterp (fun _ => .tcons "bool" []) h_fv
  have h_body : LExpr.HasTypeA [.tcons "bool" []] bv0 (.tcons "bool" []) := .bvar (by rfl)
  have h_false := denote_quant_all_false (T := TP)
    (tcInterp := trivialInterp.tcInterp) (opInterp := trivialInterp.opInterp)
    (fvarVal := h_fv) (vt := fun _ => .tcons "bool" [])
    .nil h_body all_p_ty (w := false) (by
      rw [denote_bvar]; rfl)
  simp only [all_p] at h_eq
  unfold boolTy at h_eq
  unfold LMonoTy.bool at *
  rw [h_false] at h_eq
  contradiction

end Lambda
