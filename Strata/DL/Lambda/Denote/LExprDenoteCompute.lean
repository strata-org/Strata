/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.LExprWF

/-!
## Computing Denotations

Forms of the `Denotes` rules whose value is a function of the values of the
subterms, so that a derivation for a concrete expression can be built by applying
one rule per node and its value read off at the end. The `eq`, `ite` and
quantifier rules of `Denotes` split on the outcome; the forms here return it as a
Boolean (`decide`, `bif`), and the bound-variable forms return the variable's
value itself rather than an `HList.get`.

- `Denotes.eq_decide`, `Denotes.ite_cond`, `Denotes.all_decide`,
  `Denotes.exist_decide`, `Denotes.bvar_zero`, `Denotes.bvar_succ`
- `denote_eq_of_Denotes` — turns a derivation into an equation for `denote`
- `denote_substOps` — replacing operators by operators with the same type and the
  same interpretation does not change the denotation
-/

namespace Lambda

variable {T : LExprParams}
variable {tcInterp : TyConstrInterp}
variable {opInterp : OpInterp tcInterp}
variable {fvarVal : FreeVarVal T tcInterp}
variable {vt : TyVarVal}

/-- The classical decision of a proposition is `true` exactly when it holds. -/
theorem classical_decide_eq_true {p : Prop} :
    (@decide p (Classical.propDecidable p) = true) = p :=
  propext ⟨@of_decide_eq_true _ (Classical.propDecidable p),
    @decide_eq_true _ (Classical.propDecidable p)⟩

/-- An equality denotes whether its two sides denote the same value. -/
theorem Denotes.eq_decide {Δ : List LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    {m : T.Metadata} {e1 e2 : LExpr T.mono} {τ : LMonoTy}
    {h1 : LExpr.HasTypeA Δ e1 τ} {h2 : LExpr.HasTypeA Δ e2 τ}
    {h : LExpr.HasTypeA Δ (.eq m e1 e2) .bool}
    {v1 v2 : TyDenote tcInterp vt τ}
    (hd1 : Denotes tcInterp opInterp fvarVal vt bvarVal e1 τ h1 v1)
    (hd2 : Denotes tcInterp opInterp fvarVal vt bvarVal e2 τ h2 v2) :
    Denotes tcInterp opInterp fvarVal vt bvarVal (.eq m e1 e2) .bool h
      (@decide (v1 = v2) (Classical.propDecidable _)) := by
  by_cases hv : v1 = v2
  · subst hv
    rw [@decide_eq_true _ (Classical.propDecidable _) rfl]
    exact .eq_true bvarVal hd1 hd2
  · rw [@decide_eq_false _ (Classical.propDecidable _) hv]
    exact .eq_false bvarVal hd1 hd2 hv

/-- A conditional denotes the value of the branch its condition selects. -/
theorem Denotes.ite_cond {Δ : List LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    {m : T.Metadata} {c t e : LExpr T.mono} {τ : LMonoTy}
    {h_c : LExpr.HasTypeA Δ c .bool} {h_t : LExpr.HasTypeA Δ t τ}
    {h_e : LExpr.HasTypeA Δ e τ} {h : LExpr.HasTypeA Δ (.ite m c t e) τ}
    {vc : Bool} {v1 v2 : TyDenote tcInterp vt τ}
    (hc : Denotes tcInterp opInterp fvarVal vt bvarVal c .bool h_c vc)
    (ht : Denotes tcInterp opInterp fvarVal vt bvarVal t τ h_t v1)
    (he : Denotes tcInterp opInterp fvarVal vt bvarVal e τ h_e v2) :
    Denotes tcInterp opInterp fvarVal vt bvarVal (.ite m c t e) τ h
      (bif vc then v1 else v2) := by
  cases vc
  · exact .ite_false bvarVal hc he
  · exact .ite_true bvarVal hc ht

/-- A universal quantifier denotes whether its body denotes `true` for every value. -/
theorem Denotes.all_decide {Δ : List LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    {m : T.Metadata} {name : String} {qty : LMonoTy} {tr body : LExpr T.mono}
    {h_body : LExpr.HasTypeA (qty :: Δ) body .bool}
    {h : LExpr.HasTypeA Δ (.quant m .all name (some qty) tr body) .bool}
    {f : TyDenote tcInterp vt qty → Bool}
    (hb : ∀ x, Denotes tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body (f x)) :
    Denotes tcInterp opInterp fvarVal vt bvarVal (.quant m .all name (some qty) tr body) .bool h
      (@decide (∀ x, f x = true) (Classical.propDecidable _)) := by
  by_cases hall : ∀ x, f x = true
  · rw [@decide_eq_true _ (Classical.propDecidable _) hall]
    exact .quant_all_true bvarVal fun x => hall x ▸ hb x
  · rw [@decide_eq_false _ (Classical.propDecidable _) hall]
    obtain ⟨w, hw⟩ := Classical.not_forall.mp hall
    exact .quant_all_false bvarVal w (Bool.eq_false_iff.mpr hw ▸ hb w)

/-- An existential quantifier denotes whether its body denotes `true` for some value. -/
theorem Denotes.exist_decide {Δ : List LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    {m : T.Metadata} {name : String} {qty : LMonoTy} {tr body : LExpr T.mono}
    {h_body : LExpr.HasTypeA (qty :: Δ) body .bool}
    {h : LExpr.HasTypeA Δ (.quant m .exist name (some qty) tr body) .bool}
    {f : TyDenote tcInterp vt qty → Bool}
    (hb : ∀ x, Denotes tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body (f x)) :
    Denotes tcInterp opInterp fvarVal vt bvarVal (.quant m .exist name (some qty) tr body) .bool h
      (@decide (∃ x, f x = true) (Classical.propDecidable _)) := by
  by_cases hex : ∃ x, f x = true
  · rw [@decide_eq_true _ (Classical.propDecidable _) hex]
    obtain ⟨w, hw⟩ := hex
    exact .quant_exist_true bvarVal w (hw ▸ hb w)
  · rw [@decide_eq_false _ (Classical.propDecidable _) hex]
    exact .quant_exist_false bvarVal fun x =>
      Bool.eq_false_iff.mpr (fun hx => hex ⟨x, hx⟩) ▸ hb x

/-- A universal quantifier denotes whether its body denotes `true` for every value.
The body's value is left as a `denote`, to be computed under the binder. -/
theorem Denotes.all_denote {Δ : List LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    {m : T.Metadata} {name : String} {qty : LMonoTy} {tr body : LExpr T.mono}
    {h : LExpr.HasTypeA Δ (.quant m .all name (some qty) tr body) .bool}
    (h_body : LExpr.HasTypeA (qty :: Δ) body .bool) :
    Denotes tcInterp opInterp fvarVal vt bvarVal (.quant m .all name (some qty) tr body) .bool h
      (@decide (∀ x, LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body
        = true) (Classical.propDecidable _)) :=
  Denotes.all_decide fun _ => denote_Denotes tcInterp opInterp fvarVal vt _ body _ h_body

/-- An existential quantifier denotes whether its body denotes `true` for some value.
The body's value is left as a `denote`, to be computed under the binder. -/
theorem Denotes.exist_denote {Δ : List LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    {m : T.Metadata} {name : String} {qty : LMonoTy} {tr body : LExpr T.mono}
    {h : LExpr.HasTypeA Δ (.quant m .exist name (some qty) tr body) .bool}
    (h_body : LExpr.HasTypeA (qty :: Δ) body .bool) :
    Denotes tcInterp opInterp fvarVal vt bvarVal (.quant m .exist name (some qty) tr body) .bool h
      (@decide (∃ x, LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body
        = true) (Classical.propDecidable _)) :=
  Denotes.exist_decide fun _ => denote_Denotes tcInterp opInterp fvarVal vt _ body _ h_body

/-- An application denotes the value of its function at the value of its argument,
with the argument's type the one `typeCheck` computes. -/
theorem Denotes.app_tc {Δ : List LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    {m : T.Metadata} {fn arg : LExpr T.mono} {aty τ : LMonoTy}
    {h_fn : LExpr.HasTypeA Δ fn (.arrow aty τ)} {h_arg : LExpr.HasTypeA Δ arg aty}
    {h : LExpr.HasTypeA Δ (.app m fn arg) τ}
    {vf : TyDenote tcInterp vt (.arrow aty τ)} {va : TyDenote tcInterp vt aty}
    (_ : LExpr.typeCheck Δ arg = some aty)
    (hfn : Denotes tcInterp opInterp fvarVal vt bvarVal fn (.arrow aty τ) h_fn vf)
    (harg : Denotes tcInterp opInterp fvarVal vt bvarVal arg aty h_arg va) :
    Denotes tcInterp opInterp fvarVal vt bvarVal (.app m fn arg) τ h (vf va) :=
  .app bvarVal hfn harg

/-- An equality denotes whether its two sides denote the same value, with the operands'
common type the one `typeCheck` computes. -/
theorem Denotes.eq_tc {Δ : List LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    {m : T.Metadata} {e1 e2 : LExpr T.mono} {τ : LMonoTy}
    {h1 : LExpr.HasTypeA Δ e1 τ} {h2 : LExpr.HasTypeA Δ e2 τ}
    {h : LExpr.HasTypeA Δ (.eq m e1 e2) .bool}
    {v1 v2 : TyDenote tcInterp vt τ}
    (_ : LExpr.typeCheck Δ e1 = some τ)
    (hd1 : Denotes tcInterp opInterp fvarVal vt bvarVal e1 τ h1 v1)
    (hd2 : Denotes tcInterp opInterp fvarVal vt bvarVal e2 τ h2 v2) :
    Denotes tcInterp opInterp fvarVal vt bvarVal (.eq m e1 e2) .bool h
      (@decide (v1 = v2) (Classical.propDecidable _)) :=
  Denotes.eq_decide hd1 hd2

/-- An operator denotes its interpretation at the sort of its annotation. -/
theorem Denotes.op_ann {Δ : List LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    {m : T.Metadata} {o : T.Identifier} {ty : LMonoTy}
    {h : LExpr.HasTypeA Δ (.op m o (some ty)) ty} :
    Denotes tcInterp opInterp fvarVal vt bvarVal (.op m o (some ty)) ty h
      (opInterp o.name (ty.substTyVars vt)) :=
  .op bvarVal

/-- A constant denotes its value. -/
theorem Denotes.const_val {Δ : List LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    {m : T.Metadata} {c : LConst} {h : LExpr.HasTypeA Δ (.const m c) c.ty} :
    Denotes tcInterp opInterp fvarVal vt bvarVal (.const m c) c.ty h (denoteConst tcInterp vt c) :=
  .const bvarVal

/-- A free variable denotes its value at the sort of its annotation. -/
theorem Denotes.fvar_ann {Δ : List LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    {m : T.Metadata} {x : T.Identifier} {ty : LMonoTy}
    {h : LExpr.HasTypeA Δ (.fvar m x (some ty)) ty} :
    Denotes tcInterp opInterp fvarVal vt bvarVal (.fvar m x (some ty)) ty h
      (fvarVal x (ty.substTyVars vt)) :=
  .fvar bvarVal

/-- The innermost bound variable denotes the head of the valuation. -/
theorem Denotes.bvar_zero {Δ : List LMonoTy} {τ : LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    {x : TyDenote tcInterp vt τ} {m : T.Metadata} {h : LExpr.HasTypeA (τ :: Δ) (.bvar m 0) τ} :
    Denotes tcInterp opInterp fvarVal vt (.cons x bvarVal) (.bvar m 0) τ h x :=
  Denotes.bvar (.cons x bvarVal) (h_lookup := by simp)

/-- Bound variable `i + 1` denotes, under `x :: bvarVal`, what `i` denotes under `bvarVal`. -/
theorem Denotes.bvar_succ {Δ : List LMonoTy} {τ σ : LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    {x : TyDenote tcInterp vt σ} {m : T.Metadata} {i : Nat}
    {h' : LExpr.HasTypeA Δ (.bvar m i) τ} {h : LExpr.HasTypeA (σ :: Δ) (.bvar m (i + 1)) τ}
    {v : TyDenote tcInterp vt τ}
    (hd : Denotes tcInterp opInterp fvarVal vt bvarVal (.bvar m i) τ h' v) :
    Denotes tcInterp opInterp fvarVal vt (.cons x bvarVal) (.bvar m (i + 1)) τ h v := by
  cases hd
  rename_i hl
  exact Denotes.bvar (.cons x bvarVal) (h_lookup := by simpa using hl)

syntax "denotes_step" : tactic
macro_rules
  | `(tactic| denotes_step) => `(tactic| first
    | exact LExpr.typeCheck_to_HasTypeA rfl
    | exact Denotes.bvar_zero
    | apply Denotes.bvar_succ
    | apply Denotes.all_denote
    | apply Denotes.exist_denote
    | (apply Denotes.eq_tc; exact rfl)
    | apply Denotes.ite_cond
    | (apply Denotes.app_tc; exact rfl)
    | exact Denotes.op_ann
    | exact Denotes.const_val
    | exact Denotes.fvar_ann)

/-- Build a `Denotes` derivation for a concrete expression, one rule per node. Its
value is left as a term in the values of the operators, constants, free variables
and bound variables. A leaf can be closed only once the typing goals of its parent
are, so the tactic keeps going over all open goals, closing typing goals and applying
rules, until a round changes none of them. -/
macro "denotes" : tactic => `(tactic| (
  repeat (any_goals (first | exact LExpr.typeCheck_to_HasTypeA rfl | denotes_step))))

/-- Read the denotation of an expression off a derivation of its value. -/
theorem denote_eq_of_Denotes {Δ : List LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    {e : LExpr T.mono} {τ : LMonoTy} {h : LExpr.HasTypeA Δ e τ}
    {v w : TyDenote tcInterp vt τ}
    (hd : Denotes tcInterp opInterp fvarVal vt bvarVal e τ h v) (hv : v = w) :
    LExpr.denote tcInterp opInterp fvarVal vt bvarVal e τ h = w :=
  (Denotes_denote hd).symm.trans hv

/-- A formula holds when a derivation gives it the value `true`. -/
theorem denote_true_of_Denotes {Δ : List LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    {e : LExpr T.mono} {h : LExpr.HasTypeA Δ e .bool} {v : Bool}
    (hd : Denotes tcInterp opInterp fvarVal vt bvarVal e .bool h v) (hv : v = true) :
    (LExpr.denote tcInterp opInterp fvarVal vt bvarVal e .bool h : Bool) = true :=
  denote_eq_of_Denotes hd hv

/-- A formula denotes `true` exactly when the value a derivation gives it is `true`. -/
theorem denote_true_iff_of_Denotes {Δ : List LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    {e : LExpr T.mono} {h : LExpr.HasTypeA Δ e .bool} {v : Bool}
    (hd : Denotes tcInterp opInterp fvarVal vt bvarVal e .bool h v) :
    (LExpr.denote tcInterp opInterp fvarVal vt bvarVal e .bool h = true) = (v = true) := by
  rw [denote_eq_of_Denotes hd rfl]; rfl

/-! ### Replacing operators -/

section SubstOps

variable [DecidableEq T.IDMeta] [Hashable T.IDMeta]

/-- `sm` replaces each operator it maps by an operator with the same type
annotation and the same interpretation. -/
def OpRenaming (opInterp : OpInterp tcInterp)
    (sm : Strata.Util.HMap T.Identifier (Option LMonoTy → LExpr T.mono)) : Prop :=
  ∀ name mk, sm.find? name = some mk → ∀ oty, ∃ m' name',
    mk oty = .op m' name' oty ∧ opInterp name'.name = opInterp name.name

/-- An operator renaming keeps a well-typed term well-typed (before the empty-map check). -/
private theorem HasTypeA_substOpsAux
    {sm : Strata.Util.HMap T.Identifier (Option LMonoTy → LExpr T.mono)}
    (hsm : OpRenaming opInterp sm) {Δ : List LMonoTy} {e : LExpr T.mono} {τ : LMonoTy}
    (h : LExpr.HasTypeA Δ e τ) :
    LExpr.HasTypeA Δ (LExpr.substOps.substOpsAux e sm) τ := by
  induction h with
  | const => exact .const
  | @op _ m o ty =>
    simp only [LExpr.substOps.substOpsAux]
    cases hf : sm.find? o with
    | none => exact .op
    | some mk =>
      obtain ⟨m', name', hmk, -⟩ := hsm o mk hf (some ty)
      simp only [hmk]
      exact .op
  | fvar => exact .fvar
  | bvar hl => exact .bvar hl
  | abs _ ih => exact .abs ih
  | quant _ _ ihtr ihbody => exact .quant ihtr ihbody
  | app _ _ ihfn iharg => exact .app ihfn iharg
  | ite _ _ _ ihc iht ihe => exact .ite ihc iht ihe
  | eq _ _ ih1 ih2 => exact .eq ih1 ih2

/-- A renaming maps an operator to an operator with the same interpretation. -/
private theorem substOpsAux_op
    {sm : Strata.Util.HMap T.Identifier (Option LMonoTy → LExpr T.mono)}
    (hsm : OpRenaming opInterp sm) (m : T.Metadata) (o : T.Identifier) (ty : LMonoTy) :
    ∃ m' name', LExpr.substOps.substOpsAux (.op m o (some ty)) sm = .op m' name' (some ty) ∧
      opInterp name'.name = opInterp o.name := by
  simp only [LExpr.substOps.substOpsAux]
  cases hf : sm.find? o with
  | none => exact ⟨m, o, rfl, rfl⟩
  | some mk => exact hsm o mk hf (some ty)

/-- An operator renaming keeps the value of a derivation (before the empty-map check). -/
private theorem Denotes_substOpsAux
    {sm : Strata.Util.HMap T.Identifier (Option LMonoTy → LExpr T.mono)}
    (hsm : OpRenaming opInterp sm) {Δ : List LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    {e : LExpr T.mono} {τ : LMonoTy} {h : LExpr.HasTypeA Δ e τ} {v : TyDenote tcInterp vt τ}
    (hd : Denotes tcInterp opInterp fvarVal vt bvarVal e τ h v)
    (h' : LExpr.HasTypeA Δ (LExpr.substOps.substOpsAux e sm) τ) :
    Denotes tcInterp opInterp fvarVal vt bvarVal (LExpr.substOps.substOpsAux e sm) τ h' v := by
  induction hd with
  | const => exact .const _
  | @op _ bv m o ty _ =>
    obtain ⟨m', name', heq, hag⟩ := substOpsAux_op hsm m o ty
    revert h'
    rw [heq]
    intro h'
    rw [← hag]
    exact .op bv
  | fvar => exact .fvar _
  | bvar => exact .bvar _
  | @abs _ bv _ _ _ _ _ h_body _ _ _ ih =>
    exact .abs bv (h_body := HasTypeA_substOpsAux hsm h_body) fun x => ih x _
  | @app _ bv _ _ _ _ _ h_fn h_arg _ _ _ _ _ ihfn iharg =>
    exact .app bv (h_fn := HasTypeA_substOpsAux hsm h_fn) (h_arg := HasTypeA_substOpsAux hsm h_arg)
      (ihfn _) (iharg _)
  | @ite_true _ bv _ _ _ _ _ h_c h_t _ _ _ _ ihc iht =>
    exact .ite_true bv (h_c := HasTypeA_substOpsAux hsm h_c) (h_t := HasTypeA_substOpsAux hsm h_t)
      (ihc _) (iht _)
  | @ite_false _ bv _ _ _ _ _ h_c h_e _ _ _ _ ihc ihe =>
    exact .ite_false bv (h_c := HasTypeA_substOpsAux hsm h_c) (h_e := HasTypeA_substOpsAux hsm h_e)
      (ihc _) (ihe _)
  | @eq_true _ bv _ _ _ _ h1 h2 _ _ _ _ ih1 ih2 =>
    exact .eq_true bv (h1 := HasTypeA_substOpsAux hsm h1) (h2 := HasTypeA_substOpsAux hsm h2)
      (ih1 _) (ih2 _)
  | @eq_false _ bv _ _ _ _ h1 h2 _ _ _ _ _ hne ih1 ih2 =>
    exact .eq_false bv (h1 := HasTypeA_substOpsAux hsm h1) (h2 := HasTypeA_substOpsAux hsm h2)
      (ih1 _) (ih2 _) hne
  | @quant_all_true _ bv _ _ _ _ _ h_body _ _ ih =>
    exact .quant_all_true bv (h_body := HasTypeA_substOpsAux hsm h_body) fun x => ih x _
  | @quant_all_false _ bv _ _ _ _ _ h_body _ w _ ih =>
    exact .quant_all_false bv (h_body := HasTypeA_substOpsAux hsm h_body) w (ih _)
  | @quant_exist_true _ bv _ _ _ _ _ h_body _ w _ ih =>
    exact .quant_exist_true bv (h_body := HasTypeA_substOpsAux hsm h_body) w (ih _)
  | @quant_exist_false _ bv _ _ _ _ _ h_body _ _ ih =>
    exact .quant_exist_false bv (h_body := HasTypeA_substOpsAux hsm h_body) fun x => ih x _

/-- A term is well-typed when its operator renaming is (before the empty-map check). -/
private theorem HasTypeA_of_substOpsAux
    {sm : Strata.Util.HMap T.Identifier (Option LMonoTy → LExpr T.mono)}
    (hsm : OpRenaming opInterp sm) {e : LExpr T.mono} :
    ∀ {Δ : List LMonoTy} {τ : LMonoTy},
      LExpr.HasTypeA Δ (LExpr.substOps.substOpsAux e sm) τ → LExpr.HasTypeA Δ e τ := by
  induction e with
  | const => intro _ _ h; exact h
  | bvar => intro _ _ h; exact h
  | fvar => intro _ _ h; exact h
  | op m o oty =>
    intro Δ τ h
    simp only [LExpr.substOps.substOpsAux] at h
    split at h
    · rename_i mk hf
      obtain ⟨m', name', hmk, -⟩ := hsm o mk hf oty
      rw [hmk] at h
      cases h
      exact .op
    · exact h
  | abs m name ty body ih =>
    intro Δ τ h
    simp only [LExpr.substOps.substOpsAux] at h
    cases h with
    | abs hb => exact .abs (ih hb)
  | quant m k name ty tr body ihtr ihbody =>
    intro Δ τ h
    simp only [LExpr.substOps.substOpsAux] at h
    cases h with
    | quant htr hb => exact .quant (ihtr htr) (ihbody hb)
  | app m fn arg ihfn iharg =>
    intro Δ τ h
    simp only [LExpr.substOps.substOpsAux] at h
    cases h with
    | app hfn harg => exact .app (ihfn hfn) (iharg harg)
  | ite m c t e ihc iht ihe =>
    intro Δ τ h
    simp only [LExpr.substOps.substOpsAux] at h
    cases h with
    | ite hc ht he => exact .ite (ihc hc) (iht ht) (ihe he)
  | eq m e1 e2 ih1 ih2 =>
    intro Δ τ h
    simp only [LExpr.substOps.substOpsAux] at h
    cases h with
    | eq h1 h2 => exact .eq (ih1 h1) (ih2 h2)

/-- An operator renaming reflects typing. -/
theorem HasTypeA_of_substOps
    {sm : Strata.Util.HMap T.Identifier (Option LMonoTy → LExpr T.mono)}
    (hsm : OpRenaming opInterp sm) {Δ : List LMonoTy} {e : LExpr T.mono} {τ : LMonoTy}
    (h : LExpr.HasTypeA Δ (e.substOps sm) τ) : LExpr.HasTypeA Δ e τ := by
  unfold LExpr.substOps at h
  split at h
  · exact h
  · exact HasTypeA_of_substOpsAux hsm h

/-- An operator renaming preserves typing. -/
theorem HasTypeA_substOps
    {sm : Strata.Util.HMap T.Identifier (Option LMonoTy → LExpr T.mono)}
    (hsm : OpRenaming opInterp sm) {Δ : List LMonoTy} {e : LExpr T.mono} {τ : LMonoTy}
    (h : LExpr.HasTypeA Δ e τ) : LExpr.HasTypeA Δ (e.substOps sm) τ := by
  unfold LExpr.substOps
  split
  · exact h
  · exact HasTypeA_substOpsAux hsm h

/-- An operator renaming preserves denotations. -/
theorem denote_substOps
    {sm : Strata.Util.HMap T.Identifier (Option LMonoTy → LExpr T.mono)}
    (hsm : OpRenaming opInterp sm) {Δ : List LMonoTy} (bvarVal : BVarVal tcInterp vt Δ)
    {e : LExpr T.mono} {τ : LMonoTy} (h : LExpr.HasTypeA Δ e τ)
    (h' : LExpr.HasTypeA Δ (e.substOps sm) τ) :
    LExpr.denote tcInterp opInterp fvarVal vt bvarVal (e.substOps sm) τ h' =
      LExpr.denote tcInterp opInterp fvarVal vt bvarVal e τ h := by
  apply denote_eq_of_Denotes _ rfl
  revert h'
  unfold LExpr.substOps
  split
  · intro h'
    exact denote_Denotes tcInterp opInterp fvarVal vt bvarVal e τ h'
  · intro h'
    exact Denotes_substOpsAux hsm (denote_Denotes tcInterp opInterp fvarVal vt bvarVal e τ h) h'

end SubstOps

end Lambda
