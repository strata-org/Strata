/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Experiment.HM.Subst

/-! ## Type Checker for Fully-Annotated Expressions

Checks that all type annotations in an `AExpr` are consistent.
Free variables and operators are trusted to have their annotated type.
Bound variables are typed by a de Bruijn context `Δ : List Ty`.
Returns the type of the expression on success.
-/

namespace HM

/-- Check that an annotated expression has consistent annotations.
    `Δ` maps bound variable indices to their types. -/
def check (Δ : List Ty) : AExpr → Except String Ty
  | .bvar n => match Δ[n]? with
    | some t => .ok t
    | none => .error s!"bvar {n} out of range"
  | .fvar t _ => .ok t
  | .op t _ => .ok t
  | .const (.bool _) => .ok .bool
  | .const (.int _) => .ok .int
  | .abs arrTy body => do
    match arrTy with
    | .arrow dom cod =>
      let bodyTy ← check (dom :: Δ) body
      if bodyTy == cod then .ok arrTy
      else .error s!"abs: body type {repr bodyTy} ≠ codomain {repr cod}"
    | _ => .error s!"abs: annotation {repr arrTy} is not an arrow type"
  | .app fnTy argTy f a => do
    let fTy ← check Δ f
    let aTy ← check Δ a
    if fTy != fnTy then .error s!"app: function type mismatch"
    else if aTy != argTy then .error s!"app: argument type mismatch"
    else match fnTy with
    | .arrow dom cod =>
      if dom == argTy then .ok cod
      else .error s!"app: domain {repr dom} ≠ arg type {repr argTy}"
    | _ => .error s!"app: function annotation {repr fnTy} is not an arrow type"
  | .ite resTy c t f => do
    let cTy ← check Δ c
    let tTy ← check Δ t
    let fTy ← check Δ f
    if cTy != .bool then .error s!"ite: condition type {repr cTy} ≠ bool"
    else if tTy != resTy then .error s!"ite: then type {repr tTy} ≠ annotation {repr resTy}"
    else if fTy != resTy then .error s!"ite: else type {repr fTy} ≠ annotation {repr resTy}"
    else .ok resTy
  | .eq subTy a b => do
    let aTy ← check Δ a
    let bTy ← check Δ b
    if aTy != subTy then .error s!"eq: left type {repr aTy} ≠ annotation {repr subTy}"
    else if bTy != subTy then .error s!"eq: right type {repr bTy} ≠ annotation {repr subTy}"
    else .ok .bool
  | .quant _ boundTy body => do
    let bodyTy ← check (boundTy :: Δ) body
    if bodyTy != .bool then .error s!"quant: body type {repr bodyTy} ≠ bool"
    else .ok .bool

/-! ## Typing rules for annotated expressions

`HasTypeA Δ e τ` holds iff `check Δ e = .ok τ`.
-/

inductive HasTypeA : List Ty → AExpr → Ty → Prop where
  | bvar  : Δ[n]? = some t → HasTypeA Δ (.bvar n) t
  | fvar  : HasTypeA Δ (.fvar t x) t
  | op    : HasTypeA Δ (.op t f) t
  | boolc : HasTypeA Δ (.const (.bool b)) .bool
  | intc  : HasTypeA Δ (.const (.int i)) .int
  | abs   : HasTypeA (dom :: Δ) body cod →
            HasTypeA Δ (.abs (.arrow dom cod) body) (.arrow dom cod)
  | app   : HasTypeA Δ f (.arrow argTy cod) →
            HasTypeA Δ a argTy →
            HasTypeA Δ (.app (.arrow argTy cod) argTy f a) cod
  | ite   : HasTypeA Δ c .bool →
            HasTypeA Δ t τ →
            HasTypeA Δ f τ →
            HasTypeA Δ (.ite τ c t f) τ
  | eq    : HasTypeA Δ a τ →
            HasTypeA Δ b τ →
            HasTypeA Δ (.eq τ a b) .bool
  | quant : HasTypeA (boundTy :: Δ) body .bool →
            HasTypeA Δ (.quant k boundTy body) .bool

theorem check_to_HasTypeA (Δ : List Ty) (e : AExpr) (ty : Ty)
    (h : check Δ e = .ok ty) : HasTypeA Δ e ty := by
  induction e generalizing Δ ty with
  | bvar n =>
    simp [check] at h
    split at h <;> try contradiction
    simp at h; subst h
    exact .bvar ‹_›
  | fvar t x => simp [check] at h; subst h; exact .fvar
  | op t f => simp [check] at h; subst h; exact .op
  | const c => cases c with
    | bool b => simp [check] at h; subst h; exact .boolc
    | int i => simp [check] at h; subst h; exact .intc
  | abs arrTy body ih =>
    simp [check, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i dom cod
    split at h <;> (try contradiction); rename_i hbody
    split at h <;> try contradiction
    cases h; specialize (ih _ _ hbody); subst_vars
    constructor; assumption
  | app fnTy argTy f a ihf iha =>
    simp [check, bind, Except.bind] at h
    split at h <;> (try contradiction); rename_i _ hf
    split at h <;> (try contradiction); rename_i _ ha
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i dom cod
    split at h <;> try contradiction
    cases h; subst_vars
    exact .app (ihf _ _ hf) (iha _ _ ha)
  | ite resTy c t f ihc iht ihf =>
    simp [check, bind, Except.bind] at h
    split at h <;> (try contradiction); rename_i _ hc
    split at h <;> (try contradiction); rename_i _ ht
    split at h <;> (try contradiction); rename_i _ hf'
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    cases h; subst_vars
    exact .ite (ihc _ _ hc) (iht _ _ ht) (ihf _ _ hf')
  | eq subTy a b iha ihb =>
    simp [check, bind, Except.bind] at h
    split at h <;> (try contradiction); rename_i _ ha
    split at h <;> (try contradiction); rename_i _ hb
    split at h <;> try contradiction
    split at h <;> try contradiction
    cases h; subst_vars
    exact .eq (iha _ _ ha) (ihb _ _ hb)
  | quant k boundTy body ih =>
    simp [check, bind, Except.bind] at h
    split at h <;> (try contradiction); rename_i _ hbody
    split at h <;> try contradiction
    cases h; subst_vars
    exact .quant (ih _ _ hbody)

theorem HasTypeA_to_check (Δ : List Ty) (e : AExpr) (ty : Ty)
    (h : HasTypeA Δ e ty) : check Δ e = .ok ty := by
  induction h with
  | bvar hlookup => simp [check, hlookup]
  | fvar => simp [check]
  | op => simp [check]
  | boolc => simp [check]
  | intc => simp [check]
  | abs _ ih =>
    simp only [check, bind, Except.bind, Ty.arrow]; rw [ih]; simp
  | app _ _ ihf iha =>
    simp [check, bind, Except.bind, ihf, iha]
    split <;> try grind
    split
    . rename_i heq h; cases heq; rfl
    . rename_i heq h; cases heq; contradiction
  | ite _ _ _ ihc iht ihf => simp [check, bind, Except.bind, ihc, iht, ihf]
  | eq _ _ iha ihb => simp [check, bind, Except.bind, iha, ihb]
  | quant _ ih => simp [check, bind, Except.bind, ih]

end HM
