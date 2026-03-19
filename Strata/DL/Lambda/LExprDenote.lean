/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.LExprAnnotated

namespace Lambda

/-! ### Sorts and Type Denotation -/

/-- A sort is a ground monomorphic type — an `LMonoTy` with no free type
variables. -/
inductive LSort where
  | tcons (name : String) (args : List LSort)
  | bitvec (size : Nat)

/-- Substitute all free type variables in a monomorphic type, producing a
ground sort. -/
def LMonoTy.substTyVars (ρ : TyIdentifier → LSort) : LMonoTy → LSort
  | LMonoTy.ftvar name      => ρ name
  | LMonoTy.bitvec n        => .bitvec n
  | LMonoTy.tcons name args => .tcons name (map args)
-- Need to define `map` to avoid well-founded recursion so that this reduces
where
  map : List LMonoTy → List LSort
  | [] => []
  | x :: xs => substTyVars ρ x :: map xs

/-- Interpret a sort into a Lean `Type`. Built-in sorts (bool, int, real,
string, bitvec, arrow) are mapped to their Lean counterparts; all others
are delegated to `tcInterp`. -/
def SortDenote (tcInterp : String → List LSort → Type) : LSort → Type
  | .tcons "bool" []      => Bool
  | .tcons "int" []       => Int
  | .tcons "real" []      => Rat
  | .tcons "string" []    => String
  | .bitvec n             => BitVec n
  | .tcons "arrow" [a, b] => SortDenote tcInterp a → SortDenote tcInterp b
  | .tcons name args      => tcInterp name args

/-- Two-pass type denotation: substitute type variables, then interpret. -/
abbrev TyDenote (tcInterp : String → List LSort → Type)
    (ρ : TyIdentifier → LSort) (ty : LMonoTy) : Type :=
  SortDenote tcInterp (LMonoTy.substTyVars ρ ty)

/-! ### Bound Variable Valuation -/

/-- A heterogeneous list indexed by a list of elements of type `α`. -/
inductive HList {α : Type} (f : α → Type) : List α → Type where
  | nil  : HList f []
  | cons : f a → HList f as → HList f (a :: as)

/-- Look up the `i`-th element of an `HList`, given a proof that the list
maps index `i` to `a`. -/
def HList.get {α : Type} {f : α → Type} {as : List α} {a : α} :
    HList f as → (i : Nat) → as[i]? = some a → f a
  | .cons x _, 0, h => by simp at h; subst h; exact x
  | .cons _ xs, n + 1, h => by simp at h; exact xs.get n h

/-- Bound variable valuation: an `HList` of semantic values indexed by the
typing context. -/
abbrev BVarVal (tcInterp : String → List LSort → Type)
    (ρ : TyIdentifier → LSort) (Δ : List LMonoTy) :=
  HList (TyDenote tcInterp ρ) Δ

/-! ### Inversion lemmas for `HasTypeA`

These extract subexpression types and typing proofs from a `HasTypeA` proof,
using the computable `typeCheck` function. They live in `Type` (not `Prop`)
so their results can be used in the definition of `denote`. -/

/-- From `HasTypeA Δ (.const m c) τ`, conclude `τ = c.ty`. -/
def HasTypeA.const_inv {T : LExprParams} {Δ : List LMonoTy} {m c τ}
    (h : @LExpr.HasTypeA T Δ (.const m c) τ) : τ = c.ty := by
  cases h; rfl

/-- From `HasTypeA Δ (.op m o (some ty)) τ`, conclude `τ = ty`. -/
def HasTypeA.op_inv {T : LExprParams} {Δ : List LMonoTy} {m o ty τ}
    (h : @LExpr.HasTypeA T Δ (.op m o (some ty)) τ) : τ = ty := by
  cases h; rfl

/-- From `HasTypeA Δ (.fvar m x (some ty)) τ`, conclude `τ = ty`. -/
def HasTypeA.fvar_inv {T : LExprParams} {Δ : List LMonoTy} {m x ty τ}
    (h : @LExpr.HasTypeA T Δ (.fvar m x (some ty)) τ) : τ = ty := by
  cases h; rfl

/-- From `HasTypeA Δ (.bvar m i) τ`, conclude `Δ[i]? = some τ`. -/
def HasTypeA.bvar_inv {T : LExprParams} {Δ : List LMonoTy} {m i τ}
    (h : @LExpr.HasTypeA T Δ (.bvar m i) τ) : Δ[i]? = some τ := by
  cases h; assumption

/-- From `HasTypeA Δ (.abs m name (some aty) body) τ`, extract the return type
and body typing proof. -/
def HasTypeA.abs_inv {T : LExprParams} {Δ : List LMonoTy} {m name aty body τ}
    (h : @LExpr.HasTypeA T Δ (.abs m name (some aty) body) τ)
    : Σ' rty, (τ = LMonoTy.arrow aty rty) ∧ LExpr.HasTypeA (aty :: Δ) body rty :=
  let tc := LExpr.typeCheck (aty :: Δ) body
  match h_tc : tc with
  | some rty =>
    ⟨rty,
     by have h' := LExpr.HasTypeA_to_typeCheck h
        unfold tc at *
        simp [LExpr.typeCheck, h_tc, Option.bind] at h'
        exact h'.symm,
     LExpr.typeCheck_to_HasTypeA h_tc⟩
  | none =>
    absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tc at *
          simp [LExpr.typeCheck, h_tc, Option.bind])

/-- From `HasTypeA Δ (.app m fn arg) τ`, extract the domain type and
sub-proofs. -/
def HasTypeA.app_inv {T : LExprParams} {Δ : List LMonoTy} {m fn arg τ}
    (h : @LExpr.HasTypeA T Δ (.app m fn arg) τ)
    : Σ' aty, LExpr.HasTypeA Δ fn (LMonoTy.arrow aty τ) ∧ LExpr.HasTypeA Δ arg aty :=
  let tcFn := LExpr.typeCheck Δ fn
  let tcArg := LExpr.typeCheck Δ arg
  match h_fn : tcFn, h_arg : tcArg with
  | some fty, some aty =>
    match h_arr : fty.isArrow with
    | some (dom, cod) =>
      if h_eq : dom == aty then
        ⟨aty,
         by have h' := LExpr.HasTypeA_to_typeCheck h
            unfold tcFn tcArg at *
            have h_eq' : dom = aty := by grind
            simp [LExpr.typeCheck, h_fn, h_arg, h_arr, h_eq', Option.bind, guard] at h'
            subst h'
            have h_arrow := LMonoTy.isArrow_some h_arr; subst h_arrow
            subst_vars
            exact LExpr.typeCheck_to_HasTypeA h_fn,
         LExpr.typeCheck_to_HasTypeA h_arg⟩
      else absurd (LExpr.HasTypeA_to_typeCheck h)
        (by unfold tcFn tcArg at *
            have h_eq' : ¬ dom = aty := by grind
            simp [LExpr.typeCheck, h_fn, h_arg, h_arr, h_eq', Option.bind, guard])
    | none => absurd (LExpr.HasTypeA_to_typeCheck h)
        (by unfold tcFn tcArg at *
            simp [LExpr.typeCheck, h_fn, h_arg, h_arr, Option.bind])
  | some _, none => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcFn tcArg at *
          simp [LExpr.typeCheck, h_fn, h_arg, Option.bind])
  | none, _ => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcFn tcArg at *
          simp [LExpr.typeCheck, h_fn, Option.bind])

/-- From `HasTypeA Δ (.ite m c t e) τ`, extract sub-proofs for condition,
then-branch, and else-branch. -/
def HasTypeA.ite_inv {T : LExprParams} {Δ : List LMonoTy} {m c t e τ}
    (h : @LExpr.HasTypeA T Δ (.ite m c t e) τ)
    : LExpr.HasTypeA Δ c .bool ∧ LExpr.HasTypeA Δ t τ ∧ LExpr.HasTypeA Δ e τ :=
  let tcC := LExpr.typeCheck Δ c
  let tcT := LExpr.typeCheck Δ t
  let tcE := LExpr.typeCheck Δ e
  match h_c : tcC, h_t : tcT, h_e : tcE with
  | some cty, some tty, some ety =>
    if h_cb : cty == .bool then
      if h_te : tty == ety then
        have h' := LExpr.HasTypeA_to_typeCheck h
        have hcb : cty = .bool := by grind
        have hte : tty = ety := by grind
        have hτ : tty = τ := by
          subst_vars
          unfold tcC tcT tcE at *
          simp [LExpr.typeCheck, h_c, h_t, h_e, Option.bind, guard] at h'
          exact h'
        ⟨hcb ▸ LExpr.typeCheck_to_HasTypeA h_c,
         hτ ▸ LExpr.typeCheck_to_HasTypeA h_t,
         (Eq.trans (hte.symm) hτ) ▸ LExpr.typeCheck_to_HasTypeA h_e⟩
      else absurd (LExpr.HasTypeA_to_typeCheck h)
        (by unfold tcC tcT tcE at *
            have h_ne : ¬ tty = ety := by grind
            simp [LExpr.typeCheck, h_c, h_t, h_e, Option.bind, guard, h_ne]
            grind)
    else absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcC tcT tcE at *
          have h_nb : ¬ cty = .bool := by grind
          simp [LExpr.typeCheck, h_c, h_t, h_e, Option.bind, guard, h_nb])
  | some _, some _, none => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcC tcT tcE at *
          simp [LExpr.typeCheck, h_c, h_t, h_e, Option.bind])
  | some _, none, _ => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcC tcT tcE at *
          simp [LExpr.typeCheck, h_c, h_t, Option.bind])
  | none, _, _ => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcC tcT tcE at *
          simp [LExpr.typeCheck, h_c, Option.bind])

/-- From `HasTypeA Δ (.eq m e1 e2) τ`, extract the common type and
sub-proofs. -/
def HasTypeA.eq_inv {T : LExprParams} {Δ : List LMonoTy} {m e1 e2 τ}
    (h : @LExpr.HasTypeA T Δ (.eq m e1 e2) τ)
    : Σ' ty, (τ = .bool) ∧ LExpr.HasTypeA Δ e1 ty ∧ LExpr.HasTypeA Δ e2 ty :=
  let tc1 := LExpr.typeCheck Δ e1
  let tc2 := LExpr.typeCheck Δ e2
  match h_1 : tc1, h_2 : tc2 with
  | some ty1, some ty2 =>
    if h_eq : ty1 == ty2 then
      have heq : ty1 = ty2 := by grind
      ⟨ty1,
       by have h' := LExpr.HasTypeA_to_typeCheck h
          unfold tc1 tc2 at *
          simp [LExpr.typeCheck, h_1, h_2, Option.bind, guard, heq] at h'
          exact h'.symm,
       LExpr.typeCheck_to_HasTypeA h_1,
       heq ▸ LExpr.typeCheck_to_HasTypeA h_2⟩
    else absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tc1 tc2 at *
          have h_ne : ¬ ty1 = ty2 := by grind
          simp [LExpr.typeCheck, h_1, h_2, Option.bind, guard, h_ne])
  | some _, none => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tc1 tc2 at *
          simp [LExpr.typeCheck, h_1, h_2, Option.bind])
  | none, _ => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tc1 tc2 at *
          simp [LExpr.typeCheck, h_1, Option.bind])

/-- From `HasTypeA Δ (.quant m k name (some qty) tr body) τ`, extract the
trigger type and sub-proofs. -/
def HasTypeA.quant_inv {T : LExprParams} {Δ : List LMonoTy} {m k name qty tr body τ}
    (h : @LExpr.HasTypeA T Δ (.quant m k name (some qty) tr body) τ)
    : Σ' τ_tr, (τ = .bool) ∧ LExpr.HasTypeA (qty :: Δ) tr τ_tr ∧
               LExpr.HasTypeA (qty :: Δ) body .bool :=
  let tcTr := LExpr.typeCheck (qty :: Δ) tr
  let tcBody := LExpr.typeCheck (qty :: Δ) body
  match h_tr : tcTr, h_body : tcBody with
  | some τ_tr, some bty =>
    if h_bb : bty == .bool then
      have hbb : bty = .bool := by grind
      ⟨τ_tr,
       by have h' := LExpr.HasTypeA_to_typeCheck h
          unfold tcTr tcBody at *
          simp [LExpr.typeCheck, h_tr, h_body, Option.bind, guard, hbb] at h'
          exact h'.symm,
       LExpr.typeCheck_to_HasTypeA h_tr,
       hbb ▸ LExpr.typeCheck_to_HasTypeA h_body⟩
    else absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcTr tcBody at *
          have h_nb : ¬ bty = .bool := by grind
          simp [LExpr.typeCheck, h_tr, h_body, Option.bind, guard, h_nb])
  | some _, none => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcTr tcBody at *
          simp [LExpr.typeCheck, h_tr, h_body, Option.bind])
  | none, _ => absurd (LExpr.HasTypeA_to_typeCheck h)
      (by unfold tcTr tcBody at *
          simp [LExpr.typeCheck, h_tr, Option.bind])

/-! ### Denotational Semantics -/

/-- Denote a constant literal. -/
def denoteConst (tcInterp : String → List LSort → Type) (vt : TyIdentifier → LSort) : (c : LConst) → TyDenote tcInterp vt c.ty
    | .boolConst b     => b
    | .intConst i      => i
    | .realConst r     => r
    | .strConst s      => s
    | .bitvecConst _ b => b

/-- Interpret a well-typed annotated `LExpr` into a Lean value.

`opInterp` and `fvarVal` take sorts (ground types) rather than monomorphic
types, making them independent of the type variable valuation `ρ`. This
cleanly separates interpretations (fixed for a theory) from valuations
(vary per context), enabling change-of-valuation theorems. -/
noncomputable def LExpr.denote
    {T : LExprParams}
    (tcInterp : String → List LSort → Type)
    (opInterp : Identifier T.IDMeta → (s : LSort) → SortDenote tcInterp s)
    (fvarVal : Identifier T.IDMeta → (s : LSort) → SortDenote tcInterp s)
    (vt : TyIdentifier → LSort)
    {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    {e : LExpr T.mono} {τ : LMonoTy}
    (h : HasTypeA Δ e τ)
    : TyDenote tcInterp vt τ :=
  match e with
  | .const _ c =>
    HasTypeA.const_inv h ▸ denoteConst tcInterp vt c
  | .op _ o (some ty) =>
    HasTypeA.op_inv h ▸ opInterp o (ty.substTyVars vt)
  | .op _ _ none => absurd (HasTypeA_to_typeCheck h) (by simp [typeCheck])
  | .fvar _ x (some ty) =>
    HasTypeA.fvar_inv h ▸ fvarVal x (ty.substTyVars vt)
  | .fvar _ _ none => absurd (HasTypeA_to_typeCheck h) (by simp [typeCheck])
  | .bvar _ i =>
    bvarVal.get i (HasTypeA.bvar_inv h)
  | .abs _ _ (some aty) body =>
    let ⟨rty, h_eq, h_body⟩ := HasTypeA.abs_inv h
    h_eq ▸ fun (x : TyDenote tcInterp vt aty) =>
      denote tcInterp opInterp fvarVal vt (.cons x bvarVal) h_body
  | .abs _ _ none _ => absurd (HasTypeA_to_typeCheck h) (by simp [typeCheck])
  | .app _ fn arg =>
    let ⟨aty, h_fn, h_arg⟩ := HasTypeA.app_inv h
    (denote tcInterp opInterp fvarVal vt bvarVal h_fn)
      (denote tcInterp opInterp fvarVal vt bvarVal h_arg)
  | .ite _ c t e =>
    let ⟨h_c, h_t, h_e⟩ := HasTypeA.ite_inv h
    let cond : Bool := denote tcInterp opInterp fvarVal vt bvarVal h_c
    if cond
    then denote tcInterp opInterp fvarVal vt bvarVal h_t
    else denote tcInterp opInterp fvarVal vt bvarVal h_e
  | .eq _ e1 e2 =>
    let ⟨ty', h_bool, h_1, h_2⟩ := HasTypeA.eq_inv h
    let v1 := denote tcInterp opInterp fvarVal vt bvarVal h_1
    let v2 := denote tcInterp opInterp fvarVal vt bvarVal h_2
    h_bool ▸ (Classical.propDecidable (v1 = v2) |>.decide)
  | .quant _ .all _ (some qty) tr body =>
    let ⟨_τ_tr, h_bool, _h_tr, h_body⟩ := HasTypeA.quant_inv h
    h_bool ▸ (Classical.propDecidable
      (∀ x : TyDenote tcInterp vt qty,
        (denote tcInterp opInterp fvarVal vt (.cons x bvarVal) h_body : Bool) = true)
      |>.decide)
  | .quant _ .exist _ (some qty) tr body =>
    let ⟨_τ_tr, h_bool, _h_tr, h_body⟩ := HasTypeA.quant_inv h
    h_bool ▸ (Classical.propDecidable
      (∃ x : TyDenote tcInterp vt qty,
        (denote tcInterp opInterp fvarVal vt (.cons x bvarVal) h_body : Bool) = true)
      |>.decide)
  | .quant _ _ _ none _ _ =>
    absurd (HasTypeA_to_typeCheck h) (by simp [typeCheck])

end Lambda
