/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.Denote.LExprAnnotated
public import Strata.DL.Lambda.Denote.HList
import Strata.DL.Lambda.Factory

namespace Lambda

-- TODO: move

/-- Pointwise relation between two lists. -/
inductive List.Forall₂ (R : α → β → Prop) : List α → List β → Prop where
  | nil : Forall₂ R [] []
  | cons : R a b → Forall₂ R as bs → Forall₂ R (a :: as) (b :: bs)

theorem List.Forall₂.head {R : α → β → Prop} (h : Forall₂ R (a :: as) (b :: bs)) : R a b := by
  cases h; assumption

theorem List.Forall₂.tail {R : α → β → Prop} (h : Forall₂ R (a :: as) (b :: bs)) : Forall₂ R as bs := by
  cases h; assumption

theorem List.Forall₂.length_eq {R : α → β → Prop} {as : List α} {bs : List β}
    (h : Forall₂ R as bs) : as.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem List.Forall₂.get? {R : α → β → Prop} {as : List α} {bs : List β}
    (h : Forall₂ R as bs) (i : Nat) (ha : as[i]? = some a) (hb : bs[i]? = some b)
    : R a b := by
  induction h generalizing i with
  | nil => simp at ha
  | cons h_head _ ih =>
    cases i with
    | zero => simp at ha hb; cases ha; cases hb; exact h_head
    | succ n => simp at ha hb; exact ih n ha hb

/-! ### Sorts and Type Denotation -/

/-- A sort is a ground monomorphic type — an `LMonoTy` with no free type
variables. -/
inductive LSort where
  | tcons (name : String) (args : List LSort)
  | bitvec (size : Nat)

def LSort_eqb (s1 s2: LSort) : Bool :=
  match s1, s2 with
  | .tcons n1 a1, .tcons n2 a2 =>
    n1 == n2 && LSort_eqb_list a1 a2
  | .bitvec s1, .bitvec s2 => s1 == s2
  | _ , _ => false
where LSort_eqb_list : List LSort → List LSort → Bool
  | [], [] => true
  | x :: xs, y :: ys => LSort_eqb x y && LSort_eqb_list xs ys
  | _, _ => false

theorem LSort.ind (P : LSort → Prop)
    (htcons : ∀ name args, (∀ x, x ∈ args → P x) → P (.tcons name args))
    (hbitvec : ∀ n, P (.bitvec n)) : ∀ s, P s
  | .tcons name args => htcons name args (fun x _ => ind P htcons hbitvec x)
  | .bitvec n => hbitvec n

private theorem LSort_eqb_list_eq
    (ih : ∀ x ∈ a1, ∀ s2, LSort_eqb x s2 = true → x = s2)
    (heq : LSort_eqb.LSort_eqb_list a1 a2 = true) : a1 = a2 := by
  induction a1 generalizing a2 with
  | nil => cases a2 <;> simp_all [LSort_eqb.LSort_eqb_list]
  | cons h t iht =>
    cases a2 with
    | nil => simp [LSort_eqb.LSort_eqb_list] at heq
    | cons h2 t2 =>
      simp [LSort_eqb.LSort_eqb_list] at heq
      obtain ⟨hh, ht⟩ := heq
      congr 1
      · exact ih h (List.mem_cons_self ..) h2 hh
      · exact iht (fun x hx => ih x (List.mem_cons_of_mem _ hx)) ht

private theorem LSort_eqb_eq {s1 s2} (heq: LSort_eqb s1 s2 = true) :
  s1 = s2 := by
  induction s1 using LSort.ind generalizing s2 with
  | htcons n1 a1 ih =>
    cases s2 with
    | bitvec => simp [LSort_eqb] at heq
    | tcons n2 a2 =>
      simp [LSort_eqb] at heq
      obtain ⟨hn, ha⟩ := heq
      subst_vars; congr 1
      exact LSort_eqb_list_eq ih ha
  | hbitvec n1 =>
    cases s2 with
    | tcons => simp [LSort_eqb] at heq
    | bitvec => simp [LSort_eqb] at heq; exact congrArg _ heq

instance : BEq LSort := ⟨LSort_eqb⟩

private theorem LSort_eqb_refl : ∀ a : LSort, LSort_eqb a a = true := by
  intro a; induction a using LSort.ind with
  | htcons n args ih =>
    simp [LSort_eqb]
    induction args with
    | nil => simp [LSort_eqb.LSort_eqb_list]
    | cons x xs ihxs =>
      simp [LSort_eqb.LSort_eqb_list]
      exact ⟨ih x (List.mem_cons_self ..), ihxs (fun z hz => ih z (List.mem_cons_of_mem _ hz))⟩
  | hbitvec => simp [LSort_eqb]

instance : DecidableEq LSort := fun a b =>
  if h : LSort_eqb a b then isTrue (LSort_eqb_eq h)
  else isFalse (fun heq => h (heq ▸ LSort_eqb_refl a))

/-- Iterated arrow at the sort level: `mkArrow ret [s₁, s₂] = s₁ → s₂ → ret`. -/
def LSort.mkArrow (ret : LSort) : List LSort → LSort
  | [] => ret
  | s :: ss => .tcons "arrow" [s, LSort.mkArrow ret ss]

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

/-- Interpretation of type constructors: maps a constructor name and its
sort arguments to a Lean `Type`. -/
def TyConstrInterp := String → List LSort → Type

/-- Interpret a sort into a Lean `Type`. Built-in sorts (bool, int, real,
string, bitvec, arrow) are mapped to their Lean counterparts; all others
are delegated to `tcInterp`. -/
def SortDenote (tcInterp : TyConstrInterp) : LSort → Type
  | .tcons "bool" []      => Bool
  | .tcons "int" []       => Int
  | .tcons "real" []      => Rat
  | .tcons "string" []    => String
  | .bitvec n             => BitVec n
  | .tcons "arrow" [a, b] => SortDenote tcInterp a → SortDenote tcInterp b
  | .tcons name args      => tcInterp name args

/-- Type-variable valuation: maps each type variable to a sort. -/
def TyVarVal := TyIdentifier → LSort

/-- Two-pass type denotation: substitute type variables, then interpret. -/
abbrev TyDenote (tcInterp : TyConstrInterp)
    (ρ : TyVarVal) (ty : LMonoTy) : Type :=
  SortDenote tcInterp (LMonoTy.substTyVars ρ ty)

/-! ### Bound Variable Valuation -/

/-- Bound variable valuation: an `HList` of semantic values indexed by the
typing context. -/
abbrev BVarVal (tcInterp : TyConstrInterp)
    (ρ : TyVarVal) (Δ : List LMonoTy) :=
  HList (TyDenote tcInterp ρ) Δ

/-! ### Intepreting Free Variables and Operators -/

/-- Maps each identifier and sort to a semantic value of that sort.
Used for both operator interpretations (`OpInterp`) and free-variable
valuations (`FreeVarVal`). -/
def IdentInterp (T : LExprParams)
    (tcInterp : TyConstrInterp) :=
  Identifier T.IDMeta → (s : LSort) → SortDenote tcInterp s

/-- Operator interpretation: gives meaning to each named operation.
Takes the string name (not the full identifier with metadata) so that
the semantics is independent of metadata.
Need because Factory lookup only depends on the name -/
def OpInterp
    (tcInterp : TyConstrInterp) :=
  String → (s : LSort) → SortDenote tcInterp s
/-- Free-variable valuation: maps each free variable to its value. -/
abbrev FreeVarVal := IdentInterp

/-- Update an identifier interpretation so that the names in `bindings` map to
the corresponding values from `vals`. Names not in `bindings` keep their
original interpretation. -/
def IdentInterp.withArgs [DecidableEq T.IDMeta]
    {tcInterp : TyConstrInterp}
    (fvarVal : IdentInterp T tcInterp)
    (bindings : List (Identifier T.IDMeta × LSort))
    (vals : HList (SortDenote tcInterp) (bindings.map Prod.snd))
    : IdentInterp T tcInterp :=
  fun x s =>
  match bindings, vals with
  | [], .nil => fvarVal x s
  | (name, s1) :: rest, .cons v vs =>
    if x = name then
      if hs : s = s1 then hs ▸ v
      else (fvarVal.withArgs rest vs) x s
    else (fvarVal.withArgs rest vs) x s

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
def denoteConst (tcInterp : TyConstrInterp) (vt : TyVarVal) : (c : LConst) → TyDenote tcInterp vt c.ty
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
    (tcInterp : TyConstrInterp)
    (opInterp : OpInterp tcInterp)
    (fvarVal : FreeVarVal T tcInterp)
    (vt : TyVarVal)
    {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (e : LExpr T.mono) (τ : LMonoTy)
    (h : HasTypeA Δ e τ)
    : TyDenote tcInterp vt τ :=
  match e with
  | .const _ c =>
    HasTypeA.const_inv h ▸ denoteConst tcInterp vt c
  | .op _ o (some ty) =>
    HasTypeA.op_inv h ▸ opInterp o.name (ty.substTyVars vt)
  | .op _ _ none => absurd (HasTypeA_to_typeCheck h) (by simp [typeCheck])
  | .fvar _ x (some ty) =>
    HasTypeA.fvar_inv h ▸ fvarVal x (ty.substTyVars vt)
  | .fvar _ _ none => absurd (HasTypeA_to_typeCheck h) (by simp [typeCheck])
  | .bvar _ i =>
    bvarVal.get i (HasTypeA.bvar_inv h)
  | .abs _ _ (some aty) body =>
    let ⟨rty, h_eq, h_body⟩ := HasTypeA.abs_inv h
    h_eq ▸ fun (x : TyDenote tcInterp vt aty) =>
      denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body rty h_body
  | .abs _ _ none _ => absurd (HasTypeA_to_typeCheck h) (by simp [typeCheck])
  | .app _ fn arg =>
    let ⟨aty, h_fn, h_arg⟩ := HasTypeA.app_inv h
    (denote tcInterp opInterp fvarVal vt bvarVal fn (.arrow aty τ) h_fn)
      (denote tcInterp opInterp fvarVal vt bvarVal arg aty h_arg)
  | .ite _ c t e =>
    let ⟨h_c, h_t, h_e⟩ := HasTypeA.ite_inv h
    let cond : Bool := denote tcInterp opInterp fvarVal vt bvarVal c .bool h_c
    if cond
    then denote tcInterp opInterp fvarVal vt bvarVal t τ h_t
    else denote tcInterp opInterp fvarVal vt bvarVal e τ h_e
  | .eq _ e1 e2 =>
    let ⟨ty', h_bool, h_1, h_2⟩ := HasTypeA.eq_inv h
    let v1 := denote tcInterp opInterp fvarVal vt bvarVal e1 ty' h_1
    let v2 := denote tcInterp opInterp fvarVal vt bvarVal e2 ty' h_2
    h_bool ▸ (Classical.propDecidable (v1 = v2) |>.decide)
  | .quant _ .all _ (some qty) tr body =>
    let ⟨_τ_tr, h_bool, _h_tr, h_body⟩ := HasTypeA.quant_inv h
    h_bool ▸ (Classical.propDecidable
      (∀ x : TyDenote tcInterp vt qty,
        (denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body : Bool) = true)
      |>.decide)
  | .quant _ .exist _ (some qty) tr body =>
    let ⟨_τ_tr, h_bool, _h_tr, h_body⟩ := HasTypeA.quant_inv h
    h_bool ▸ (Classical.propDecidable
      (∃ x : TyDenote tcInterp vt qty,
        (denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body : Bool) = true)
      |>.decide)
  | .quant _ _ _ none _ _ =>
    absurd (HasTypeA_to_typeCheck h) (by simp [typeCheck])

/-! ### Relational Denotational Semantics

An inductive predicate relating well-typed expressions to their semantic values.
Unlike the functional `denote`, this avoids typecasts (`▸`) and
`Classical.propDecidable` — each constructor directly fixes the result type,
and `eq`/`quant` state their conditions propositionally. -/

/-- `Denotes tcInterp opInterp fvarVal vt bvarVal e τ h v` holds when the
well-typed expression `e` (of type `τ` in context `Δ`) denotes the value `v`. -/
inductive Denotes
    {T : LExprParams}
    (tcInterp : TyConstrInterp)
    (opInterp : OpInterp tcInterp)
    (fvarVal : FreeVarVal T tcInterp)
    (vt : TyVarVal)
    : {Δ : List LMonoTy} → (bvarVal : BVarVal tcInterp vt Δ) →
      (e : LExpr T.mono) → (τ : LMonoTy) → LExpr.HasTypeA Δ e τ →
      TyDenote tcInterp vt τ → Prop where
  | const : ∀ {Δ} (bvarVal : BVarVal tcInterp vt Δ) {m c h},
      Denotes tcInterp opInterp fvarVal vt bvarVal (.const m c) c.ty h (denoteConst tcInterp vt c)
  | op : ∀ {Δ} (bvarVal : BVarVal tcInterp vt Δ) {m o ty h},
      Denotes tcInterp opInterp fvarVal vt bvarVal (.op m o (some ty)) ty h (opInterp o.name (ty.substTyVars vt))
  | fvar : ∀ {Δ} (bvarVal : BVarVal tcInterp vt Δ) {m x ty h},
      Denotes tcInterp opInterp fvarVal vt bvarVal (.fvar m x (some ty)) ty h (fvarVal x (ty.substTyVars vt))
  | bvar : ∀ {Δ} (bvarVal : BVarVal tcInterp vt Δ) {m i τ} {h_lookup : Δ[i]? = some τ} {h},
      Denotes tcInterp opInterp fvarVal vt bvarVal (.bvar m i) τ h (bvarVal.get i h_lookup)
  | abs : ∀ {Δ} (bvarVal : BVarVal tcInterp vt Δ) {m name aty rty body h_body h}
      {f : TyDenote tcInterp vt aty → TyDenote tcInterp vt rty},
      (∀ x, Denotes tcInterp opInterp fvarVal vt (.cons x bvarVal) body rty h_body (f x)) →
      Denotes tcInterp opInterp fvarVal vt bvarVal (.abs m name (some aty) body) (.arrow aty rty) h f
  | app : ∀ {Δ} (bvarVal : BVarVal tcInterp vt Δ) {m fn arg aty τ h_fn h_arg h}
      {vf : TyDenote tcInterp vt (.arrow aty τ)} {va},
      Denotes tcInterp opInterp fvarVal vt bvarVal fn (.arrow aty τ) h_fn vf →
      Denotes tcInterp opInterp fvarVal vt bvarVal arg aty h_arg va →
      Denotes tcInterp opInterp fvarVal vt bvarVal (.app m fn arg) τ h (vf va)
  | ite_true : ∀ {Δ} (bvarVal : BVarVal tcInterp vt Δ) {m c t e τ h_c h_t h} {v : TyDenote tcInterp vt τ},
      Denotes tcInterp opInterp fvarVal vt bvarVal c .bool h_c true →
      Denotes tcInterp opInterp fvarVal vt bvarVal t τ h_t v →
      Denotes tcInterp opInterp fvarVal vt bvarVal (.ite m c t e) τ h v
  | ite_false : ∀ {Δ} (bvarVal : BVarVal tcInterp vt Δ) {m c t e τ h_c h_e h} {v : TyDenote tcInterp vt τ},
      Denotes tcInterp opInterp fvarVal vt bvarVal c .bool h_c false →
      Denotes tcInterp opInterp fvarVal vt bvarVal e τ h_e v →
      Denotes tcInterp opInterp fvarVal vt bvarVal (.ite m c t e) τ h v
  | eq_true : ∀ {Δ} (bvarVal : BVarVal tcInterp vt Δ) {m e1 e2 τ' h1 h2 h}
      {v : TyDenote tcInterp vt τ'},
      Denotes tcInterp opInterp fvarVal vt bvarVal e1 τ' h1 v →
      Denotes tcInterp opInterp fvarVal vt bvarVal e2 τ' h2 v →
      Denotes tcInterp opInterp fvarVal vt bvarVal (.eq m e1 e2) .bool h true
  | eq_false : ∀ {Δ} (bvarVal : BVarVal tcInterp vt Δ) {m e1 e2 τ' h1 h2 h}
      {v1 v2 : TyDenote tcInterp vt τ'},
      Denotes tcInterp opInterp fvarVal vt bvarVal e1 τ' h1 v1 →
      Denotes tcInterp opInterp fvarVal vt bvarVal e2 τ' h2 v2 →
      v1 ≠ v2 →
      Denotes tcInterp opInterp fvarVal vt bvarVal (.eq m e1 e2) .bool h false
  | quant_all_true : ∀ {Δ} (bvarVal : BVarVal tcInterp vt Δ)
      {m name qty tr body h_body h},
      (∀ x : TyDenote tcInterp vt qty,
        Denotes tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body true) →
      Denotes tcInterp opInterp fvarVal vt bvarVal (.quant m .all name (some qty) tr body) .bool h true
  | quant_all_false : ∀ {Δ} (bvarVal : BVarVal tcInterp vt Δ)
      {m name qty tr body h_body h},
      (w : TyDenote tcInterp vt qty) →
      Denotes tcInterp opInterp fvarVal vt (.cons w bvarVal) body .bool h_body false →
      Denotes tcInterp opInterp fvarVal vt bvarVal (.quant m .all name (some qty) tr body) .bool h false
  | quant_exist_true : ∀ {Δ} (bvarVal : BVarVal tcInterp vt Δ)
      {m name qty tr body h_body h},
      (w : TyDenote tcInterp vt qty) →
      Denotes tcInterp opInterp fvarVal vt (.cons w bvarVal) body .bool h_body true →
      Denotes tcInterp opInterp fvarVal vt bvarVal (.quant m .exist name (some qty) tr body) .bool h true
  | quant_exist_false : ∀ {Δ} (bvarVal : BVarVal tcInterp vt Δ)
      {m name qty tr body h_body h},
      (∀ x : TyDenote tcInterp vt qty,
        Denotes tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body false) →
      Denotes tcInterp opInterp fvarVal vt bvarVal (.quant m .exist name (some qty) tr body) .bool h false

/-! ### Equivalence between functional and relational semantics -/

-- Shared tactic for cases where `denote` unfolds into a 3-way typeCheck split.
-- After the user has done `unfold; simp only [..._inv]; split; rename_i ...`,
-- this handles `split at heq` twice, `cases heq`, closes the 3 contradiction
-- branches via `HasTypeA_to_typeCheck`, and runs `t` for the real case.
-- `h1a`/`h1b` are for the innermost contradiction, `h2` middle, `h3` outermost.
local macro "typecheck_split" h1a:ident h1b:ident h2:ident h3:ident heq:ident
    " => " t:tacticSeq : tactic =>
  `(tactic| (
     split at $heq:ident
     · split at $heq:ident
       · cases $heq:ident; ($t:tacticSeq)
       · have := LExpr.HasTypeA_to_typeCheck $h1a
         have := LExpr.HasTypeA_to_typeCheck $h1b
         simp_all; try grind
     · have := LExpr.HasTypeA_to_typeCheck $h2; simp_all
     · have := LExpr.HasTypeA_to_typeCheck $h3; simp_all))

theorem denote_Denotes
    {T : LExprParams}
    (tcInterp : TyConstrInterp)
    (opInterp : OpInterp tcInterp)
    (fvarVal : FreeVarVal T tcInterp)
    (vt : TyVarVal)
    {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (e : LExpr T.mono) (τ : LMonoTy)
    (h : LExpr.HasTypeA Δ e τ)
    : Denotes tcInterp opInterp fvarVal vt bvarVal e τ h
        (LExpr.denote tcInterp opInterp fvarVal vt bvarVal e τ h) := by
  match e with
  | .const _ c =>
    have heq := HasTypeA.const_inv h
    subst heq; exact .const bvarVal
  | .op _ _ (some ty) =>
    have heq := HasTypeA.op_inv h
    subst heq; exact .op bvarVal
  | .op _ _ none => exact absurd (LExpr.HasTypeA_to_typeCheck h) (by simp [LExpr.typeCheck])
  | .fvar _ _ (some ty) =>
    have heq := HasTypeA.fvar_inv h
    subst heq; exact .fvar bvarVal
  | .fvar _ _ none => exact absurd (LExpr.HasTypeA_to_typeCheck h) (by simp [LExpr.typeCheck])
  | .bvar _ i =>
    exact .bvar bvarVal
  | .abs _ _ (some aty) body =>
    let ⟨rty, h_eq, h_body⟩ := HasTypeA.abs_inv h
    subst h_eq
    unfold LExpr.denote
    simp only [HasTypeA.abs_inv]
    split
    rename_i x rty' h_eq' h_body' heq
    cases h_eq'
    split at heq
    . cases heq
      exact .abs bvarVal fun x => denote_Denotes tcInterp opInterp fvarVal vt (.cons x bvarVal) body _ h_body'
    . have := LExpr.HasTypeA_to_typeCheck h_body'
      simp_all
  | .abs _ _ none _ => exact absurd (LExpr.HasTypeA_to_typeCheck h) (by simp [LExpr.typeCheck])
  | .app _ fn arg =>
    let ⟨aty, h_fn, h_arg⟩ := HasTypeA.app_inv h
    unfold LExpr.denote
    simp only [HasTypeA.app_inv]
    split
    rename_i x aty' h_fn' h_arg' heq
    split at heq
    · rename_i ty1 ty2 hty1 hty2
      split at heq
      · rename_i dom cod harr
        split at heq
        · -- The real case: all matches succeeded
          cases heq
          exact .app bvarVal
            (denote_Denotes tcInterp opInterp fvarVal vt bvarVal fn _ h_fn')
            (denote_Denotes tcInterp opInterp fvarVal vt bvarVal arg _ h_arg')
        · -- Vars neq - contradicts typing
          have := LExpr.HasTypeA_to_typeCheck h_fn'
          have: aty'.arrow τ = ty1 := by simp_all
          subst_vars
          simp at harr; cases harr; subst_vars
          have := LExpr.HasTypeA_to_typeCheck h_arg'
          grind
      · -- Not arrow - contradicts typing
        rename_i hnotarr
        have := LExpr.HasTypeA_to_typeCheck h_fn'
        have: ty1 = aty'.arrow τ := by simp_all
        subst_vars
        simp at hnotarr
    · have := LExpr.HasTypeA_to_typeCheck h_arg'
      simp_all
    . have := LExpr.HasTypeA_to_typeCheck h_fn
      simp_all
  | .ite _ c t e' =>
    let ⟨h_c, h_t, h_e⟩ := HasTypeA.ite_inv h
    unfold LExpr.denote
    split
    rename_i _ h_c' h_t' h_e'
    dsimp only
    split
    · rename_i htrue
      exact .ite_true bvarVal
        (htrue ▸ denote_Denotes tcInterp opInterp fvarVal vt bvarVal c _ h_c')
        (denote_Denotes tcInterp opInterp fvarVal vt bvarVal t _ h_t')
    · rename_i hntrue
      have hf : LExpr.denote tcInterp opInterp fvarVal vt bvarVal _ _ h_c' = false :=
        Bool.eq_false_iff.mpr hntrue
      exact .ite_false bvarVal
        (hf ▸ denote_Denotes tcInterp opInterp fvarVal vt bvarVal c _ h_c')
        (denote_Denotes tcInterp opInterp fvarVal vt bvarVal e' _ h_e')
  | .eq _ e1 e2 =>
    let ⟨ty', h_bool, h_1, h_2⟩ := HasTypeA.eq_inv h
    subst h_bool
    unfold LExpr.denote
    simp only [HasTypeA.eq_inv]
    split
    rename_i x ty'' h_bool' h_1' h_2' heq
    typecheck_split h_1' h_2' h_2' h_1' heq =>
      by_cases hv : LExpr.denote tcInterp opInterp fvarVal vt bvarVal e1 ty'' h_1' =
                    LExpr.denote tcInterp opInterp fvarVal vt bvarVal e2 ty'' h_2'
      · simp [hv]
        exact .eq_true bvarVal
          (denote_Denotes tcInterp opInterp fvarVal vt bvarVal e1 _ h_1')
          (hv ▸ denote_Denotes tcInterp opInterp fvarVal vt bvarVal e2 _ h_2')
      · simp [hv]
        exact .eq_false bvarVal
          (denote_Denotes tcInterp opInterp fvarVal vt bvarVal e1 _ h_1')
          (denote_Denotes tcInterp opInterp fvarVal vt bvarVal e2 _ h_2')
          hv
  | .quant _ .all _ (some qty) tr body =>
    let ⟨τ_tr, h_bool, h_tr, h_body⟩ := HasTypeA.quant_inv h
    subst h_bool
    unfold LExpr.denote
    simp only [HasTypeA.quant_inv]
    split
    rename_i x τ_tr' h_bool' h_tr' h_body' heq
    typecheck_split h_body' h_body' h_body' h_tr' heq =>
      by_cases hv : ∀ x : TyDenote tcInterp vt qty,
        (LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body' : Bool) = true
      · simp [hv]
        exact .quant_all_true bvarVal fun x =>
          hv x ▸ denote_Denotes tcInterp opInterp fvarVal vt (.cons x bvarVal) body _ h_body'
      · simp [hv]
        have ⟨w, hw⟩ := Classical.not_forall.mp hv
        have hwf : (LExpr.denote tcInterp opInterp fvarVal vt (.cons w bvarVal) body .bool h_body' : Bool) = false :=
          Bool.eq_false_iff.mpr hw
        exact .quant_all_false bvarVal w
          (hwf ▸ denote_Denotes tcInterp opInterp fvarVal vt (.cons w bvarVal) body _ h_body')
  | .quant _ .exist _ (some qty) tr body =>
    let ⟨τ_tr, h_bool, h_tr, h_body⟩ := HasTypeA.quant_inv h
    subst h_bool
    unfold LExpr.denote
    simp only [HasTypeA.quant_inv]
    split
    rename_i x τ_tr' h_bool' h_tr' h_body' heq
    typecheck_split h_body' h_body' h_body' h_tr' heq =>
      by_cases hv : ∃ x : TyDenote tcInterp vt qty,
        (LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body' : Bool) = true
      · simp [hv]
        have ⟨w, hw⟩ := hv
        exact .quant_exist_true bvarVal w
          (hw ▸ denote_Denotes tcInterp opInterp fvarVal vt (.cons w bvarVal) body _ h_body')
      · simp [hv]
        exact .quant_exist_false bvarVal fun x =>
          let hf : (LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body' : Bool) = false :=
            Bool.eq_false_iff.mpr (fun hp => hv ⟨x, hp⟩)
          hf ▸ denote_Denotes tcInterp opInterp fvarVal vt (.cons x bvarVal) body _ h_body'
  | .quant _ _ _ none _ _ =>
    exact absurd (LExpr.HasTypeA_to_typeCheck h) (by simp [LExpr.typeCheck])

theorem Denotes_denote
    {T : LExprParams}
    {tcInterp : TyConstrInterp}
    {opInterp : OpInterp tcInterp}
    {fvarVal : FreeVarVal T tcInterp}
    {vt : TyVarVal}
    {Δ : List LMonoTy}
    {bvarVal : BVarVal tcInterp vt Δ}
    {e : LExpr T.mono} {τ : LMonoTy}
    {h : LExpr.HasTypeA Δ e τ}
    {v : TyDenote tcInterp vt τ}
    (hd : Denotes tcInterp opInterp fvarVal vt bvarVal e τ h v)
    : v = LExpr.denote tcInterp opInterp fvarVal vt bvarVal e τ h := by
  induction hd with
  | const => unfold LExpr.denote; simp
  | op => unfold LExpr.denote; simp
  | fvar => unfold LExpr.denote; simp
  | bvar => unfold LExpr.denote; simp
  | abs _ hbody ih =>
    unfold LExpr.denote; simp only [HasTypeA.abs_inv]
    split; rename_i rty h_body heq
    split at heq
    · cases heq; rename_i rty _; cases rty; funext x; exact ih x
    · have htc := LExpr.HasTypeA_to_typeCheck h_body; simp_all
  | app _ hf ha ihf iha =>
    rename_i fn arg tya tyb htyfn htyarg htyapp vf va
    unfold LExpr.denote; simp only [HasTypeA.app_inv]
    split; rename_i aty h_fn h_arg heq
    split at heq
    · rename_i ty1 ty2 hty1 hty2
      split at heq
      · rename_i dom cod harr
        split at heq
        · -- true case
          rename_i htyeq
          have : ty1 = aty.arrow tyb := by
            have := LExpr.HasTypeA_to_typeCheck h_fn
            simp_all
          have: dom = ty2 := by grind
          have : tya = aty := by
            have h := HasTypeA_unique htyfn h_fn
            cases h; rfl
          subst_vars
          rfl
        . have := LExpr.HasTypeA_to_typeCheck h_fn
          have: aty.arrow tyb = ty1 := by simp_all
          subst_vars
          simp at harr; cases harr; subst_vars
          have := LExpr.HasTypeA_to_typeCheck h_arg
          grind
      · -- Not arrow - contradicts typing
        rename_i hnotarr
        have := LExpr.HasTypeA_to_typeCheck h_fn
        have: ty1 = aty.arrow tyb := by simp_all
        subst_vars
        simp at hnotarr
    · have := LExpr.HasTypeA_to_typeCheck h_arg
      simp_all
    . have := LExpr.HasTypeA_to_typeCheck h_fn
      simp_all
  | ite_true _ hc ht ihc iht =>
    unfold LExpr.denote
    split; rename_i _ h_c h_t h_e
    dsimp only
    split
    · exact iht
    · rename_i hntrue
      have : LExpr.denote tcInterp opInterp fvarVal vt _ _ _ h_c = true := ihc.symm
      contradiction
  | ite_false _ hc he ihc ihe =>
    unfold LExpr.denote
    split; rename_i _ h_c h_t h_e
    dsimp only
    split
    · rename_i htrue
      have : LExpr.denote tcInterp opInterp fvarVal vt _ _ _ h_c = false := ihc.symm
      simp_all
    · exact ihe
  | eq_true _ h1 h2 ih1 ih2 =>
    rename_i bvarVal  _ _ _ _ htye1 htye2 _ _
    unfold LExpr.denote
    simp only [HasTypeA.eq_inv]
    split
    rename_i x ty' h_bool h_1 h_2 heq
    typecheck_split h_1 h_2 h_2 h_1 heq =>
      have := HasTypeA_unique htye1 h_1
      subst_vars
      simp[ih2]
  | eq_false _ h1 h2 hne ih1 ih2 =>
    rename_i bvarVal  _ _ _ _ htye1 htye2 _ _ _
    unfold LExpr.denote
    simp only [HasTypeA.eq_inv]
    split
    rename_i x ty' h_bool h_1 h_2 heq
    typecheck_split h_1 h_2 h_2 h_1 heq =>
      have := HasTypeA_unique htye1 h_1
      subst_vars
      simp[hne]
  | quant_all_true _ hall ih =>
    unfold LExpr.denote; simp only [HasTypeA.quant_inv]
    split; rename_i x τ_tr h_bool h_tr h_body heq
    typecheck_split h_body h_body h_body h_tr heq =>
      simp [fun x => (ih x).symm]
  | quant_all_false _ w hbody ih =>
    unfold LExpr.denote; simp only [HasTypeA.quant_inv]
    split; rename_i x τ_tr h_bool h_tr h_body heq
    typecheck_split h_body h_body h_body h_tr heq =>
      apply Eq.symm; rw [decide_eq_false_iff_not]
      intro hall; have := (hall w).symm.trans ih.symm; contradiction
  | quant_exist_true _ w hbody ih =>
    unfold LExpr.denote; simp only [HasTypeA.quant_inv]
    split; rename_i x τ_tr h_bool h_tr h_body heq
    typecheck_split h_body h_body h_body h_tr heq =>
      have hexists : ∃ x, LExpr.denote tcInterp opInterp fvarVal vt (.cons x _) _ .bool h_body = true :=
        ⟨w, ih.symm⟩
      simp [hexists]
  | quant_exist_false _ hall ih =>
    unfold LExpr.denote; simp only [HasTypeA.quant_inv]
    split; rename_i x τ_tr h_bool h_tr h_body heq
    typecheck_split h_body h_body h_body h_tr heq =>
      apply Eq.symm; rw [decide_eq_false_iff_not]
      intro ⟨w, hw⟩; have := hw.symm.trans (ih w).symm; contradiction

/-! ### Unfolding lemmas for `denote`

These lemmas expose the structure of `denote` for each expression form,
proved via `Denotes` to avoid dependent-type casts from the `_inv` lemmas. -/

/-- Unfolding lemma for `denote` of a constant. -/
theorem denote_const
    {T : LExprParams}
    (tcInterp : TyConstrInterp)
    (opInterp : OpInterp tcInterp)
    (fvarVal : FreeVarVal T tcInterp)
    (vt : TyVarVal)
    {m : T.mono.base.Metadata} {c : LConst} {τ : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h : LExpr.HasTypeA Δ (.const m c) τ)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.const m c) τ h =
      HasTypeA.const_inv h ▸ denoteConst tcInterp vt c := by rfl

/-- Unfolding lemma for `denote` of a bound variable. -/
theorem denote_op
    {T : LExprParams}
    (tcInterp : TyConstrInterp)
    (opInterp : OpInterp tcInterp)
    (fvarVal : FreeVarVal T tcInterp)
    (vt : TyVarVal)
    {m : T.mono.base.Metadata} {o : T.Identifier} {ty : LMonoTy} {τ : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h : LExpr.HasTypeA Δ (.op m o (some ty)) τ)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.op m o (some ty)) τ h =
      HasTypeA.op_inv h ▸ opInterp o.name (ty.substTyVars vt) := by rfl

theorem denote_fvar
    {T : LExprParams}
    (tcInterp : TyConstrInterp)
    (opInterp : OpInterp tcInterp)
    (fvarVal : FreeVarVal T tcInterp)
    (vt : TyVarVal)
    {m : T.mono.base.Metadata} {name : T.Identifier} {ty : LMonoTy} {τ : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h : LExpr.HasTypeA Δ (.fvar m name (some ty)) τ)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.fvar m name (some ty)) τ h =
      HasTypeA.fvar_inv h ▸ fvarVal name (ty.substTyVars vt) := by rfl

theorem denote_bvar
    {T : LExprParams}
    (tcInterp : TyConstrInterp)
    (opInterp : OpInterp tcInterp)
    (fvarVal : FreeVarVal T tcInterp)
    (vt : TyVarVal)
    {m : T.mono.base.Metadata} {i : Nat} {τ : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h : LExpr.HasTypeA Δ (.bvar m i) τ)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.bvar m i) τ h =
      bvarVal.get i (HasTypeA.bvar_inv h) := by rfl

/-- Unfolding lemma for `denote` of an application. -/
theorem denote_app
    {T : LExprParams}
    {tcInterp : TyConstrInterp}
    {opInterp : OpInterp tcInterp}
    {fvarVal : FreeVarVal T tcInterp}
    {vt : TyVarVal}
    {m : T.Metadata} {fn arg : LExpr T.mono} {aty τ : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h_fn : LExpr.HasTypeA Δ fn (.arrow aty τ))
    (h_arg : LExpr.HasTypeA Δ arg aty)
    (h_app : LExpr.HasTypeA Δ (.app m fn arg) τ)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.app m fn arg) τ h_app =
      (LExpr.denote tcInterp opInterp fvarVal vt bvarVal fn (.arrow aty τ) h_fn)
        (LExpr.denote tcInterp opInterp fvarVal vt bvarVal arg aty h_arg) := by
  have hd_fn := denote_Denotes tcInterp opInterp fvarVal vt bvarVal fn (.arrow aty τ) h_fn
  have hd_arg := denote_Denotes tcInterp opInterp fvarVal vt bvarVal arg aty h_arg
  have hd_app := Denotes.app bvarVal (h := h_app) hd_fn hd_arg
  exact (Denotes_denote hd_app).symm

/-- Unfolding lemma for `denote` of an abstraction. -/
theorem denote_abs
    {T : LExprParams}
    {tcInterp : TyConstrInterp}
    {opInterp : OpInterp tcInterp}
    {fvarVal : FreeVarVal T tcInterp}
    {vt : TyVarVal}
    {m : T.Metadata} {name : String} {body : LExpr T.mono} {aty rty : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h_body : LExpr.HasTypeA (aty :: Δ) body rty)
    (h_abs : LExpr.HasTypeA Δ (.abs m name (some aty) body) (.arrow aty rty))
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal
        (.abs m name (some aty) body) (.arrow aty rty) h_abs =
      fun x => LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body rty h_body := by
  have hd_body : ∀ x, Denotes tcInterp opInterp fvarVal vt (.cons x bvarVal) body rty h_body
      (LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body rty h_body) :=
    fun x => denote_Denotes tcInterp opInterp fvarVal vt (.cons x bvarVal) body rty h_body
  have hd_abs := Denotes.abs bvarVal (h := h_abs) hd_body
  exact (Denotes_denote hd_abs).symm

/-- Unfolding lemma for `denote` of `eq` when operands are equal. -/
theorem denote_eq_true
    {T : LExprParams}
    {tcInterp : TyConstrInterp}
    {opInterp : OpInterp tcInterp}
    {fvarVal : FreeVarVal T tcInterp}
    {vt : TyVarVal}
    {m : T.Metadata} {e1 e2 : LExpr T.mono} {ty' : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h_1 : LExpr.HasTypeA Δ e1 ty')
    (h_2 : LExpr.HasTypeA Δ e2 ty')
    (h_eq : LExpr.HasTypeA Δ (.eq m e1 e2) .bool)
    (heq : LExpr.denote tcInterp opInterp fvarVal vt bvarVal e1 ty' h_1 =
           LExpr.denote tcInterp opInterp fvarVal vt bvarVal e2 ty' h_2)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.eq m e1 e2) .bool h_eq = true := by
  have hd1 := denote_Denotes tcInterp opInterp fvarVal vt bvarVal e1 ty' h_1
  have hd2 := denote_Denotes tcInterp opInterp fvarVal vt bvarVal e2 ty' h_2
  rw [heq] at hd1
  exact (Denotes_denote (Denotes.eq_true bvarVal (h := h_eq) hd1 hd2)).symm

/-- Unfolding lemma for `denote` of `eq` when operands are not equal. -/
theorem denote_eq_false
    {T : LExprParams}
    {tcInterp : TyConstrInterp}
    {opInterp : OpInterp tcInterp}
    {fvarVal : FreeVarVal T tcInterp}
    {vt : TyVarVal}
    {m : T.Metadata} {e1 e2 : LExpr T.mono} {ty' : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h_1 : LExpr.HasTypeA Δ e1 ty')
    (h_2 : LExpr.HasTypeA Δ e2 ty')
    (h_eq : LExpr.HasTypeA Δ (.eq m e1 e2) .bool)
    (hne : LExpr.denote tcInterp opInterp fvarVal vt bvarVal e1 ty' h_1 ≠
           LExpr.denote tcInterp opInterp fvarVal vt bvarVal e2 ty' h_2)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.eq m e1 e2) .bool h_eq = false := by
  have hd1 := denote_Denotes tcInterp opInterp fvarVal vt bvarVal e1 ty' h_1
  have hd2 := denote_Denotes tcInterp opInterp fvarVal vt bvarVal e2 ty' h_2
  exact (Denotes_denote (Denotes.eq_false bvarVal (h := h_eq) hd1 hd2 hne)).symm

/-- Unfolding lemma for `denote` of an `ite`. -/
theorem denote_ite
    {T : LExprParams}
    {tcInterp : TyConstrInterp}
    {opInterp : OpInterp tcInterp}
    {fvarVal : FreeVarVal T tcInterp}
    {vt : TyVarVal}
    {m : T.Metadata} {c t e : LExpr T.mono} {τ : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h_c : LExpr.HasTypeA Δ c .bool)
    (h_t : LExpr.HasTypeA Δ t τ)
    (h_e : LExpr.HasTypeA Δ e τ)
    (h_ite : LExpr.HasTypeA Δ (.ite m c t e) τ)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.ite m c t e) τ h_ite =
      bif LExpr.denote tcInterp opInterp fvarVal vt bvarVal c .bool h_c
      then LExpr.denote tcInterp opInterp fvarVal vt bvarVal t τ h_t
      else LExpr.denote tcInterp opInterp fvarVal vt bvarVal e τ h_e := by
  cases hb : LExpr.denote tcInterp opInterp fvarVal vt bvarVal c .bool h_c with
  | true =>
    simp
    have hd_c := denote_Denotes tcInterp opInterp fvarVal vt bvarVal c .bool h_c
    rw [hb] at hd_c
    have hd_t := denote_Denotes tcInterp opInterp fvarVal vt bvarVal t τ h_t
    have hd_ite := Denotes.ite_true bvarVal (h := h_ite) hd_c hd_t
    exact (Denotes_denote hd_ite).symm
  | false =>
    simp
    have hd_c := denote_Denotes tcInterp opInterp fvarVal vt bvarVal c .bool h_c
    rw [hb] at hd_c
    have hd_e := denote_Denotes tcInterp opInterp fvarVal vt bvarVal e τ h_e
    have hd_ite := Denotes.ite_false bvarVal (h := h_ite) hd_c hd_e
    exact (Denotes_denote hd_ite).symm

/-- Unfolding lemma for `denote` of `quant .all` when the body is true for all values. -/
theorem denote_quant_all_true
    {T : LExprParams}
    {tcInterp : TyConstrInterp}
    {opInterp : OpInterp tcInterp}
    {fvarVal : FreeVarVal T tcInterp}
    {vt : TyVarVal}
    {m : T.Metadata} {name : String} {tr body : LExpr T.mono} {qty : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h_body : LExpr.HasTypeA (qty :: Δ) body .bool)
    (h_quant : LExpr.HasTypeA Δ (.quant m .all name (some qty) tr body) .bool)
    (hall : ∀ x : TyDenote tcInterp vt qty,
      (LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body : Bool) = true)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal
        (.quant m .all name (some qty) tr body) .bool h_quant = true := by
  have hd := Denotes.quant_all_true bvarVal (h := h_quant) fun x =>
    hall x ▸ denote_Denotes tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body
  exact (Denotes_denote hd).symm

/-- Unfolding lemma for `denote` of `quant .all` when the body is false for some value. -/
theorem denote_quant_all_false
    {T : LExprParams}
    {tcInterp : TyConstrInterp}
    {opInterp : OpInterp tcInterp}
    {fvarVal : FreeVarVal T tcInterp}
    {vt : TyVarVal}
    {m : T.Metadata} {name : String} {tr body : LExpr T.mono} {qty : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h_body : LExpr.HasTypeA (qty :: Δ) body .bool)
    (h_quant : LExpr.HasTypeA Δ (.quant m .all name (some qty) tr body) .bool)
    (w : TyDenote tcInterp vt qty)
    (hw : (LExpr.denote tcInterp opInterp fvarVal vt (.cons w bvarVal) body .bool h_body : Bool) = false)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal
        (.quant m .all name (some qty) tr body) .bool h_quant = false := by
  have hd := Denotes.quant_all_false bvarVal (h := h_quant) w
    (hw ▸ denote_Denotes tcInterp opInterp fvarVal vt (.cons w bvarVal) body .bool h_body)
  exact (Denotes_denote hd).symm

/-- Unfolding lemma for `denote` of `quant .exist` when the body is true for some value. -/
theorem denote_quant_exist_true
    {T : LExprParams}
    {tcInterp : TyConstrInterp}
    {opInterp : OpInterp tcInterp}
    {fvarVal : FreeVarVal T tcInterp}
    {vt : TyVarVal}
    {m : T.Metadata} {name : String} {tr body : LExpr T.mono} {qty : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h_body : LExpr.HasTypeA (qty :: Δ) body .bool)
    (h_quant : LExpr.HasTypeA Δ (.quant m .exist name (some qty) tr body) .bool)
    (w : TyDenote tcInterp vt qty)
    (hw : (LExpr.denote tcInterp opInterp fvarVal vt (.cons w bvarVal) body .bool h_body : Bool) = true)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal
        (.quant m .exist name (some qty) tr body) .bool h_quant = true := by
  have hd := Denotes.quant_exist_true bvarVal (h := h_quant) w
    (hw ▸ denote_Denotes tcInterp opInterp fvarVal vt (.cons w bvarVal) body .bool h_body)
  exact (Denotes_denote hd).symm

/-- Unfolding lemma for `denote` of `quant .exist` when the body is false for all values. -/
theorem denote_quant_exist_false
    {T : LExprParams}
    {tcInterp : TyConstrInterp}
    {opInterp : OpInterp tcInterp}
    {fvarVal : FreeVarVal T tcInterp}
    {vt : TyVarVal}
    {m : T.Metadata} {name : String} {tr body : LExpr T.mono} {qty : LMonoTy} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h_body : LExpr.HasTypeA (qty :: Δ) body .bool)
    (h_quant : LExpr.HasTypeA Δ (.quant m .exist name (some qty) tr body) .bool)
    (hall : ∀ x : TyDenote tcInterp vt qty,
      (LExpr.denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body : Bool) = false)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal
        (.quant m .exist name (some qty) tr body) .bool h_quant = false := by
  have hd := Denotes.quant_exist_false bvarVal (h := h_quant) fun x =>
    (hall x) ▸ denote_Denotes tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body
  exact (Denotes_denote hd).symm

/-! ### Factory-consistent interpretations

We define what it means for an `opInterp` to be *consistent* with a factory:
for every function that has a body, the interpretation of the op applied to
argument values equals the denotation of the body under a valuation that maps
the formal parameters to those argument values. -/

section FactoryConsistent

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp tcInterp)

/-- Apply a curried `SortDenote` value of iterated-arrow sort to an `HList`
of argument values. -/
def SortDenote.applyArgs
    : {args : List LSort} → {ret : LSort} →
      SortDenote tcInterp (LSort.mkArrow ret args) →
      HList (SortDenote tcInterp) args →
      SortDenote tcInterp ret
  | [], _, f, .nil => f
  | _ :: _, _, f, .cons x xs => applyArgs (f x) xs

/-- An `opInterp` is consistent with an `LFunc` whose definition is given by
`body`: for every choice of argument values, the interpretation of the op
applied to those arguments equals the denotation of the body under the
valuation that maps the formal parameters to those arguments. -/
def LFunc.InterpConsistentBody [DecidableEq T.IDMeta]
    (f : LFunc T) (body : LExpr T.mono) : Prop :=
  ∀ (vt : TyVarVal)
    (fvarVal : FreeVarVal T tcInterp),
  let bindings : List (Identifier T.IDMeta × LSort) :=
    f.inputs.map (fun (id, ty) => (id, LMonoTy.substTyVars vt ty))
  let inputSorts := bindings.map Prod.snd
  let outputSort := LMonoTy.substTyVars vt f.output
  let fullSort := LSort.mkArrow outputSort inputSorts
  ∀ (h_body : LExpr.HasTypeA [] body f.output)
    (args : HList (SortDenote tcInterp) inputSorts),
    SortDenote.applyArgs tcInterp (opInterp f.name.name fullSort) args =
    LExpr.denote tcInterp opInterp
      (fvarVal.withArgs bindings args)
      vt .nil body f.output h_body

/-- Denote a list of well-typed expressions into an `HList` of semantic values. -/
noncomputable def denoteArgs
    (fvarVal : FreeVarVal T tcInterp) (vt : TyVarVal)
    {Δ : List LMonoTy} (bvarVal : BVarVal tcInterp vt Δ) :
    (argExprs : List (LExpr T.mono)) → (tys : List LMonoTy)  →
      List.Forall₂ (LExpr.HasTypeA Δ) argExprs tys →
      HList (SortDenote tcInterp) (tys.map (LMonoTy.substTyVars vt))
  | [], [], _ => .nil
  | e :: es, ty :: tys, h =>
    .cons (LExpr.denote tcInterp opInterp fvarVal vt bvarVal e ty h.head)
          (denoteArgs fvarVal vt bvarVal es tys h.tail)

/-- An `opInterp` is consistent with an `LFunc` whose definition is given by
a `concreteEval` function: whenever `ceval md argExprs = some resultExpr` and
all expressions are well-typed, the denotation of the result equals the
interpretation of the op applied to the denotations of the arguments. -/
def LFunc.InterpConsistentEval [DecidableEq T.IDMeta]
    (f : LFunc T) (ceval : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono)) : Prop :=
  ∀ (vt : TyVarVal)
    (fvarVal : FreeVarVal T tcInterp)
    (md : T.Metadata)
    (argExprs : List (LExpr T.mono))
    (resultExpr : LExpr T.mono),
  ceval md argExprs = some resultExpr →
  let inputTys := List.map Prod.snd f.inputs
  let inputSorts := inputTys.map (LMonoTy.substTyVars vt)
  let outputSort := LMonoTy.substTyVars vt f.output
  let fullSort := LSort.mkArrow outputSort inputSorts
  ∀ (h_args : List.Forall₂ (LExpr.HasTypeA []) argExprs inputTys)
    (h_result : LExpr.HasTypeA [] resultExpr f.output),
  LExpr.denote tcInterp opInterp fvarVal vt .nil resultExpr f.output h_result =
    SortDenote.applyArgs tcInterp (opInterp f.name.name fullSort)
      (denoteArgs tcInterp opInterp fvarVal vt .nil argExprs inputTys h_args)

/-- Every fvar in `e` whose name is in `tyMap` is annotated with the
corresponding type. -/
def fvars_annotated_by [DecidableEq T.IDMeta]
    (tyMap : Map T.Identifier LMonoTy) : LExpr T.mono → Prop
  | .fvar _ name (some ty) =>
    ∀ ty', Map.find? tyMap name = some ty' → ty = ty'
  | .fvar _ _ none => False
  | .const _ _ => True
  | .bvar _ _ => True
  | .op _ _ _ => True
  | .app _ fn arg => fvars_annotated_by tyMap fn ∧ fvars_annotated_by tyMap arg
  | .abs _ _ _ body => fvars_annotated_by tyMap body
  | .ite _ c t e => fvars_annotated_by tyMap c ∧ fvars_annotated_by tyMap t ∧ fvars_annotated_by tyMap e
  | .eq _ e1 e2 => fvars_annotated_by tyMap e1 ∧ fvars_annotated_by tyMap e2
  | .quant _ _ _ _ tr body => fvars_annotated_by tyMap tr ∧ fvars_annotated_by tyMap body

/-- A factory is well-typed when every function body type-checks at the
function's declared output type. -/
def Factory.WellTyped [DecidableEq T.IDMeta] (F : @Factory T) : Prop :=
  ∀ (f : String), (hf : f ∈ F) → ∀ body, (F[f]).body = some body →
    LExpr.HasTypeA [] body (F[f]).output ∧
    fvars_annotated_by (F[f]).inputs body

/-- A factory is consistent with an `opInterp` when every function with a body
is `InterpConsistentBody` and every function with a `concreteEval` is
`InterpConsistentEval`. -/
def Factory.InterpConsistent [DecidableEq T.IDMeta] (F : @Factory T) : Prop :=
  (∀ (f : String), (hf : f ∈ F) → ∀ body, (F[f]).body = some body →
    LFunc.InterpConsistentBody tcInterp opInterp (F[f]) body) ∧
  (∀ (f : String), (hf : f ∈ F) → ∀ ceval, (F[f]).concreteEval = some ceval →
    LFunc.InterpConsistentEval tcInterp opInterp (F[f]) ceval)

end FactoryConsistent

section EnvConsistent

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp tcInterp)

/-- A free-variable valuation `fvarVal` is consistent with an environment `env`
when every binding `env x = some e` that is well-typed at `ty` denotes to the
same value as `fvarVal x (substTyVars vt ty)`. -/
def Env.InterpConsistent (env : T.Identifier → Option (LExpr T.mono)) (fvarVal : FreeVarVal T tcInterp) : Prop :=
  ∀ (vt : TyVarVal) (x : T.Identifier) (e : LExpr T.mono) (ty : LMonoTy),
    env x = some e →
    ∀ (h : LExpr.HasTypeA [] e ty),
      LExpr.denote tcInterp opInterp fvarVal vt .nil e ty h = fvarVal x (ty.substTyVars vt)

end EnvConsistent

end Lambda
