/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.DL.Lambda.Factory
meta import Init.Grind.Cases
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Strata.DL.Util.HList

/-!
## Core Denotational Semantics

Defines the `denote` function and the relational `Denotes` predicate mapping
well-typed lambda expressions to Lean values. `Denotes` is used to prove
correct unfolding lemmas for `denote` that minimize exposure to dependent types.
Also defines interpretation structures (`OpInterp`, `IdentInterp`,
`Factory.InterpConsistent`, etc.) and satisfaction/validity.

- `LExpr.denote` — denotation function for well-typed expressions
- `Denotes` — relational specification of `denote`
- `denote_Denotes` / `Denotes_denote` — soundness and completeness of `Denotes` w.r.t. `denote`
- `Interp` / `Satisfiable` / `Valid` / `LogConseq` — semantic notions over consistent interpretations
-/

namespace Lambda

/-! ### Sorts and Type Denotation -/

/-- A sort is a ground monomorphic type — an `LMonoTy` with no free type
variables. We use a separate type rather than `LMonoTy` to avoid carrying
around proofs that a type has no type variables. -/
public inductive LSort where
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

def LSort.rec' (P : LSort → Sort u)
    (htcons : ∀ name args, (∀ x, x ∈ args → P x) → P (.tcons name args))
    (hbitvec : ∀ n, P (.bitvec n)) : ∀ s, P s
  | .tcons name args => htcons name args (fun x _ => rec' P htcons hbitvec x)
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
@[expose] public def LSort.mkArrow (ret : LSort) : List LSort → LSort
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
sort arguments to a Lean `Type`.

A `TyConstrInterp` is total, so every constructor name is interpreted. Three
kinds of type constructors may be encountered:
1. Defined type constructors (ADTs in the `TypeFactory`): their interpretation
   is constrained by `Factory.ConstrInterpConsistent` together with
   `Factory.ConstrWellFormed` (see `Assumptions.lean`).
2. Uninterpreted type constructors: their interpretation is arbitrary; proofs
   must hold for any interpretation.
3. Type constructors not appearing in any Core program: by typing, these never
   appear in proof goals we care about, so their interpretation may be chosen
   arbitrarily (e.g. `Unit`). -/
@[expose] public def TyConstrInterp := String → List LSort → Type

/-- Every type produced by a `TyConstrInterp` is inhabited. This holds for
inductive datatypes defined in Core because `adt_inhab` ensures the existence
of an inhabited constructor. -/
class TyConstrInterp.AllInhabited (tcInterp : TyConstrInterp) : Type where
  inhabited : ∀ name args, Inhabited (tcInterp name args)

/-- Interpret a sort into a Lean `Type`. Built-in sorts (bool, int, real,
string, bitvec, arrow) are mapped to their Lean counterparts; all others
are delegated to `tcInterp`. -/
@[expose] public def SortDenote (tcInterp : TyConstrInterp) : LSort → Type
  | .tcons "bool" []      => Bool
  | .tcons "int" []       => Int
  | .tcons "real" []      => Rat
  | .tcons "string" []    => String
  | .bitvec n             => BitVec n
  | .tcons "arrow" [a, b] => SortDenote tcInterp a → SortDenote tcInterp b
  | .tcons name args      => tcInterp name args

/--
Every sort denotes an inhabited type, given that the type constructor
interpretation produces inhabited types.
-/
@[reducible]
def SortDenote.inhabited (tcInterp : TyConstrInterp)
    (h : ∀ name args, Inhabited (tcInterp name args))
    (s : LSort) : Inhabited (SortDenote tcInterp s) := by
  induction s using LSort.rec' with
  | htcons name args ih =>
    unfold SortDenote
    split
    · exact ⟨false⟩
    · exact ⟨(0 : Int)⟩
    · exact ⟨(0 : Rat)⟩
    · exact ⟨""⟩
    . rename_i n _; exact ⟨(0 : BitVec n)⟩
    · exact ⟨fun _ => (ih _ (by simp_all)).default⟩
    · exact h _ _
  | hbitvec n => exact ⟨(0 : BitVec n)⟩

instance SortDenote.instInhabited [TyConstrInterp.AllInhabited tcInterp]
    (s : LSort) : Inhabited (SortDenote tcInterp s) :=
  SortDenote.inhabited tcInterp TyConstrInterp.AllInhabited.inhabited s

/-- Type-variable valuation: maps each type variable to a sort. This is a total
function; type variables that do not appear in the term's type may be assigned
any sort (e.g. `int`) since their value will never be used. -/
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

/-! ### Interpreting Free Variables and Operators -/

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
(vary per context), enabling change-of-valuation theorems.

Noncomputable due to `Classical.propDecidable` in the `eq` and `quant`
cases; used only for reasoning, not computation. -/
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
  | .quant _ k _ (some qty) tr body =>
    let ⟨_τ_tr, h_bool, _h_tr, h_body⟩ := HasTypeA.quant_inv h
    let pred := fun x : TyDenote tcInterp vt qty =>
      (denote tcInterp opInterp fvarVal vt (.cons x bvarVal) body .bool h_body : Bool) = true
    h_bool ▸ (Classical.propDecidable
      (match k with | .all => ∀ x, pred x | .exist => ∃ x, pred x)
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
      apply Eq.symm
      apply decide_eq_false_iff_not.mpr
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
      apply Eq.symm
      apply decide_eq_false_iff_not.mpr
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

theorem denote_intConst
    {T : LExprParams}
    (tcInterp : TyConstrInterp)
    (opInterp : OpInterp tcInterp)
    (fvarVal : FreeVarVal T tcInterp)
    (vt : TyVarVal)
    {m : T.mono.base.Metadata} {i : Int} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h : LExpr.HasTypeA Δ (.const m (.intConst i)) (.tcons "int" []))
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.const m (.intConst i)) (.tcons "int" []) h = i := by
  rw [denote_const]; simp [denoteConst]

theorem denote_boolConst
    {T : LExprParams}
    (tcInterp : TyConstrInterp)
    (opInterp : OpInterp tcInterp)
    (fvarVal : FreeVarVal T tcInterp)
    (vt : TyVarVal)
    {m : T.mono.base.Metadata} {b : Bool} {Δ : List LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h : LExpr.HasTypeA Δ (.const m (.boolConst b)) (.tcons "bool" []))
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal (.const m (.boolConst b)) (.tcons "bool" []) h = b := by
  rw [denote_const]; simp [denoteConst]

/-- Unfolding lemma for `denote` of an operator. -/
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

/-- Unfolding lemma for `denote` of a free variable. -/
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

/-- Unfolding lemma for `denote` of a bound variable. -/
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
all expressions are well-typed at the instantiated types (via a type
substitution `tySubst`), the denotation of the result equals the
interpretation of the op applied to the denotations of the arguments. -/
def LFunc.InterpConsistentEval [DecidableEq T.IDMeta]
    (f : LFunc T) (ceval : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono)) : Prop :=
  ∀ (vt : TyVarVal)
    (fvarVal : FreeVarVal T tcInterp)
    (md : T.Metadata)
    (tySubst : Subst)
    (argExprs : List (LExpr T.mono))
    (resultExpr : LExpr T.mono),
  ceval md argExprs = some resultExpr →
  let instInputTys := (List.map Prod.snd f.inputs).map (LMonoTy.subst tySubst)
  let instOutputTy := LMonoTy.subst tySubst f.output
  let inputSorts := instInputTys.map (LMonoTy.substTyVars vt)
  let outputSort := LMonoTy.substTyVars vt instOutputTy
  let fullSort := LSort.mkArrow outputSort inputSorts
  ∀ (h_args : List.Forall₂ (LExpr.HasTypeA []) argExprs instInputTys)
    (h_result : LExpr.HasTypeA [] resultExpr instOutputTy),
  LExpr.denote tcInterp opInterp fvarVal vt .nil resultExpr instOutputTy h_result =
    SortDenote.applyArgs tcInterp (opInterp f.name.name fullSort)
      (denoteArgs tcInterp opInterp fvarVal vt .nil argExprs instInputTys h_args)

end FactoryConsistent

section FactoryInterpConsistent

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp tcInterp)

/-- A factory is consistent with an `opInterp` when every function with a body
is `InterpConsistentBody` and every function with a `concreteEval` is
`InterpConsistentEval`. -/
def Factory.InterpConsistent [DecidableEq T.IDMeta] (F : @Factory T) : Prop :=
  (∀ (f : String), (hf : f ∈ F) → ∀ body, (F[f]).body = some body →
    LFunc.InterpConsistentBody tcInterp opInterp (F[f]) body) ∧
  (∀ (f : String), (hf : f ∈ F) → ∀ ceval, (F[f]).concreteEval = some ceval →
    LFunc.InterpConsistentEval tcInterp opInterp (F[f]) ceval)

end FactoryInterpConsistent

section ConstrConsistent

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp tcInterp)

/-! ### ADT Interpretation Consistency

These properties express that the semantic interpretation (`opInterp`) of
datatype constructors satisfies the standard algebraic datatype axioms:
disjointness and injectivity. Note that this is NOT complete: there are two
other properties ADT interpretations should have:
1. an inversion principle asserting that we can produce the constructor and
arguments that give rise to a given ADT interpretation instance
2. a generalized induction principle (this justifies recursive functions
over these types)

TODO: add these properties as they are needed

Note that this approach involves axiomatizing ADTs rather than representing
them as inductive types in Lean. See Section 5 of
https://dl.acm.org/doi/10.1145/3632902 for an explanation of this method
and a demonstration of how one could provide models for the axioms.
-/

/-- ADT interpretation consistency: the semantic interpretation of constructors
satisfies disjointness and injectivity.-/
structure ConstrInterpConsistent
    (F : @Factory T) : Prop where
  /-- Constructor disjointness (global): two constructor functions with
  different names, when fully applied, produce different values, provided
  their result sorts are equal. This is required to ensure that we can
  distinguish the intepretations of different ADT instances when checking
  equality. This is sound: there are an infinite number of isomorphic
  inductive types in Lean.-/
  constr_disjoint :
    ∀ (f1 f2 : LFunc T),
      f1 ∈ F.toArray → f2 ∈ F.toArray →
      f1.isConstr = true → f2.isConstr = true →
      f1.name.name ≠ f2.name.name →
      ∀ (vt : TyVarVal),
        let inputSorts1 := f1.inputs.values.map (LMonoTy.substTyVars vt)
        let inputSorts2 := f2.inputs.values.map (LMonoTy.substTyVars vt)
        let outputSort1 := LMonoTy.substTyVars vt f1.output
        let outputSort2 := LMonoTy.substTyVars vt f2.output
        let fullSort1 := LSort.mkArrow outputSort1 inputSorts1
        let fullSort2 := LSort.mkArrow outputSort2 inputSorts2
        ∀ (heq : outputSort1 = outputSort2)
          (args1 : HList (SortDenote tcInterp) inputSorts1)
          (args2 : HList (SortDenote tcInterp) inputSorts2),
          heq ▸ SortDenote.applyArgs tcInterp (opInterp f1.name.name fullSort1) args1 ≠
          SortDenote.applyArgs tcInterp (opInterp f2.name.name fullSort2) args2
  /-- A2. Constructor injectivity: a constructor function is injective in its
  arguments. -/
  constr_injective :
    ∀ (f : LFunc T),
      f ∈ F.toArray →
      f.isConstr = true →
      ∀ (vt : TyVarVal),
        let inputSorts := f.inputs.values.map (LMonoTy.substTyVars vt)
        let outputSort := LMonoTy.substTyVars vt f.output
        let fullSort := LSort.mkArrow outputSort inputSorts
        ∀ (args1 args2 : HList (SortDenote tcInterp) inputSorts),
          SortDenote.applyArgs tcInterp (opInterp f.name.name fullSort) args1 =
          SortDenote.applyArgs tcInterp (opInterp f.name.name fullSort) args2 →
          args1 = args2

end ConstrConsistent



/-! ### Interpretations, Satisfiability, and Validity

An `Interp` bundles a type-constructor interpretation and an operator
interpretation together with proofs that the interpretation is consistent
with a given factory: function bodies denote correctly and constructor
axioms (disjointness, injectivity) hold. Satisfiability and validity
are defined over consistent interpretations. -/

/-- A consistent interpretation of a factory: bundles `tcInterp` and
`opInterp` with proofs that the interpretation is inhabited, consistent
with function definitions, and respects ADT axioms. -/
structure Interp {T : LExprParams} (F : @Factory T) [DecidableEq T.IDMeta] where
  tcInterp : TyConstrInterp
  opInterp : OpInterp tcInterp
  allInhabited : TyConstrInterp.AllInhabited tcInterp
  interpConsistent : Factory.InterpConsistent tcInterp opInterp F
  constrConsistent : ConstrInterpConsistent tcInterp opInterp F

section Satisfaction

variable {T : LExprParams} [DecidableEq T.IDMeta]
variable {F : @Factory T}

/-- An interpretation satisfies a bool-typed formula `e` when `e` denotes
`true` for *every* type-variable valuation and free-variable valuation.
Non-closed formulas are treated as universally quantified (universal
closure over both type and term variables). -/
def Interp.satisfies (I : Interp F)
    (e : LExpr T.mono)
    (h : LExpr.HasTypeA [] e .bool)
    : Prop :=
  ∀ (vt : TyVarVal) (fvarVal : FreeVarVal T I.tcInterp),
    (LExpr.denote I.tcInterp I.opInterp fvarVal vt .nil e .bool h : Bool) = true

/-- A formula is *satisfiable* if there exists a consistent interpretation
that satisfies it. -/
def Satisfiable (F : @Factory T)
    (e : LExpr T.mono)
    (h : LExpr.HasTypeA [] e .bool)
    : Prop :=
  ∃ (I : Interp F),
    I.satisfies e h

/-- A formula is *valid* if every consistent interpretation satisfies it. -/
def Valid (F : @Factory T)
    (e : LExpr T.mono)
    (h : LExpr.HasTypeA [] e .bool)
    : Prop :=
  ∀ (I : Interp F),
    I.satisfies e h

/-- Logical consequence: `e` is a consequence of `Δ` when every consistent
interpretation that satisfies all formulas in `Δ` also satisfies `e`. -/
def LogConseq (F : @Factory T)
    (Δ : List (LExpr T.mono))
    (hΔ : ∀ d ∈ Δ, LExpr.HasTypeA [] d .bool)
    (e : LExpr T.mono)
    (h : LExpr.HasTypeA [] e .bool)
    : Prop :=
  ∀ (I : Interp F),
    (∀ d (hd : d ∈ Δ), I.satisfies d (hΔ d hd)) →
    I.satisfies e h

end Satisfaction

end Lambda
