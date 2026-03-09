/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Util.Tactics

/-! ## Monotypes and Type Schemes for Hindley-Milner

Nat-indexed type variables, type constructors with argument lists,
and type schemes (quantified monotypes). No dependency on Lambda/LTy.
-/

namespace HM

---------------------------------------------------------------------
-- Monotypes
---------------------------------------------------------------------

inductive Ty where
  | var : Nat → Ty
  | con : String → List Ty → Ty
  deriving Inhabited, Repr

mutual
theorem Ty.ind' (P : Ty → Prop)
    (hvar : ∀ n, P (.var n))
    (hcon : ∀ name args, (∀ t, t ∈ args → P t) → P (.con name args)) :
    ∀ t, P t
  | .var n => hvar n
  | .con name args => hcon name args (Ty.ind'_list P hvar hcon args)

theorem Ty.ind'_list (P : Ty → Prop)
    (hvar : ∀ n, P (.var n))
    (hcon : ∀ name args, (∀ t, t ∈ args → P t) → P (.con name args)) :
    ∀ (args: List Ty), ∀ t, t ∈ args → P t
  | [], _, h => by grind
  | a :: as, t, h => by
    cases h with
    | head => exact Ty.ind' P hvar hcon a
    | tail _ h => exact Ty.ind'_list P hvar hcon as t h
end

---------------------------------------------------------------------
-- DecidableEq for Ty (nested List Ty prevents deriving)
---------------------------------------------------------------------

mutual
def Ty.beq : Ty → Ty → Bool
  | .var n, .var m => n == m
  | .con n as, .con m bs => n == m && Ty.beqList as bs
  | _, _ => false

def Ty.beqList : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => a.beq b && Ty.beqList as bs
  | _, _ => false
end

mutual
private theorem Ty.beq_refl : (a : Ty) → a.beq a = true
  | .var n => by simp [Ty.beq]
  | .con n as => by simp [Ty.beq]; exact Ty.beqList_refl as

private theorem Ty.beqList_refl : (as : List Ty) → Ty.beqList as as = true
  | [] => by simp [Ty.beqList]
  | a :: as => by simp [Ty.beqList, Ty.beq_refl a, Ty.beqList_refl as]
end

mutual
private theorem Ty.beq_eq : (a b : Ty) → a.beq b = true → a = b
  | .var n, .var m, h => by simp [Ty.beq] at h; exact congrArg _ h
  | .con n as, .con m bs, h => by
    simp [Ty.beq, Bool.and_eq_true] at h
    obtain ⟨hn, habs⟩ := h
    have := Ty.beqList_eq as bs habs
    subst hn; subst this; rfl
  | .var _, .con _ _, h => by simp [Ty.beq] at h
  | .con _ _, .var _, h => by simp [Ty.beq] at h

private theorem Ty.beqList_eq : (as bs : List Ty) → Ty.beqList as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp [Ty.beqList, Bool.and_eq_true] at h
    have := Ty.beq_eq a b h.1
    have := Ty.beqList_eq as bs h.2
    subst_vars; rfl
  | [], _ :: _, h => by simp [Ty.beqList] at h
  | _ :: _, [], h => by simp [Ty.beqList] at h
end

instance : DecidableEq Ty := fun a b =>
  if h : a.beq b then isTrue (Ty.beq_eq a b h)
  else isFalse (fun h' => by subst h'; exact h (Ty.beq_refl a))

---------------------------------------------------------------------
-- Convenience constructors
---------------------------------------------------------------------

@[match_pattern] def Ty.bool : Ty := .con "bool" []
@[match_pattern] def Ty.int  : Ty := .con "int" []
@[match_pattern] def Ty.arrow (a b : Ty) : Ty := .con "→" [a, b]

---------------------------------------------------------------------
-- Free variables
---------------------------------------------------------------------

def Ty.freeVars : Ty → List Nat
  | .var n => [n]
  | .con _ args => args.attach.flatMap fun ⟨t, _⟩ => t.freeVars
termination_by t => t
decreasing_by term_by_mem

---------------------------------------------------------------------
-- Substitution of a single type variable
---------------------------------------------------------------------

def Ty.substVar (α : Nat) (t: Ty) (τ : Ty) : Ty :=
  match t with
  | .var n => if n = α then τ else .var n
  | .con name args => .con name (args.attach.map fun ⟨t, _⟩ => t.substVar α τ)
termination_by SizeOf.sizeOf t
decreasing_by all_goals (simp_wf; term_by_mem)

---------------------------------------------------------------------
-- Size (for termination arguments)
---------------------------------------------------------------------

mutual
def Ty.size : Ty → Nat
  | .var _ => 1
  | .con _ args => 1 + Ty.sizeList args

def Ty.sizeList : List Ty → Nat
  | [] => 0
  | t :: ts => t.size + Ty.sizeList ts
end

@[simp] theorem Ty.size_var (n : Nat) : (Ty.var n).size = 1 := rfl
@[simp] theorem Ty.size_con (n : String) (args : List Ty) :
    (Ty.con n args).size = 1 + Ty.sizeList args := rfl
@[simp] theorem Ty.sizeList_nil : Ty.sizeList [] = 0 := rfl
@[simp] theorem Ty.sizeList_cons (t : Ty) (ts : List Ty) :
    Ty.sizeList (t :: ts) = t.size + Ty.sizeList ts := rfl

theorem Ty.size_pos (t : Ty) : 0 < t.size := by
  cases t <;> simp [Ty.size]; omega

---------------------------------------------------------------------
-- Max variable index (for freshness)
---------------------------------------------------------------------

def Ty.maxVar : Ty → Nat
  | .var n => n
  | .con _ args => args.attach.foldl (fun acc ⟨t, _⟩ => max acc t.maxVar) 0
termination_by t => t
decreasing_by term_by_mem

---------------------------------------------------------------------
-- Type Schemes
---------------------------------------------------------------------

structure Scheme where
  vars : List Nat
  body : Ty
  deriving Inhabited, Repr, DecidableEq

def Scheme.mono (τ : Ty) : Scheme := ⟨[], τ⟩

def Scheme.isMono (σ : Scheme) : Prop := σ.vars = []

instance : Decidable (Scheme.isMono σ) :=
  inferInstanceAs (Decidable (σ.vars = []))

def Scheme.freeVars (σ : Scheme) : List Nat :=
  σ.body.freeVars.filter (· ∉ σ.vars)

def Scheme.close (α : Nat) (σ : Scheme) : Scheme :=
  ⟨α :: σ.vars, σ.body⟩

def Scheme.open (α : Nat) (τ : Ty) (σ : Scheme) : Scheme :=
  if α ∈ σ.vars then
    ⟨σ.vars.removeAll [α], σ.body.substVar α τ⟩
  else σ

/-- Apply a sequence of `Scheme.open` operations. -/
def Scheme.openAll (subst : List (Nat × Ty)) (σ : Scheme) : Scheme :=
  subst.foldl (fun acc (α, τ) => acc.open α τ) σ

/-- `σ.isInstanceOf τ` means `Scheme.mono τ` is an instance of `σ`:
    there exists a sequence of instantiations yielding `Scheme.mono τ`. -/
def Scheme.isInstanceOf (σ : Scheme) (τ : Ty) : Prop :=
  ∃ subst : List (Nat × Ty),
    σ.openAll subst = Scheme.mono τ

end HM
