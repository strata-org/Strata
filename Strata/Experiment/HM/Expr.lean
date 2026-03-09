/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Experiment.HM.Ty
import Strata.DL.Util.List

/-! ## Expressions for Hindley-Milner (locally nameless) -/

namespace HM

inductive QuantKind where
  | all | exist
  deriving Inhabited, Repr, DecidableEq

inductive Const where
  | bool : Bool → Const
  | int  : Int → Const
  deriving Inhabited, Repr, DecidableEq

inductive Expr where
  | bvar  : Nat → Expr
  | fvar  : String → Expr
  | app   : Expr → Expr → Expr
  | abs   : Expr → Expr
  | op    : String → Expr
  | const : Const → Expr
  | ite   : Expr → Expr → Expr → Expr
  | eq    : Expr → Expr → Expr
  | quant : QuantKind → Expr → Expr
  deriving Inhabited, Repr, DecidableEq

---------------------------------------------------------------------
-- Locally nameless infrastructure
---------------------------------------------------------------------

/-- Open: replace `bvar k` with `fvar x` -/
def Expr.varOpen (k : Nat) (x : String) : Expr → Expr
  | .bvar n       => if n = k then .fvar x else .bvar n
  | .fvar y       => .fvar y
  | .app e₁ e₂   => .app (e₁.varOpen k x) (e₂.varOpen k x)
  | .abs e        => .abs (e.varOpen (k + 1) x)
  | .op s         => .op s
  | .const c      => .const c
  | .ite c t e    => .ite (c.varOpen k x) (t.varOpen k x) (e.varOpen k x)
  | .eq e₁ e₂    => .eq (e₁.varOpen k x) (e₂.varOpen k x)
  | .quant q e  => .quant q (e.varOpen (k + 1) x)

/-- Close: replace `fvar x` with `bvar k` -/
def Expr.varClose (k : Nat) (x : String) : Expr → Expr
  | .bvar n       => .bvar n
  | .fvar y       => if y = x then .bvar k else .fvar y
  | .app e₁ e₂   => .app (e₁.varClose k x) (e₂.varClose k x)
  | .abs e        => .abs (e.varClose (k + 1) x)
  | .op s         => .op s
  | .const c      => .const c
  | .ite c t e    => .ite (c.varClose k x) (t.varClose k x) (e.varClose k x)
  | .eq e₁ e₂    => .eq (e₁.varClose k x) (e₂.varClose k x)
  | .quant q e  => .quant q (e.varClose (k + 1) x)

/-- Locally closed: no dangling bound variables above depth `k` -/
def Expr.lcAt (k : Nat) : Expr → Prop
  | .bvar n       => n < k
  | .fvar _       => True
  | .app e₁ e₂   => e₁.lcAt k ∧ e₂.lcAt k
  | .abs e        => e.lcAt (k + 1)
  | .op _         => True
  | .const _      => True
  | .ite c t e    => c.lcAt k ∧ t.lcAt k ∧ e.lcAt k
  | .eq e₁ e₂    => e₁.lcAt k ∧ e₂.lcAt k
  | .quant _ e  => e.lcAt (k + 1)

def Expr.lc (e : Expr) : Prop := e.lcAt 0

/-- `x` does not occur free in `e` -/
def Expr.fresh (x : String) : Expr → Prop
  | .bvar _       => True
  | .fvar y       => y ≠ x
  | .app e₁ e₂   => e₁.fresh x ∧ e₂.fresh x
  | .abs e        => e.fresh x
  | .op _         => True
  | .const _      => True
  | .ite c t e    => c.fresh x ∧ t.fresh x ∧ e.fresh x
  | .eq e₁ e₂    => e₁.fresh x ∧ e₂.fresh x
  | .quant _ e  => e.fresh x

---------------------------------------------------------------------
-- Structural size (ignores payload, so varOpen preserves it)
---------------------------------------------------------------------

def Expr.size : Expr → Nat
  | .bvar _       => 1
  | .fvar _       => 1
  | .app e₁ e₂   => 1 + e₁.size + e₂.size
  | .abs e        => 1 + e.size
  | .op _         => 1
  | .const _      => 1
  | .ite c t e    => 1 + c.size + t.size + e.size
  | .eq e₁ e₂    => 1 + e₁.size + e₂.size
  | .quant _ e  => 1 + e.size

@[simp] theorem Expr.size_varOpen (k : Nat) (x : String) (e : Expr) :
    (e.varOpen k x).size = e.size := by
  induction e generalizing k with
  | bvar n       => simp [varOpen, size]; split <;> simp [size]
  | fvar _       => rfl
  | app _ _ ih₁ ih₂ => simp [varOpen, size, ih₁, ih₂]
  | abs _ ih     => simp [varOpen, size, ih]
  | op _         => rfl
  | const _      => rfl
  | ite _ _ _ ihc iht ihf => simp [varOpen, size, ihc, iht, ihf]
  | eq _ _ ih₁ ih₂ => simp [varOpen, size, ih₁, ih₂]
  | quant _ _ ih => simp [varOpen, size, ih]

---------------------------------------------------------------------
-- Free variable name collection and fresh name generation
---------------------------------------------------------------------

/-- Collect all free variable names in an expression. -/
def Expr.freeVarNames : Expr → List String
  | .bvar _       => []
  | .fvar x       => [x]
  | .app e₁ e₂   => e₁.freeVarNames ++ e₂.freeVarNames
  | .abs e        => e.freeVarNames
  | .op _         => []
  | .const _      => []
  | .ite c t e    => c.freeVarNames ++ t.freeVarNames ++ e.freeVarNames
  | .eq e₁ e₂    => e₁.freeVarNames ++ e₂.freeVarNames
  | .quant _ e    => e.freeVarNames

/-- Try candidates `"_w0"`, `"_w1"`, ... up to `fuel`, return first not in `names`. -/
def freshForAux (names : List String) (k fuel : Nat) : Option String :=
  match fuel with
  | 0      => none
  | fuel+1 => let c := s!"_w{k}"
              if c ∈ names then freshForAux names (k+1) fuel else some c

/-- Generate a variable name fresh for expression `e`.
    Tries `|freeVarNames e| + 1` candidates, so by pigeonhole one must be fresh. -/
def Expr.freshFor (e : Expr) : String :=
  let names := e.freeVarNames
  (freshForAux names 0 (names.length + 1)).getD "_unreachable"

/-! ### freshForAux correctness -/

-- 1. If freshForAux returns some c, then c ∉ names
theorem freshForAux_some_not_mem (names : List String) (k fuel : Nat) (c : String)
    (h : freshForAux names k fuel = some c) : c ∉ names := by
  induction fuel generalizing k with
  | zero => simp [freshForAux] at h
  | succ fuel ih =>
    simp [freshForAux] at h
    split at h
    · exact ih (k + 1) h
    · cases h; assumption

-- 2. If freshForAux returns none, then all fuel candidates are in names
theorem freshForAux_none_all_mem (names : List String) (k fuel : Nat)
    (h : freshForAux names k fuel = none) :
    ∀ i, i < fuel → s!"_w{k + i}" ∈ names := by
  induction fuel generalizing k with
  | zero => intro i hi; omega
  | succ fuel ih =>
    simp [freshForAux] at h
    split at h
    · rename_i hmem
      intro i hi
      cases i with
      | zero => simp at hmem ⊢; exact hmem
      | succ i =>
        have := ih (k + 1) h i (by omega)
        have hk: (k + (i + 1)) = k + 1 + i := by omega
        rw[hk]; assumption
    · exact absurd h (by simp [Option.some_ne_none])

-- Not in older Lean versions?
@[simp]
theorem String.append_right_inj (s : String) {t₁ t₂ : String} :
    s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ := by
  simp [← String.toByteArray_inj]

-- Helper: the candidates "_w{k}", ..., "_w{k+fuel-1}" are all distinct
private axiom wname_injective (i j : Nat) (h : s!"_w{i}" = s!"_w{j}") : i = j
--  := by
--   rw[String.append_right_inj] at h
--   -- exact Nat.repr_inj.mp h
--   sorry

private theorem candidates_nodup (k fuel : Nat) :
    (List.range fuel |>.map (fun i => s!"_w{k + i}")).Nodup := by
  apply List.Pairwise.map (R := (fun x y => x ≠ y)) (S := (fun x y => x ≠ y)) (fun i => s!"_w{k + i}")
  · intro a b hab
    intro heq
    have := wname_injective _ _ heq
    omega
  · exact List.nodup_range

-- Main: freshForAux with enough fuel always returns some
theorem freshForAux_isSome (names : List String) (k fuel : Nat)
    (hfuel : names.length < fuel) :
    (freshForAux names k fuel).isSome = true := by
  cases hq : freshForAux names k fuel with
  | none =>
    exfalso
    have hall := freshForAux_none_all_mem names k fuel hq
    have hnd := candidates_nodup k fuel
    have hsub : (List.range fuel |>.map (fun i => s!"_w{k + i}")) ⊆ names := by
      intro x hx
      simp [List.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact hall i (List.mem_range.mp (by grind))
    have hle := List.subset_nodup_length hnd hsub
    simp [List.length_map] at hle
    omega
  | some _ => rfl

theorem not_mem_freeVarNames_fresh (x : String) (e : Expr) (h : x ∉ e.freeVarNames) :
    e.fresh x := by
  induction e with
  | bvar _ => trivial
  | fvar y => simp [Expr.freeVarNames, Expr.fresh] at *; grind
  | app _ _ ih₁ ih₂ =>
    simp [Expr.freeVarNames, List.mem_append] at h
    exact ⟨ih₁ h.1, ih₂ h.2⟩
  | abs _ ih => exact ih (by simp [Expr.freeVarNames] at h; exact h)
  | op _ => trivial
  | const _ => trivial
  | ite _ _ _ ihc iht ihf =>
    simp [Expr.freeVarNames, List.mem_append] at h
    exact ⟨ihc h.1, iht h.2.1, ihf h.2.2⟩
  | eq _ _ ih₁ ih₂ =>
    simp [Expr.freeVarNames, List.mem_append] at h
    exact ⟨ih₁ h.1, ih₂ h.2⟩
  | quant _ _ ih => exact ih (by simp [Expr.freeVarNames] at h; exact h)

theorem freshFor_fresh (e : Expr) : e.fresh e.freshFor := by
  simp [Expr.freshFor]
  have hsome := freshForAux_isSome e.freeVarNames 0 (e.freeVarNames.length + 1) (by omega)
  match hq : freshForAux e.freeVarNames 0 (e.freeVarNames.length + 1) with
  | some c =>
    simp [Option.getD]
    exact not_mem_freeVarNames_fresh c e (freshForAux_some_not_mem _ _ _ _ hq)
  | none => simp [hq] at hsome

end HM
