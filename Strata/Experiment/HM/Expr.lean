/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Experiment.HM.Ty

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
def freshForAux (names : List String) (k fuel : Nat) : String :=
  match fuel with
  | 0      => s!"_w{k}"  -- fallback, unreachable with enough fuel
  | fuel+1 => let c := s!"_w{k}"
              if c ∈ names then freshForAux names (k+1) fuel else c

/-- Generate a variable name fresh for expression `e`.
    Tries `|freeVarNames e| + 1` candidates, so by pigeonhole one must be fresh. -/
def Expr.freshFor (e : Expr) : String :=
  let names := e.freeVarNames
  freshForAux names 0 (names.length + 1)

end HM
