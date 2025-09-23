/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Lambda.LExpr

/-! ## Well-formedness of Lambda Expressions

See the definition `Lambda.LExpr.WF`. Also see theorem `HasType.regularity` in
`Strata.DL.Lambda.LExprTypeSpec`.
-/

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)

namespace LExpr

variable {T : LExprParams}

/--
Compute the free variables in an `LExpr`, which are simply all the `LExpr.fvar`s
in it.
-/
def freeVars (e : LExpr T.mono) : IdentTs T.Identifier :=
  match e with
  | .const _ _ _ => []
  | .op _ _ _ => []
  | .bvar _ _ => []
  | .fvar _ x ty => [(x, ty)]
  | .abs _ _ e1 => freeVars e1
  | .quant _ _ _ tr e1 => freeVars tr ++ freeVars e1
  | .app _ e1 e2 => freeVars e1 ++ freeVars e2
  | .ite _ c t e => freeVars c ++ freeVars t ++ freeVars e
  | .eq _ e1 e2 => freeVars e1 ++ freeVars e2

/--
Is `x` is a fresh variable w.r.t. `e`?
-/
def fresh (x : IdentT T.Identifier) (e : LExpr T.mono) : Prop :=
  x ∉ (freeVars e)

/-- An expression `e` is closed if has no free variables. -/
def closed (e : LExpr T.mono) : Bool :=
  freeVars e |>.isEmpty

@[simp]
theorem fresh_abs {x : IdentT T.Identifier} {m : T.Metadata} {ty : Option LMonoTy} {e : LExpr T.mono} :
  fresh x (.abs m ty e) = fresh x e := by
  simp [fresh, freeVars]

@[simp]
theorem freeVars_abs {m : T.Metadata} {ty : Option LMonoTy} {e : LExpr T.mono} :
  freeVars (.abs m ty e) = freeVars e := by
  simp [freeVars]

@[simp]
theorem closed_abs {m : T.Metadata} {ty : Option LMonoTy} {e : LExpr T.mono} :
  closed (.abs m ty e) = closed e := by
  simp [closed]

---------------------------------------------------------------------

/-! ### Substitutions in `LExpr`s -/

/--
This function replaces some bound variables in `e` by an arbitrary expression
`s` (and `s` may contain some free variables).

`substK k s e` keeps track of the number `k` of abstractions that have passed
by; it replaces all leaves of the form `(.bvar k)` with `s`.
-/
def substK (k : Nat) (s : T.Metadata → LExpr T.mono) (e : LExpr T.mono) : LExpr T.mono :=
  match e with
  | .const m c ty => .const m c ty
  | .op m o ty => .op m o ty
  | .bvar m i => if i == k then s m else .bvar m i
  | .fvar m y ty => .fvar m y ty
  | .abs m ty e' => .abs m ty (substK (k + 1) s e')
  | .quant m qk ty tr' e' => .quant m qk ty (substK (k + 1) s tr') (substK (k + 1) s e')
  | .app m e1 e2 => .app m (substK k s e1) (substK k s e2)
  | .ite m c t e => .ite m (substK k s c) (substK k s t) (substK k s e)
  | .eq m e1 e2 => .eq m (substK k s e1) (substK k s e2)

/--
Substitute the outermost bound variable in `e` by an arbitrary expression `s`.

This function is useful for β-reduction -- the reduction of
`app (abs e) s` can be implemented by `subst s e`. Having a locally nameless
representation allows us to avoid the pitfalls of variable shadowing and
capture. E.g., consider the following, written in the "raw" style of lambda
calculus.

`(λxλy x y) (λa b) --β--> λy (λa b) y`

If we'd used vanilla de Bruijn representation, we'd have the following instead,
where we'd need to shift the index of the free variable `b` to avoid capture:

`(λλ 1 0) (λ 5) --β--> λ (λ 6) 0`

We distinguish between free and bound variables in our notation, which allows us
to avoid such issues:

`(λλ 1 0) (λ b) --β--> (λ (λ b) 0)`
-/
def subst (s : T.Metadata → LExpr T.mono) (e : LExpr T.mono) : LExpr T.mono :=
  substK 0 s e

/--
This function turns some bound variables to free variables to investigate the
body of an abstraction. `varOpen k x e` keeps track of the number `k` of
abstractions that have passed by; it replaces all leaves of the form `(.bvar k)`
with `(.fvar x)`.

Note that `x` is expected to be a fresh variable w.r.t. `e`.
-/
def varOpen (k : Nat) (x : IdentT T.Identifier) (e : LExpr T.mono) : LExpr T.mono :=
  substK k (fun m => .fvar m x.fst x.snd) e

/--
This function turns some free variables into bound variables to build an
abstraction, given its body. `varClose k x e` keeps track of the number `k`
of abstractions that have passed by; it replaces all `(.fvar x)` with
`(.bvar k)`.
-/
def varClose [BEq T.Identifier] (k : Nat) (x : IdentT T.Identifier) (e : LExpr T.mono) : LExpr T.mono :=
  match e with
  | .const m c ty => .const m c ty
  | .op m o ty => .op m o ty
  | .bvar m i => .bvar m i
  | .fvar m y (yty: Option LMonoTy) => if (x.fst == y) && (yty == x.snd) then
                      (.bvar m k) else (.fvar m y yty)
  | .abs m ty e' => .abs m ty (varClose (k + 1) x e')
  | .quant m qk ty tr' e' => .quant m qk ty (varClose (k + 1) x tr') (varClose (k + 1) x e')
  | .app m e1 e2 => .app m (varClose k x e1) (varClose k x e2)
  | .ite m c t e => .ite m (varClose k x c) (varClose k x t) (varClose k x e)
  | .eq m e1 e2 => .eq m (varClose k x e1) (varClose k x e2)


theorem varClose_of_varOpen [BEq T.Identifier] [ReflBEq T.Identifier] [LawfulBEq T.Identifier] [BEq T.Metadata] [ReflBEq T.Metadata] [ReflBEq LMonoTy] [LawfulBEq LMonoTy] {x : IdentT T.Identifier} {e : LExpr T.mono} {i : Nat} (h : fresh x e) :
  varClose (T := T) i x (varOpen i x e) = e := by
  induction e generalizing i x
  all_goals try simp_all [fresh, varOpen, LExpr.substK, varClose, freeVars]
  case bvar j =>
    by_cases hi : j = i <;>
    simp_all [varClose]
  case fvar name ty =>
    intro h1
    have ⟨x1, x2⟩ := x
    simp at h h1
    have p: (x1, x2).snd = x2 := by simp
    rw [p]
    replace h := h h1
    intro m
    replace m := m.symm
    contradiction
  done

---------------------------------------------------------------------

/-! ### Well-formedness of `LExpr`s -/

/--
Characterizing terms that are locally closed, i.e., have no dangling bound
variables.

Example of a term that is not locally closed: `(.abs "x" (.bvar 1))`.
-/
def lcAt (k : Nat) (e : LExpr T.mono) : Bool :=
  match e with
  | .const _ _ _ => true
  | .op _ _ _ => true
  | .bvar _ i => i < k
  | .fvar _ _ _ => true
  | .abs _ _ e1 => lcAt (k + 1) e1
  | .quant _ _ _ tr e1 => lcAt (k + 1) tr && lcAt (k + 1) e1
  | .app _ e1 e2 => lcAt k e1 && lcAt k e2
  | .ite _ c t e' => lcAt k c && lcAt k t && lcAt k e'
  | .eq _ e1 e2 => lcAt k e1 && lcAt k e2

theorem varOpen_varClose_when_lcAt [BEq T.Identifier] [BEq T.Metadata] [LawfulBEq T.Identifier] [LawfulBEq T.Metadata] [LawfulBEq LMonoTy]
  (h1 : lcAt k e) (h2 : k <= i) :
  (varOpen i x (varClose (T := T) i x e)) = e := by
  induction e generalizing k i x
  case const c ty =>
    simp! [lcAt, varOpen, substK]
  case op o ty =>
    simp! [lcAt, varOpen, substK]
  case bvar j =>
    simp_all! [lcAt, varOpen, substK]; omega
  case fvar name ty =>
    simp_all [lcAt, varOpen, varClose]
    by_cases hx: x.fst = name <;> simp_all [substK]
    by_cases ht: ty = x.snd <;> simp_all [substK]
  case abs e e_ih =>
    simp_all [lcAt, varOpen, substK, varClose]
    simp_all [@e_ih (k + 1) (i + 1) x.fst]
  case quant qk e tr_ih e_ih =>
    simp_all [lcAt, varOpen, substK, varClose]
    simp_all [@e_ih (k + 1) (i + 1) x.fst, @tr_ih (k + 1) (i + 1) x.fst]
  case app fn e fn_ih e_ih =>
    simp_all [lcAt, varOpen, substK, varClose]
    simp_all [@e_ih k i x.fst, @fn_ih k i x.fst]
  case ite c t e c_ih t_ih e_ih =>
    simp_all [lcAt, varOpen, substK, varClose]
    simp_all [@e_ih k i x.fst, @c_ih k i x.fst, @t_ih k i x.fst]
  case eq e1 e2 e1_ih e2_ih =>
    simp_all [lcAt, varOpen, substK, varClose]
    simp_all [@e1_ih k i x.fst, @e2_ih k i x.fst]
  done

theorem lcAt_varOpen_abs  (h1 : fresh (T := T) x y)
  (h2 : lcAt k (varOpen i x y)) (h3 : k <= i) :
  lcAt i (.abs m ty y) := by
  induction y generalizing i k
  case const => simp_all [lcAt]
  case op => simp_all [lcAt]
  case bvar j =>
    simp_all [lcAt, varOpen, substK]
    by_cases j = i <;> simp_all [lcAt]; try omega
  case fvar => simp_all [lcAt]
  case abs e e_ih =>
    simp_all [varOpen]
    simp [substK, lcAt] at h2
    have e_ih' := @e_ih (k + 1) (i + 1) h2 (by omega)
    simp_all [lcAt]
  case quant tr e tr_ih e_ih =>
    simp_all [varOpen]
    simp [substK, lcAt] at h2
    rw [fresh] at h1
    cases h2
    rename_i h2_tr h2_e
    have h1_e : fresh x e = true := by
      rw [fresh]
      rw [freeVars] at h1
      simp
      simp at h1
      exact h1.2
    have h1_tr : fresh x tr = true := by
      rw [fresh]
      rw [freeVars] at h1
      simp
      simp at h1
      exact h1.1
    simp at h1_e
    simp at h1_tr
    have e_ih' := @e_ih (k + 1) (i + 1) h1_e (by exact h2_e)
    have tr_ih' := @tr_ih (k + 1) (i + 1) h1_tr (by exact h2_tr)
    simp_all [lcAt]
  case app fn e fn_ih e_ih =>
    simp_all [varOpen, lcAt, substK, fresh, freeVars]
    rw [@fn_ih k i h2.1 h3, @e_ih k i h2.2 h3]; simp
  case ite c t e c_ih t_ih e_ih =>
    simp_all [varOpen, lcAt, substK, fresh, freeVars]
    rw [@c_ih k i h2.left.left h3,
        @t_ih k i h2.left.right h3,
        @e_ih k i h2.right h3];
        simp
  case eq e1 e2 e1_ih e2_ih =>
    simp_all [varOpen, lcAt, substK, fresh, freeVars]
    rw [@e1_ih k i h2.left h3,
        @e2_ih k i h2.right h3]
    simp
  done

/--
An `LExpr e` is well-formed if it has no dangling bound variables.

We expect the type system to guarantee the well-formedness of an `LExpr`, i.e.,
we will prove a _regularity_ lemma; see lemma `HasType.regularity`.
-/
def WF (e : LExpr T.mono) : Bool :=
  lcAt 0 e

theorem varOpen_of_varClose [BEq T.Metadata] [LawfulBEq T.Metadata] [BEq T.Identifier] [LawfulBEq T.Identifier] {i : Nat} {x : IdentT T.Identifier} {e : LExpr T.mono} (h : LExpr.WF e) :
  varOpen i x (varClose i x e) = e := by
  simp_all [LExpr.WF]
  rw [varOpen_varClose_when_lcAt (k:=0) h]
  omega
  done

---------------------------------------------------------------------

/-! ### Substitution on `LExpr`s -/

/--
Substitute `(.fvar x _)` in `e` with `s`. Note that unlike `substK`, `varClose`,
and `varOpen`, this function is agnostic of types.

Also see function `subst`, where `subst s e` substitutes the outermost _bound_
variable in `e` with `s`.
-/
def substFvar [BEq T.Identifier] (e : LExpr T.mono) (fr : T.Identifier) (to : LExpr T.mono)
  : (LExpr T.mono) :=
  match e with
  | .const _ _ _ => e | .bvar _ _ => e | .op _ _ _ => e
  | .fvar _ name _ => if name == fr then to else e
  | .abs m ty e' => .abs m ty (substFvar e' fr to)
  | .quant m qk ty tr' e' => .quant m qk ty (substFvar tr' fr to) (substFvar e' fr to)
  | .app m fn e' => .app m (substFvar fn fr to) (substFvar e' fr to)
  | .ite m c t e' => .ite m (substFvar c fr to) (substFvar t fr to) (substFvar e' fr to)
  | .eq m e1 e2 => .eq m (substFvar e1 fr to) (substFvar e2 fr to)

def substFvars [BEq T.Identifier] (e : LExpr T.mono) (sm : Map T.Identifier (LExpr T.mono))
  : LExpr T.mono :=
  List.foldl (fun e (var, s) => substFvar e var s) e sm

---------------------------------------------------------------------

end LExpr
end Lambda
