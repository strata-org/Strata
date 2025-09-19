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

variable {Identifier : Type} [DecidableEq Identifier]

/--
Compute the free variables in an `LExpr`, which are simply all the `LExpr.fvar`s
in it.
-/
def freeVars (e : LExpr LMonoTy Identifier) : IdentTs Identifier :=
  match e with
  | .const _ _ => []
  | .op _ _ => []
  | .bvar _ => []
  | .fvar x ty => [(x, ty)]
  | .mdata _ e1 => freeVars e1
  | .abs _ e1 => freeVars e1
  | .quant _ _ tr e1 => freeVars tr ++ freeVars e1
  | .app e1 e2 => freeVars e1 ++ freeVars e2
  | .ite c t e => freeVars c ++ freeVars t ++ freeVars e
  | .eq e1 e2 => freeVars e1 ++ freeVars e2

/--
Is `x` is a fresh variable w.r.t. `e`?
-/
def fresh (x : IdentT Identifier) (e : LExpr LMonoTy Identifier) : Bool :=
  x ∉ (freeVars e)

/-- An expression `e` is closed if has no free variables. -/
def closed (e : LExpr LMonoTy Identifier) : Bool :=
  freeVars e |>.isEmpty

@[simp]
theorem fresh_abs :
  fresh (Identifier:=Identifier) x (.abs ty e) = fresh x e := by
  simp [fresh, freeVars]

@[simp]
theorem fresh_mdata :
  fresh (Identifier:=Identifier) x (.mdata info e) = fresh x e := by
  simp [fresh, freeVars]

omit [DecidableEq Identifier] in
@[simp]
theorem freeVars_abs :
  freeVars (Identifier:=Identifier) (.abs ty e) = freeVars e := by
  simp [freeVars]

omit [DecidableEq Identifier] in
@[simp]
theorem freeVars_mdata :
  freeVars (Identifier:=Identifier) (.mdata info e) = freeVars e := by
  simp [freeVars]

omit [DecidableEq Identifier] in
@[simp]
theorem closed_abs :
  closed (Identifier:=Identifier) (.abs ty e) = closed e := by
  simp [closed]

omit [DecidableEq Identifier] in
@[simp]
theorem closed_mdata :
  closed (Identifier:=Identifier) (.mdata info e) = closed e := by
  simp [closed]

---------------------------------------------------------------------

/-! ### Substitutions in `LExpr`s -/

/--
This function replaces some bound variables in `e` by an arbitrary expression
`s` (and `s` may contain some free variables).

`substK k s e` keeps track of the number `k` of abstractions that have passed
by; it replaces all leaves of the form `(.bvar k)` with `s`.
-/
def substK (k : Nat) (s : LExpr LMonoTy Identifier) (e : LExpr LMonoTy Identifier) : LExpr LMonoTy Identifier :=
  match e with
  | .const c ty => .const c ty
  | .op o ty => .op o ty
  | .bvar i => if (i == k) then s else .bvar i
  | .fvar y ty => .fvar y ty
  | .mdata info e' => .mdata info (substK k s e')
  | .abs ty e' => .abs ty (substK (k + 1) s e')
  | .quant qk ty tr' e' => .quant qk ty (substK (k + 1) s tr') (substK (k + 1) s e')
  | .app e1 e2 => .app (substK k s e1) (substK k s e2)
  | .ite c t e => .ite (substK k s c) (substK k s t) (substK k s e)
  | .eq e1 e2 => .eq (substK k s e1) (substK k s e2)

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
def subst (s : LExpr LMonoTy Identifier) (e : LExpr LMonoTy Identifier) : LExpr LMonoTy Identifier :=
  substK 0 s e

/--
This function turns some bound variables to free variables to investigate the
body of an abstraction. `varOpen k x e` keeps track of the number `k` of
abstractions that have passed by; it replaces all leaves of the form `(.bvar k)`
with `(.fvar x)`.

Note that `x` is expected to be a fresh variable w.r.t. `e`.
-/
def varOpen (k : Nat) (x : IdentT Identifier) (e : LExpr LMonoTy Identifier) : LExpr LMonoTy Identifier :=
  substK k (.fvar x.fst x.snd) e

/--
This function turns some free variables into bound variables to build an
abstraction, given its body. `varClose k x e` keeps track of the number `k`
of abstractions that have passed by; it replaces all `(.fvar x)` with
`(.bvar k)`.
-/
def varClose (k : Nat) (x : IdentT Identifier) (e : LExpr LMonoTy Identifier) : LExpr LMonoTy Identifier :=
  match e with
  | .const c ty => .const c ty
  | .op o ty => .op o ty
  | .bvar i => .bvar i
  | .fvar y yty => if (x.fst == y) && (yty == x.snd) then
                      (.bvar k) else (.fvar y yty)
  | .mdata info e' => .mdata info (varClose k x e')
  | .abs ty e' => .abs ty (varClose (k + 1) x e')
  | .quant qk ty tr' e' => .quant qk ty (varClose (k + 1) x tr') (varClose (k + 1) x e')
  | .app e1 e2 => .app (varClose k x e1) (varClose k x e2)
  | .ite c t e => .ite (varClose k x c) (varClose k x t) (varClose k x e)
  | .eq e1 e2 => .eq (varClose k x e1) (varClose k x e2)


theorem varClose_of_varOpen (h : fresh x e) :
  varClose (Identifier:=Identifier) i x (varOpen i x e) = e := by
  induction e generalizing i x
  all_goals try simp_all [fresh, varOpen, LExpr.substK, varClose, freeVars]
  case bvar j =>
    by_cases hi : j = i <;>
    simp_all [varClose]
  case fvar name ty =>
    intro h1
    have ⟨x1, x2⟩ := x
    simp at h h1
    exact fun a => h h1 (id (Eq.symm a))
  done
---------------------------------------------------------------------

/-! ### Well-formedness of `LExpr`s -/

/--
Characterizing terms that are locally closed, i.e., have no dangling bound
variables.

Example of a term that is not locally closed: `(.abs "x" (.bvar 1))`.
-/
def lcAt (k : Nat) (e : LExpr LMonoTy Identifier) : Bool :=
  match e with
  | .const _ _ => true
  | .op _ _ => true
  | .bvar i => i < k
  | .fvar _ _ => true
  | .mdata _ e1 => lcAt k e1
  | .abs _ e1 => lcAt (k + 1) e1
  | .quant _ _ tr e1 => lcAt (k + 1) tr && lcAt (k + 1) e1
  | .app e1 e2 => lcAt k e1 && lcAt k e2
  | .ite c t e' => lcAt k c && lcAt k t && lcAt k e'
  | .eq e1 e2 => lcAt k e1 && lcAt k e2

theorem varOpen_varClose_when_lcAt
  (h1 : lcAt k e) (h2 : k <= i) :
  (varOpen i x (varClose (Identifier:=Identifier) i x e)) = e := by
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
  case mdata info e ih =>
    simp_all [lcAt, varOpen, substK, varClose]
    rw [@ih k i x.fst x.snd h1 h2]
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

theorem lcAt_varOpen_abs
  (h1 : lcAt k (varOpen i x y)) (h2 : k <= i) :
  lcAt i (abs ty y) := by
  induction y generalizing i k
  case const => simp_all [lcAt]
  case op => simp_all [lcAt]
  case bvar j =>
    simp_all [lcAt, varOpen, substK]
    by_cases j = i <;> simp_all [lcAt]; try omega
  case fvar => simp_all [lcAt]
  case mdata info e ih =>
    simp_all [lcAt, varOpen, substK]
    rw [@ih k i h1 h2]
  case abs e e_ih =>
    simp_all [varOpen]
    simp [substK, lcAt] at h1
    have e_ih' := @e_ih (k + 1) (i + 1) h1 (by omega)
    simp_all [lcAt]
  case quant tr e tr_ih e_ih =>
    simp_all [varOpen]
    simp_all [substK, lcAt]
    have e_ih' := @e_ih (k + 1) (i + 1)
    have tr_ih' := @tr_ih (k + 1) (i + 1)
    constructor
    exact tr_ih' h1.left (by omega)
    exact e_ih' h1.right (by omega)
  case app fn e fn_ih e_ih =>
    simp_all [varOpen, lcAt, substK]
    rw [@fn_ih k i h1.1 h2, @e_ih k i h1.2 h2]; simp
  case ite c t e c_ih t_ih e_ih =>
    simp_all [varOpen, lcAt, substK]
    rw [@c_ih k i h1.left.left h2,
        @t_ih k i h1.left.right h2,
        @e_ih k i h1.right h2];
        simp
  case eq e1 e2 e1_ih e2_ih =>
    simp_all [varOpen, lcAt, substK]
    rw [@e1_ih k i h1.left h2,
        @e2_ih k i h1.right h2]
    simp
  done

/--
An `LExpr e` is well-formed if it has no dangling bound variables.

We expect the type system to guarantee the well-formedness of an `LExpr`, i.e.,
we will prove a _regularity_ lemma; see lemma `HasType.regularity`.
-/
def WF (e : LExpr LMonoTy Identifier) : Bool :=
  lcAt 0 e

theorem varOpen_of_varClose (h : LExpr.WF e) :
  varOpen i x (varClose (Identifier:=Identifier) i x e) = e := by
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
def substFvar {Identifier: Type} [DecidableEq Identifier] (e : LExpr LMonoTy Identifier) (fr : Identifier) (to : LExpr LMonoTy Identifier)
  : (LExpr LMonoTy Identifier) :=
  match e with
  | .const _ _ => e | .bvar _ => e | .op _ _ => e
  | .fvar  name _ => if name == fr then to else e
  | .mdata info e' => .mdata info (substFvar e' fr to)
  | .abs   ty e' => .abs ty (substFvar e' fr to)
  | .quant qk ty tr' e' => .quant qk ty (substFvar tr' fr to) (substFvar e' fr to)
  | .app   fn e' => .app (substFvar fn fr to) (substFvar e' fr to)
  | .ite   c t e' => .ite (substFvar c fr to) (substFvar t fr to) (substFvar e' fr to)
  | .eq    e1 e2 => .eq (substFvar e1 fr to) (substFvar e2 fr to)

def substFvars {Identifier: Type} [DecidableEq Identifier] (e : LExpr LMonoTy Identifier) (sm : Map Identifier (LExpr LMonoTy Identifier))
  : LExpr LMonoTy Identifier :=
  List.foldl (fun e (var, s) => substFvar e var s) e sm

---------------------------------------------------------------------

end LExpr
end Lambda
