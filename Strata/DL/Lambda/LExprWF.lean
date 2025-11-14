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

variable {IDMeta : Type} [DecidableEq IDMeta]

/--
Compute the free variables in an `LExpr`, which are simply all the `LExpr.fvar`s
in it.
-/
def freeVars {GenericTy} (e : LExpr GenericTy IDMeta)
  : IdentTs GenericTy IDMeta :=
  match e with
  | .const _ => []
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
Is `x` a fresh variable w.r.t. `e`?
-/
def fresh {GenericTy} [DecidableEq GenericTy]
    (x : IdentT GenericTy IDMeta) (e : LExpr GenericTy IDMeta) : Bool :=
  x ∉ (freeVars e)

/-- An expression `e` is closed if has no free variables. -/
def closed {GenericTy} (e : LExpr GenericTy IDMeta) : Bool :=
  freeVars e |>.isEmpty

@[simp]
theorem fresh_abs {GenericTy} [DecidableEq GenericTy]
  {x:IdentT GenericTy IDMeta} {e:LExpr GenericTy IDMeta} {ty:Option GenericTy}:
  fresh (IDMeta:=IDMeta) x (.abs ty e) = fresh x e := by
  simp [fresh, freeVars]

@[simp]
theorem fresh_mdata {GenericTy} [DecidableEq GenericTy]
  {x:IdentT GenericTy IDMeta} {e:LExpr GenericTy IDMeta}:
  fresh (IDMeta:=IDMeta) x (.mdata info e) = fresh x e := by
  simp [fresh, freeVars]

omit [DecidableEq IDMeta] in
@[simp]
theorem freeVars_abs :
  freeVars (IDMeta:=IDMeta) (.abs ty e) = freeVars e := by
  simp [freeVars]

omit [DecidableEq IDMeta] in
@[simp]
theorem freeVars_mdata :
  freeVars (IDMeta:=IDMeta) (.mdata info e) = freeVars e := by
  simp [freeVars]

omit [DecidableEq IDMeta] in
@[simp]
theorem closed_abs :
  closed (IDMeta:=IDMeta) (.abs ty e) = closed e := by
  simp [closed]

omit [DecidableEq IDMeta] in
@[simp]
theorem closed_mdata :
  closed (IDMeta:=IDMeta) (.mdata info e) = closed e := by
  simp [closed]

---------------------------------------------------------------------

/-! ### Substitutions in `LExpr`s -/

/--
This function replaces some bound variables in `e` by an arbitrary expression
`s` (and `s` may contain some free variables).

`substK k s e` keeps track of the number `k` of abstractions that have passed
by; it replaces all leaves of the form `(.bvar k)` with `s`.
-/
def substK {GenericTy} (k : Nat) (s : LExpr GenericTy IDMeta)
    (e : LExpr GenericTy IDMeta) : LExpr GenericTy IDMeta :=
  match e with
  | .const c => .const c
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
def subst {GenericTy} (s : LExpr GenericTy IDMeta) (e : LExpr GenericTy IDMeta)
    : LExpr GenericTy IDMeta :=
  substK 0 s e

/--
This function turns some bound variables to free variables to investigate the
body of an abstraction. `varOpen k x e` keeps track of the number `k` of
abstractions that have passed by; it replaces all leaves of the form `(.bvar k)`
with `(.fvar x)`.

Note that `x` is expected to be a fresh variable w.r.t. `e`.
-/
def varOpen {GenericTy} (k : Nat) (x : IdentT GenericTy IDMeta)
    (e : LExpr GenericTy IDMeta) : LExpr GenericTy IDMeta :=
  substK k (.fvar x.fst x.snd) e

/--
This function turns some free variables into bound variables to build an
abstraction, given its body. `varClose k x e` keeps track of the number `k`
of abstractions that have passed by; it replaces all `(.fvar x)` with
`(.bvar k)`.
-/
def varClose {GenericTy} (k : Nat) (x : IdentT GenericTy IDMeta)
    [DecidableEq GenericTy]
    (e : LExpr GenericTy IDMeta) : LExpr GenericTy IDMeta :=
  match e with
  | .const c => .const c
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


theorem varClose_of_varOpen {GenericTy} [DecidableEq GenericTy]
  {x: IdentT GenericTy IDMeta} (e: LExpr GenericTy IDMeta) (h : fresh x e) :
  varClose (IDMeta:=IDMeta) i x (varOpen i x e) = e := by
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
def lcAt {GenericTy} (k : Nat) (e : LExpr GenericTy IDMeta) : Bool :=
  match e with
  | .const _ => true
  | .op _ _ => true
  | .bvar i => i < k
  | .fvar _ _ => true
  | .mdata _ e1 => lcAt k e1
  | .abs _ e1 => lcAt (k + 1) e1
  | .quant _ _ tr e1 => lcAt (k + 1) tr && lcAt (k + 1) e1
  | .app e1 e2 => lcAt k e1 && lcAt k e2
  | .ite c t e' => lcAt k c && lcAt k t && lcAt k e'
  | .eq e1 e2 => lcAt k e1 && lcAt k e2

theorem varOpen_varClose_when_lcAt {GenericTy} [DecidableEq GenericTy]
  {x : IdentT GenericTy IDMeta} {e : LExpr GenericTy IDMeta}
  (h1 : lcAt k e) (h2 : k <= i) :
  (varOpen i x (varClose (IDMeta:=IDMeta) i x e)) = e := by
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

theorem lcAt_substK_inv (he: lcAt k (substK i s e)) (hik: k ≤ i) : lcAt (i + 1) e := by
  induction e generalizing i k s <;> simp_all[lcAt, substK] <;> try grind
  case bvar id j =>
    by_cases j = i
    case pos hji => omega
    case neg hji => rw[if_neg hji] at he; simp[lcAt] at he; omega

theorem lcAt_varOpen_inv (hs: lcAt k (varOpen i x e)) (hik: k ≤ i) : lcAt (i + 1) e := by
  unfold varOpen at hs; exact (lcAt_substK_inv hs hik)

theorem lcAt_varOpen_abs
  (h1 : lcAt k (varOpen i x y)) (h2 : k <= i) :
  lcAt i (abs ty y) := by
  simp[lcAt]; apply (@lcAt_varOpen_inv k i)<;> assumption

theorem lcAt_varOpen_quant
  (hy : lcAt k (varOpen i x y)) (hki : k <= i)
  (htr: lcAt k (varOpen i x tr)) :
  lcAt i (quant qk ty tr y) := by
  simp[lcAt]; constructor<;> apply (@lcAt_varOpen_inv k i) <;> assumption

/--
An `LExpr e` is well-formed if it has no dangling bound variables.

We expect the type system to guarantee the well-formedness of an `LExpr`, i.e.,
we will prove a _regularity_ lemma; see lemma `HasType.regularity`.
-/
def WF {GenericTy} (e : LExpr GenericTy IDMeta) : Bool :=
  lcAt 0 e

theorem varOpen_of_varClose {GenericTy} [DecidableEq GenericTy]
  {e : LExpr GenericTy IDMeta} {x : IdentT GenericTy IDMeta} (h : LExpr.WF e) :
  varOpen i x (varClose (IDMeta:=IDMeta) i x e) = e := by
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
def substFvar {GenericTy} {IDMeta: Type} [DecidableEq IDMeta]
  (e : LExpr GenericTy IDMeta) (fr : Identifier IDMeta) (to : LExpr GenericTy IDMeta)
  : (LExpr GenericTy IDMeta) :=
  match e with
  | .const _ => e | .bvar _ => e | .op _ _ => e
  | .fvar  name _ => if name == fr then to else e
  | .mdata info e' => .mdata info (substFvar e' fr to)
  | .abs   ty e' => .abs ty (substFvar e' fr to)
  | .quant qk ty tr' e' => .quant qk ty (substFvar tr' fr to) (substFvar e' fr to)
  | .app   fn e' => .app (substFvar fn fr to) (substFvar e' fr to)
  | .ite   c t e' => .ite (substFvar c fr to) (substFvar t fr to) (substFvar e' fr to)
  | .eq    e1 e2 => .eq (substFvar e1 fr to) (substFvar e2 fr to)

def substFvars {GenericTy} {IDMeta: Type} [DecidableEq IDMeta]
  (e : LExpr GenericTy IDMeta) (sm : Map (Identifier IDMeta)
  (LExpr GenericTy IDMeta))
  : LExpr GenericTy IDMeta :=
  List.foldl (fun e (var, s) => substFvar e var s) e sm

---------------------------------------------------------------------

end LExpr
end Lambda
