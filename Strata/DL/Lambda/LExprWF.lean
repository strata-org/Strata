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

variable {T : LExprParams} [DecidableEq T.IDMeta]

/--
Compute the free variables in an `LExpr`, which are simply all the `LExpr.fvar`s
in it.
-/
def freeVars (e : LExpr ⟨T, GenericTy⟩) : IdentTs GenericTy T.IDMeta :=
  match e with
  | .const _ _ => []
  | .op _ _ _ => []
  | .bvar _ _ => []
  | .fvar _ x ty => [(x, ty)]
  | .abs _ _ e1 => freeVars e1
  | .quant _ _ _ tr e1 => freeVars tr ++ freeVars e1
  | .app _ e1 e2 => freeVars e1 ++ freeVars e2
  | .ite _ c t e => freeVars c ++ freeVars t ++ freeVars e
  | .eq _ e1 e2 => freeVars e1 ++ freeVars e2

/--
Is `x` a fresh variable w.r.t. `e`?
-/
def fresh (x : IdentT GenericTy T.IDMeta) (e : LExpr ⟨T, GenericTy⟩) : Prop :=
  x ∉ (freeVars e)

/-- An expression `e` is closed if has no free variables. -/
def closed (e : LExpr ⟨T, GenericTy⟩) : Bool :=
  freeVars e |>.isEmpty

omit [DecidableEq T.IDMeta] in
@[simp]
theorem fresh_abs {x : IdentT GenericTy T.IDMeta} {m : T.Metadata} {ty : Option GenericTy} {e : LExpr ⟨T, GenericTy⟩} :
  fresh x (.abs m ty e) = fresh x e := by
  simp [fresh, freeVars]

omit [DecidableEq T.IDMeta] in
@[simp]
theorem freeVars_abs {m : T.Metadata} {ty : Option GenericTy} {e : LExpr ⟨T, GenericTy⟩} :
  freeVars (.abs m ty e) = freeVars e := by
  simp [freeVars]

omit [DecidableEq T.IDMeta] in
@[simp]
theorem closed_abs {m : T.Metadata} {ty : Option GenericTy} {e : LExpr ⟨T, GenericTy⟩} :
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
def substK {T:LExprParamsT} (k : Nat) (s : T.base.Metadata → LExpr T)
    (e : LExpr T) : LExpr T :=
  match e with
  | .const m c => .const m c
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
def subst {T:LExprParamsT} (s : T.base.Metadata → LExpr T) (e : LExpr T) : LExpr T :=
  substK 0 s e

/--
This function turns some bound variables to free variables to investigate the
body of an abstraction. `varOpen k x e` keeps track of the number `k` of
abstractions that have passed by; it replaces all leaves of the form `(.bvar k)`
with `(.fvar x)`.

Note that `x` is expected to be a fresh variable w.r.t. `e`.
-/
def varOpen (k : Nat) (x : IdentT GenericTy T.IDMeta) (e : LExpr ⟨T, GenericTy⟩) : LExpr ⟨T, GenericTy⟩ :=
  substK k (fun m => .fvar m x.fst x.snd) e

theorem varOpen_sizeOf {T}:
  ∀ (x:IdentT GenericTy T.IDMeta) e k,
    (varOpen (T := T) k x e).sizeOf = e.sizeOf := by
  intros x e
  induction e
  case const _ _ | op _ _ _ | fvar _ _ _ =>
    unfold varOpen substK; solve | simp
  case bvar _ n =>
    intro k
    unfold varOpen substK
    split <;> solve | simp
  case abs _ ty e IH =>
    unfold varOpen substK
    intro k
    simp only [sizeOf]
    unfold varOpen at IH
    grind
  case quant _ ty e trigger x_IH trigger_IH =>
    unfold varOpen substK
    intro k
    simp only [sizeOf]
    unfold varOpen at x_IH trigger_IH
    grind
  case app _ _ lhs_IH rhs_IH  | eq _ _ lhs_IH rhs_IH =>
    unfold varOpen substK
    unfold varOpen at lhs_IH rhs_IH
    simp only [sizeOf]
    grind
  case ite _ _ c_IH then_IH else_IH =>
    unfold varOpen substK
    unfold varOpen at c_IH then_IH else_IH
    simp only [sizeOf]
    grind

/--
This function turns some free variables into bound variables to build an
abstraction, given its body. `varClose k x e` keeps track of the number `k`
of abstractions that have passed by; it replaces all `(.fvar x)` with
`(.bvar k)`.
-/
def varClose {T} {GenericTy} [BEq (Identifier T.IDMeta)] [BEq GenericTy] (k : Nat) (x : IdentT GenericTy T.IDMeta) (e : LExpr ⟨T, GenericTy⟩) : LExpr ⟨T, GenericTy⟩ :=
  match e with
  | .const m c => .const m c
  | .op m o ty => .op m o ty
  | .bvar m i => .bvar m i
  | .fvar m y (yty: Option GenericTy) => if x.fst == y && (yty == x.snd) then
                      (.bvar m k) else (.fvar m y yty)
  | .abs m ty e' => .abs m ty (varClose (k + 1) x e')
  | .quant m qk ty tr' e' => .quant m qk ty (varClose (k + 1) x tr') (varClose (k + 1) x e')
  | .app m e1 e2 => .app m (varClose k x e1) (varClose k x e2)
  | .ite m c t e => .ite m (varClose k x c) (varClose k x t) (varClose k x e)
  | .eq m e1 e2 => .eq m (varClose k x e1) (varClose k x e2)


theorem varClose_of_varOpen [LawfulBEq T.IDMeta] [BEq T.Metadata] [ReflBEq T.Metadata] [BEq GenericTy] [ReflBEq GenericTy] [LawfulBEq GenericTy]  (h : fresh x e) :
  varClose (T := T) (GenericTy := GenericTy) i x (varOpen i x e) = e := by
  induction e generalizing i x
  all_goals try simp_all [fresh, varOpen, LExpr.substK, varClose, freeVars]
  case bvar _ j =>
    by_cases hi : j = i <;>
    simp_all [varClose]
  case fvar _ name ty =>
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
def lcAt (k : Nat) (e : LExpr ⟨T, GenericTy⟩) : Bool :=
  match e with
  | .const _ _ => true
  | .op _ _ _ => true
  | .bvar _ i => i < k
  | .fvar _ _ _ => true
  | .abs _ _ e1 => lcAt (k + 1) e1
  | .quant _ _ _ tr e1 => lcAt (k + 1) tr && lcAt (k + 1) e1
  | .app _ e1 e2 => lcAt k e1 && lcAt k e2
  | .ite _ c t e' => lcAt k c && lcAt k t && lcAt k e'
  | .eq _ e1 e2 => lcAt k e1 && lcAt k e2

theorem varOpen_varClose_when_lcAt [DecidableEq GenericTy] [BEq T.Metadata] [LawfulBEq T.Metadata]
  (h1 : lcAt k e) (h2 : k <= i) :
  (varOpen i x (varClose (T := T) (GenericTy := GenericTy) i x e)) = e := by
  induction e generalizing k i x
  case const c ty =>
    simp! [lcAt, varOpen, substK]
  case op o ty =>
    simp! [lcAt, varOpen, substK]
  case bvar j =>
    simp_all! [lcAt, varOpen, substK]; omega
  case fvar name ty =>
    simp_all [lcAt, varOpen, varClose]
    by_cases hx: x.fst = name <;> simp_all[substK]
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
  lcAt i (abs m ty y) := by
  simp[lcAt]; apply (@lcAt_varOpen_inv k i)<;> assumption

theorem lcAt_varOpen_quant
  (hy : lcAt k (varOpen i x y)) (hki : k <= i)
  (htr: lcAt k (varOpen i x tr)) :
  lcAt i (quant m qk ty tr y) := by
  simp[lcAt]; constructor<;> apply (@lcAt_varOpen_inv k i) <;> assumption

/--
An `LExpr e` is well-formed if it has no dangling bound variables.

We expect the type system to guarantee the well-formedness of an `LExpr`, i.e.,
we will prove a _regularity_ lemma; see lemma `HasType.regularity`.
-/
def WF {T} {GenericTy} (e : LExpr ⟨T, GenericTy⟩) : Bool :=
  lcAt 0 e

theorem varOpen_of_varClose {T} {GenericTy} [BEq T.Metadata] [LawfulBEq T.Metadata] [DecidableEq T.IDMeta] [DecidableEq GenericTy] {i : Nat} {x : IdentT GenericTy T.IDMeta} {e : LExpr ⟨T, GenericTy⟩} (h : LExpr.WF e) :
  varOpen i x (varClose i x e) = e := by
  simp_all [LExpr.WF]
  rename_i r1 r2 r3
  have c := varOpen_varClose_when_lcAt (GenericTy:=GenericTy) (k:=0) (e:=e) (i:=i) (x:=x) h
  simp at c
  exact c

---------------------------------------------------------------------

/-! ### Substitution on `LExpr`s -/

/--
Substitute `(.fvar x _)` in `e` with `s`. Note that unlike `substK`, `varClose`,
and `varOpen`, this function is agnostic of types.

Also see function `subst`, where `subst s e` substitutes the outermost _bound_
variable in `e` with `s`.
-/
def substFvar [BEq T.IDMeta] (e : LExpr ⟨T, GenericTy⟩) (fr : T.Identifier) (to : LExpr ⟨T, GenericTy⟩)
  : (LExpr ⟨T, GenericTy⟩) :=
  match e with
  | .const _ _ => e | .bvar _ _ => e | .op _ _ _ => e
  | .fvar _ name _ => if name == fr then to else e
  | .abs m ty e' => .abs m ty (substFvar e' fr to)
  | .quant m qk ty tr' e' => .quant m qk ty (substFvar tr' fr to) (substFvar e' fr to)
  | .app m fn e' => .app m (substFvar fn fr to) (substFvar e' fr to)
  | .ite m c t e' => .ite m (substFvar c fr to) (substFvar t fr to) (substFvar e' fr to)
  | .eq m e1 e2 => .eq m (substFvar e1 fr to) (substFvar e2 fr to)

def substFvars [BEq T.IDMeta] (e : LExpr ⟨T, GenericTy⟩) (sm : Map T.Identifier (LExpr ⟨T, GenericTy⟩))
  : LExpr ⟨T, GenericTy⟩ :=
  List.foldl (fun e (var, s) => substFvar e var s) e sm

---------------------------------------------------------------------

end LExpr
end Lambda
