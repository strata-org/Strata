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

variable {MetadataType : Type} {Identifier : Type} [DecidableEq Identifier]

/--
Compute the free variables in an `LExpr`, which are simply all the `LExpr.fvar`s
in it.
-/
def freeVars (e : LExpr MetadataType LMonoTy Identifier) : IdentTs Identifier :=
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
def fresh (x : IdentT Identifier) (e : LExpr MetadataType LMonoTy Identifier) : Bool :=
  x ∉ (freeVars e)

/-- An expression `e` is closed if has no free variables. -/
def closed (e : LExpr MetadataType LMonoTy Identifier) : Bool :=
  freeVars e |>.isEmpty

@[simp]
theorem fresh_abs :
  fresh (Identifier:=Identifier) x (.abs m ty e) = fresh x e := by
  simp [fresh, freeVars]

omit [DecidableEq Identifier] in
@[simp]
theorem freeVars_abs :
  freeVars (Identifier:=Identifier) (.abs m ty e) = freeVars e := by
  simp [freeVars]

omit [DecidableEq Identifier] in
@[simp]
theorem closed_abs :
  closed (Identifier:=Identifier) (.abs m ty e) = closed e := by
  simp [closed]

---------------------------------------------------------------------

/-! ### Substitutions in `LExpr`s -/

/--
This function replaces some bound variables in `e` by an arbitrary expression
`s` (and `s` may contain some free variables).

`substK k s e` keeps track of the number `k` of abstractions that have passed
by; it replaces all leaves of the form `(.bvar k)` with `s`.
-/
def substK (k : Nat) (s : LExpr MetadataType LMonoTy Identifier) (e : LExpr MetadataType LMonoTy Identifier) : LExpr MetadataType LMonoTy Identifier :=
  match e with
  | .const m c ty => .const m c ty
  | .op m o ty => .op m o ty
  | .bvar m i => if (i == k) then s else .bvar m i
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
def subst (s : LExpr MetadataType LMonoTy Identifier) (e : LExpr MetadataType LMonoTy Identifier) : LExpr MetadataType LMonoTy Identifier :=
  substK 0 s e

/--
This function turns some bound variables to free variables to investigate the
body of an abstraction. `varOpen k x e` keeps track of the number `k` of
abstractions that have passed by; it replaces all leaves of the form `(.bvar k)`
with `(.fvar x)`.

Note that `x` is expected to be a fresh variable w.r.t. `e`.
-/
def varOpen [Inhabited MetadataType] (k : Nat) (x : IdentT Identifier) (e : LExpr MetadataType LMonoTy Identifier) : LExpr MetadataType LMonoTy Identifier :=
  substK k (.fvar default x.fst x.snd) e

/--
This function turns some free variables into bound variables to build an
abstraction, given its body. `varClose k x e` keeps track of the number `k`
of abstractions that have passed by; it replaces all `(.fvar x)` with
`(.bvar k)`.
-/
def varClose [Inhabited MetadataType] (k : Nat) (x : IdentT Identifier) (e : LExpr MetadataType LMonoTy Identifier) : LExpr MetadataType LMonoTy Identifier :=
  match e with
  | .const m c ty => .const m c ty
  | .op m o ty => .op m o ty
  | .bvar m i => .bvar m i
  | .fvar m y yty => if (x.fst == y) && (yty == x.snd) then
                      (.bvar default k) else (.fvar m y yty)
  | .abs m ty e' => .abs m ty (varClose (k + 1) x e')
  | .quant m qk ty tr' e' => .quant m qk ty (varClose (k + 1) x tr') (varClose (k + 1) x e')
  | .app m e1 e2 => .app m (varClose k x e1) (varClose k x e2)
  | .ite m c t e => .ite m (varClose k x c) (varClose k x t) (varClose k x e)
  | .eq m e1 e2 => .eq m (varClose k x e1) (varClose k x e2)


theorem varClose_of_varOpen [Inhabited MetadataType] {x : IdentT Identifier} {e : LExpr MetadataType LMonoTy Identifier} {i : Nat} (h : fresh x e) :
  varClose (Identifier:=Identifier) i x (varOpen i x e) = e := by
  sorry
---------------------------------------------------------------------

/-! ### Well-formedness of `LExpr`s -/

/--
Characterizing terms that are locally closed, i.e., have no dangling bound
variables.

Example of a term that is not locally closed: `(.abs "x" (.bvar 1))`.
-/
def lcAt (k : Nat) (e : LExpr MetadataType LMonoTy Identifier) : Bool :=
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

theorem varOpen_varClose_when_lcAt [Inhabited MetadataType] {k i : Nat} {x : IdentT Identifier} {e : LExpr MetadataType LMonoTy Identifier}
  (h1 : lcAt k e) (h2 : k <= i) :
  (varOpen i x (varClose (Identifier:=Identifier) i x e)) = e := by
  sorry

theorem lcAt_varOpen_abs [Inhabited MetadataType] {k i : Nat} {x : IdentT Identifier} {y : LExpr MetadataType LMonoTy Identifier} {m : MetadataType} {ty : Option LMonoTy} (h1 : fresh (Identifier:=Identifier) x y)
  (h2 : lcAt k (varOpen i x y)) (h3 : k <= i) :
  lcAt i (.abs m ty y) := by
  sorry

/--
An `LExpr e` is well-formed if it has no dangling bound variables.

We expect the type system to guarantee the well-formedness of an `LExpr`, i.e.,
we will prove a _regularity_ lemma; see lemma `HasType.regularity`.
-/
def WF (e : LExpr MetadataType LMonoTy Identifier) : Bool :=
  lcAt 0 e

theorem varOpen_of_varClose [Inhabited MetadataType] {i : Nat} {x : IdentT Identifier} {e : LExpr MetadataType LMonoTy Identifier} (h : LExpr.WF e) :
  varOpen i x (varClose (Identifier:=Identifier) i x e) = e := by
  sorry

---------------------------------------------------------------------

/-! ### Substitution on `LExpr`s -/

/--
Substitute `(.fvar x _)` in `e` with `s`. Note that unlike `substK`, `varClose`,
and `varOpen`, this function is agnostic of types.

Also see function `subst`, where `subst s e` substitutes the outermost _bound_
variable in `e` with `s`.
-/
def substFvar {MetadataType : Type} {Identifier: Type} [DecidableEq Identifier] (e : LExpr MetadataType LMonoTy Identifier) (fr : Identifier) (to : LExpr MetadataType LMonoTy Identifier)
  : (LExpr MetadataType LMonoTy Identifier) :=
  match e with
  | .const _ _ _ => e | .bvar _ _ => e | .op _ _ _ => e
  | .fvar m name _ => if name == fr then to else e
  | .abs m ty e' => .abs m ty (substFvar e' fr to)
  | .quant m qk ty tr' e' => .quant m qk ty (substFvar tr' fr to) (substFvar e' fr to)
  | .app m fn e' => .app m (substFvar fn fr to) (substFvar e' fr to)
  | .ite m c t e' => .ite m (substFvar c fr to) (substFvar t fr to) (substFvar e' fr to)
  | .eq m e1 e2 => .eq m (substFvar e1 fr to) (substFvar e2 fr to)

def substFvars {MetadataType : Type} {Identifier: Type} [DecidableEq Identifier] (e : LExpr MetadataType LMonoTy Identifier) (sm : Map Identifier (LExpr MetadataType LMonoTy Identifier))
  : LExpr MetadataType LMonoTy Identifier :=
  List.foldl (fun e (var, s) => substFvar e var s) e sm

---------------------------------------------------------------------

end LExpr
end Lambda
