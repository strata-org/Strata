/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LExpr
public import Strata.DL.Util.Map

/-! ## Well-formedness of Lambda Expressions

See the definition `Lambda.LExpr.WF`. Also see theorem `HasType.regularity` in
`Strata.DL.Lambda.LExprTypeSpec`.
-/

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)

public section

namespace LExpr

variable {T : LExprParams} [DecidableEq T.IDMeta]

/--
Compute the free variables in an `LExpr`, which are simply all the `LExpr.fvar`s
in it.
-/
@[expose] def freeVars (e : LExpr ⟨T, GenericTy⟩) : IdentTs GenericTy T.IDMeta :=
  match e with
  | .const _ _ => []
  | .op _ _ _ => []
  | .bvar _ _ => []
  | .fvar _ x ty => [(x, ty)]
  | .abs _ _ _ e1 => freeVars e1
  | .quant _ _ _ _ tr e1 => freeVars tr ++ freeVars e1
  | .app _ e1 e2 => freeVars e1 ++ freeVars e2
  | .ite _ c t e => freeVars c ++ freeVars t ++ freeVars e
  | .eq _ e1 e2 => freeVars e1 ++ freeVars e2

/--
Is `x` a fresh variable w.r.t. `e`?
-/
def fresh (x : IdentT GenericTy T.IDMeta) (e : LExpr ⟨T, GenericTy⟩) : Prop :=
  x ∉ (freeVars e)

/-- An expression `e` is closed if has no free variables. -/
@[expose] def closed (e : LExpr ⟨T, GenericTy⟩) : Bool :=
  freeVars e |>.isEmpty

omit [DecidableEq T.IDMeta] in
@[simp]
theorem fresh_abs {x : IdentT GenericTy T.IDMeta} {m : T.Metadata} {name : String} {ty : Option GenericTy} {e : LExpr ⟨T, GenericTy⟩} :
  fresh x (.abs m name ty e) = fresh x e := by
  simp [fresh, freeVars]

omit [DecidableEq T.IDMeta] in
@[simp]
theorem freeVars_abs {m : T.Metadata} {name : String} {ty : Option GenericTy} {e : LExpr ⟨T, GenericTy⟩} :
  freeVars (.abs m name ty e) = freeVars e := by
  simp [freeVars]

omit [DecidableEq T.IDMeta] in
@[simp]
theorem closed_abs {m : T.Metadata} {name : String} {ty : Option GenericTy} {e : LExpr ⟨T, GenericTy⟩} :
  closed (.abs m name ty e) = closed e := by
  simp [closed]

---------------------------------------------------------------------

/-! ### Substitutions in `LExpr`s -/

/--
This function replaces some bound variables in `e` by an arbitrary expression
`s` (and `s` may contain some free variables).

`substK k s e` keeps track of the number `k` of abstractions that have passed
by; it replaces all leaves of the form `(.bvar k)` with `s`.
-/
@[expose] def substK {T:LExprParamsT} (k : Nat) (s : T.base.Metadata → LExpr T)
    (e : LExpr T) : LExpr T :=
  match e with
  | .const m c => .const m c
  | .op m o ty => .op m o ty
  | .bvar m i => if i == k then s m else .bvar m i
  | .fvar m y ty => .fvar m y ty
  | .abs m name ty e' => .abs m name ty (substK (k + 1) s e')
  | .quant m qk name ty tr' e' => .quant m qk name ty (substK (k + 1) s tr') (substK (k + 1) s e')
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
@[expose] def subst {T:LExprParamsT} (s : T.base.Metadata → LExpr T) (e : LExpr T) : LExpr T :=
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
  | .abs m name ty e' => .abs m name ty (varClose (k + 1) x e')
  | .quant m qk name ty tr' e' => .quant m qk name ty (varClose (k + 1) x tr') (varClose (k + 1) x e')
  | .app m e1 e2 => .app m (varClose k x e1) (varClose k x e2)
  | .ite m c t e => .ite m (varClose k x c) (varClose k x t) (varClose k x e)
  | .eq m e1 e2 => .eq m (varClose k x e1) (varClose k x e2)


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
  | .abs _ _ _ e1 => lcAt (k + 1) e1
  | .quant _ _ _ _ tr e1 => lcAt (k + 1) tr && lcAt (k + 1) e1
  | .app _ e1 e2 => lcAt k e1 && lcAt k e2
  | .ite _ c t e' => lcAt k c && lcAt k t && lcAt k e'
  | .eq _ e1 e2 => lcAt k e1 && lcAt k e2

/--
An `LExpr e` is well-formed if it has no dangling bound variables.

We expect the type system to guarantee the well-formedness of an `LExpr`, i.e.,
we will prove a _regularity_ lemma; see lemma `HasType.regularity`.
-/
def WF {T} {GenericTy} (e : LExpr ⟨T, GenericTy⟩) : Bool :=
  lcAt 0 e

/-! ### Substitution on `LExpr`s -/

/--
Increment bound variable indices in `e` by `n`. Only bvars at or above `cutoff`
are shifted; bvars below `cutoff` (bound within `e`) are left alone. The cutoff
increases when going under binders.
-/
def liftBVars (n : Nat) (e : LExpr ⟨T, GenericTy⟩) (cutoff : Nat := 0) : LExpr ⟨T, GenericTy⟩ :=
  match e with
  | .const _ _ => e | .op _ _ _ => e | .fvar _ _ _ => e
  | .bvar m i => if i >= cutoff then .bvar m (i + n) else e
  | .abs m name ty e' => .abs m name ty (liftBVars n e' (cutoff + 1))
  | .quant m qk name ty tr' e' => .quant m qk name ty (liftBVars n tr' (cutoff + 1)) (liftBVars n e' (cutoff + 1))
  | .app m fn e' => .app m (liftBVars n fn cutoff) (liftBVars n e' cutoff)
  | .ite m c t e' => .ite m (liftBVars n c cutoff) (liftBVars n t cutoff) (liftBVars n e' cutoff)
  | .eq m e1 e2 => .eq m (liftBVars n e1 cutoff) (liftBVars n e2 cutoff)

/--
Substitute `(.fvar x _)` in `e` with `to`. Does NOT lift de Bruijn indices in `to`
when going under binders - safe when `to` contains no bvars (e.g., substituting
fvar→fvar). Use `substFvarLifting` when `to` contains bvars.
-/
def substFvar [BEq T.IDMeta] (e : LExpr ⟨T, GenericTy⟩) (fr : T.Identifier) (to : LExpr ⟨T, GenericTy⟩)
  : (LExpr ⟨T, GenericTy⟩) :=
  match e with
  | .const _ _ => e | .bvar _ _ => e | .op _ _ _ => e
  | .fvar _ name _ => if name == fr then to else e
  | .abs m name ty e' => .abs m name ty (substFvar e' fr to)
  | .quant m qk name ty tr' e' => .quant m qk name ty (substFvar tr' fr to) (substFvar e' fr to)
  | .app m fn e' => .app m (substFvar fn fr to) (substFvar e' fr to)
  | .ite m c t e' => .ite m (substFvar c fr to) (substFvar t fr to) (substFvar e' fr to)
  | .eq m e1 e2 => .eq m (substFvar e1 fr to) (substFvar e2 fr to)

/--
Like `substFvar`, but properly lifts de Bruijn indices in `to` when going under
binders. Use this when `to` contains bound variables that should be preserved.

**Important:** `to` is interpreted in the *outer* scope (before entering `e`).
Any bvars in `to` must refer to binders *outside* `e`, not to binders within `e`.
When the traversal descends under a binder in `e`, `liftBVars` shifts `to`'s
indices so they continue to point to the same outer binders.
-/
def substFvarLifting [BEq T.IDMeta] (e : LExpr ⟨T, GenericTy⟩) (fr : T.Identifier) (to : LExpr ⟨T, GenericTy⟩)
  : (LExpr ⟨T, GenericTy⟩) :=
  go e 0
where
  go (e : LExpr ⟨T, GenericTy⟩) (depth : Nat) : LExpr ⟨T, GenericTy⟩ :=
    match e with
    | .const _ _ => e | .bvar _ _ => e | .op _ _ _ => e
    | .fvar _ name _ => if name == fr then liftBVars depth to else e
    | .abs m name ty e' => .abs m name ty (go e' (depth + 1))
    | .quant m qk name ty tr' e' => .quant m qk name ty (go tr' (depth + 1)) (go e' (depth + 1))
    | .app m fn e' => .app m (go fn depth) (go e' depth)
    | .ite m c t f => .ite m (go c depth) (go t depth) (go f depth)
    | .eq m e1 e2 => .eq m (go e1 depth) (go e2 depth)

/--
Simultaneous substitution of multiple free variables. Replaces all variables
in a single pass, avoiding variable capture between substitutions.

Does NOT lift de Bruijn indices when going under binders. Safe only when all
replacement expressions contain no bvars.
-/
def substFvars [BEq T.IDMeta] (e : LExpr ⟨T, GenericTy⟩) (sm : Map T.Identifier (LExpr ⟨T, GenericTy⟩))
  : LExpr ⟨T, GenericTy⟩ :=
  if sm.isEmpty then e else substFvarsAux e sm
where
  substFvarsAux (e : LExpr ⟨T, GenericTy⟩) (sm : Map T.Identifier (LExpr ⟨T, GenericTy⟩))
    : LExpr ⟨T, GenericTy⟩ :=
    match e with
    | .const _ _ => e | .bvar _ _ => e | .op _ _ _ => e
    | .fvar _ name _ => match sm.find? name with | some to => to | none => e
    | .abs m name ty e' => .abs m name ty (substFvarsAux e' sm)
    | .quant m qk name ty tr' e' => .quant m qk name ty (substFvarsAux tr' sm) (substFvarsAux e' sm)
    | .app m fn e' => .app m (substFvarsAux fn sm) (substFvarsAux e' sm)
    | .ite m c t e' => .ite m (substFvarsAux c sm) (substFvarsAux t sm) (substFvarsAux e' sm)
    | .eq m e1 e2 => .eq m (substFvarsAux e1 sm) (substFvarsAux e2 sm)

/--
Simultaneous substitution of multiple free variables with bvar-safe lifting.
Replaces all variables in a single pass, avoiding variable capture between
substitutions.

Properly lifts de Bruijn indices in replacement expressions when going under
binders. Use this when replacement expressions may contain bvars.
-/
def substFvarsLifting [BEq T.IDMeta] (e : LExpr ⟨T, GenericTy⟩) (sm : Map T.Identifier (LExpr ⟨T, GenericTy⟩))
  : LExpr ⟨T, GenericTy⟩ :=
  if sm.isEmpty then e else go e 0
where
  go (e : LExpr ⟨T, GenericTy⟩) (depth : Nat) : LExpr ⟨T, GenericTy⟩ :=
    match e with
    | .const _ _ => e | .bvar _ _ => e | .op _ _ _ => e
    | .fvar _ name _ => match sm.find? name with | some to => liftBVars depth to | none => e
    | .abs m name ty e' => .abs m name ty (go e' (depth + 1))
    | .quant m qk name ty tr' e' => .quant m qk name ty (go tr' (depth + 1)) (go e' (depth + 1))
    | .app m fn e' => .app m (go fn depth) (go e' depth)
    | .ite m c t f => .ite m (go c depth) (go t depth) (go f depth)
    | .eq m e1 e2 => .eq m (go e1 depth) (go e2 depth)


/--
Replace all user-provided type annotations in an `LExpr` using `f`.
-/
@[expose] def replaceUserProvidedType {T : LExprParamsT} (e : LExpr T) (f : T.TypeType → T.TypeType) : LExpr T :=
  match e with
  | .const m c => .const m c
  | .op m o uty => .op m o (uty.map f)
  | .bvar m b => .bvar m b
  | .fvar m x uty => .fvar m x (uty.map f)
  | .app m e1 e2 => .app m (replaceUserProvidedType e1 f) (replaceUserProvidedType e2 f)
  | .abs m name uty e => .abs m name (uty.map f) (replaceUserProvidedType e f)
  | .quant m qk name argTy tr e =>
    .quant m qk name (argTy.map f) (replaceUserProvidedType tr f) (replaceUserProvidedType e f)
  | .ite m c t f_expr =>
    .ite m (replaceUserProvidedType c f) (replaceUserProvidedType t f) (replaceUserProvidedType f_expr f)
  | .eq m e1 e2 => .eq m (replaceUserProvidedType e1 f) (replaceUserProvidedType e2 f)

end LExpr

end -- public section
end Lambda
