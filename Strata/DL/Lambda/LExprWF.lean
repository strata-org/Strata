/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LExpr
public import Strata.Util.ListUtilsProps
public import Strata.Util.ListMapProps
public import Strata.Util.HMap

/-! ## Well-formedness of Lambda Expressions

See the definition `Lambda.LExpr.WF`. Also see theorem `HasType.regularity` in
`Strata.DL.Lambda.LExprTypeSpec`.

Key theorems:

- `LExpr.freeVars_eq_freeVarsFast` (`@[csimp]`) — `freeVars` and its
  linear-time implementation `freeVarsFast` agree; the compiler emits
  `freeVarsFast` wherever compiled code calls `freeVars`.

This theorem lives here rather than in `LExprWFProps.lean` because `@[csimp]`
substitution only applies in modules that import the file containing the
theorem.
-/

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)
open Strata.Util (HMap)

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
Accumulator-passing form of `freeVars`: prepends the free variables
of `e` onto `acc`.
-/
private def freeVarsAcc (e : LExpr ⟨T, GenericTy⟩) (acc : IdentTs GenericTy T.IDMeta) :
    IdentTs GenericTy T.IDMeta :=
  match e with
  | .const _ _ => acc
  | .op _ _ _ => acc
  | .bvar _ _ => acc
  | .fvar _ x ty => (x, ty) :: acc
  | .abs _ _ _ e1 => freeVarsAcc e1 acc
  | .quant _ _ _ _ tr e1 => freeVarsAcc tr (freeVarsAcc e1 acc)
  | .app _ e1 e2 => freeVarsAcc e1 (freeVarsAcc e2 acc)
  | .ite _ c t e => freeVarsAcc c (freeVarsAcc t (freeVarsAcc e acc))
  | .eq _ e1 e2 => freeVarsAcc e1 (freeVarsAcc e2 acc)

omit [DecidableEq T.IDMeta] in
private theorem freeVarsAcc_eq (e : LExpr ⟨T, GenericTy⟩) (acc : IdentTs GenericTy T.IDMeta) :
    freeVarsAcc e acc = freeVars e ++ acc := by
  induction e generalizing acc with
  | const _ _ =>
    rw [freeVarsAcc, freeVars, List.nil_append]
  | op _ _ _ =>
    rw [freeVarsAcc, freeVars, List.nil_append]
  | bvar _ _ =>
    rw [freeVarsAcc, freeVars, List.nil_append]
  | fvar _ _ _ =>
    rw [freeVarsAcc, freeVars, List.singleton_append]
  | abs _ _ _ _ ih =>
    rw [freeVarsAcc, freeVars, ih]
  | quant _ _ _ _ _ _ ih_tr ih_e1 =>
    rw [freeVarsAcc, freeVars, ih_e1, ih_tr, List.append_assoc]
  | app _ _ _ ih1 ih2 =>
    rw [freeVarsAcc, freeVars, ih2, ih1, List.append_assoc]
  | ite _ _ _ _ ih_c ih_t ih_e =>
    rw [freeVarsAcc, freeVars, ih_e, ih_t, ih_c, List.append_assoc, List.append_assoc]
  | eq _ _ _ ih1 ih2 =>
    rw [freeVarsAcc, freeVars, ih2, ih1, List.append_assoc]

/-- Linear-time implementation of `freeVars`. -/
def freeVarsFast (e : LExpr ⟨T, GenericTy⟩) : IdentTs GenericTy T.IDMeta :=
  freeVarsAcc e []

/-- `freeVars` and `freeVarsFast` agree so the compiler emits
    `freeVarsFast` whenever `freeVars` is called. -/
@[csimp]
theorem freeVars_eq_freeVarsFast : @freeVars = @freeVarsFast := by
  funext T GenericTy e
  unfold freeVarsFast
  rw [freeVarsAcc_eq, List.append_nil]

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
Worker for `betaReduceWith`/`betaReduce` at binder depth `k` (mirrors `substK`):
replace bound variable `k` with `liftBVars k (s m) 0`, decrement bound variables
above `k`, and leave those below `k` (local binders) untouched.
-/
def betaReduceK {T : LExprParamsT} (k : Nat) (s : T.base.Metadata → LExpr T) (e : LExpr T) : LExpr T :=
  match e with
  | .bvar m i => if i == k then liftBVars k (s m) 0 else if i > k then .bvar m (i - 1) else .bvar m i
  | .abs m n ty b => .abs m n ty (betaReduceK (k + 1) s b)
  | .quant m qk n ty tr b => .quant m qk n ty (betaReduceK (k + 1) s tr) (betaReduceK (k + 1) s b)
  | .app m a b => .app m (betaReduceK k s a) (betaReduceK k s b)
  | .ite m c t f => .ite m (betaReduceK k s c) (betaReduceK k s t) (betaReduceK k s f)
  | .eq m a b => .eq m (betaReduceK k s a) (betaReduceK k s b)
  | .const m c => .const m c
  | .op m o ty => .op m o ty
  | .fvar m x ty => .fvar m x ty

/--
Capture-avoiding β-substitution with a metadata-aware replacement: replace the
outermost bound variable (index 0) of `body` with `s m` (where `m` is that
occurrence's metadata), decrement every remaining bound variable by one, and
lift the replacement's free bound variables by the binder depth. Metadata-
preserving generalization of `betaReduce`; coincides with `subst s` on
locally-closed input — see `betaReduceWith_eq_subst_of_lc`.
-/
def betaReduceWith {T : LExprParamsT} (s : T.base.Metadata → LExpr T) (body : LExpr T) : LExpr T :=
  betaReduceK 0 s body

/--
Capture-avoiding β-substitution for a single redex: replace the outermost bound
variable (index 0) of `body` with `arg`, decrement every remaining bound
variable (those referred to *enclosing* binders) by one, and lift `arg`'s own
free bound variables by the binder depth at each substitution site. Unlike
`subst`, this performs both the index shift β-reducing a *nested* redex requires
and the argument lift needed when `arg` itself mentions enclosing binders (e.g.
a `let`-alias `var t := field(c)` whose argument refers to an outer pattern
binding `c`). On a locally-closed redex (`body` closed at 1, `arg` closed at 0)
it coincides with `subst (fun _ => arg)` — see `betaReduce_eq_subst_of_lc`.
-/
def betaReduce {T : LExprParamsT} (arg : LExpr T) (body : LExpr T) : LExpr T :=
  betaReduceWith (fun _ => arg) body

/-- Does the bound variable with index `k` occur in `e` (counting binders as we
descend)? Used to tell a genuine alias redex `(λ x. … x …) a` (bvar 0 used)
apart from a constant-lambda redex `(λ _. e0) a` (bvar 0 unused), whose argument
`a` a `betaReduce` would erase. -/
def bvarUsed {T : LExprParamsT} (k : Nat) (e : LExpr T) : Bool :=
  match e with
  | .bvar _ i => i == k
  | .abs _ _ _ b => bvarUsed (k + 1) b
  | .quant _ _ _ _ tr b => bvarUsed (k + 1) tr || bvarUsed (k + 1) b
  | .app _ a b => bvarUsed k a || bvarUsed k b
  | .ite _ c t f => bvarUsed k c || bvarUsed k t || bvarUsed k f
  | .eq _ a b => bvarUsed k a || bvarUsed k b
  | _ => false

/-- Worker for `betaReduceRedexesFuel`: reduces `e`, answering `none` when
nothing was reduced. -/
def betaReduceRedexesFuel? {T : LExprParamsT}
    (keepConstantRedexes : Bool) (fuel : Nat) (e : LExpr T) : Option (LExpr T) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match e with
    | .app m fn arg =>
      let ra := betaReduceRedexesFuel? keepConstantRedexes fuel arg
      let rf := betaReduceRedexesFuel? keepConstantRedexes fuel fn
      match rf.getD fn with
      | .abs _ _ _ body =>
        if keepConstantRedexes && !bvarUsed 0 body then
          -- Constant lambda: reducing would erase `arg`. Keep the redex so `arg`
          -- (and any recursive call inside it) remains syntactically present.
          -- Reuses rather than rebuilding the `.abs`, so an
          -- unchanged `fn` stays pointer-identical in the result.
          if ra.isNone && rf.isNone then none
          else some (.app m (rf.getD fn) (ra.getD arg))
        else
          -- A redex is contracted here, so this subterm does change.
          let contracted := betaReduce (ra.getD arg) body
          some ((betaReduceRedexesFuel? keepConstantRedexes fuel contracted).getD contracted)
      | fn' =>
        if ra.isNone && rf.isNone then none else some (.app m fn' (ra.getD arg))
    | .abs m n t body =>
      (betaReduceRedexesFuel? keepConstantRedexes fuel body).map (.abs m n t ·)
    | .ite m c t f =>
      let rc := betaReduceRedexesFuel? keepConstantRedexes fuel c
      let rt := betaReduceRedexesFuel? keepConstantRedexes fuel t
      let rf := betaReduceRedexesFuel? keepConstantRedexes fuel f
      if rc.isNone && rt.isNone && rf.isNone then none
      else some (.ite m (rc.getD c) (rt.getD t) (rf.getD f))
    | .eq m a b =>
      let ra := betaReduceRedexesFuel? keepConstantRedexes fuel a
      let rb := betaReduceRedexesFuel? keepConstantRedexes fuel b
      if ra.isNone && rb.isNone then none
      else some (.eq m (ra.getD a) (rb.getD b))
    | .quant m qk n t tr body =>
      let rtr := betaReduceRedexesFuel? keepConstantRedexes fuel tr
      let rb := betaReduceRedexesFuel? keepConstantRedexes fuel body
      if rtr.isNone && rb.isNone then none
      else some (.quant m qk n t (rtr.getD tr) (rb.getD body))
    | _ => none

/-- Shared worker for `betaReduceRedexes` (erasing) and
`betaReduceRedexesPreservingArgs` (non-erasing), fuel-bounded so it is a *total*
definition we can reason about (see `getOps_subset_betaReduceRedexesFuel`).

`fuel` bounds the reduction depth: structural descent and each redex contraction
consume one unit. On exhaustion the (possibly still-reducible) term is returned
unchanged, so the reduction is best-effort by construction: no fuel budget can
guarantee a normal form (an ill-typed self-applying term such as Ω never
terminates at any budget). Exhaustion is safe for callers: consumers that
require abstraction-free results must check for residual abstractions
themselves, and analyses relying on call preservation stay sound because
`getOps` is preserved at *every* fuel (`getOps_subset_betaReduceRedexesFuel`
in `LExprWFProps` holds for all fuel,
even `0`).

When `keepConstantRedexes` is `true`, a redex `(λ _. e0) arg` whose body does
*not* use its bound variable is left un-reduced, so `arg` survives in the term;
otherwise the redex is β-reduced and `arg` is erased (`betaReduce` drops the
argument of a constant lambda). -/
def betaReduceRedexesFuel {T : LExprParamsT}
    (keepConstantRedexes : Bool) (fuel : Nat) (e : LExpr T) : LExpr T :=
  (betaReduceRedexesFuel? keepConstantRedexes fuel e).getD e

/-- Count occurrences of the bound variable introduced `d` binders out (i.e. the
`.bvar` leaves with index `d` at this depth). Helper for `maxBvarMultiplicity`. -/
private def countVarAtDepth {T : LExprParamsT} (d : Nat) : LExpr T → Nat
  | .bvar _ i => if i == d then 1 else 0
  | .abs _ _ _ b => countVarAtDepth (d + 1) b
  | .quant _ _ _ _ tr b => countVarAtDepth (d + 1) tr + countVarAtDepth (d + 1) b
  | .app _ a b => countVarAtDepth d a + countVarAtDepth d b
  | .ite _ c t f => countVarAtDepth d c + countVarAtDepth d t + countVarAtDepth d f
  | .eq _ a b => countVarAtDepth d a + countVarAtDepth d b
  | _ => 0

/-- The maximum number of times any binder's own bound variable is referenced in
its body. β-reducing a redex `(λ x. body) arg` duplicates `arg` once per
occurrence of `x` in `body`, so this bounds the size blow-up of a single
reduction step. The `betaReduceRedexes*` wrappers scale their fuel budget by
`(this + 1)` so that a duplicating redex (e.g. `(fun x => x + x + x)(arg)`)
gets enough budget in the common single-level case. This is a heuristic: full
reduction is not guaranteed in general (nested duplicating redexes compound
multiplicatively), and on exhaustion the partially-reduced term is returned
unchanged, which every caller must (and does) tolerate. -/
def maxBvarMultiplicity {T : LExprParamsT} : LExpr T → Nat
  | .abs _ _ _ b => Nat.max (countVarAtDepth 0 b) (maxBvarMultiplicity b)
  | .quant _ _ _ _ tr b => Nat.max (maxBvarMultiplicity tr) (maxBvarMultiplicity b)
  | .app _ a b => Nat.max (maxBvarMultiplicity a) (maxBvarMultiplicity b)
  | .ite _ c t f => Nat.max (maxBvarMultiplicity c) (Nat.max (maxBvarMultiplicity t) (maxBvarMultiplicity f))
  | .eq _ a b => Nat.max (maxBvarMultiplicity a) (maxBvarMultiplicity b)
  | _ => 0

/-- Is no subterm of `e` an `.app` of an `.abs`? The shape the SMT encoder
    rejects, and what `betaReduceRedexes` contracts. Checked syntactically
    rather than by running the reduction, whose fuel bound would let a
    residual redex pass. -/
@[expose] def noBetaRedex {T : LExprParamsT} : LExpr T → Bool
  | .app _ (.abs ..) _ => false
  | .app _ fn arg => noBetaRedex fn && noBetaRedex arg
  | .abs _ _ _ body => noBetaRedex body
  | .quant _ _ _ _ trigger body => noBetaRedex trigger && noBetaRedex body
  | .ite _ c t e => noBetaRedex c && noBetaRedex t && noBetaRedex e
  | .eq _ e₁ e₂ => noBetaRedex e₁ && noBetaRedex e₂
  | .const .. | .op .. | .bvar .. | .fvar .. => true

/--
β-reduce directly-applied lambda redexes `(.app (.abs body) arg)` everywhere in
`e`, substituting the argument for the bound variable (via `betaReduce`, which
shifts indices correctly for nested redexes). This eliminates `let`-alias
redexes `(λ x. body) v` — the shape a binding that names an intermediate value
lowers to — so the residual term is free of such spurious abstractions.

NOTE: this reduction is *value-preserving but not call-preserving*: a constant
lambda `(λ _. e0) arg` reduces to `e0`, erasing `arg`. That is fine for
value-level consumers (the argument is dead code) but unsound for any syntactic
analysis that must see every subterm, such as extracting the calls a term
makes — use `betaReduceRedexesPreservingArgs` there.
-/
def betaReduceRedexes {T : LExprParamsT} (e : LExpr T) : LExpr T :=
  betaReduceRedexesFuel false (sizeOf e * (maxBvarMultiplicity e + 1)) e

/--
Like `betaReduceRedexes`, but never erases a redex's argument: a constant-lambda
redex `(λ _. e0) arg` (bound variable unused) is left un-reduced so that `arg` —
and any recursive call hidden inside it — stays syntactically present.

For syntactic analyses whose soundness depends on every call remaining in the
term (e.g. recursive-call extraction): plain `betaReduceRedexes` would drop
`arg`, so a call wrapped in `(λ _. 0) (f x)` would vanish from the term before
the analysis sees it. Alias redexes (bound variable used, e.g.
`(λ c. … tl(c) …) xs`) are still reduced. Call preservation is
`getOps_subset_betaReduceRedexesPreservingArgs`.
-/
def betaReduceRedexesPreservingArgs {T : LExprParamsT} (e : LExpr T) : LExpr T :=
  betaReduceRedexesFuel true (sizeOf e * (maxBvarMultiplicity e + 1)) e

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
Simultaneous substitution of operator references (`.op`).  Replaces every
`.op name ty` whose `name` is a key of `sm` with `(sm name) ty` — i.e. the
mapped *builder* is applied to that occurrence's own type annotation `ty`, so
the replacement can be annotated in terms of the original one.  A single
structural pass, keyed on operator names (mirrors `substFvars`, which is keyed
on free variables).

Like `substFvars`, this does NOT lift de Bruijn indices when going under
binders, so it is safe only when the replacement expressions contain no bvars.
(This holds for the closure-conversion use in `LiftInternalFuncDecls`, where a
replacement is an operator reference applied to free snapshot variables.)
-/
def substOps [Hashable T.IDMeta] (e : LExpr ⟨T, GenericTy⟩)
    (sm : HMap T.Identifier (Option GenericTy → LExpr ⟨T, GenericTy⟩))
  : LExpr ⟨T, GenericTy⟩ :=
  if sm.isEmpty then e else substOpsAux e sm
where
  substOpsAux (e : LExpr ⟨T, GenericTy⟩)
      (sm : HMap T.Identifier (Option GenericTy → LExpr ⟨T, GenericTy⟩))
    : LExpr ⟨T, GenericTy⟩ :=
    match e with
    | .const _ _ => e | .bvar _ _ => e | .fvar _ _ _ => e
    | .op _ name ty => match sm.find? name with | some mk => mk ty | none => e
    | .abs m name ty e' => .abs m name ty (substOpsAux e' sm)
    | .quant m qk name ty tr' e' => .quant m qk name ty (substOpsAux tr' sm) (substOpsAux e' sm)
    | .app m fn e' => .app m (substOpsAux fn sm) (substOpsAux e' sm)
    | .ite m c t e' => .ite m (substOpsAux c sm) (substOpsAux t sm) (substOpsAux e' sm)
    | .eq m e1 e2 => .eq m (substOpsAux e1 sm) (substOpsAux e2 sm)

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
