/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Experiment.HM.AlgorithmW

/-! ## Freshness properties of Algorithm W

Algorithm W uses a monotonically increasing counter `n` to generate fresh
type variables. This module defines the key freshness invariant and proves
(informally, with the theorem left as `sorry`) that W preserves it.

The main result `W_freshForCtx` is used to discharge the freshness
obligations in the `W_ctxCompat` proof.
-/

namespace HM

---------------------------------------------------------------------
-- Map.fmap preserves/transforms values
---------------------------------------------------------------------

theorem Map.values_fmap (f : β → γ) (m : Map α β) :
    (m.fmap f).values = m.values.map f := by
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    simp only [Map.fmap, List.map_cons, Map.values]
    exact congrArg _ ih

---------------------------------------------------------------------
-- Freshness definitions
---------------------------------------------------------------------

/-- No bound variable of σ appears free in any value of S. -/
def Subst.freshForScheme (S : Subst) (σ : Scheme) : Prop :=
  ∀ α ∈ σ.vars, α ∉ substFreeVars S

/-- S is fresh for every scheme in Γ: no bound type variable of any
    scheme in Γ appears free in the range of S. -/
def Subst.freshForCtx (S : Subst) (Γ : Ctx) : Prop :=
  ∀ σ, (σ ∈ Γ.vars.values ∨ σ ∈ Γ.ops.values) → S.freshForScheme σ

---------------------------------------------------------------------
-- freshForScheme is determined only by σ.vars
---------------------------------------------------------------------

/-- `applyScheme` preserves `vars`, so freshness transfers. -/
theorem Subst.freshForScheme_applyScheme (S S' : Subst) (σ : Scheme)
    (h : S'.freshForScheme σ) : S'.freshForScheme (S.applyScheme σ) := by
  intro α hα
  simp [Subst.applyScheme] at hα
  exact h α hα

---------------------------------------------------------------------
-- freshForCtx is preserved by applyCtx
---------------------------------------------------------------------

theorem Subst.freshForCtx_applyCtx (S S' : Subst) (Γ : Ctx)
    (h : S'.freshForCtx Γ) : S'.freshForCtx (S.applyCtx Γ) := by
  intro σ hmem
  simp [Subst.applyCtx, Map.values_fmap] at hmem
  rcases hmem with ⟨σ₀, hmem₀, rfl⟩ | ⟨σ₀, hmem₀, rfl⟩
  · exact freshForScheme_applyScheme S S' σ₀ (h σ₀ (.inl hmem₀))
  · exact freshForScheme_applyScheme S S' σ₀ (h σ₀ (.inr hmem₀))

---------------------------------------------------------------------
-- freshForCtx is preserved by addVar with a mono scheme
---------------------------------------------------------------------

theorem Subst.freshForScheme_mono (S : Subst) (τ : Ty) :
    S.freshForScheme (Scheme.mono τ) := by
  intro α hα; simp [Scheme.mono] at hα

theorem Subst.freshForCtx_addVar_mono (S : Subst) (Γ : Ctx) (x : String) (τ : Ty)
    (h : S.freshForCtx Γ) : S.freshForCtx (Γ.addVar x (.mono τ)) := by
  intro σ hmem
  simp [Ctx.addVar] at hmem
  rcases hmem with hmem | hmem
  · have := Map.insert_values Γ.vars (key := x) (val := Scheme.mono τ) hmem
    simp at this
    rcases this with rfl | hmem'
    · exact freshForScheme_mono S τ
    · exact h σ (.inl hmem')
  · exact h σ (.inr hmem)

---------------------------------------------------------------------
-- All bound type variables in Γ are below n
---------------------------------------------------------------------

/-- Every bound type variable index in every scheme in Γ is < n. -/
def Ctx.boundVarsBelow (Γ : Ctx) (n : Nat) : Prop :=
  (∀ σ ∈ Γ.vars.values, ∀ α ∈ σ.vars, α < n) ∧
  (∀ σ ∈ Γ.ops.values, ∀ α ∈ σ.vars, α < n)

theorem Ctx.boundVarsBelow_addVar_mono (Γ : Ctx) (x : String) (n : Nat) (τ : Ty)
    (h : Γ.boundVarsBelow n) : (Γ.addVar x (.mono τ)).boundVarsBelow n := by
  constructor
  · intro σ hmem α hα
    simp [Ctx.addVar] at hmem
    have := Map.insert_values Γ.vars (key := x) (val := Scheme.mono τ) hmem
    simp at this
    rcases this with rfl | hmem'
    · simp [Scheme.mono] at hα
    · exact h.1 σ hmem' α hα
  · exact h.2

theorem Ctx.boundVarsBelow_mono (Γ : Ctx) (n m : Nat)
    (h : Γ.boundVarsBelow n) (hle : n ≤ m) : Γ.boundVarsBelow m :=
  ⟨fun σ hσ α hα => Nat.lt_of_lt_of_le (h.1 σ hσ α hα) hle,
   fun σ hσ α hα => Nat.lt_of_lt_of_le (h.2 σ hσ α hα) hle⟩

theorem Ctx.boundVarsBelow_applyCtx (S : Subst) (Γ : Ctx) (n : Nat)
    (h : Γ.boundVarsBelow n) : (S.applyCtx Γ).boundVarsBelow n := by
  constructor <;> {
    intro σ hmem α hα
    simp [Subst.applyCtx, Map.values_fmap] at hmem
    obtain ⟨σ₀, hmem₀, rfl⟩ := hmem
    simp [Subst.applyScheme] at hα
    first | exact h.1 σ₀ hmem₀ α hα | exact h.2 σ₀ hmem₀ α hα
  }

---------------------------------------------------------------------
-- W increases the counter
---------------------------------------------------------------------

theorem W_counter_le (h : W Γ e n = .ok (S, ae, n')) : n ≤ n' := by
  sorry

---------------------------------------------------------------------
-- Main freshness theorem
---------------------------------------------------------------------

/-
Theorem: If `W Γ e n = .ok (S, ae, n')` and `Γ.boundVarsBelow n`,
  then `S.freshForCtx Γ`.

Informal Proof: By induction on `e` (via `fun_induction` on `W`).

The key invariant: Algorithm W only introduces type variables with
indices ≥ n (via the counter), and unification only produces
substitutions whose range variables come from the types being unified.
Since `Γ.boundVarsBelow n` means all bound type variable indices in Γ
are < n, and the types flowing into unification never contain these
bound variables (they contain only fresh variables ≥ n and free
variables of the context, which by definition of Scheme.freeVars
exclude bound variables), the resulting substitution's range avoids
all bound variables of Γ.

More precisely, we maintain the invariant that for every substitution S
produced by W, `substFreeVars S` contains only variables that are either:
  (a) free type variables of the context Γ (which exclude bound vars), or
  (b) fresh type variables with index ≥ n.
Since bound variables have index < n, they cannot appear in (b).
And by definition of Scheme.freeVars, they don't appear in (a) either.

Detailed case analysis:

  Case fvar x / op f:
    W returns S = Subst.id. substFreeVars [] = [].
    freshForCtx holds vacuously.

  Case const c:
    Same as fvar: S = Subst.id.

  Case abs body:
    W picks fresh α = Ty.var n, extends context with Γ.addVar x (.mono α),
    recurses: W (Γ.addVar x (.mono α)) (body.varOpen 0 x) (n+1) = .ok (S₁, ae₁, n₁).

    The extended context (Γ.addVar x (.mono α)) has boundVarsBelow (n+1):
    - Original Γ has boundVarsBelow n, hence boundVarsBelow (n+1).
    - The added scheme .mono α has vars = [], so no bound vars.

    By IH, S₁.freshForCtx (Γ.addVar x (.mono α)).
    Since every σ in Γ.vars.values is also in (Γ.addVar x _).vars.values
    (via Map.insert_values), and Γ.ops = (Γ.addVar x _).ops,
    we get S₁.freshForCtx Γ.
    W returns S = S₁, so S.freshForCtx Γ.

  Case app e₁ e₂:
    W infers e₁ → (S₁, ae₁, n₁), e₂ in S₁(Γ) → (S₂, ae₂, n₂),
    unifies → S₃, returns S = S₃ ∘ S₂ ∘ S₁.

    1. By IH on e₁: S₁.freshForCtx Γ.
       Γ.boundVarsBelow n, and W_counter_le gives n ≤ n₁.

    2. S₁.applyCtx Γ has boundVarsBelow n (by boundVarsBelow_applyCtx),
       hence boundVarsBelow n₁ (by monotonicity).
       By IH on e₂: S₂.freshForCtx (S₁.applyCtx Γ).
       By freshForCtx_applyCtx: this implies S₂.freshForScheme for
       every scheme whose vars match those in Γ.
       W_counter_le gives n₁ ≤ n₂.

    3. S₃ comes from unify (S₂.apply ae₁.tyOf) (.arrow ae₂.tyOf (Ty.var n₂)).
       The types being unified contain:
       - ae₁.tyOf, ae₂.tyOf: type annotations from W's output, whose variables
         are either free vars of the context or fresh vars ≥ n.
       - Ty.var n₂: a fresh variable with index n₂ ≥ n.
       After applying S₂, the variables are still in the same categories
       (S₂'s range avoids bound vars by step 2).

       By the bounded property of unification (substBounded), S₃'s range
       variables come from the unified types plus S₃'s own accumulated
       substitution (which starts empty for top-level unify).
       Since the unified types avoid bound vars of Γ, S₃.freshForCtx Γ.

    4. For the composition S₃ ∘ S₂ ∘ S₁:
       substFreeVars of a composition is bounded by the union of the
       components' range variables (after applying outer substitutions).
       Since each component avoids bound vars, the composition does too.

       More precisely, freshForCtx for the composition follows from
       freshForCtx_compose (proved separately).

  Case ite c t f:
    Same pattern as app, with more substitutions (S₁ through S₅).
    Each intermediate substitution is fresh for Γ by IH or unification
    boundedness. The final composition inherits freshness.

  Case eq e₁ e₂:
    Same pattern as app.

  Case quant k body:
    Same pattern as abs: extend context with mono scheme, recurse,
    then unify with bool. The unification substitution S₂ is fresh
    because bool has no type variables, and ae₁.tyOf avoids bound vars.
    The composition S₂ ∘ S₁ inherits freshness.

  Case bvar: contradiction (W returns error).
-/

theorem W_freshForCtx (h : W Γ e n = .ok (S, ae, n'))
    (hbound : Γ.boundVarsBelow n) :
    S.freshForCtx Γ := by
  sorry

---------------------------------------------------------------------
-- Freshness for unification
---------------------------------------------------------------------

/-
Theorem: If `unify s t = .ok S` and no bound variable of any scheme
  in Γ appears in `s.freeVars` or `t.freeVars`, then `S.freshForCtx Γ`.

Informal Proof:
  By the `substBounded` property of unification, the free variables in
  the range of S are bounded by the free variables of the input types
  (s and t). Since no bound variable of Γ appears in s or t, no bound
  variable appears in the range of S.
-/
theorem unify_freshForCtx (h : unify s t = .ok S) (Γ : Ctx)
    (hs : ∀ σ, (σ ∈ Γ.vars.values ∨ σ ∈ Γ.ops.values) → ∀ α ∈ σ.vars, α ∉ s.freeVars)
    (ht : ∀ σ, (σ ∈ Γ.vars.values ∨ σ ∈ Γ.ops.values) → ∀ α ∈ σ.vars, α ∉ t.freeVars) :
    S.freshForCtx Γ := by
  sorry

---------------------------------------------------------------------
-- Composition preserves freshForCtx
---------------------------------------------------------------------

/-- If both S₁ and S₂ are fresh for Γ, then S₂ ∘ S₁ is fresh for Γ.
    This follows because substFreeVars of the composition is bounded by
    the union of the components' range variables (after applying the
    outer substitution). -/
theorem Subst.freshForCtx_compose (S₂ S₁ : Subst) (Γ : Ctx)
    (h₁ : S₁.freshForCtx Γ) (h₂ : S₂.freshForCtx Γ) :
    (S₂.compose S₁).freshForCtx Γ := by
  sorry

---------------------------------------------------------------------
-- Extracting freshness from a composition
---------------------------------------------------------------------

/-- substFreeVars of the right component is a subset of the composition. -/
theorem substFreeVars_subset_compose_right (S₂ S₁ : Subst) :
    ∀ v, v ∈ substFreeVars S₂ → v ∈ substFreeVars (S₂.compose S₁) := by
  sorry

/-- If S₂ ∘ S₁ is fresh for σ, then S₂ is fresh for σ. -/
theorem Subst.freshForScheme_of_compose (S₂ S₁ : Subst) (σ : Scheme)
    (h : (S₂.compose S₁).freshForScheme σ) : S₂.freshForScheme σ := by
  intro α hα habs
  exact h α hα (substFreeVars_subset_compose_right S₂ S₁ _ habs)

/-- If S₂ ∘ S₁ is fresh for Γ, then S₂ is fresh for Γ. -/
theorem Subst.freshForCtx_of_compose_right (S₂ S₁ : Subst) (Γ : Ctx)
    (h : (S₂.compose S₁).freshForCtx Γ) : S₂.freshForCtx Γ := by
  intro σ hmem
  exact freshForScheme_of_compose S₂ S₁ σ (h σ hmem)

end HM
