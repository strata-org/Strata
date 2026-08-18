/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.ProcedureType
public import Strata.Languages.Core.WF
public import Strata.Languages.Core.IdentifiersProps
public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.LExprTProps
public import Strata.DL.Lambda.Denote.LExprResolveAnnotated
public import Strata.DL.Lambda.LExprWF
import all Strata.Languages.Core.Identifiers
import all Strata.DL.Lambda.LExprTypeSpec
import all Strata.DL.Lambda.LExprTProps
import all Strata.DL.Lambda.Denote.LExprResolveAnnotated
import all Strata.DL.Lambda.LExprWF

public section

/-!
# `noOldFvars` for successfully type-checked preconditions

A precondition is resolved against `envWithInputs` (`setupInputEnv`:
`pushEmptyContext` + inputs); the corresponding well-formedness field
`WFPreProp.noOldFvars` inspects `getFvars` of the STORED (unresolved) expression.

### Key definitions
* `ResolvesInOrder` — inductive predicate capturing the env-threading shape of the
  `typeCheckConditions` fold (each condition resolves against the previous one's
  output env, `Env₀ → … → Envₙ`).

### Key results
* `env_no_pred_precond_no_pred` — conditional core (arbitrary predicate `P`): if
  no known var of the resolve env satisfies `P`, no output free var does.
* `env_no_pred_preserved_by_resolve` — transport step: the no-`P`-known-var
  invariant survives a successful `resolve`.
* `noOldFvars_of_resolve_in_inputEnv` — top-level bridge for a single expression
  resolved against `envWithInputs`: it has no `old`-prefixed free var.
* `noOldFvars_of_resolvesInOrder` — fold-level result over a whole `ResolvesInOrder`
  chain (a list of expressions resolved in sequence).

The chain assembled here, in detail:

* `env_no_pred_precond_no_pred` — CONDITIONAL CORE, stated for an arbitrary
  identifier predicate `P`. If no known var of the resolve env satisfies `P`,
  then no output free variable does. This is routed through the OUTPUT side of
  `resolve` (`resolve_getVars_mem_knownVars`, `getVars_unresolved` from
  `Lambda.LExpr.Proofs`). The output side is freshness-free: the generated binder
  is closed away by `varCloseT`, so every surviving output fvar is a known var of
  the input context. An input-side `WellScoped`-from-`resolve` route is NOT
  available — it would require the generated binder to be fresh in the body,
  which does not follow from `typeBoundVar`'s specification. Instantiated at
  `P := CoreIdent.isOldIdent` at the precondition call sites.

* `env_no_pred_preserved_by_resolve` — TRANSPORT STEP. `resolve` never adds a new
  known var to its output context (`resolve_knownVars_subset`), so the abstract
  "no known var satisfies `P`" invariant survives a successful `resolve` call.
  This is what lets the atomic result above apply to EVERY precondition typed
  by the fold in `typeCheckConditions`, not only the first: precondition `i+1`
  resolves against the previous call's output env, and the invariant it needs
  is exactly the invariant propagated by this transport step from precondition
  `i`.

* `noOldFvars_of_resolve_in_inputEnv` — the top-level bridge for a SINGLE
  expression resolved against `envWithInputs` directly (the shape the FIRST
  precondition takes). The statement is generic — nothing constrains the
  expression to be syntactically a precondition — so the name reflects the env,
  not the caller. Its env hypothesis is discharged by splitting
  `knownVars envWithInputs` into the input names (not `old` by
  `WFProcedureProp.ioNotOld`-shaped data) and the outer program scopes. There is
  currently no well-formedness invariant forbidding an `old`-named outer/global
  binding, so the outer part is carried as an EXPLICIT hypothesis
  `h_outer_no_old`; if such an invariant is added it plugs in here.  For a chain
  of expressions, compose this with `env_no_pred_preserved_by_resolve` along the
  fold.

* `noOldFvars_of_resolvesInOrder` — the FOLD-LEVEL result over a whole
  `ResolvesInOrder` chain (a list of expressions resolved in sequence — the
  abstract shape of the `typeCheckConditions` env-threading fold). Proved by
  list induction: the atomic `env_no_pred_precond_no_pred` (at
  `P := CoreIdent.isOldIdent`) discharges each head, and
  the three fold invariants (no-`old`-known-var, `TEnvWF`, `context.types ≠ []`)
  advance across each step via the transport lemmas above. This is the statement
  a `WFPreProp.noOldFvars` construction site consumes for a full precondition
  list; connecting `ResolvesInOrder` to the `private`, `for`-loop-shaped
  `typeCheckConditions` is left as a follow-up.
-/

namespace Core
namespace WF

open Lambda Lambda.LExpr.Proofs Imperative

/-- If no known var of the resolve env satisfies a predicate `P`, then no free
    variable of the STORED (unresolved) resolved expression does either. The
    predicate is arbitrary — the proof only forwards membership from
    `resolve_getVars_mem_knownVars` into the env hypothesis. -/
theorem env_no_pred_precond_no_pred
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : Lambda.LExprT Core.CoreLParams.mono)
    (P : CoreIdent → Prop)
    (h_env_no : ∀ v ∈ Lambda.TContext.knownVars Env.context, ¬ P v)
    (h : Lambda.LExpr.resolve C Env e = .ok (et, Env'))
    (h_envwf : Lambda.LExpr.TEnvWF (T := Core.CoreLParams) Env) (h_ne : Env.context.types ≠ [])
    (h_fwf : Lambda.FactoryWF C.functions) :
    ∀ id ∈ HasFvars.getFvars (P := Core.Expression) et.unresolved, ¬ P id := by
  intro id hid
  simp only [HasFvars.getFvars] at hid
  rw [getVars_unresolved] at hid
  exact h_env_no id (resolve_getVars_mem_knownVars C Env Env' e et h h_envwf h_ne h_fwf id hid)

/-- The abstract "no known var satisfies `P`" invariant survives a successful
    `resolve` call: `resolve` never adds a new known var (`resolve_knownVars_subset`),
    so any predicate that holds for all knowns of the input env holds for all
    knowns of the output env.  This is the transport step that lifts the atomic
    `env_no_pred_precond_no_pred` from the FIRST resolve call in a fold to every
    subsequent call: precondition `i+1` in `typeCheckConditions` resolves
    against the previous call's output env, and its no-`P`-known-var hypothesis
    is exactly what this step delivers from the previous iteration's. -/
theorem env_no_pred_preserved_by_resolve
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : Lambda.LExprT Core.CoreLParams.mono)
    (P : CoreIdent → Prop)
    (h_env_no : ∀ v ∈ Lambda.TContext.knownVars Env.context, ¬ P v)
    (h : Lambda.LExpr.resolve C Env e = .ok (et, Env'))
    (h_envwf : Lambda.LExpr.TEnvWF (T := Core.CoreLParams) Env) (h_ne : Env.context.types ≠ [])
    (h_fwf : Lambda.FactoryWF C.functions) :
    ∀ v ∈ Lambda.TContext.knownVars Env'.context, ¬ P v := by
  intro v hv
  exact h_env_no v (resolve_knownVars_subset C Env Env' e et h h_envwf h_ne h_fwf v hv)

/-- Splitting the known vars into input names and outer scopes, each of which is
    known to carry no identifier satisfying `P`, gives no `P`-satisfying known var
    overall.  Stated for an arbitrary predicate `P` (like the `env_no_pred_*`
    layer above); the proof only forwards membership through the split. -/
private theorem env_no_pred_of_split
    (Env : Core.Expression.TyEnv)
    (inputNames : List CoreIdent) (outer : List CoreIdent)
    (P : CoreIdent → Prop)
    (h_split : ∀ v ∈ Lambda.TContext.knownVars Env.context, v ∈ inputNames ∨ v ∈ outer)
    (h_in : ∀ v ∈ inputNames, ¬ P v)
    (h_out : ∀ v ∈ outer, ¬ P v) :
    ∀ v ∈ Lambda.TContext.knownVars Env.context, ¬ P v := by
  intro v hv
  rcases h_split v hv with h | h
  · exact h_in v h
  · exact h_out v h

/-- Top-level bridge for `WFPreProp.noOldFvars`.  Any expression resolved against
    `envWithInputs` carries no `old`-prefixed free variable in its STORED
    (unresolved) form, provided the known vars split into input names (not `old`)
    and outer scopes (carried as `h_outer_no_old`; no well-formedness invariant
    currently forbids an `old`-named outer/global binding).  The statement is
    generic in the expression — the intended instantiation is the FIRST
    precondition, which `typeCheckConditions` resolves against `envWithInputs`
    (the inputs-only pre-state env, before any `old` binding is introduced). -/
theorem noOldFvars_of_resolve_in_inputEnv
    (C : Core.Expression.TyContext) (envWithInputs Env' : Core.Expression.TyEnv)
    (precond : Core.Expression.Expr) (et : Lambda.LExprT Core.CoreLParams.mono)
    (h_resolve : Lambda.LExpr.resolve C envWithInputs precond = .ok (et, Env'))
    (h_envwf : Lambda.LExpr.TEnvWF (T := Core.CoreLParams) envWithInputs)
    (h_ne : envWithInputs.context.types ≠ [])
    (h_fwf : Lambda.FactoryWF C.functions)
    (inputNames outer : List CoreIdent)
    (h_split : ∀ v ∈ Lambda.TContext.knownVars envWithInputs.context,
                 v ∈ inputNames ∨ v ∈ outer)
    (h_io : ∀ id ∈ inputNames, ∀ x, id ≠ CoreIdent.mkOld x)
    (h_outer_no_old : ∀ v ∈ outer, ¬ CoreIdent.isOldIdent v) :
    ∀ id ∈ HasFvars.getFvars (P := Core.Expression) et.unresolved,
      ¬ CoreIdent.isOldIdent id := by
  have h_env_no_old : ∀ v ∈ Lambda.TContext.knownVars envWithInputs.context,
      ¬ CoreIdent.isOldIdent v :=
    env_no_pred_of_split envWithInputs inputNames outer (fun id => CoreIdent.isOldIdent id) h_split
      (fun v hv => not_isOldIdent_of_ne_mkOld v (h_io v hv)) h_outer_no_old
  exact env_no_pred_precond_no_pred C envWithInputs Env' precond et
    (fun id => CoreIdent.isOldIdent id) h_env_no_old h_resolve h_envwf h_ne h_fwf

/-- The precondition list resolves in sequence: each condition is resolved
    against the previous one's output env, threading `Env₀ → … → Envₙ`.  This is
    the abstract shape of the `typeCheckConditions` fold
    (`ProcedureType.lean`, which threads `currentEnv := newEnv` through
    `proc.spec.preconditions`); stating it inductively lets the fold-level
    `noOldFvars` result below be proved by list induction.  Wiring this predicate
    to the (`private`, `for`-loop-shaped) `typeCheckConditions` itself — so a
    `WFPreProp` constructor can discharge it for a fully type-checked procedure —
    is left as a follow-up. -/
inductive ResolvesInOrder (C : Core.Expression.TyContext) :
    List Core.Expression.Expr → List (Lambda.LExprT Core.CoreLParams.mono) →
    Core.Expression.TyEnv → Core.Expression.TyEnv → Prop where
  | nil (Env : Core.Expression.TyEnv) : ResolvesInOrder C [] [] Env Env
  | cons {Env Envₘ Envₙ : Core.Expression.TyEnv}
      {e : Core.Expression.Expr} {et : Lambda.LExprT Core.CoreLParams.mono}
      {conds : List Core.Expression.Expr}
      {ets : List (Lambda.LExprT Core.CoreLParams.mono)}
      (h_head : Lambda.LExpr.resolve C Env e = .ok (et, Envₘ))
      (h_rest : ResolvesInOrder C conds ets Envₘ Envₙ) :
      ResolvesInOrder C (e :: conds) (et :: ets) Env Envₙ

/-- Fold-level `noOldFvars`.  If the starting env's known vars carry no
    `old`-prefixed identifier, then EVERY expression in a `ResolvesInOrder` chain
    (not only the first) carries no `old`-prefixed free variable in its STORED
    (unresolved) form.  Stated generically over a list of expressions resolved in
    sequence; the intended instantiation is a full precondition list, so this is
    the statement `WFPreProp.noOldFvars` construction sites consume.  The
    induction advances three invariants across each fold step: the
    no-`old`-known-var hypothesis via `env_no_pred_preserved_by_resolve`, `TEnvWF`
    via `resolve_TEnvWF`, and `context.types ≠ []` via `resolve_preserves_context`
    + `TContext.Equiv.types_ne_nil`; the head is discharged by the atomic
    `env_no_pred_precond_no_pred` at `P := CoreIdent.isOldIdent`. -/
theorem noOldFvars_of_resolvesInOrder
    (C : Core.Expression.TyContext) (Env₀ Envₙ : Core.Expression.TyEnv)
    (conds : List Core.Expression.Expr)
    (ets : List (Lambda.LExprT Core.CoreLParams.mono))
    (h_fold : ResolvesInOrder C conds ets Env₀ Envₙ)
    (h_env_no_old : ∀ v ∈ Lambda.TContext.knownVars Env₀.context, ¬ CoreIdent.isOldIdent v)
    (h_envwf : Lambda.LExpr.TEnvWF (T := Core.CoreLParams) Env₀)
    (h_ne : Env₀.context.types ≠ [])
    (h_fwf : Lambda.FactoryWF C.functions) :
    ∀ et ∈ ets, ∀ id ∈ HasFvars.getFvars (P := Core.Expression) et.unresolved,
      ¬ CoreIdent.isOldIdent id := by
  induction h_fold with
  | nil => intro et h; simp at h
  | @cons Env Envₘ Envₙ e et conds ets h_head h_rest ih =>
    intro et' h_et' id h_id
    rw [List.mem_cons] at h_et'
    rcases h_et' with h_eq | h_tail
    · subst h_eq
      exact env_no_pred_precond_no_pred C Env Envₘ e et' (fun id => CoreIdent.isOldIdent id)
        h_env_no_old h_head h_envwf h_ne h_fwf id h_id
    · have h_env_no_old' : ∀ v ∈ Lambda.TContext.knownVars Envₘ.context,
          ¬ CoreIdent.isOldIdent v :=
        env_no_pred_preserved_by_resolve C Env Envₘ e et (fun id => CoreIdent.isOldIdent id)
          h_env_no_old h_head h_envwf h_ne h_fwf
      have h_envwf' : Lambda.LExpr.TEnvWF (T := Core.CoreLParams) Envₘ :=
        Lambda.resolve_TEnvWF e et C Env Envₘ h_head h_envwf h_fwf
      have h_ne' : Envₘ.context.types ≠ [] :=
        (Lambda.LExpr.resolve_preserves_context e et C Env Envₘ h_head h_envwf h_ne
          h_fwf).symm.types_ne_nil h_ne
      exact ih h_env_no_old' h_envwf' h_ne' et' h_tail id h_id

end WF
end Core

end -- public section
