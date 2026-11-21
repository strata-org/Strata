/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkPhases

/-! # The `(b)→(a)` producer, and the semantic-bridge predicates of its drive

The `(b)→(a)` producer `reconstructAssertionFromCexValuation` turns a level-`(b)` counterexample
(a `CexValuation`: a valuation of the obligation and an optional fuel) into the first
`BackLinkOutcome`, at the final passive unit.  `resolveCexValuationFuel` computes the fuel the
runtime attaches to a `CexValuation`.

On the good-obligation-shape branch (`checkObligationProgram = some f`) the producer emits a
claim without running the replay; its genuineness is proved by a drive at run/halt fuel `f + fb`,
where `fb` is the level-`(b)` counterexample's own validation fuel: `f` (`Block.stepBudget`)
counts statement steps, not the goal's evaluation depth.  The module also holds the
engine-independent predicates that drive needs beyond bounded level-`(b)` validity.

Key definitions: `reconstructAssertionFromCexValuation`, `ExtractBackLink.liftCexValuation`,
`resolveCexValuationFuel`, `ModelBinds`, `WellScopedObl`. -/

namespace Core

open Imperative

public section

/-- Every value of the runtime store `σ` is a value expression of the factory `F`
    (`LExpr.isValue`): the runtime counterpart of `WellFormedStore`. -/
@[expose] def RWellFormedStore (σ : RStore Expression) (F : @Lambda.Factory CoreLParams) : Prop :=
  ∀ x v, σ x = some v → Lambda.LExpr.isValue F v = true

/-! ## Semantic-bridge predicates

Bounded level-`(b)` validity says the goal is false on the *declarative* store — the
valuation threaded by the obligation's assumptions.  The drive needs it false in the
*reconstructed run store*, and needs the run to stay well-scoped.  `ModelBinds`
(model-adequacy: the valuation binds each input / nondet-write target with a
well-typed canonical value, and every free variable of the goal) and `WellScopedObl`
(each statement's reads are defined in the threaded store) supply that bridge. -/

/-- Model-adequacy clause 1 (env): the valuation binds each input / nondet-write
    target with a well-typed canonical value, else a default is available. -/
def ModelBindsEnvAdequate
    (link : ObligationExtraction.ExtractBackLink)
    (obligation : ProofObligation Expression)
    (factory : @Lambda.Factory CoreLParams)
    (store : RStore Expression) : Prop :=
  (∀ name ty, (name, ty) ∈ (PassiveUnit.forObligation link obligation).inputs →
      (∀ v, store name = some v →
        Lambda.LExpr.isValue factory v = true ∧ valueHasMonoType factory v ty = true)
      ∧ (store name = none → (defaultValueIn factory ty).isSome = true)) ∧
  (∀ name expectedType,
      ObligationExtraction.ExtractReplayEvent.nondetWrite name expectedType ∈ link.events →
      (∀ v, store name = some v →
        Lambda.LExpr.isValue factory v = true ∧
          (∀ ty, expectedType = some ty → valueHasType factory v ty = true))
      ∧ (store name = none →
          (expectedType.bind (fun ty => Lambda.LTy.toMonoType? ty)
            |>.bind (defaultValueIn factory)).isSome = true))

/-- Model-adequacy clause 2 (replay): every free variable of the goal is bound by
    the valuation, so self-completion never dodges the goal's failure. -/
def ModelBindsReplayAdequate
    (obligation : ProofObligation Expression)
    (store : RStore Expression) : Prop :=
  ∀ nameTy, nameTy ∈ (Lambda.LExpr.freeVars obligation.obligation) →
    store nameTy.fst ≠ none

/-- The model is adequate for replaying the obligation: it binds each input and nondeterministic
    write target with a well-typed value (or the target's type has a default), and it binds every
    free variable of the goal. -/
def ModelBinds
    (link : ObligationExtraction.ExtractBackLink)
    (obligation : ProofObligation Expression)
    (factory : @Lambda.Factory CoreLParams)
    (store : RStore Expression) : Prop :=
  ModelBindsEnvAdequate link obligation factory store ∧
  ModelBindsReplayAdequate obligation store

/-- Well-scopedness of the obligation program under the threaded store: each
    statement's read variables are defined when it runs. -/
def WellScopedObl (σ : RStore Expression) : Statements → Prop
  | [] => True
  | (.cmd (.cmd (.init name _ (.det e) _))) :: rest =>
      RStore.isDefined σ (Lambda.LExpr.freeVars e).unzip.fst ∧ σ name = none ∧
        WellScopedObl (RStore.update σ name e) rest
  | (.cmd (.cmd (.init name _ty .nondet _md))) :: rest =>
      σ name = none ∧
        WellScopedObl (RStore.update σ name (Lambda.LExpr.fvar default name none)) rest
  | (.cmd (.cmd (.assume _ e _))) :: rest =>
      RStore.isDefined σ (Lambda.LExpr.freeVars e).unzip.fst ∧ WellScopedObl σ rest
  | (.cmd (.cmd (.assert _ e _))) :: rest =>
      RStore.isDefined σ (Lambda.LExpr.freeVars e).unzip.fst ∧ WellScopedObl σ rest
  | (.cmd (.cmd (.cover _ e _))) :: rest =>
      RStore.isDefined σ (Lambda.LExpr.freeVars e).unzip.fst ∧ WellScopedObl σ rest
  | (.ite .nondet thenSs elseSs _) :: _ =>
      WellScopedObl σ thenSs ∧ WellScopedObl σ elseSs
  | _ :: rest => WellScopedObl σ rest

/-! ## The `(b)→(a)` producer

`reconstructAssertionFromCexValuation` turns a level-`(b)` counterexample into the first
`BackLinkOutcome` at the final passive unit; `ValuationToRunBackLinkValid` is its contract. -/

/-- The fuel-carrying `(b) → (a)` lift: the `BackLinkOutcome` of a level-`(b)`
    counterexample's `(env, oracle)` and optional fuel `cexFuel`.  When the obligation program
    has good shape (`predictedFuel = some f`) and `cexFuel = some fb`, it claims the `CexA` at
    fuel `f + fb` (enough to step the program and to re-evaluate the goal) without replaying;
    otherwise it replays with a guessed fuel. -/
@[expose] def ObligationExtraction.ExtractBackLink.liftCexValuation
    (link : ObligationExtraction.ExtractBackLink)
    (env : IEnv Expression) (oracle : List Expression.Expr)
    (predictedFuel : Option Nat) (π : String → Option Procedure)
    (target : AssertId Expression) (cexFuel : Option Nat)
    (defaultFuel : Nat := replayFuelGuess) :
    BackLinkOutcome Expression Command :=
  let topCfg : IConfig Expression Command := .stmts link.entryStatements env
  match predictedFuel, cexFuel with
  | some f, some fb =>
    ⟨[], some ({ cfg := topCfg, oracle }, f + fb)⟩
  | _, _ =>
    let candidate : CexCandidateA Expression Command :=
      { cfg := topCfg, oracle := oracle }
    match replayCandidate π target (fun _ _ _ => none) candidate defaultFuel with
    | some top => ⟨[], some top⟩
    | none => ⟨[{ cfg := topCfg, oracle }], none⟩

/-- The **fuel-carrying** `(b) → (a)` producer: consumes a `CexValuation` (valuation +
    optional fuel) and mints via `ExtractBackLink.liftCexValuation`, so the good-shape branch
    claims the `CexA` at `predictedFuel + fb` when the cex carries a fuel `fb`. -/
@[expose] def reconstructAssertionFromCexValuation (factory : @Lambda.Factory CoreLParams)
    (unit : PassiveUnit) (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink)
    (π : String → Option Procedure) (defaultFuel : Nat := replayFuelGuess)
    (cex : CexValuation) : BackLinkOutcome Expression Command :=
  match valuationToEnv factory unit obligation link cex.valuation with
  | .error _ => .empty
  | .ok (env, oracle) =>
    let predictedFuel := checkObligationProgram (unit.inputs.map (·.1)) link.entryStatements
    let target : AssertId Expression := { label := obligation.label, md := obligation.metadata }
    link.liftCexValuation env oracle predictedFuel π target cex.fuel defaultFuel

/-- Resolve the fuel at which `valuation` is a *bounded* level-`(b)` counterexample:
    `some cap` when the shared `valuationObligationCheck'` reduces the obligation to `false`
    under `evalBounded cap`, else `none`.  The runtime attaches this to a `CexValuation` so the
    producer can claim the reconstructed `CexA` at `predictedFuel + fb`; a `some fb`
    result is *sufficient* by construction (the check is `.genuine` at `fb`).

    One probe at the cap suffices: the fuel is only a budget, so any sufficient value is
    as good as the smallest, and `evalBounded cap` costs only what the evaluation needs. -/
@[expose] def resolveCexValuationFuel (factory : @Lambda.Factory CoreLParams)
    (obligation : ProofObligation Expression) (valuation : RStore Expression)
    (cap : Nat) (isValidityCheck : Bool := true) : Option Nat :=
  match Imperative.valuationObligationCheck' (P := Expression)
      (.runtime (evalBounded cap)) factory valuation obligation
      (isValidityCheck := isValidityCheck) with
  | .genuine => some cap
  | _ => none

end -- public section

end Core
