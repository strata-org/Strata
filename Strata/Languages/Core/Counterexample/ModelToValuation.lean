/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.Model
public import Strata.Languages.Core.Interpreter
public import Strata.DL.Imperative.Counterexample.Valuation
import all Strata.DL.Imperative.Counterexample.Valuation

/-! # From level (c) to level (b): the valuation a solver model denotes, and its check

The `(c) → (b)` translation turns a lifted solver model (`FlaggedLExprModel`) into a
level-`(b)` counterexample, a runtime valuation of the obligation's variables
(`modelValuation`, self-completed with `valuationDefaults`), and decides it against the
obligation with the runtime VC check `runVCCheck`.  `runVCCheck` is a thin evaluator wrapper:
the shared genuineness implementation `Imperative.valuationObligationCheck'` instantiated with
the fuel-bounded evaluator `Core.evalBounded`.  Its verdict is an
`Imperative.CEValidationVerdict String`, printed by `CEValidationVerdict.describe`.  The
module has no dependency on the verification pipeline.

The values a model gives uninterpreted constants (a `ConstInterp`) enter the check through
the factory: `withConsts F I` is the factory in which each constant that `I` interprets has
its value as an inlined body, so evaluation under it reads the constant as that value and
every other operator as in `F`; `IsValuationObligationCexWith` is the level-`(b)`
counterexample property under it.

Key definitions: `flaggedModelToValuation`, `valuationDefaults`, `completeValuation`,
`modelValuation`, `runVCCheck`, `DistinctLiteralsAt`, `withConsts`,
`IsValuationObligationCexWith`.
-/

namespace Core

open _root_.Lambda Imperative

public section

/-- The `(c) → (b)` producer: turn the flagged solver model into the level-`(b)`
    counterexample — a runtime *valuation* (`RStore Expression`).  It keeps the
    bindings whose SMT term was successfully converted to a Core value (the
    `true`-flagged entries) and drops the flags; a name with no liftable binding
    is left unassigned (`none`).  Its self-completion `modelValuation` is the
    valuation that validity is decided against and that the `(b) → (a)`
    translation consumes. -/
def flaggedModelToValuation (model : FlaggedLExprModel) : RStore Expression :=
  fun name =>
    (model.find? fun (candidate, _, liftable) => liftable && candidate == name)
      |>.map (fun (_, value, _) => value)

/-- The defaults `completeValuation` binds for the obligation `obligation`: each name the
    obligation reads (`obligationReadVars`) mapped to the canonical value, in the factory `F`
    (`defaultValueIn`), of the type of its first typed read that has one. -/
def valuationDefaults (F : @Lambda.Factory CoreLParams) (obligation : ProofObligation Expression) :
    Std.HashMap Expression.Ident Expression.Expr :=
  (obligationReadVars obligation).foldl (fun m (name, mty) =>
    if m.contains name then m else
      match defaultValueIn F mty with
      | some v => m.insert name v
      | none => m) {}

/-- **Self-complete a level-`(b)` valuation.**  A solver model is *partial*: it
    assigns only what the query constrained, so a variable the verification
    condition happens to read may be absent (it is irrelevant to satisfiability, or
    its value was not liftable).  Reading it leaves the evaluation stuck, and the
    obligation check then reports `cantValidate` even though a counterexample
    exists.  Bind every such name to a canonical value of its annotated type.

    This cannot manufacture a false counterexample: validity is still *decided by
    evaluating* the assumptions and the goal under the completed valuation, so a
    completion that contradicts the model makes the assumptions reduce to `false`
    (`spurious`), never a spurious `genuine`.  It mirrors the self-completion
    `valuationToEnv` performs at level `(a)`, so both levels read the same store.

    `defaults` is the map `valuationDefaults` computes: a name the store leaves unbound
    gets its value in `defaults`, the canonical value of the type of its *first* typed
    read that has one. -/
def completeValuation (defaults : Std.HashMap Expression.Ident Expression.Expr)
    (store : RStore Expression) : RStore Expression :=
  fun name =>
    match store name with
    | some v => some v
    | none => defaults[name]?

/-- The level-`(b)` valuation a solver model denotes: the liftable bindings,
    self-completed with the defaults `defaults` of the obligation (`valuationDefaults`,
    `completeValuation`).  This is the store both the level-`(b)` check and the
    `(b) → (a)` reconstruction use, so the counterexample that is validated is the one
    that is lifted. -/
def modelValuation (defaults : Std.HashMap Expression.Ident Expression.Expr)
    (model : FlaggedLExprModel) : RStore Expression :=
  completeValuation defaults (flaggedModelToValuation model)

/-- The text of a runtime VC check's verdict: `genuine` (the model satisfies the obligation's
    satisfying condition), `spurious` (it does not), or `can't-validate` with the reason the
    evaluator got stuck. -/
def _root_.Imperative.CEValidationVerdict.describe : CEValidationVerdict String → String
  | .genuine => "genuine"
  | .spurious => "spurious"
  | .cantValidate reason => s!"can't-validate: {reason}"

/-- Run the VC check for a lifted model against an obligation under the
    fuel-bounded evaluator.  `isValidityCheck = true` asks whether the model is a
    counterexample (`A ∧ ¬Q` satisfiable); `false` asks whether the point is
    coverable (`A ∧ Q` satisfiable). -/
@[expose] def runVCCheck (F : @Lambda.Factory CoreLParams) (fuel : Nat)
    (liftedModel : List (Expression.Ident × Lambda.LExpr CoreLParams.mono × Bool))
    (obligation : ProofObligation Expression)
    (isValidityCheck : Bool) : CEValidationVerdict String :=
  Imperative.valuationObligationCheck' (.runtime (evalBounded fuel)) F
    (modelValuation (valuationDefaults F obligation) liftedModel) obligation isValidityCheck

/-- An advisory verdict record for one obligation: its label and the validator's
    verdict. -/
def formatVerdictRecord (label : String) (v : CEValidationVerdict String) : String :=
  s!"{label}: {v.describe}"

/-! ## The runtime evaluator of the check -/

/-- The runtime evaluator of the VC check at fuel `fuel`. -/
abbrev bcRuntime (fuel : Nat) :
    ObligationEvaluator Expression (@Lambda.Factory CoreLParams) Expression.Expr :=
  .runtime (evalBounded fuel)

/-- The values the runtime check computes for the `.distinct` entries of `obligation` on the
    store `s` are primitive literals (`LConst.isPrimitive`), the literals whose values are equal
    only when the literals are. -/
@[expose] def DistinctLiteralsAt (F : @Lambda.Factory CoreLParams) (fuel : Nat)
    (s : RStore Expression) (obligation : ProofObligation Expression) : Prop :=
  ∀ l es, PathConditionEntry.distinct l es ∈ obligation.assumptions.flatten →
    ∀ rs, es.mapM (evalBounded fuel F s) = some rs → ∀ r ∈ rs,
      ∃ c, c.isPrimitive = true ∧ r = .const default c

/-- `f` with the value `I` gives it as an inlined body, when `f` is an uninterpreted
    constant that `I` interprets; `f` itself otherwise. -/
@[expose] def interpretConst (I : ConstInterp) (f : LFunc CoreLParams) : LFunc CoreLParams :=
  match I.lookup f.name.name with
  | some v =>
    if isUninterpretedConst f then { f with body := some v, attr := f.attr.push .inline }
    else f
  | none => f

/-- `F` with every uninterpreted constant that `I` interprets given its value
    (`interpretConst`); every other function of `F` is unchanged. -/
@[expose] def withConsts (F : @Lambda.Factory CoreLParams) (I : ConstInterp) :
    @Lambda.Factory CoreLParams :=
  if I.isEmpty then F else Factory.ofArray (F.toArray.map (interpretConst I))

/-- A level-`(b)` counterexample with interpreted constants: the runtime valuation `store`
    violates the validity of `obligation` when the uninterpreted constants that `I` interprets
    take their values: for every factory `M` whose runtime factory is `withConsts F I`, every
    semantic valuation `store` denotes under `M` is a counterexample
    (`IsValuationObligationCex`). -/
@[expose] def IsValuationObligationCexWith (F : @Lambda.Factory CoreLParams) (I : ConstInterp)
    (store : RStore Expression) (obligation : ProofObligation Expression) : Prop :=
  ∀ M : Expression.Factory, InterpLang.rfactory M = withConsts F I →
    ∀ σ, StoreDenotes M store σ →
      Imperative.IsValuationObligationCex (P := Expression) M σ obligation

end -- public section

end Core
