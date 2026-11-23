/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.ModelToValuation
public import Strata.Languages.Core.ObligationExtraction
public import Strata.Languages.Core.Counterexample.Run
public import Strata.DL.Imperative.Counterexample.Run
public import Strata.DL.Imperative.Counterexample.BackLink

/-! # From level (b) to level (a): valuations as runs, and the contract of the translation

The `(b) → (a)` translation turns a level-`(b)` counterexample (a valuation of an
obligation's variables) into the entry environment and oracle of a level-`(a)`
counterexample (`CexA`, a run of the program), the input of the engine replay
`Imperative.runReplay`.  It follows the Assertion Extraction link
(`ObligationExtraction.ExtractBackLink`): `PassiveUnit` separates the entry inputs from the
variables the passive program initializes, `valuationToEnv` performs the store/oracle split,
and `checkObligationProgram` checks the shape of an obligation program and predicts the
replay fuel.  Nothing here decides whether a candidate is genuine.

The module also states what the translation must achieve: the fuel-carrying level-`(b)`
counterexample (`CexValuation`, valid by `CexValuationValid`, through
`IsValuationObligationCexBounded` / `IsValuationObligationCovBounded`) and the contract
`ValuationToRunBackLinkValid` of a `(b) → (a)` back-link.

Key definitions: `PassiveUnit`, `checkObligationProgram`, `valuationToEnv`,
`IsValuationObligationCexBounded`, `IsValuationObligationCovBounded`, `CexValuation`,
`CexValuationValid`, `ValuationToRunBackLinkValid`.
-/

namespace Core

open _root_.Lambda Imperative

public section

abbrev OracleSeed := List Expression.Expr

/-- Context needed to distinguish entry inputs from variables initialized by
    the passive program. -/
structure PassiveUnit where
  inputs : List (CoreIdent × Lambda.LMonoTy)
  statements : Statements

/-- Infer true entry inputs at the Core boundary: typed obligation variables
    that are not initialized by the passive program. -/
def PassiveUnit.forObligation (link : ObligationExtraction.ExtractBackLink)
    (obligation : ProofObligation Expression) : PassiveUnit :=
  let initialized := Block.initVars link.entryStatements
  let inputs := (Core.ProofObligation.getVars obligation).filterMap fun (name, type?) =>
    match type? with
    | some ty => if name ∈ initialized then none else some (name, ty)
    | none => none
  { inputs, statements := link.entryStatements }

/-! ## Obligation-program shape check + predicted replay fuel

`checkObligationProgram` decides, computably, the program-shape assumptions the
`(b) → (a)` reconstruction proof needs, and on success predicts a replay-fuel
budget adequate to reach the target assert.  The remaining assumption (factory
well-formedness) is not a program property and is discharged separately
(`Lambda.FactoryWF`, proved for `Core.Factory`).

  * `Block.nondetIteLast` — every nondeterministic `.ite` is the sole/last element
    of its statement list (the left-nested singleton-`ite` tower shape that
    `toCoreProofObligationProgram` emits).  Kills the after-join drain.
  * `Block.onlyAssertLast` — every `.assert` is the last statement of its list, so an
    execution path holds at most one assert.
  * `Block.readsDefined defined` — store-independent well-scopedness: every read
    (det-`.init` RHS, `.assume`/`.assert`/`.cover` condition) has its free vars in
    the names defined so far (`defined`, seeded with the passive unit's declared
    inputs, grown by each on-path `.init`).  Once `valuationToEnv` supplies the
    inputs, replay never stalls on an undefined read.
  * `Block.stepBudget` — a structural over-approximation of the `Imperative.runInterp` iteration
    count to walk the entry program (admin framing + one per command).  Because a
    genuine verdict is preserved under fuel increase, an over-estimate suffices.
-/

/-- Decide the program-shape assumptions (`Block.nondetIteLast`, `Block.onlyAssertLast`,
    `Block.readsDefined`) and, on success, predict an adequate replay-fuel budget.  `none` = bad
    shape; `some fuel` = good shape and `fuel` replay steps suffice to reach the target assert. -/
def checkObligationProgram (inputs : List CoreIdent) (ss : Statements) : Option Nat :=
  if Block.nondetIteLast ss && Block.onlyAssertLast ss && Block.readsDefined inputs ss then
    some (Block.stepBudget ss)
  else
    none

/-- The `(b) → (a)` translation reading directly from a level-`(b)` counterexample
    runtime *valuation* (`RStore Expression`), rather than a flagged solver model.
    This is the shape the generic `(b) → (a)` specification quantifies over: a
    function from the level-`(b)` valuation to a level-`(a)` `BackLinkOutcome`.
    It performs the store/oracle split central to `(b) → (a)`, reading each required
    value from the valuation, and **self-completing** any replay-required name the
    valuation omits with a type-correct don't-care value (`defaultValueIn`):
    a name absent from the model is one the VC did not constrain, so its value is
    irrelevant to whether the counterexample replays.  An omitted nondeterministic write
    target is completed only when its type is known. -/
def valuationToEnv (factory : @Lambda.Factory CoreLParams)
    (unit : PassiveUnit) (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink) (valuation : RStore Expression) :
    Except StopReason (IEnv Expression × OracleSeed) := do
  if link.targetLabel != obligation.label then
    throw .extractionLinkDoesNotMatchObligation
  let mut inputBindings : LExprModel := []
  for (name, ty) in unit.inputs do
    let value ← match valuation name with
      | some value => pure value
      | none => match defaultValueIn factory ty with
        | some value => pure value
        | none => throw (.missingBinding name.name)
    if !Lambda.LExpr.isValue factory value then throw .expectedValueChoice
    if !valueHasMonoType factory value ty then throw .illTypedValue
    inputBindings := inputBindings ++ [(name, value)]
  let store : RStore Expression := fun name =>
    (inputBindings.find? fun (candidate, _) => candidate == name).map Prod.snd
  let mut oracle : OracleSeed := []
  for event in link.events do
    match event with
    | .branch takeThen =>
      oracle := oracle ++ [if takeThen then HasBool.tt else HasBool.ff]
    | .nondetWrite name expectedType =>
      let value ← match valuation name with
        | some value => pure value
        | none => match expectedType.bind (fun ty => Lambda.LTy.toMonoType? ty)
                        |>.bind (defaultValueIn factory) with
          | some value => pure value
          | none => throw (.missingBinding name.name)
      if !Lambda.LExpr.isValue factory value then throw .expectedValueChoice
      if let some ty := expectedType then
        if !valueHasType factory value ty then throw .illTypedValue
      oracle := oracle ++ [value]
  return ({ store := .ofStore store, factory }, oracle)

/-- **Fuel-bounded level-`(b)` validity.**  `store` is a level-`(b)` counterexample
    to `obligation` whose VC decides at fuel `fb`: the obligation check under the
    *bounded* evaluator `evalBounded fb` (assumptions reduce to `true`, goal to `ff`)
    returns `.genuine`.  Carrying `fb : Nat` makes the fuel **present**, and
    `= .genuine` under `evalBounded fb` makes it **sufficient** (a too-small `fb`
    leaves `evalBounded fb = none`, so the check is not `.genuine`).  This is the
    runtime, fuel-carrying level-`(b)` notion — homogeneous with the fuel of a
    `BackLinkOutcome.claim` at level `(a)` — used in place of the pure-logic
    `IsValuationObligationCex` (which uses the unbounded `P.eval` and is too weak to drive the
    bounded replay whose halt predicate `assertFailureHalt` evaluates with
    `evalBounded`). -/
@[expose] def IsValuationObligationCexBounded
    (factory : @Lambda.Factory CoreLParams) (store : RStore Expression)
    (obligation : ProofObligation Expression) (fb : Nat) : Prop :=
  Imperative.valuationObligationCheck' (P := Expression)
    (.runtime (evalBounded fb)) factory store obligation
    (isValidityCheck := true) = .genuine

/-- The **cover** dual of `IsValuationObligationCexBounded`: a fuel-bounded level-`(b)`
    *reachability* witness.  A cover obligation is discharged by finding a model
    where its goal is **true** (the point is coverable), so the check runs at
    `isValidityCheck := false` — `valuationObligationCheck'` then reports `.genuine` exactly
    when the assumptions reduce true and the goal reduces to the **true** literal
    (dual to the assert case's false literal). -/
@[expose] def IsValuationObligationCovBounded
    (factory : @Lambda.Factory CoreLParams) (store : RStore Expression)
    (obligation : ProofObligation Expression) (fb : Nat) : Prop :=
  Imperative.valuationObligationCheck' (P := Expression)
    (.runtime (evalBounded fb)) factory store obligation
    (isValidityCheck := false) = .genuine

/-- A **level-`(b)` counterexample**: a valuation paired with an optional fuel at
    which it is claimed to violate the obligation.  Modeling the pair explicitly
    (rather than a bare valuation) makes the fuel part of the level-`(b)` datum,
    homogeneous with the fuel of a `BackLinkOutcome.claim` at level `(a)`.
    `fuel = some fb` is a *bounded* claim (validated at `fb`); `fuel = none` is the
    pure-logic claim (must be replayed to validate). -/
structure CexValuation where
  valuation : RStore Expression
  fuel : Option Nat := none

/-- Validity of a level-`(b)` counterexample.  A `some fb` claim is valid iff the
    bounded check succeeds **at that fuel**: for an assert obligation, the valuation
    violates it (`IsValuationObligationCexBounded … fb`); for a cover obligation, the
    valuation reaches it with the goal true (`IsValuationObligationCovBounded … fb`).  If
    the VC only reduces at a *larger* fuel, the `some fb` claim is INVALID (the fuel
    must be present *and sufficient*).  A `none` fuel makes **no claim**, so it is
    trivially valid (the level-`(b)` analogue of a level-`(a)` outcome without a
    claim): a `(b)→(a)` back-link given a `none`-fuel `CexValuation` cannot trust a bounded
    claim and must establish any claim itself (e.g. by the level-`(a)` replay). -/
@[expose] def CexValuationValid (factory : @Lambda.Factory CoreLParams)
    (obligation : ProofObligation Expression) (cex : CexValuation) : Prop :=
  match cex.fuel with
  | some fb =>
    if obligation.property = Imperative.PropertyType.cover
      then IsValuationObligationCovBounded factory cex.valuation obligation fb
      else IsValuationObligationCexBounded factory cex.valuation obligation fb
  | none => True

/-- `(b)→(a)` back-link validity contract over the engine: every **valid level-`(b)`
    counterexample** (`CexValuationValid`) yields a `ValidOutcome` outcome — i.e. one whose
    top-level cex replays, through the engine (`replayWithM`, callees via `π`), to the
    **target** assertion `target`.  The contract quantifies over a `CexValuation`, not a bare
    store, so the link sees the cex's fuel; the cases are those of `CexValuationValid`. -/
@[expose] def ValuationToRunBackLinkValid (π : String → Option Procedure)
    (target : AssertId Expression)
    (factory : @Lambda.Factory CoreLParams) (obligation : ProofObligation Expression)
    (stmts : List (Stmt Expression Command))
    (link : CexValuation → BackLinkOutcome Expression Command) : Prop :=
  ∀ (cex : CexValuation), CexValuationValid factory obligation cex →
    ValidOutcome π target stmts (link cex)

end -- public section

end Core
