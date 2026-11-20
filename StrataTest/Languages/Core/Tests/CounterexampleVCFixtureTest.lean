/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Counterexample.ModelToValuation
meta import Strata.Languages.Core.Factory
meta import Strata.DL.Imperative.EvalContext

/-! # Fixture replay of the level-`(b)` validator (`runVCCheck`)

An advisory harness.  It loads `(obligation, model)` fixtures, replays each
through `Core.runVCCheck` (the level-`(b)` validator), and records the verdict as
a plain textual advisory record via `Core.formatVerdictRecord`.  It depends on no
reporting machinery (such as SARIF output).

Fixtures here are a small hand-made set so the harness builds and runs
standalone, with no pipeline or solver dependency. -/

meta section

namespace CounterexampleVCFixtureTest

open Imperative Lambda Core

/-- One fixture: a label, the obligation, the lifted solver model (flagged), and
    whether the check is a validity query (`A ∧ ¬Q`; `false` = coverability
    `A ∧ Q`). -/
structure Fixture where
  label : String
  obligation : ProofObligation Expression
  model : List (Expression.Ident × Lambda.LExpr CoreLParams.mono × Bool)
  isValidityCheck : Bool

private def mkObligation (label : String) (property : PropertyType)
    (goal : Expression.Expr) : ProofObligation Expression :=
  { label := label, property := property, assumptions := [],
    obligation := goal, metadata := MetaData.empty }

/-- Hand-made fixtures: a violated assert and a reached cover (`genuine`), and an assert
    that holds (`spurious`). -/
def fixtures : List Fixture :=
  [ -- An assert whose goal reduces to `false`: `A ∧ ¬Q` holds → genuine cex.
    { label := "assert-violated", obligation := mkObligation "assert-violated" .assert Core.false,
      model := [], isValidityCheck := true },
    -- An assert whose goal reduces to `true`: no counterexample → spurious.
    { label := "assert-holds", obligation := mkObligation "assert-holds" .assert Core.true,
      model := [], isValidityCheck := true },
    -- A cover whose goal reduces to `true` under the coverability query
    -- (`A ∧ Q`): the point is reachable-and-true → genuine.
    { label := "cover-reached", obligation := mkObligation "cover-reached" .cover Core.true,
      model := [], isValidityCheck := false } ]

/-- Default fuel for the fixture replay. -/
def fuel : Nat := 20000

/-- Replay one fixture through the level-`(b)` validator. -/
def runFixture (fx : Fixture) : Imperative.CEValidationVerdict String :=
  Core.runVCCheck Core.Factory fuel fx.model fx.obligation fx.isValidityCheck

/-- The advisory report: one record per fixture. -/
def advisoryReport : List String :=
  fixtures.map fun fx => Core.formatVerdictRecord fx.label (runFixture fx)

/-- info: ["assert-violated: genuine", "assert-holds: spurious", "cover-reached: genuine"] -/
#guard_msgs in
#eval advisoryReport

#guard (fixtures.map (fun fx => (runFixture fx).describe)) ==
  ["genuine", "spurious", "genuine"]

end CounterexampleVCFixtureTest
