/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.Languages.Core.Counterexample.BackLinkChainReplay

/-! # Shared fixtures for the counterexample back-link tests

Term fixtures and outcome summarizers used by `ChainReplayTest`, `CallElimSlicingTest`,
`CounterexampleExtractionTest`, `ExactBackLinkTest` and `LoopElimSlicingTest`. Each test
keeps its own store builder `env`, whose shape differs per test. -/

meta section

public section

namespace Core.CexTestUtils

open Core _root_.Lambda Imperative

/-- An integer literal. -/
def int (n : Int) : Expression.Expr := .intConst default n

/-- Empty metadata. -/
def md : MetaData Expression := #[]

/-- An `int`-annotated variable. -/
def v (n : String) : Expression.Expr := .fvar default ⟨n, ()⟩ (some .int)

/-- The statements of a `.stmts` configuration. -/
def stmtsOf : IConfig Expression Command → Option (List Statement)
  | .stmts ss _ => some ss
  | _ => none

/-- An outcome's slice statements and its claim's statements, fuel and oracle. -/
def summary (o : BackLinkOutcome Expression Command) :
    List (Option (List Statement)) ×
      Option (Option (List Statement) × Nat × List Expression.Expr) :=
  (o.slices.map (stmtsOf ·.cfg), o.claim.map fun (c, f) => (stmtsOf c.cfg, f, c.oracle))

/-- The value of variable `x` in a configuration's store. -/
def valueOf (c : IConfig Expression Command) (x : String) : Option Expression.Expr :=
  c.getEnv.store.get ⟨x, ()⟩

/-- A default-value provider that supplies no value. -/
def noDefaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty →
    Option Expression.Expr := fun _ _ _ => none

/-- The empty procedure table. -/
def noPi : String → Option Procedure := fun _ => none

end Core.CexTestUtils

end -- public section

end -- meta section
