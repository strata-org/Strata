/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.Termination
public import Strata.Util.Monad

/-! # Analyses as definitions

An analysis is defined by a relation between a program and an output, saying
which outputs are correct answers about the program. An analyzer is a function
producing outputs, possibly in a monad. The two are separate: a definition can
have many analyzers, and `MatchesAnalysis` (or `MatchesAnalysisWhenOk`, for an
analyzer in a monad) states that one of them is correct. `ℙ` is written
double-struck (\bbP) to avoid clashing with the pure-expression parameter `P`.

It also defines when the runs of one program overapproximate those of another,
`EventLang.RunsOverapproximate`, and a verifier run after a sequence of
transformations, `thenVerify` and `runTransforms`, so that a verifier's
soundness on the transformed program can be carried back to the original.
-/

public section

namespace Imperative.Analysis

open Strata.Logic

variable {ℙ D : Type}

/-- `analyzer` implements `analysisDefinition`: on every program, the output it
    produces is one the definition accepts as correct. -/
@[expose] def MatchesAnalysis (analyzer : ℙ → D) (analysisDefinition : ℙ → D → Prop) : Prop :=
  ∀ p : ℙ, analysisDefinition p (analyzer p)

/-- **`analyzer` matches `analysisDefinition` whenever it completes normally**:
    every output it can return is one the definition accepts. An analyzer that
    fails, or never returns, claims nothing. -/
@[expose] def MatchesAnalysisWhenOk {m : Type → Type} [MonadIsSuccess m]
    (analyzer : ℙ → m D) (analysisDefinition : ℙ → D → Prop) : Prop :=
  ∀ p d, MonadIsSuccess.IsSuccess (analyzer p) d → analysisDefinition p d

/-- **Soundness** as an analysis definition: an output is correct when passing
    implies `property`, so a passing output claims `property`, and any other
    claims nothing. An analyzer matches it exactly when it passes only programs
    with the property. -/
def Sound (property : ℙ → Prop) (pass : D → Prop) : ℙ → D → Prop :=
  fun p d => pass d → property p

/-- **Completeness** as an analysis definition: an output is correct when
    `property` implies passing. An analyzer matches it exactly when it passes
    every program with the property. -/
def Complete (property : ℙ → Prop) (pass : D → Prop) : ℙ → D → Prop :=
  fun p d => property p → pass d

/-- Transform with `T`, then run `analyze` on the result. A statement `T`
    rejects does not pass. -/
@[expose] def thenVerify {P : PureExpr} {L₁ L₂ : Lang P} (T : L₁.StmtT → Option L₂.StmtT)
    (analyze : L₂.StmtT → Bool) (s : L₁.StmtT) : Bool :=
  match T s with
  | some s' => analyze s'
  | none => false

/-- Run transformations of one language in order, stopping at the first that
    rejects. -/
@[expose] def runTransforms {P : PureExpr} {L : Lang P} :
    List (L.StmtT → Option L.StmtT) → L.StmtT → Option L.StmtT
  | [], s => some s
  | T :: rest, s => (T s).bind (runTransforms rest)

end Imperative.Analysis

namespace Strata.Logic

open Imperative

variable {P : PureExpr}

/-- **The runs from `cfg₂` in `EL₂` overapproximate those from `cfg₁` in
    `EL₁` up to `R`**: every bounded path from `cfg₁` has a bounded path from
    `cfg₂` whose trace it is related to by `R`. The relation says what the
    overapproximation keeps: equality keeps every event, and a weaker one keeps
    only what an analysis reads. -/
@[expose] def EventLang.RunsOverapproximate {EventT₁ EventT₂ : Type}
    (R : List EventT₁ → List EventT₂ → Prop)
    (EL₁ : EventLang P EventT₁) (EL₂ : EventLang P EventT₂)
    (cfg₁ : EL₁.CfgT) (cfg₂ : EL₂.CfgT) : Prop :=
  ∀ n trace c, EL₁.ReachesWithin n cfg₁ trace c →
    ∃ m trace' c', EL₂.ReachesWithin m cfg₂ trace' c' ∧ R trace trace'

end Strata.Logic

end -- public section
