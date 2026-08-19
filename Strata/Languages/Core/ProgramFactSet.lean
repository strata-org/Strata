/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.ProgramFact
public import Strata.Languages.Core.ProgramFactProps
public import Strata.Pipeline.FactSet
public import Strata.Pipeline.FactSetProps
public import Strata.Pipeline.PhaseContract
public import Strata.Pipeline.PhaseContractProps

/-! # Fact sets for Core

`ProgramFactSet` is the language-neutral `Strata.Pipeline.FactSet` at
`ProgramFact`: a set of facts whose representation is unique, so that it can
index `ValidatedPipeline` — `[a, b]` and `[b, a]` must not be two types for one
set, or two pipelines agreeing on the facts they exchange would fail to
typecheck.

This module is the Core-side spelling of that machinery: the notation for a
written-out set, and names for the operations. Everything they stand on —
canonicity, the union, intersection and inclusion the composition check uses,
and the diagnostics — lives in `Strata/Pipeline`, so Laurel can reuse it with a
fact vocabulary of its own. -/

namespace Core

open Strata.Pipeline

public section

/-- A set of program facts known to hold on a program at a point in a pipeline. -/
@[expose] abbrev ProgramFactSet := FactSet ProgramFact

/-- The empty fact set: nothing is known about the program. -/
@[expose] def ProgramFactSet.empty : ProgramFactSet := emptyFactSet

/-- Every fact. The honest `preserves` for a phase that returns the program it
    was given, and the only place a fact set may follow `ProgramFact.all` instead
    of being written out: a phase that changes nothing preserves a new fact the
    moment the fact exists, so there is nothing for a reviewer to re-check. -/
@[expose] def ProgramFactSet.all : ProgramFactSet := allFactSet

/-- Dynamic construction, for fact sets that only exist at runtime. Prefer
    `factSet![…]` when the facts are written out, since that costs nothing at
    runtime. -/
@[expose] def ProgramFactSet.ofList (l : List ProgramFact) : ProgramFactSet :=
  factSetOfList l

/-- `ProgramFactSet.holds σ p` holds when every fact in `σ` holds on `p`. Reads
    the facts through the algebra's accessor rather than the default
    representation's field, so it says nothing about how a set is stored. -/
@[expose, reducible] def ProgramFactSet.holds (σ : ProgramFactSet) (p : Program) : Prop :=
  ∀ f ∈ factsOf σ, f.holds p

end -- public section

end Core
