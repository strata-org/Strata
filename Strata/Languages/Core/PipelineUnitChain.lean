/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.RuntimeCompositionProof
public import Strata.Languages.Core.Counterexample.BackLinkExact

/-! # Per-level units of the runtime pipeline, and the forward chain they form

`composeRuntimeBackLinks_sound` takes a forward chain (`ForwardChainT`) of the links'
targeted readings whose per-link input units are the units the runtime fold lifts at
(`runtimeUnits`).  Phases transform programs, not units, so this file builds that chain
from the units themselves: level `i`'s forward map is the graph `unitStep uᵢ uᵢ₊₁` of the
pair (its input unit, the next level's input unit — the final unit after the last
level).  Chaining then holds by construction (`levelChain`), and what remains per level is
the link's validity at that one pair (`LinkPreservesAt`, collected over the levels by
`LevelsOK`).

Key definitions: `Program.bodyOf`, `Program.unitBodyOf` (the body and the unit of a named
procedure), `unitStep`, `LinkPreservesAt`, `LevelsOK`, `levelChain`, and `PhaseRecord` (one
executed phase with its input and output programs) with `PhaseRecord.link` and
`PhaseRecord.Chained`. -/

namespace Core

open Imperative

public section

/-! ## Units of a program -/

/-- The structured body of the procedure named `n` in `p` (the first such procedure);
    `[]` when there is none or its body is a CFG. -/
@[expose] def Program.bodyOf (p : Program) (n : String) : List Statement :=
  (p.decls.findSome? (Decl.bodyNamed n)).getD []

/-- The unit of the procedure named `n` in `p` (the first such procedure): its
    contract-wrapped body (`Decl.unitNamed`); `[]` when there is none or its body is a
    CFG. -/
@[expose] def Program.unitBodyOf (p : Program) (n : String) : List Statement :=
  (p.decls.findSome? (Decl.unitNamed n)).getD []

/-! ## Per-level forward maps -/

/-- The forward map sending exactly the unit `a` to the unit `b`. -/
@[expose] def unitStep (a b : List Statement) : List Statement → Option (List Statement) :=
  fun st => if st = a then some b else none

/-- The forward map `unitStep a b` sends `a` to `b`. -/
theorem unitStep_self (a b : List Statement) : unitStep a b a = some b := by simp [unitStep]

/-- A runtime link is valid at the unit pair `(a, b)`: read as a targeted link at any
    procedure name, it preserves validity along the forward map `unitStep a b`. -/
@[expose] def LinkPreservesAt (π : String → Option Procedure) (link : RuntimeBackLink)
    (a b : List Statement) : Prop :=
  ∀ procName, TargetedBackLinkPreserves π (unitStep a b) (link.toTargeted π procName)

/-! ## The chain of levels -/

/-- Every level's link is valid at its unit pair: `units` are the links' input units in
    forward order, `last` the unit after the last level. -/
@[expose] def LevelsOK (π : String → Option Procedure) (last : List Statement) :
    List RuntimeBackLink → List (List Statement) → Prop
  | [], [] => True
  | l :: ls, u :: us => LinkPreservesAt π l u (us.headD last) ∧ LevelsOK π last ls us
  | _, _ => False

/-- The per-level forward maps: level `i` maps its unit to the next level's. -/
@[expose] def levelMaps (last : List Statement) :
    List (List Statement) → List (List Statement → Option (List Statement))
  | [] => []
  | u :: us => unitStep u (us.headD last) :: levelMaps last us

/-- The forward chain of the links' targeted readings (`runtimeTargeted` from `target` and
    `procName0`) through `units`. -/
@[expose] def levelChain (π : String → Option Procedure) (last : List Statement)
    (target : Target) (procName0 : Option String) :
    (links : List RuntimeBackLink) → (units : List (List Statement)) →
    LevelsOK π last links units →
    ForwardChainT π (runtimeTargeted π target procName0 links) (levelMaps last units)
      (units.headD last) last
  | [], [], _ => .nil last
  | l :: ls, u :: us, h =>
    .cons (l.toTargeted π (runtimeState target procName0 ls).2) (unitStep u (us.headD last))
      (runtimeTargeted π target procName0 ls) (levelMaps last us) u (us.headD last) last
      (h.1 _) (unitStep_self _ _) (levelChain π last target procName0 ls us h.2)
  | [], _ :: _, h => absurd h (by simp [LevelsOK])
  | _ :: _, [], h => absurd h (by simp [LevelsOK])

/-! ## Links recorded from a run of the phases -/

/-- One executed phase with the programs it was run on and produced. -/
structure PhaseRecord where
  phase : PipelinePhase
  input : Program
  output : Program

/-- The runtime carrier `runTransformsWithBackLinks` records for one executed phase. -/
@[expose] def PhaseRecord.link (r : PhaseRecord) : RuntimeBackLink :=
  (r.phase.buildBackLink r.input r.output).withPrograms r.input r.output

/-- Consecutive records chain: each phase ran on the previous phase's output. -/
@[expose] def PhaseRecord.Chained : List PhaseRecord → Prop
  | [] => True
  | [_] => True
  | r :: r' :: rs => r.output = r'.input ∧ PhaseRecord.Chained (r' :: rs)

end -- public section

end Core
