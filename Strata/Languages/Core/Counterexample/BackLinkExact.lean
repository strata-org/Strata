/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkSimProps
public import Strata.Languages.Core.Counterexample.BackLinkChainReplayProps
import all Strata.DL.Imperative.Counterexample.Run
import all Strata.DL.Imperative.Counterexample.BackLink
import Strata.DL.Imperative.Counterexample.RunProps
import Strata.DL.Imperative.Counterexample.BackLinkProps

/-! # Replay-free back-links for exact phases: Core certificates

An *exact* phase loses no behaviour: its back-link translates the incoming outcome with no
replay (`Imperative.exactBackLink`), valid by one proof (`Imperative.exactBackLink_preserves`)
from a per-phase simulation certificate (`Imperative.ExactCert`).  This module instantiates
the certificate for Core (`ExactCert`: slice starts well-formed by `CfgWF`) and gives three
certificates any phase can use when the downstream replays are simulated by the upstream
ones (`IsReplaySimulation π' π`):

* `ExactCert.ofReplaySimulation` — for a phase that leaves every unit unchanged: all
  four maps are identities.
* `ExactCert.ofSubTable` — its instance for a phase that leaves every unit unchanged and
  keeps or filters the procedure table (the downstream table is a sub-table of the upstream
  one).
* `ExactCert.ofUnchangedUnit` — for any forward map: a slice start is kept as it is
  when this is consistent with the input unit (`unchangedBackCfg`), so the certificate
  translates the chains of a unit the phase left unchanged.

The Core instantiation of the target is `Tgt := AssertId Expression` and of the validity
`V := genuineFeasible π` (`exactBackLink_backLinkPreserves` in `BackLinkExactProps`). -/

namespace Core

open Imperative

public section

/-- The simulation certificate of an exact Core phase (`Imperative.ExactCert`), with slice
    starts well-formed by `CfgWF`. -/
abbrev ExactCert (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command)))
    {Tgt : Type} (V' V : CexValidity Tgt) :=
  Imperative.ExactCert CfgWF T V' V

/-- **Identity certificate from a replay simulation.**  For a phase that leaves every
    unit unchanged and whose downstream replays are simulated by the upstream ones
    (`IsReplaySimulation π' π`), all four maps are identities. -/
@[expose] def ExactCert.ofReplaySimulation {π' π : String → Option Procedure}
    (hsim : IsReplaySimulation π' π) :
    ExactCert (fun st => some st) (fun t f c => genuineFeasible π' t f c)
      (fun t f c => genuineFeasible π t f c) where
  backCfg := fun _ _ c => some c
  backOracle := fun _ _ o => o
  backTarget := id
  backFuel := fun _ => id
  top_back := fun _ _ hT _ _ htop hc _ => by cases hT; cases hc; exact htop
  nontop_back := fun _ _ hT _ _ htop hc _ => by cases hT; cases hc; exact htop
  wf_back := fun _ _ _ _ _ _ hw hc => by cases hc; exact hw
  claim_back := fun _ _ _ t f _ c' _ _ hg hc => by
    cases hc
    exact claim_back_of_simulation hsim t (Nat.le_refl f) c' hg

/-- **Identity certificate for a phase that keeps or filters the procedure table.**  For a
    phase that leaves every unit unchanged and whose downstream procedure table `π'` is a
    sub-table of the upstream table `π` (every procedure `π'` resolves, `π` resolves to the same
    procedure), all four maps are identities. -/
@[expose] def ExactCert.ofSubTable {π' π : String → Option Procedure}
    (hsub : ∀ n p, π' n = some p → π n = some p) :
    ExactCert (fun st => some st) (genuineFeasible π') (genuineFeasible π) :=
  ExactCert.ofReplaySimulation (isReplaySimulation_of_sub hsub)

/-- The configuration map of the unchanged-unit certificate: the chain's head maps to
    itself when it starts at the top of the input unit (the phase left the unit
    unchanged), a later slice start maps to itself unless it starts at the top of the
    input unit. -/
@[expose] def unchangedBackCfg (st : List Statement) (head : Bool)
    (c : IConfig Expression Command) : Option (IConfig Expression Command) :=
  if head then (if isTopLevelAtB st c then some c else none)
  else (if isTopLevelAtB st c then none else some c)

/-- A configuration `c'` that `unchangedBackCfg st head` maps to `c` is `c` itself, and the
    check `isTopLevelAtB st c'` (whether `c'` starts at the top of `st`) returns `head`. -/
theorem unchangedBackCfg_eq_some {st : List Statement} {head : Bool}
    {c' c : IConfig Expression Command} (h : unchangedBackCfg st head c' = some c) :
    c' = c ∧ isTopLevelAtB st c' = head := by
  cases head <;> cases hb : isTopLevelAtB st c' <;> simp_all [unchangedBackCfg]

/-- **The unchanged-unit certificate**, for any forward map `T`: a slice start is kept
    as it is when this is consistent with the input unit `st` (the head at its top, a
    later slice not).  A downstream claim replays upstream on the same configuration
    because the downstream table is a sub-table of the upstream one
    (`IsReplaySimulation`).  It translates exactly the chains of a unit the phase left
    unchanged; for a changed unit the head has no counterpart. -/
@[expose] def ExactCert.ofUnchangedUnit {π' π : String → Option Procedure}
    (hsim : IsReplaySimulation π' π) (T : List Statement → Option (List Statement)) :
    ExactCert T (fun t f c => genuineFeasible π' t f c) (fun t f c => genuineFeasible π t f c) where
  backCfg := unchangedBackCfg
  backOracle := fun _ _ o => o
  backTarget := id
  backFuel := fun _ => id
  top_back := fun _ _ _ c' _ _ hc oracle => by
    obtain ⟨rfl, htop⟩ := unchangedBackCfg_eq_some hc
    exact isTopLevelAt_of_isTopLevelAtB (cex := ⟨c'.cfg, oracle⟩) htop
  nontop_back := fun _ _ _ c' _ _ hc oracle => by
    obtain ⟨rfl, hnt⟩ := unchangedBackCfg_eq_some hc
    exact not_isTopLevelAt_of_isTopLevelAtB_false (cex := ⟨c'.cfg, oracle⟩) hnt
  wf_back := fun _ _ _ _ _ _ hw hc => (unchangedBackCfg_eq_some hc).1 ▸ hw
  claim_back := fun _ _ _ t f _ c' _ _ hg hc => by
    obtain ⟨rfl, -⟩ := unchangedBackCfg_eq_some hc
    exact claim_back_of_simulation hsim t (Nat.le_refl f) c' hg

end -- public section

end Core
