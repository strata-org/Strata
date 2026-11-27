/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkTargetLinks
public import Strata.Languages.Core.Counterexample.BackLinkTargetProps
import all Strata.DL.Imperative.Counterexample.Run
import all Strata.DL.Imperative.Counterexample.BackLink
import all Strata.Languages.Core.Counterexample.BackLinkExact
import all Strata.Languages.Core.Counterexample.BackLinkExactInsert
import all Strata.Languages.Core.Counterexample.BackLinkTarget
import all Strata.Languages.Core.Counterexample.BackLinkTargetLinks
import Strata.DL.Imperative.Counterexample.Tactics
import all Strata.Languages.Core.Counterexample.BackLinkExactProps

/-! # Properties of the exact back-links over targets

Validity facts for the back-links of `BackLinkTargetLinks`.  `BackLinkPreservesT π t
t' T link` says that whenever the forward map `T` maps the unit `st` to `st'`, `link`
lifts every outcome valid for the target `t` at `st'` to one valid for `t'` at `st`.
`ExactCert.liftChecked` translates an outcome with an exact certificate and keeps the
translated claim only when a decision procedure accepts it; `exactCheckedTargetLink` and
`exactTargetBackLink` are the exact back-links of a phase at a target.

Key theorems: `exactTargetBackLink_preserves`, `exactCheckedTargetLink_preserves`,
`exactCheckedTargetLink_preserves_of_nonempty`, `exactTransportTargetLink_preserves`,
`exactTransportTargetLink_preserves_of_nonempty`. -/

namespace Core

open Imperative

public section

/-! ## Checked translation through an exact certificate -/

namespace ExactCert

variable {T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
  {Tgt : Type} {V' V : CexValidity Tgt}

/-- **Validity of a checked translation.**  Let `check` decide the target `u` soundly for
    the claim-validity predicate `W`: every counterexample it accepts at a fuel satisfies
    `W u` there.  Whenever the certificate's forward map `T` maps the unit `st` to `st'`,
    the checked translation (`liftChecked`) lifts every outcome valid at `st'` for some
    target `t` (`ValidOutcomeOf V'`) to one valid for `u` at `st` (`ValidOutcomeOf W`). -/
private theorem liftChecked_valid (cert : ExactCert T V' V) (fuel : Nat → Nat)
    (check : Nat → CexA Expression Command → Bool) {Tgt' : Type} (W : CexValidity Tgt')
    (u : Tgt') (hcheck : ∀ f c, check f c = true → W u f c) :
    ∀ st st', T st = some st' → ∀ (t : Tgt) (o : BackLinkOutcome Expression Command),
      ValidOutcomeOf V' t st' o → ValidOutcomeOf W u st (cert.liftChecked fuel check st o) := by
  rintro st st' hT t o ⟨hhead, hclaim, hwf⟩
  have hlift : ValidOutcomeOf (fun _ _ _ => True) () st (cert.liftOutcome st o) :=
    exactBackLink_preserves "" cert.forget st st' hT () o
      ⟨hhead, fun c f h => ⟨trivial, (hclaim c f h).2⟩, hwf⟩
  grind [liftChecked, ValidOutcomeOf, BackLinkOutcome.chain, BackLinkOutcome.empty]

end ExactCert

/-! ## Validity of the exact back-links -/

/-- Guarding a back-link to return the empty outcome at an empty unit (`guardEmptyUnit`)
    keeps validity preservation from `t` to `t'` along `T` (`BackLinkPreservesT`: whenever
    `T` maps `st` to `st'`, an outcome valid for `t` at `st'` lifts to one valid for `t'`
    at `st`). -/
private theorem guardEmptyUnitT_preserves {π : String → Option Procedure} {t t' : Target}
    {T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
    {link : BackLink Expression Command Command} (h : BackLinkPreservesT π t t' T link) :
    BackLinkPreservesT π t t' T link.guardEmptyUnit := fun _ _ => by
  simp only [BackLink.guardEmptyUnit]
  split <;> solve_by_elim [validOutcomeT_empty]

/-- If `primary` and `fallback` both preserve validity from `t` to `t'` along `T`
    (`BackLinkPreservesT`), so does `primary.preferClaim fallback` (the outcome of
    `fallback` where `primary` claims nothing and `fallback` claims). -/
private theorem preferClaimT_preserves {π : String → Option Procedure} {t t' : Target}
    {T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
    {primary fallback : BackLink Expression Command Command}
    (hp : BackLinkPreservesT π t t' T primary) (hf : BackLinkPreservesT π t t' T fallback) :
    BackLinkPreservesT π t t' T (primary.preferClaim fallback) := fun _ _ _ _ => by
  simp only [BackLink.preferClaim]
  split <;> (try split) <;> solve_by_elim

/-- If `primary` and `fallback` both preserve validity from `t` to `t'` along `T`
    (`BackLinkPreservesT`), so does `primary.orElseIfEmpty fallback` (the outcome of
    `fallback` where `primary` translates nothing of a non-empty chain). -/
private theorem orElseIfEmptyT_preserves {π : String → Option Procedure} {t t' : Target}
    {T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
    {primary fallback : BackLink Expression Command Command}
    (hp : BackLinkPreservesT π t t' T primary) (hf : BackLinkPreservesT π t t' T fallback) :
    BackLinkPreservesT π t t' T (primary.orElseIfEmpty fallback) := fun _ _ _ _ => by
  simp only [BackLink.orElseIfEmpty]
  split <;> solve_by_elim

/-- Let `check` decide the target `t'` soundly: every counterexample it accepts at a fuel
    is a valid claim for `t'` there (`genuineFeasibleT`).  Then the checked back-link of
    an exact certificate, at fuel `walkClaimFuel`, preserves validity from any target `t`
    to `t'` along the certificate's forward map `T` (`BackLinkPreservesT`: whenever `T`
    maps `st` to `st'`, an outcome valid for `t` at `st'` lifts to one valid for `t'` at
    `st`). -/
private theorem checkedExactBackLink_preserves (π : String → Option Procedure)
    {T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
    {Tgt : Type} {V' V : CexValidity Tgt} (name : String) (cert : ExactCert T V' V)
    (check : Nat → CexA Expression Command → Bool) (t t' : Target)
    (hcheck : ∀ f c, check f c = true → genuineFeasibleT π t' f c) :
    BackLinkPreservesT π t t' T (checkedExactBackLink name cert walkClaimFuel
        check) := fun st st' hT o ⟨hhead, hclaim, hwf⟩ =>
  ExactCert.liftChecked_valid cert.forget walkClaimFuel _ (genuineFeasibleT π) _ hcheck st st'
    hT () o ⟨hhead, fun c f h => ⟨trivial, (hclaim c f h).2⟩, hwf⟩

/-- Let `check` decide the target `t'` soundly (every counterexample it accepts is a valid
    claim for `t'`, `genuineFeasibleT`) and let `fallback` preserve validity from `t` to
    `t'` along the certificate's forward map `T`.  Then the walk-decided back-link
    `exactCheckedBackLink` preserves validity from `t` to `t'` along `T`
    (`BackLinkPreservesT`). -/
private theorem exactCheckedBackLink_preserves (π : String → Option Procedure)
    {T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
    {Tgt : Type} {V' V : CexValidity Tgt} (name : String) (cert : ExactCert T V' V)
    (check : Nat → CexA Expression Command → Bool)
    (fallback : BackLink Expression Command Command) (t t' : Target)
    (hcheck : ∀ f c, check f c = true → genuineFeasibleT π t' f c)
    (hfb : BackLinkPreservesT π t t' T fallback) :
    BackLinkPreservesT π t t' T (exactCheckedBackLink name cert check fallback) := by
  apply_rules [preferClaimT_preserves, orElseIfEmptyT_preserves, guardEmptyUnitT_preserves,
    checkedExactBackLink_preserves]

/-- Let `check` decide the target `t'` soundly (every counterexample it accepts is a valid
    claim for `t'`, `genuineFeasibleT`), let `fallback` preserve validity from `t` to `t'`
    along a forward map `T'`, and let `T'` relate only pairs that the certificate's forward
    map `T` relates too whenever the input unit is non-empty.  Then the walk-decided
    back-link `exactCheckedBackLink` preserves validity from `t` to `t'` along `T'`
    (`BackLinkPreservesT`). -/
private theorem exactCheckedBackLink_preserves_of_nonempty (π : String → Option Procedure)
    {T T' : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
    {Tgt : Type} {V' V : CexValidity Tgt} (name : String) (cert : ExactCert T V' V)
    (check : Nat → CexA Expression Command → Bool)
    (fallback : BackLink Expression Command Command) (t t' : Target)
    (hcheck : ∀ f c, check f c = true → genuineFeasibleT π t' f c)
    (hfb : BackLinkPreservesT π t t' T' fallback)
    (hT : ∀ st st', T' st = some st' → st ≠ [] → T st = some st') :
    BackLinkPreservesT π t t' T' (exactCheckedBackLink name cert check
        fallback) :=
  preferClaimT_preserves (orElseIfEmptyT_preserves (fun _ _ h _ ho => by
    simp only [BackLink.guardEmptyUnit, List.isEmpty_iff]
    split
    exact exactBackLink_preserves.validOutcome_empty_of
    apply_rules [checkedExactBackLink_preserves]) hfb) hfb

/-- For all targets `t` and `t'`, the exact back-link of a phase at `t'`
    (`exactCheckedTargetLink`) preserves validity from `t` to `t'` along the certificate's
    forward map `T` (`BackLinkPreservesT`: whenever `T` maps `st` to `st'`, an outcome
    valid for `t` at `st'` lifts to one valid for `t'` at `st`). -/
theorem exactCheckedTargetLink_preserves (π : String → Option Procedure)
    {T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
    {Tgt : Type} {V' V : CexValidity Tgt} (name : String) (cert : ExactCert T V' V)
    (t t' : Target) :
    BackLinkPreservesT π t t' T (exactCheckedTargetLink π name cert t') := by
  cases t' with
  | loopVC i =>
    exact exactCheckedBackLink_preserves _ _ _ _ _ _ _ (fun _ _ => id)
      (directLoopVCBackLink_preserves _ _ _ _ _)
  | atPoint i =>
    exact exactCheckedBackLink_preserves _ _ _ _ _ _ _ (fun _ _ => id)
      (directPointBackLink_preserves _ _ _ _ _)
  | _ => apply_rules [directTargetBackLink_preserves]

/-- Let the forward map `T'` relate only pairs that the certificate's forward map `T`
    relates too whenever the input unit is non-empty.  Then for all targets `t` and `t'`,
    the exact back-link of a phase at `t'` (`exactCheckedTargetLink`) preserves validity
    from `t` to `t'` along `T'` (`BackLinkPreservesT`). -/
theorem exactCheckedTargetLink_preserves_of_nonempty (π : String → Option Procedure)
    {T T' : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
    {Tgt : Type} {V' V : CexValidity Tgt} (name : String) (cert : ExactCert T V' V)
    (t t' : Target) (hT : ∀ st st', T' st = some st' → st ≠ [] → T st = some st') :
    BackLinkPreservesT π t t' T' (exactCheckedTargetLink π name cert t') := by
  cases t' with
  | loopVC i =>
    exact exactCheckedBackLink_preserves_of_nonempty _ _ _ _ _ _ _ (fun _ _ => id)
      (directLoopVCBackLink_preserves _ _ _ _ _) hT
  | atPoint i =>
    exact exactCheckedBackLink_preserves_of_nonempty _ _ _ _ _ _ _ (fun _ _ => id)
      (directPointBackLink_preserves _ _ _ _ _) hT
  | _ => apply_rules [directTargetBackLink_preserves]

/-- Let the replay-free certificate link `exactBackLink name cert` preserve validity for
    every assertion along the certificate's forward map `T` (`BackLinkPreserves`).  Then
    for every target `t`, the exact back-link of the phase at `t` (`exactTargetBackLink`)
    preserves validity for `t` along `T` (`BackLinkPreservesT`: whenever `T` maps `st` to
    `st'`, an outcome valid for `t` at `st'` lifts to one valid for `t` at `st`). -/
theorem exactTargetBackLink_preserves (π : String → Option Procedure)
    {T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
    (name : String) (cert : ExactCert T (genuineFeasible π) (genuineFeasible π))
    (hp : ∀ a, BackLinkPreserves π a T (exactBackLink name cert)) (t : Target) :
    BackLinkPreservesT π t t T (exactTargetBackLink π name cert t) := by
  cases t <;> solve_by_elim [orElseIfEmptyT_preserves, guardEmptyUnitT_preserves,
    backLinkPreservesT_assert, exactCheckedTargetLink_preserves]

/-- Let the certificate `certT` over targets keep the target (`backTarget = id`), and let the
    forward map `T'` relate only pairs that the certificate's forward map `T` relates too
    whenever the input unit is non-empty.  Then its replay-free back-link, guarded at an empty
    unit, preserves validity for every target `t` along `T'` (`BackLinkPreservesT`). -/
private theorem guardedTransport_preserves (π : String → Option Procedure)
    {T T' : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
    (name : String) (certT : ExactCert T (genuineFeasibleT π) (genuineFeasibleT π))
    (htgt : certT.backTarget = id) (t : Target)
    (hT : ∀ st st', T' st = some st' → st ≠ [] → T st = some st') :
    BackLinkPreservesT π t t T' (exactBackLink name certT).guardEmptyUnit :=
  fun st _ h o ho => by
    simp only [BackLink.guardEmptyUnit, List.isEmpty_iff]
    split
    · exact validOutcomeT_empty π t st
    · have hv := exactBackLink_preserves name certT _ _ (hT _ _ h ‹_›) t o ho
      rwa [htgt] at hv

/-- Let the replay-free certificate link `exactBackLink name cert` preserve validity for
    every assertion along `T` (`BackLinkPreserves`), let the certificate `certT` over targets
    keep the target (`backTarget = id`), and let the forward map `T'` relate only pairs that
    `T` relates too whenever the input unit is non-empty.  Then for every target `t`, the exact
    back-link `exactTransportTargetLink` preserves validity for `t` along `T'`
    (`BackLinkPreservesT`: whenever `T'` maps `st` to `st'`, an outcome valid for `t` at `st'`
    lifts to one valid for `t` at `st`). -/
theorem exactTransportTargetLink_preserves_of_nonempty (π : String → Option Procedure)
    {T T' : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
    (name : String) (cert : ExactCert T (genuineFeasible π) (genuineFeasible π))
    (certT : ExactCert T (genuineFeasibleT π) (genuineFeasibleT π))
    (hp : ∀ a, BackLinkPreserves π a T (exactBackLink name cert))
    (htgt : certT.backTarget = id)
    (hT : ∀ st st', T' st = some st' → st ≠ [] → T st = some st') (t : Target) :
    BackLinkPreservesT π t t T' (exactTransportTargetLink π name cert certT t) := by
  cases t with
  | assert a =>
    refine orElseIfEmptyT_preserves (fun st _ h o ho => ?_)
      (directTargetBackLink_preserves π name (.assert a) (.assert a) _)
    simp only [BackLink.guardEmptyUnit, List.isEmpty_iff]
    split
    · exact validOutcomeT_empty π _ st
    · exact hp a _ _ (hT _ _ h ‹_›) o ho
  | loopVC i =>
    exact preferClaimT_preserves (orElseIfEmptyT_preserves
      (guardedTransport_preserves π name certT htgt _ hT)
      (directLoopVCBackLink_preserves _ _ _ _ _)) (directLoopVCBackLink_preserves _ _ _ _ _)
  | atPoint i =>
    exact preferClaimT_preserves (orElseIfEmptyT_preserves
      (guardedTransport_preserves π name certT htgt _ hT) (directPointBackLink_preserves _ _ _ _ _))
      (directPointBackLink_preserves _ _ _ _ _)
  | declCheck i => exact directTargetBackLink_preserves _ _ _ _ _

/-- Let the replay-free certificate link `exactBackLink name cert` preserve validity for
    every assertion along `T` (`BackLinkPreserves`), and let the certificate `certT` over
    targets keep the target (`backTarget = id`).  Then for every target `t`, the exact
    back-link `exactTransportTargetLink` preserves validity for `t` along `T`
    (`BackLinkPreservesT`). -/
theorem exactTransportTargetLink_preserves (π : String → Option Procedure)
    {T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
    (name : String) (cert : ExactCert T (genuineFeasible π) (genuineFeasible π))
    (certT : ExactCert T (genuineFeasibleT π) (genuineFeasibleT π))
    (hp : ∀ a, BackLinkPreserves π a T (exactBackLink name cert))
    (htgt : certT.backTarget = id) (t : Target) :
    BackLinkPreservesT π t t T (exactTransportTargetLink π name cert certT t) :=
  exactTransportTargetLink_preserves_of_nonempty π name cert certT hp htgt (fun _ _ h _ => h) t

end -- public section

end Core
