/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Util.Counter
import Strata.DL.Util.StringGen
namespace LabelGen

/-! ## Well-Formed Label Generator -/

/--
  A well-formed label generator of type `α`, guaranteeing that all generated
  labels are unique.  The generator `gen` takes a prefix of type `α`, and a
  state of type `State`, returning a pair consisting of the generated identifier
  of type and a new state (`α × State`).

  It takes a generator-specific well-formedness property `wf` on the state. The
  generator requires that

1. well-formedness is preserved across label generation,
2. the newly generated label is a member of the new state, and
3. the new state is a superset of the old state.
  -/
class WFLabelGen (α : Type) (State : Type) [HasSubset State] [DecidableEq α] where
  /-- an empty state -/
  emp : State
  /-- a generator function -/
  gen : α → State → (α × State)
  /-- all labels generated so far -/
  generated : State → List α
  wf : State → Prop
  wf_emp : wf emp
  wf_gen : ∀ (γ γ': State) (pf l: α),
    gen pf γ = (l, γ') →
    wf γ →
    wf γ' ∧ l ∈ generated γ' ∧ γ ⊆ γ'

/-- CounterState has a unique generator -/
instance : WFLabelGen Nat Counter.CounterState where
  emp := Counter.CounterState.emp
  gen := λ _ ↦ Counter.genCounter -- discards the prefix
  generated := Counter.CounterState.generated
  wf := Counter.WF
  wf_emp := by
    constructor ; simp [Counter.CounterState.emp] ; simp
  wf_gen := fun γ γ' _ l Hgen Hwf =>
    ⟨Counter.genCounterWFMono Hwf Hgen,
    Counter.genCounterContains Hgen,
    Counter.genCounterSubset Hgen⟩


/-- StringGen has a unique generator -/
instance : WFLabelGen String StringGenState where
  emp := .emp
  gen := StringGenState.gen
  generated := Prod.snd ∘ List.unzip ∘ StringGenState.generated
  wf := StringGenState.WF
  wf_emp := by
    simp [StringGenState.WF, Counter.WF]
  wf_gen := by
    intros γ γ' pf l Hgen Hwf
    refine ⟨?_, ?_, ?_⟩
    . exact StringGenState.WFMono Hwf Hgen
    . exact StringGenState.contains Hgen
    . exact StringGenState.subset Hgen

abbrev StringGenM := StateM StringGenState

end LabelGen
