/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.WF
import all Strata.Languages.Core.CallWF

/-! # Properties of well-formed calls

`callArgsError?_eq_none_iff`: `callArgsError?` accepts exactly the arguments that
match the procedure's signature with distinct result variables.
`callError?_eq_none_iff`: `callError?` accepts exactly the calls that satisfy
`WF.WFcallProp`. `illFormedCalls_eq_nil_iff`: `illFormedCalls` finds nothing exactly
when every call of the program is well-formed (`Program.callsWellFormed`).
-/

namespace Core

open Imperative

public section

/-- Every call in `p` is well-formed. -/
@[expose] def Program.callsWellFormed (p : Program) : Prop :=
  ∀ c ∈ p.callSites, WF.WFcallProp p c.procName c.args

/-! ## Agreement with `WF.WFcallProp` -/

/-- `aliasedResultsMessage?` finds nothing exactly when the result variables are
    distinct. -/
private theorem aliasedResultsMessage?_eq_none_iff (procName : String)
    (args : List (CallArg Expression)) :
    aliasedResultsMessage? procName args = none ↔ (CallArg.getLhs args).Nodup := by
  simp only [aliasedResultsMessage?, Option.map_eq_none_iff, List.find?_eq_none,
    decide_eq_true_eq, Nat.not_lt]
  rw [List.nodup_iff_count]
  constructor
  · intro h a
    by_cases ha : a ∈ CallArg.getLhs args
    · simpa [List.count_eq_length_filter] using h a ha
    · simp [List.count_eq_zero_of_not_mem ha]
  · intro h x _
    simpa [List.count_eq_length_filter] using h x

/-- `inputMismatchMessage?` finds nothing exactly when every input argument matches
    its formal. -/
private theorem inputMismatchMessage?_eq_none_iff (procName : String) (proc : Procedure)
    (args : List (CallArg Expression)) :
    inputMismatchMessage? procName proc args = none ↔
      ∀ xa ∈ proc.header.inputs.keys.zip (CallArg.inputArgs args),
        WF.inputArgMatches proc.header.outputs.keys (CallArg.getLhs args) xa.1 xa.2 = true := by
  simp [inputMismatchMessage?]

/-- `outputMismatchMessage?` finds nothing exactly when every result argument matches
    its formal. -/
private theorem outputMismatchMessage?_eq_none_iff (procName : String) (proc : Procedure)
    (args : List (CallArg Expression)) :
    outputMismatchMessage? procName proc args = none ↔
      ∀ zr ∈ proc.header.outputs.keys.zip (CallArg.resultArgs args),
        WF.outputArgMatches proc.header.inputs.keys zr.1 zr.2 = true := by
  simp [outputMismatchMessage?]

/-- `callArgsError?` finds nothing exactly when the arguments match the procedure's
    signature and the result variables are distinct. -/
theorem callArgsError?_eq_none_iff (procName : String) (proc : Procedure)
    (args : List (CallArg Expression)) :
    callArgsError? procName proc args = none ↔
      WF.ArgsMatchSignature proc args ∧ (CallArg.getLhs args).Nodup := by
  simp only [callArgsError?]
  by_cases h1 : (CallArg.getInputExprs args).length = proc.header.inputs.length
  · by_cases h2 : (CallArg.getLhs args).length = proc.header.outputs.length
    · simp only [h1, h2, ne_eq, not_true_eq_false, ↓reduceIte]
      rw [← aliasedResultsMessage?_eq_none_iff procName args]
      have hin := inputMismatchMessage?_eq_none_iff procName proc args
      have hout := outputMismatchMessage?_eq_none_iff procName proc args
      constructor
      · intro h
        split at h
        · simp at h
        · rename_i hi
          split at h
          · simp at h
          · rename_i ho
            exact ⟨⟨h1, h2, hin.mp hi, hout.mp ho⟩, h⟩
      · intro ⟨hm, hn⟩
        rw [hin.mpr hm.inputsMatch, hout.mpr hm.outputsMatch]
        exact hn
    · simp only [h1, h2, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte,
        reduceCtorEq, false_iff]
      exact fun h => h2 h.1.resultCount
  · simp only [h1, ne_eq, not_false_eq_true, ↓reduceIte, reduceCtorEq, false_iff]
    exact fun h => h1 h.1.inputCount

/-- `callError?` accepts exactly the well-formed calls. -/
theorem callError?_eq_none_iff (p : Program) (procName : String)
    (args : List (CallArg Expression)) :
    callError? p procName args = none ↔ WF.WFcallProp p procName args := by
  unfold callError?
  split
  · rename_i hfind
    simp only [reduceCtorEq, false_iff]
    intro h
    simpa [hfind] using h.defined
  · rename_i proc hfind
    rw [callArgsError?_eq_none_iff]
    constructor
    · intro ⟨hm, hnodup⟩
      exact {
        defined := by simp [hfind]
        argsMatch := fun h => by rw [hfind] at h; cases h; exact hm
        lhsWF := hnodup
        wfargs := List.Forall_mem_iff.mpr fun _ _ => ⟨⟩ }
    · intro h
      exact ⟨h.argsMatch hfind, h.lhsWF⟩

/-- `illFormedCalls` finds nothing exactly when every call is well-formed. -/
@[simp] theorem illFormedCalls_eq_nil_iff (p : Program) :
    illFormedCalls p = [] ↔ p.callsWellFormed := by
  simp only [illFormedCalls, List.filterMap_eq_nil_iff, Option.map_eq_none_iff,
    Program.callsWellFormed]
  constructor
  · intro h c hc
    exact (callError?_eq_none_iff p c.procName c.args).mp (h c hc)
  · intro h c hc
    exact (callError?_eq_none_iff p c.procName c.args).mpr (h c hc)

end -- public section

end Core
