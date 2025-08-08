/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Util.Counter

/-! ## String Generator
  This file contains a string generator `StringGenState.gen`, where the
  uniqueness of the generated strings is designed to be provable. It relies on a
  `CounterState` to generate unique natural numbers (See `Counter.lean`).

  Also see `LabelGen.lean` for the generic type class for a unique label generator.
-/

/-- `s.IsSuffix t` checks if the string `s` is a suffix of the string `t`.
from mathlib https://github.com/leanprover-community/mathlib4/blob/f3c56c29d5c787d62f66c207e097a159ff66318a/Mathlib/Data/String/Defs.lean#L37-L39
-/
def String.IsSuffix : String → String → Prop
  | ⟨d1⟩, ⟨d2⟩ => List.IsSuffix d1 d2

/-- Wrapper around CounterState to allow a prefix -/
structure StringGenState where
  cs : Counter.CounterState
  generated : List (Nat × String)

instance : HasSubset StringGenState where
  Subset σ₁ σ₂ := σ₁.generated.unzip.2.Subset σ₂.generated.unzip.2

@[simp]
def StringGenState.emp : StringGenState := { cs := .emp, generated := [] }

/--
  The unique string generator. Generated strings consist of a prefix `pf`,
  followed by an underscore (`_`), followed by a unique number given by its
  underlying counter `σ.cs`.
 -/
def StringGenState.gen (pf : String) (σ : StringGenState) : String × StringGenState :=
  let (counter, cs) := Counter.genCounter σ.cs
  let newString : String := (pf ++ "_" ++ toString counter)
  let newState : StringGenState := { cs, generated := (counter, newString) :: σ.generated }
  (newString, newState)

def StringGenState.WF (σ : StringGenState)
  := Counter.WF σ.cs ∧
    σ.cs.generated = σ.generated.unzip.fst ∧
    σ.generated.unzip.snd.Nodup ∧
    ∀ c s, (c,s) ∈ σ.generated →
      String.IsSuffix ("_" ++ toString c) s

theorem String.append_eq_suffix (as bs bs' : String):
  (as ++ bs = as ++ bs') → bs = bs' := by
  intros Heq
  by_cases bs = bs' <;> simp_all
  next Hne =>
  have Heq' := String.ext_iff.mp Heq
  have Hne' : ¬ bs.data = bs'.data := by
    intros Heq
    have HH := String.ext_iff.mpr Heq
    contradiction
  simp [String.data_append] at *
  contradiction

theorem String.append_eq_prefix (as as' bs : String):
  (as ++ bs = as' ++ bs) → as = as' := by
  intros Heq
  by_cases as = as' <;> simp_all
  next Hne =>
  have Heq' := String.ext_iff.mp Heq
  have Hne' : ¬ as.data = as'.data := by
    intros Heq
    have HH := String.ext_iff.mpr Heq
    contradiction
  simp [String.data_append] at *
  contradiction

theorem List.reverse_injective :
  List.reverse l₁ = List.reverse l₂ → l₁ = l₂ := List.reverse_inj.mp

theorem String.data_wrap : pf = { data:= pf : String}.data := rfl
theorem String.data_wrap_eq (a b : String) : a.data = b.data → a = b := String.ext

theorem StringGenState.contains :
  StringGenState.gen pf σ = (s, σ') →
  s ∈ σ'.generated.unzip.2 := by
  intros Hgen
  simp [gen] at Hgen
  simp [← Hgen]

theorem StringGenState.subset : gen pf σ = (n, σ') → σ ⊆ σ' := by
  intros Hgen
  simp [gen] at Hgen
  simp [← Hgen, HasSubset.Subset]
  intros a Hin
  simp_all

/--
  (Incomplete) proof that the string generator produces unique strings.

  The main argument for the uniqueness of the generated string is that, if the
  unique numbers at the end of all strings are unique, then the strings
  themselves must be unique as well.  Some injectivity theorems about
  `Nat.toString` might be needed to prove the admitted cases in this theorem.
-/
theorem StringGenState.WFMono :
  WF σ →
  gen pf σ = (n, σ') →
  WF σ' := by
  intros Hwf Hgen
  simp [gen] at Hgen
  cases Hgen with
  | intro Hl Hr =>
  simp [← Hr]
  simp [Hl, WF] at *
  cases Hwf with
  | intro Hwfctr Hwf =>
  cases Hwf with
  | intro Hwf1 Hwf =>
  cases Hwf with
  | intro Hwfnd Hwf12 =>
  refine ⟨?_, ?_, ?_, ?_⟩
  . exact Counter.genCounterWFMono Hwfctr rfl
  . exact
    Eq.symm
      (List.reverse_injective
        (congrArg List.reverse
          (congrArg (List.cons (Counter.genCounter σ.cs).fst) (id (Eq.symm Hwf1)))))
  . refine ⟨?_, Hwfnd⟩
    intros x Hin
    specialize Hwf12 _ _ Hin
    /- `x` is the generated counter, given the counter `x` is fresh, we need to
    show that it's impossible for "_x" to be a suffix of the generated name `n` -/
    sorry
  . intros c s Heq
    simp [String.IsSuffix]
    cases Heq with
    | inl HH =>
      /- the newly generated counter `c` and name `s` satisfy the relationship
      that the the "_c" is a suffix of `s` -/
      sorry
    | inr HH =>
      exact Hwf12 _ _ HH
