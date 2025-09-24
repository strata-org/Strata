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

theorem StringGenState.gen_nonEmpty: gen pf σ = (n, σ') → σ'.generated ≠ [] := by
  simp [gen]
  intro _ Hgen
  simp [← Hgen]

theorem StringGenState.genCounter_of_StringGenStategen
  (Hgen: gen pf σ = (n, σ')): Counter.genCounter σ.cs = ((σ'.generated.head $ gen_nonEmpty Hgen).fst, σ'.cs) := by
  simp [gen] at Hgen
  simp [← Hgen.right]

theorem Nat_digitchar_neq_underscore {x: Nat}: ¬ '_' =  Nat.digitChar x := by
  unfold Nat.digitChar
  repeat (cases x; simp; rename_i x; simp [*])

theorem Nat_toDigitsCore_not_contain_underscore: ¬'_' ∈ l → ¬'_' ∈ (Nat.toDigitsCore 10 n m l).asString.data := by
  intro Hnin
  induction n using Nat.strongRecOn generalizing m l
  rename_i n ind
  cases n
  simp [Nat.toDigitsCore, List.asString, Hnin]
  rename_i n
  simp [Nat.toDigitsCore, List.asString]
  split
  simp [Nat_digitchar_neq_underscore, Hnin]
  apply ind <;> simp [*, Nat_digitchar_neq_underscore]

theorem Nat_toString_not_contain_underscore {x: Nat} : ¬ '_' ∈ (toString x).data := by
  simp [toString, Nat.repr, Nat.toDigits]
  exact Nat_toDigitsCore_not_contain_underscore (by simp)

theorem Nat_digitChar_index: x.digitChar =
    #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f','*'][min x 16]'(by simp; omega) := by
  simp
  unfold Nat.digitChar
  repeat (cases x; simp; rename_i x)
  any_goals simp

theorem neq_elem_of_neq_index_of_nodup (H: List.Nodup a) (Hl1: x < a.length) (Hl2: y < a.length) (Hneq: ¬ x = y): ¬ a[x]'Hl1 = a[y]'Hl2 := by
  unfold List.Nodup at H
  induction a generalizing x y
  simp at Hl1
  rename_i h t ind
  simp at H
  cases x; cases y
  contradiction
  simp
  apply H.left _ (by simp)
  cases y <;> simp
  rename_i y
  simp [Eq.comm, H.left (t[y]'(by simp at Hl1; omega)) (by simp)]
  rename_i x y
  simp_all

theorem Nat_eq_of_digitChar_eq {n m: Nat}: n < 16 → m < 16 → n.digitChar = m.digitChar → n = m := by
  intro H1 H2
  simp [Nat_digitChar_index]
  have: min n 16 = n := by omega
  simp [this]
  have: min m 16 = m := by omega
  simp [this]
  intro H
  false_or_by_contra
  have : ¬ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f', '*'][n]'(by simp; omega) =
    ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f', '*'][m]'(by simp; omega) :=by
    apply neq_elem_of_neq_index_of_nodup (by simp) (by simp; omega) (by simp; omega) (by assumption)
  contradiction

theorem Nat_toDigitsCore_list_suffix : l <:+ Nat.toDigitsCore 10 x n l := by
  induction x generalizing n l <;> simp [Nat.toDigitsCore]
  split
  simp
  rename_i ind _
  have ind:= @ind ((n % 10).digitChar :: l) (n/10)
  simp [List.IsSuffix] at *
  obtain ⟨t, ind⟩ := ind
  exists t ++ [(n % 10).digitChar]
  simp [← ind]

theorem Nat_toDigitsCore_list_len_le: (Nat.toDigitsCore 10 x n l).length ≥ l.length := by
  have H : l <:+ Nat.toDigitsCore 10 x n l := Nat_toDigitsCore_list_suffix
  simp [List.IsSuffix] at H
  obtain ⟨t, H⟩ := H
  simp [← H]

theorem Nat_toDigitsCore_list_len_lt {n:Nat}: x > 0 → n > 0 →  (Nat.toDigitsCore 10 x n l).length > l.length := by
  intros
  cases x; contradiction
  rename_i x _
  simp [Nat.toDigitsCore]
  split
  simp
  have : (Nat.toDigitsCore 10 x (n / 10) ((n % 10).digitChar :: l)).length ≥ ((n % 10).digitChar :: l).length := Nat_toDigitsCore_list_len_le
  simp at this
  omega

theorem Nat_toDigitsCore_list_head_eq : Nat.toDigitsCore 10 x n (h1::t) = Nat.toDigitsCore 10 y m (h2::t) → h1 = h2 := by
  intro H
  unfold Nat.toDigitsCore at H
  split at H <;> (simp at H; split at H)
  any_goals split at H
  any_goals simp at H
  any_goals split at H
  assumption
  rename_i m _ _ _ x _
  have Hsuf : ((m % 10).digitChar :: h2 :: t) <:+ Nat.toDigitsCore 10 x (m / 10) ((m % 10).digitChar :: h2 :: t) := Nat_toDigitsCore_list_suffix
  simp [← H, List.suffix_iff_eq_drop] at Hsuf
  simp at H
  simp [H]
  rename_i n _ _ _ x _
  have Hsuf : ((n % 10).digitChar :: h2 :: t) <:+ Nat.toDigitsCore 10 x (n / 10) ((n % 10).digitChar :: h2 :: t) := Nat_toDigitsCore_list_suffix
  simp [← H, List.suffix_iff_eq_drop] at Hsuf
  simp [Hsuf]
  rename_i n _ _ _ x _ _ _ _ _
  have: (Nat.toDigitsCore 10 x (n / 10) ((n % 10).digitChar :: h1 :: t)).length ≥  ((n % 10).digitChar :: h1 :: t).length := Nat_toDigitsCore_list_len_le
  simp [H] at this
  omega
  rename_i n _ _ _ x _ _ _ _ _ _ _
  have Hsuf : ((n % 10).digitChar :: h1 :: t) <:+ Nat.toDigitsCore 10 x (n / 10) ((n % 10).digitChar :: h1 :: t) := Nat_toDigitsCore_list_suffix
  simp [H, List.suffix_iff_eq_drop] at Hsuf
  simp [Hsuf]
  rename_i n _ _ _ x _ m _ _ _ y _
  have Hsuf : ((m % 10).digitChar :: h2 :: t) <:+ Nat.toDigitsCore 10 y (m / 10) ((m % 10).digitChar :: h2 :: t) := Nat_toDigitsCore_list_suffix
  have Hsuf' : ((n % 10).digitChar :: h1 :: t) <:+ Nat.toDigitsCore 10 x (n / 10) ((n % 10).digitChar :: h1 :: t) := Nat_toDigitsCore_list_suffix
  simp [H, List.suffix_iff_eq_drop] at *
  simp [← Hsuf'] at Hsuf
  simp [Hsuf]

theorem Nat_eq_of_toDigitsCore_eq : x > n → y > m
  → Nat.toDigitsCore 10 x n l = Nat.toDigitsCore 10 y m l → n = m := by
  induction x using Nat.strongRecOn generalizing y n m l
  rename_i x ind
  intro Hn1 Hn2
  cases x <;> cases y
  any_goals omega
  rename_i x y
  simp [Nat.toDigitsCore]
  split
  split <;> intro H
  simp at H
  have := Nat_eq_of_digitChar_eq (by omega) (by omega) H
  omega
  have: (Nat.toDigitsCore 10 y (m / 10) ((m % 10).digitChar :: l)).length > ((m % 10).digitChar :: l).length := by
    apply Nat_toDigitsCore_list_len_lt (by omega) (by omega)
  simp [← H] at this
  split <;> intro H
  have: (Nat.toDigitsCore 10 x (n / 10) ((n % 10).digitChar :: l)).length > ((n % 10).digitChar :: l).length := by
    apply Nat_toDigitsCore_list_len_lt (by omega) (by omega)
  simp [H] at this
  have H':= Nat_eq_of_digitChar_eq (by omega) (by omega) $ Nat_toDigitsCore_list_head_eq H
  rw [H'] at H
  have ind:= ind _ (by simp) (by omega) (by omega) H
  omega

theorem Nat_eq_of_toString_eq {x y: Nat}: (toString x) = (toString y) → x = y := by
  intro H
  simp [toString, Nat.repr, Nat.toDigits, List.asString] at H
  apply Nat_eq_of_toDigitsCore_eq (by simp) (by simp) H

theorem Nat_eq_of_StringGen_suffix {x y: Nat}: ("_" ++ toString x).IsSuffix (s ++ "_" ++ toString y) → x = y := by
  intro Hsuf
  apply Nat_eq_of_toString_eq
  simp only [String.IsSuffix] at Hsuf
  by_cases Hc: (toString x).length < (toString y).length
  have Hsuf':  (toString y).data  <:+ ((s ++ "_").append (toString y)).data := by
    simp only [String.append, List.append_assoc, List.cons_append, List.nil_append, toString]
    apply List.suffix_append_of_suffix
    simp
  have : ("_".append (toString x)).data <:+ (toString y).data := by
    apply List.suffix_of_suffix_length_le Hsuf Hsuf'
    simp [String.append, String.length, toString] at *
    omega
  have : ¬ ("_".append (toString x)).data <:+ (toString y).data := by
    intro h;
    simp [String.append, List.IsSuffix] at h
    obtain ⟨t, h⟩ := h
    have : '_' ∈ (toString y).data := by simp [← h]
    have := @Nat_toString_not_contain_underscore y
    contradiction
  contradiction
  --case 2
  by_cases Hc: (toString x).length > (toString y).length
  have Hsuf : (toString x).data <:+ ((s ++ "_").append (toString y)).data := by
    simp [String.append, toString, List.IsSuffix] at *
    obtain ⟨t, H⟩ := Hsuf
    exists t ++ ['_']
    simp [← H]
  have Hsuf':  ("_".append (toString y)).data  <:+ ((s ++ "_").append (toString y)).data := by
    simp only [String.append, List.append_assoc, List.cons_append, List.nil_append]
    apply List.suffix_append_of_suffix
    simp
  have H: ("_".append (toString y)).data <:+ (toString x).data := by
    apply List.suffix_of_suffix_length_le Hsuf' Hsuf
    simp [String.append, String.length, toString] at *
    omega
  have : ¬ ("_".append (toString y)).data <:+ (toString x).data := by
    intro h;
    simp [String.append, List.IsSuffix] at h
    obtain ⟨t, h⟩ := h
    have : '_' ∈ (toString x).data := by simp [← h]
    have := @Nat_toString_not_contain_underscore x
    contradiction
  contradiction
  -- case 3
  have Hc: (toString x).data.length = (toString y).data.length := by simp [String.length, toString] at *; omega
  have Hsuf : (toString x).data <:+ ((s ++ "_").append (toString y)).data := by
    simp [String.append, toString, List.IsSuffix] at *
    obtain ⟨t, H⟩ := Hsuf
    exists t ++ ['_']
    simp [← H]
  have Hsuf':  (toString y).data  <:+ ((s ++ "_").append (toString y)).data := by
    simp only [String.append, List.append_assoc, List.cons_append, List.nil_append, toString]
    apply List.suffix_append_of_suffix
    simp
  simp [List.suffix_iff_eq_drop, Hc] at *
  rw [← Hsuf] at Hsuf'
  simp [String.ext_iff, Hsuf']

theorem StringGenState.WFMono :
  WF σ →
  gen pf σ = (n, σ') →
  WF σ' := by
  intros Hwf Hgen
  simp [WF] at *
  constructor
  exact Counter.genCounterWFMono Hwf.left $ StringGenState.genCounter_of_StringGenStategen Hgen
  simp [gen] at Hgen
  simp [← Hgen.right, Counter.genCounter, ←Hwf.right.left, Hwf.right.right.left]
  constructor
  intro x Hx
  have Hx := Nat_eq_of_StringGen_suffix $ Hwf.right.right.right x _ Hx
  have : x ∈ List.map Prod.fst σ.generated  := by refine List.mem_map.mpr ?_; exists (x, pf ++ "_" ++ toString σ.cs.counter)
  rw [← Hwf.right.left, Hx] at this
  have Hcontra:= Hwf.left.left _ this
  simp at Hcontra
  intro c s H
  cases H
  rename_i H
  simp [H.right, H.left, String.IsSuffix, String.append]
  apply List.suffix_append
  apply Hwf.right.right.right <;> assumption
