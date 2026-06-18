/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Util.Counter
import all Strata.DL.Util.Counter
import all Init.Data.Repr

public section

/-! ## String Generator
  This file contains a string generator `StringGenState.gen`, where the
  uniqueness of the generated strings is designed to be provable. It relies on a
  `CounterState` to generate unique natural numbers (See `Counter.lean`).

  Also see `LabelGen.lean` for the generic type class for a unique label generator.
-/

/-- `s.IsSuffix t` checks if the string `s` is a suffix of the string `t`.
Mirrors mathlib's `String.IsSuffix`. -/
abbrev String.IsSuffix (s1 s2 : String) : Prop := List.IsSuffix s1.toList s2.toList

local infixl:50 " <:+ " => String.IsSuffix

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
@[expose]
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

theorem Nat_toDigitsCore_not_contain_underscore {n m l} : '_' ∉ l → '_' ∉ Nat.toDigitsCore 10 n m l := by
  intro Hnin
  induction n using Nat.strongRecOn generalizing m l
  rename_i n ind
  cases n
  simp [Nat.toDigitsCore, Hnin]
  rename_i n
  simp [Nat.toDigitsCore]
  split
  simp [Nat_digitchar_neq_underscore, Hnin]
  apply ind <;> simp [*, Nat_digitchar_neq_underscore]

theorem Nat_toString_not_contain_underscore {x: Nat} : '_' ∉ (toString x).toList := by
  simp [toString, Nat.repr, Nat.toDigits]
  exact Nat_toDigitsCore_not_contain_underscore (l := []) (by simp)

theorem Nat_digitChar_index: x.digitChar =
    #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f','*'][min x 16]'(by simp; omega) := by
  unfold Nat.digitChar
  match h : x with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => simp
  | j + 16 => simp

theorem nodup_implies_injective (H: List.Nodup a) (Hl1: x < a.length) (Hl2: y < a.length) (eq : a[x]'Hl1 = a[y]'Hl2) : x = y := by
  unfold List.Nodup at H
  induction a generalizing x y
  case nil =>
    simp at Hl1
  case cons h t ind =>
    simp only [List.pairwise_cons] at H
    grind

theorem Nat_eq_of_digitChar_eq : n < 16 → m < 16 → n.digitChar = m.digitChar → n = m := by
  intro H1 H2
  simp [Nat_digitChar_index]
  have: min n 16 = n := by omega
  simp [this]
  have: min m 16 = m := by omega
  simp [this]
  intro H
  apply nodup_implies_injective (by simp) _ _ H

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

theorem Nat_toDigitsCore_list_len_lt : x > 0 → n > 0 → (Nat.toDigitsCore 10 x n l).length > l.length := by
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
  simp only [toString, Nat.repr] at H
  apply Nat_eq_of_toDigitsCore_eq (by simp) (by simp) (String.ofList_injective H)

private theorem under_toList : "_".toList = ['_'] := rfl

theorem Nat_eq_of_StringGen_suffix {x y: Nat}: ("_" ++ toString x).IsSuffix (s ++ "_" ++ toString y) → x = y := by
  intro Hsuf
  apply Nat_eq_of_toString_eq
  if x_lt : (toString x).length < (toString y).length then
    simp only [String.IsSuffix, String.toList_append, under_toList] at Hsuf
    have Hsuf': (toString y).toList  <:+ s.toList ++ ['_'] ++ (toString y).toList :=
      List.suffix_append_of_suffix (List.suffix_refl _)
    have ⟨t, h⟩ : ['_'] ++ (toString x).toList <:+ (toString y).toList :=
      List.suffix_of_suffix_length_le Hsuf Hsuf' (by simp; exact x_lt)
    have : '_' ∈ (toString y).toList := by grind
    have := @Nat_toString_not_contain_underscore y
    contradiction
  else if x_gt : (toString x).length > (toString y).length then
    have Hsuf : (toString x).toList <:+ s.toList ++ ['_'] ++ (toString y).toList := by
      obtain ⟨t, H⟩ := Hsuf
      exists t ++ ['_']
      simp only [String.toList_append, under_toList, List.append_assoc] at H
      simp only [List.append_assoc]
      exact H
    have Hsuf': ['_'] ++ (toString y).toList  <:+ s.toList ++ ['_'] ++ (toString y).toList := by
      simp only [List.append_assoc]
      exact List.suffix_append_of_suffix (List.suffix_refl _)
    have ⟨t, h⟩ : ['_'] ++ (toString y).toList <:+ (toString x).toList :=
      List.suffix_of_suffix_length_le Hsuf' Hsuf (by simp_all; exact x_gt)
    have : '_' ∈ (toString x).toList := by grind
    have := @Nat_toString_not_contain_underscore x
    contradiction
  else
    have eq_len: (toString x).length = (toString y).length := by omega
    obtain ⟨cs, H⟩ := Hsuf
    simp only [String.toList_append, ← List.append_assoc] at H
    have this := List.append_inj_right' H eq_len
    exact String.toList_inj.mp this

/--
The uniqueness of the generated string follows from the following: given that the numbers at the end of all strings are unique, then the strings themselves must be unique.
-/
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
  · rename_i H
    simp only [H.right, H.left, String.IsSuffix, String.toList_append, List.append_assoc]
    apply List.suffix_append
  · apply Hwf.right.right.right <;> assumption

/-! ## Convenience helpers for the list of generated string labels -/

/-- The empty generator state is well-formed. -/
theorem StringGenState.wf_emp : StringGenState.WF StringGenState.emp := by
  simp [StringGenState.WF, Counter.WF]

/-- Convenience: the list of generated string labels in a `StringGenState`. -/
def StringGenState.stringGens (σ : StringGenState) : List String :=
  σ.generated.unzip.2

/-- The empty generator state has produced no labels. -/
@[simp] theorem StringGenState.stringGens_emp :
    StringGenState.stringGens StringGenState.emp = [] := by
  simp [StringGenState.stringGens, StringGenState.emp]

/-- No string is among the empty generator state's produced labels. -/
theorem StringGenState.not_mem_stringGens_emp (s : String) :
    s ∉ StringGenState.stringGens StringGenState.emp := by
  rw [StringGenState.stringGens_emp]; exact List.not_mem_nil

/-- After generating, the new state's labels list is the new label cons'd onto the old. -/
theorem StringGenState.stringGens_gen
    (pf : String) (σ : StringGenState) :
    StringGenState.stringGens (StringGenState.gen pf σ).2
      = (StringGenState.gen pf σ).1 :: StringGenState.stringGens σ := by
  simp [StringGenState.gen, StringGenState.stringGens]

/-- The freshly generated label is not in the old state's labels list, given WF. -/
theorem StringGenState.stringGens_gen_not_in
    (pf : String) (σ : StringGenState) (hwf : StringGenState.WF σ) :
    (StringGenState.gen pf σ).1 ∉ StringGenState.stringGens σ := by
  intro h_in
  have hwf' : StringGenState.WF (StringGenState.gen pf σ).2 :=
    StringGenState.WFMono hwf rfl
  have h_gens_eq : StringGenState.stringGens (StringGenState.gen pf σ).2
      = (StringGenState.gen pf σ).1 :: StringGenState.stringGens σ :=
    StringGenState.stringGens_gen pf σ
  have h_nodup : (StringGenState.stringGens (StringGenState.gen pf σ).2).Nodup := by
    simp only [StringGenState.WF] at hwf'
    exact hwf'.2.2.1
  rw [h_gens_eq] at h_nodup
  rw [List.nodup_cons] at h_nodup
  exact h_nodup.1 h_in

/-! ## Shape predicates: distinguishing user labels from generated labels

Every label produced by `StringGenState.gen pf σ` has the form
`pf ++ "_" ++ toString n` for some natural number `n`. This means user-provided
labels can be guaranteed disjoint from generator output by demonstrating that
they do *not* match this suffix shape, or that they have a non-overlapping
prefix in front of the trailing `_<digits>`.

The lemmas below provide the building blocks for proving such disjointness.
The most useful one for client code is `gen_ne_of_not_hasUnderscoreDigitSuffix`:
a string without the `_<digits>` suffix shape can never be the output
of `gen`. -/

/-- A string has the shape `_<digits>` as a (non-empty) suffix.  Equivalently,
its last `_` is followed only by digit characters (and there is at least one).
This is exactly the shape a label generated by `gen` always has. -/
def String.HasUnderscoreDigitSuffix (s : String) : Prop :=
  ∃ pf n, s = pf ++ "_" ++ toString (n : Nat)

/-- The label produced by `gen` has the form `pf ++ "_" ++ toString n`. -/
theorem StringGenState.gen_eq (pf : String) (σ : StringGenState) :
    (StringGenState.gen pf σ).1 = pf ++ "_" ++ toString σ.cs.counter := by
  simp [StringGenState.gen, Counter.genCounter]

/-- Every label produced by `gen` has the `_<digits>` suffix shape. -/
theorem StringGenState.gen_hasUnderscoreDigitSuffix
    (pf : String) (σ : StringGenState) :
    String.HasUnderscoreDigitSuffix (StringGenState.gen pf σ).1 := by
  refine ⟨pf, σ.cs.counter, ?_⟩
  exact StringGenState.gen_eq pf σ

/-- Every label inside a WF `StringGenState`'s `generated` list has the
`_<digits>` suffix shape. -/
theorem StringGenState.hasUnderscoreDigitSuffix_of_mem_generated
    {σ : StringGenState} (hwf : StringGenState.WF σ)
    {s : String} (hs : s ∈ σ.stringGens) :
    String.HasUnderscoreDigitSuffix s := by
  simp only [StringGenState.stringGens, List.unzip_snd, List.mem_map] at hs
  obtain ⟨⟨c, s'⟩, h_mem, h_eq⟩ := hs
  subst h_eq
  have hsuf : ("_" ++ toString c).IsSuffix s' := hwf.2.2.2 c s' h_mem
  obtain ⟨t_chars, h_t⟩ := hsuf
  refine ⟨String.ofList t_chars, c, ?_⟩
  apply String.toList_inj.mp
  simp only [String.toList_append, under_toList, String.toList_ofList]
  rw [← h_t, String.toList_append, under_toList]
  simp [List.append_assoc]

/-- If a string does not have the `_<digits>` suffix shape, it cannot have been
produced by `gen`. -/
theorem StringGenState.gen_ne_of_not_hasUnderscoreDigitSuffix
    (pf : String) (σ : StringGenState) (s : String)
    (h : ¬ String.HasUnderscoreDigitSuffix s) :
    s ≠ (StringGenState.gen pf σ).1 := by
  intro h_eq
  apply h
  rw [h_eq]
  exact StringGenState.gen_hasUnderscoreDigitSuffix pf σ

/-- If a string does not have the `_<digits>` suffix shape, it cannot appear
in the `stringGens` list of any WF `StringGenState`. -/
theorem StringGenState.not_mem_stringGens_of_not_hasUnderscoreDigitSuffix
    {σ : StringGenState} (hwf : StringGenState.WF σ)
    {s : String} (h : ¬ String.HasUnderscoreDigitSuffix s) :
    s ∉ σ.stringGens := by
  intro h_in
  exact h (StringGenState.hasUnderscoreDigitSuffix_of_mem_generated hwf h_in)

/-- Two `gen` calls with different prefixes produce different labels, given
WF: the suffix `_<counter>` matches but the prefix preceding the *last* `_`
must coincide; together with `WF` ensuring no `_` appears in the digit suffix,
the prefixes themselves must be equal. -/
theorem StringGenState.gen_inj_of_pf_eq
    {pf₁ pf₂ : String} {σ₁ σ₂ : StringGenState}
    (h : (StringGenState.gen pf₁ σ₁).1 = (StringGenState.gen pf₂ σ₂).1) :
    pf₁ ++ "_" ++ toString σ₁.cs.counter = pf₂ ++ "_" ++ toString σ₂.cs.counter := by
  rw [StringGenState.gen_eq, StringGenState.gen_eq] at h
  exact h

/-- A string with prefix `pf` followed by `_` is generated only if its
suffix-counter portion's prefix matches. Combined with the `Nat_eq_of_StringGen_suffix`
machinery: if a user label `pf' ++ rest` does not have the `_<digits>` shape,
it cannot equal any `gen pf σ`. -/
theorem StringGenState.gen_ne_of_user_label_no_digit_suffix
    {pf : String} {σ : StringGenState} {s : String}
    (h : ¬ String.HasUnderscoreDigitSuffix s) :
    s ≠ (StringGenState.gen pf σ).1 :=
  StringGenState.gen_ne_of_not_hasUnderscoreDigitSuffix pf σ s h

/-! ## GenStep: well-formed monotone transitions of a `StringGenState`

A `GenStep gen gen'` witnesses that `gen` transitioned to `gen'` via some
sequence of `gen` operations: well-formedness is preserved and the set of
generated labels only grows. Useful as a reusable abstraction for any
monadic computation in `StringGenM`. -/

/-- A "generator step": a transition from `gen` to `gen'` that preserves
well-formedness and only adds new labels (never removes them). -/
structure StringGenState.GenStep (gen gen' : StringGenState) : Prop where
  wf_mono : StringGenState.WF gen → StringGenState.WF gen'
  subset  : StringGenState.stringGens gen ⊆ StringGenState.stringGens gen'

namespace StringGenState.GenStep

/-- Identity transition. -/
theorem refl (gen : StringGenState) : GenStep gen gen :=
  ⟨id, fun _ h => h⟩

/-- Composition of transitions. -/
theorem trans {gen gen_mid gen' : StringGenState}
    (h₁ : GenStep gen gen_mid) (h₂ : GenStep gen_mid gen') :
    GenStep gen gen' :=
  ⟨h₂.wf_mono ∘ h₁.wf_mono, fun _ hx => h₂.subset (h₁.subset hx)⟩

/-- A single `gen` call is a `GenStep`. -/
theorem of_gen (pf : String) (σ : StringGenState) :
    GenStep σ (StringGenState.gen pf σ).2 := by
  refine ⟨?_, ?_⟩
  · intro hwf; exact StringGenState.WFMono hwf rfl
  · intro x hx
    rw [StringGenState.stringGens_gen]
    exact List.mem_cons.mpr (Or.inr hx)

end StringGenState.GenStep

/-! ## Kind-contract: per-prefix membership witnesses

The shape predicate `HasUnderscoreDigitSuffix` answers "could this label have
come from *some* generator". For composing several generators that each mint
under their own prefix, we need a finer, per-prefix contract: a label `s` was
minted under prefix `pf` exactly when `pf ++ "_"` is a prefix of `s`, which
`HasGenPrefix` captures. -/

/-- `pf` is a *generator prefix* of `s`: the literal `pf ++ "_"` is a prefix of
`s`. Every label produced by `gen pf σ` satisfies `HasGenPrefix pf`. -/
@[expose]
def String.HasGenPrefix (pf s : String) : Prop :=
  (pf ++ "_").toList.isPrefixOf s.toList = true

/-- The label produced by `gen pf σ` carries `pf` as a generator prefix. -/
theorem StringGenState.gen_hasGenPrefix (pf : String) (σ : StringGenState) :
    String.HasGenPrefix pf (StringGenState.gen pf σ).1 := by
  unfold String.HasGenPrefix
  rw [gen_eq, List.isPrefixOf_iff_prefix]
  refine ⟨(toString σ.cs.counter).toList, ?_⟩
  simp [String.toList_append, List.append_assoc]

/-! ## Membership tracking: `AllMem`

A prefix-only contract is too weak to certify a *foreign-label* obligation
against a predicate that — like the structured-to-unstructured label *kind* —
pins the label to a concrete `gen`-output equality (a non-generated string
sharing a prefix would slip past a prefix check).

`AllMem R σ` is the stronger invariant: *every produced label satisfies `R`
itself*.  At each `gen pf` step the newly produced label is literally
`(gen pf σ).1`, so the step preserves `AllMem R` as soon as `R` holds of every
`gen`-output under that prefix — exactly the per-prefix mint witnesses a pass
already establishes.  The foreign discharge is then plain contraposition. -/

/-- `AllMem R σ`: every label produced so far satisfies `R`. -/
@[expose]
def StringGenState.AllMem (R : String → Prop) (σ : StringGenState) : Prop :=
  ∀ s ∈ stringGens σ, R s

/-- The empty generator state vacuously satisfies any `AllMem`. -/
theorem StringGenState.allMem_emp (R : String → Prop) :
    StringGenState.AllMem R StringGenState.emp := by
  intro s hs
  rw [stringGens_emp] at hs
  exact absurd hs (List.not_mem_nil)

/-- `AllMem` is preserved by a `gen pf` step whose newly produced label satisfies
`R`. -/
theorem StringGenState.allMem_gen (R : String → Prop) (pf : String)
    (σ : StringGenState) (h : StringGenState.AllMem R σ)
    (hnew : R (StringGenState.gen pf σ).1) :
    StringGenState.AllMem R (StringGenState.gen pf σ).2 := by
  intro s hs
  rw [stringGens_gen, List.mem_cons] at hs
  rcases hs with hnew' | hold
  · exact hnew' ▸ hnew
  · exact h s hold

/-- THE BRIDGE: a label `s` that fails `R` cannot appear in a state satisfying
`AllMem R`.  Plain contraposition — no generator-shape reasoning needed. -/
theorem StringGenState.not_mem_stringGens_of_not_allMem {R : String → Prop}
    {σ : StringGenState} {s : String}
    (hall : StringGenState.AllMem R σ) (hns : ¬ R s) :
    s ∉ stringGens σ := fun h_in => hns (hall s h_in)

end
