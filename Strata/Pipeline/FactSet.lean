/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Lean

/-! # Fact sets, independent of any language

A pipeline phase declares what it needs of the program it receives and what it
guarantees about the program it produces, as sets of named *facts*. Nothing about
that machinery is specific to a language: this module holds the vocabulary of
facts, the sets over it, and the operations the composition check needs, so that
Core and Laurel can each supply a fact type and share everything else.

Two classes:

* `FactVocabulary F` — the facts themselves: a closed enumeration with names for
  diagnostics. One instance per language.
* `FactAlgebra F` — how a set of facts is represented: `ofList` and `toList`
  with their two laws, and union, intersection and decidable inclusion, so that a
  representation whose facts are ordered can walk two sets together instead of
  testing membership per fact. `CanonicalFactList` is the default: the facts in
  declaration order, carrying the proof that they are.

Its key results are what specify those three operations for the default
representation. `canon_subset_iff_sublist` says inclusion between canonical lists
is the sublist relation, which is what makes it one walk; `mergeWalk_eq_filter`
and `interWalk_eq_filter` say the union and intersection walks compute the facts
of either and of both. The lemmas carrying the cursor invariant through those
proofs are `private`.
-/

namespace Strata.Pipeline

public section

/-! ## The vocabulary -/

/-- The facts a pipeline talks about: a closed enumeration, with names used in
    diagnostics. `all_complete` and `all_nodup` are fields rather than theorems
    because the generic layer cannot decide them for an unknown `F`; for a
    concrete enum both are `by decide`. -/
class FactVocabulary (F : Type) where
  /-- Facts can be compared. -/
  decEq : DecidableEq F
  /-- Every fact, in the order that defines canonical form. -/
  all : List F
  /-- `all` enumerates every fact. -/
  all_complete : ∀ f : F, f ∈ all
  /-- and lists each of them once. -/
  all_nodup : all.Nodup
  /-- Short, human-readable name, used in diagnostics. -/
  name : F → String

variable {F : Type} [FactVocabulary F]

/-- Facts can be compared, from the vocabulary. Reducible, as an instance
    producing a `DecidableEq` must be. -/
@[expose, reducible, instance] def factDecidableEq : DecidableEq F := FactVocabulary.decEq

/-- Short name of a fact. -/
@[expose] def factName (f : F) : String := FactVocabulary.name f

/-! ## Canonical lists

Canonicity is what makes a set's representation unique, which is what lets a
set index a type: `[a, b]` and `[b, a]` must not be two different indices for
one set. Filtering the fixed enumeration *is* the sort, so no order instance
and no sorting algorithm is needed. -/

/-- Canonicalize `l`: the facts of `l`, in `FactVocabulary.all` order, without
    duplicates. -/
@[expose] def canonFacts (l : List F) : List F :=
  (FactVocabulary.all (F := F)).filter (· ∈ l)

/-- `l` is canonical: its facts appear in `FactVocabulary.all` order without
    duplicates.

    Phrased as a fixpoint of the canonicalizing filter rather than as `Sorted`,
    because that needs no order instance on `F`, is decided by `decEq`, and
    reduces uniqueness of the representation to two rewrites. -/
@[expose] def FactsCanonical (l : List F) : Prop := canonFacts l = l

instance (l : List F) : Decidable (FactsCanonical l) :=
  inferInstanceAs (Decidable (_ = _))

/-! The two lemmas below are stated here rather than with the other theorems
about this representation, because the default `FactAlgebra` instance at the end
of this file is built from them: `ofList` from `factsCanonical_canonFacts` and
`mem_toList` from `mem_canonFacts`. A properties module imports its definition
module, so a definition cannot depend on a theorem stated there. -/

/-- Canonicalization preserves membership: reordering a list of facts and
    dropping its duplicates changes which facts it contains not at all. -/
@[simp] theorem mem_canonFacts {f : F} {l : List F} : f ∈ canonFacts l ↔ f ∈ l := by
  simp [canonFacts, List.mem_filter, FactVocabulary.all_complete f]

/-- Canonicalizing a list produces a canonical one, which is the proof every
    set built from a runtime list carries. -/
theorem factsCanonical_canonFacts (l : List F) : FactsCanonical (canonFacts l) := by
  unfold FactsCanonical canonFacts
  apply List.filter_congr
  intro f _
  simp [List.mem_filter, FactVocabulary.all_complete f]

/-! ### Inclusion is linear because both sides are canonical

Two canonical lists are ordered by the same enumeration, so one containing every
fact of the other is the same as it *being* a sublist of it. That turns the
inclusion the composition check runs per phase into the one-pass sublist walk
Lean's core provides, rather than a membership scan per fact. -/

omit [FactVocabulary F] in
/-- Filtering one list by a weaker predicate yields a sublist. -/
private theorem filter_sublist_filter {l : List F} {p q : F → Bool}
    (h : ∀ f ∈ l, p f = true → q f = true) : (l.filter p).Sublist (l.filter q) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun f hf => h f (List.mem_cons_of_mem a hf))
    by_cases hp : p a = true
    · have hq : q a = true := h a List.mem_cons_self hp
      simp only [List.filter_cons, hp, hq, if_pos]
      exact List.cons_sublist_cons.mpr ih'
    · by_cases hq : q a = true
      · simp only [List.filter_cons, hp, hq, if_pos]
        exact ih'.cons a
      · simp only [List.filter_cons, hp, hq]
        exact ih'

/-- For canonical lists, containing every fact of another is being a sublist of
    it, which is decided in one walk of the two lists. -/
theorem canon_subset_iff_sublist {l₁ l₂ : List F}
    (h₁ : FactsCanonical l₁) (h₂ : FactsCanonical l₂) :
    (∀ f ∈ l₁, f ∈ l₂) ↔ l₁.Sublist l₂ := by
  constructor
  · intro h
    rw [← h₁, ← h₂]
    unfold canonFacts
    exact filter_sublist_filter (fun f _ hf => by
      have hf₁ : f ∈ l₁ := by simpa using hf
      simpa using h f hf₁)
  · intro hs f hf
    exact hs.mem hf

/-! ### Union and intersection in one walk

The same observation makes union and intersection one pass: walking the
vocabulary with a cursor into each set, a set contains the fact under
consideration exactly when that fact heads its cursor. `stepCursor` advances one
cursor, and the three lemmas below are the invariant — a stepped cursor is still
a cursor into the rest of the vocabulary, heading a cursor is containment, and
stepping changes nothing about the facts still to come. -/

/-- Advance `l` past `a` when `a` heads it, otherwise leave it alone. -/
@[expose] def stepCursor (a : F) (l : List F) : List F :=
  match l with
  | [] => []
  | b :: rest => if a = b then rest else l

omit [FactVocabulary F] in
/-- Heading a cursor into `a :: as` is containing `a`, when `a` occurs once. -/
private theorem head_eq_iff_mem {a : F} {as l : List F}
    (hnd : (a :: as).Nodup) (h : l.Sublist (a :: as)) : l.head? = some a ↔ a ∈ l := by
  constructor
  · intro hh
    match l, hh with
    | b :: _, hh => simp only [List.head?_cons, Option.some.injEq] at hh; simp [hh]
  · intro hmem
    cases h with
    | cons _ h' => exact absurd (h'.mem hmem) (List.nodup_cons.mp hnd).1
    | cons₂ _ _ => simp

/-- A stepped cursor is a cursor into the rest of the vocabulary. -/
private theorem stepCursor_sublist {a : F} {as l : List F}
    (hnd : (a :: as).Nodup) (h : l.Sublist (a :: as)) : (stepCursor a l).Sublist as := by
  cases h with
  | cons _ h' =>
    match l, h' with
    | [], _ => simp [stepCursor]
    | b :: rest, h' =>
      have hne : ¬ a = b := by
        intro heq
        exact (List.nodup_cons.mp hnd).1 (heq ▸ h'.mem List.mem_cons_self)
      simp only [stepCursor, if_neg hne]
      exact h'
  | cons₂ _ h' => simpa [stepCursor] using h'

/-- Stepping past `a` cannot lose a fact of `as`, since `a` occurs once in the
    vocabulary. -/
private theorem mem_stepCursor {a f : F} {as l : List F}
    (hnd : (a :: as).Nodup) (hf : f ∈ as) :
    f ∈ stepCursor a l ↔ f ∈ l := by
  have hfa : ¬ f = a := fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ hf)
  match l with
  | [] => simp [stepCursor]
  | b :: rest =>
    by_cases hab : a = b
    · subst hab
      simp only [stepCursor, List.mem_cons]
      exact ⟨fun hm => Or.inr hm, fun hm => hm.elim (fun he => absurd he hfa) id⟩
    · simp [stepCursor, hab]

/-- A canonical list is a cursor into the vocabulary. -/
private theorem canonical_sublist_all {l : List F} (h : FactsCanonical l) :
    l.Sublist (FactVocabulary.all (F := F)) := by
  rw [← h]
  exact List.filter_sublist

/-- Any filter of the vocabulary is canonical, which is what makes a walk's
    result a fact set without a second canonicity argument. -/
private theorem factsCanonical_filter (p : F → Bool) :
    FactsCanonical ((FactVocabulary.all (F := F)).filter p) := by
  unfold FactsCanonical canonFacts
  apply List.filter_congr
  intro f hf
  simp [List.mem_filter, hf]

/-- Union of two cursors, walking the vocabulary once. -/
@[expose] def mergeWalk : List F → List F → List F → List F
  | [], _, _ => []
  | a :: as, l₁, l₂ =>
    if l₁.head? = some a ∨ l₂.head? = some a then
      a :: mergeWalk as (stepCursor a l₁) (stepCursor a l₂)
    else mergeWalk as (stepCursor a l₁) (stepCursor a l₂)

/-- Intersection of two cursors, walking the vocabulary once. -/
@[expose] def interWalk : List F → List F → List F → List F
  | [], _, _ => []
  | a :: as, l₁, l₂ =>
    if l₁.head? = some a ∧ l₂.head? = some a then
      a :: interWalk as (stepCursor a l₁) (stepCursor a l₂)
    else interWalk as (stepCursor a l₁) (stepCursor a l₂)

/-- The walk computes exactly the facts of either set, in vocabulary order. -/
theorem mergeWalk_eq_filter {as l₁ l₂ : List F} (hnd : as.Nodup)
    (h₁ : l₁.Sublist as) (h₂ : l₂.Sublist as) :
    mergeWalk as l₁ l₂ = as.filter (fun f => decide (f ∈ l₁ ∨ f ∈ l₂)) := by
  induction as generalizing l₁ l₂ with
  | nil =>
    have e₁ : l₁ = [] := List.sublist_nil.mp h₁
    have e₂ : l₂ = [] := List.sublist_nil.mp h₂
    simp [mergeWalk, e₁, e₂]
  | cons a as ih =>
    have hnd' : as.Nodup := (List.nodup_cons.mp hnd).2
    have s₁ := stepCursor_sublist hnd h₁
    have s₂ := stepCursor_sublist hnd h₂
    have rest := ih hnd' s₁ s₂
    have congrFilter : as.filter (fun f => decide (f ∈ stepCursor a l₁ ∨ f ∈ stepCursor a l₂))
        = as.filter (fun f => decide (f ∈ l₁ ∨ f ∈ l₂)) := by
      apply List.filter_congr
      intro f hf
      simp only [decide_eq_decide]
      rw [mem_stepCursor hnd hf, mem_stepCursor hnd hf]
    by_cases hhead : l₁.head? = some a ∨ l₂.head? = some a
    · have hmem : a ∈ l₁ ∨ a ∈ l₂ := by
        rcases hhead with h | h
        · exact Or.inl ((head_eq_iff_mem hnd h₁).mp h)
        · exact Or.inr ((head_eq_iff_mem hnd h₂).mp h)
      simp only [mergeWalk, if_pos hhead, List.filter_cons, decide_eq_true hmem, if_pos]
      rw [rest, congrFilter]
    · have hmem : ¬ (a ∈ l₁ ∨ a ∈ l₂) := by
        intro hm
        rcases hm with h | h
        · exact hhead (Or.inl ((head_eq_iff_mem hnd h₁).mpr h))
        · exact hhead (Or.inr ((head_eq_iff_mem hnd h₂).mpr h))
      simp only [mergeWalk, if_neg hhead, List.filter_cons, decide_eq_false hmem,
        if_false, Bool.false_eq_true]
      rw [rest, congrFilter]

/-- Intersection's walk computes the facts of both sets. -/
theorem interWalk_eq_filter {as l₁ l₂ : List F} (hnd : as.Nodup)
    (h₁ : l₁.Sublist as) (h₂ : l₂.Sublist as) :
    interWalk as l₁ l₂ = as.filter (fun f => decide (f ∈ l₁ ∧ f ∈ l₂)) := by
  induction as generalizing l₁ l₂ with
  | nil =>
    have e₁ : l₁ = [] := List.sublist_nil.mp h₁
    have e₂ : l₂ = [] := List.sublist_nil.mp h₂
    simp [interWalk, e₁, e₂]
  | cons a as ih =>
    have hnd' : as.Nodup := (List.nodup_cons.mp hnd).2
    have rest := ih hnd' (stepCursor_sublist hnd h₁) (stepCursor_sublist hnd h₂)
    have congrFilter : as.filter (fun f => decide (f ∈ stepCursor a l₁ ∧ f ∈ stepCursor a l₂))
        = as.filter (fun f => decide (f ∈ l₁ ∧ f ∈ l₂)) := by
      apply List.filter_congr
      intro f hf
      simp only [decide_eq_decide]
      rw [mem_stepCursor hnd hf, mem_stepCursor hnd hf]
    by_cases hhead : l₁.head? = some a ∧ l₂.head? = some a
    · have hmem : a ∈ l₁ ∧ a ∈ l₂ :=
        ⟨(head_eq_iff_mem hnd h₁).mp hhead.1, (head_eq_iff_mem hnd h₂).mp hhead.2⟩
      simp only [interWalk, if_pos hhead, List.filter_cons, decide_eq_true hmem, if_pos]
      rw [rest, congrFilter]
    · have hmem : ¬ (a ∈ l₁ ∧ a ∈ l₂) := by
        intro hm
        exact hhead ⟨(head_eq_iff_mem hnd h₁).mpr hm.1, (head_eq_iff_mem hnd h₂).mpr hm.2⟩
      simp only [interWalk, if_neg hhead, List.filter_cons, decide_eq_false hmem,
        if_false, Bool.false_eq_true]
      rw [rest, congrFilter]

/-! ## Discharging canonicity

A written-out set is checked when it is elaborated, so it costs nothing at
runtime, and a misordered or duplicated literal is an author error worth a fix
rather than a silent normalization. The tactic works for any fact type: it
reduces the vocabulary's `all` and the given list to expressions and compares
them, so it needs no knowledge of `F`'s constructors. -/

open Lean Elab Tactic Meta in
/-- The elements of a `List F` expression, or `none` when it is not a concrete
    list — which is how `canon_facts` tells an author error from a set that only
    exists at runtime. -/
private meta partial def reduceListExpr (e : Lean.Expr) : MetaM (Option (List Lean.Expr)) := do
  withTransparency .all do
    let e ← reduce e (skipTypes := false) (skipProofs := false)
    match_expr e with
    | List.nil _ => return some []
    | List.cons _ h t =>
      let some tv ← reduceListExpr t | return none
      return some (h :: tv)
    | _ => return none

open Lean Meta in
/-- How a fact expression is written in a literal: `.noLoops` for a
    constructor, its pretty-printed form otherwise. -/
private meta def renderFact (e : Lean.Expr) : MetaM String := do
  match e.getAppFn.constName? with
  | some n => return "." ++ n.getString!
  | none => return toString (← ppExpr e)

open Lean Elab Tactic Meta in
/-- Discharge the canonicity obligation a canonical fact set carries.

    A canonical literal is closed by `decide`. A non-canonical one is reported
    with the literal to write instead, spelled with the notation whose name is
    given (`factSet!` by default). A set the tactic cannot see is not an error:
    it is the case `ofList` exists for. -/
elab "canon_facts" notation?:(str)? : tactic => do
  let notationName := match notation? with
    | some s => s.getString
    | none => "factSet!"
  let goal ← instantiateMVars (← getMainTarget)
  let_expr FactsCanonical factType vocab l := goal
    | throwError "canon_facts: goal is not of the form `FactsCanonical _`"
  let some given ← reduceListExpr l
    | throwError "fact set is not statically known, so `canon_facts` cannot check \
        that it is in canonical order. Use `ofList`, which sorts the list at \
        runtime and produces the proof, or write a concrete literal here."
  let allExpr ← instantiateMVars (← mkAppOptM ``FactVocabulary.all #[factType, vocab])
  let some every ← reduceListExpr allExpr
    | throwError "canon_facts: the vocabulary's `all` did not reduce to a list of facts"
  -- Canonical order: the enumeration filtered by membership in what was given.
  let mut canon : List Lean.Expr := []
  for e in every do
    if ← given.anyM (fun g => isDefEq g e) then
      canon := canon ++ [e]
  let sameLength := canon.length == given.length
  let mut same := sameLength
  if sameLength then
    for (a, b) in canon.zip given do
      unless ← isDefEq a b do same := false
  if same then
    evalTactic (← `(tactic| decide))
  else
    let duplicated := canon.length != given.length
    let reason := if duplicated then "lists a fact more than once"
                  else "lists facts out of order"
    let rendered ← canon.mapM (fun e => liftM (renderFact e))
    let order := match factType.getAppFn.constName? with
      | some n => s!"`{n.getString!}.all`"
      | none => "declaration"
    throwError "fact set {reason}; fact sets must be written in {order} \
      declaration order without duplicates. Write \
      {notationName}[{", ".intercalate rendered}] instead. For a list that is \
      only known at runtime, use `ofList`, which sorts it and produces the proof."

/-! ## The default representation -/

/-- A set of facts as a list in `FactVocabulary.all` order, carrying the proof
    that it is. The canonicity proof is an auto-param, so it stays invisible at
    ordinary construction sites. -/
structure CanonicalFactList (F : Type) [FactVocabulary F] where
  /-- The facts, in declaration order, without duplicates. -/
  facts : List F
  /-- Canonicity of `facts`, discharged statically. -/
  canonical : FactsCanonical facts := by canon_facts

/-! ## The algebra

What the machinery needs of a representation: build a set from a list, read the
facts back, and two laws. Everything else — empty, universe, union,
intersection, inclusion, difference — is derived below, so a new representation
(a bit mask, say) is a handful of lines. A representation that can beat the
derived operations may gain fields for them later without disturbing callers. -/

class FactAlgebra (F : Type) [FactVocabulary F] where
  /-- The representation. -/
  Set : Type
  /-- Build a set from a list, in whatever order the list came. -/
  ofList : List F → Set
  /-- The facts of a set, in a deterministic order, so a diagnostic reads the
      same on every run. -/
  toList : Set → List F
  /-- `ofList` keeps exactly the facts it was given. -/
  mem_toList : ∀ (f : F) (l : List F), f ∈ toList (ofList l) ↔ f ∈ l
  /-- Two sets with the same facts are the same set. This is what lets a set
      index a type; a representation admitting two values with the same members
      cannot be used here. -/
  ext : ∀ (σ₁ σ₂ : Set), (∀ f, f ∈ toList σ₁ ↔ f ∈ toList σ₂) → σ₁ = σ₂
  /-- Union, so that a representation whose facts are ordered can walk the two
      sets together rather than test membership per fact. -/
  union : Set → Set → Set
  /-- `union` holds the facts of either set, however it is computed. -/
  mem_union : ∀ (σ₁ σ₂ : Set) (f : F),
      f ∈ toList (union σ₁ σ₂) ↔ f ∈ toList σ₁ ∨ f ∈ toList σ₂
  /-- Intersection, for the same reason as `union`. -/
  inter : Set → Set → Set
  /-- `inter` holds the facts of both sets, however it is computed. -/
  mem_inter : ∀ (σ₁ σ₂ : Set) (f : F),
      f ∈ toList (inter σ₁ σ₂) ↔ f ∈ toList σ₁ ∧ f ∈ toList σ₂
  /-- How inclusion is decided, which is the operation the composition check runs
      once per phase. The default tests membership per fact,
      `O(|σ₁| · |σ₂|)`; a representation whose facts are ordered can walk the two
      sets together instead, which is what the canonical list does. -/
  decSubset : ∀ (σ₁ σ₂ : Set), Decidable (∀ f ∈ toList σ₁, f ∈ toList σ₂) :=
    fun _ _ => inferInstance

/-- The set type of the ambient algebra. -/
@[expose] abbrev FactSet (F : Type) [FactVocabulary F] [FactAlgebra F] : Type :=
  FactAlgebra.Set (F := F)

/-- Static construction: the canonicity obligation is discharged when the
    literal is elaborated, so a written-out contract costs nothing at runtime
    and a misordered or duplicated literal is a compile error naming the literal
    to write instead. The fact type comes from the expected type, so any
    vocabulary can use it. -/
syntax (name := factSetNotation)
  "factSet![" sepBy(term, ",", ", ", allowTrailingSep) "]" : term

macro_rules
  | `(factSet![$fs,*]) =>
    `(({ facts := [$fs,*], canonical := by canon_facts "factSet!" } : CanonicalFactList _))

/-- The default representation is the canonical list. -/
instance : FactAlgebra F where
  Set := CanonicalFactList F
  ofList l := ⟨canonFacts l, factsCanonical_canonFacts l⟩
  toList σ := σ.facts
  -- Both lists are canonical, so inclusion is being a sublist, which core
  -- decides by one walk of the two lists rather than a membership scan per fact.
  decSubset σ₁ σ₂ :=
    decidable_of_iff (σ₁.facts.Sublist σ₂.facts)
      (canon_subset_iff_sublist σ₁.canonical σ₂.canonical).symm
  -- One walk of the vocabulary and the two cursors, rather than a membership
  -- test per fact.
  union σ₁ σ₂ :=
    ⟨mergeWalk (FactVocabulary.all (F := F)) σ₁.facts σ₂.facts, by
      rw [mergeWalk_eq_filter FactVocabulary.all_nodup
            (canonical_sublist_all σ₁.canonical) (canonical_sublist_all σ₂.canonical)]
      exact factsCanonical_filter _⟩
  mem_union σ₁ σ₂ f := by
    show f ∈ mergeWalk _ _ _ ↔ _
    rw [mergeWalk_eq_filter FactVocabulary.all_nodup
          (canonical_sublist_all σ₁.canonical) (canonical_sublist_all σ₂.canonical)]
    simp [List.mem_filter, FactVocabulary.all_complete f]
  inter σ₁ σ₂ :=
    ⟨interWalk (FactVocabulary.all (F := F)) σ₁.facts σ₂.facts, by
      rw [interWalk_eq_filter FactVocabulary.all_nodup
            (canonical_sublist_all σ₁.canonical) (canonical_sublist_all σ₂.canonical)]
      exact factsCanonical_filter _⟩
  mem_inter σ₁ σ₂ f := by
    show f ∈ interWalk _ _ _ ↔ _
    rw [interWalk_eq_filter FactVocabulary.all_nodup
          (canonical_sublist_all σ₁.canonical) (canonical_sublist_all σ₂.canonical)]
    simp [List.mem_filter, FactVocabulary.all_complete f]
  mem_toList _ _ := by simp
  ext σ₁ σ₂ h := by
    obtain ⟨l₁, c₁⟩ := σ₁
    obtain ⟨l₂, c₂⟩ := σ₂
    have hl : l₁ = l₂ := by
      calc l₁ = canonFacts l₁ := c₁.symm
        _ = canonFacts l₂ := by
            unfold canonFacts
            apply List.filter_congr
            intro f _
            simp [h f]
        _ = l₂ := c₂
    subst hl
    rfl

end -- public section

end Strata.Pipeline
