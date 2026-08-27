/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Pipeline.FactSet

/-! # Phase contracts and validated pipelines

The composition check, independent of any language. A phase is anything with a
name and three fact sets (`PhaseContract`); a `ValidatedPipeline` is a list of
them whose contracts line up, indexed by the facts it assumes of the program it
is given.

Nothing here knows what a phase *does*: the transform, the monad it runs in, and
whatever else a language attaches to a phase stay on that language's side. What
is shared is the part worth sharing — threading facts through a phase, deciding
whether a list composes, and explaining why it does not.
-/

namespace Strata.Pipeline

public section

variable {F : Type} [FactVocabulary F] [FactAlgebra F]

/-! ## Sets, derived

The algebra supplies `ofList` and `toList`; everything the check needs follows
from them, so a representation has two operations to implement rather than ten. -/

/-- The facts of a set, in the representation's order. -/
@[expose] def factsOf (σ : FactSet F) : List F := FactAlgebra.toList σ

/-- Build a set from a list. -/
@[expose] def factSetOfList (l : List F) : FactSet F := FactAlgebra.ofList l

instance : Membership F (FactSet F) := ⟨fun σ f => f ∈ factsOf σ⟩

instance (f : F) (σ : FactSet F) : Decidable (f ∈ σ) :=
  inferInstanceAs (Decidable (f ∈ factsOf σ))

/-! The theorem below is stated here rather than with the other theorems about
fact sets, because the decidable-equality instance that follows it is built from
it. A properties module imports its definition module, so a definition cannot
depend on a theorem stated there. -/

/-- Extensionally equal fact sets are *equal*, which is what lets a set index a
    validated pipeline. -/
theorem factSet_ext {σ₁ σ₂ : FactSet F} (h : ∀ f, f ∈ σ₁ ↔ f ∈ σ₂) : σ₁ = σ₂ :=
  FactAlgebra.ext σ₁ σ₂ h

instance (σ₁ σ₂ : FactSet F) : Decidable (σ₁ = σ₂) :=
  decidable_of_iff (∀ f ∈ FactVocabulary.all (F := F), f ∈ σ₁ ↔ f ∈ σ₂)
    ⟨fun h => factSet_ext fun f => h f (FactVocabulary.all_complete f),
     fun h f _ => by subst h; exact Iff.rfl⟩

/-- Nothing is known about the program. -/
@[expose] def emptyFactSet : FactSet F := factSetOfList []

/-- Every fact. The honest `preserves` for a phase that returns the program it
    was given, and the only place a fact set may follow the vocabulary's
    enumeration instead of being written out: a phase that changes nothing
    preserves a new fact the moment the fact exists. -/
@[expose] def allFactSet : FactSet F := factSetOfList (FactVocabulary.all (F := F))

/-- Union: the facts of either set. The representation supplies it, so for the
    canonical list this is one walk of the vocabulary and the two sets. -/
@[expose] def factSetUnion (σ₁ σ₂ : FactSet F) : FactSet F :=
  FactAlgebra.union σ₁ σ₂

/-- Intersection: the facts of both sets, by the same walk as union. -/
@[expose] def factSetInter (σ₁ σ₂ : FactSet F) : FactSet F :=
  FactAlgebra.inter σ₁ σ₂

/-- Inclusion: used by the composition check, where the next phase's `requires`
    must be covered by what the pipeline already guarantees. Decided by
    `FactAlgebra.decSubset`, which for the canonical list is one walk of the two
    sets — see `canon_subset_iff_sublist`.

    It runs once per phase when a pipeline is checked.

    Marked `@[expose]` so the body unfolds in importing modules: an inclusion
    proof has to be applicable as a function. -/
@[expose, reducible] def factSetSubset (σ₁ σ₂ : FactSet F) : Prop :=
  ∀ f ∈ factsOf σ₁, f ∈ σ₂

instance (σ₁ σ₂ : FactSet F) : Decidable (factSetSubset σ₁ σ₂) :=
  FactAlgebra.decSubset σ₁ σ₂

@[inherit_doc] infix:50 " ⊑ " => factSetSubset

/-! ## Threading facts through a phase -/

/-- After a phase runs, the facts it `establishes` together with the facts in
    `σ` that it `preserves`. Anything in neither is dropped. -/
@[expose] def applyPhase (establishes preserves σ : FactSet F) : FactSet F :=
  factSetUnion establishes (factSetInter σ preserves)

/-! ## Contracts -/

/-- What the validator needs of a phase: a name for diagnostics and the three
    fact sets of its contract. One instance per phase type. -/
class PhaseContract (P : Type) (F : Type) [FactVocabulary F] [FactAlgebra F] where
  /-- Canonical name of the phase, used in diagnostics. -/
  name : P → String
  /-- Facts that must hold on the input program for this phase to run. -/
  requires : P → FactSet F
  /-- Facts guaranteed to hold on the output program. -/
  establishes : P → FactSet F
  /-- Facts that, if they held on the input, also hold on the output. -/
  preserves : P → FactSet F

variable {P : Type} [PhaseContract P F]

/-! ## Validated pipelines -/

/-- A pipeline validated to compose correctly, indexed by the facts it expects
    at entry. What it establishes is not a second index but a function of this
    one and the phases, computed by `ValidatedPipeline.establishes`.

    `cons p h rest` runs `p` first and `rest` afterwards: `h` is about the facts
    known on entry, which is why the head is the phase that receives the input
    program and `nil` is the end of the run. -/
inductive ValidatedPipeline (P F : Type) [FactVocabulary F] [FactAlgebra F]
    [PhaseContract P F] : (requires : FactSet F) → Type where
  | nil {requires : FactSet F} : ValidatedPipeline P F requires
  | cons {requires : FactSet F} (p : P) (h : PhaseContract.requires p ⊑ requires)
         (rest : ValidatedPipeline P F
                   (applyPhase (PhaseContract.establishes p) (PhaseContract.preserves p) requires)) :
         ValidatedPipeline P F requires

/-- What the pipeline establishes of the program it produces, given that its own
    `requires` held of the program it was given: the `requires` carried through
    `applyPhase` by every phase in turn.

    The same relation to `requires` that a phase's `establishes` has to its own,
    which is why it takes that name. It is derived rather than declared, so there
    is nowhere to state it wrongly. -/
def ValidatedPipeline.establishes :
    {requires : FactSet F} → ValidatedPipeline P F requires → FactSet F
  | requires, .nil => requires
  | _, .cons _ _ rest => rest.establishes

/-- The phases of this pipeline, in the order they run. -/
def ValidatedPipeline.phases :
    {requires : FactSet F} → ValidatedPipeline P F requires → List P
  | _, .nil => []
  | _, .cons p _ rest => p :: rest.phases

/-! ### Checking a phase list

Pipelines are assembled and checked at runtime. Because `⊑` is decidable,
checking a phase list *produces* the per-phase inclusion proof instead of
demanding one. -/

/-- The facts `needed` asks for that `σ` does not supply. Empty exactly when
    `needed ⊑ σ`. -/
@[expose] def missingFacts (needed σ : FactSet F) : List F :=
  (factsOf needed).filter (· ∉ σ)

/-! #### Tracing a lost fact

A rejection says where the missing fact came from and which phase dropped it, so
the author knows what to reorder. The walked prefix is threaded as
`(position, phase)` pairs together with the caller's entry facts, which is what
those two ends are read off. A fact can enter either way — established by a
phase, or supplied by the caller — so the origin is a phase position or `entry`
at position 0. -/

/-- Where a fact came from and which phase dropped it. `estPos = 0` with
    `estName = "(entry)"` means it came from the caller's entry facts rather than
    from a phase. -/
private structure FactLoss where
  /-- Position of the phase that last established the fact, or `0` for the
      caller's entry facts. -/
  estPos : Nat
  /-- Name of that phase, or `"(entry)"`. -/
  estName : String
  /-- Position of the earliest later phase that dropped the fact. -/
  invPos : Nat
  /-- Name of that phase. -/
  invName : String

/-- Name used for the caller-supplied entry facts in diagnostics. -/
private def entryOrigin : String := "(entry)"

/-- The phase in `history` that most recently established `f`, if any. `history`
    is earliest-first, so a left fold keeps the last match. -/
private def lastEstablisher (history : List (Nat × P)) (f : F) : Option (Nat × String) :=
  history.foldl
    (fun acc e =>
      if f ∈ PhaseContract.establishes (F := F) e.2 then some (e.1, PhaseContract.name (F := F) e.2)
      else acc)
    none

/-- The earliest phase in `history` after position `after` that neither
    establishes nor preserves `f` — the one that dropped it. -/
private def firstInvalidator (history : List (Nat × P)) (after : Nat) (f : F) :
    Option (Nat × String) :=
  (history.find? (fun e =>
      after < e.1 && f ∉ PhaseContract.establishes (F := F) e.2
        && f ∉ PhaseContract.preserves (F := F) e.2)).map
    (fun e => (e.1, PhaseContract.name (F := F) e.2))

/-- Explain a missing fact as "available here, dropped there". `none` when the
    fact was never available in the first place, in which case it is absent
    rather than lost and there is nothing to trace. -/
private def traceLostFact (σ₀ : FactSet F) (history : List (Nat × P)) (f : F) :
    Option FactLoss := do
  let (estPos, estName) ←
    match lastEstablisher history f with
    | some origin => some origin
    | none => if f ∈ σ₀ then some (0, entryOrigin) else none
  let (invPos, invName) ← firstInvalidator history estPos f
  return { estPos, estName, invPos, invName }

/-- A phase *later* in the same list that establishes `f`. An ordering mistake is
    the likeliest reason a fact is missing, so the candidate is drawn from the
    pipeline the caller passed in. -/
private def findEstablisher : Nat → List P → F → Option (Nat × String)
  | _, [], _ => none
  | pos, p :: rest, f =>
    if f ∈ PhaseContract.establishes (F := F) p then some (pos, PhaseContract.name (F := F) p)
    else findEstablisher (pos + 1) rest f

/-- Full diagnostic for a requirement that is unmet: position, who requires it,
    per-fact origin-and-loss trace, what the preceding phases do guarantee, and a
    later-establisher suggestion.

    `anchor` is a name rather than a phase, so the analysis consuming the
    pipeline is reported exactly as a phase is without having to be modelled as
    one. -/
private def requiresDiagnostic (σ₀ : FactSet F) (history : List (Nat × P))
    (pos : Nat) (anchor : String) (needed σ : FactSet F) (rest : List P) : String :=
  let missing := missingFacts needed σ
  let hint (f : F) : String :=
    match findEstablisher (pos + 1) rest f with
    | some (lpos, lname) =>
        s!" — phase #{lpos} `{lname}` later in this pipeline establishes it, " ++
        s!"so it may be ordered too late"
    | none => ""
  let cause (f : F) : String :=
    match traceLostFact σ₀ history f with
    | some t =>
        let origin :=
          if t.estPos == 0 then "guaranteed on entry"
          else s!"guaranteed by phase #{t.estPos} `{t.estName}`"
        s!"{origin} but phase #{t.invPos} `{t.invName}` afterwards does not preserve it"
    | none =>
        if (factsOf σ).isEmpty then "no preceding phase guarantees it"
        else s!"preceding phases only guarantee `{", ".intercalate ((factsOf σ).map factName)}`"
  match missing with
  | [f] =>
    -- Single-fact phrasing: "requires `f` but ..." when the fact was never
    -- available, "requires `f`, <trace>" when it was.
    match traceLostFact σ₀ history f with
    | some _ => s!"phase #{pos} `{anchor}` requires `{factName f}`, {cause f}{hint f}"
    | none   => s!"phase #{pos} `{anchor}` requires `{factName f}` but {cause f}{hint f}"
  | _ =>
    let lines := missing.map (fun f => s!"  • `{factName f}`: {cause f}{hint f}")
    s!"phase #{pos} `{anchor}` requires:\n" ++ "\n".intercalate lines

/-- Worker for `ValidatedPipeline.ofListFrom`. `σ₀` is the caller's entry facts
    and `history` the phases already validated, earliest first, paired with their
    1-based positions; both exist only to make diagnostics explanatory. -/
private def ValidatedPipeline.ofListAux (σ₀ : FactSet F) (σ : FactSet F)
    (history : List (Nat × P)) :
    (phases : List P) → Except String (ValidatedPipeline P F σ)
  | [] => .ok .nil
  | p :: rest =>
    let pos := history.length + 1
    if h : PhaseContract.requires p ⊑ σ then
      match ofListAux σ₀ (applyPhase (PhaseContract.establishes p) (PhaseContract.preserves p) σ)
              (history ++ [(pos, p)]) rest with
      | .ok tail => .ok (.cons p h tail)
      | .error e => .error e
    else
      .error (requiresDiagnostic σ₀ history pos (PhaseContract.name (F := F) p)
                (PhaseContract.requires p) σ rest)

/-- Validate a dynamically assembled phase list against the facts `σ` known to
    hold on entry. On failure, an explanatory diagnostic for the first phase
    whose contract is unmet; positions in diagnostics are 1-based. -/
def ValidatedPipeline.ofListFrom (σ : FactSet F) (phases : List P) :
    Except String (ValidatedPipeline P F σ) :=
  ofListAux σ σ [] phases

/-- Validate a phase list that assumes nothing about its input program. -/
def ValidatedPipeline.ofList (phases : List P) :
    Except String (ValidatedPipeline P F emptyFactSet) :=
  ofListFrom emptyFactSet phases

/-- Validate `phases`, and that what they establish covers what `consumer` needs
    of the program they produce.

    The consumer is not a phase — it hands on no program — so it is not modelled
    as one; it is reported through the same diagnostic, at the position after the
    last phase. -/
def ValidatedPipeline.ofListDelivering (consumer : String) (needed : FactSet F)
    (phases : List P) : Except String (ValidatedPipeline P F emptyFactSet) := do
  let validated ← ofList phases
  let delivered := validated.establishes
  if needed ⊑ delivered then
    .ok validated
  else
    let history := phases.zipIdx.map (fun (p, i) => (i + 1, p))
    .error (requiresDiagnostic emptyFactSet history (phases.length + 1) consumer
              needed delivered [])

end -- public section

end Strata.Pipeline
