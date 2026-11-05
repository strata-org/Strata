/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.CoreProgram
public import Strata.Languages.Core.Factory
import Strata.Util.ExceptProps

/-! # Properties of the declaration phase

A successful run of the declaration phase has the obligation unit of an obligation with the
lemma's name for every lemma of its input (`declObligationsProgramWith_lemma`), so every lemma
of a program keeps its obligation through the declaration phase. -/

namespace Core
namespace WP

open Imperative Imperative.WP

public section

/-- The obligation the lemma map of `declObligationsProgramWith` holds for a label is an
    obligation of the list with that label. -/
private theorem lemmaMap_mem :
    ∀ (obs : List (Imperative.ProofObligation Expression)) (k : String)
      (ob : Imperative.ProofObligation Expression),
      (obs.foldr (fun ob (m : Std.HashMap String (Imperative.ProofObligation Expression)) =>
        m.insert ob.label ob) {})[k]? = some ob → ob ∈ obs ∧ ob.label = k
  | [], _, _, h => by simp at h
  | o :: obs, k, ob, h => by grind [lemmaMap_mem obs k ob]

/-- A successful run of `declObligationsProgramWith`: the output has the obligation unit of an
    obligation of `lemmaObls` with the lemma's name for every lemma of `program`. -/
private theorem declObligationsProgramWith_lemma
    {declProgram program mid : Program} {lemmaObls : List (Imperative.ProofObligation Expression)}
    (h : declObligationsProgramWith declProgram lemmaObls program = .ok mid) :
    ∀ l md, Decl.lemma l md ∈ program.decls →
      ∃ ob ∈ lemmaObls, ob.label = l.name ∧ lemmaUnit l.name ob ∈ mid.decls := by
  obtain ⟨decls, hf, h⟩ := (Except.bind_is_ok _ _ _).1 h
  dsimp only at h
  split at h <;> cases h
  refine (?_ : (∀ x ∈ ([] : List Decl), x ∈ decls) ∧ _).2
  generalize ([] : List Decl) = acc, program.decls = l at hf ⊢
  induction l generalizing acc with
  | nil => exact ⟨fun _ h => Except.ok.inj hf ▸ h, by simp⟩
  | cons d l ih =>
    obtain ⟨acc', hd, hf⟩ := (Except.bind_is_ok _ _ _).1 hf
    have ih' := ih acc' hf
    cases d <;> grind [Except.bind_is_ok, Except.pure_is_ok, Except.throw_is_ok, lemmaMap_mem]

end -- public section
end WP
end Core
