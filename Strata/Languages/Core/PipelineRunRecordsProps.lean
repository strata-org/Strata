/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelineRunRecords
import all Strata.Languages.Core.PipelinePhase
import all Strata.Pipeline.Context
import all Init.System.ST
import all Init.System.IO
import Strata.DL.Imperative.Counterexample.Tactics

/-! # The records of a pipeline run

Key theorems:

* `runTransformsWithBackLinks_records` — a successful run of the pipeline phases returns
  the carriers of a list of run records (`RunRecords`: one record per executed phase,
  chained from the input program to the returned one, each a successful run of its phase);
* `runTransformsWithBackLinks_records_phases` — those records follow the phase list: one
  record per phase of the list, in order. -/

namespace Core

public section

/-- A bound computation that succeeds had a successful first step. -/
private theorem eio_bind_ok_inv {ε α β : Type} {x : EIO ε α} {g : α → EIO ε β}
    {w w' : Void IO.RealWorld} {b : β} (h : (x >>= g) w = .ok b w') :
    ∃ a w1, x w = .ok a w1 ∧ g a w1 = .ok b w' := by
  change EST.bind x g w = _ at h
  unfold EST.bind at h
  split at h <;> first | exact ⟨_, _, ‹_›, h⟩ | cases h

/-- Appending a record whose input is the last record's output keeps a record list chained
    (`PhaseRecord.Chained`: each record's input is the previous record's output). -/
private theorem PhaseRecord.Chained.append_single :
    ∀ (rs : List PhaseRecord) (x : PhaseRecord), PhaseRecord.Chained rs →
      (∀ l ∈ rs.getLast?, l.output = x.input) → PhaseRecord.Chained (rs ++ [x])
  := fun
  | [], _, _, _ => trivial
  | [r], x, _, h => ⟨h r rfl, trivial⟩
  | r :: r' :: rs, x, ⟨hhead, htail⟩, h =>
    ⟨hhead, PhaseRecord.Chained.append_single (r' :: rs) x htail (by simpa using h)⟩

/-- A run of `phases` from `p` that has executed no phase, has reached `p` and recorded no
    carrier, is described (`RunRecords`) by the empty record list. -/
private theorem RunRecords.nil (p : Program) (phases : List PipelinePhase) :
    RunRecords p phases p [] [] := ⟨rfl, trivial, nofun, rfl, nofun⟩

/-- If `records` describe a run of `phases` from `p` that has reached `cur` with carriers
    `links` (`RunRecords`), and a phase `pp` of `phases` runs successfully on `cur` producing
    `next` (`PipelinePhase.Produces`), then appending the record of that run and its carrier
    describes the run reaching `next`. -/
private theorem RunRecords.snoc {p : Program} {phases : List PipelinePhase} {cur next : Program}
    {links : List RuntimeBackLink} {records : List PhaseRecord} {pp : PipelinePhase}
    (h : RunRecords p phases cur links records) (hpp : pp ∈ phases)
    (hrun : pp.Produces cur next) :
    RunRecords p phases next (links ++ [(pp.buildBackLink cur next).withPrograms cur next])
      (records ++ [⟨pp, cur, next⟩]) := by
  obtain ⟨hlinks, hchain, hhead, hlast, hall⟩ := h
  refine ⟨by simp [hlinks, PhaseRecord.link],
    PhaseRecord.Chained.append_single _ _ hchain fun l hl => ?_, ?_, by simp, ?_⟩
  · simp [← hlast, Option.mem_def.1 hl]
  · cases records <;> grind
  · grind

/-- An invariant of a `for` loop in `EIO`, indexed by the processed prefix of the list,
    holds of the loop's result for the whole list when every successful step continues
    and extends it by the processed element. -/
private theorem eio_forIn_prefix {ε α β : Type} (f : α → β → EIO ε (ForInStep β))
    (I : List α → β → Prop) :
    ∀ (l pre : List α), (∀ a ∈ l, ∀ pre b w b' w', I pre b → f a b w = .ok b' w' →
      ∃ v, b' = .yield v ∧ I (pre ++ [a]) v) →
      ∀ b w r w', I pre b → forIn l b f w = .ok r w' → I (pre ++ l) r
  | [], pre, _, b, w, r, w', hb, h => by
    rw [List.forIn_nil] at h
    cases h
    simpa using hb
  | a :: l, pre, hf, b, w, r, w', hb, h => by
    rw [List.forIn_cons] at h
    obtain ⟨b', w1, hstep, h⟩ := eio_bind_ok_inv h
    obtain ⟨v, rfl, hv⟩ := hf a (.head _) pre b w b' w1 hb hstep
    simpa using eio_forIn_prefix f I l (pre ++ [a]) (fun c hc => hf c (.tail _ hc)) v w1 r w' hv h

/-- A successful run of a phase's transform is a run of the phase (`PipelinePhase.Produces`). -/
private theorem PipelinePhase.produces_of_run {pp : PipelinePhase} {p p' : Program}
    {s s' : Transform.CoreTransformState} {c : Bool}
    (h : StateT.run (pp.transform p) s = (.ok (c, p'), s')) : pp.Produces p p' :=
  ⟨s, s', by
    simp only [Transform.runWith, StateT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      StateT.bind] at h ⊢
    rw [h]; rfl⟩

/-- **The records of a run follow the phase list.**  A successful
    `runTransformsWithBackLinks` run of `phases` on `p`, returning `pk` and the carriers
    `links`, has records (`RunRecords`: one record per executed phase, chained from `p` to
    `pk`, each a successful run of its phase, whose links are `links`) with exactly one
    record per phase of `phases`, in order. -/
theorem runTransformsWithBackLinks_records_phases (p : Program) (phases : List PipelinePhase)
    (s0 : Transform.CoreTransformState) (ctx : Option Strata.Pipeline.PipelineContext)
    (pfx : Option String) (w w' : Void IO.RealWorld)
    (pk : Program) (st : Transform.CoreTransformState) (links : List RuntimeBackLink)
    (h : runTransformsWithBackLinks p phases s0 ctx pfx w = .ok (pk, st, links) w') :
    ∃ records, RunRecords p phases pk links records ∧ records.map (·.phase) = phases := by
  unfold runTransformsWithBackLinks runTransformsRecording at h
  cases ctx <;> cases pfx <;> simp only [Transform.runWith, Nat.toString_eq_repr, ite_true] at h
  all_goals
    obtain ⟨⟨_, _, _, _⟩, _, h, hpure⟩ := eio_bind_ok_inv h
    cases hpure
  all_goals try
    generalize System.FilePath.parent _ = parent at h
    cases parent <;> simp only at h
    rotate_left
    obtain ⟨_, _, -, h⟩ := eio_bind_ok_inv h
  all_goals
    obtain ⟨⟨_, _, _, _, _, _⟩, _, h, hinit⟩ := eio_bind_ok_inv h
    cases hinit
    have := eio_forIn_prefix _ (fun pre b => ∃ e, RunRecords p phases b.1 b.2.2.1 e ∧
      e.map (·.phase) = pre.map Prod.fst) phases.zipIdx [] ?_ _ _ _ _ ⟨_, .nil _ _, rfl⟩ h
    · obtain ⟨e, he, hm⟩ := this
      exact ⟨e, he, by simpa using hm⟩
    intro x hmem pre b w b' w' ⟨records, hrec, hpre⟩ hstep
    have hmem' := List.fst_mem_of_mem_zipIdx hmem
    split at hstep <;> obtain ⟨⟨_ | ⟨_, _⟩, _⟩, _, hres, hstep⟩ := eio_bind_ok_inv hstep <;>
      injection hres with hres <;>
      (try obtain ⟨_, _, hstep0, hstep⟩ := eio_bind_ok_inv hstep) <;> cases hstep
    all_goals first
      | exact ⟨_, rfl, _, hrec.snoc hmem' (PipelinePhase.produces_of_run hres), by simp [hpre]⟩
      | cases hstep0

/-- A successful `runTransformsWithBackLinks` run of `phases` on `p`, for any telemetry
    context and file prefix, returns one carrier per executed phase: those of a chained list of
    records from `p` to the returned program, each a successful run of one of `phases`
    (`RunRecords`). -/
theorem runTransformsWithBackLinks_records (p : Program) (phases : List PipelinePhase)
    (s0 : Transform.CoreTransformState) (ctx : Option Strata.Pipeline.PipelineContext)
    (pfx : Option String) (w w' : Void IO.RealWorld)
    (pk : Program) (st : Transform.CoreTransformState) (links : List RuntimeBackLink)
    (h : runTransformsWithBackLinks p phases s0 ctx pfx w = .ok (pk, st, links) w') :
    ∃ records, RunRecords p phases pk links records :=
  let ⟨records, h, _⟩ := runTransformsWithBackLinks_records_phases p phases s0 ctx pfx w w' pk st
    links h
  ⟨records, h⟩

end -- public section

end Core
