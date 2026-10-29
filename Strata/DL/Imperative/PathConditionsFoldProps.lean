/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Strata.DL.Imperative.EvalContext
import Strata.DL.Imperative.EvalContextProps
import all Strata.DL.Imperative.PathConditionsFold
public import Strata.DL.Imperative.PathConditionsFold
import Strata.Util.ExceptProps

/-!
# Faithfulness of the incremental `PathConditions` fold

Fix a fold `f`. The *reference fold* `Fold.reference f initial target`
starts from a fresh state at checkpoint `initial` and pushes each
`PathCondition` of `target` in turn, oldest first (`pushPathCondition`),
never reusing prior work. The main theorem,
`Fold.advance_eq_reference`, states that for any state `st` satisfying the
invariant `st.RefFaithful f initial`,

    (f.advance target).exec st = Fold.reference f initial target

Hence the result of `advance` does not depend on the sequence of `advance`
calls that produced `st`: the incremental fold removes only the work of
re-running `stepEntry` on shared prefixes, never changing the outcome.

Key results:

- `MatchSpec` — correctness of a `ReusePlan`: the target decomposes, as an
  equation on lists, into the part the plan keeps and the part it processes
  anew.
- `computeReusePlanGo_spec` — the plan the engine computes satisfies
  `MatchSpec`.
- `FoldState.RefFaithful` — the invariant. It is parameterized by the
  checkpoint `initial` the run started from (the state does not store it),
  and says: for every `k`, reference-folding the first `k` `PathCondition`s
  recorded by `st`'s frames from `initial` succeeds and yields
  `st.keepFrames k`.
- `applyReusePlan_eq_reference` — applying *any* `MatchSpec`-satisfying plan
  equals the reference fold.
- `Fold.advance_eq_reference` — the theorem above, the composition of the
  previous two; `refFaithful_init` and `Fold.reference_refFaithful`
  establish and preserve the invariant across a run of `advance` calls.
-/

namespace Imperative
open Std (ToFormat Format format)

namespace PathConditions

public section

variable {E σ ω : Type} {P : PureExpr}
variable [DecidableEq P.Ident] [DecidableEq P.Ty] [DecidableEq P.Expr]

/-- When `stripPathConditionPrefix ys xs` returns `some rest`, then
    `xs = ys.toList ++ rest`: the matched `PathConditionEntry`s are *equal*,
    to the corresponding prefix of `xs`. -/
private theorem stripPathConditionPrefix_eq {ys : Array (PathConditionEntry P)}
    {xs rest : PathCondition P}
    (h : stripPathConditionPrefix ys xs = some rest) :
    xs = ys.toList ++ rest := by
  unfold stripPathConditionPrefix at h
  generalize ys.toList = ysl at h ⊢
  induction ysl generalizing xs rest with
  | nil =>
    simp only [stripPathConditionPrefixGo, Option.some.injEq] at h
    rw [List.nil_append, h]
  | cons y ytl ih =>
    cases xs with
    | nil => simp [stripPathConditionPrefixGo] at h
    | cons x xtl =>
      rw [stripPathConditionPrefixGo] at h
      split at h
      · next heq =>
        -- The heads matched (`fastEq_eq`), and the tails match inductively.
        have htail : xtl = ytl ++ rest := ih h
        rw [List.cons_append, ← PathConditionEntry.fastEq_eq heq, htail]
      · simp at h

/-! ## `computeReusePlanGo` characterization

A `ReusePlan` splits the target into a kept part and a part to process anew.
`computeReusePlanGo_spec` states, as an equation on lists, that the kept
part is exactly what the kept frames recorded. So the frames' saved results
are the results *for* that part of the target, and reusing them is sound. -/

/-- Correctness of a `ReusePlan` for a given pair of processed and target
    `PathConditions`: the two shapes a sound `plan` can take, as equations on
    the target `nextPathConds`, where `originalPathConds` lists the frames'
    recorded `PathConditionEntry`s (oldest frame first).
    `computeReusePlanGo_spec` shows the plan the engine computes satisfies
    this predicate; `applyReusePlan_eq_reference` shows applying any plan
    that satisfies it is faithful. The shapes:

    * *extension* (`plan.keep = originalPathConds.length`) —
      `nextPathConds` is `originalPathConds` with its last `PathCondition`
      extended by `plan.topDelta`, followed by `plan.newPathConditions`;
    * *rewind* (`plan.topDelta = []`) — `nextPathConds` is the first
      `plan.keep` elements of `originalPathConds` followed by
      `plan.newPathConditions`.

    In both shapes the kept part of `nextPathConds` *equals* the
    corresponding recorded entries. -/
abbrev MatchSpec (originalPathConds : List (Array (PathConditionEntry P)))
    (nextPathConds : PathConditions P) (plan : ReusePlan P) : Prop :=
  (∃ init top, originalPathConds = init ++ [top] ∧
     plan.keep = originalPathConds.length ∧
     nextPathConds = init.map (·.toList)
       ++ ((top.toList ++ plan.topDelta) :: plan.newPathConditions))
  ∨
  (plan.topDelta = [] ∧ plan.keep ≤ originalPathConds.length ∧
     nextPathConds = ((originalPathConds.take plan.keep).map (·.toList))
       ++ plan.newPathConditions)

omit [DecidableEq P.Ident] [DecidableEq P.Ty] [DecidableEq P.Expr] in
/-- The starting plan (`keep = 0`): nothing is shared, so the whole target is
    the fresh `newPathConditions` (here `nextPathConds` itself). Closes every
    leaf where `computeReusePlanGo` bottoms out without matching a
    `PathCondition`. -/
private theorem matchSpec_rewindStart
    (originalPathConds : List (Array (PathConditionEntry P)))
    (nextPathConds : PathConditions P) :
    MatchSpec originalPathConds nextPathConds ⟨0, [], nextPathConds⟩ := by
  have hts : nextPathConds
      = ((originalPathConds.take 0).map (·.toList)) ++ nextPathConds := by
    simp only [List.take_zero, List.map_nil, List.nil_append]
  exact .inr ⟨rfl, Nat.zero_le _, hts⟩

omit [DecidableEq P.Ident] [DecidableEq P.Ty] [DecidableEq P.Expr] in
/-- Prepend a fully-matched `PathCondition`: if `t = w0.toList` and
    `wrest`/`trest` already decompose per `MatchSpec`, then so do
    `w0 :: wrest` / `t :: trest`, with the kept-frame count raised by one.
    This is the recursion step. -/
private theorem matchSpec_prepend
    {w0 : Array (PathConditionEntry P)}
    {wrest : List (Array (PathConditionEntry P))}
    {t : PathCondition P} {trest : PathConditions P}
    {plan : ReusePlan P}
    (ht : t = w0.toList)
    (hspec : MatchSpec wrest trest plan) :
    MatchSpec (w0 :: wrest) (t :: trest) { plan with keep := plan.keep + 1 } := by
  rcases hspec with ⟨init, top, hws, hkeep', hts⟩ | ⟨htd', hk, hts⟩
  · -- Prepend the matched PathCondition to the extension decomposition.
    have hws' : w0 :: wrest = (w0 :: init) ++ [top] := by rw [hws]; rfl
    have hkeep'' : plan.keep + 1 = (w0 :: wrest).length := by rw [hkeep', hws]; simp
    have hts' : t :: trest = (w0 :: init).map (·.toList)
        ++ ((top.toList ++ plan.topDelta) :: plan.newPathConditions) := by
      rw [List.map_cons, List.cons_append, ← ht, hts]
    exact .inl ⟨w0 :: init, top, hws', hkeep'', hts'⟩
  · -- Prepend the matched PathCondition to the rewind decomposition.
    have hk' : plan.keep + 1 ≤ (w0 :: wrest).length := by simpa using Nat.succ_le_succ hk
    have hts' : t :: trest
        = (((w0 :: wrest).take (plan.keep + 1)).map (·.toList)) ++ plan.newPathConditions := by
      rw [List.take_succ_cons, List.map_cons, List.cons_append, ← ht, hts]
    exact .inr ⟨htd', hk', hts'⟩

/-- The plan `computeReusePlanGo` computes always fits one of the
    `MatchSpec` shapes: `computeReusePlanGo` is correct. -/
theorem computeReusePlanGo_spec
    (originalPathConds : List (Array (PathConditionEntry P)))
    (nextPathConds : PathConditions P) :
    MatchSpec originalPathConds nextPathConds
      (computeReusePlanGo originalPathConds nextPathConds) := by
  induction originalPathConds generalizing nextPathConds with
  | nil =>
    -- No recorded frames: nothing to share, the whole target is fresh.
    rw [computeReusePlanGo]
    exact matchSpec_rewindStart [] nextPathConds
  | cons w0 wrest ih =>
    cases nextPathConds with
    | nil =>
      -- No target PathConditions: the recorded frames are all deeper; pop them.
      rw [computeReusePlanGo]
      exact matchSpec_rewindStart (w0 :: wrest) []
    | cons t trest =>
      rw [computeReusePlanGo]
      cases hpre : stripPathConditionPrefix w0 t with
      | none =>
        -- Top recorded frame isn't a prefix of the target: diverged here.
        exact matchSpec_rewindStart (w0 :: wrest) (t :: trest)
      | some leftover =>
        simp only
        split
        · -- wrest empty: `w0` is the top frame, `leftover` extends it.
          next hempty =>
          have hnil : wrest = [] := List.isEmpty_iff.mp hempty
          have hws : w0 :: wrest = [] ++ [w0] := by rw [hnil]; rfl
          have hkeep : (1 : Nat) = (w0 :: wrest).length := by rw [hnil]; rfl
          have hts : t :: trest
              = ([] : List (Array (PathConditionEntry P))).map (·.toList)
                ++ ((w0.toList ++ leftover) :: trest) := by
            simp only [List.map_nil, List.nil_append]
            rw [← stripPathConditionPrefix_eq hpre]
          exact .inl ⟨[], w0, hws, hkeep, hts⟩
        · split
          · -- fully-consumed closed frame: recurse, then prepend it.
            next hleft =>
            have hleftover : leftover = [] := List.isEmpty_iff.mp hleft
            have ht : t = w0.toList := by
              rw [stripPathConditionPrefix_eq hpre, hleftover, List.append_nil]
            exact matchSpec_prepend ht (ih trest)
          · -- closed frame partial match: nothing below is reusable.
            exact matchSpec_rewindStart (w0 :: wrest) (t :: trest)

/-! ## `FoldM.exec` toolkit

The fold's operations are `FoldM` actions (`StateT` over `Except`). The
lemmas below re-express `exec` of the monadic combinators as plain `Except`
computations on states, so the proofs that follow can reason equationally
without touching the monad-transformer layer again. All are definitional or
near-definitional. -/

omit [DecidableEq P.Ident] [DecidableEq P.Ty] [DecidableEq P.Expr] in section

/-- `exec` of `pure` returns the state unchanged. -/
private theorem exec_pure (st : FoldState σ ω P) :
    (pure () : FoldM E σ ω P Unit).exec st = .ok st := rfl

/-- `exec` of `modify` applies the function to the state. -/
private theorem exec_modify (f : FoldState σ ω P → FoldState σ ω P)
    (st : FoldState σ ω P) :
    (modify f : FoldM E σ ω P Unit).exec st = .ok (f st) := rfl

/-- `exec` of a `get`-headed action feeds the state to the continuation. -/
private theorem exec_get_bind (f : FoldState σ ω P → FoldM E σ ω P Unit)
    (st : FoldState σ ω P) :
    ((get >>= f : FoldM E σ ω P Unit)).exec st = (f st).exec st := rfl

/-- `exec` distributes over `>>=`: run the first action, then the second
    from its final state. -/
private theorem exec_bind (x : FoldM E σ ω P Unit) (f : Unit → FoldM E σ ω P Unit)
    (st : FoldState σ ω P) :
    (x >>= f).exec st = x.exec st >>= fun st' => (f ()).exec st' := by
  show (StateT.run x st >>= fun p => StateT.run (f p.1) p.2).map (·.2)
      = (StateT.run x st).map (·.2) >>= fun st' => (StateT.run (f ()) st').map (·.2)
  cases StateT.run x st with
  | error e => rfl
  | ok p => obtain ⟨⟨⟩, s⟩ := p; rfl

/-- Success of `exec`, at the level of the underlying `run`. -/
private theorem exec_ok_iff {x : FoldM E σ ω P Unit} {st st' : FoldState σ ω P} :
    x.exec st = .ok st' ↔ StateT.run x st = .ok ((), st') := by
  unfold FoldM.exec
  cases StateT.run x st with
  | error e => simp [Except.map]
  | ok p => obtain ⟨⟨⟩, s⟩ := p; simp [Except.map]

/-- `List.forM` on a cons, as a rewrite (definitional; `List.forM_cons` is
    stated about the `ForM`-class `forM`, not `List.forM`). -/
private theorem forM_cons_eq {α : Type} (f : α → FoldM E σ ω P Unit) (a : α)
    (l : List α) :
    (a :: l).forM f = f a >>= fun _ => l.forM f := rfl

/-- `exec` of `forM` over an appended list splits at the seam. -/
private theorem exec_forM_append {α : Type} (f : α → FoldM E σ ω P Unit)
    (as bs : List α) (st : FoldState σ ω P) :
    ((as ++ bs).forM f).exec st = (as.forM f).exec st >>= (bs.forM f).exec := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih =>
    rw [List.cons_append, forM_cons_eq, forM_cons_eq]
    simp only [exec_bind]
    cases (f a).exec st with
    | error e => rfl
    | ok st1 => exact ih st1

/-- `exec` of `forM` over a singleton is `exec` of the single action. -/
private theorem exec_forM_singleton {α : Type} (f : α → FoldM E σ ω P Unit)
    (a : α) (st : FoldState σ ω P) :
    ([a].forM f).exec st = (f a).exec st := by
  rw [forM_cons_eq]
  simp only [exec_bind]
  cases (f a).exec st with
  | error e => rfl
  | ok st1 => rfl

/-- The state `pushEmptyFrame` produces. -/
private theorem exec_pushEmptyFrame (f : Fold E σ ω P) (st : FoldState σ ω P) :
    f.pushEmptyFrame.exec st = .ok { st with frames :=
      { entries := #[], baseCheckpoint := st.current,
        output := f.emptyOutput } :: st.frames } := rfl

end

/-! ## The reference fold and pass faithfulness -/

/-- The reference fold: process `target` from a fresh state at checkpoint
    `initial`, running `pushPathCondition` on each `PathCondition`, oldest
    first. -/
def Fold.reference (f : Fold E σ ω P) (initial : σ)
    (target : PathConditions P) :
    Except E (FoldState σ ω P) :=
  (target.forM f.pushPathCondition).exec { current := initial }

omit [DecidableEq P.Ident] [DecidableEq P.Ty] [DecidableEq P.Expr] in section

/-- The `PathConditions` value recorded by the state's frames: each frame's
    `entries` as a `PathCondition`, oldest frame first. -/
def FoldState.recordedPathConditions (st : FoldState σ ω P) : PathConditions P :=
  st.frames.reverse.map (·.entries.toList)

/-- The invariant relating a state to the reference fold, parameterized by
    the checkpoint `initial` the run started from (the state does not store
    it): for every `k`, reference-folding the first `k` of
    `st.recordedPathConditions` from `initial` succeeds and yields
    `st.keepFrames k`. In particular (`k = st.frames.length`) the state
    itself is a reference-fold result of what its frames record. -/
def FoldState.RefFaithful (f : Fold E σ ω P) (initial : σ)
    (st : FoldState σ ω P) : Prop :=
  ∀ k, Fold.reference f initial (st.recordedPathConditions.take k)
    = .ok (st.keepFrames k)

/-- Fold decomposition: the reference fold of `as ++ bs` is the reference
    fold of `as`, then the `bs` fold run from its result. -/
private theorem Fold.reference_append (f : Fold E σ ω P) (initial : σ)
    (as bs : PathConditions P) :
    Fold.reference f initial (as ++ bs) =
      Fold.reference f initial as >>= (bs.forM f.pushPathCondition).exec := by
  unfold Fold.reference
  exact exec_forM_append f.pushPathCondition as bs _

/-- Entry-level fold decomposition within one `PathCondition`: pushing one
    whose entries are `xs ++ ys` is pushing the `PathCondition` `xs`, then
    folding `ys` (no new frame). -/
private theorem pushPathCondition_append (f : Fold E σ ω P) (st : FoldState σ ω P)
    (xs ys : PathCondition P) :
    (f.pushPathCondition (xs ++ ys)).exec st =
      (f.pushPathCondition xs).exec st >>= (ys.forM f.appendEntry).exec := by
  unfold Fold.pushPathCondition
  simp only [exec_bind, exec_pushEmptyFrame, Except.ok_bind, exec_forM_append]

/-! ### Bookkeeping lemmas -/

private theorem length_recordedPathConditions (st : FoldState σ ω P) :
    st.recordedPathConditions.length = st.frames.length := by
  simp only [FoldState.recordedPathConditions, List.length_map, List.length_reverse]

private theorem recordedPathConditions_eq_map (st : FoldState σ ω P) :
    st.recordedPathConditions = (st.frames.reverse.map (·.entries)).map (·.toList) := by
  simp only [FoldState.recordedPathConditions, List.map_map]
  rfl

/-- Peeling one pop off `popFrames`. -/
private theorem popFrames_succ (st : FoldState σ ω P) (n : Nat) :
    st.popFrames (n + 1) = st.popFrame.popFrames n := rfl

/-- `keepFrames k` is the identity when `k ≥ st.frames.length`. -/
private theorem keepFrames_of_le {st : FoldState σ ω P} {k : Nat}
    (h : st.frames.length ≤ k) :
    st.keepFrames k = st := by
  simp only [FoldState.keepFrames, Nat.sub_eq_zero_of_le h, FoldState.popFrames]

/-- If `st'` is `st` with one frame pushed on top (a frame whose
    `baseCheckpoint` is `st.current`), then `keepFrames k` agrees on both
    states for every `k ≤ st.frames.length`. -/
private theorem keepFrames_cons {st st' : FoldState σ ω P}
    {f : PathConditionFrame σ ω P} {k : Nat}
    (hbase : f.baseCheckpoint = st.current)
    (hframes : st'.frames = f :: st.frames) (hk : k ≤ st.frames.length) :
    st'.keepFrames k = st.keepFrames k := by
  -- Popping the pushed frame recovers `st`: its `baseCheckpoint` is the old
  -- `current`, and `FoldState` has no other fields.
  obtain ⟨c', fr'⟩ := st'
  obtain rfl : fr' = f :: st.frames := hframes
  have hpop : (FoldState.mk c' (f :: st.frames)).popFrame = st := by
    show ({ current := f.baseCheckpoint, frames := st.frames } : FoldState σ ω P) = st
    rw [hbase]
  -- `st'` has one extra frame, so its truncation is one extra pop — the one
  -- that lands on `st`.
  have hlen : (FoldState.mk c' (f :: st.frames)).frames.length - k
      = (st.frames.length - k) + 1 := by
    show (f :: st.frames).length - k = (st.frames.length - k) + 1
    simp only [List.length_cons]
    omega
  show (FoldState.mk c' (f :: st.frames)).popFrames
      ((FoldState.mk c' (f :: st.frames)).frames.length - k) = st.keepFrames k
  rw [hlen, popFrames_succ, hpop]
  rfl

/-! ### Shape of successful fold steps -/

/-- If `appendEntry` succeeds on a state whose top frame is `top`, the
    result differs from the input only in `current` and in the top frame,
    which gains the entry in `entries` and a new `output`. In particular
    `top.baseCheckpoint` and the frames below `top` are unchanged. -/
private theorem appendEntry_shape (f : Fold E σ ω P)
    {st st' : FoldState σ ω P} {e : PathConditionEntry P}
    {top : PathConditionFrame σ ω P} {rest : List (PathConditionFrame σ ω P)}
    (hs : st.frames = top :: rest)
    (h : (f.appendEntry e).exec st = .ok st') :
    ∃ live out,
      st' = { current := live,
              frames := ({ entries := top.entries.push e,
                           baseCheckpoint := top.baseCheckpoint,
                           output := out } : PathConditionFrame σ ω P) :: rest } := by
  rw [exec_ok_iff] at h
  simp only [Fold.appendEntry, StateT.run] at h
  rw [hs] at h
  simp only at h
  obtain ⟨⟨live', out⟩, -, hpack⟩ := (Except.bind_is_ok _ _ _).mp h
  refine ⟨live', out, ?_⟩
  exact (congrArg Prod.snd (Except.ok.inj hpack)).symm

/-- `appendEntry_shape` iterated over a whole `PathCondition` `l`: if the
    fold succeeds on a state whose top frame is `top`, the result's top frame
    holds `top.entries ++ l` and keeps `top.baseCheckpoint`, while the frames
    below `top` are unchanged. -/
private theorem forM_appendEntry_shape (f : Fold E σ ω P)
    {l : PathCondition P} {st st' : FoldState σ ω P}
    {top : PathConditionFrame σ ω P} {rest : List (PathConditionFrame σ ω P)}
    (hs : st.frames = top :: rest)
    (h : (l.forM f.appendEntry).exec st = .ok st') :
    ∃ ent out,
      st'.frames = ({ entries := ent, baseCheckpoint := top.baseCheckpoint,
                      output := out } : PathConditionFrame σ ω P) :: rest ∧
      ent.toList = top.entries.toList ++ l := by
  induction l generalizing st st' top rest with
  | nil =>
    -- No entries folded: the state is unchanged and the top frame is `top`.
    obtain rfl : st = st' := Except.ok.inj h
    have hframes : st.frames =
        ({ entries := top.entries, baseCheckpoint := top.baseCheckpoint,
           output := top.output } : PathConditionFrame σ ω P) :: rest := by
      rw [hs]
    have hent : top.entries.toList
        = top.entries.toList ++ ([] : PathCondition P) := by
      rw [List.append_nil]
    exact ⟨top.entries, top.output, hframes, hent⟩
  | cons e tl ih =>
    rw [forM_cons_eq] at h
    simp only [exec_bind] at h
    obtain ⟨st1, he, h1⟩ := (Except.bind_is_ok _ _ _).mp h
    obtain ⟨live1, out1, hst1⟩ := appendEntry_shape f hs he
    have hs1 : st1.frames =
        ({ entries := top.entries.push e, baseCheckpoint := top.baseCheckpoint,
           output := out1 } : PathConditionFrame σ ω P) :: rest := by
      rw [hst1]
    obtain ⟨ent, out, hframes, hent⟩ := ih hs1 h1
    have hlist : (top.entries.push e).toList ++ tl = top.entries.toList ++ (e :: tl) := by
      rw [Array.toList_push, List.append_assoc, List.singleton_append]
    -- The accumulated entries chain through `st1`'s top frame.
    have hent' : ent.toList = top.entries.toList ++ (e :: tl) := hent.trans hlist
    exact ⟨ent, out, hframes, hent'⟩

/-- A successful `pushPathCondition` leaves the input state's frames intact
    and stacks a single new frame on top, with the input's `current` as its
    `baseCheckpoint` and the pushed `PathCondition` as its `entries`. -/
private theorem pushPathCondition_shape (f : Fold E σ ω P)
    {st st' : FoldState σ ω P} {s : PathCondition P}
    (h : (f.pushPathCondition s).exec st = .ok st') :
    ∃ ent out,
      st'.frames = ({ entries := ent, baseCheckpoint := st.current,
                      output := out } : PathConditionFrame σ ω P) :: st.frames ∧
      ent.toList = s := by
  unfold Fold.pushPathCondition at h
  simp only [exec_bind, exec_pushEmptyFrame, Except.ok_bind] at h
  -- `h` now folds `s` into the state with the fresh empty frame on top.
  obtain ⟨ent, out, hframes, hent⟩ := forM_appendEntry_shape f rfl h
  exact ⟨ent, out, hframes, hent⟩

/-! ### Faithfulness -/

/-- `FoldState.init s` satisfies `RefFaithful`: it records no
    `PathCondition`s, and the reference fold of `[]` is the initial state
    itself. -/
theorem refFaithful_init (f : Fold E σ ω P) (s : σ) :
    (FoldState.init (ω := ω) (P := P) s).RefFaithful f s := by
  intro k
  show Fold.reference f s (List.take k []) = .ok (FoldState.keepFrames _ k)
  rw [List.take_nil, keepFrames_of_le (Nat.zero_le k)]
  rfl

/-- `RefFaithful` at full depth (`k = st.frames.length`): the state is the
    reference fold of all of `st.recordedPathConditions`. -/
private theorem refFaithful_full (f : Fold E σ ω P)
    {st : FoldState σ ω P} {initial : σ} (hc : st.RefFaithful f initial) :
    Fold.reference f initial st.recordedPathConditions = .ok st := by
  -- Instantiate faithfulness at the full depth...
  have h := hc st.frames.length
  -- ...where the `take` covers all of `recordedPathConditions` and the
  -- truncation is a no-op.
  have htake : st.recordedPathConditions.take st.frames.length = st.recordedPathConditions :=
    List.take_of_length_le (Nat.le_of_eq (length_recordedPathConditions st))
  have hpop : st.keepFrames st.frames.length = st := keepFrames_of_le (Nat.le_refl _)
  rw [htake, hpop] at h
  exact h

/-- `RefFaithful` is preserved by one successful `pushPathCondition` step,
    which appends exactly `[s]` to the recorded `PathConditions`. -/
private theorem pushPathCondition_refFaithful (f : Fold E σ ω P)
    {st st' : FoldState σ ω P} {initial : σ} {s : PathCondition P}
    (hc : st.RefFaithful f initial)
    (h : (f.pushPathCondition s).exec st = .ok st') :
    st'.RefFaithful f initial ∧
      st'.recordedPathConditions = st.recordedPathConditions ++ [s] := by
  obtain ⟨ent, out, hframes, hent⟩ := pushPathCondition_shape f h
  -- The step appends exactly one recorded PathCondition.
  have hrec : st'.recordedPathConditions = st.recordedPathConditions ++ [s] := by
    simp only [FoldState.recordedPathConditions, hframes, List.reverse_cons,
      List.map_append, List.map_cons, List.map_nil]
    rw [hent]
  -- Faithfulness at every depth, split on whether `k` reaches the new frame.
  have hfaithful : st'.RefFaithful f initial := by
    intro k
    rcases Nat.lt_or_ge st.frames.length k with hk | hk
    · -- The new full prefix: fold the old state, then the new PathCondition —
      -- which is the step `h` itself.
      have htake : st'.recordedPathConditions.take k = st.recordedPathConditions ++ [s] := by
        -- `k` covers the whole (grown) record, so the take is everything.
        have hlen : st'.recordedPathConditions.length ≤ k := by
          rw [hrec, List.length_append, length_recordedPathConditions, List.length_cons,
            List.length_nil]
          omega
        rw [← hrec]
        exact List.take_of_length_le hlen
      have hpop : st'.keepFrames k = st' := by
        -- `k` is beyond the new depth, so the truncation is a no-op.
        have hdepth : st'.frames.length ≤ k := by
          rw [hframes, List.length_cons]
          omega
        exact keepFrames_of_le hdepth
      rw [htake, hpop, Fold.reference_append, refFaithful_full f hc]
      show ([s].forM f.pushPathCondition).exec st = .ok st'
      rw [exec_forM_singleton]
      exact h
    · -- A prefix of the old state: unchanged on both sides.
      have htake : st'.recordedPathConditions.take k = st.recordedPathConditions.take k := by
        have hlen : k ≤ st.recordedPathConditions.length := by
          rw [length_recordedPathConditions]
          exact hk
        rw [hrec]
        exact List.take_append_of_le_length hlen
      have hpop : st'.keepFrames k = st.keepFrames k := keepFrames_cons rfl hframes hk
      rw [htake, hpop]
      exact hc k
  exact ⟨hfaithful, hrec⟩

/-- A successful reference fold yields a state satisfying `RefFaithful` (at
    the fold's own starting checkpoint `initial`) that records exactly
    `target`. -/
theorem Fold.reference_refFaithful (f : Fold E σ ω P)
    {initial : σ} {target : PathConditions P}
    {st' : FoldState σ ω P} (h : Fold.reference f initial target = .ok st') :
    st'.RefFaithful f initial ∧ st'.recordedPathConditions = target := by
  obtain ⟨rev, rfl⟩ : ∃ rev : PathConditions P, rev.reverse = target :=
    ⟨target.reverse, List.reverse_reverse target⟩
  induction rev generalizing st' with
  | nil =>
    simp only [List.reverse_nil] at h ⊢
    -- Folding nothing returns the untouched initial state.
    obtain rfl := Except.ok.inj h
    exact ⟨refFaithful_init f initial, rfl⟩
  | cons s a ih =>
    rw [List.reverse_cons] at h ⊢
    rw [Fold.reference_append] at h
    -- The successful fold factors: `a` reference-folds to some `st1`, and
    -- one `pushPathCondition` step takes `st1` to `st'`.
    obtain ⟨st1, ha, hstep⟩ := (Except.bind_is_ok _ _ _).mp h
    rw [exec_forM_singleton] at hstep
    obtain ⟨hc1, hrec1⟩ := ih ha
    obtain ⟨hc', hrec'⟩ := pushPathCondition_refFaithful f hc1 hstep
    -- Chain the records: `st1` records the prefix, and the step appends `[s]`.
    have hrecorded : st'.recordedPathConditions = a.reverse ++ [s] := by
      rw [hrec', hrec1]
    exact ⟨hc', hrecorded⟩

end

/-! ### The faithfulness theorem -/

omit [DecidableEq P.Ident] [DecidableEq P.Ty] [DecidableEq P.Expr] in
/-- The extension shape of `MatchSpec`: `plan.keep` covers every frame and
    `target` extends the recorded `PathConditions` by `plan.topDelta` on the
    last `PathCondition` plus `plan.newPathConditions` after it. Applying the
    plan — folding `plan.topDelta` and `plan.newPathConditions` from `st` —
    equals the reference fold of `target`. -/
private theorem advance_extension (f : Fold E σ ω P)
    {st : FoldState σ ω P} {initial : σ} (hc : st.RefFaithful f initial)
    {target : PathConditions P} {plan : ReusePlan P}
    {init : PathConditions P} {top : PathCondition P}
    (hws : st.recordedPathConditions = init ++ [top])
    (hkeep : plan.keep = st.frames.length)
    (hts : target = init ++ ((top ++ plan.topDelta) :: plan.newPathConditions)) :
    (f.applyReusePlan plan).exec st = Fold.reference f initial target := by
  -- `plan.keep` covers every open frame, so the truncation is a no-op.
  have hpop : st.keepFrames plan.keep = st := keepFrames_of_le (Nat.le_of_eq hkeep.symm)
  -- Peel the recorded prefix off the reference fold.
  have hsplit : Fold.reference f initial (init ++ [top]) = .ok st := by
    rw [← hws]; exact refFaithful_full f hc
  rw [Fold.reference_append] at hsplit
  -- The successful prefix fold factors (bind inversion): `init` folds to
  -- some `st1`, and the top PathCondition folds `st1` to `st`.
  obtain ⟨st1, hinit, htop⟩ := (Except.bind_is_ok _ _ _).mp hsplit
  rw [exec_forM_singleton] at htop
  -- The reference fold retraces the recorded `PathConditions` (landing on
  -- `st`) and then folds `plan.topDelta` and `plan.newPathConditions` —
  -- which is all the incremental side does.
  unfold Fold.applyReusePlan
  rw [hts, Fold.reference_append, hinit]
  simp only [exec_bind, exec_modify, hpop, Except.ok_bind, forM_cons_eq,
    pushPathCondition_append, htop]

omit [DecidableEq P.Ident] [DecidableEq P.Ty] [DecidableEq P.Expr] in
/-- The rewind shape of `MatchSpec`: `target` is the first `plan.keep`
    recorded `PathCondition`s followed by `plan.newPathConditions`.
    `keepFrames plan.keep` equals the reference fold of that prefix (the
    `RefFaithful` hypothesis at `plan.keep`), so applying the plan — folding
    `plan.newPathConditions` from there — equals the reference fold of
    `target`. -/
private theorem advance_rewind (f : Fold E σ ω P)
    {st : FoldState σ ω P} {initial : σ} (hc : st.RefFaithful f initial)
    {target : PathConditions P} {plan : ReusePlan P}
    (htd : plan.topDelta = [])
    (hts : target = st.recordedPathConditions.take plan.keep
      ++ plan.newPathConditions) :
    (f.applyReusePlan plan).exec st = Fold.reference f initial target := by
  unfold Fold.applyReusePlan
  rw [htd, hts, Fold.reference_append, hc plan.keep]
  simp only [exec_bind, exec_modify, Except.ok_bind]
  rfl

omit [DecidableEq P.Ident] [DecidableEq P.Ty] [DecidableEq P.Expr] in
/-- Soundness of `MatchSpec`: applying *any* plan that satisfies the spec
    for the state's recorded entries and the target equals the reference
    fold of the target. Together with `computeReusePlanGo_spec` (the plan the
    engine computes satisfies the spec) this splits the faithfulness theorem
    into a fact about the planner and a fact about plans. -/
theorem applyReusePlan_eq_reference (f : Fold E σ ω P)
    {st : FoldState σ ω P} {initial : σ} (hc : st.RefFaithful f initial)
    {target : PathConditions P} {plan : ReusePlan P}
    (hspec : MatchSpec (st.frames.reverse.map (·.entries)) target plan) :
    (f.applyReusePlan plan).exec st = Fold.reference f initial target := by
  rcases hspec with ⟨init, top, hws, hkeep, hts⟩ | ⟨htd, _, hts⟩
  -- Convert the spec's raw-list facts into `recordedPathConditions`
  -- vocabulary before handing off to the per-shape lemmas.
  · have hws' : st.recordedPathConditions = init.map (·.toList) ++ [top.toList] := by
      rw [recordedPathConditions_eq_map, hws, List.map_append, List.map_cons, List.map_nil]
    have hkeep' : plan.keep = st.frames.length := by
      rw [hkeep, List.length_map, List.length_reverse]
    exact advance_extension f hc hws' hkeep' hts
  · have hts' : target = st.recordedPathConditions.take plan.keep
        ++ plan.newPathConditions := by
      rw [hts, recordedPathConditions_eq_map, List.map_take]
    exact advance_rewind f hc htd hts'

/-- **The faithfulness theorem**: on a state satisfying `RefFaithful f
    initial`, `advance` equals the reference fold of `target` from `initial`,
    so the two sides agree. The result of `advance` therefore does not depend
    on the sequence of `advance` calls that produced `st`. -/
theorem Fold.advance_eq_reference (f : Fold E σ ω P)
    {st : FoldState σ ω P} {initial : σ} (hc : st.RefFaithful f initial)
    (target : PathConditions P) :
    (f.advance target).exec st = Fold.reference f initial target := by
  unfold Fold.advance
  simp only [exec_get_bind]
  unfold FoldState.computeReusePlan
  exact applyReusePlan_eq_reference f hc (computeReusePlanGo_spec _ target)

end -- public section

end PathConditions

end Imperative
