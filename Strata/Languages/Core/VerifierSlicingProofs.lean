/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.Languages.Core.Verifier
import all Strata.Languages.Core.DefinitionSlicing
import all Strata.DL.Imperative.PathConditionsFold
import all Strata.DL.Imperative.PathConditionsFoldProps
import Strata.DL.Imperative.PathConditionHolds
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.Languages.Core.ObligationExtractionProps
import Strata.Transform.Passive.CoreTyped

/-!
# Per-obligation definition slicing

The discharge leaves out of each obligation's SMT query the definitions of its path condition
that `unreadDefinitions` names (`dischargeObligations`), computing what the path conditions read
with the incremental fold `readFold`. This file proves that the slicing is exact at the level of
the path-condition predicate `Imperative.PathConditions.Holds`: no kept term reads a left-out
definition, and a counterexample of the sliced obligation extends to one of the whole
obligation.

- `Core.unreadDefinitions_closed` — the goal and every kept entry read no unread name
- `Core.readFold_advance_current` — the incremental fold computes `readStateOf`
- `Core.holds_extendDefinitions` — a store where the kept entries hold extends to one where all
  entries hold, changing only the dropped variables
- `Core.sliced_counterexample_extends` — the two combined for `unreadDefinitions`
- `Core.sliced_counterexample_extends_of_ordered` — the same for an obligation whose definitions
  are declared before use (`ObligationExtraction.DefsOrdered`), which gives the premises on the
  order and the distinctness of the unread definitions
- `Core.extracted_sliced_counterexample_extends` — the same for an obligation `extractObligations`
  returns from def-use well formed statement lists
  (`ObligationExtraction.extractObligations_defsOrdered`)
- `Core.sliced_counterexample_extends_of_typed` — the same for an obligation whose definitions
  are declared before use and typed (`ObligationExtraction.DefsTyped`), in a store satisfying the
  typed-model premise `Core.ModelTyped`, without the premise that each unread right-hand side
  evaluates

The premise that each unread right-hand side evaluates constrains the store, which is any store
where the kept entries hold; it does not hold of every such store (`init x : int := p + 1` with
`p` unbound). `Core.ModelTyped` replaces it by what an SMT model provides: each variable an unread
right-hand side reads, other than an unread one, holds a value of its annotated type. That the
encoder and the solver provide it is trusted.

One step stays trusted. On the captured-file path the solver does not read an encoding of the
sliced obligation: the emitter cuts, out of the declarations captured for the shared
path-condition frames, the `define-fun` command of each unread variable (at the byte ranges
`CapturedFrame.defSpans` records; `CapturedFrame.declPiecesWithout`), and
`EmitterState.emitObligation` assembles the file. Assumed, not proved: the assembled file states
the same SMT problem as the file `Strata.SMT.Encoder.encodeCore` writes on the path without a
captured file, from the encoded terms of the entries the slicing keeps
(`EncodeResult.Assembly.ofFramesKept`), that is, of the sliced obligation
`ProofObligation.withoutDefinitions obligation unread`.

Key definitions: `Core.keptEntry`, `Core.droppedDefinitions`, `Core.extendDefinitions`,
`Core.KeptEntriesHold`, `Core.SlicedCounterexampleExtends`, `Core.ModelTyped`,
`Core.SlicedModel`.
-/

namespace Core
open Imperative Imperative.PathConditions

/-- Appending entries to the fold's top frame moves its checkpoint by `ReadState.step`. -/
private theorem forM_appendEntry_current (xs : PathCondition Expression) :
    ∀ (st st' : FoldState ReadState Unit Expression),
      (xs.forM readFold.appendEntry).exec st = .ok st' →
      st'.current = xs.foldl ReadState.step st.current := by
  induction xs with
  | nil => exact fun _ _ h => (Except.ok.inj h) ▸ rfl
  | cons _ _ ih => exact fun _ _ h => ih _ _ h

/-- Pushing path conditions moves the fold's checkpoint by `ReadState.step` over their entries,
oldest first. -/
private theorem forM_push_current (target : PathConditions Expression) :
    ∀ (st st' : FoldState ReadState Unit Expression),
      (target.forM readFold.pushPathCondition).exec st = .ok st' →
      st'.current = target.flatten.foldl ReadState.step st.current := by
  induction target with
  | nil => exact fun _ _ h => (Except.ok.inj h) ▸ rfl
  | cons pc rest ih =>
    intro st st' h
    rw [forM_cons_eq, exec_bind] at h
    rcases h1 : (readFold.pushPathCondition pc).exec st with e | st1 <;> rw [h1] at h
    · cases h
    rw [ih st1 st' h, List.flatten_cons, List.foldl_append, forM_appendEntry_current pc _ st1 h1]

/-- The names a successful `reachThrough` returns: every name already reached, every name of
`pending`, and, when every reached name's bodies are reached or queued, a set closed under
`bodies`. -/
private theorem reachThrough_spec {bodies : Std.HashMap String (List String)} :
    ∀ {fuel pending reached out}, reachThrough bodies fuel pending reached = some out →
      (∀ x, reached.contains x = true → out.contains x = true) ∧
      (∀ v ∈ pending, out.contains v = true) ∧
      ((∀ k, reached.contains k = true → ∀ v ∈ bodies.getD k [],
          reached.contains v = true ∨ v ∈ pending) →
        ∀ k, out.contains k = true → ∀ v ∈ bodies.getD k [], out.contains v = true) := by
  intro fuel pending reached out h
  fun_induction reachThrough bodies fuel pending reached generalizing out with
  | case1 =>
    cases h
    exact ⟨fun _ h => h, nofun, fun hg k hk v hv => (hg k hk v hv).resolve_right nofun⟩
  | case2 => cases h
  | case3 fuel v pending reached hv ih =>
    obtain ⟨hm, hp, hc⟩ := ih h
    refine ⟨hm, fun w hw => (List.mem_cons.1 hw).elim (fun h => h ▸ hm _ hv) (hp w),
      fun hg => hc fun k hk w hw => ?_⟩
    exact (hg k hk w hw).elim .inl fun h => (List.mem_cons.1 h).imp (fun h : w = v => h ▸ hv) id
  | case4 fuel v pending reached hv ih =>
    obtain ⟨hm, hp, hc⟩ := ih h
    have hins : ∀ x, reached.contains x = true → (reached.insert v).contains x = true :=
      fun x hx => by simp [Std.HashSet.contains_insert, hx]
    have hself : (reached.insert v).contains v = true := by simp [Std.HashSet.contains_insert]
    refine ⟨fun x hx => hm x (hins x hx),
      fun w hw => (List.mem_cons.1 hw).elim (fun h => h ▸ hm _ hself)
        (hp w <| List.mem_append_right _ ·),
      fun hg => hc fun k hk w hw => ?_⟩
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hk
    rcases hk with rfl | hk
    · exact .inr (List.mem_append_left _ hw)
    · exact (hg k hk w hw).elim (.inl <| hins w ·) fun h =>
        (List.mem_cons.1 h).imp (fun h : w = v => h ▸ hself) (List.mem_append_right _)

/-- Whether a path-condition entry is a definition (`init x := e`). -/
private def isDefinition : PathConditionEntry Expression → Bool
  | .varDecl _ _ (.det _) => true
  | _ => false

/-- The facts `ReadState.step` maintains about the entries it has processed: the names a
definition's right-hand side reads are among its variable's bodies; and, while no closure has
run out of fuel, the reached names are closed under the bodies and contain every name a
non-definition entry reads. -/
private structure ReadInv (st : ReadState) (entries : List (PathConditionEntry Expression)) :
    Prop where
  bodies : ∀ x ty e, PathConditionEntry.varDecl x ty (.det e) ∈ entries →
    ∀ v ∈ freeVarNames e, v ∈ st.bodies.getD x.name []
  closed : st.complete = true → ∀ k, st.reached.contains k = true →
    ∀ v ∈ st.bodies.getD k [], st.reached.contains v = true
  reads : st.complete = true → ∀ e ∈ entries, isDefinition e = false →
    ∀ v ∈ entryReadNames e, st.reached.contains v = true

/-- `ReadState.reach` keeps the bodies, and when it leaves the state complete, it was
complete before and its reached names are the closure `reachThrough` computes. -/
private theorem ReadState.reach_eq (st : ReadState) (names : List String) :
    (st.reach names).bodies = st.bodies ∧ ((st.reach names).complete = true →
      st.complete = true ∧
        reachThrough st.bodies (names.length + st.size) names st.reached =
          some (st.reach names).reached) := by
  obtain ⟨bodies, size, reached, complete⟩ := st
  simp only [ReadState.reach]
  split <;> simp_all

/-- Reaching names keeps the invariant, and reaches them. -/
private theorem ReadInv.reach {st : ReadState} {es : List (PathConditionEntry Expression)}
    (h : ReadInv st es) (names : List String) :
    ReadInv (st.reach names) es ∧ ((st.reach names).complete = true →
      ∀ v ∈ names, (st.reach names).reached.contains v = true) := by
  obtain ⟨hb, hc⟩ := ReadState.reach_eq st names
  refine ⟨⟨fun x ty e he v hv => hb ▸ h.bodies x ty e he v hv, fun hcomp => ?_,
    fun hcomp e he hd v hv => (reachThrough_spec (hc hcomp).2).1 _
      (h.reads (hc hcomp).1 e he hd v hv)⟩, fun hcomp => (reachThrough_spec (hc hcomp).2).2.1⟩
  obtain ⟨hcomp0, hr⟩ := hc hcomp
  rw [hb]
  exact (reachThrough_spec hr).2.2 fun k hk v hv => .inl (h.closed hcomp0 k hk v hv)

/-- One step of `ReadState.step` keeps the invariant. -/
private theorem ReadInv.step {st : ReadState} {es : List (PathConditionEntry Expression)}
    (h : ReadInv st es) (e : PathConditionEntry Expression) : ReadInv (st.step e) (es ++ [e]) := by
  have hnd : ∀ (st' : ReadState), ReadInv st' es → isDefinition e = false →
      (st'.complete = true → ∀ v ∈ entryReadNames e, st'.reached.contains v = true) →
      ReadInv st' (es ++ [e]) := fun st' h' hd hr =>
    ⟨fun x ty e' he' => (List.mem_append.1 he').elim (h'.bodies x ty e') fun h =>
      absurd (List.mem_singleton.1 h ▸ hd) nofun, h'.closed,
      fun hc e' he' hd' => (List.mem_append.1 he').elim (h'.reads hc e' · hd') fun h =>
        List.mem_singleton.1 h ▸ hr hc⟩
  match e with
  | .assumption .. | .distinct .. | .varDecl _ _ .nondet =>
    exact hnd _ (h.reach _).1 rfl (h.reach _).2
  | .varDecl x ty (.det rhs) =>
    let st1 : ReadState := { st with
      bodies := st.bodies.insert x.name (freeVarNames rhs ++ st.bodies.getD x.name [])
      size := st.size + (freeVarNames rhs).length }
    have hbodies : ∀ y ty' e',
        PathConditionEntry.varDecl y ty' (.det e') ∈ es ++ [.varDecl x ty (.det rhs)] →
        ∀ v ∈ freeVarNames e', v ∈ st1.bodies.getD y.name [] := fun y ty' e' he v hv => by
      grind [h.bodies y ty' e']
    have hreads : st.complete = true → ∀ e' ∈ es ++ [.varDecl x ty (.det rhs)],
        isDefinition e' = false → ∀ v ∈ entryReadNames e', st.reached.contains v = true :=
      fun hc e' he hd => (List.mem_append.1 he).elim (h.reads hc e' · hd) fun h' => by
        cases List.mem_singleton.1 h'; cases hd
    by_cases hx : st.reached.contains x.name = true
    · rw [show st.step (.varDecl x ty (.det rhs)) = st1.reach (freeVarNames rhs) by
        simp [ReadState.step, st1, hx]]
      obtain ⟨hb, hc⟩ := ReadState.reach_eq st1 (freeVarNames rhs)
      refine ⟨fun y ty' e' he v hv => hb ▸ hbodies y ty' e' he v hv, fun hcomp => ?_,
        fun hcomp e' he hd v hv => (reachThrough_spec (hc hcomp).2).1 _
          (hreads (hc hcomp).1 e' he hd v hv)⟩
      obtain ⟨hcomp0, hr⟩ := hc hcomp
      rw [hb]
      refine (reachThrough_spec hr).2.2 fun k hk w hw => ?_
      grind [h.closed hcomp0 k hk w, h.closed hcomp0 x.name hx w]
    · rw [show st.step (.varDecl x ty (.det rhs)) = st1 by simp [ReadState.step, st1, hx]]
      refine ⟨hbodies, fun hcomp k hk w hw => ?_, hreads⟩
      grind [h.closed hcomp k hk w]

/-- Folding `ReadState.step` over more entries keeps the invariant. -/
private theorem ReadInv.foldl (es : List (PathConditionEntry Expression)) :
    ∀ {st pre}, ReadInv st pre → ReadInv (es.foldl ReadState.step st) (pre ++ es) := by
  induction es with
  | nil => intro st pre h; simpa using h
  | cons e es ih => intro st pre h; simpa using ih (h.step e)

/-- The read state of path conditions satisfies the invariant for their entries. -/
private theorem readInv_readStateOf (pcs : PathConditions Expression) :
    ReadInv (readStateOf pcs) pcs.flatten :=
  ReadInv.foldl pcs.flatten (st := {}) (pre := []) ⟨by simp, by simp, by simp⟩

/-- Whether the slicing keeps the entry `e` when `dropped` names the variables whose
definitions it leaves out: every entry but a definition of such a variable. -/
def keptEntry (dropped : String → Bool) : PathConditionEntry Expression → Bool
  | .varDecl x _ (.det _) => !dropped x.name
  | _ => true

/-- The definitions of `entries` whose variables `dropped` names, in order, each as its variable
and right-hand side. -/
def droppedDefinitions (dropped : String → Bool) (entries : List (PathConditionEntry Expression)) :
    List (Expression.Ident × Expression.Expr) :=
  entries.filterMap fun
    | .varDecl x _ (.det e) => if dropped x.name then some (x, e) else none
    | _ => none

/-- `σ` with the variables of `ds` set in order, each to the value of its right-hand side in the
store the earlier ones produced. -/
def extendDefinitions (F : Expression.Factory) :
    SemanticStore Expression → List (Expression.Ident × Expression.Expr) → SemanticStore Expression
  | σ, [] => σ
  | σ, (x, e) :: ds =>
    extendDefinitions F (fun y => if y = x then Expression.eval F σ e else σ y) ds

/-- `extendDefinitions` leaves every variable outside `ds` unchanged. -/
private theorem extendDefinitions_of_not_mem (F : Expression.Factory) :
    ∀ (ds : List (Expression.Ident × Expression.Expr)) (σ : SemanticStore Expression) y,
      y ∉ ds.map (·.1) → extendDefinitions F σ ds y = σ y
  | [], _, _, _ => rfl
  | (x, e) :: ds, σ, y, hy => by
    simp only [List.map_cons, List.mem_cons, not_or] at hy
    rw [extendDefinitions, extendDefinitions_of_not_mem F ds _ y hy.2,
      ite_eq_right_iff.2 (absurd · hy.1)]

/-- Extending along `ds₁ ++ ds₂` extends along `ds₁`, then along `ds₂`. -/
private theorem extendDefinitions_append (F : Expression.Factory) :
    ∀ (ds₁ ds₂ : List (Expression.Ident × Expression.Expr)) (σ : SemanticStore Expression),
      extendDefinitions F σ (ds₁ ++ ds₂) = extendDefinitions F (extendDefinitions F σ ds₁) ds₂
  | [], _, _ => rfl
  | (_, _) :: ds₁, ds₂, _ => extendDefinitions_append F ds₁ ds₂ _

/-- With distinct variables, the extended store holds, at the `i`-th variable, the value of its
right-hand side in the store the first `i` definitions produce. -/
private theorem extendDefinitions_getElem (F : Expression.Factory)
    (ds : List (Expression.Ident × Expression.Expr)) (σ : SemanticStore Expression)
    (hnd : (ds.map (·.1)).Nodup) (i : Nat) (hi : i < ds.length) :
    extendDefinitions F σ ds ds[i].1 =
      Expression.eval F (extendDefinitions F σ (ds.take i)) ds[i].2 := by
  have hsplit : ds = ds.take i ++ ds[i] :: ds.drop (i + 1) := by simp
  have hnot : ds[i].1 ∉ (ds.drop (i + 1)).map (·.1) := (List.nodup_cons.1 <| List.map_cons ▸
    List.drop_eq_getElem_cons hi ▸ hnd.sublist ((List.drop_sublist i ds).map (·.1))).1
  rw [show extendDefinitions F σ ds = _ from congrArg (extendDefinitions F σ) hsplit,
    extendDefinitions_append, extendDefinitions, extendDefinitions_of_not_mem F _ _ _ hnot,
    ite_eq_left_iff.2 (absurd rfl ·)]

/-- Evaluation in a store agrees with evaluation in `σ` when the two agree on every variable
whose name `dropped` does not name, for an expression that reads no dropped name. -/
private theorem eval_eq_of_reads {F : Expression.Factory} {σ σ' : SemanticStore Expression}
    {dropped : String → Bool} (hag : ∀ y, dropped y.name = false → σ' y = σ y)
    {e : Expression.Expr} (he : ∀ v ∈ freeVarNames e, dropped v = false) :
    Expression.eval F σ' e = Expression.eval F σ e :=
  Lambda.LExpr.denoteEval_congr e fun y ty hy =>
    hag y (he _ (List.mem_map.2 ⟨(y, ty), hy, rfl⟩))

/-- The members of `droppedDefinitions dropped entries`: the definitions of `entries` whose
variables `dropped` names. -/
private theorem mem_droppedDefinitions {dropped : String → Bool}
    {entries : List (PathConditionEntry Expression)} {x : Expression.Ident}
    {rhs : Expression.Expr} :
    (x, rhs) ∈ droppedDefinitions dropped entries ↔
      dropped x.name = true ∧ ∃ ty, PathConditionEntry.varDecl x ty (.det rhs) ∈ entries := by
  simp only [droppedDefinitions, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hf⟩
    rcases e with _ | ⟨x', ty, rhs' | _⟩ | _ <;> simp only [reduceCtorEq,
      Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨hd, rfl, rfl⟩ := hf
    exact ⟨hd, ty, he⟩
  · exact fun ⟨hd, ty, he⟩ => ⟨_, he, by simp [hd]⟩

/-- `mapM` of functions that agree on the list's members. -/
private theorem mapM_congr' {α β : Type _} {f g : α → Option β} :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    simp [List.mapM_cons, h a (by simp), mapM_congr' l fun b hb => h b (by simp [hb])]

/-- `holds_extendDefinitions` for any list `ds` holding exactly the dropped definitions. -/
private theorem holds_extend_of_mem {F : Expression.Factory} {σ : SemanticStore Expression}
    {dropped : String → Bool} {entries : List (PathConditionEntry Expression)}
    {ds : List (Expression.Ident × Expression.Expr)}
    (hmem : ∀ x rhs, (x, rhs) ∈ ds ↔
      dropped x.name = true ∧ ∃ ty, PathConditionEntry.varDecl x ty (.det rhs) ∈ entries)
    (hclosed : ∀ e ∈ entries, keptEntry dropped e = true →
      ∀ v ∈ entryReadNames e, dropped v = false)
    (hnodup : (ds.map (·.1)).Nodup)
    (horder : ∀ i (hi : i < ds.length), ∀ y ty, (y, ty) ∈ (ds[i].2).freeVars →
      dropped y.name = true → ∃ j, ∃ hj : j < i, (ds[j]'(by omega)).1 = y)
    (heval : ∀ i (hi : i < ds.length),
      (Expression.eval F (extendDefinitions F σ (ds.take i)) ds[i].2).isSome)
    (hkept : ∀ e ∈ entries, keptEntry dropped e = true → e.Holds F σ) :
    (∀ y, dropped y.name = false → extendDefinitions F σ ds y = σ y) ∧
    ∀ e ∈ entries, e.Holds F (extendDefinitions F σ ds) := by
  have hag : ∀ ds' : List (Expression.Ident × Expression.Expr),
      (∀ p ∈ ds', dropped p.1.name = true) →
      ∀ y, dropped y.name = false → extendDefinitions F σ ds' y = σ y := fun ds' hd y hy =>
    extendDefinitions_of_not_mem F ds' σ y fun hm => (List.mem_map.1 hm).elim fun p ⟨hp, he⟩ =>
      Bool.false_ne_true (hy.symm.trans (he ▸ hd p hp))
  have hnames : ∀ p ∈ ds, dropped p.1.name = true := fun p hp => ((hmem p.1 p.2).1 hp).1
  have hagree := hag ds hnames
  have hkey := extendDefinitions_getElem F ds σ hnodup
  have hcongr : ∀ i (hi : i < ds.length), Expression.eval F (extendDefinitions F σ ds) ds[i].2 =
      Expression.eval F (extendDefinitions F σ (ds.take i)) ds[i].2 := fun i hi =>
    Lambda.LExpr.denoteEval_congr _ fun y ty hy => by
      cases hd : dropped y.name
      · rw [hagree y hd, hag _ (fun p hp => hnames p (List.mem_of_mem_take hp)) y hd]
      · obtain ⟨j, hj, rfl⟩ := horder i hi y ty hy hd
        have h2 := extendDefinitions_getElem F (ds.take i) σ
          (hnodup.sublist ((List.take_sublist i ds).map _)) j (by rw [List.length_take]; omega)
        simp only [List.getElem_take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hj)] at h2
        rw [hkey j (by omega), h2]
  refine ⟨hagree, fun e he => ?_⟩
  cases hk : keptEntry dropped e
  · rcases e with _ | ⟨x, ty, rhs | _⟩ | _ <;>
      simp only [keptEntry, Bool.not_eq_eq_eq_not, Bool.not_false, Bool.true_eq_false] at hk
    obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 ((hmem x rhs).2 ⟨hk, ty, he⟩)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hie ▸ heval i hi)
    exact ⟨v, (hie ▸ hcongr i hi).trans hv, (hie ▸ hkey i hi).trans hv⟩
  · have hr := hclosed e he hk
    have hh := hkept e he hk
    rcases e with ⟨l, a⟩ | ⟨x, ty, rhs | _⟩ | ⟨l, es⟩ <;>
      simp only [entryReadNames, entryExprs, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] at hr
    · exact (eval_eq_of_reads hagree hr).trans hh
    · exact hh.imp fun v ⟨hv, hx⟩ => ⟨(eval_eq_of_reads hagree hr).trans hv,
        (hagree x (by simpa [keptEntry] using hk)).trans hx⟩
    · trivial
    · exact hh.imp fun vs ⟨hvs, hnd⟩ => ⟨(mapM_congr' es fun e' he' => eval_eq_of_reads hagree
        fun v hv => hr v (List.mem_flatMap.2 ⟨e', he', hv⟩)).trans hvs, hnd⟩

/-- **Slicing keeps counterexamples.** A store where every kept entry holds extends to one
where every entry holds, when no kept entry reads a dropped variable (`unreadDefinitions` gives
this, `unreadDefinitions_closed`), the dropped variables are distinct, each dropped right-hand
side reads only dropped variables defined before it, and each evaluates in the store the earlier
dropped definitions produce. The extension changes only dropped variables. -/
theorem holds_extendDefinitions {F : Expression.Factory} {σ : SemanticStore Expression}
    {dropped : String → Bool} {entries : List (PathConditionEntry Expression)}
    (hclosed : ∀ e ∈ entries, keptEntry dropped e = true →
      ∀ v ∈ entryReadNames e, dropped v = false)
    (hnodup : ((droppedDefinitions dropped entries).map (·.1)).Nodup)
    (horder : ∀ i (hi : i < (droppedDefinitions dropped entries).length),
      ∀ y ty, (y, ty) ∈ ((droppedDefinitions dropped entries)[i].2).freeVars →
        dropped y.name = true →
          ∃ j, ∃ hj : j < i, ((droppedDefinitions dropped entries)[j]'(by omega)).1 = y)
    (heval : ∀ i (hi : i < (droppedDefinitions dropped entries).length),
      (Expression.eval F (extendDefinitions F σ ((droppedDefinitions dropped entries).take i))
        (droppedDefinitions dropped entries)[i].2).isSome)
    (hkept : ∀ e ∈ entries, keptEntry dropped e = true → e.Holds F σ) :
    (∀ y, dropped y.name = false →
      extendDefinitions F σ (droppedDefinitions dropped entries) y = σ y) ∧
    ∀ e ∈ entries, e.Holds F (extendDefinitions F σ (droppedDefinitions dropped entries)) :=
  holds_extend_of_mem (fun _ _ => mem_droppedDefinitions) hclosed hnodup horder heval hkept

/-- The names `unreadStep` collects over a path condition: those collected before, and the
variables of its definitions whose names `kept` does not contain. -/
private theorem foldl_unreadStep_contains (kept : Std.HashSet String) (n : String) :
    ∀ (pc : PathCondition Expression) (acc : Std.HashSet String),
      (pc.foldl (unreadStep kept) acc).contains n = true ↔ acc.contains n = true ∨
        ∃ x ty rhs, PathConditionEntry.varDecl x ty (.det rhs) ∈ pc ∧ x.name = n ∧
          kept.contains n = false
  | [], acc => by simp
  | e :: pc, acc => by
    rw [List.foldl_cons, foldl_unreadStep_contains kept n pc]
    rcases e with _ | ⟨x, ty, rhs | _⟩ | _ <;>
      simp only [unreadStep, List.mem_cons, PathConditionEntry.varDecl.injEq, reduceCtorEq,
        false_or, ExprOrNondet.det.injEq]
    · grind
    all_goals simp

/-- The names `unreadDefinitions`' fold collects over path conditions. -/
private theorem foldl_foldl_unreadStep_contains (kept : Std.HashSet String) (n : String) :
    ∀ (pcs : PathConditions Expression) (acc : Std.HashSet String),
      (pcs.foldl (fun acc pc => pc.foldl (unreadStep kept) acc) acc).contains n = true ↔
        acc.contains n = true ∨ ∃ pc ∈ pcs, ∃ x ty rhs,
          PathConditionEntry.varDecl x ty (.det rhs) ∈ pc ∧ x.name = n ∧ kept.contains n = false
  | [], acc => by simp
  | pc :: pcs, acc => by
    rw [List.foldl_cons, foldl_foldl_unreadStep_contains kept n pcs,
      foldl_unreadStep_contains kept n pc]
    simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

/-- `unreadDefinitions` over a read state that satisfies the invariant for entries including
the obligation's: the goal and every entry the slicing keeps read no unread name. -/
private theorem unreadDefinitions_closed_of_inv {st : ReadState}
    {entries : List (PathConditionEntry Expression)} (hinv : ReadInv st entries)
    {obligation : ProofObligation Expression}
    (hsub : ∀ pc ∈ obligation.assumptions, ∀ e ∈ pc, e ∈ entries) :
    (∀ v ∈ freeVarNames obligation.obligation,
      (unreadDefinitions st obligation).contains v = false) ∧
    ∀ pc ∈ obligation.assumptions, ∀ e ∈ pc,
      keptEntry (unreadDefinitions st obligation).contains e = true →
        ∀ v ∈ entryReadNames e, (unreadDefinitions st obligation).contains v = false := by
  unfold unreadDefinitions
  dsimp only
  split
  · next kept hc hr =>
    obtain ⟨hmono, hroots, hclos⟩ := reachThrough_spec hr
    have hkc := hclos fun k hk v hv => .inl (hinv.closed hc k hk v hv)
    generalize hp : obligation.assumptions.foldl
      (fun acc pc => pc.foldl (unreadStep kept) acc) {} = u
    have hu : ∀ n, u.contains n = true ↔ ∃ pc ∈ obligation.assumptions, ∃ x ty rhs,
        PathConditionEntry.varDecl x ty (.det rhs) ∈ pc ∧ x.name = n ∧
          kept.contains n = false := fun n => by
      simpa [hp] using foldl_foldl_unreadStep_contains kept n obligation.assumptions {}
    have hnk : ∀ n, kept.contains n = true → u.contains n = false := fun n hk => by grind
    refine ⟨fun v hv => hnk v (hroots v hv), fun pc hpc e he hk v hv => ?_⟩
    rcases e with ⟨l, a⟩ | ⟨x, ty, rhs | _⟩ | ⟨l, es⟩
    all_goals try exact hnk v (hmono v (hinv.reads hc _ (hsub pc hpc _ he) rfl v hv))
    have hx : kept.contains x.name = true := by grind [keptEntry]
    simp only [entryReadNames, entryExprs, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] at hv
    exact hnk v (hkc x.name hx v (hinv.bodies x ty rhs (hsub pc hpc _ he) v hv))
  · simp

/-- **No kept term reads an unread definition.** For the read state of an obligation's path
conditions (`readStateOf`, which the discharge's incremental `readFold` computes,
`readFold_advance_current`), the goal and every entry the slicing keeps read no name of
`unreadDefinitions`: every name they read that the path condition defines is kept. -/
theorem unreadDefinitions_closed (obligation : ProofObligation Expression) :
    (∀ v ∈ freeVarNames obligation.obligation,
      (unreadDefinitions (readStateOf obligation.assumptions.reverse) obligation).contains v =
        false) ∧
    ∀ pc ∈ obligation.assumptions, ∀ e ∈ pc,
      keptEntry (unreadDefinitions (readStateOf obligation.assumptions.reverse)
        obligation).contains e = true →
      ∀ v ∈ entryReadNames e,
        (unreadDefinitions (readStateOf obligation.assumptions.reverse) obligation).contains v =
          false :=
  unreadDefinitions_closed_of_inv (readInv_readStateOf _) fun pc hpc _ he =>
    List.mem_flatten.2 ⟨pc, List.mem_reverse.2 hpc, he⟩

/-- **The incremental fold computes the read state.** Advancing `readFold` to path conditions
`target`, from a state satisfying `RefFaithful` (as `FoldState.init` does), gives the read state
`readStateOf target` computes from scratch, in a state that again satisfies `RefFaithful`. So the
read states the discharge threads through an environment's obligations are those of their own
path conditions, whatever prefix the obligations share. -/
theorem readFold_advance_current
    {st st' : Imperative.PathConditions.FoldState ReadState Unit Expression}
    (hc : st.RefFaithful readFold {}) (target : PathConditions Expression)
    (h : (readFold.advance target).exec st = .ok st') :
    st'.current = readStateOf target ∧ st'.RefFaithful readFold {} := by
  rw [Imperative.PathConditions.Fold.advance_eq_reference readFold hc] at h
  exact ⟨forM_push_current target _ _ h,
    (Imperative.PathConditions.Fold.reference_refFaithful readFold h).1⟩

/-- **The kept entries hold**: every entry of `obligation`'s path condition, taken oldest first,
that leaving out the definitions `unreadDefinitions` names keeps (`keptEntry`) holds in `σ`. -/
def KeptEntriesHold (F : Expression.Factory) (σ : SemanticStore Expression)
    (obligation : ProofObligation Expression) : Prop :=
  ∀ e ∈ obligation.assumptions.reverse.flatten,
    keptEntry (unreadDefinitions (readStateOf obligation.assumptions.reverse)
      obligation).contains e = true → e.Holds F σ

/-- **A counterexample of the sliced obligation extends to one of the full obligation**: the
store `σ`, extended by the definitions of `obligation`'s path condition (entries oldest first)
that `unreadDefinitions` names (`extendDefinitions`, `droppedDefinitions`), makes every entry hold
and gives the goal the value it has in `σ`. -/
def SlicedCounterexampleExtends (F : Expression.Factory) (σ : SemanticStore Expression)
    (obligation : ProofObligation Expression) : Prop :=
  (∀ e ∈ obligation.assumptions.reverse.flatten,
    e.Holds F (extendDefinitions F σ (droppedDefinitions (unreadDefinitions
      (readStateOf obligation.assumptions.reverse) obligation).contains
        obligation.assumptions.reverse.flatten))) ∧
  Expression.eval F (extendDefinitions F σ (droppedDefinitions (unreadDefinitions
      (readStateOf obligation.assumptions.reverse) obligation).contains
        obligation.assumptions.reverse.flatten)) obligation.obligation =
    Expression.eval F σ obligation.obligation

/-- **A counterexample of the sliced obligation is one of the full obligation.** Leave out of
an obligation's path condition the definitions `unreadDefinitions` names (its entries taken
oldest first). A store where the kept entries hold extends to one where every entry holds and
the goal has the same value, when the unread variables are distinct, each unread right-hand side
reads only unread variables defined before it, and each evaluates in the store the earlier unread
definitions produce. -/
theorem sliced_counterexample_extends {F : Expression.Factory} {σ : SemanticStore Expression}
    (obligation : ProofObligation Expression)
    (hnodup : ((droppedDefinitions (unreadDefinitions (readStateOf obligation.assumptions.reverse)
      obligation).contains obligation.assumptions.reverse.flatten).map (·.1)).Nodup)
    (horder : ∀ i (hi : i < (droppedDefinitions (unreadDefinitions
        (readStateOf obligation.assumptions.reverse) obligation).contains
          obligation.assumptions.reverse.flatten).length),
      ∀ y ty, (y, ty) ∈ ((droppedDefinitions (unreadDefinitions
          (readStateOf obligation.assumptions.reverse) obligation).contains
            obligation.assumptions.reverse.flatten)[i].2).freeVars →
        (unreadDefinitions (readStateOf obligation.assumptions.reverse) obligation).contains
          y.name = true →
        ∃ j, ∃ hj : j < i, ((droppedDefinitions (unreadDefinitions
          (readStateOf obligation.assumptions.reverse) obligation).contains
            obligation.assumptions.reverse.flatten)[j]'(by omega)).1 = y)
    (heval : ∀ i (hi : i < (droppedDefinitions (unreadDefinitions
        (readStateOf obligation.assumptions.reverse) obligation).contains
          obligation.assumptions.reverse.flatten).length),
      (Expression.eval F (extendDefinitions F σ ((droppedDefinitions (unreadDefinitions
        (readStateOf obligation.assumptions.reverse) obligation).contains
          obligation.assumptions.reverse.flatten).take i))
        (droppedDefinitions (unreadDefinitions (readStateOf obligation.assumptions.reverse)
          obligation).contains obligation.assumptions.reverse.flatten)[i].2).isSome)
    (hkept : KeptEntriesHold F σ obligation) : SlicedCounterexampleExtends F σ obligation := by
  obtain ⟨hgoal, hcl⟩ := unreadDefinitions_closed obligation
  obtain ⟨hag, hall⟩ := holds_extendDefinitions (fun e he => (List.mem_flatten.1 he).elim
    fun pc ⟨hpc, he⟩ => hcl pc (List.mem_reverse.1 hpc) e he) hnodup horder heval hkept
  exact ⟨hall, eval_eq_of_reads hag hgoal⟩


/-- The definitions `droppedDefinitions` leaves out are those of the path condition whose
variables `dropped` names, in order. -/
private theorem droppedDefinitions_eq_filter (dropped : String → Bool)
    (entries : List (PathConditionEntry Expression)) :
    droppedDefinitions dropped entries =
      (ObligationExtraction.definitions entries).filter (dropped ·.1.name) := by
  rw [droppedDefinitions, ObligationExtraction.definitions, List.filter_filterMap]
  refine congrArg (List.filterMap · entries) (funext fun e => ?_)
  rcases e with _ | ⟨x, ty, rhs | _⟩ | _ <;> simp [Option.filter]

/-- Every name of `unreadDefinitions` is the name of a variable an obligation's path condition
defines. -/
private theorem unreadDefinitions_defined {st : ReadState}
    {obligation : ProofObligation Expression} {n : String}
    (h : (unreadDefinitions st obligation).contains n = true) :
    ∃ x ty rhs, PathConditionEntry.varDecl x ty (.det rhs) ∈
      obligation.assumptions.reverse.flatten ∧ x.name = n := by
  unfold unreadDefinitions at h
  dsimp only at h
  split at h
  · next kept _ _ =>
    obtain ⟨pc, hpc, x, ty, rhs, hm, hx, -⟩ := ((foldl_foldl_unreadStep_contains kept n
      obligation.assumptions {}).1 h).resolve_left (by simp)
    exact ⟨x, ty, rhs, List.mem_flatten.2 ⟨pc, List.mem_reverse.2 hpc, hm⟩, hx⟩
  · simp at h

/-- When the definitions of `entries` are declared before use (`DefsOrdered`) and `dropped` names
only variables `entries` defines, the dropped definitions have distinct variables, and each
dropped right-hand side reads only dropped variables defined before it: the premises `hnodup`
and `horder` of `holds_extendDefinitions`. -/
private theorem dropped_ordered {dropped : String → Bool}
    {entries : List (PathConditionEntry Expression)}
    (hord : ObligationExtraction.DefsOrdered (ObligationExtraction.definitions entries))
    (hdef : ∀ n, dropped n = true →
      ∃ x ty rhs, PathConditionEntry.varDecl x ty (.det rhs) ∈ entries ∧ x.name = n) :
    ((droppedDefinitions dropped entries).map (·.1)).Nodup ∧
    ∀ i (hi : i < (droppedDefinitions dropped entries).length),
      ∀ y ty, (y, ty) ∈ ((droppedDefinitions dropped entries)[i].2).freeVars →
        dropped y.name = true →
          ∃ j, ∃ hj : j < i, ((droppedDefinitions dropped entries)[j]'(by omega)).1 = y := by
  have hds : ObligationExtraction.DefsOrdered (droppedDefinitions dropped entries) := by
    rw [droppedDefinitions_eq_filter]
    exact ⟨hord.1.filter _, fun a ha => hord.2 a (List.mem_filter.1 ha).1⟩
  refine ⟨List.pairwise_map.2 (hds.1.imp (·.1)), fun i hi y ty hy hd => ?_⟩
  obtain ⟨x, ty', rhs, hx, hn⟩ := hdef _ hd
  obtain rfl : x = y := match x, y, hn with | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
  obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.1 (mem_droppedDefinitions.2 ⟨hd, ty', hx⟩)
  rcases Nat.lt_trichotomy j i with h | rfl | h
  · exact ⟨j, h, by simp [hje]⟩
  · exact absurd hy (by simpa [hje] using hds.2 _ (List.getElem_mem hj) ty)
  · exact absurd hy (by simpa [hje] using (List.pairwise_iff_getElem.1 hds.1 i j hi hj h).2 ty)

/-- **A counterexample of a sliced obligation with ordered definitions is one of the full
obligation.** `sliced_counterexample_extends` for an obligation whose path condition, its
entries taken oldest first, has its definitions declared before use with distinct variables
(`ObligationExtraction.DefsOrdered`): a store where the entries kept by leaving out the
definitions `unreadDefinitions` names hold extends to one where every entry holds and the goal
has the same value, when each unread right-hand side evaluates in the store the earlier unread
definitions produce. -/
theorem sliced_counterexample_extends_of_ordered {F : Expression.Factory}
    {σ : SemanticStore Expression} (obligation : ProofObligation Expression)
    (hord : ObligationExtraction.DefsOrdered
      (ObligationExtraction.definitions obligation.assumptions.reverse.flatten))
    (heval : ∀ i (hi : i < (droppedDefinitions (unreadDefinitions
        (readStateOf obligation.assumptions.reverse) obligation).contains
          obligation.assumptions.reverse.flatten).length),
      (Expression.eval F (extendDefinitions F σ ((droppedDefinitions (unreadDefinitions
        (readStateOf obligation.assumptions.reverse) obligation).contains
          obligation.assumptions.reverse.flatten).take i))
        (droppedDefinitions (unreadDefinitions (readStateOf obligation.assumptions.reverse)
          obligation).contains obligation.assumptions.reverse.flatten)[i].2).isSome)
    (hkept : KeptEntriesHold F σ obligation) : SlicedCounterexampleExtends F σ obligation := by
  obtain ⟨hnodup, horder⟩ := dropped_ordered hord fun _ hn => unreadDefinitions_defined hn
  exact sliced_counterexample_extends obligation hnodup horder heval hkept

/-- **The typed-model premise.**  The store `σ` binds the variable of every annotated
free-variable occurrence, in the right-hand side of a definition of `entries` whose variable
`dropped` names, to a value of the annotated type, when `dropped` does not name the variable.
For the definitions the slicing leaves out (`dropped` the names `unreadDefinitions` gives), this
is what an SMT model of the sliced obligation provides: the encoder declares each free variable
of the query at its annotated sort, and the solver assigns it a value of that sort.  That the
encoder and the solver provide it is trusted, not proved. -/
def ModelTyped (F : Expression.Factory) (σ : SemanticStore Expression)
    (dropped : String → Bool) (entries : List (PathConditionEntry Expression)) : Prop :=
  ∀ d ∈ droppedDefinitions dropped entries, ∀ y τ, (y, some τ) ∈ Lambda.LExpr.freeVars d.2 →
    dropped y.name = false → ∃ v, σ y = some v ∧ HasVal.valueOfTy F v (.forAll [] τ)

/-- **The model premise of the typed slicing theorems**: the store `σ` satisfies the typed-model
premise `ModelTyped` for the definitions `unreadDefinitions` names, and the entries the slicing
keeps hold in it (`KeptEntriesHold`). -/
def SlicedModel (F : Expression.Factory) (σ : SemanticStore Expression)
    (obligation : ProofObligation Expression) : Prop :=
  ModelTyped F σ (unreadDefinitions (readStateOf obligation.assumptions.reverse)
    obligation).contains obligation.assumptions.reverse.flatten ∧ KeptEntriesHold F σ obligation

/-- With typed definitions `tds` (`ObligationExtraction.DefsTyped`) of dropped, distinct
variables, each right-hand side reading only dropped variables defined before it, and a store
`σ` holding at every other annotated occurrence a value of the annotated type, each right-hand
side of `ds`, the definitions `tds` without their types, evaluates in the store the earlier ones
produce: the premise `heval` of `holds_extendDefinitions`. -/
private theorem dropped_eval_of_typed {F : Expression.Factory} {σ : SemanticStore Expression}
    {dropped : String → Bool} {ds : List (Expression.Ident × Expression.Expr)}
    {tds : List (Expression.Ident × Expression.Ty × Expression.Expr)}
    (hds : ds = tds.map fun d => (d.1, d.2.2)) (hty : ObligationExtraction.DefsTyped tds)
    (hnames : ∀ d ∈ tds, dropped d.1.name = true) (hnodup : (ds.map (·.1)).Nodup)
    (horder : ∀ i (hi : i < ds.length), ∀ y ty, (y, ty) ∈ (ds[i].2).freeVars →
      dropped y.name = true → ∃ j, ∃ hj : j < i, (ds[j]'(by omega)).1 = y)
    (hmodel : ∀ d ∈ ds, ∀ y τ, (y, some τ) ∈ Lambda.LExpr.freeVars d.2 →
      dropped y.name = false → ∃ v, σ y = some v ∧ HasVal.valueOfTy F v (.forAll [] τ)) :
    ∀ i (hi : i < ds.length),
      (Expression.eval F (extendDefinitions F σ (ds.take i)) ds[i].2).isSome := by
  subst hds
  have hkey : ∀ i (hi : i < tds.length), ∃ v, Expression.eval F
      (extendDefinitions F σ ((tds.map fun d => (d.1, d.2.2)).take i)) tds[i].2.2 = some v ∧
      HasVal.valueOfTy F v tds[i].2.1 := by
    refine fun i => Nat.strongRecOn i fun i ih hi => ?_
    refine eval_of_typed F _ (hty.1 _ (List.getElem_mem hi)) fun y τ hy => ?_
    cases hd : dropped y.name
    · rw [extendDefinitions_of_not_mem F _ σ y fun hm => ?_]
      · exact hmodel _ (List.mem_map.2 ⟨_, List.getElem_mem hi, rfl⟩) y τ hy hd
      obtain ⟨_, hp, rfl⟩ := List.mem_map.1 hm
      obtain ⟨d, hd', rfl⟩ := List.mem_map.1 (List.mem_of_mem_take hp)
      simp [hnames d hd'] at hd
    · obtain ⟨j, hj, hjy⟩ := horder i (by simpa using hi) y (some τ) (by simpa using hy) hd
      simp only [List.getElem_map] at hjy
      subst hjy
      have h2 := extendDefinitions_getElem F ((tds.map fun d => (d.1, d.2.2)).take i) σ
        (hnodup.sublist ((List.take_sublist i _).map _)) j
        (by rw [List.length_take, List.length_map]; omega)
      simp only [List.getElem_take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hj),
        List.getElem_map] at h2
      rw [h2]
      obtain ⟨v, hv, hvt⟩ := ih j hj (by omega)
      exact ⟨v, hv, (List.pairwise_iff_getElem.1 hty.2 j i (by omega) hi hj) τ hy ▸ hvt⟩
  exact fun i hi => (hkey i (by simpa using hi)).elim fun v ⟨hv, _⟩ => by
    simpa using congrArg Option.isSome hv

/-- **A counterexample of a sliced obligation with ordered, typed definitions is one of the full
obligation.**  `sliced_counterexample_extends_of_ordered` without its premise on the evaluation of
the unread right-hand sides, for an obligation whose definitions are typed
(`ObligationExtraction.DefsTyped`: every right-hand side typed at its declared type, and every
annotated read of an earlier definition's variable carrying that definition's type), in a store
satisfying the typed-model premise `ModelTyped` where the entries kept by leaving out the
definitions `unreadDefinitions` names hold (`SlicedModel`): it extends to one where every entry
holds and the goal has the same value (`SlicedCounterexampleExtends`). -/
theorem sliced_counterexample_extends_of_typed {F : Expression.Factory}
    {σ : SemanticStore Expression} (obligation : ProofObligation Expression)
    (hord : ObligationExtraction.DefsOrdered
      (ObligationExtraction.definitions obligation.assumptions.reverse.flatten))
    (htyped : ObligationExtraction.DefsTyped
      (ObligationExtraction.typedDefinitions obligation.assumptions.reverse.flatten))
    (hm : SlicedModel F σ obligation) : SlicedCounterexampleExtends F σ obligation := by
  obtain ⟨hnodup, horder⟩ := dropped_ordered hord fun _ hn => unreadDefinitions_defined hn
  refine sliced_counterexample_extends_of_ordered obligation hord
    (dropped_eval_of_typed (tds := (ObligationExtraction.typedDefinitions
      obligation.assumptions.reverse.flatten).filter fun d =>
        (unreadDefinitions (readStateOf obligation.assumptions.reverse) obligation).contains
          d.1.name) ?_ ⟨fun d hd => htyped.1 d (List.mem_filter.1 hd).1, htyped.2.filter _⟩
      (fun d hd => (List.mem_filter.1 hd).2) hnodup horder hm.1) hm.2
  rw [droppedDefinitions_eq_filter, ObligationExtraction.definitions_eq_typedDefinitions,
    List.filter_map]
  rfl

/-- **A counterexample of a sliced extracted obligation is one of the full obligation.**
`sliced_counterexample_extends` for an obligation that `extractObligations p` returns, when the
statement list extraction reads from every procedure of `p` is def-use well formed from some
defined-names predicate (the `defUseOk` field of the initial-environment gate
`Imperative.Logic.BlockInitEnvWF`): the unread definitions are then declared before use with
distinct variables (`ObligationExtraction.extractObligations_defsOrdered`). A store where the
entries kept by leaving out the definitions `unreadDefinitions` names hold extends to one where
every entry holds and the goal has the same value, when each unread right-hand side evaluates in
the store the earlier unread definitions produce. -/
theorem extracted_sliced_counterexample_extends {F : Expression.Factory}
    {σ : SemanticStore Expression} {p : Program} {obs : ProofObligations Expression}
    (hp : ObligationExtraction.extractObligations p = .ok obs)
    (hwf : ∀ q md ss, Decl.proc q md ∈ p.decls →
      ObligationExtraction.procedureStatements p.funcNames q = .ok ss →
        ∃ D df, Imperative.Block.defUseWellFormed D df ss = true)
    (obligation : ProofObligation Expression) (hob : obligation ∈ obs)
    (heval : ∀ i (hi : i < (droppedDefinitions (unreadDefinitions
        (readStateOf obligation.assumptions.reverse) obligation).contains
          obligation.assumptions.reverse.flatten).length),
      (Expression.eval F (extendDefinitions F σ ((droppedDefinitions (unreadDefinitions
        (readStateOf obligation.assumptions.reverse) obligation).contains
          obligation.assumptions.reverse.flatten).take i))
        (droppedDefinitions (unreadDefinitions (readStateOf obligation.assumptions.reverse)
          obligation).contains obligation.assumptions.reverse.flatten)[i].2).isSome)
    (hkept : KeptEntriesHold F σ obligation) : SlicedCounterexampleExtends F σ obligation :=
  sliced_counterexample_extends_of_ordered obligation
    (ObligationExtraction.extractObligations_defsOrdered hp hwf obligation hob) heval hkept

end Core
