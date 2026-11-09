/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.IncrementalSolve
public import Strata.Languages.Core.ObligationExtraction
import all Strata.Languages.Core.IncrementalSolve
import all Strata.Languages.Core.ObligationExtraction
import all Strata.DL.Imperative.EvalContext
import Strata.Util.ExceptProps

/-! # The tree holds exactly the obligations `extractObligations` finds

Every verdict of the incremental back end rests on `readProgram` reading the obligations
`ObligationExtraction.extractObligations` reads: the same labels, properties and goals, in the
same order, each under the same assumptions in the same order. `readProgram_obligations` proves
it.

The proof goes through `VTree.obligations`, which lists a tree's goals in pre-order, each under
the facts on its path:

1. `layoutOf_obligations`: the layout's work items, in goal order, are `t.obligations []`, since
   `buildLayout` numbers the goals in pre-order and gives each one the facts on its path.
2. `readDecls_extract`, with `readStmts_extract` for each procedure body: reading a program into
   a tree `t` and extracting its obligations agree, the extraction yielding `t.obligations []`.
   Both walk the same statements in the same order. A fact the reader puts in a child, because
   it follows a goal, is one the extraction adds after recording that goal, so the goal does not
   see it either way.
-/

public section

namespace Core.IncrementalSolve

open Imperative (PathConditionEntry ProofObligation RevPathConditions)
open Core.ObligationExtraction

/-- A tree's obligations in pre-order, each under the facts on its path, after the facts `ctx`
    on the path above the root. -/
private def VTree.obligations (ctx : List (PathConditionEntry Expression)) (t : VTree) :
    List (ProofObligation Expression) :=
  t.goals.toList.map (Goal.obligation (ctx ++ t.facts.toList)) ++
    t.children.toList.flatMap (VTree.obligations (ctx ++ t.facts.toList))
termination_by t
decreasing_by exact VTree.sizeOf_lt_of_mem (Array.mem_toList_iff.mp ‹_›)

/-- The obligations of a node holding `facts`, `goals` and `kids` so far, after the facts `ctx`
    above it: its goals', then its children's. -/
@[simp] private def nodeObligations (ctx : List (PathConditionEntry Expression))
    (facts : Array (PathConditionEntry Expression)) (goals : Array Goal) (kids : Array VTree) :
    List (ProofObligation Expression) :=
  goals.toList.map (Goal.obligation (ctx ++ facts.toList)) ++
    kids.toList.flatMap (VTree.obligations (ctx ++ facts.toList))

/-- The obligations of a node built from `facts`, `goals` and `children` are its goals', then its
    children's, all after its facts. Unlike the equation of `VTree.obligations`, this rewrites
    only the node it names, leaving the subtrees as they are. -/
private theorem obligations_mk (ctx : List (PathConditionEntry Expression))
    (facts : Array (PathConditionEntry Expression)) (goals : Array Goal) (children : Array VTree) :
    VTree.obligations ctx { facts, goals, children } =
      nodeObligations ctx facts goals children := by
  rw [VTree.obligations, nodeObligations]

/-! ## The layout lists the tree's obligations in pre-order -/

/-- A work item stands for its goal's obligation under the facts on its path. -/
private theorem obligationOf_eq (item : WorkItem) :
    obligationOf item = item.goal.obligation (item.path.toList.flatMap (·.toList)) := rfl

/-- A fold whose every step on an element `x` appends `f x` to the obligations of the work items
    `proj` selects appends `xs.flatMap f`. -/
private theorem fold_tasks {α σ : Type} (proj : σ → Array WorkItem)
    (f : α → List (ProofObligation Expression))
    (step : σ → α → σ) (xs : List α)
    (hstep : ∀ s x, x ∈ xs → (proj (step s x)).toList.map obligationOf =
      (proj s).toList.map obligationOf ++ f x)
    (s : σ) :
    (proj (xs.foldl step s)).toList.map obligationOf =
      (proj s).toList.map obligationOf ++ xs.flatMap f := by
  have := List.foldl_rel (l := xs) (f := step) (g := fun acc x => acc ++ f x) (a := s)
    (b := (proj s).toList.map obligationOf)
    (r := fun s acc => (proj s).toList.map obligationOf = acc) rfl
    (fun x hx _ _ h => by simp only [hstep _ x hx, h])
  rw [this, List.foldl_append_eq_append, List.flatMap_def]

/-- `buildLayout` appends to the work items it is given the obligations of the tree, in
    pre-order, each under the facts on its path. -/
private theorem buildLayout_tasks (t : VTree) (pos : Pos)
    (path : Array (Array (PathConditionEntry Expression))) (b : Build) :
    (buildLayout t pos path b).tasks.toList.map obligationOf =
      b.tasks.toList.map obligationOf ++ t.obligations (path.toList.flatMap (·.toList)) := by
  rw [buildLayout, VTree.obligations]
  split
  rename_i tasks ids heq
  rw [← Array.foldl_toList] at heq
  dsimp only
  rw [← Array.foldl_toList]
  refine (fold_tasks (fun bi : Build × Nat => bi.1.tasks)
    (VTree.obligations (path.toList.flatMap (·.toList) ++ t.facts.toList)) _ t.children.toList
    ?_ _).trans ?_
  · intro s c hc
    simp only
    rw [buildLayout_tasks c]
    simp
  · simp only
    rw [show tasks = _ from (congrArg Prod.fst heq).symm,
      fold_tasks (σ := Array WorkItem × Array Nat) Prod.fst
        (fun g => [Goal.obligation (path.toList.flatMap (·.toList) ++ t.facts.toList) g])
        (hstep := ?_)]
    · simp [List.map_eq_flatMap]
    · intro s g _
      simp [obligationOf_eq]
termination_by t
decreasing_by exact VTree.sizeOf_lt_of_mem (Array.mem_toList_iff.mp hc)

/-- The layout's work items, in goal order, stand for the tree's obligations in pre-order. -/
private theorem layoutOf_obligations (t : VTree) :
    (layoutOf t).tasks.toList.map obligationOf = t.obligations [] := by
  simp [layoutOf, buildLayout_tasks]

/-! ## Reading a body extracts its obligations -/

/-- The obligations extraction records under the path conditions `ctx`, oldest first. -/
private abbrev pcOf (ctx : List (PathConditionEntry Expression)) :
    RevPathConditions Expression := ⟨[ctx.reverse]⟩

/-- The path conditions `pcOf ctx` hand an obligation are the facts `ctx`, in order. -/
private theorem consume_pcOf (ctx : List (PathConditionEntry Expression)) :
    (pcOf ctx).consume = [ctx] := by
  simp [RevPathConditions.consume]

/-- Adding the fact `e` to `pcOf ctx` gives the path conditions of `ctx` followed by `e`. -/
private theorem prepend_pcOf (ctx : List (PathConditionEntry Expression)) (e) :
    (pcOf ctx).prepend e = pcOf (ctx ++ [e]) := by
  simp [RevPathConditions.prepend]

/-- Reading `ss` into a node holding `facts` and `goals`, under the facts `ctx` above it, and
    extracting the obligations of `ss` under the same facts, with the goals already recorded in
    `acc`, agree. -/
private abbrev ReadsLikeExtract (ss : Statements) : Prop :=
  ∀ (facts : Array (PathConditionEntry Expression)) (goals : Array Goal) (t : VTree),
    readStmts facts goals ss = .ok t →
    ∀ (ctx : List (PathConditionEntry Expression)) (acc : Array (ProofObligation Expression))
      (pre : List (ProofObligation Expression)),
    acc.toList = pre ++ goals.toList.map (Goal.obligation (ctx ++ facts.toList)) →
    ∃ A, extractGo (pcOf (ctx ++ facts.toList)) ss acc = .ok A ∧
      A.toList = pre ++ t.obligations ctx

/-- A fact read before `rest`: it joins the node when no goal precedes it, and otherwise starts
    a child holding `rest`. Either way the goals read from `rest` see it, as extraction has them. -/
private theorem fact_extract (entry : PathConditionEntry Expression)
    (facts : Array (PathConditionEntry Expression)) (goals : Array Goal) (rest : Statements)
    (t : VTree) (ctx : List (PathConditionEntry Expression))
    (acc : Array (ProofObligation Expression)) (pre : List (ProofObligation Expression))
    (hacc : acc.toList = pre ++ goals.toList.map (Goal.obligation (ctx ++ facts.toList)))
    (ih : ReadsLikeExtract rest)
    (h : (if goals.isEmpty = true then readStmts (facts.push entry) goals rest else do
      let child ← readStmts #[entry] #[] rest
      Except.ok { facts := facts, goals := goals, children := #[child] }) = .ok t) :
    ∃ A, extractGo (pcOf (ctx ++ facts.toList ++ [entry])) rest acc = .ok A ∧
      A.toList = pre ++ t.obligations ctx := by
  split at h
  · simpa using ih _ _ t h ctx acc pre (by simp_all)
  · obtain ⟨child, hchild, h⟩ := (Except.bind_is_ok _ _ _).mp h
    cases h
    obtain ⟨A, hA, hA'⟩ := ih _ _ child hchild (ctx ++ facts.toList) acc acc.toList (by simp)
    refine ⟨A, by simpa using hA, ?_⟩
    rw [hA', hacc, obligations_mk]
    simp

/-- `readStmts` and `extractGo` agree on every body: see `ReadsLikeExtract`. -/
private theorem readStmts_extract (ss : Statements) : ReadsLikeExtract ss := by
  intro facts goals t h ctx acc pre hacc
  match ss with
  | [] =>
    rw [readStmts] at h
    cases h
    refine ⟨acc, by rw [extractGo], ?_⟩
    rw [VTree.obligations]; simp [hacc]
  | s :: rest =>
    unfold readStmts at h
    dsimp only at h
    split at h
    case h_1 | h_2 =>
      unfold extractGo; dsimp only
      exact readStmts_extract rest _ _ t h ctx _ pre
        (by simp [hacc, Goal.obligation, consume_pcOf])
    case h_3 | h_4 =>
      unfold extractGo; dsimp only
      rw [prepend_pcOf]
      exact fact_extract _ facts goals rest t ctx acc pre hacc (readStmts_extract rest) h
    case h_5 =>
      rename_i thenSs elseSs _
      obtain ⟨tt, htt, h⟩ := (Except.bind_is_ok _ _ _).mp h
      obtain ⟨tf, htf, h⟩ := (Except.bind_is_ok _ _ _).mp h
      obtain ⟨A1, hA1, hA1'⟩ :=
        readStmts_extract thenSs #[] #[] tt htt (ctx ++ facts.toList) #[] [] (by simp)
      obtain ⟨A2, hA2, hA2'⟩ :=
        readStmts_extract elseSs #[] #[] tf htf (ctx ++ facts.toList) #[] [] (by simp)
      simp only [List.append_nil] at hA1 hA2
      unfold extractGo; dsimp only
      simp only [extractFromStatements_eq, hA1, hA2]
      show ∃ A, extractGo (pcOf (ctx ++ facts.toList)) rest (acc ++ A1 ++ A2) = .ok A ∧ _
      split at h
      · rename_i hr
        have hr : rest = [] := by simpa using hr
        obtain ⟨_, ha, h⟩ := (Except.bind_is_ok _ _ _).mp h
        obtain rfl := Except.ok.inj (ha : Except.ok #[] = _)
        obtain rfl := Except.ok.inj h
        refine ⟨acc ++ A1 ++ A2, by rw [hr]; unfold extractGo; rfl, ?_⟩
        rw [obligations_mk]; simp [hacc, hA1', hA2']
      · obtain ⟨r, hr, h⟩ := (Except.bind_is_ok _ _ _).mp h
        obtain ⟨_, ha, h⟩ := (Except.bind_is_ok _ _ _).mp h
        obtain rfl := Except.ok.inj (ha : Except.ok #[r] = _)
        obtain rfl := Except.ok.inj h
        obtain ⟨A, hA, hA'⟩ := readStmts_extract rest #[] #[] r hr (ctx ++ facts.toList)
          (acc ++ A1 ++ A2) (acc ++ A1 ++ A2).toList (by simp)
        refine ⟨A, by simpa using hA, ?_⟩
        rw [hA', obligations_mk]; simp [hacc, hA1', hA2']
    case h_6 => cases h

/-! ## Reading the declarations extracts their obligations -/

/-- Reading the declarations `ds` into a node holding `facts`, `goals` and `kids`, under the facts
    `ctx` above it, and folding `extractDecl` over `ds` from the global facts `ctx ++ facts`
    (newest first) and the obligations of that node so far, agree. -/
private abbrev DeclsLikeExtract (fn : List String) (ds : List Decl) : Prop :=
  ∀ (facts : Array (PathConditionEntry Expression)) (goals : Array Goal) (kids : Array VTree)
    (t : VTree), readDecls fn facts goals kids ds = .ok t →
    ∀ (ctx : List (PathConditionEntry Expression)) (allObs : Array (ProofObligation Expression))
      (pre : List (ProofObligation Expression)),
    allObs.toList = pre ++ nodeObligations ctx facts goals kids →
    ∃ r, ds.foldlM (extractDecl fn) ((ctx ++ facts.toList).reverse, allObs) = .ok r ∧
      r.2.toList = pre ++ t.obligations ctx

/-- The declarations after a goal or a child are read in a new child holding `facts'` and
    `goals'`, which sees the node's facts, as extraction has them. -/
private theorem below_extract (fn : List String) (facts : Array (PathConditionEntry Expression))
    (goals : Array Goal) (kids : Array VTree) (rest : List Decl) (t : VTree)
    (ctx : List (PathConditionEntry Expression)) (allObs : Array (ProofObligation Expression))
    (pre : List (ProofObligation Expression))
    (hacc : allObs.toList = pre ++ nodeObligations ctx facts goals kids)
    (facts' : Array (PathConditionEntry Expression)) (goals' : Array Goal)
    (ih : DeclsLikeExtract fn rest)
    (h : (do
      let t' ← readDecls fn facts' goals' #[] rest
      (Except.ok { facts := facts, goals := goals, children := kids.push t' } :
        Except String VTree)) = .ok t)
    (allObs' : Array (ProofObligation Expression))
    (hacc' : allObs'.toList = allObs.toList ++
      goals'.toList.map (Goal.obligation (ctx ++ facts.toList ++ facts'.toList))) :
    ∃ r, rest.foldlM (extractDecl fn) ((ctx ++ facts.toList ++ facts'.toList).reverse, allObs') =
      .ok r ∧ r.2.toList = pre ++ t.obligations ctx := by
  obtain ⟨t', ht', h⟩ := (Except.bind_is_ok _ _ _).mp h
  obtain rfl := Except.ok.inj h
  obtain ⟨r, hr, hr'⟩ :=
    ih _ _ _ t' ht' (ctx ++ facts.toList) allObs' allObs.toList (by simp [hacc'])
  refine ⟨r, hr, ?_⟩
  rw [hr', hacc, obligations_mk]
  simp

/-- An axiom or `distinct` group, the fact `e`: it joins the node when nothing precedes it there,
    and otherwise starts a child holding the declarations after it. -/
private theorem global_extract (fn : List String) (facts : Array (PathConditionEntry Expression))
    (goals : Array Goal) (kids : Array VTree) (rest : List Decl) (t : VTree)
    (ctx : List (PathConditionEntry Expression)) (allObs : Array (ProofObligation Expression))
    (pre : List (ProofObligation Expression))
    (hacc : allObs.toList = pre ++ nodeObligations ctx facts goals kids)
    (e : PathConditionEntry Expression) (ih : DeclsLikeExtract fn rest)
    (h : (if (kids.isEmpty && goals.isEmpty) = true then readDecls fn (facts.push e) goals kids rest
      else do
        let t' ← readDecls fn #[e] #[] #[] rest
        (Except.ok { facts := facts, goals := goals, children := kids.push t' } :
          Except String VTree)) = .ok t) :
    ∃ r, rest.foldlM (extractDecl fn) (e :: (ctx ++ facts.toList).reverse, allObs) = .ok r ∧
      r.2.toList = pre ++ t.obligations ctx := by
  split at h
  · rename_i hk
    simp only [Bool.and_eq_true, Array.isEmpty_iff] at hk
    obtain ⟨rfl, rfl⟩ := hk
    simpa using ih _ _ _ t h ctx allObs pre (by simpa using hacc)
  · simpa using below_extract fn facts goals kids rest t ctx allObs pre hacc #[e] #[] ih h allObs
      (by simp)

/-- A function or a block of them, which holds no fact: the declarations after it go in a child
    when a goal or a child precedes it. -/
private theorem definition_extract (fn : List String)
    (facts : Array (PathConditionEntry Expression))
    (goals : Array Goal) (kids : Array VTree) (rest : List Decl) (t : VTree)
    (ctx : List (PathConditionEntry Expression)) (allObs : Array (ProofObligation Expression))
    (pre : List (ProofObligation Expression))
    (hacc : allObs.toList = pre ++ nodeObligations ctx facts goals kids)
    (ih : DeclsLikeExtract fn rest)
    (h : (if (kids.isEmpty && goals.isEmpty) = true then readDecls fn facts goals kids rest
      else do
        let t' ← readDecls fn #[] #[] #[] rest
        (Except.ok { facts := facts, goals := goals, children := kids.push t' } :
          Except String VTree)) = .ok t) :
    ∃ r, rest.foldlM (extractDecl fn) ((ctx ++ facts.toList).reverse, allObs) = .ok r ∧
      r.2.toList = pre ++ t.obligations ctx := by
  split at h
  · exact ih _ _ _ t h ctx allObs pre hacc
  · simpa using below_extract fn facts goals kids rest t ctx allObs pre hacc #[] #[] ih h allObs
      (by simp)

/-- `readDecls` and the fold of `extractDecl` agree on every list of declarations: see
    `DeclsLikeExtract`. -/
private theorem readDecls_extract (fn : List String) (ds : List Decl) : DeclsLikeExtract fn ds := by
  intro facts goals kids t h ctx allObs pre hacc
  match ds with
  | [] =>
    unfold readDecls at h
    obtain rfl := Except.ok.inj h
    refine ⟨_, rfl, ?_⟩
    rw [hacc, obligations_mk]
  | d :: rest =>
    have ih := readDecls_extract fn rest
    unfold readDecls at h
    dsimp only at h
    rw [List.foldlM_cons]
    split at h
    case h_1 | h_2 =>
      simp only [extractDecl, Except.ok_bind]
      exact global_extract fn facts goals kids rest t ctx allObs pre hacc _ ih h
    case h_3 =>
      obtain ⟨ss, hss, h⟩ := (Except.bind_is_ok _ _ _).mp h
      obtain ⟨tp, htp, h⟩ := (Except.bind_is_ok _ _ _).mp h
      obtain ⟨A, hA, hA'⟩ :=
        readStmts_extract ss #[] #[] tp htp (ctx ++ facts.toList) #[] [] (by simp)
      have hA : extractGo ⟨[(ctx ++ facts.toList).reverse]⟩ ss #[] = .ok A := by
        simpa [pcOf] using hA
      simp only [extractDecl, hss, Except.ok_bind, extractFromStatements_eq, hA]
      exact ih _ _ _ t h ctx (allObs ++ A) pre (by simp [hacc, hA'])
    case h_4 =>
      split at h
      · rename_i hpre
        simp only [extractDecl, hpre, Except.ok_bind, ite_true]
        exact definition_extract fn facts goals kids rest t ctx allObs pre hacc ih h
      · cases h
    case h_5 =>
      split at h
      · cases h
      · rename_i hfind
        simp only [extractDecl, hfind, Except.ok_bind]
        exact definition_extract fn facts goals kids rest t ctx allObs pre hacc ih h
    case h_6 =>
      simp only [extractDecl, Except.ok_bind]
      split at h
      · rename_i hk
        simp only [Array.isEmpty_iff] at hk
        subst hk
        exact ih _ _ _ t h ctx _ pre
          (by simp [hacc, Goal.obligation, RevPathConditions.consume])
      · simpa using below_extract fn facts goals kids rest t ctx allObs pre hacc #[] _ ih h _
          (by simp [Goal.obligation, RevPathConditions.consume])
    case h_7 =>
      -- A type declaration, the one kind both sides skip.
      obtain ⟨td, md, rfl⟩ : ∃ td md, d = .type td md := by cases d <;> simp_all
      simp only [extractDecl, Except.ok_bind]
      exact ih _ _ _ t h ctx allObs pre hacc

/-! ## The tree holds the extracted obligations -/

/-- When `readProgram` reads `p` into a tree, `extractObligations` succeeds on `p`, and the
    layout's work items, in goal order, stand for exactly the obligations it finds, in the same
    order. -/
theorem readProgram_obligations {p : Program} {t : VTree} (h : readProgram p = .ok t) :
    ∃ obs, extractObligations p = .ok obs ∧
      obs.toList = (layoutOf t).tasks.toList.map obligationOf := by
  obtain ⟨r, hr, hr'⟩ := readDecls_extract _ p.decls #[] #[] #[] t h [] #[] [] (by simp)
  refine ⟨r.2, ?_, by rw [hr', layoutOf_obligations]; simp⟩
  simp only [List.append_nil, List.reverse_nil] at hr
  unfold extractObligations
  rw [hr]
  rfl

end Core.IncrementalSolve

end -- public section
