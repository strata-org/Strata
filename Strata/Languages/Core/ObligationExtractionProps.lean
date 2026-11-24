/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.ObligationExtraction
import all Strata.Languages.Core.ObligationExtraction
import all Strata.DL.Imperative.EvalContext

/-! # Properties of proof obligation extraction

Key theorems: `extractFromStatements_ok` (a body in obligation form extracts),
`extractGoLinked_map_fst` and `extractObligations_of_extractLinkedObligations` (the linked
extraction has exactly the obligations of the plain one), `extractLinkedFromStatements_ok`,
and `extractGoLinked_induct` with the per-statement equations `extractGoLinked_assert` …
`extractGoLinked_unsupported`.
-/

public section

namespace Core.ObligationExtraction
open Lambda Imperative

/-- `extractFromStatements` is the statement walk `extractGo` from the empty accumulator. -/
@[simp] theorem extractFromStatements_eq (pc : RevPathConditions Expression) (ss : Statements) :
    extractFromStatements pc ss = extractGo pc ss #[] := by rw [extractFromStatements]

/-- `extractGo` succeeds on any body satisfying `hasObligationForm`, for any path
    conditions and accumulator. -/
private theorem extractGo_ok (pc : RevPathConditions Expression) (ss : Statements)
    (acc : Array (ProofObligation Expression))
    (h : Statements.hasObligationForm ss = true) :
    (extractGo pc ss acc).isOk = true := by
  induction pc, ss, acc using extractGo.induct
      (motive2 := fun pcs stmts => stmts.hasObligationForm → (extractGo pcs stmts #[]).isOk) <;>
    simp only [Statements.hasObligationForm, Block.allSubstmts, extractGo, Except.toBool,
      Stmt.allSubstmts.eq_def, Statement.isObligationForm, bind, Except.bind,
      extractFromStatements_eq] at * <;>
    grind

/-- `extractFromStatements` succeeds on any body satisfying `hasObligationForm`. -/
theorem extractFromStatements_ok (pc : RevPathConditions Expression) (ss : Statements)
    (h : Statements.hasObligationForm ss = true) :
    (extractFromStatements pc ss).isOk = true := by simp [extractGo_ok, h]

/-! ## The linked extraction agrees with `extractGo` -/

/-- `extractGo` from the accumulator `acc` gives `acc` followed by the result of the same
    walk from the empty accumulator; the walks fail together. -/
private theorem extractGo_acc (pc : RevPathConditions Expression) (ss : Statements)
    (acc : Array (ProofObligation Expression)) :
    extractGo pc ss acc = (extractGo pc ss #[]).map (acc ++ ·) := by
  suffices h : ∀ pc ss (acc₀ : Array (ProofObligation Expression)) acc,
      extractGo pc ss acc = (extractGo pc ss #[]).map (acc ++ ·) from h pc ss #[] acc
  intro pc ss acc₀
  induction pc, ss, acc₀ using extractGo.induct (motive2 := fun _ _ => True)
  case case5 ihR =>
    intro acc
    simp only [extractGo, extractFromStatements_eq, bind, Except.bind]
    split <;> try rfl
    split <;> try rfl
    rw [ihR #[] #[] (acc ++ _ ++ _), ihR #[] #[] (_ ++ _)]
    cases extractGo _ _ #[] <;> simp [Except.map]
  case case2 ih | case3 ih =>
    intro acc
    simp only [extractGo]
    rw [ih, ih (#[].push _)]
    cases extractGo _ _ #[] <;> simp [Except.map]
  case case4 ih | case6 ih =>
    intro acc
    simp only [extractGo]
    exact ih acc
  case case8 => trivial
  all_goals
    intro acc
    simp [extractGo, Except.map]

/-- A successful `extractGo` run from accumulator `acc` returns `acc` followed by one
    obligation for each entry of `linkEventsGo events ss`. -/
private theorem linkEventsGo_size (pc : RevPathConditions Expression) (ss : Statements)
    (acc obs : Array (ProofObligation Expression)) (events : List ExtractReplayEvent)
    (h : extractGo pc ss acc = .ok obs) :
    acc.size + (linkEventsGo events ss).size = obs.size := by
  revert obs events h
  induction pc, ss, acc using extractGo.induct (motive2 := fun pc ss => ∀ obs events,
      extractGo pc ss #[] = .ok obs → (linkEventsGo events ss).size = obs.size)
  case case8 =>
    rename_i ih _ _ h
    simpa using ih _ _ h
  case case6 e _ _ =>
    intro obs events h
    cases e <;> grind [extractGo, linkEventsGo]
  all_goals
    intro obs events h
    simp only [extractGo, extractFromStatements_eq, linkEventsGo, bind, Except.bind] at h ⊢
  all_goals (repeat' split at h) <;> grind

/-- Dropping the back-links of `attachLinks entry obs events` gives `obs`. -/
private theorem attachLinks_map_fst (entry : Statements) (obs : Array (ProofObligation Expression))
    (events : Array (List ExtractReplayEvent)) :
    (attachLinks entry obs events).map Prod.fst = obs := by
  apply Array.ext <;> simp [attachLinks]

/-- Linking two obligation arrays against two event arrays is linking each against its own,
    when the first obligation array has one event list per obligation. -/
private theorem attachLinks_append (entry : Statements)
    (a b : Array (ProofObligation Expression)) (ea eb : Array (List ExtractReplayEvent))
    (h : a.size = ea.size) :
    attachLinks entry (a ++ b) (ea ++ eb) = attachLinks entry a ea ++ attachLinks entry b eb := by
  apply Array.ext
  · simp [attachLinks]
  · intro i _ _
    simp only [attachLinks, Array.getElem_mapIdx, Array.getElem_append, Array.size_mapIdx,
      Array.getD_eq_getD_getElem?]
    split
    · rw [Array.getElem?_append_left (by omega)]
    · simp [Array.getElem?_append_right (show ea.size ≤ i by omega), h]

/-- `extractGoLinked` from the accumulator `acc` gives `acc` followed by the result of the
    same walk from the empty accumulator; the walks fail together. -/
theorem extractGoLinked_acc (entry : Statements) (pc : RevPathConditions Expression)
    (events : List ExtractReplayEvent) (ss : Statements) (acc : Array LinkedObligation) :
    extractGoLinked entry pc events ss acc =
      (extractGoLinked entry pc events ss #[]).map (acc ++ ·) := by
  unfold extractGoLinked
  cases extractGo pc ss #[] <;> simp [Except.map]

/-- `extractGoLinked` on no statements returns its accumulator. -/
theorem extractGoLinked_nil (entry : Statements) (pc : RevPathConditions Expression)
    (events : List ExtractReplayEvent) (acc : Array LinkedObligation) :
    extractGoLinked entry pc events [] acc = .ok acc := by
  simp [extractGoLinked, extractGo, attachLinks, Except.map]

/-- One statement of `extractGoLinked`: an `assert` or `cover` adds its obligation with the
    link to the current `events`; an `assume` or `init` extends the path conditions, a
    nondeterministic `init` also the events with its write; a nondeterministic `if` walks both
    branches, each with its branch event, and the rest of the list after the join with the
    else-branch completion path; any other statement is an error. -/
private theorem extractGoLinked_cons (entry : Statements) (pc : RevPathConditions Expression)
    (events : List ExtractReplayEvent) (s : Statement) (rest : Statements)
    (acc : Array LinkedObligation) :
    extractGoLinked entry pc events (s :: rest) acc =
      match s with
      | .cmd (.cmd (.assert label e md)) =>
        extractGoLinked entry pc events rest (acc.push
          (⟨label, convertMetaDataPropertyType md, pc.consume, e, md⟩, ⟨entry, label, events⟩))
      | .cmd (.cmd (.cover label e md)) =>
        extractGoLinked entry pc events rest
          (acc.push (⟨label, .cover, pc.consume, e, md⟩, ⟨entry, label, events⟩))
      | .cmd (.cmd (.assume label e _)) =>
        extractGoLinked entry (pc.prepend (.assumption label e)) events rest acc
      | .ite .nondet thenSs elseSs _ => do
        let thenObs ← extractGoLinked entry pc (events ++ [.branch true]) thenSs #[]
        let elseObs ← extractGoLinked entry pc (events ++ [.branch false]) elseSs #[]
        extractGoLinked entry pc (events ++ [.branch false] ++
          completionEventsForStatements elseSs) rest (acc ++ thenObs ++ elseObs)
      | .cmd (.cmd (.init name ty value _)) =>
        extractGoLinked entry (pc.prepend (.varDecl name ty value))
          (match value with
            | .det _ => events
            | .nondet => events ++ [.nondetWrite name (some ty)]) rest acc
      | _ => .error "ObligationExtraction: unsupported statement" := by
  unfold extractGoLinked
  split
  all_goals simp only [extractGo, extractFromStatements_eq, linkEventsGo, bind, Except.bind]
  case h_5 value _ =>
    cases value <;> simp only [linkEventsGo]
  case h_6 => rfl
  case h_4 thenSs elseSs _ =>
    rcases ht : extractGo pc thenSs #[] with _ | t <;> simp only [Except.map]
    rcases he : extractGo pc elseSs #[] with _ | e <;> simp only
    rw [extractGo_acc]
    cases extractGo pc rest #[] <;> simp only [Except.map, Array.empty_append]
    have hT := linkEventsGo_size _ _ _ _ (events ++ [.branch true]) ht
    have hE := linkEventsGo_size _ _ _ _ (events ++ [.branch false]) he
    simp only [List.size_toArray, List.length_nil, Nat.zero_add] at hT hE
    rw [attachLinks_append _ _ _ _ _ (by rw [Array.size_append, Array.size_append, hT, hE]),
      attachLinks_append _ _ _ _ _ hT.symm]
    simp only [Array.append_assoc]
  case h_1 | h_2 =>
    rw [extractGo_acc]
    cases extractGo pc rest #[] <;> simp only [Except.map]
    rw [Array.push_eq_append, Array.empty_append, attachLinks_append _ _ _ _ _ rfl]
    simp [attachLinks]

/-- `extractGoLinked` on an `assert` adds its obligation, linked to the current `events`. -/
theorem extractGoLinked_assert (entry : Statements) (pc : RevPathConditions Expression)
    (events : List ExtractReplayEvent) (label : String) (e : Expression.Expr)
    (md : MetaData Expression) (rest : Statements) (acc : Array LinkedObligation) :
    extractGoLinked entry pc events (.cmd (.cmd (.assert label e md)) :: rest) acc =
      extractGoLinked entry pc events rest (acc.push
        (⟨label, convertMetaDataPropertyType md, pc.consume, e, md⟩, ⟨entry, label, events⟩)) :=
  extractGoLinked_cons ..

/-- `extractGoLinked` on a `cover` adds its obligation, linked to the current `events`. -/
theorem extractGoLinked_cover (entry : Statements) (pc : RevPathConditions Expression)
    (events : List ExtractReplayEvent) (label : String) (e : Expression.Expr)
    (md : MetaData Expression) (rest : Statements) (acc : Array LinkedObligation) :
    extractGoLinked entry pc events (.cmd (.cmd (.cover label e md)) :: rest) acc =
      extractGoLinked entry pc events rest
        (acc.push (⟨label, .cover, pc.consume, e, md⟩, ⟨entry, label, events⟩)) :=
  extractGoLinked_cons ..

/-- `extractGoLinked` on an `assume` adds the assumption to the path conditions. -/
theorem extractGoLinked_assume (entry : Statements) (pc : RevPathConditions Expression)
    (events : List ExtractReplayEvent) (label : String) (e : Expression.Expr)
    (md : MetaData Expression) (rest : Statements) (acc : Array LinkedObligation) :
    extractGoLinked entry pc events (.cmd (.cmd (.assume label e md)) :: rest) acc =
      extractGoLinked entry (pc.prepend (.assumption label e)) events rest acc :=
  extractGoLinked_cons ..

/-- `extractGoLinked` on a nondeterministic `if` walks both branches from the current path
    conditions, each with its branch event, then the rest of the list with the else-branch
    completion path, after the obligations of both branches. -/
theorem extractGoLinked_ite (entry : Statements) (pc : RevPathConditions Expression)
    (events : List ExtractReplayEvent) (thenSs elseSs : Statements) (md : MetaData Expression)
    (rest : Statements) (acc : Array LinkedObligation) :
    extractGoLinked entry pc events (.ite .nondet thenSs elseSs md :: rest) acc = (do
      let thenObs ← extractGoLinked entry pc (events ++ [.branch true]) thenSs #[]
      let elseObs ← extractGoLinked entry pc (events ++ [.branch false]) elseSs #[]
      extractGoLinked entry pc (events ++ [.branch false] ++
        completionEventsForStatements elseSs) rest (acc ++ thenObs ++ elseObs)) :=
  extractGoLinked_cons ..

/-- `extractGoLinked` on an `init` adds the variable definition to the path conditions and,
    for a nondeterministic `init`, its write to the events. -/
theorem extractGoLinked_init (entry : Statements) (pc : RevPathConditions Expression)
    (events : List ExtractReplayEvent) (name : Expression.Ident) (ty : Expression.Ty)
    (value : ExprOrNondet Expression) (md : MetaData Expression) (rest : Statements)
    (acc : Array LinkedObligation) :
    extractGoLinked entry pc events (.cmd (.cmd (.init name ty value md)) :: rest) acc =
      extractGoLinked entry (pc.prepend (.varDecl name ty value))
        (match value with
          | .det _ => events
          | .nondet => events ++ [.nondetWrite name (some ty)]) rest acc :=
  extractGoLinked_cons ..

/-- `extractGoLinked` on a statement that is none of `assert`, `cover`, `assume`, `init` and
    a nondeterministic `if` is an error. -/
theorem extractGoLinked_unsupported (entry : Statements) (pc : RevPathConditions Expression)
    (events : List ExtractReplayEvent) (s : Statement) (rest : Statements)
    (acc : Array LinkedObligation)
    (h1 : ∀ label e md, s = .cmd (.cmd (.assert label e md)) → False)
    (h2 : ∀ label e md, s = .cmd (.cmd (.cover label e md)) → False)
    (h3 : ∀ label e md, s = .cmd (.cmd (.assume label e md)) → False)
    (h4 : ∀ thenSs elseSs md, s = .ite .nondet thenSs elseSs md → False)
    (h5 : ∀ name ty e md, s = .cmd (.cmd (.init name ty e md)) → False) :
    extractGoLinked entry pc events (s :: rest) acc =
      .error "ObligationExtraction: unsupported statement" := by
  rw [extractGoLinked_cons]
  split <;> first | rfl | (exfalso; grind)

/-- Induction along the recursion of `extractGoLinked entry`: a property `motive` of the path
    conditions, events, statements and accumulator of a walk holds for every walk when it holds
    for the empty list, for every unsupported statement, and for each supported statement form
    given the property of the walk that statement continues with (for a nondeterministic `if`:
    of both branch walks, and of the walk after the join from every accumulator). -/
theorem extractGoLinked_induct (entry : Statements)
    (motive : RevPathConditions Expression → List ExtractReplayEvent → Statements →
      Array LinkedObligation → Prop)
    (case1 : ∀ pc events acc, motive pc events [] acc)
    (case2 : ∀ pc events rest acc label e md,
      have propType := convertMetaDataPropertyType md
      have obligation : ProofObligation Expression := ⟨label, propType, pc.consume, e, md⟩
      have link : ExtractBackLink := ⟨entry, label, events⟩
      motive pc events rest (acc.push (obligation, link)) →
      motive pc events (.cmd (.cmd (.assert label e md)) :: rest) acc)
    (case3 : ∀ pc events rest acc label e md,
      have obligation : ProofObligation Expression := ⟨label, .cover, pc.consume, e, md⟩
      have link : ExtractBackLink := ⟨entry, label, events⟩
      motive pc events rest (acc.push (obligation, link)) →
      motive pc events (.cmd (.cmd (.cover label e md)) :: rest) acc)
    (case4 : ∀ pc events rest acc label e md,
      motive (pc.prepend (.assumption label e)) events rest acc →
      motive pc events (.cmd (.cmd (.assume label e md)) :: rest) acc)
    (case5 : ∀ pc events rest acc thenSs elseSs md,
      motive pc (events ++ [.branch true]) thenSs #[] →
      motive pc (events ++ [.branch false]) elseSs #[] →
      (∀ thenObs elseObs,
        have continuationEvents := events ++ [.branch false] ++
          completionEventsForStatements elseSs
        motive pc continuationEvents rest (acc ++ thenObs ++ elseObs)) →
      motive pc events (.ite .nondet thenSs elseSs md :: rest) acc)
    (case6 : ∀ pc events rest acc name ty e md,
      have events' := match e with
        | .det _ => events
        | .nondet => events ++ [.nondetWrite name (some ty)]
      motive (pc.prepend (.varDecl name ty e)) events' rest acc →
      motive pc events (.cmd (.cmd (.init name ty e md)) :: rest) acc)
    (case7 : ∀ pc events rest acc (s : Statement),
      (∀ label e md, s = .cmd (.cmd (.assert label e md)) → False) →
      (∀ label e md, s = .cmd (.cmd (.cover label e md)) → False) →
      (∀ label e md, s = .cmd (.cmd (.assume label e md)) → False) →
      (∀ thenSs elseSs md, s = .ite .nondet thenSs elseSs md → False) →
      (∀ name ty e md, s = .cmd (.cmd (.init name ty e md)) → False) →
      motive pc events (s :: rest) acc)
    (pc : RevPathConditions Expression) (events : List ExtractReplayEvent) (ss : Statements)
    (acc : Array LinkedObligation) : motive pc events ss acc :=
  extractGo.induct (fun pc ss _ => ∀ events acc, motive pc events ss acc)
    (fun pc ss => ∀ events, motive pc events ss #[])
    (fun pc _ events acc => case1 pc events acc)
    (fun pc rest _ label e md ih events acc => case2 pc events rest acc label e md (ih _ _))
    (fun pc rest _ label e md ih events acc => case3 pc events rest acc label e md (ih _ _))
    (fun pc rest _ label e md ih events acc => case4 pc events rest acc label e md (ih _ _))
    (fun pc rest _ thenSs elseSs md ihT ihE ihR events acc =>
      case5 pc events rest acc thenSs elseSs md (ihT _) (ihE _) fun _ _ => ihR #[] #[] _ _)
    (fun pc rest _ name ty e md ih events acc => case6 pc events rest acc name ty e md (ih _ _))
    (fun pc rest _ s h1 h2 h3 h4 h5 events acc => case7 pc events rest acc s h1 h2 h3 h4 h5)
    (fun _ _ ih events => ih events #[]) pc ss #[] events acc

/-- The obligations of a linked extraction walk are exactly those of `extractGo` on the same
    path conditions and statements, from the obligations of the accumulator: the two walks
    fail together, and on success dropping the back-links gives `extractGo`'s result. -/
theorem extractGoLinked_map_fst (entry : Statements) (pc : RevPathConditions Expression)
    (events : List ExtractReplayEvent) (ss : Statements) (acc : Array LinkedObligation) :
    (extractGoLinked entry pc events ss acc).map (·.map Prod.fst) =
      extractGo pc ss (acc.map Prod.fst) := by
  rw [extractGo_acc, extractGoLinked]
  cases extractGo pc ss #[] <;> simp [Except.map, attachLinks_map_fst]

/-- The obligations of `extractLinkedFromStatements` are exactly those of
    `extractFromStatements` on the same path conditions and statements: the two fail
    together, and on success dropping the back-links gives `extractFromStatements`'s
    result. -/
private theorem extractLinkedFromStatements_map_fst (pc : RevPathConditions Expression)
    (ss : Statements) :
    (extractLinkedFromStatements pc ss).map (·.map Prod.fst) = extractFromStatements pc ss := by
  rw [extractLinkedFromStatements, extractGoLinked_map_fst, extractFromStatements_eq,
    Array.map_empty]

/-- `extractLinkedFromStatements` succeeds on any body satisfying `hasObligationForm`. -/
theorem extractLinkedFromStatements_ok (pc : RevPathConditions Expression) (ss : Statements)
    (h : Statements.hasObligationForm ss = true) :
    (extractLinkedFromStatements pc ss).isOk = true := by
  have hok := extractFromStatements_ok pc ss h
  rw [← extractLinkedFromStatements_map_fst] at hok
  revert hok
  cases extractLinkedFromStatements pc ss <;> exact id

/-- `extractDecl` from the obligations `acc` gives `acc` followed by the obligations of the
    same step from no obligations, with the same path-condition facts; the steps fail
    together. -/
private theorem extractDecl_acc (funcNames : List String) (globalPc : PathCondition Expression)
    (acc : Array (ProofObligation Expression)) (decl : Decl) :
    extractDecl funcNames (globalPc, acc) decl =
      (extractDecl funcNames (globalPc, #[]) decl).map fun r => (r.1, acc ++ r.2) := by
  cases decl <;> simp only [extractDecl, bind, Except.bind] <;> (repeat' split) <;>
    simp [Except.map]

/-- A step of `extractLinkedObligations` on a declaration that is not a lemma is the step of
    `extractObligations` once the back-links are dropped. -/
private theorem extractLinkedDecl_map_fst (funcNames : List String)
    (globalPc : PathCondition Expression) (acc : Array LinkedObligation) (decl : Decl)
    (h : ∀ l md, decl ≠ .lemma l md) :
    (extractLinkedDecl funcNames (globalPc, acc) decl).map (fun r => (r.1, r.2.map Prod.fst)) =
      extractDecl funcNames (globalPc, acc.map Prod.fst) decl := by
  rw [extractDecl_acc]
  cases decl
  case lemma l md => exact absurd rfl (h l md)
  all_goals simp only [extractLinkedDecl, extractDecl, bind, Except.bind, pure, Except.pure]
  case proc proc _ =>
    rcases procedureStatements funcNames proc with _ | ss
    · rfl
    · simp only [extractFromStatements_eq]
      cases extractGo ⟨[globalPc]⟩ ss #[] <;> simp [Except.map, attachLinks_map_fst]
  case func f _ =>
    by_cases hf : f.preconditions.isEmpty <;> simp [hf, Except.map, attachLinks]
  case recFuncBlock fs _ =>
    cases fs.find? (fun f => !f.preconditions.isEmpty) <;> simp [Except.map, attachLinks]
  all_goals simp [Except.map, attachLinks]

/-- A step of `extractLinkedObligations` on a procedure appends the linked obligations of its
    statements (`procedureStatements`), extracted from the global path-condition facts. -/
theorem extractLinkedDecl_proc (funcNames : List String) (globalPc : PathCondition Expression)
    (acc : Array LinkedObligation) (proc : Procedure) (md : MetaData Expression) :
    extractLinkedDecl funcNames (globalPc, acc) (.proc proc md) = (do
      let ss ← procedureStatements funcNames proc
      let obs ← extractLinkedFromStatements ⟨[globalPc]⟩ ss
      .ok (globalPc, acc ++ obs)) := by
  simp only [extractLinkedDecl, extractDecl, bind, Except.bind]
  rcases procedureStatements funcNames proc with _ | ss
  · rfl
  · simp only [extractLinkedFromStatements, extractGoLinked, ← extractFromStatements_eq]
    rcases extractFromStatements ⟨[globalPc]⟩ ss with _ | obs <;> simp [Except.map, pure,
      Except.pure]

/-- A step of `extractLinkedObligations` on a declaration other than a procedure or a lemma
    adds no obligation: it is the step of `extractObligations`, which only updates the global
    path-condition facts or fails, with the obligations `acc` kept. -/
private theorem extractLinkedDecl_of_not_proc (funcNames : List String)
    (globalPc : PathCondition Expression) (acc : Array LinkedObligation) (decl : Decl)
    (hp : ∀ proc md, decl ≠ .proc proc md) (hl : ∀ l md, decl ≠ .lemma l md) :
    extractLinkedDecl funcNames (globalPc, acc) decl =
      (extractDecl funcNames (globalPc, #[]) decl).map fun r => (r.1, acc) := by
  cases decl
  case proc proc md => exact absurd rfl (hp proc md)
  case lemma l md => exact absurd rfl (hl l md)
  all_goals simp only [extractLinkedDecl, extractDecl, bind, Except.bind, pure, Except.pure]
  case func f _ =>
    by_cases hf : f.preconditions.isEmpty <;> simp [hf, Except.map, attachLinks]
  case recFuncBlock fs _ =>
    cases fs.find? (fun f => !f.preconditions.isEmpty) <;> simp [Except.map, attachLinks]
  all_goals simp [Except.map, attachLinks]

/-- A fold in `Except` that succeeds from `s` with `r` succeeds, with a second step function,
    from `g s` with `g r`, when every successful step of the first maps through `g` to a
    successful step of the second. -/
private theorem foldlM_ok_of_step {α σ τ ε : Type} (g : σ → τ) (fL : σ → α → Except ε σ)
    (fM : τ → α → Except ε τ) (hstep : ∀ s a r, fL s a = .ok r → fM (g s) a = .ok (g r)) :
    ∀ (l : List α) (s r : σ), l.foldlM fL s = .ok r → l.foldlM fM (g s) = .ok (g r)
  | [], _, _, h => by cases h; rfl
  | a :: l, s, r, h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h ⊢
    split at h
    · cases h
    · rename_i s' hs'
      rw [hstep s a s' hs']
      exact foldlM_ok_of_step g fL fM hstep l s' r h

/-- The obligations of a successful `extractLinkedObligations` run are exactly those
    `extractObligations` extracts from the same program, so the two extractions cannot
    disagree on the obligations; `extractLinkedObligations` fails on a program with a
    lemma. -/
theorem extractObligations_of_extractLinkedObligations (p : Program)
    (arr : Array LinkedObligation) (h : extractLinkedObligations p = .ok arr) :
    extractObligations p = .ok (arr.map Prod.fst) := by
  simp only [extractLinkedObligations, extractObligations, bind, Except.bind] at h ⊢
  split at h
  · cases h
  rename_i r hr
  have hstep : ∀ s d r, extractLinkedDecl p.funcNames s d = .ok r →
      extractDecl p.funcNames (s.1, s.2.map Prod.fst) d = .ok (r.1, r.2.map Prod.fst) := by
    intro ⟨globalPc, acc⟩ d r hr
    have hd : ∀ l md, d ≠ .lemma l md := by
      rintro l md rfl
      simp [extractLinkedDecl] at hr
    rw [← extractLinkedDecl_map_fst _ _ _ _ hd, hr]
    rfl
  have hp : p.decls.foldlM (extractDecl p.funcNames) ([], #[]) = .ok (r.1, r.2.map Prod.fst) :=
    by simpa using foldlM_ok_of_step (fun r => (r.1, r.2.map Prod.fst)) _ _ hstep _ _ _ hr
  rw [hp]
  cases h
  rfl

end Core.ObligationExtraction

end -- public section
