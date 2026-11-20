/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.ObligationExtraction
public import Strata.DL.Imperative.Logic.LangDef
public import Strata.Transform.GuardFwdCoreCorrect
public import Strata.Transform.DefInlineCoreCorrect
public import Strata.Transform.BetaReduceProps
public import Strata.Transform.Passive.CoreTyped
public import Strata.Transform.WPLoopCorrect
import all Strata.Languages.Core.ObligationExtraction
import all Strata.Transform.CoreTransform
import all Strata.DL.Imperative.EvalContext
import Strata.DL.Lambda.LExprWFProps
import Strata.Util.ExceptProps
import Strata.Languages.Core.ProcedureProps

/-! # Properties of proof obligation extraction

Key theorems: `extractFromStatements_ok` (a body in obligation form extracts),
`extractGoLinked_map_fst` and `extractObligations_of_extractLinkedObligations` (the linked
extraction has exactly the obligations of the plain one), `extractLinkedFromStatements_ok`,
and `extractGoLinked_induct` with the per-statement equations `extractGoLinked_assert` …
`extractGoLinked_unsupported`.

The definitions of an extracted obligation's path condition come from the `init`s on the path to
its `assert` or `cover`, in program order. When every statement list extraction reads is def-use
well formed (`Block.defUseWellFormed`, the `defUseOk` field of the initial-environment gate
`Imperative.Logic.BlockInitEnvWF`), no definition re-declares a variable and no right-hand side
reads its own variable or a later one (`extractObligations_defsOrdered`).

- `Core.ObligationExtraction.extractFromStatements_defsOrdered` — the definitions of every
  obligation extracted from a def-use well formed statement list are declared before use and
  have distinct variables
- `Core.ObligationExtraction.extractObligations_defsOrdered` — the same for a program
- `Core.ObligationExtraction.extractObligations_defsOrdered_of_gate` — the same, when every
  statement list extraction reads has an entry environment satisfying the gate
- `Core.ObligationExtraction.extractFromStatements_defsTyped` — the definitions of every
  obligation extracted from a def-use well formed statement list whose annotations agree with a
  typing and whose `init`s are typed are typed (`DefsTyped`)
- `Core.ObligationExtraction.extractObligations_defsTyped` — the same for a program

Key definitions: `Core.ObligationExtraction.definitions`, `Core.ObligationExtraction.DefsOrdered`,
`Core.ObligationExtraction.WPPipelineEntryGates`, `Core.ObligationExtraction.typedDefinitions`,
`Core.ObligationExtraction.DefsTyped`.
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
private theorem extractDecl_acc (globalPc : PathCondition Expression)
    (acc : Array (ProofObligation Expression)) (decl : Decl) :
    extractDecl (globalPc, acc) decl =
      (extractDecl (globalPc, #[]) decl).map fun r => (r.1, acc ++ r.2) := by
  cases decl <;> simp only [extractDecl, bind, Except.bind] <;> (repeat' split) <;>
    simp [Except.map]

/-- A step of `extractLinkedObligations` on a declaration that is not a lemma is the step of
    `extractObligations` once the back-links are dropped. -/
private theorem extractLinkedDecl_map_fst
    (globalPc : PathCondition Expression) (acc : Array LinkedObligation) (decl : Decl)
    (h : ∀ l md, decl ≠ .lemma l md) :
    (extractLinkedDecl (globalPc, acc) decl).map (fun r => (r.1, r.2.map Prod.fst)) =
      extractDecl (globalPc, acc.map Prod.fst) decl := by
  rw [extractDecl_acc]
  cases decl
  case lemma l md => exact absurd rfl (h l md)
  all_goals simp only [extractLinkedDecl, extractDecl, bind, Except.bind, pure, Except.pure]
  case proc proc _ =>
    rcases procedureStatements proc with _ | ss
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
theorem extractLinkedDecl_proc (globalPc : PathCondition Expression)
    (acc : Array LinkedObligation) (proc : Procedure) (md : MetaData Expression) :
    extractLinkedDecl (globalPc, acc) (.proc proc md) = (do
      let ss ← procedureStatements proc
      let obs ← extractLinkedFromStatements ⟨[globalPc]⟩ ss
      .ok (globalPc, acc ++ obs)) := by
  simp only [extractLinkedDecl, extractDecl, bind, Except.bind]
  rcases procedureStatements proc with _ | ss
  · rfl
  · simp only [extractLinkedFromStatements, extractGoLinked, ← extractFromStatements_eq]
    rcases extractFromStatements ⟨[globalPc]⟩ ss with _ | obs <;> simp [Except.map, pure,
      Except.pure]

/-- A step of `extractLinkedObligations` on a declaration other than a procedure or a lemma
    adds no obligation: it is the step of `extractObligations`, which only updates the global
    path-condition facts or fails, with the obligations `acc` kept. -/
private theorem extractLinkedDecl_of_not_proc
    (globalPc : PathCondition Expression) (acc : Array LinkedObligation) (decl : Decl)
    (hp : ∀ proc md, decl ≠ .proc proc md) (hl : ∀ l md, decl ≠ .lemma l md) :
    extractLinkedDecl (globalPc, acc) decl =
      (extractDecl (globalPc, #[]) decl).map fun r => (r.1, acc) := by
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
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hv
  simp only [hv, Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at h ⊢
  split at h
  · cases h
  rename_i r hr
  have hstep : ∀ s d r, extractLinkedDecl s d = .ok r →
      extractDecl (s.1, s.2.map Prod.fst) d = .ok (r.1, r.2.map Prod.fst) := by
    intro ⟨globalPc, acc⟩ d r hr
    have hd : ∀ l md, d ≠ .lemma l md := by
      rintro l md rfl
      simp [extractLinkedDecl] at hr
    rw [← extractLinkedDecl_map_fst _ _ _ hd, hr]
    rfl
  have hp : p.decls.foldlM extractDecl ([], #[]) = .ok (r.1, r.2.map Prod.fst) :=
    by simpa using foldlM_ok_of_step (fun r => (r.1, r.2.map Prod.fst)) _ _ hstep _ _ _ hr
  rw [hp]
  cases h
  rfl


/-- The definitions of the path-condition entries `entries`, in order, each as its variable and
    right-hand side. -/
@[expose] def definitions (entries : List (PathConditionEntry Expression)) :
    List (Expression.Ident × Expression.Expr) :=
  entries.filterMap fun
    | .varDecl x _ (.det e) => some (x, e)
    | _ => none

/-- The definitions `ds` are declared before use with distinct variables: of two definitions,
    the earlier has another variable and does not read the later one's, and no right-hand side
    reads its own variable. -/
@[expose] def DefsOrdered (ds : List (Expression.Ident × Expression.Expr)) : Prop :=
  ds.Pairwise (fun a b => a.1 ≠ b.1 ∧ ∀ ty, (b.1, ty) ∉ LExpr.freeVars a.2) ∧
    ∀ a ∈ ds, ∀ ty, (a.1, ty) ∉ LExpr.freeVars a.2

/-- The path invariant of the extraction walk: the definitions of the path condition `E` so far
    are declared before use, and the defined-names predicate `D` holds of their variables and of
    every name their right-hand sides read. -/
private def PathInv (D : Expression.Ident → Bool) (E : List (PathConditionEntry Expression)) :
    Prop :=
  DefsOrdered (definitions E) ∧
    ∀ a ∈ definitions E, D a.1 = true ∧ ∀ y ty, (y, ty) ∈ LExpr.freeVars a.2 → D y = true

/-- The path invariant holds for a larger defined-names predicate. -/
private theorem PathInv.mono {D D' : Expression.Ident → Bool} {E}
    (hD : ∀ n, D n = true → D' n = true) (h : PathInv D E) : PathInv D' E :=
  ⟨h.1, fun a ha => ⟨hD _ (h.2 a ha).1, fun y ty hy => hD _ ((h.2 a ha).2 y ty hy)⟩⟩

/-- The definitions of a concatenation are those of its parts. -/
private theorem definitions_append (a b : List (PathConditionEntry Expression)) :
    definitions (a ++ b) = definitions a ++ definitions b :=
  List.filterMap_append

/-- Appending an entry that is not a definition keeps the path invariant. -/
private theorem PathInv.push {D : Expression.Ident → Bool} {E} {e : PathConditionEntry Expression}
    (he : definitions [e] = []) (h : PathInv D E) : PathInv D (E ++ [e]) := by
  rwa [PathInv, definitions_append, he, List.append_nil]

/-- Appending a definition of a name `D` does not hold of, whose right-hand side reads only names
    `D` holds of, keeps the path invariant once `D` also holds of the new name. -/
private theorem PathInv.push_def {D : Expression.Ident → Bool} {E} {x : Expression.Ident}
    {ty : Expression.Ty} {e : Expression.Expr} (hx : D x = false)
    (hr : ∀ y ty, (y, ty) ∈ LExpr.freeVars e → D y = true) (h : PathInv D E) :
    PathInv (fun n => D n || decide (n ∈ [x])) (E ++ [.varDecl x ty (.det e)]) := by
  obtain ⟨⟨hp, hs⟩, hd⟩ := h
  rw [PathInv, definitions_append]
  refine ⟨⟨List.pairwise_append.2 ⟨hp, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩,
    fun a ha ty' hm => ?_⟩, fun a ha => ?_⟩
  · obtain rfl := List.mem_singleton.1 hb
    exact ⟨fun h => Bool.false_ne_true (hx.symm.trans (h ▸ (hd a ha).1 :)),
      fun ty' hm => by simp [(hd a ha).2 _ ty' hm] at hx⟩
  · rcases List.mem_append.1 ha with ha | _ | ⟨_, ⟨⟩⟩
    · exact hs a ha ty' hm
    · simp [hr _ ty' hm] at hx
  · rcases List.mem_append.1 ha with ha | _ | ⟨_, ⟨⟩⟩
    · exact ⟨by simp [(hd a ha).1], fun y ty' hy => by simp [(hd a ha).2 y ty' hy]⟩
    · exact ⟨by simp, fun y ty' hy => by simp [hr y ty' hy]⟩

/-- The path conditions of an obligation the walk captures from the scopes `[r]`: the entries
    of `r` oldest first. -/
private theorem consume_single (r : PathCondition Expression) :
    (RevPathConditions.consume (P := Expression) ⟨[r]⟩).reverse.flatten = r.reverse := by
  simp [RevPathConditions.consume]

/-- **The extraction walk keeps definitions in order.** From one scope `r` whose entries satisfy
    the path invariant for `D`, on a def-use well formed statement list, every obligation the walk
    adds to `acc` has its definitions declared before use, when those of `acc` have. -/
private theorem extractGo_defsOrdered (ss : Statements) :
    ∀ (r : PathCondition Expression) (acc obs : Array (ProofObligation Expression))
      (D df : Expression.Ident → Bool),
      extractGo ⟨[r]⟩ ss acc = .ok obs → Block.defUseWellFormed D df ss = true →
      PathInv D r.reverse →
      (∀ ob ∈ acc, DefsOrdered (definitions ob.assumptions.reverse.flatten)) →
      ∀ ob ∈ obs, DefsOrdered (definitions ob.assumptions.reverse.flatten) := by
  match ss with
  | [] => exact fun _ _ _ _ _ h _ _ hacc => Except.ok.inj ((extractGo.eq_1 ..).symm.trans h) ▸ hacc
  | s :: rest =>
    intro r acc obs D df h hwf hinv hacc
    obtain ⟨hs, hrest⟩ := Bool.and_eq_true_iff.1 hwf
    have hmono : ∀ (l : List Expression.Ident) n, D n = true → (D n || decide (n ∈ l)) = true :=
      fun _ _ h => by simp [h]
    unfold extractGo at h
    split at h
    iterate 2
      refine extractGo_defsOrdered rest r _ obs _ df h hrest (hinv.mono (hmono _)) fun ob hob => ?_
      exact (Array.mem_push.1 hob).elim (hacc ob) (· ▸ by simpa only [consume_single] using hinv.1)
    · refine extractGo_defsOrdered rest (_ :: r) acc obs _ df h hrest ?_ hacc
      exact List.reverse_cons .. ▸ (hinv.push rfl).mono (hmono _)
    · rename_i thenSs elseSs _
      obtain ⟨thenObs, hthen, h⟩ := (Except.bind_is_ok _ _ _).1 h
      obtain ⟨elseObs, helse, h⟩ := (Except.bind_is_ok _ _ _).1 h
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hs
      rw [extractFromStatements_eq] at hthen helse
      refine extractGo_defsOrdered rest r _ obs _ df h hrest (hinv.mono (hmono _)) fun ob hob => ?_
      exact (Array.mem_append.1 hob).elim (fun h => (Array.mem_append.1 h).elim (hacc ob)
        (extractGo_defsOrdered thenSs r #[] thenObs D df hthen hs.1.2 hinv nofun ob))
        (extractGo_defsOrdered elseSs r #[] elseObs D df helse hs.2 hinv nofun ob)
    · rename_i name ty e _
      refine extractGo_defsOrdered rest (_ :: r) acc obs _ df h hrest ?_ hacc
      rw [List.reverse_cons]
      simp only [Stmt.defUseWellFormed, HasVarsImp.readVars, CmdExt.readVars,
        HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨⟨⟨hrd, -⟩, hdx⟩, -⟩ := hs
      rcases e with e | _
      · refine hinv.push_def (Bool.eq_false_iff.2 hdx) fun y ty hy => List.all_eq_true.1 hrd y ?_
        show y ∈ LExpr.LExpr.getVars e
        exact getVars_eq_freeVars_idents e ▸ List.mem_map.2 ⟨(y, ty), hy, rfl⟩
      · exact (hinv.push rfl).mono (hmono _)
    · cases h
  termination_by sizeOf ss

/-- No definitions is a list of definitions declared before use. -/
private theorem defsOrdered_nil : DefsOrdered [] := ⟨.nil, nofun⟩

/-! ## Typed definitions -/

/-- The definitions of the path-condition entries `entries`, in order, each as its variable,
    declared type and right-hand side. -/
@[expose] def typedDefinitions (entries : List (PathConditionEntry Expression)) :
    List (Expression.Ident × Expression.Ty × Expression.Expr) :=
  entries.filterMap fun
    | .varDecl x ty (.det e) => some (x, ty, e)
    | _ => none

/-- **Typed definitions.**  Every right-hand side of the definitions `ds` is typed at the declared
    type of its variable (`Core.Expression.Typed`), and every annotated occurrence, in a
    right-hand side, of the variable of an earlier definition carries that definition's declared
    type. -/
@[expose] def DefsTyped (ds : List (Expression.Ident × Expression.Ty × Expression.Expr)) : Prop :=
  (∀ d ∈ ds, Expression.Typed d.2.2 d.2.1) ∧
    ds.Pairwise fun a b => ∀ τ, (a.1, some τ) ∈ LExpr.freeVars b.2.2 → a.2.1 = .forAll [] τ

/-- The definitions of a path condition are its typed definitions without their types. -/
theorem definitions_eq_typedDefinitions (entries : List (PathConditionEntry Expression)) :
    definitions entries = (typedDefinitions entries).map fun d => (d.1, d.2.2) := by
  rw [definitions, typedDefinitions, List.map_filterMap]
  congr 1
  funext e
  rcases e with _ | ⟨x, ty, rhs | _⟩ | _ <;> rfl

/-- The typed definitions of a concatenation are those of its parts. -/
private theorem typedDefinitions_append (a b : List (PathConditionEntry Expression)) :
    typedDefinitions (a ++ b) = typedDefinitions a ++ typedDefinitions b :=
  List.filterMap_append

/-- The typing invariant of the extraction walk: the definitions of the path condition `E` so far
    are typed, and `Γ` gives each of their variables its declared type and `D` holds of it. -/
private def TyInv (Γ : VarTyping Expression) (D : Expression.Ident → Bool)
    (E : List (PathConditionEntry Expression)) : Prop :=
  DefsTyped (typedDefinitions E) ∧
    ∀ d ∈ typedDefinitions E, Γ d.1 = some d.2.1 ∧ D d.1 = true

/-- The typing invariant holds for a larger defined-names predicate. -/
private theorem TyInv.mono {Γ : VarTyping Expression} {D D' : Expression.Ident → Bool} {E}
    (hD : ∀ n, D n = true → D' n = true) (h : TyInv Γ D E) : TyInv Γ D' E :=
  ⟨h.1, fun d hd => ⟨(h.2 d hd).1, hD _ (h.2 d hd).2⟩⟩

/-- Appending an entry that is not a definition keeps the typing invariant. -/
private theorem TyInv.push {Γ : VarTyping Expression} {D : Expression.Ident → Bool} {E}
    {e : PathConditionEntry Expression} (he : typedDefinitions [e] = []) (h : TyInv Γ D E) :
    TyInv Γ D (E ++ [e]) := by
  rwa [TyInv, typedDefinitions_append, he, List.append_nil]

/-- Extending `Γ` at a name `D` does not hold of keeps `Γ`'s types of the definitions. -/
private theorem TyInv.extend {Γ : VarTyping Expression} {D : Expression.Ident → Bool} {E}
    {x : Expression.Ident} {ty : Expression.Ty} (hx : D x = false) (h : TyInv Γ D E) :
    TyInv (Γ.extend [(x, ty)]) (fun n => D n || decide (n ∈ [x])) E := by
  refine ⟨h.1, fun d hd => ⟨?_, by simp [(h.2 d hd).2]⟩⟩
  have hne : d.1 ≠ x := fun he => by simp [he ▸ (h.2 d hd).2] at hx
  rw [VarTyping.extend_of_not_mem (by simpa using hne)]
  exact (h.2 d hd).1

/-- Appending a definition of a name `D` does not hold of, whose right-hand side is typed at the
    declared type and has annotations agreeing with `Γ`, keeps the typing invariant once `Γ` is
    extended with the definition and `D` holds of its name. -/
private theorem TyInv.push_def {Γ : VarTyping Expression} {D : Expression.Ident → Bool} {E}
    {x : Expression.Ident} {ty : Expression.Ty} {e : Expression.Expr} (hx : D x = false)
    (ht : Expression.Typed e ty) (hann : Γ.annotates (HasFvars.getTypedFvars e))
    (h : TyInv Γ D E) :
    TyInv (Γ.extend [(x, ty)]) (fun n => D n || decide (n ∈ [x]))
      (E ++ [.varDecl x ty (.det e)]) := by
  have hE := TyInv.extend (ty := ty) hx h
  obtain ⟨⟨htd, hpw⟩, hΓ⟩ := h
  rw [TyInv, typedDefinitions_append]
  refine ⟨⟨fun d hd => ?_, List.pairwise_append.2 ⟨hpw, List.pairwise_singleton _ _,
    fun a ha b hb τ hm => ?_⟩⟩, fun d hd => ?_⟩
  · exact (List.mem_append.1 hd).elim (htd d) fun h => List.mem_singleton.1 h ▸ ht
  · obtain rfl := List.mem_singleton.1 hb
    have hΓa := hann a.1 _ (List.mem_filterMap.2 ⟨(a.1, some τ), hm, rfl⟩)
    exact Option.some.inj ((hΓ a ha).1.symm.trans hΓa)
  · rcases List.mem_append.1 hd with hd | _ | ⟨_, ⟨⟩⟩
    · exact hE.2 d hd
    · exact ⟨by simp [VarTyping.extend], by simp⟩

/-- **The extraction walk keeps definitions typed.** From one scope `r` whose entries satisfy
    the typing invariant for `Γ` and `D`, on a def-use well formed statement list whose
    annotations agree with `Γ` and whose `init`s are typed, every obligation the walk adds to
    `acc` has typed definitions, when those of `acc` have. -/
private theorem extractGo_defsTyped (ss : Statements) :
    ∀ (r : PathCondition Expression) (acc obs : Array (ProofObligation Expression))
      (D df : Expression.Ident → Bool) (Γ : VarTyping Expression),
      extractGo ⟨[r]⟩ ss acc = .ok obs → Block.defUseWellFormed D df ss = true →
      Block.fvarTypesWellAnnotated Γ ss → Block.initsTyped Expression.Typed ss →
      TyInv Γ D r.reverse →
      (∀ ob ∈ acc, DefsTyped (typedDefinitions ob.assumptions.reverse.flatten)) →
      ∀ ob ∈ obs, DefsTyped (typedDefinitions ob.assumptions.reverse.flatten) := by
  match ss with
  | [] => exact fun _ _ _ _ _ _ h _ _ _ _ hacc =>
      Except.ok.inj ((extractGo.eq_1 ..).symm.trans h) ▸ hacc
  | s :: rest =>
    rintro r acc obs D df Γ h hwf ⟨hWs, hWr⟩ ⟨hTs, hTr⟩ hinv hacc
    obtain ⟨hs, hrest⟩ := Bool.and_eq_true_iff.1 hwf
    have hmono : ∀ (l : List Expression.Ident) n, D n = true → (D n || decide (n ∈ l)) = true :=
      fun _ _ h => by simp [h]
    unfold extractGo at h
    split at h
    iterate 2
      refine extractGo_defsTyped rest r _ obs _ df Γ h hrest hWr hTr (hinv.mono (hmono _))
        fun ob hob => ?_
      exact (Array.mem_push.1 hob).elim (hacc ob) (· ▸ by simpa only [consume_single] using hinv.1)
    · refine extractGo_defsTyped rest (_ :: r) acc obs _ df Γ h hrest hWr hTr ?_ hacc
      exact List.reverse_cons .. ▸ (hinv.push rfl).mono (hmono _)
    · rename_i thenSs elseSs _
      obtain ⟨thenObs, hthen, h⟩ := (Except.bind_is_ok _ _ _).1 h
      obtain ⟨elseObs, helse, h⟩ := (Except.bind_is_ok _ _ _).1 h
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hs
      rw [extractFromStatements_eq] at hthen helse
      refine extractGo_defsTyped rest r _ obs _ df Γ h hrest hWr hTr (hinv.mono (hmono _))
        fun ob hob => ?_
      exact (Array.mem_append.1 hob).elim (fun h => (Array.mem_append.1 h).elim (hacc ob)
        (extractGo_defsTyped thenSs r #[] thenObs D df Γ hthen hs.1.2 hWs.2.1 hTs.1 hinv nofun ob))
        (extractGo_defsTyped elseSs r #[] elseObs D df Γ helse hs.2 hWs.2.2 hTs.2 hinv nofun ob)
    · rename_i name ty e _
      refine extractGo_defsTyped rest (_ :: r) acc obs _ df _ h hrest hWr hTr ?_ hacc
      rw [List.reverse_cons]
      simp only [Stmt.defUseWellFormed, HasVarsImp.readVars, CmdExt.readVars,
        HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨⟨⟨-, -⟩, hdx⟩, -⟩ := hs
      rcases e with e | _
      · exact hinv.push_def (Bool.eq_false_iff.2 hdx) hTs fun z T hz => hWs z T (by
          simpa [HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars, Cmd.getTypedVars,
            ExprOrNondet.getTypedVars] using hz)
      · exact (TyInv.extend (Bool.eq_false_iff.2 hdx) hinv).push rfl
    · cases h
  termination_by sizeOf ss

/-- **Definitions extracted from a typed statement list are typed.** From global facts `g`
    without definitions, every obligation `extractFromStatements` returns for a def-use well
    formed statement list `ss` whose annotations agree with a typing `Γ` and whose `init`s have
    right-hand sides typed at their declared types has typed definitions (`DefsTyped`): each
    right-hand side is typed at its declared type, and each annotated read of the variable of an
    earlier definition carries that definition's declared type. -/
theorem extractFromStatements_defsTyped {g : PathCondition Expression} {ss : Statements}
    {obs : Array (ProofObligation Expression)} {D df : Expression.Ident → Bool}
    {Γ : VarTyping Expression}
    (h : extractFromStatements ⟨[g]⟩ ss = .ok obs) (hg : definitions g.reverse = [])
    (hwf : Block.defUseWellFormed D df ss = true) (hW : Block.fvarTypesWellAnnotated Γ ss)
    (hT : Block.initsTyped Expression.Typed ss) :
    ∀ ob ∈ obs, DefsTyped (typedDefinitions ob.assumptions.reverse.flatten) := by
  have hg' : typedDefinitions g.reverse = [] := by simpa [definitions_eq_typedDefinitions] using hg
  exact extractGo_defsTyped ss g #[] obs D df Γ (by simpa using h) hwf hW hT
    ⟨⟨by simp [hg'], by simp [hg']⟩, by simp [hg']⟩ nofun

/-- **Definitions extracted from a statement list are declared before use.** From global facts
    `g` without definitions, every obligation `extractFromStatements` returns for a def-use well
    formed statement list `ss` has the definitions of its path condition, oldest first, declared
    before use with distinct variables. -/
theorem extractFromStatements_defsOrdered {g : PathCondition Expression} {ss : Statements}
    {obs : Array (ProofObligation Expression)} {D df : Expression.Ident → Bool}
    (h : extractFromStatements ⟨[g]⟩ ss = .ok obs) (hg : definitions g.reverse = [])
    (hwf : Block.defUseWellFormed D df ss = true) :
    ∀ ob ∈ obs, DefsOrdered (definitions ob.assumptions.reverse.flatten) :=
  extractGo_defsOrdered ss g #[] obs D df (by simpa using h) hwf
    ⟨by simpa [hg] using defsOrdered_nil, by simp [hg]⟩ nofun

/-- **A property of every extracted obligation.** A property `P` of obligations holds of every
    obligation `extractObligations p` returns when it holds of every obligation
    `extractFromStatements` returns, from global facts without definitions, for the statements of
    a procedure of `p`, and of every obligation whose path condition is such global facts. -/
private theorem extractObligations_inv {p : Program} {obs : ProofObligations Expression}
    (P : ProofObligation Expression → Prop) (h : extractObligations p = .ok obs)
    (hss : ∀ q md ss (g : PathCondition Expression) obs, Decl.proc q md ∈ p.decls →
      procedureStatements q = .ok ss → definitions g.reverse = [] →
      extractFromStatements ⟨[g]⟩ ss = .ok obs → ∀ ob ∈ obs, P ob)
    (hg : ∀ (g : PathCondition Expression) (ob : ProofObligation Expression),
      definitions g.reverse = [] → ob.assumptions = RevPathConditions.consume ⟨[g]⟩ → P ob) :
    ∀ ob ∈ obs, P ob := by
  simp only [extractObligations] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  simp only [pure, Except.pure] at h
  obtain ⟨res, hres, h⟩ := (Except.bind_is_ok _ _ _).1 h
  suffices hf : ∀ (ds : List Decl) acc, (∀ q md, Decl.proc q md ∈ ds → Decl.proc q md ∈ p.decls) →
      definitions acc.1.reverse = [] → (∀ ob ∈ acc.2, P ob) →
      ds.foldlM extractDecl acc = .ok res → ∀ ob ∈ res.2, P ob from
    Except.ok.inj h ▸ hf _ _ (fun _ _ h => h) rfl (by simp) hres
  intro ds
  induction ds with
  | nil => exact fun _ _ _ hacc h => Except.ok.inj h ▸ hacc
  | cons d ds ih =>
    rintro ⟨g, allObs⟩ hm hg0 hacc h
    obtain ⟨acc', hd, h⟩ := (Except.bind_is_ok _ _ _).1 h
    have hg' : definitions acc'.1.reverse = [] ∧ ∀ ob ∈ acc'.2, P ob := by
      dsimp only [extractDecl] at hd
      split at hd
      iterate 2
        exact Except.ok.inj hd ▸ ⟨by rw [List.reverse_cons, definitions_append, hg0]; rfl, hacc⟩
      iterate 2
        split at hd <;> cases hd
        exact ⟨hg0, hacc⟩
      · rename_i q md
        obtain ⟨ss, hs, hd⟩ := (Except.bind_is_ok _ _ _).1 hd
        obtain ⟨obs, ho, hd⟩ := (Except.bind_is_ok _ _ _).1 hd
        refine Except.ok.inj hd ▸ ⟨hg0, fun ob hob => (Array.mem_append.1 hob).elim (hacc ob) ?_⟩
        exact hss q md ss g obs (hm q md List.mem_cons_self) hs hg0 ho ob
      · refine Except.ok.inj hd ▸ ⟨hg0, fun ob hob => (Array.mem_push.1 hob).elim (hacc ob) ?_⟩
        exact (· ▸ hg g _ hg0 rfl)
      · exact Except.ok.inj hd ▸ ⟨hg0, hacc⟩
    exact ih acc' (fun q md h => hm q md (List.mem_cons_of_mem _ h)) hg'.1 hg'.2 h

/-- **Extracted definitions are declared before use.** When the statement list extraction reads
    from every procedure of `p` (`procedureStatements`) is def-use well formed from some
    defined-names predicate (as the `defUseOk` field of the initial-environment gate
    `Imperative.Logic.BlockInitEnvWF` says of an entry environment), every obligation that
    `extractObligations p` returns has the definitions of its path condition, oldest first,
    declared before use with distinct variables (`DefsOrdered`): no right-hand side reads its
    own variable or the variable of a later definition. -/
theorem extractObligations_defsOrdered {p : Program} {obs : ProofObligations Expression}
    (h : extractObligations p = .ok obs)
    (hwf : ∀ q md ss, Decl.proc q md ∈ p.decls → procedureStatements q = .ok ss →
      ∃ D df, Block.defUseWellFormed D df ss = true) :
    ∀ ob ∈ obs, DefsOrdered (definitions ob.assumptions.reverse.flatten) :=
  extractObligations_inv _ h (fun q md ss _ _ hq hss hg hx =>
    (hwf q md ss hq hss).elim fun _ ⟨_, hd⟩ => extractFromStatements_defsOrdered hx hg hd)
    fun _ _ hg hob => by simpa only [hob, consume_single, hg] using defsOrdered_nil

/-- **Extracted definitions are declared before use, from the gate.**
    `extractObligations_defsOrdered` when the statement list extraction reads from every
    procedure of `p` has an entry environment satisfying the initial-environment gate
    `Imperative.Logic.BlockInitEnvWF`, whose `defUseOk` field is the def-use well-formedness it
    needs. -/
theorem extractObligations_defsOrdered_of_gate {p : Program} {obs : ProofObligations Expression}
    (h : extractObligations p = .ok obs)
    (hwf : ∀ q md ss, Decl.proc q md ∈ p.decls → procedureStatements q = .ok ss →
      ∃ params ρ, Imperative.Logic.BlockInitEnvWF params ss ρ) :
    ∀ ob ∈ obs, DefsOrdered (definitions ob.assumptions.reverse.flatten) :=
  extractObligations_defsOrdered h fun q md ss hq hss =>
    (hwf q md ss hq hss).elim fun _ ⟨_, hg⟩ => ⟨_, _, hg.defUseOk⟩

/-- **Extracted definitions are typed.** When the statement list extraction reads from every
    procedure of `p` (`procedureStatements`) is def-use well formed, has annotations agreeing
    with some typing and has `init`s typed at their declared types, every obligation that
    `extractObligations p` returns has typed definitions (`DefsTyped`). -/
theorem extractObligations_defsTyped {p : Program} {obs : ProofObligations Expression}
    (h : extractObligations p = .ok obs)
    (hwf : ∀ q md ss, Decl.proc q md ∈ p.decls → procedureStatements q = .ok ss →
      ∃ D df Γ, Block.defUseWellFormed D df ss = true ∧ Block.fvarTypesWellAnnotated Γ ss ∧
        Block.initsTyped Expression.Typed ss) :
    ∀ ob ∈ obs, DefsTyped (typedDefinitions ob.assumptions.reverse.flatten) := by
  refine extractObligations_inv _ h (fun q md ss _ _ hq hss hg hx => ?_) fun g _ hg hob => ?_
  · obtain ⟨_, _, _, hd, hW, hT⟩ := hwf q md ss hq hss
    exact extractFromStatements_defsTyped hx hg hd hW hT
  · have h0 : typedDefinitions g.reverse = [] := by simpa [definitions_eq_typedDefinitions] using hg
    simp [hob, consume_single, h0, DefsTyped]

/-- The entry gates of the WP pipeline's input `mid` for the factory of the pipeline on `mid`
    (`wpFactory moreFns mid`), at the gate parameters `params`: every procedure of `mid` with a
    structured body `lay` has `lay` in tree form, an assertion or a cover in every `ite` arm, each
    of its free variables among the procedure's parameters (`Procedure.entryParams`) and their
    aliases (`Procedure.oldAliases`) or neither assigned nor defined in `lay` (as the free
    variables of an obligation unit, which keep their own names through the SSA phase), and an
    entry environment `ρ₀` satisfying the initial-environment gate of `lay` related by the SSA
    phase's entry renaming to an environment `ρ₀'` (`WP.SSAEntryRel`, for the names the SSA phase
    avoids in `mid`). -/
@[expose] def WPPipelineEntryGates (params : Core.Logic.InitEnvWFParams)
    (moreFns : Lambda.Factory CoreLParams) (mid : Program) : Prop :=
  ∀ fac, wpFactory moreFns mid = .ok fac →
    ∀ q md lay opq, Decl.proc q md ∈ mid.decls → q.body = .structured lay opq →
      Block.treeForm lay = true ∧ Block.armsHaveChecks lay = true ∧
      (∀ x ∈ Block.freeVars lay, x ∈ q.entryParams ∨ x ∈ q.oldAliases.map (·.1) ∨
        x ∉ Block.modifiedOrDefinedVars lay false) ∧
      ∃ ρ₀ ρ₀', WP.SSAEntryRel fac
          (Imperative.WP.IdSet.ofList
            (WP.avoidOf [] (fac.toArray.toList.map (·.name) ++ WP.declNames mid)))
          q.paramTys q.entryParams q.oldAliases lay ρ₀ ρ₀' ∧
        Core.Logic.BlockInitEnvWF params lay ρ₀

/-- The SSA phase keeps the datatypes a program declares, so the factory of the WP pipeline on
    its output is the one on its input. -/
private theorem wpFactory_ssaProgram {fac moreFns : Lambda.Factory CoreLParams}
    {R : List Expression.Ident} {mid p₁ : Program} (h : WP.ssaProgram fac R mid = .ok p₁) :
    wpFactory moreFns p₁ = wpFactory moreFns mid := by
  obtain ⟨decls, hdecls, h⟩ := (Except.bind_is_ok _ _ _).1 h
  cases h
  suffices hd : ∀ (ds : List Decl) (decls : List (Option Decl)), ds.mapM (fun d => match d with
      | .proc q _ => WP.ssaProc fac (Imperative.WP.IdSet.ofList
          (WP.avoidOf [] (R ++ WP.declNames mid))) q
      | d => pure (some d)) = Except.ok decls →
      (decls.filterMap id).filterMap (fun | .type (.data b) _ => some b | _ => none) =
        ds.filterMap (fun | .type (.data b) _ => some b | _ => none) by
    have hpd : programDatatypes { decls := decls.filterMap id } = programDatatypes mid :=
      hd _ _ hdecls
    simp only [wpFactory, hpd]
  intro ds
  induction ds with
  | nil => exact fun _ h => Except.ok.inj h ▸ rfl
  | cons d rest ih =>
    intro decls h
    rw [List.mapM_cons] at h
    obtain ⟨d', hd', h⟩ := (Except.bind_is_ok _ _ _).1 h
    obtain ⟨ds', hds', h⟩ := (Except.bind_is_ok _ _ _).1 h
    cases h
    rcases d with _ | _ | _ | _ | ⟨q, md⟩ | _
    all_goals first
      | (cases hd'; simp only [List.filterMap_cons, id, ih _ hds']) | skip
    simp only [WP.ssaProc, bind, Except.bind] at hd'
    split at hd' <;> try cases hd'
    · split at hd' <;> cases hd'
      simp [Decl.obligationProc, ih _ hds']
    · simp [ih _ hds']

end Core.ObligationExtraction

end -- public section
