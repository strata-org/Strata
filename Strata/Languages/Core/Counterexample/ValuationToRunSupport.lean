/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Util.ExceptProps
public import Strata.Languages.Core.Counterexample.ValuationToRunProducer
public import Strata.Languages.Core.Counterexample.Model
public import Strata.Languages.Core.Counterexample.ModelToValuation
public import Strata.Languages.Core.Counterexample.ValuationToRun
public import Strata.Languages.Core.FactoryWF
public import Strata.Languages.Core.ObligationExtraction
public import Strata.DL.Imperative.Counterexample.Run
public import Strata.DL.Imperative.Counterexample.BackLink
public import Strata.DL.Imperative.Counterexample.Valuation
public import Strata.DL.Imperative.EvalContextProps
import all Strata.Languages.Core.Counterexample.ValuationToRunProducer
import all Strata.Languages.Core.Counterexample.Model
import all Strata.Languages.Core.Counterexample.ModelToValuation
import all Strata.Languages.Core.Counterexample.ValuationToRun
import all Strata.Languages.Core.InterpreterEval
import all Strata.Languages.Core.Interpreter
import all Strata.Languages.Core.ObligationExtraction
import Strata.Languages.Core.ObligationExtractionProps
import all Strata.DL.Imperative.Counterexample.Run
import all Strata.DL.Imperative.Counterexample.BackLink
import all Strata.DL.Imperative.Counterexample.Valuation
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExprEvalProps
public import Strata.Languages.Core.Counterexample.ValuationToRunSupportA
import all Strata.Languages.Core.Counterexample.ValuationToRunSupportA
import Strata.DL.Imperative.Counterexample.Tactics
import all Strata.DL.Lambda.LExprEvalFuelProps

/-! # Engine-independent support lemmas for the `(b)→(a)` replay, part 2

Facts that relate a level-`(b)` counterexample (a valuation of an extracted proof obligation) to
the store a replay of the source program starts from, without mentioning the replay engine:
the per-entry content of a genuine verdict, agreement of the `valuationToEnv` store with the
valuation on the input names, single static assignment of the variable definitions of every
extracted obligation, declarative-to-operational evaluation transfer, frame facts for the
`extendWithVarDecls'` threading, and the domain-only dependence of `WellScopedObl`.

Key theorems: `valuationToEnv_entry_agrees`, `eval_transfer_mono`, `extractGoLinked_pc_prefix`,
`extractLinked_all_ssa`, `WellScopedObl_dom_congr`.

Key definitions: `allVarNames` (names bound by the variable definitions of a path-condition
set), `cel_ssaOK` (selected names distinct and disjoint from the
inputs). -/

namespace Core
open _root_.Lambda Imperative

public section
open Imperative

/-! ### Decomposition of a genuine verdict

A `.genuine` verdict reduces the assumptions and the goal under the declarative store, the
valuation with the variable definitions threaded onto it; it is unpacked into one fact per
assumption and one for the goal. -/

/-- A conjunction of two Boolean reductions (`BReduction.and`) is `.isTrue` iff both
    conjuncts are. -/
private theorem BReduction.and_eq_isTrue {a b : Imperative.BReduction} :
    a.and b = .isTrue ↔ a = .isTrue ∧ b = .isTrue := by
  cases a <;> cases b <;> simp [BReduction.and]

/-- **`BReduction.and`-fold decomposition.**  If a left fold of `BReduction.and`
    from `init` reduces to `.isTrue`, then `init` and every element's contribution
    `f e` are `.isTrue`. -/
theorem and_foldl_isTrue_forall {α : Type} (f : α → Imperative.BReduction) :
    ∀ (l : List α) (init : Imperative.BReduction),
      l.foldl (fun acc e => acc.and (f e)) init = .isTrue →
      init = .isTrue ∧ ∀ e ∈ l, f e = .isTrue := fun l => by
  induction l <;> grind [BReduction.and_eq_isTrue]

/-! ### Restricted store agreement

Wherever the valuation `store` binds an input, the store `valuationToEnv` builds holds the same
value; at an input `store` leaves unbound it holds a type default. -/

/-- An invariant preserved by every successful step of an `Except` `forIn` that only yields holds of
    its result. -/
private theorem cel_forIn_inv {α β ε : Type} (I : β → Prop) (f : α → β → Except ε (ForInStep β))
    (hf : ∀ a b s, I b → f a b = .ok s → ∃ b', s = .yield b' ∧ I b') :
    ∀ (l : List α) (acc out : β), I acc → forIn l acc f = .ok out → I out := fun l => by
  induction l <;> intro acc out hacc h <;>
    simp only [List.forIn_nil, List.forIn_cons, Except.bind_is_ok, Except.pure_is_ok] at h <;> grind

/-- **`valuationToEnv` env facts.**  A successful `valuationToEnv` produces an `env`
    whose factory is the given one and whose store holds only canonical values
    (`WellFormedStore`). -/
theorem valuationToEnv_env_facts
    (factory : @Lambda.Factory CoreLParams)
    (unit : PassiveUnit) (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink)
    (store : RStore Expression)
    (env : IEnv Expression) (oracle : OracleSeed)
    (henv : valuationToEnv factory unit obligation link store = .ok (env, oracle)) :
    env.factory = factory ∧ RWellFormedStore env.store.get factory := by
  obtain ⟨_, hloop, -, -, rfl⟩ := cel_vte henv
  refine ⟨rfl, fun x w h => ?_⟩
  simp only [IStore.get_ofStore, Option.map_eq_some_iff, Prod.exists, exists_eq_right] at h
  obtain ⟨_, h⟩ := h
  exact cel_forIn_inv (fun r => ∀ k w, (k, w) ∈ r → Lambda.LExpr.isValue factory w = true) _
    (fun _ _ _ hI h => by (repeat' split at h) <;> cases h <;> grind) _ [] _ nofun hloop _ _
    (List.mem_of_find?_eq_some h)

/-- **Restricted entry agreement.**  For a successful `valuationToEnv`, at every input name
    `x` of the passive unit that the valuation `store` binds to `v`, the operational store
    `env.store` also binds `x` to `v`: `valuationToEnv` copies present input values
    verbatim and defaults only the absent ones. -/
theorem valuationToEnv_entry_agrees
    (factory : @Lambda.Factory CoreLParams)
    (unit : PassiveUnit) (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink)
    (store : RStore Expression)
    (env : IEnv Expression) (oracle : OracleSeed)
    (henv : valuationToEnv factory unit obligation link store = .ok (env, oracle)) :
    ∀ x, x ∈ unit.inputs.map (·.1) → ∀ v, store x = some v → env.store.get x = some v := by
  obtain ⟨bindings, hloop, hkeys, -, rfl⟩ := cel_vte henv
  have hval := cel_forIn_inv (fun r => ∀ k w, (k, w) ∈ r → store k = some w ∨ store k = none) _
    (fun _ _ _ hI h => by (repeat' split at h) <;> cases h <;> grind) _ [] _ nofun hloop
  intro x
  simp only [IStore.get_ofStore]
  cases hfind : bindings.find? (·.1 == x) <;> grind

/-- An entry of the flattened path conditions stays one after another entry is added. -/
private theorem mem_flatten_addEntry (ps : Imperative.PathConditions Expression)
    (e x : Imperative.PathConditionEntry Expression)
    (hx : x ∈ ps.flatten) : x ∈ (ps.addEntry e).flatten := by
  cases ps <;> grind [PathConditions.addEntry]

/-- **Path-condition entries are assumptions.**  When the extraction walk `extractGoLinked`,
    run from path conditions `pc` and any accumulator `acc`, emits the pair
    `(obligation, link)` and that pair is not already in `acc`, every entry of the
    consumed path conditions `pc.consume` is an entry of `obligation.assumptions`. -/
theorem extractGoLinked_pc_entries_subset
    (entry : Statements)
    (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink) :
    ∀ (pc : Imperative.RevPathConditions Expression)
      (events : List ObligationExtraction.ExtractReplayEvent) (ss : Statements)
      (acc arr : Array ObligationExtraction.LinkedObligation),
      ObligationExtraction.extractGoLinked entry pc events ss acc = .ok arr →
      (obligation, link) ∈ arr.toList →
      (obligation, link) ∉ acc.toList →
      ∀ x ∈ (pc.consume).flatten, x ∈ obligation.assumptions.flatten := by
  intro pc events ss acc arr h
  induction pc, events, ss, acc using ObligationExtraction.extractGoLinked_induct entry
      generalizing arr <;>
    simp_all +zetaDelta only [ObligationExtraction.extractGoLinked_nil,
      ObligationExtraction.extractGoLinked_assert, ObligationExtraction.extractGoLinked_cover,
      ObligationExtraction.extractGoLinked_assume, ObligationExtraction.extractGoLinked_ite,
      ObligationExtraction.extractGoLinked_init, ObligationExtraction.extractGoLinked_unsupported,
      Except.bind_is_ok, Array.mem_toList_iff, Array.toList_append, List.mem_append,
      List.not_mem_nil, not_false_eq_true, forall_const, not_or, and_imp]
  case case5 ihThen ihElse ihRest =>
    obtain ⟨thenObs, hthen, elseObs, helse, hrest⟩ := h
    intro hmem hfresh
    by_cases hinThen : (obligation, link) ∈ thenObs
    · exact ihThen _ hthen hinThen
    by_cases hinElse : (obligation, link) ∈ elseObs
    · exact ihElse _ helse hinElse
    exact ihRest _ _ _ hrest hmem hfresh hinThen hinElse
  all_goals grind +splitImp [RevPathConditions.consume_prepend, mem_flatten_addEntry]

/-- Names a selector `g` picks from the entries of a path-condition set. -/
def cel_names (g : Imperative.PathConditionEntry Expression → List Expression.Ident)
    (pcs : Imperative.PathConditions Expression) : List Expression.Ident :=
  pcs.flatten.flatMap g

/-- The names `g` picks from `pcs` are pairwise distinct and disjoint from `inputs`. -/
def cel_ssaOK (g : Imperative.PathConditionEntry Expression → List Expression.Ident)
    (inputs : List Expression.Ident) (pcs : Imperative.PathConditions Expression) : Prop :=
  (cel_names g pcs).Nodup ∧ ∀ n ∈ cel_names g pcs, n ∉ inputs

/-- Prepending an entry `e` to reversed path conditions `pc` adds the names the selector `g`
    picks from `e` to those it picks from `pc.consume`: distinctness and membership of the
    picked names are those of `g e ++` the old names. -/
private theorem cel_prepend (g : Imperative.PathConditionEntry Expression → List Expression.Ident)
    (pc : Imperative.RevPathConditions Expression) (e : Imperative.PathConditionEntry Expression) :
    ((cel_names g (pc.prepend e).consume).Nodup ↔ (g e ++ cel_names g pc.consume).Nodup) ∧
      ∀ n, n ∈ cel_names g (pc.prepend e).consume ↔ n ∈ g e ∨ n ∈ cel_names g pc.consume := by
  have hperm : (cel_names g (pc.prepend e).consume).Perm (g e ++ cel_names g pc.consume) := by
    rcases pc with ⟨_ | _⟩ <;> simp [cel_names, RevPathConditions.prepend,
      RevPathConditions.consume, List.perm_append_comm_assoc]
  exact ⟨hperm.nodup_iff, fun n => hperm.mem_iff.trans List.mem_append⟩

/-- The extraction walk `extractGoLinked` keeps the names a selector `g` of
    variable-definition names picks pairwise distinct and disjoint from `inputs`
    (`cel_ssaOK`).  Assumptions: the program passes `Block.readsDefined D` (every read is of
    a name defined earlier, and no definition rebinds a defined name) and `Block.nondetIteLast`
    (a nondeterministic `.ite` is last in its list); `inputs ⊆ D`; the names picked from the
    starting path conditions are distinct, in `D` and not inputs; every pair of the starting
    accumulator already satisfies `cel_ssaOK`. -/
private theorem cel_ssa_walk (g : Imperative.PathConditionEntry Expression → List Expression.Ident)
    (hg : ∀ e, g e = [] ∨ ∃ n ty v, e = .varDecl n ty v ∧ g e = [n])
    {inputs : List Expression.Ident} {entry : Statements}
    {pc : Imperative.RevPathConditions Expression}
    {events : List ObligationExtraction.ExtractReplayEvent} {ss : Statements}
    {acc arr : Array ObligationExtraction.LinkedObligation} (D : List Expression.Ident)
    (h : ObligationExtraction.extractGoLinked entry pc events ss acc = .ok arr)
    (hw : Block.readsDefined D ss = true) (hs : Block.nondetIteLast ss = true)
    (hi : ∀ x ∈ inputs, x ∈ D)
    (hn : (cel_names g pc.consume).Nodup ∧ (∀ n ∈ cel_names g pc.consume, n ∈ D ∧ n ∉ inputs))
    (ha : ∀ p ∈ acc.toList, cel_ssaOK g inputs p.1.assumptions) :
    ∀ p ∈ arr.toList, cel_ssaOK g inputs p.1.assumptions := by
  induction pc, events, ss, acc using ObligationExtraction.extractGoLinked_induct entry
      generalizing arr D <;>
    simp only [ObligationExtraction.extractGoLinked_nil,
      ObligationExtraction.extractGoLinked_assert, ObligationExtraction.extractGoLinked_cover,
      ObligationExtraction.extractGoLinked_assume, ObligationExtraction.extractGoLinked_init,
      Block.readsDefined, Block.nondetIteLast, Bool.and_eq_true] at h hw hs
  case case5 =>
    rw [ObligationExtraction.extractGoLinked_ite] at h
    obtain ⟨_, hthen, h⟩ := (Except.bind_is_ok _ _ _).1 h
    obtain ⟨_, helse, h⟩ := (Except.bind_is_ok _ _ _).1 h
    rw [List.isEmpty_iff.1 hs.1.1, ObligationExtraction.extractGoLinked_nil] at h
    grind
  case case7 => simp [ObligationExtraction.extractGoLinked_unsupported, *] at h
  case case6 =>
    rename_i n _ e _ _ ih
    cases e <;> apply ih (n :: D) h <;> grind [Block.readsDefined, cel_prepend]
  case case4 =>
    rename_i ih
    apply ih D h <;> grind [cel_prepend]
  all_goals grind [cel_ssaOK]

/-- **Restricted declarative-to-operational evaluation transfer.**  On a well-formed, closed
    factory, if an expression `e` evaluates to `b` in a declarative store `declStore`, the
    operational store `opStore` reproduces every binding `declStore` holds at a free
    variable of `e`, and those bindings are closed terms (as canonical values are), then `e`
    evaluates to the same `b` in `opStore`.  Bindings of `declStore` at names `e` does not
    read, and names `declStore` leaves unbound, are irrelevant. -/
theorem eval_transfer_mono
    (factory : @Lambda.Factory CoreLParams)
    (hWF : Lambda.FactoryWF factory)
    (declStore opStore : RStore Expression) (e b : Expression.Expr)
    (hclosed : ∀ x ∈ HasFvars.getFvars (P := Expression) e, ∀ w,
        declStore x = some w → Lambda.LExpr.LExpr.getVars w = [])
    (hmatch : ∀ x ∈ HasFvars.getFvars (P := Expression) e, ∀ w,
        declStore x = some w → opStore x = some w)
    (hdecl : Lambda.LExpr.evalFully factory declStore e = some b) :
    Lambda.LExpr.evalFully factory opStore e = some b := by
  let σ0 : RStore Expression := fun x => if x ∈ HasFvars.getFvars e then declStore x else none
  have hcongr := evalFully_env_congr (fun a b h => by cases a; cases b; grind) factory declStore
    σ0 hWF (fun x v h => by grind) e (fun x hx => (ite_eq_left hx).symm)
  obtain ⟨n, hn, -⟩ := evalFully_some_exists _ _ _ _ (hcongr.symm.trans hdecl)
  exact evalFully_of_value_true _ _ _ n _ (eval_frame _ σ0 _ (fun x w h => by grind) n e b hn)

/-- **Single scope.**  Folding `addEntry` over a path-condition set with at most one
    scope gives a set with at most one scope. -/
theorem foldl_addEntry_length_le_one
    (extras : List (Imperative.PathConditionEntry Expression)) :
    ∀ (acc : Imperative.PathConditions Expression), acc.length ≤ 1 →
      (extras.foldl (fun ps e => Imperative.PathConditions.addEntry ps e) acc).length ≤ 1 := by
  induction extras with
  | nil => exact fun _ h => h
  | cons e extras ih => exact fun acc h => ih _ (by cases acc <;> simp_all!)

/-- Name bound by a variable definition of either kind (det or nondet) in a path-condition
    entry. -/
def allEntry (e : Imperative.PathConditionEntry Expression) : List CoreIdent :=
  match e with
  | .varDecl n _ _ => [n]
  | _ => []

/-- Names bound by all (det or nondet) variable definitions in a path-condition set. -/
def allVarNames (pcs : Imperative.PathConditions Expression) : List CoreIdent :=
  pcs.flatten.flatMap allEntry

/-- A root path condition (`RootPc`: at most one scope and no variable definition) binds no
    variable-definition name. -/
private theorem allVarNames_eq_nil_of_rootPc {pc0 : Imperative.RevPathConditions Expression}
    (h : RootPc pc0) : allVarNames pc0.consume = [] := List.flatMap_eq_nil_iff.2 fun e he => by
  cases e <;> simp! only [allEntry, List.cons_ne_self]
  exact h.2 _ he _ _ _ rfl

/-- `allVarNames` of an `addEntry` is (up to order) the entry's name prepended. -/
theorem allVarNames_addEntry_perm (ps : Imperative.PathConditions Expression)
    (e : Imperative.PathConditionEntry Expression) :
    (allVarNames (ps.addEntry e)).Perm (allEntry e ++ allVarNames ps) := by
  cases ps <;> simp [allVarNames, PathConditions.addEntry, List.perm_append_comm_assoc]

/-! ### Domain-only congruence for `WellScopedObl` -/

/-- Two stores that are defined at exactly the same names agree on `RStore.isDefined` for
    any variable list (`RStore.isDefined` only reads which names are bound). -/
private theorem isDefined_dom_congr (σ₁ σ₂ : RStore Expression) (vs : List CoreIdent)
    (h : ∀ x, (σ₁ x).isSome = (σ₂ x).isSome) : RStore.isDefined σ₁ vs ↔ RStore.isDefined σ₂ vs := by
  grind [RStore.isDefined]

/-- Two stores that are defined at exactly the same names are simultaneously
    undefined at any given name. -/
private theorem eqNone_dom_congr (σ₁ σ₂ : RStore Expression) (nm : CoreIdent)
    (h : ∀ x, (σ₁ x).isSome = (σ₂ x).isSome) : (σ₁ nm = none) ↔ (σ₂ nm = none) := by
  grind [Option.not_isSome_iff_eq_none]

/-- Point-updating two same-domain stores at one name — with possibly different
    values — leaves them defined at exactly the same names (the update makes `nm`
    defined in both, and changes nothing else). -/
theorem update_dom_congr (σ₁ σ₂ : RStore Expression) (nm : CoreIdent)
    (a b : Expression.Expr) (h : ∀ x, (σ₁ x).isSome = (σ₂ x).isSome) :
    ∀ x, ((RStore.update σ₁ nm a) x).isSome = ((RStore.update σ₂ nm b) x).isSome := by
  grind [RStore.update]

/-- **`WellScopedObl` is domain-only.**  Two stores that are defined at exactly the
    same names satisfy `WellScopedObl` (every statement's reads are defined in the store
    threaded up to it) on the same statement lists: the predicate reads a store only
    through `RStore.isDefined` and the freshness test `σ name = none`. -/
theorem WellScopedObl_dom_congr :
    ∀ (σ₁ : RStore Expression) (ss : Statements) (σ₂ : RStore Expression),
      (∀ x, (σ₁ x).isSome = (σ₂ x).isSome) →
      (WellScopedObl σ₁ ss ↔ WellScopedObl σ₂ ss) := by
  intro σ₁ ss
  induction σ₁, ss using WellScopedObl.induct <;> intro σ₂ h <;> grind [WellScopedObl,
    isDefined_dom_congr _ _ _ h, eqNone_dom_congr _ _ _ h, update_dom_congr _ _ _ _ _ h]

/-! ### Single-scope structure of the extraction's `RevPathConditions` -/

/-- Prepending an entry keeps a single-scope `RevPathConditions` single-scope
    (the extraction only ever grows the one open scope). -/
theorem prepend_scopes_length_le_one
    (pc : Imperative.RevPathConditions Expression) (e : Imperative.PathConditionEntry Expression)
    (h : pc.scopes.length ≤ 1) : (pc.prepend e).scopes.length ≤ 1 := by
  grind [RevPathConditions.prepend]

/-- For a single-scope `RevPathConditions`, prepending an entry appends it, in
    program order, to the flattened consumed path conditions:
    `(pc.prepend e).consume.flatten = pc.consume.flatten ++ [e]`. -/
theorem consume_flatten_prepend_single
    (pc : Imperative.RevPathConditions Expression) (e : Imperative.PathConditionEntry Expression)
    (h : pc.scopes.length ≤ 1) :
    (pc.prepend e).consume.flatten = pc.consume.flatten ++ [e] := by
  rcases pc with ⟨_ | ⟨_, _ | _⟩⟩ <;> simp_all! [RevPathConditions.consume]

/-- **Path conditions are a prefix of the assumptions.**  When the extraction walk
    `extractGoLinked`, run from single-scope path conditions `pc` and an accumulator `acc`,
    emits the pair `(obligation, link)` and that pair is not already in `acc`, the
    flattened `pc.consume` is a prefix of the flattened `obligation.assumptions`: the
    entries keep their program-order position inside the emitted scope. -/
theorem extractGoLinked_pc_prefix
    (entry : Statements) (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink) :
    ∀ (pc : Imperative.RevPathConditions Expression)
      (events : List ObligationExtraction.ExtractReplayEvent) (ss : Statements)
      (acc arr : Array ObligationExtraction.LinkedObligation),
      pc.scopes.length ≤ 1 →
      ObligationExtraction.extractGoLinked entry pc events ss acc = .ok arr →
      (obligation, link) ∈ arr.toList →
      (obligation, link) ∉ acc.toList →
      pc.consume.flatten <+: obligation.assumptions.flatten := by
  intro pc events ss acc arr hsingle h
  induction pc, events, ss, acc using ObligationExtraction.extractGoLinked_induct entry
      generalizing arr <;>
    simp_all +zetaDelta only [ObligationExtraction.extractGoLinked_nil,
      ObligationExtraction.extractGoLinked_assert, ObligationExtraction.extractGoLinked_cover,
      ObligationExtraction.extractGoLinked_assume, ObligationExtraction.extractGoLinked_ite,
      ObligationExtraction.extractGoLinked_init, ObligationExtraction.extractGoLinked_unsupported,
      Except.bind_is_ok, Array.mem_toList_iff, Array.toList_append, List.mem_append,
      List.not_mem_nil, not_false_eq_true, forall_const, not_or, and_imp]
  case case5 ihThen ihElse ihRest =>
    obtain ⟨thenObs, hthen, elseObs, helse, hrest⟩ := h
    intro hmem hfresh
    by_cases hinThen : (obligation, link) ∈ thenObs
    · exact ihThen _ hthen hinThen
    by_cases hinElse : (obligation, link) ∈ elseObs
    · exact ihElse _ helse hinElse
    exact ihRest _ _ _ hrest hmem hfresh hinThen hinElse
  all_goals grind +splitImp [prepend_scopes_length_le_one, consume_flatten_prepend_single,
    List.prefix_append]

/-- **Single static assignment of all definitions.**  For a program that passes
    `Block.readsDefined inputs` (every read is of a name defined earlier, and no definition
    rebinds a defined name) and `Block.nondetIteLast`, extracted from a root path condition
    (`RootPc`), all variable-definition names (det and nondet) of any extracted obligation's
    `assumptions` are pairwise distinct and disjoint from `inputs`. -/
theorem extractLinked_all_ssa
    {pc0 : Imperative.RevPathConditions Expression} (statements : Statements)
      (inputs : List CoreIdent)
    (obligation : ProofObligation Expression) (link : ObligationExtraction.ExtractBackLink)
    (arr : Array ObligationExtraction.LinkedObligation)
    (hok : ObligationExtraction.extractLinkedFromStatements pc0 statements = .ok arr)
    (hmem : (obligation, link) ∈ arr.toList)
    (hpc0 : RootPc pc0)
    (hws : Block.readsDefined inputs statements = true)
    (hshape : Block.nondetIteLast statements = true) :
    (allVarNames obligation.assumptions).Nodup ∧
      ∀ n ∈ allVarNames obligation.assumptions, n ∉ inputs :=
  cel_ssa_walk allEntry (fun e => by cases e <;> simp!) _ hok hws hshape (fun _ => id)
    (by rw [cel_names, ← allVarNames, allVarNames_eq_nil_of_rootPc hpc0]; simp) nofun _ hmem

end -- public section

end Core
